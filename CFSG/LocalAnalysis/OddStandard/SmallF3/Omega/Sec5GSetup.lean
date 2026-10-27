module

public import CFSG.GH74.GLS.C3.Layer1.Th2P412GoldX
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5GDefs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Open CFSG.Goldschmidt CFSG.GH74.GLS.Th2.P412

variable {X : Type} [Group X] (A : Subgroup X)

theorem sec5g_mem_img {x : Sec5GBar A} :
    x ∈ Sec5GImg A ↔ ∃ (a : X) (ha : a ∈ A), sec5g_pi A ⟨a, subset_normalClosure ha⟩ = x := by
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨(m : X), hm, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, subset_normalClosure ha⟩, ha, rfl⟩

theorem sec5g_inj_of_pgroup [Finite X] {P : Subgroup ↥(normalClosure (A : Set X))}
    (hP : IsPGroup 2 ↥P) {x y : ↥(normalClosure (A : Set X))} (hx : x ∈ P) (hy : y ∈ P)
    (hxy : sec5g_pi A x = sec5g_pi A y) : x = y := by
  have h1 : x⁻¹ * y ∈ goldschmidtOddCore ↥(normalClosure (A : Set X)) := QuotientGroup.eq.1 hxy
  have h2 : x⁻¹ * y ∈ P := Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) hy
  exact inv_mul_eq_one.1 (eq_one_of_mem_oddCore_of_isPGroup h1 hP h2)

theorem sec5g_card_img [Finite X] (hAsq : ∀ a ∈ A, a * a = 1) (hA4 : Nat.card A = 4) :
    Nat.card ↥(Sec5GImg A) = 4 := by
  have hinjA : ∀ x ∈ A.subgroupOf (normalClosure (A : Set X)),
      ∀ y ∈ A.subgroupOf (normalClosure (A : Set X)), sec5g_pi A x = sec5g_pi A y → x = y := by
    intro x hx y hy hxy
    have h1 : x⁻¹ * y ∈ goldschmidtOddCore ↥(normalClosure (A : Set X)) := QuotientGroup.eq.1 hxy
    have h2 : (((x⁻¹ * y : ↥(normalClosure (A : Set X)))) : X) ∈ A := by
      have : (((x⁻¹ * y : ↥(normalClosure (A : Set X)))) : X) = (x : X)⁻¹ * (y : X) := by simp
      rw [this]
      exact A.mul_mem (A.inv_mem hx) hy
    have h3 := eq_one_of_mem_oddCore_of_sq h1 (Subtype.ext (hAsq _ h2))
    exact inv_mul_eq_one.1 h3
  rw [Sec5GImg, card_map_eq_of_injOn _ _ hinjA]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe subset_normalClosure).toEquiv).trans hA4

theorem sec5g_eq_one_of_pi [Finite X] (hAsq : ∀ a ∈ A, a * a = 1) {a : X} (ha : a ∈ A)
    (h : sec5g_pi A ⟨a, subset_normalClosure ha⟩ = 1) : a = 1 := by
  have hO1 : (⟨a, subset_normalClosure ha⟩ : ↥(normalClosure (A : Set X))) ∈
      goldschmidtOddCore ↥(normalClosure (A : Set X)) := (QuotientGroup.eq_one_iff _).1 h
  exact congrArg Subtype.val (eq_one_of_mem_oddCore_of_sq hO1 (Subtype.ext (hAsq a ha)))

theorem sec5g_pCore_psiAut [Finite X] (g : X) {u : Sec5GBar A}
    (hu : u ∈ CFSG.Open.pCore 2 (Sec5GBar A)) :
    psiAut (normalClosure (A : Set X)) g u ∈ CFSG.Open.pCore 2 (Sec5GBar A) := by
  have := Subgroup.mem_map_of_mem (psiAut (normalClosure (A : Set X)) g).toMonoidHom hu
  rwa [map_pCore_psiAut] at this

theorem sec5g_psiAut_pi (g : X) {a : X} (ha : a ∈ A) (hb : g * a * g⁻¹ ∈ A) :
    psiAut (normalClosure (A : Set X)) g (sec5g_pi A ⟨a, subset_normalClosure ha⟩) =
      sec5g_pi A ⟨g * a * g⁻¹, subset_normalClosure hb⟩ := by
  simp only [QuotientGroup.mk'_apply]
  rw [psiAut_mk]
  congr 1

theorem sec5g_dich [Finite X]
    (htrans : ∀ a ∈ A, ∀ b ∈ A, a ≠ 1 → b ≠ 1 → ∃ g : X, g⁻¹ * a * g = b)
    (hUAb : CFSG.Open.pCore 2 (Sec5GBar A) ≤ Sec5GImg A) :
    CFSG.Open.pCore 2 (Sec5GBar A) = ⊥ ∨ Sec5GImg A ≤ CFSG.Open.pCore 2 (Sec5GBar A) := by
  classical
  by_cases hcase : ∃ (a : X) (ha : a ∈ A), a ≠ 1 ∧
      sec5g_pi A ⟨a, subset_normalClosure ha⟩ ∈ CFSG.Open.pCore 2 (Sec5GBar A)
  · right
    obtain ⟨a, ha, ha1, haU⟩ := hcase
    intro x hx
    obtain ⟨b, hb, rfl⟩ := (sec5g_mem_img A).1 hx
    by_cases hb1 : b = 1
    · subst hb1
      have : (⟨1, subset_normalClosure hb⟩ : ↥(normalClosure (A : Set X))) = 1 := rfl
      rw [this, map_one]
      exact Subgroup.one_mem _
    · obtain ⟨g, hg⟩ := htrans a ha b hb ha1 hb1
      have hgb : g⁻¹ * a * g⁻¹⁻¹ = b := by simpa using hg
      have hgA : g⁻¹ * a * g⁻¹⁻¹ ∈ A := by rw [hgb]; exact hb
      have h1 := sec5g_psiAut_pi A g⁻¹ ha hgA
      have h2 : (⟨g⁻¹ * a * g⁻¹⁻¹, subset_normalClosure hgA⟩ : ↥(normalClosure (A : Set X))) =
          ⟨b, subset_normalClosure hb⟩ := Subtype.ext hgb
      rw [h2] at h1
      rw [← h1]
      exact sec5g_pCore_psiAut A g⁻¹ haU
  · left
    push Not at hcase
    refine eq_bot_iff.2 fun u hu => ?_
    obtain ⟨a, ha, rfl⟩ := (sec5g_mem_img A).1 (hUAb hu)
    by_cases ha1 : a = 1
    · subst ha1
      have : (⟨1, subset_normalClosure ha⟩ : ↥(normalClosure (A : Set X))) = 1 := rfl
      rw [this, map_one]
      exact Subgroup.one_mem _
    · exact absurd hu (hcase a ha ha1)

theorem sec5g_img_top [Finite X] (hAbU : Sec5GImg A ≤ CFSG.Open.pCore 2 (Sec5GBar A))
    (hUAb : CFSG.Open.pCore 2 (Sec5GBar A) ≤ Sec5GImg A) : Sec5GImg A = ⊤ := by
  classical
  set M : Subgroup X := normalClosure (A : Set X) with hMdef
  set U : Subgroup (Sec5GBar A) := CFSG.Open.pCore 2 (Sec5GBar A) with hU
  set Q : Subgroup X := (U.comap (sec5g_pi A)).map M.subtype with hQ
  have hQn : Q.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨m, hm, rfl⟩ := hn
    refine ⟨MulAut.conjNormal g m, ?_, ?_⟩
    · have h1 : psiAut M g (sec5g_pi A m) = sec5g_pi A (MulAut.conjNormal g m) := by
        simp only [QuotientGroup.mk'_apply]
        exact psiAut_mk M g m
      show sec5g_pi A (MulAut.conjNormal g m) ∈ U
      rw [← h1]
      exact sec5g_pCore_psiAut A g hm
    · simp [MulAut.conjNormal_apply]
  have hAQ : A ≤ Q := fun a ha =>
    ⟨⟨a, subset_normalClosure ha⟩, hAbU ((sec5g_mem_img A).2 ⟨a, ha, rfl⟩), rfl⟩
  have hMQ : M ≤ Q := Subgroup.normalClosure_le_normal hAQ
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective _ x
  obtain ⟨m', hm', hm'e⟩ := hMQ m.2
  have : m' = m := Subtype.ext hm'e
  subst this
  exact hUAb hm'

end CFSG.OddStandard.SmallF3.Omega
