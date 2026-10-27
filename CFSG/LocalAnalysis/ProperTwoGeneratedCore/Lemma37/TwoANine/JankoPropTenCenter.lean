module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPropTenFree

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTen

open Subgroup CFSG.Semidihedral.Principal.PrimewiseScalar

variable {G : Type} [Group G] [Finite G] {z : G} {fr : JankoFrame G z}

namespace Hyp

omit [Finite G] in
theorem F_le_normalizer_M (fr : JankoFrame G z) : fr.F ≤ normalizer (fr.M : Set G) :=
  fr.F_le_centralizer.trans (C₁_le_normalizer_M fr)

theorem centralizer_M_le (h : Hyp fr) :
    centralizer (fr.M : Set G) ⊓ centralizer (fr.P₁ : Set G) ≤ fr.M := by
  set Cm := centralizer (fr.M : Set G) ⊓ centralizer (fr.P₁ : Set G)
  have hC₁Cm : centralizer (fr.P₁ : Set G) ≤ normalizer (Cm : Set G) := fun c hc =>
    inf_mem_normalizer (mem_normalizer_centralizer (C₁_le_normalizer_M fr hc))
      (Subgroup.le_normalizer hc)
  have hCmM : Cm ≤ normalizer (fr.M : Set G) := fun c hc => C₁_le_normalizer_M fr hc.2
  set B := (Cm ⊔ fr.M) ⊓ fr.F
  have hFB : fr.F ≤ normalizer (B : Set G) := fun f hf =>
    inf_mem_normalizer (Subgroup.inf_normalizer_le_normalizer_sup _ _
      ⟨hC₁Cm (fr.F_le_centralizer hf), F_le_normalizer_M fr hf⟩) (Subgroup.le_normalizer hf)
  have hB : B = ⊥ := by
    by_contra hne
    have hzB := fr.z_mem_of_normal B inf_le_right hFB hne
    have hz' : z ∈ ((Cm ⊔ fr.M : Subgroup G) : Set G) := hzB.1
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hCmM] at hz'
    obtain ⟨c, hc, m, hm, hcm⟩ := Set.mem_mul.mp hz'
    have hcM : ∀ x ∈ fr.M, x * c = c * x := mem_centralizer_iff.mp hc.1
    have hzm : m * z = z * m := by
      have h1 := hcM m hm
      calc m * z = m * (c * m) := by rw [hcm]
        _ = c * m * m := by rw [← mul_assoc, h1]
        _ = z * m := by rw [hcm]
    have hmP : m ∈ fr.P₁ := by
      rw [← M_inf_H h]; exact ⟨hm, mem_centralizer_singleton_iff.mpr hzm⟩
    have hMz : fr.M ≤ fr.M ⊓ centralizer ({z} : Set G) := fun x hx => by
      refine ⟨hx, mem_centralizer_singleton_iff.mpr ?_⟩
      have h1 := hcM x hx
      have h2 : x * m = m * x := commute_of_mem_C₁ fr (M_le_C₁ fr hx) hmP
      calc x * z = x * (c * m) := by rw [hcm]
        _ = c * (x * m) := by rw [← mul_assoc, h1, mul_assoc]
        _ = c * m * x := by rw [h2, mul_assoc]
        _ = z * x := by rw [hcm]
    rw [M_inf_H h] at hMz
    exact M_ne_P₁ h (le_antisymm hMz (P₁_le_M fr))
  intro x hx
  have hx' : x ∈ ((fr.M ⊔ fr.F : Subgroup G) : Set G) := by
    rw [← centralizer_P₁_eq h]; exact hx.2
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ (F_le_normalizer_M fr)] at hx'
  obtain ⟨m, hm, f, hf, rfl⟩ := Set.mem_mul.mp hx'
  have hfB : f ∈ B := by
    refine ⟨?_, hf⟩
    have : f = m⁻¹ * (m * f) := by group
    rw [this]
    exact mul_mem (mem_sup_right (inv_mem hm)) (mem_sup_left hx)
  rw [hB, mem_bot] at hfB
  rw [hfB, mul_one]
  exact hm

omit [Finite G] in
theorem t_mem_centralizer_tz (fr : JankoFrame G z) : fr.t ∈ centralizer ({fr.t * z} : Set G) :=
  mem_centralizer_singleton_iff.mpr (by rw [mul_assoc, t_mul_z fr, ← mul_assoc])

omit [Finite G] in
theorem z_mem_centralizer_tz (fr : JankoFrame G z) : z ∈ centralizer ({fr.t * z} : Set G) :=
  mem_centralizer_singleton_iff.mpr (by rw [← mul_assoc, ← t_mul_z fr])

theorem t_mem_normalizer_At (fr : JankoFrame G z) : fr.t ∈ normalizer (fr.At : Set G) :=
  inf_mem_normalizer (t_mem_normalizer_M fr)
    (Subgroup.le_normalizer (mem_centralizer_singleton_iff.mpr rfl))

theorem t_mem_normalizer_Atz (fr : JankoFrame G z) : fr.t ∈ normalizer (fr.Atz : Set G) :=
  inf_mem_normalizer (t_mem_normalizer_M fr) (Subgroup.le_normalizer (t_mem_centralizer_tz fr))

omit [Finite G] in
theorem z_mem_normalizer_Atz (fr : JankoFrame G z) : z ∈ normalizer (fr.Atz : Set G) :=
  inf_mem_normalizer (z_mem_normalizer_M fr) (Subgroup.le_normalizer (z_mem_centralizer_tz fr))

omit [Finite G] in
theorem inf_t_of_le {B : Subgroup G} (hAB : fr.At ≤ B) (hBM : B ≤ fr.M) :
    B ⊓ centralizer ({fr.t} : Set G) = fr.At :=
  le_antisymm (fun _ hx => ⟨hBM hx.1, hx.2⟩) (le_inf hAB (At_le_t fr))

omit [Finite G] in
theorem inf_tz_of_le {B : Subgroup G} (hAB : fr.Atz ≤ B) (hBM : B ≤ fr.M) :
    B ⊓ centralizer ({fr.t * z} : Set G) = fr.Atz :=
  le_antisymm (fun _ hx => ⟨hBM hx.1, hx.2⟩) (le_inf hAB inf_le_right)

theorem M_eq (h : Hyp fr) : fr.M = fr.P₁ ⊔ fr.At ⊔ fr.Atz := by
  set M₀ := fr.P₁ ⊔ fr.At ⊔ fr.Atz
  have hM₀M : M₀ ≤ fr.M := sup_le (sup_le (P₁_le_M fr) (At_le_M fr)) inf_le_left
  have hAM₀ : fr.At ≤ M₀ := le_sup_right.trans le_sup_left
  have hAzM₀ : fr.Atz ≤ M₀ := le_sup_right
  have hnorm : ∀ g : G, g ∈ normalizer (fr.P₁ : Set G) → g ∈ normalizer (fr.At : Set G) →
      g ∈ normalizer (fr.Atz : Set G) → g ∈ normalizer (M₀ : Set G) := fun g h1 h2 h3 =>
    Subgroup.inf_normalizer_le_normalizer_sup _ _
      ⟨Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨h1, h2⟩, h3⟩
  have key := card_eq_of_le_M h (le_sup_left.trans le_sup_left) hM₀M
    (hnorm _ (t_mem_normalizer_P₁ fr) (t_mem_normalizer_At fr) (t_mem_normalizer_Atz fr))
    (hnorm _ (C₁_le_normalizer_P₁ fr (z_mem_C₁ fr)) (z_mem_normalizer_At fr)
      (z_mem_normalizer_Atz fr))
  rw [inf_t_of_le hAM₀ hM₀M, inf_tz_of_le hAzM₀ hM₀M, card_At h, card_Atz h] at key
  exact (Subgroup.eq_of_le_of_card_ge hM₀M (by rw [key, card_M h]; norm_num)).symm

theorem P₁_le_center_M (fr : JankoFrame G z) :
    fr.P₁ ≤ fr.M ⊓ centralizer (fr.M : Set G) :=
  le_inf (P₁_le_M fr) fun _ hp => mem_centralizer_iff.mpr fun _ hm =>
    commute_of_mem_C₁ fr (M_le_C₁ fr hm) hp

theorem center_M_eq
    (h : Hyp fr) (hnc : ¬ ∀ a ∈ fr.M, ∀ b ∈ fr.M, a * b = b * a) :
    fr.M ⊓ centralizer (fr.M : Set G) = fr.P₁ := by
  set ZM := fr.M ⊓ centralizer (fr.M : Set G)
  have hnorm : ∀ g : G, g ∈ normalizer (fr.M : Set G) → g ∈ normalizer (ZM : Set G) :=
    fun g hg => inf_mem_normalizer hg (mem_normalizer_centralizer hg)
  obtain ⟨T, hTF, hT⟩ := exists_T fr
  have hZt : ZM ⊓ centralizer ({fr.t} : Set G) ≤ fr.At := fun _ hx => ⟨hx.1.1, hx.2⟩
  have hTZ : T ≤ normalizer ((ZM ⊓ centralizer ({fr.t} : Set G) : Subgroup G) : Set G) :=
    fun u hu => inf_mem_normalizer
      (hnorm u (C₁_le_normalizer_M fr (fr.F_le_centralizer (F₁_le_F fr (hTF hu)))))
      (Subgroup.le_normalizer (F₁_le_t fr (hTF hu)))
  have h8 := eight_dvd_card_sub_one h hTF hT hZt hTZ
  have hdvd : Nat.card (ZM ⊓ centralizer ({fr.t} : Set G) : Subgroup G) ∣ 9 :=
    card_At h ▸ Subgroup.card_dvd_of_le hZt
  have hcases : Nat.card (ZM ⊓ centralizer ({fr.t} : Set G) : Subgroup G) = 1 ∨
      Nat.card (ZM ⊓ centralizer ({fr.t} : Set G) : Subgroup G) = 9 := by
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases hc : Nat.card (ZM ⊓ centralizer ({fr.t} : Set G) : Subgroup G) <;> omega
  rcases hcases with h1 | h9
  · have hZcard := card_eq_of_le_M h (P₁_le_center_M fr) inf_le_left
      (hnorm _ (t_mem_normalizer_M fr)) (hnorm _ (z_mem_normalizer_M fr))
    rw [card_inf_tz_eq fr (hnorm _ (y_mem_normalizer_M fr)), h1] at hZcard
    exact (Subgroup.eq_of_le_of_card_ge (P₁_le_center_M fr) (by rw [hZcard, card_P₁])).symm
  · exfalso
    apply hnc
    have heq : ZM ⊓ centralizer ({fr.t} : Set G) = fr.At :=
      Subgroup.eq_of_le_of_card_ge hZt (by rw [h9, card_At h])
    have hAZ : fr.At ≤ ZM := by rw [← heq]; exact inf_le_left
    have hAzZ : fr.Atz ≤ ZM := by
      rw [← map_y_At fr, ← map_conj_eq_of_mem_normalizer (hnorm _ (y_mem_normalizer_M fr))]
      exact Subgroup.map_mono hAZ
    have hMZ : fr.M ≤ ZM := by
      rw [M_eq h]; exact sup_le (sup_le (P₁_le_center_M fr) hAZ) hAzZ
    intro a ha b hb
    exact mem_centralizer_iff.mp (hMZ hb).2 a ha

end Hyp

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTen
