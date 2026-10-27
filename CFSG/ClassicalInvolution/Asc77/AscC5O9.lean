module

public import CFSG.ClassicalInvolution.Asc77.AscC5O8

public section

namespace CFSG.ClassicalInvolution.Asc77.C5O

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap

variable {G : Type} [Group G]

@[expose] def mulSub (A B : Subgroup G) (h : ∀ x ∈ A, ∀ y ∈ B, x * y * x⁻¹ ∈ B) :
    Subgroup G where
  carrier := {g | ∃ x ∈ A, ∃ y ∈ B, g = x * y}
  one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨x₁, hx₁, y₁, hy₁, rfl⟩ ⟨x₂, hx₂, y₂, hy₂, rfl⟩
    refine ⟨x₁ * x₂, mul_mem hx₁ hx₂, x₂⁻¹ * y₁ * x₂ * y₂, mul_mem ?_ hy₂, by group⟩
    have := h x₂⁻¹ (inv_mem hx₂) y₁ hy₁
    simpa using this
  inv_mem' := by
    rintro _ ⟨x, hx, y, hy, rfl⟩
    exact ⟨x⁻¹, inv_mem hx, x * y⁻¹ * x⁻¹, h x hx _ (inv_mem hy), by group⟩

theorem mem_mulSub {A B : Subgroup G} {h : ∀ x ∈ A, ∀ y ∈ B, x * y * x⁻¹ ∈ B} {g : G} :
    g ∈ mulSub A B h ↔ ∃ x ∈ A, ∃ y ∈ B, g = x * y := Iff.rfl

theorem le_mulSub_left {A B : Subgroup G} (h : ∀ x ∈ A, ∀ y ∈ B, x * y * x⁻¹ ∈ B) :
    A ≤ mulSub A B h := fun x hx => ⟨x, hx, 1, one_mem _, by simp⟩

theorem le_mulSub_right {A B : Subgroup G} (h : ∀ x ∈ A, ∀ y ∈ B, x * y * x⁻¹ ∈ B) :
    B ≤ mulSub A B h := fun y hy => ⟨1, one_mem _, y, hy, by simp⟩

theorem zpow_of_sq {τ : G} (hτ : τ * τ = 1) (k : ℤ) : τ ^ k = 1 ∨ τ ^ k = τ := by
  have hi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ
  have step : ∀ x : G, (x = 1 ∨ x = τ) → (x * τ = 1 ∨ x * τ = τ) := by
    rintro x (rfl | rfl)
    · right; rw [one_mul]
    · left; exact hτ
  induction k using Int.induction_on with
  | zero => left; rw [zpow_zero]
  | succ n ih => rw [zpow_add_one]; exact step _ ih
  | pred n ih => rw [zpow_sub_one, hi]; exact step _ ih

variable [Finite G]


theorem conj_mem_kerLayer {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {c g n : G}
    (hg : g ∈ Subgroup.centralizer ({c} : Set G)) (hn : n ∈ kerLayer Ω c) :
    g * n * g⁻¹ ∈ kerLayer Ω c := by
  refine ⟨(Subgroup.centralizer ({c} : Set G)).mul_mem
    ((Subgroup.centralizer ({c} : Set G)).mul_mem hg hn.1)
    ((Subgroup.centralizer ({c} : Set G)).inv_mem hg), ?_⟩
  have h := trivialOnQuot_conjSub hn.2 g
  rwa [conjSub_exactLayer hΩ hg] at h

theorem mem_normalizer_kerLayer {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {c g : G}
    (hg : g ∈ Subgroup.centralizer ({c} : Set G)) :
    g ∈ Subgroup.normalizer ((kerLayer Ω c : Subgroup G) : Set G) := by
  refine Subgroup.mem_normalizer_iff.mpr fun n => ⟨fun hn => conj_mem_kerLayer hΩ hg hn,
    fun hn => ?_⟩
  have := conj_mem_kerLayer hΩ (inv_mem hg) hn
  simpa [mul_assoc] using this

theorem conj_mem_oddCore_kerLayer {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {c g o : G}
    (hg : g ∈ Subgroup.centralizer ({c} : Set G)) (ho : o ∈ oddCoreIn (kerLayer Ω c)) :
    g * o * g⁻¹ ∈ oddCoreIn (kerLayer Ω c) :=
  conj_mem_oddCoreIn_of_mem_normalizer (mem_normalizer_kerLayer hΩ hg) ho

@[expose] def hSub {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) (c τ : G)
    (hτ : τ ∈ Subgroup.centralizer ({c} : Set G)) : Subgroup G :=
  mulSub (Subgroup.zpowers τ)
    (mulSub (exactLayer Ω c) (oddCoreIn (kerLayer Ω c))
      (fun x hx o ho => conj_mem_oddCore_kerLayer hΩ (exactLayer_le_centralizer Ω c hx) ho))
    (fun y hy w hw => by
      obtain ⟨k, rfl⟩ := hy
      have hk : τ ^ k ∈ Subgroup.centralizer ({c} : Set G) := zpow_mem hτ k
      obtain ⟨x, hx, o, ho, rfl⟩ := hw
      refine ⟨τ ^ k * x * (τ ^ k)⁻¹, ?_, τ ^ k * o * (τ ^ k)⁻¹,
        conj_mem_oddCore_kerLayer hΩ hk ho, by group⟩
      have := conjSub_exactLayer hΩ hk (c := c)
      rw [← this]
      exact ⟨x, hx, rfl⟩)

theorem le_hSub_layer {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {c τ : G}
    (hτ : τ ∈ Subgroup.centralizer ({c} : Set G)) : exactLayer Ω c ≤ hSub hΩ c τ hτ :=
  (le_mulSub_left _).trans (le_mulSub_right _)

theorem le_hSub_odd {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {c τ : G}
    (hτ : τ ∈ Subgroup.centralizer ({c} : Set G)) :
    oddCoreIn (kerLayer Ω c) ≤ hSub hΩ c τ hτ :=
  (le_mulSub_right _).trans (le_mulSub_right _)

theorem mem_hSub_self {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {c τ : G}
    (hτ : τ ∈ Subgroup.centralizer ({c} : Set G)) : τ ∈ hSub hΩ c τ hτ :=
  le_mulSub_left _ (Subgroup.mem_zpowers τ)

variable {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ a : G}

namespace Ctx

theorem a_mem_kerLayer (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a) : a ∈ kerLayer Ω a :=
  ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, C.a_triv⟩

theorem mem_oddCore_of_odd [IsSimpleGroup G] (hM5 : Om5Centerless p f)
    (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a) {n : G} (hn : n ∈ kerLayer Ω a)
    (hodd : Odd (orderOf n)) : n ∈ oddCoreIn (kerLayer Ω a) := by
  have ha := C.a_mem_kerLayer
  have hsyl : IsSylow2In (Subgroup.zpowers a) (kerLayer Ω a) := by
    refine ⟨Subgroup.zpowers_le.mpr ha, isPGroup_zpowers_of_sq_eq_one C.ha2, ?_⟩
    intro V hV hV2 hle
    apply le_antisymm _ hle
    intro v hv
    have hv2 : IsPGroup 2 (Subgroup.zpowers v) := hV2.to_le (Subgroup.zpowers_le.mpr hv)
    have hvN := hV hv
    rcases C.twoElt_triv hM5 (Subgroup.mem_centralizer_singleton_iff.mp hvN.1) hvN.2 hv2 with
      h | h
    · rw [h]; exact one_mem _
    · rw [h]; exact Subgroup.mem_zpowers a
  have hNC : ∀ g ∈ kerLayer Ω a, (∀ x : G, x ∈ Subgroup.zpowers a ↔
      g * x * g⁻¹ ∈ Subgroup.zpowers a) → ∀ x ∈ Subgroup.zpowers a, g * x = x * g := by
    intro g hg _ x hx
    obtain ⟨k, rfl⟩ := hx
    have hga : g * a = a * g := Subgroup.mem_centralizer_singleton_iff.mp hg.1
    exact ((Commute.zpow_right hga k)).eq
  obtain ⟨o, ho, b, hb, rfl⟩ := exists_oddCore_mul_of_normalizer_le hsyl hNC n hn
  obtain ⟨k, rfl⟩ := hb
  dsimp only at hodd ⊢
  rcases zpow_of_sq C.ha2 k with h | h
  · rw [h, mul_one]; exact ho
  · exfalso
    rw [h] at hodd
    have hoN : o ∈ kerLayer Ω a := oddCoreIn_le _ ho
    have hoa : o * a = a * o := (Subgroup.mem_centralizer_singleton_iff.mp hoN.1)
    obtain ⟨j, hj⟩ := hodd
    have h1 : (o * a) ^ (2 * j + 1) = 1 := by rw [← hj]; exact pow_orderOf_eq_one _
    have hapow : a ^ (2 * j + 1) = a := by
      rw [pow_succ, pow_mul, sq, C.ha2, one_pow, one_mul]
    rw [(Commute.mul_pow hoa.symm.symm _), hapow] at h1
    have h2 : a = (o ^ (2 * j + 1))⁻¹ := eq_inv_of_mul_eq_one_right h1
    have h3 : (o ^ (2 * j + 1))⁻¹ ∈ oddCoreIn (kerLayer Ω a) := inv_mem (pow_mem ho _)
    rw [← h2] at h3
    have h4 := eq_one_of_isPGroup_of_odd (isPGroup_zpowers_of_sq_eq_one C.ha2)
      (odd_card_oddCoreIn _) (Subgroup.mem_zpowers a) h3
    exact C.ha1 h4

theorem not_inner [IsSimpleGroup G] (hM : ModelFacts p f)
    (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a) {τ cτ : G}
    (hτC : τ ∈ Subgroup.centralizer ({a} : Set G)) (hcτ : cτ * z * cτ⁻¹ = τ)
    (hτn : ∀ h : G, h * a = a * h → h * z * h⁻¹ ≠ τ)
    (hτX : conjSub τ (exactLayer Ω a) = exactLayer Ω a) :
    ¬ ∃ yb, ∀ e, C25Y.layerAut (exactLayer Ω a) hτX e = yb * e * yb⁻¹ := by
  rintro ⟨yb, hyb⟩
  subst hcτ
  have hs : Hyp23Setting p f Ω K K' z := C.hyp.std.setting
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  obtain ⟨hzY, hu₁Y, hu₂Y, hK₂, hK₂', hD⟩ := C.om5
  have hτ2 : (cτ * z * cτ⁻¹) * (cτ * z * cτ⁻¹) = 1 := by
    calc (cτ * z * cτ⁻¹) * (cτ * z * cτ⁻¹) = cτ * (z * z) * cτ⁻¹ := by group
      _ = 1 := by rw [C.hz2]; group
  have hyb2 : yb * yb = 1 := by
    apply hM.centerless _ _ _ _ _ _ _ hD
    intro x
    have h1 := C25Y.layerAut_involutive _ hτX hτ2 x
    rw [hyb, hyb] at h1
    calc yb * yb * x = (yb * (yb * x * yb⁻¹) * yb⁻¹) * (yb * yb) := by group
      _ = x * (yb * yb) := by rw [h1]
  by_cases hy1 : yb = 1
  · have hτT : cτ * z * cτ⁻¹ ∈ trivialOnQuot (exactLayer Ω a) := by
      rw [← layerAut_eq_id_iff _ hτX]
      intro e
      rw [hyb, hy1]
      group
    rcases C.twoElt_triv hM.centerless (Subgroup.mem_centralizer_singleton_iff.mp hτC) hτT
      (isPGroup_zpowers_of_sq_eq_one hτ2) with h | h
    · apply C.hz1
      calc z = cτ⁻¹ * (cτ * z * cτ⁻¹) * cτ := by group
        _ = 1 := by rw [h]; group
    · exact C.not_conj_z cτ h
  · obtain ⟨J, hJ, x, hxJ, hx4, hx2, hxc⟩ := hM.invFixFour _ _ _ _ _ _ _ hD yb hyb2 hy1
    have hfix : C25Y.layerAut (exactLayer Ω a) hτX x = x := by
      rw [hyb, hxc]
      group
    obtain ⟨D, hD1, i₀, hDi⟩ := hD.lie
    have hD4 : ∀ i, D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4 := by
      intro i
      have hi : i = i₀ := Fin.ext (by have h1 := i.2; have h2 := i₀.2; omega)
      subst hi
      simp only [IsOrthTag] at hDi
      rcases hDi with ⟨-, ht, -⟩ | ⟨h6, -⟩ | ⟨h6, -⟩ | ⟨h7, -⟩ | ⟨h8, -⟩ | ⟨h8, -⟩
      · rw [ht]; exact ⟨by decide, by decide⟩
      all_goals omega
    obtain ⟨h, hhC, hh⟩ := C25Y.c25_8_one C.hyp C.ha2 hzY hK₂ D hD1 hD4 hτC hJ hxJ hx4 hx2 hfix
    exact hτn h (Subgroup.mem_centralizer_singleton_iff.mp hhC) hh

theorem oddCore_layer_le (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a) :
    oddCoreIn (exactLayer Ω a) ≤ oddCoreIn (kerLayer Ω a) := by
  have hΩ : HypOmegaMod p f Ω := C.hyp.std.setting.stand.hyp
  refine le_oddCoreIn_of_normalizes (fun o ho => ?_) (fun n hn => ?_) (odd_card_oddCoreIn _)
  · have hoX : o ∈ exactLayer Ω a := oddCoreIn_le _ ho
    refine ⟨exactLayer_le_centralizer Ω a hoX,
      mem_normalizer_of_conjSub_eq (conjSub_eq_self_of_mem hoX), fun y hy => ?_⟩
    rw [commutatorElement_def]
    have h1 : y * o⁻¹ * y⁻¹ ∈ oddCoreIn (exactLayer Ω a) :=
      conj_mem_oddCoreIn hy ((oddCoreIn _).inv_mem ho)
    have := (oddCoreIn (exactLayer Ω a)).mul_mem ho h1
    simpa [mul_assoc] using this
  · have hX : n ∈ Subgroup.normalizer ((exactLayer Ω a : Subgroup G) : Set G) :=
      mem_normalizer_of_conjSub_eq (conjSub_exactLayer hΩ.conjInvariant hn.1)
    refine Subgroup.mem_normalizer_iff.mpr fun o => ⟨fun ho =>
      conj_mem_oddCoreIn_of_mem_normalizer hX ho, fun ho => ?_⟩
    have := conj_mem_oddCoreIn_of_mem_normalizer (inv_mem hX) ho
    simpa [mul_assoc] using this

theorem a_not_mem_hSub [IsSimpleGroup G] (hM : ModelFacts p f)
    (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a) {τ cτ : G}
    (hτC : τ ∈ Subgroup.centralizer ({a} : Set G)) (hcτ : cτ * z * cτ⁻¹ = τ)
    (hτn : ∀ h : G, h * a = a * h → h * z * h⁻¹ ≠ τ) :
    a ∉ hSub C.hyp.std.setting.stand.hyp.conjInvariant a τ hτC := by
  have hs : Hyp23Setting p f Ω K K' z := C.hyp.std.setting
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hτ2 : τ * τ = 1 := by
    rw [← hcτ]
    calc (cτ * z * cτ⁻¹) * (cτ * z * cτ⁻¹) = cτ * (z * z) * cτ⁻¹ := by group
      _ = 1 := by rw [C.hz2]; group
  obtain ⟨hzY, hu₁Y, hu₂Y, hK₂, hK₂', hD⟩ := C.om5
  have haK := C.a_mem_kerLayer
  rintro ⟨y, ⟨k, rfl⟩, w, ⟨x, hx, o, ho, rfl⟩, ha⟩
  have hoN : o ∈ kerLayer Ω a := oddCoreIn_le _ ho
  rcases zpow_of_sq hτ2 k with h | h <;> dsimp only at h ha <;> rw [h] at ha
  ·
    rw [one_mul] at ha
    have hxN : x ∈ kerLayer Ω a := by
      have e : x = a * o⁻¹ := by rw [ha]; group
      rw [e]
      exact mul_mem haK (inv_mem hoN)
    have hxO : x ∈ oddCoreIn (exactLayer Ω a) := by
      have hxX : conjSub x (exactLayer Ω a) = exactLayer Ω a := conjSub_eq_self_of_mem hx
      have hfix := (layerAut_eq_id_iff (exactLayer Ω a) hxX).mpr hxN.2
      refine (mk_eq_one_iff (exactLayer Ω a) ⟨x, hx⟩).mp ?_
      apply hM.centerless _ _ _ _ _ _ _ hD
      intro e
      have h1 := hfix e
      rw [layerAut_of_mem _ hx] at h1
      calc QuotientGroup.mk ⟨x, hx⟩ * e = (QuotientGroup.mk ⟨x, hx⟩ * e *
            (QuotientGroup.mk ⟨x, hx⟩)⁻¹) * QuotientGroup.mk ⟨x, hx⟩ := by group
        _ = e * QuotientGroup.mk ⟨x, hx⟩ := by rw [h1]
    have hxO' := C.oddCore_layer_le hxO
    have haO : x * o ∈ oddCoreIn (kerLayer Ω a) := mul_mem hxO' ho
    rw [← ha] at haO
    exact C.ha1 (eq_one_of_isPGroup_of_odd (isPGroup_zpowers_of_sq_eq_one C.ha2)
      (odd_card_oddCoreIn _) (Subgroup.mem_zpowers a) haO)
  ·
    have hτX : conjSub τ (exactLayer Ω a) = exactLayer Ω a :=
      conjSub_exactLayer hΩ.conjInvariant hτC
    apply C.not_inner hM hτC hcτ hτn hτX
    refine ⟨QuotientGroup.mk ⟨x⁻¹, inv_mem hx⟩, fun e => ?_⟩
    have e1 : τ = (a * o⁻¹) * x⁻¹ := by rw [ha]; group
    have hao : a * o⁻¹ ∈ kerLayer Ω a := mul_mem haK (inv_mem hoN)
    have hx1 : conjSub x⁻¹ (exactLayer Ω a) = exactLayer Ω a :=
      conjSub_eq_self_of_mem (inv_mem hx)
    have hao1 : conjSub (a * o⁻¹) (exactLayer Ω a) = exactLayer Ω a :=
      conjSub_exactLayer hΩ.conjInvariant hao.1
    have hfixa := (layerAut_eq_id_iff (exactLayer Ω a) hao1).mpr hao.2
    have h2 : conjSub ((a * o⁻¹) * x⁻¹) (exactLayer Ω a) = exactLayer Ω a := by
      rw [← e1]; exact hτX
    have h3 := layerAut_mul_apply (exactLayer Ω a) hao1 hx1 h2 e
    rw [hfixa, layerAut_of_mem _ (inv_mem hx)] at h3
    have h4 : C25Y.layerAut (exactLayer Ω a) hτX e =
        C25Y.layerAut (exactLayer Ω a) h2 e := by
      subst e1
      rfl
    rw [h4, h3]

end Ctx

end CFSG.ClassicalInvolution.Asc77.C5O
