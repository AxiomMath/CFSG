module

public import CFSG.ClassicalInvolution.Q3.Q3T8AF05

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

section Facts

@[expose] def LinkModelFacts (Q : Type) [Group Q] : Prop :=
  (∀ u v : Q, u * u = 1 → u ≠ 1 → v * v = 1 → v ≠ 1 → ∃ g : Q, g * u * g⁻¹ = v) ∧
  (∀ u v : Q, u * u = 1 → u ≠ 1 → v * v = 1 → v ≠ 1 → u ≠ v → u * v = v * u →
    Subgroup.centralizer ({u} : Set Q) ⊔ Subgroup.centralizer ({v} : Set Q) ⊔
      Subgroup.centralizer ({u * v} : Set Q) = ⊤)

end Facts

section Glue

variable {G : Type} [Group G] [Finite G]

theorem link_conj_of_frame {X Λ H : Subgroup G} (hXΛ : X ≤ Λ)
    (hΛ : Λ ≤ Subgroup.normalizer (X : Set G)) {z t s t' : G} (hzΛ : z ∈ Λ) (hz2 : z * z = 1)
    (hzX : ∀ x ∈ X, ⁅x, z⁆ ∈ oddCoreOf X) (htX : t ∈ X) (hsX : s ∈ X) (ht'X : t' ∈ X)
    (ht2 : t * t = 1) (hs2 : s * s = 1) (ht'2 : t' * t' = 1) (hts : t ≠ s)
    (hzt : z * t = t * z) (hzs : z * s = s * z)
    (hzt' : z * t' = t' * z) (hst : t * s = s * t) (hO : oddCoreOf X ≤ H)
    (hHt : Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({t} : Set G) ≤ H)
    (hHs : Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({s} : Set G) ≤ H)
    (hHts : Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({t * s} : Set G) ≤ H)
    (hq : ∃ g : ↥X ⧸ classicalInvolutionOddCore ↥X,
      g * QuotientGroup.mk' (classicalInvolutionOddCore ↥X) ⟨t, htX⟩ * g⁻¹ =
        QuotientGroup.mk' (classicalInvolutionOddCore ↥X) ⟨t', ht'X⟩)
    (hgen : Subgroup.centralizer
          ({QuotientGroup.mk' (classicalInvolutionOddCore ↥X) ⟨t, htX⟩} :
            Set (↥X ⧸ classicalInvolutionOddCore ↥X)) ⊔
        Subgroup.centralizer
          ({QuotientGroup.mk' (classicalInvolutionOddCore ↥X) ⟨s, hsX⟩} :
            Set (↥X ⧸ classicalInvolutionOddCore ↥X)) ⊔
        Subgroup.centralizer
          ({QuotientGroup.mk' (classicalInvolutionOddCore ↥X) ⟨t, htX⟩ *
            QuotientGroup.mk' (classicalInvolutionOddCore ↥X) ⟨s, hsX⟩} :
            Set (↥X ⧸ classicalInvolutionOddCore ↥X)) = ⊤) :
    ∃ y ∈ H, y * z * y⁻¹ = z ∧ y * t * y⁻¹ = t' := by
  classical
  set O : Subgroup G := oddCoreOf X with hOdef
  have hOodd : Odd (Nat.card O) := oddCoreOf_odd_natCard X
  have hOX : O ≤ X := oddCoreOf_le_self X
  have hconjO : ∀ g ∈ Λ, ∀ o ∈ O, g * o * g⁻¹ ∈ O := fun g hg o ho =>
    (Subgroup.mem_normalizer_iff.mp (mem_normalizer_oddCore_of_mem_normalizer (hΛ hg)) o).mp ho
  have hCz : ∀ g ∈ Subgroup.centralizer ({z} : Set G), g * z * g⁻¹ = z := fun g hg => by
    rw [mul_inv_eq_iff_eq_mul]
    exact Subgroup.mem_centralizer_singleton_iff.mp hg
  set M : Subgroup ↥X := classicalInvolutionOddCore ↥X with hM
  set π : ↥X →* (↥X ⧸ M) := QuotientGroup.mk' M with hπ
  have hker : ∀ a : ↥X, π a = 1 → (a : G) ∈ O := fun a h =>
    mem_oddCoreOf_iff.mpr ⟨a.2, (QuotientGroup.eq_one_iff _).mp h⟩
  have hker' : ∀ a : ↥X, (a : G) ∈ O → π a = 1 := fun a h =>
    (QuotientGroup.eq_one_iff _).mpr (mem_oddCoreOf_iff.mp h).2
  set X₁ : Subgroup G := X ⊓ Subgroup.centralizer ({z} : Set G) with hX₁
  have hlift : ∀ q : ↥X ⧸ M, ∃ x : G, ∃ hx : x ∈ X₁, π ⟨x, hx.1⟩ = q := by
    intro q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨o, ho, hoz⟩ := exists_mul_mem_centralizer hOodd hconjO hzΛ hz2 (hzX a a.2)
    have hoX : o⁻¹ ∈ X := X.inv_mem (hOX ho)
    refine ⟨o⁻¹ * a, ⟨X.mul_mem hoX a.2, hoz⟩, ?_⟩
    have e : (⟨o⁻¹ * a, X.mul_mem hoX a.2⟩ : ↥X) = ⟨o⁻¹, hoX⟩ * a := rfl
    rw [e, map_mul, hker' ⟨o⁻¹, hoX⟩ (O.inv_mem ho), one_mul]
    rfl
  set W₀ : Subgroup ↥X := (H ⊓ X₁).subgroupOf X with hW₀
  set Ŵ : Subgroup (↥X ⧸ M) := W₀.map π with hŴ
  have hOodd₁ : Odd (Nat.card (O ⊓ Subgroup.centralizer ({z} : Set G) : Subgroup G)) :=
    hOodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hYn : ∀ y ∈ X₁, ∀ o ∈ O ⊓ Subgroup.centralizer ({z} : Set G),
      y * o * y⁻¹ ∈ O ⊓ Subgroup.centralizer ({z} : Set G) := fun y hy o ho =>
    ⟨hconjO y (hXΛ hy.1) o ho.1,
      (Subgroup.centralizer ({z} : Set G)).mul_mem
        ((Subgroup.centralizer ({z} : Set G)).mul_mem hy.2 ho.2)
        ((Subgroup.centralizer ({z} : Set G)).inv_mem hy.2)⟩
  have hcentW : ∀ (c : G) (hcX : c ∈ X), c * c = 1 → z * c = c * z →
      Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({c} : Set G) ≤ H →
      Subgroup.centralizer ({π ⟨c, hcX⟩} : Set (↥X ⧸ M)) ≤ Ŵ := by
    intro c hcX hc2 hzc hHc q hq
    obtain ⟨x, hx, rfl⟩ := hlift q
    have hcomm1 : π ⟨x, hx.1⟩ * π ⟨c, hcX⟩ = π ⟨c, hcX⟩ * π ⟨x, hx.1⟩ :=
      Subgroup.mem_centralizer_singleton_iff.mp hq
    have hcX₁ : c ∈ X₁ := ⟨hcX, Subgroup.mem_centralizer_singleton_iff.mpr hzc.symm⟩
    have hcommO : ⁅x, c⁆ ∈ O := by
      have h1 : π ⁅(⟨x, hx.1⟩ : ↥X), (⟨c, hcX⟩ : ↥X)⁆ = 1 := by
        rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm1
      have h2 := hker _ h1
      simpa [commutatorElement_def] using h2
    have hcommz : ⁅x, c⁆ ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [commutatorElement_def]
      exact (Subgroup.centralizer ({z} : Set G)).mul_mem
        ((Subgroup.centralizer ({z} : Set G)).mul_mem
          ((Subgroup.centralizer ({z} : Set G)).mul_mem hx.2 hcX₁.2)
          ((Subgroup.centralizer ({z} : Set G)).inv_mem hx.2))
        ((Subgroup.centralizer ({z} : Set G)).inv_mem hcX₁.2)
    obtain ⟨o, ho, hoc⟩ := exists_mul_mem_centralizer hOodd₁ hYn hcX₁ hc2 ⟨hcommO, hcommz⟩
    have hoX : o⁻¹ ∈ X := X.inv_mem (hOX ho.1)
    have hy₁ : o⁻¹ * x ∈ Subgroup.centralizer ({z} : Set G) :=
      (Subgroup.centralizer ({z} : Set G)).mul_mem
        ((Subgroup.centralizer ({z} : Set G)).inv_mem ho.2) hx.2
    have hyX : o⁻¹ * x ∈ X := X.mul_mem hoX hx.1
    have hyH : o⁻¹ * x ∈ H := hHc ⟨hy₁, hoc⟩
    refine ⟨⟨o⁻¹ * x, hyX⟩, Subgroup.mem_subgroupOf.mpr ⟨hyH, hyX, hy₁⟩, ?_⟩
    have e : (⟨o⁻¹ * x, hyX⟩ : ↥X) = ⟨o⁻¹, hoX⟩ * ⟨x, hx.1⟩ := rfl
    rw [e, map_mul, hker' ⟨o⁻¹, hoX⟩ (O.inv_mem ho.1), one_mul]
  have htsX : t * s ∈ X := X.mul_mem htX hsX
  have hts2 : (t * s) * (t * s) = 1 := by
    calc t * s * (t * s) = t * (s * t) * s := by group
      _ = t * (t * s) * s := by rw [← hst]
      _ = (t * t) * (s * s) := by group
      _ = 1 := by rw [ht2, hs2, one_mul]
  have hzts : z * (t * s) = (t * s) * z := by
    calc z * (t * s) = (z * t) * s := by group
      _ = (t * z) * s := by rw [hzt]
      _ = t * (z * s) := by group
      _ = t * (s * z) := by rw [hzs]
      _ = (t * s) * z := by group
  have hu2 : π ⟨t, htX⟩ * π ⟨t, htX⟩ = 1 := by
    rw [← map_mul]
    have : (⟨t, htX⟩ * ⟨t, htX⟩ : ↥X) = 1 := Subtype.ext ht2
    rw [this, map_one]
  have hv2 : π ⟨s, hsX⟩ * π ⟨s, hsX⟩ = 1 := by
    rw [← map_mul]
    have : (⟨s, hsX⟩ * ⟨s, hsX⟩ : ↥X) = 1 := Subtype.ext hs2
    rw [this, map_one]
  have huv : π ⟨t, htX⟩ ≠ π ⟨s, hsX⟩ := by
    intro h
    have h1 : π (⟨t, htX⟩⁻¹ * ⟨s, hsX⟩) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    have h2 : t⁻¹ * s ∈ O := hker _ h1
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    rw [hti] at h2
    have h3 : t * s = 1 := eq_one_of_isPGroup_of_mem_odd hOodd h2
      (ExactLayer.isPGroup_zpowers_of_sq_eq_one hts2)
    exact hts ((eq_inv_of_mul_eq_one_right h3).trans hti).symm
  have hcomm : π ⟨t, htX⟩ * π ⟨s, hsX⟩ = π ⟨s, hsX⟩ * π ⟨t, htX⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg π (Subtype.ext hst)
  have hFgen := hgen
  have hŴtop : Ŵ = ⊤ := by
    rw [eq_top_iff, ← hFgen]
    refine sup_le (sup_le ?_ ?_) ?_
    · exact hcentW t htX ht2 hzt hHt
    · exact hcentW s hsX hs2 hzs hHs
    · have e : π ⟨t, htX⟩ * π ⟨s, hsX⟩ = π ⟨t * s, htsX⟩ := (map_mul π _ _).symm
      rw [e]
      exact hcentW (t * s) htsX hts2 hzts hHts
  have hX₁H : ∀ x ∈ X₁, x ∈ H := by
    intro x hx
    have hq : π ⟨x, hx.1⟩ ∈ Ŵ := hŴtop ▸ Subgroup.mem_top _
    obtain ⟨w, hwW, hw⟩ := hq
    have hwH : (w : G) ∈ H := (Subgroup.mem_subgroupOf.mp hwW).1
    have h1 : π (⟨x, hx.1⟩ * w⁻¹) = 1 := by rw [map_mul, map_inv, hw, mul_inv_cancel]
    have h2 : x * (w : G)⁻¹ ∈ O := hker _ h1
    have e : x = (x * (w : G)⁻¹) * (w : G) := by group
    rw [e]
    exact H.mul_mem (hO h2) hwH
  obtain ⟨gq, hgq⟩ := hq
  obtain ⟨x₁, hx₁, hπx₁⟩ := hlift gq
  have hx₁H : x₁ ∈ H := hX₁H x₁ hx₁
  have htX₁ : t ∈ X₁ := ⟨htX, Subgroup.mem_centralizer_singleton_iff.mpr hzt.symm⟩
  have hux : x₁ * t * x₁⁻¹ ∈ X₁ := X₁.mul_mem (X₁.mul_mem hx₁ htX₁) (X₁.inv_mem hx₁)
  have hπu : π ⟨x₁ * t * x₁⁻¹, hux.1⟩ = π ⟨t', ht'X⟩ := by
    have e : (⟨x₁ * t * x₁⁻¹, hux.1⟩ : ↥X) = ⟨x₁, hx₁.1⟩ * ⟨t, htX⟩ * ⟨x₁, hx₁.1⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hπx₁, ← hgq]
  have ht'X₁ : t' ∈ X₁ := ⟨ht'X, Subgroup.mem_centralizer_singleton_iff.mpr hzt'.symm⟩
  have hinv : (x₁ * t * x₁⁻¹)⁻¹ * t' ∈ O ⊓ Subgroup.centralizer ({z} : Set G) := by
    refine ⟨?_, (X₁.mul_mem (X₁.inv_mem hux) ht'X₁).2⟩
    have h1 : π ((⟨x₁ * t * x₁⁻¹, hux.1⟩ : ↥X)⁻¹ * ⟨t', ht'X⟩) = 1 := by
      rw [map_mul, map_inv, hπu, inv_mul_cancel]
    exact hker _ h1
  have hu2' : (x₁ * t * x₁⁻¹) * (x₁ * t * x₁⁻¹) = 1 := by
    calc x₁ * t * x₁⁻¹ * (x₁ * t * x₁⁻¹) = x₁ * (t * t) * x₁⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  obtain ⟨ν, hν, hνe⟩ := CFSG.ClassicalInvolution.Q3.Q3T8.AF.exists_conj_of_inv_mul_mem hu2' ht'2
    hOodd₁ hinv
  refine ⟨ν * x₁, H.mul_mem (hO hν.1) hx₁H, ?_, ?_⟩
  · calc ν * x₁ * z * (ν * x₁)⁻¹ = ν * (x₁ * z * x₁⁻¹) * ν⁻¹ := by group
      _ = ν * z * ν⁻¹ := by rw [hCz x₁ hx₁.2]
      _ = z := hCz ν hν.2
  · calc ν * x₁ * t * (ν * x₁)⁻¹ = ν * (x₁ * t * x₁⁻¹) * ν⁻¹ := by group
      _ = t' := hνe.symm

theorem link_conj_of_modelFacts {X Λ H : Subgroup G} (hXΛ : X ≤ Λ)
    (hΛ : Λ ≤ Subgroup.normalizer (X : Set G)) {z t s t' : G} (hzΛ : z ∈ Λ) (hz2 : z * z = 1)
    (hzX : ∀ x ∈ X, ⁅x, z⁆ ∈ oddCoreOf X) (htX : t ∈ X) (hsX : s ∈ X) (ht'X : t' ∈ X)
    (ht2 : t * t = 1) (hs2 : s * s = 1) (ht'2 : t' * t' = 1) (ht1 : t ≠ 1) (hs1 : s ≠ 1)
    (ht'1 : t' ≠ 1) (hts : t ≠ s) (hzt : z * t = t * z) (hzs : z * s = s * z)
    (hzt' : z * t' = t' * z) (hst : t * s = s * t) (hO : oddCoreOf X ≤ H)
    (hHt : Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({t} : Set G) ≤ H)
    (hHs : Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({s} : Set G) ≤ H)
    (hHts : Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({t * s} : Set G) ≤ H)
    (hF : LinkModelFacts (↥X ⧸ classicalInvolutionOddCore ↥X)) :
    ∃ y ∈ H, y * z * y⁻¹ = z ∧ y * t * y⁻¹ = t' := by
  classical
  have hOodd : Odd (Nat.card (oddCoreOf X)) := oddCoreOf_odd_natCard X
  set π : ↥X →* (↥X ⧸ classicalInvolutionOddCore ↥X) :=
    QuotientGroup.mk' (classicalInvolutionOddCore ↥X) with hπ
  have hker : ∀ a : ↥X, π a = 1 → (a : G) ∈ oddCoreOf X := fun a h =>
    mem_oddCoreOf_iff.mpr ⟨a.2, (QuotientGroup.eq_one_iff _).mp h⟩
  have hnot : ∀ c : G, c * c = 1 → c ≠ 1 → ∀ hcX : c ∈ X, π ⟨c, hcX⟩ ≠ 1 := by
    intro c hc2 hc1 hcX h
    exact hc1 (eq_one_of_isPGroup_of_mem_odd hOodd (hker _ h)
      (ExactLayer.isPGroup_zpowers_of_sq_eq_one hc2))
  have hsq : ∀ c : G, c * c = 1 → ∀ hcX : c ∈ X, π ⟨c, hcX⟩ * π ⟨c, hcX⟩ = 1 := by
    intro c hc2 hcX
    rw [← map_mul]
    have : (⟨c, hcX⟩ * ⟨c, hcX⟩ : ↥X) = 1 := Subtype.ext hc2
    rw [this, map_one]
  have hts2 : (t * s) * (t * s) = 1 := by
    calc t * s * (t * s) = t * (s * t) * s := by group
      _ = t * (t * s) * s := by rw [← hst]
      _ = (t * t) * (s * s) := by group
      _ = 1 := by rw [ht2, hs2, one_mul]
  have huv : π ⟨t, htX⟩ ≠ π ⟨s, hsX⟩ := by
    intro h
    have h1 : π (⟨t, htX⟩⁻¹ * ⟨s, hsX⟩) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    have h2 : t⁻¹ * s ∈ oddCoreOf X := hker _ h1
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    rw [hti] at h2
    have h3 : t * s = 1 := eq_one_of_isPGroup_of_mem_odd hOodd h2
      (ExactLayer.isPGroup_zpowers_of_sq_eq_one hts2)
    exact hts ((eq_inv_of_mul_eq_one_right h3).trans hti).symm
  have hcomm : π ⟨t, htX⟩ * π ⟨s, hsX⟩ = π ⟨s, hsX⟩ * π ⟨t, htX⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg π (Subtype.ext hst)
  exact link_conj_of_frame hXΛ hΛ hzΛ hz2 hzX htX hsX ht'X ht2 hs2 ht'2 hts hzt hzs hzt' hst hO
    hHt hHs hHts
    (hF.1 _ _ (hsq t ht2 htX) (hnot t ht2 ht1 htX) (hsq t' ht'2 ht'X) (hnot t' ht'2 ht'1 ht'X))
    (hF.2 _ _ (hsq t ht2 htX) (hnot t ht2 ht1 htX) (hsq s hs2 hsX) (hnot s hs2 hs1 hsX) huv hcomm)

end Glue

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
