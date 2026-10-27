module

public import CFSG.ClassicalInvolution.Q3.Q3YLie
public import CFSG.ClassicalInvolution.Q3.Q3ANbhd
public import CFSG.ClassicalInvolution.Q3.Q3TAxis

public section

namespace CFSG.ClassicalInvolution.Q3.Q3Y

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure
open CFSG.ClassicalInvolution.Balance (oddCoreIn odd_card_oddCoreIn oddCoreIn_le)

section Images

variable {G : Type} [Group G]

theorem modOddIn_conjSub (X : Subgroup G) (x : X) (M : Subgroup G) :
    modOddIn X (conjSub (x : G) M) =
      conjSub (QuotientGroup.mk' (classicalInvolutionOddCore ↥X) x) (modOddIn X M) := by
  unfold modOddIn
  rw [conjSub_map, conjSub_subgroupOf]

theorem conjSub_le_of_mem {X M : Subgroup G} (hMX : M ≤ X) {x : G} (hx : x ∈ X) :
    conjSub x M ≤ X := by
  intro y hy
  rw [mem_conjSub_iff] at hy
  have h1 := X.mul_mem (X.mul_mem hx (hMX hy)) (X.inv_mem hx)
  simpa [mul_assoc] using h1

theorem nbrSpan3_le_centralizingLayer {Ω : Set (Subgroup G)} {K : Subgroup G} {a : G}
    (ha : a ∈ K) : nbrSpan3 Ω K ≤ centralizingLayer Ω {a} := by
  refine iSup₂_le fun J hJ => ?_
  exact le_centralizingLayer (A := {a}) ⟨hJ.1, fun j hj =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hJ.2.2 a ha j hj).symm⟩

end Images

section Link

variable {G : Type} [Group G] [Finite G]

theorem involutionLink3_of_triangle {K : Subgroup G} {z : G} (hz : IsClassicalMember3 K z)
    (hΩ : InClass3 (conjClass3 K)) (hBelow : CIT3Below (Nat.card G))
    (hB : ¬ BootData3 (conjClass3 K)) (hA2 : ¬ A2Configuration z K)
    {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ : G}
    (htri : IsTriangle3 (conjClass3 K) K₁ K₂ K₃ z₁ z₂) {A : Subgroup G} (hA₁ : z₁ ∈ A)
    (hA₂ : z₂ ∈ A) (hA₃ : z₁ * z₂ ∈ A) :
    InvolutionLink3 (conjClass3 K) A {K₁, K₂, K₃} z₁ := by
  classical
  have hK₁ : IsClassicalMember3 K₁ z₁ := htri.edge.cls₁
  have hK₂ : IsClassicalMember3 K₂ z₂ := htri.edge.cls₂
  have hK₃ : IsClassicalMember3 K₃ (z₁ * z₂) := htri.cls₃
  have hz1sq : z₁ * z₁ = 1 := hK₁.isCentralInvolution.sq
  have hz2sq : z₂ * z₂ = 1 := hK₂.isCentralInvolution.sq
  have hz3sq : (z₁ * z₂) * (z₁ * z₂) = 1 := hK₃.isCentralInvolution.sq
  have hK₂nbr : K₂ ∈ nbrs3 (conjClass3 K) K₁ := by
    refine ⟨htri.edge.mem₂, fun h => htri.edge.ne ?_, htri.edge.comm⟩
    rw [h] at hK₂
    exact involution_unique3 hK₁ hK₂
  have hK₃nbr : K₃ ∈ nbrs3 (conjClass3 K) K₁ := by
    refine ⟨htri.mem₃, fun h => hK₂.ne_one ?_, htri.comm₁₃⟩
    rw [h] at hK₃
    have := involution_unique3 hK₁ hK₃
    simpa using this
  set X := nbrSpan3 (conjClass3 K) K₁ with hX
  have hz₂X : z₂ ∈ X := le_nbrSpan3 hK₂nbr hK₂.mem
  have hz₃X : z₁ * z₂ ∈ X := le_nbrSpan3 hK₃nbr hK₃.mem
  have hz₁X : z₁ ∈ X := by
    have := X.mul_mem hz₃X hz₂X
    simpa [mul_assoc, hz2sq] using this
  have hXY : X ≤ centralizingLayer (conjClass3 K) {z₁} :=
    nbrSpan3_le_centralizingLayer hK₁.mem
  obtain ⟨ι, -, ⟨D⟩⟩ := lieSystemMod3_nbrSpan3 hΩ hBelow hK₁ ⟨K₂, hK₂nbr⟩
  set ρ := QuotientGroup.mk' (classicalInvolutionOddCore ↥X) with hρ
  have hz1 : ρ ⟨z₁, hz₁X⟩ ≠ 1 := mk_ne_one_of_involution X hz₁X hz1sq hK₁.ne_one
  have hzc : ∀ x : ↥X ⧸ classicalInvolutionOddCore ↥X, x * ρ ⟨z₁, hz₁X⟩ = ρ ⟨z₁, hz₁X⟩ * x := by
    intro x
    obtain ⟨x', rfl⟩ := QuotientGroup.mk'_surjective _ x
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (nbrSpan3_le_centralizer (conjClass3 K) K₁ x'.2) z₁
      hK₁.mem).symm
  have hF : ∀ F : Subgroup (↥X ⧸ classicalInvolutionOddCore ↥X), IsElemAbelian 2 F →
      Nat.card F = 4 → ρ ⟨z₁, hz₁X⟩ ∈ F := fun F hF hc =>
    (nbhd_fourGroup_mem3 hB htri.edge.mem₁ hK₁ hF hc).2
  have hD1 : SingleClassComponents3 D := D.singleClassComponents3_of_central hz1 hzc hF
  have hK₂X : K₂ ≤ X := le_nbrSpan3 hK₂nbr
  have hz1z2 : (⟨z₁ * z₂, hz₃X⟩ : ↥X) = ⟨z₁, hz₁X⟩ * ⟨z₂, hz₂X⟩ := rfl
  intro M hM w hw
  by_cases hwz : w = z₁
  · exact ⟨K₁, by simp, z₁, hA₁, hK₁, 1, (centralizingLayer (conjClass3 K) {z₁}).one_mem,
      by simp [hwz]⟩
  have hwc : z₁ * w = w * z₁ :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hM.2 hw.mem)).symm
  have hcommM : Commutes K₁ M :=
    commutes_of_not_a2Configuration3 hz hA2 htri.edge.mem₁ hM.1 hK₁ hw (Ne.symm hwz) hwc
  have hMK₁ : M ≠ K₁ := by
    intro h
    rw [h] at hw
    exact hwz (involution_unique3 hw hK₁)
  have hMnbr : M ∈ nbrs3 (conjClass3 K) K₁ := ⟨hM.1, hMK₁, hcommM⟩
  have hMX : M ≤ X := le_nbrSpan3 hMnbr
  have hwX : w ∈ X := hMX hw.mem
  have hw2 : w * w = 1 := hw.isCentralInvolution.sq
  have hMΦ : modOddIn X M ∈ oddQuotientFamily
      {L' : Subgroup ↥X | ∃ L ∈ nbrs3 (conjClass3 K) K₁, L' = L.subgroupOf X} :=
    ⟨M.subgroupOf X, ⟨M, hMnbr, rfl⟩, rfl⟩
  have hK₂Φ : modOddIn X K₂ ∈ oddQuotientFamily
      {L' : Subgroup ↥X | ∃ L ∈ nbrs3 (conjClass3 K) K₁, L' = L.subgroupOf X} :=
    ⟨K₂.subgroupOf X, ⟨K₂, hK₂nbr, rfl⟩, rfl⟩
  have finish : ∀ (K' : Subgroup G) (z' : G), K' ∈ ({K₁, K₂, K₃} : Set (Subgroup G)) → z' ∈ A →
      IsClassicalMember3 K' z' → ∀ hz'X : z' ∈ X, z' * z' = 1 →
      ρ ⟨w, hwX⟩ = ρ ⟨z', hz'X⟩ →
      ∃ K'' ∈ ({K₁, K₂, K₃} : Set (Subgroup G)), ∃ z'' ∈ A, IsClassicalMember3 K'' z'' ∧
        ∃ h ∈ centralizingLayer (conjClass3 K) {z₁}, w = h * z'' * h⁻¹ := by
    intro K' z' hK'S hz'A hK'z' hz'X hz'2 hmk
    obtain ⟨o, ho, hoz⟩ := exists_conj_of_mk_eq X hwX hz'X hw2 hz'2 hmk
    refine ⟨K', hK'S, z', hz'A, hK'z', o⁻¹, hXY (X.inv_mem (oddCoreIn_le X ho)), ?_⟩
    rw [hoz]
    group
  by_cases hcm : ∀ a ∈ modOddIn X M, ∀ b ∈ modOddIn X K₂, a * b = b * a
  · have hwm : ρ ⟨w, hwX⟩ ∈ modOddIn X M :=
      ⟨⟨w, hwX⟩, Subgroup.mem_subgroupOf.mpr hw.mem, rfl⟩
    have hz2m : ρ ⟨z₂, hz₂X⟩ ∈ modOddIn X K₂ :=
      ⟨⟨z₂, hz₂X⟩, Subgroup.mem_subgroupOf.mpr hK₂.mem, rfl⟩
    have hcw := hcm _ hwm _ hz2m
    by_cases hwz2 : ρ ⟨w, hwX⟩ = ρ ⟨z₂, hz₂X⟩
    · exact finish K₂ z₂ (by simp) hA₂ hK₂ hz₂X hz2sq hwz2
    · have hwb1 : ρ ⟨w, hwX⟩ ≠ 1 := mk_ne_one_of_involution X hwX hw2 hw.ne_one
      have hz2b1 : ρ ⟨z₂, hz₂X⟩ ≠ 1 := mk_ne_one_of_involution X hz₂X hz2sq hK₂.ne_one
      have hsqw : ρ ⟨w, hwX⟩ * ρ ⟨w, hwX⟩ = 1 := by
        rw [← map_mul]
        have : (⟨w, hwX⟩ : ↥X) * ⟨w, hwX⟩ = 1 := Subtype.ext hw2
        rw [this, map_one]
      have hsq2 : ρ ⟨z₂, hz₂X⟩ * ρ ⟨z₂, hz₂X⟩ = 1 := by
        rw [← map_mul]
        have : (⟨z₂, hz₂X⟩ : ↥X) * ⟨z₂, hz₂X⟩ = 1 := Subtype.ext hz2sq
        rw [this, map_one]
      have hFe := isElemAbelian_closure_pair hsqw hsq2 hcw
      have hF4 : Nat.card (Subgroup.closure ({ρ ⟨w, hwX⟩, ρ ⟨z₂, hz₂X⟩} : Set _)) = 4 :=
        Balance.Bootstrap.card_closure_pair_eq_four hsqw hsq2 hwb1 hz2b1 hwz2 hcw
      have hz1F := hF _ hFe hF4
      have h3 : ρ ⟨z₁ * z₂, hz₃X⟩ = ρ ⟨z₁, hz₁X⟩ * ρ ⟨z₂, hz₂X⟩ := by rw [hz1z2, map_mul]
      rcases mem_closure_pair_cases hsqw hsq2 hcw hz1F with h | h | h | h
      · exact absurd h hz1
      · exact finish K₁ z₁ (by simp) hA₁ hK₁ hz₁X hz1sq h.symm
      · exfalso
        refine mk_ne_one_of_involution X hz₃X hz3sq hK₃.ne_one ?_
        rw [h3, h, hsq2]
      · refine finish K₃ (z₁ * z₂) (by simp) hA₃ hK₃ hz₃X hz3sq ?_
        rw [h3, h, mul_assoc, hsq2, mul_one]
  · obtain ⟨g, hg⟩ := D.exists_conj_of_not_commute hD1 hMΦ hK₂Φ hcm
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ g
    rw [← modOddIn_conjSub X x M] at hg
    have hxMX : conjSub (x : G) M ≤ X := conjSub_le_of_mem hMX x.2
    have hcl : IsClassicalMember3 (conjSub (x : G) M) (x * w * (x : G)⁻¹) := hw.conj (x : G)
    have hU : z₂ * ((x : G) * w * (x : G)⁻¹) ∈ oddCoreIn X :=
      mul_mem_oddCoreIn_of_modOddIn_eq3 hK₂ hcl hK₂X hxMX hg
    obtain ⟨o, ho, hoz⟩ := exists_conj_of_mul_mem hcl.isCentralInvolution.sq hz2sq
      (odd_card_oddCoreIn X) hU
    refine ⟨K₂, by simp, z₂, hA₂, hK₂, (o * x)⁻¹, ?_, ?_⟩
    · exact hXY (X.inv_mem (X.mul_mem (oddCoreIn_le X ho) x.2))
    · rw [hoz]
      group

end Link

end CFSG.ClassicalInvolution.Q3.Q3Y
