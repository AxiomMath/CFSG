module

public import CFSG.ClassicalInvolution.Q3.AE.Twins
public import CFSG.ClassicalInvolution.Q3.TL3T1
public import CFSG.ClassicalInvolution.Q3.TL4SepTwoB

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G] {Δ : Set (Subgroup G)}

theorem T4Hyp.isPGroup_of_all {r : ℕ} (h : T4Hyp r G Δ)
    (hall : ∀ K ∈ Δ, ∀ z : G, IsUniqueInvolution K z → TightInO2 z) {J : Subgroup G}
    (hJ : J ∈ Δ) : IsPGroup 2 J := by
  obtain ⟨⟨u, hu⟩, -⟩ := h.hyp.omega1 J hJ
  exact h.isPGroup_of_inO2 hJ hu (hall J hJ u hu)

omit [Finite G] in
theorem T4Hyp.card_eq_eight (h : T4Hyp 3 G Δ) {J : Subgroup G} (hJ : J ∈ Δ)
    (hJ2 : IsPGroup 2 J) : Nat.card J = 8 := by
  have hJS : IsSylow2In J J := ⟨le_rfl, hJ2, fun V' hV'J _ hJV' => le_antisymm hV'J hJV'⟩
  obtain ⟨e⟩ := h.quat J hJ J hJS
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  norm_num

theorem T4Hyp.mem_of_mem_normal_two (h : T4Hyp 3 G Δ) {J L : Subgroup G} (hJ : J ∈ Δ)
    (hL : L ∈ Δ) {u v : G} (hu : IsUniqueInvolution J u) (hv : IsUniqueInvolution L v)
    (hL2 : IsPGroup 2 L) (huv : u * v ≠ v * u) {T : Subgroup G} (hTn : T.Normal)
    (hT2 : IsPGroup 2 T) {x : G} (hxJ : x ∈ J) (hxT : x ∈ T) : x = 1 ∨ x = u := by
  by_cases h2 : 2 < Nat.card ↥(J ⊓ T)
  · exfalso
    have : T.Normal := hTn
    obtain ⟨S, hS⟩ := (IsPGroup.to_sup_of_normal_right hL2 hT2).exists_le_sylow
    obtain ⟨η, hη, hηS, hWab, -⟩ := exists_eta h.hyp S
    have hJS2 : 2 < Nat.card ↥(J ⊓ (S : Subgroup G)) :=
      lt_of_lt_of_le h2 (Subgroup.card_le_of_le (inf_le_inf_left J (le_sup_right.trans hS)))
    have hLS2 : 2 < Nat.card ↥(L ⊓ (S : Subgroup G)) := by
      rw [inf_eq_left.mpr (le_sup_left.trans hS), h.card_eq_eight hL hL2]
      norm_num
    obtain ⟨-, huW⟩ := h.mem_eta_of_two_lt hη hηS hJ hu hJS2
    obtain ⟨-, hvW⟩ := h.mem_eta_of_two_lt hη hηS hL hv hLS2
    exact huv (hWab u huW v hvW)
  · have hc2 : x * x = 1 := by
      have hpow : (⟨x, hxJ, hxT⟩ : ↥(J ⊓ T)) ^ Nat.card ↥(J ⊓ T) = 1 := pow_card_eq_one'
      have hpos : 0 < Nat.card ↥(J ⊓ T) := Nat.card_pos
      have hle : Nat.card ↥(J ⊓ T) ≤ 2 := not_lt.mp h2
      have hcp : x ^ Nat.card ↥(J ⊓ T) = 1 := by
        have := congrArg Subtype.val hpow
        simpa using this
      interval_cases hn : Nat.card ↥(J ⊓ T)
      · rw [pow_one] at hcp
        rw [hcp, one_mul]
      · rw [← pow_two]
        exact hcp
    exact hu.unique x hxJ hc2

theorem commutes_of_le_two (hΩ : HypOmegaGen Δ) (h2 : ∀ J ∈ Δ, IsPGroup 2 J)
    {A B : Subgroup G} (hA : A ∈ Δ) (hB : B ∈ Δ) (hne : A ≠ B) {P : Subgroup G}
    (hP : IsPGroup 2 P) (hAP : A ≤ P) (hBP : B ≤ P) : Commutes A B := by
  obtain ⟨S, hPS⟩ := hP.exists_le_sylow
  exact Q3CP.l67Gen G Δ hΩ S A (TC.mem_RSet_of_isPGroup hA (h2 A hA)) B
    (TC.mem_RSet_of_isPGroup hB (h2 B hB)) (hAP.trans hPS) (hBP.trans hPS) hne

theorem eq_of_map_le_memBar (hΩ : HypOmegaGen Δ) (h2 : ∀ J ∈ Δ, IsPGroup 2 J)
    {X : Subgroup G} {n : ℕ} (hn : 5 ≤ n) (φ : ↥X →* AE.AEQ n) (hk : IsPGroup 2 φ.ker)
    {L₁ L₂ : Subgroup G} (h₁ : L₁ ∈ Δ) (h₂ : L₂ ∈ Δ) (hL₁ : L₁ ≤ X) (hL₂ : L₂ ≤ X)
    {α : Finset (Fin n)} {h : α.card = 4} {b : Bool}
    (hlab : (L₁.subgroupOf X).map φ = AE.memBar α h b)
    (hle : (L₁.subgroupOf X).map φ ≤ (L₂.subgroupOf X).map φ) : L₁ = L₂ := by
  by_contra hne
  have hS2 : IsPGroup 2 ((L₂.subgroupOf X).map φ) :=
    ((h2 L₂ h₂).of_equiv (Subgroup.subgroupOfEquivOfLe hL₂).symm).map _
  have hQ2 : IsPGroup 2 ((((L₂.subgroupOf X).map φ).comap φ).map X.subtype) :=
    (hS2.comap_of_ker_isPGroup φ hk).map _
  have hLQ : ∀ {L : Subgroup G}, L ≤ X → (L.subgroupOf X).map φ ≤ (L₂.subgroupOf X).map φ →
      L ≤ (((L₂.subgroupOf X).map φ).comap φ).map X.subtype := by
    intro L hLX hLS l hl
    exact ⟨⟨l, hLX hl⟩, hLS ⟨⟨l, hLX hl⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩, rfl⟩
  have hc := commutes_of_le_two hΩ h2 h₁ h₂ hne hQ2 (hLQ hL₁ hle) (hLQ hL₂ le_rfl)
  obtain ⟨x, hx, x', hx', hxx'⟩ := AE.exists_not_comm_memBar hn α h b
  rw [← hlab] at hx hx'
  obtain ⟨⟨l, hlX⟩, hl, rfl⟩ := hx
  obtain ⟨⟨l', hl'X⟩, hl', hl'e⟩ := hle hx'
  apply hxx'
  rw [← hl'e, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hc l (Subgroup.mem_subgroupOf.mp hl) l' (Subgroup.mem_subgroupOf.mp hl'))

end CFSG.ClassicalInvolution.Q3.TL4
