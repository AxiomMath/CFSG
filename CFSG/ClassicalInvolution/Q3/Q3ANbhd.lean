module

public import CFSG.ClassicalInvolution.Q3.Q3ARank
public import CFSG.ClassicalInvolution.Balance.GoodDataBasic

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

section Vocabulary

variable {G : Type} [Group G]

@[expose] def nbrs3 (Ω : Set (Subgroup G)) (K : Subgroup G) : Set (Subgroup G) :=
  {J | J ∈ Ω ∧ J ≠ K ∧ Commutes K J}

@[expose] def nbrSpan3 (Ω : Set (Subgroup G)) (K : Subgroup G) : Subgroup G :=
  ⨆ J ∈ nbrs3 Ω K, J

variable {Ω : Set (Subgroup G)} {K J : Subgroup G}

theorem nbrs3_subset (Ω : Set (Subgroup G)) (K : Subgroup G) : nbrs3 Ω K ⊆ Ω := fun _ h => h.1

theorem le_nbrSpan3 (h : J ∈ nbrs3 Ω K) : J ≤ nbrSpan3 Ω K :=
  le_iSup₂ (f := fun (J : Subgroup G) (_ : J ∈ nbrs3 Ω K) => J) J h

theorem nbrs3_le_centralizer (h : J ∈ nbrs3 Ω K) : J ≤ Subgroup.centralizer (K : Set G) :=
  fun j hj => Subgroup.mem_centralizer_iff.mpr fun k hk => h.2.2 k hk j hj

theorem nbrSpan3_le_centralizer (Ω : Set (Subgroup G)) (K : Subgroup G) :
    nbrSpan3 Ω K ≤ Subgroup.centralizer (K : Set G) :=
  iSup₂_le fun _ h => nbrs3_le_centralizer h

theorem conjSub_eq_self_of_mem_centralizer {x : G} (hx : x ∈ Subgroup.centralizer (K : Set G)) :
    conjSub x K = K := by
  have hc : ∀ k ∈ K, k * x = x * k := fun k hk => Subgroup.mem_centralizer_iff.mp hx k hk
  ext y
  rw [mem_conjSub_iff]
  constructor
  · intro hy
    have h1 : (x⁻¹ * y * x) * x = y * x := by
      rw [hc _ hy]
      group
    have h2 : x⁻¹ * y * x = y := mul_right_cancel h1
    rwa [h2] at hy
  · intro hy
    have h1 : x⁻¹ * y * x = y := by
      have : y * x = x * y := hc y hy
      calc x⁻¹ * y * x = x⁻¹ * (y * x) := by rw [mul_assoc]
        _ = x⁻¹ * (x * y) := by rw [this]
        _ = y := by rw [← mul_assoc, inv_mul_cancel, one_mul]
    rwa [h1]

theorem conjSub_mem_nbrs3 (hΩ : ConjInvariant Ω) {x : G}
    (hx : x ∈ Subgroup.centralizer (K : Set G)) (h : J ∈ nbrs3 Ω K) :
    conjSub x J ∈ nbrs3 Ω K := by
  have hxK : conjSub x K = K := conjSub_eq_self_of_mem_centralizer hx
  have hxinv : x⁻¹ ∈ Subgroup.centralizer (K : Set G) := Subgroup.inv_mem _ hx
  refine ⟨hΩ x J h.1, ?_, ?_⟩
  · intro heq
    apply h.2.1
    calc J = conjSub x⁻¹ (conjSub x J) := (conjSub_inv_conjSub x J).symm
      _ = conjSub x⁻¹ K := by rw [heq]
      _ = K := conjSub_eq_self_of_mem_centralizer hxinv
  · have := h.2.2.conjSub x
    rwa [hxK] at this

end Vocabulary

section Class

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {K : Subgroup G}

theorem inClass3_nbrSpan3 (hΩ : InClass3 Ω) (hne : (nbrs3 Ω K).Nonempty) :
    InClass3 {L' : Subgroup ↥(nbrSpan3 Ω K) |
      ∃ L ∈ nbrs3 Ω K, L' = L.subgroupOf (nbrSpan3 Ω K)} :=
  inClass3_of_le hΩ (nbrs3_subset Ω K) (fun _ h => le_nbrSpan3 h) hne
    (fun h _ hL => conjSub_mem_nbrs3 hΩ.conjInvariant (nbrSpan3_le_centralizer Ω K h.2) hL) rfl

variable [Finite G]

omit [Finite G] in
theorem nbrSpan3_ne_top {z : G} (hz : IsClassicalMember3 K z) : nbrSpan3 Ω K ≠ ⊤ := by
  intro htop
  apply hz.not_le_center
  have h1 : Subgroup.centralizer (K : Set G) = ⊤ :=
    top_unique (htop ▸ nbrSpan3_le_centralizer Ω K)
  rw [Subgroup.centralizer_eq_top_iff_subset] at h1
  exact h1

theorem lieSystemMod3_nbrSpan3 {z : G} (hΩ : InClass3 Ω) (hBelow : CIT3Below (Nat.card G))
    (hz : IsClassicalMember3 K z) (hne : (nbrs3 Ω K).Nonempty) :
    LieSystemMod3 {L' : Subgroup ↥(nbrSpan3 Ω K) |
      ∃ L ∈ nbrs3 Ω K, L' = L.subgroupOf (nbrSpan3 Ω K)} :=
  hBelow _ (card_lt_of_ne_top (nbrSpan3_ne_top hz)) _ (inClass3_nbrSpan3 hΩ hne)

end Class

section FourGroups

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem nbhd_fourGroup_mem3 (hB : ¬ BootData3 Ω) {K : Subgroup G} {z : G} (hKΩ : K ∈ Ω)
    (hz : IsClassicalMember3 K z)
    {F : Subgroup (↥(nbrSpan3 Ω K) ⧸ classicalInvolutionOddCore ↥(nbrSpan3 Ω K))}
    (hF : IsElemAbelian 2 F) (hcard : Nat.card F = 4) :
    ∃ hzX : z ∈ nbrSpan3 Ω K,
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrSpan3 Ω K)) ⟨z, hzX⟩ ∈ F := by
  have hNodd : Odd (Nat.card (classicalInvolutionOddCore ↥(nbrSpan3 Ω K))) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥(nbrSpan3 Ω K)
  obtain ⟨H, hH, hHF, hHcard⟩ :=
    Balance.GoodData.exists_isElemAbelian_lift_map (classicalInvolutionOddCore ↥(nbrSpan3 Ω K))
      hNodd F hF
  have hH'card : Nat.card (H.map (nbrSpan3 Ω K).subtype) = 4 := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective (nbrSpan3 Ω K)), hHcard,
      hcard]
  have hsq : ∀ x ∈ H.map (nbrSpan3 Ω K).subtype, x * x = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have := hH.2 x hx
    rw [pow_two] at this
    exact congrArg Subtype.val this
  have hcomm : ∀ x ∈ H.map (nbrSpan3 Ω K).subtype, ∀ y ∈ H.map (nbrSpan3 Ω K).subtype,
      x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have := hH.1.is_comm.comm (⟨x, hx⟩ : H) ⟨y, hy⟩
    exact congrArg (fun t : H => ((t : ↥(nbrSpan3 Ω K)) : G)) this
  have hcent : K ≤ Subgroup.centralizer ((H.map (nbrSpan3 Ω K).subtype : Subgroup G) : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    have hxK : (x : G) ∈ Subgroup.centralizer (K : Set G) := nbrSpan3_le_centralizer Ω K x.2
    exact (Subgroup.mem_centralizer_iff.mp hxK k hk).symm
  have hzH' : z ∈ H.map (nbrSpan3 Ω K).subtype :=
    mem_fourGroup_of_not_bootData3 hB hKΩ hz hsq hcomm hH'card hcent
  obtain ⟨x, hxH, hxz⟩ := hzH'
  have hzX : z ∈ nbrSpan3 Ω K := by
    rw [← hxz]
    exact x.2
  refine ⟨hzX, ?_⟩
  have hx : x = ⟨z, hzX⟩ := Subtype.ext hxz
  rw [← hHF]
  exact ⟨x, hxH, by rw [hx]⟩

end FourGroups

section NoA2

variable {G : Type} [Group G]

@[expose] def NoA2InNbhd3 (Ω : Set (Subgroup G)) : Prop :=
  ∀ K ∈ Ω, ∀ J₁ ∈ nbrs3 Ω K, ∀ J₂ ∈ nbrs3 Ω K, ∀ z₁ z₂ : G, IsClassicalMember3 J₁ z₁ →
    IsClassicalMember3 J₂ z₂ → z₁ ≠ z₂ → z₁ * z₂ = z₂ * z₁ → Commutes J₁ J₂

theorem not_commonNbr_of_noA2InNbhd3 {Ω : Set (Subgroup G)} (hNA : NoA2InNbhd3 Ω)
    {K₁ K₂ M : Subgroup G} {z₁ z₂ : G} (h : IsA2Pair3 Ω K₁ K₂ z₁ z₂) (hM : M ∈ Ω)
    (h₁ : Commutes M K₁) (h₂ : Commutes M K₂) : False := by
  have hne₁ : K₁ ≠ M := by
    rintro rfl
    exact h.not_comm h₂
  have hne₂ : K₂ ≠ M := by
    rintro rfl
    exact h.not_comm h₁.symm
  exact h.not_comm (hNA M hM K₁ ⟨h.mem₁, hne₁, h₁⟩ K₂ ⟨h.mem₂, hne₂, h₂⟩ z₁ z₂ h.cls₁ h.cls₂
    h.ne h.comm_involutions)

end NoA2



end CFSG.ClassicalInvolution.Q3
