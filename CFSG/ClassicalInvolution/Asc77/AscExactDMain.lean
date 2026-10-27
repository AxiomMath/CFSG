module

public import CFSG.ClassicalInvolution.Asc77.AscExactDCover
public import CFSG.ClassicalInvolution.Asc77.WP2Stand

public section

open scoped commutatorElement MatrixGroups Pointwise

namespace CFSG.ClassicalInvolution.Asc77.ExactD

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ComponentClassification

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K K' : Subgroup G} {z : G}

omit [Fact p.Prime] in
theorem commutator_oddCore_centralizer_le_alphaOf {c : G} (hc1 : c ≠ 1) (A₀ : Subgroup G)
    (hcA : c ∈ A₀) :
    ⁅oddCoreOf (Subgroup.centralizer ({c} : Set G)), A₀⁆ ≤ alphaOf A₀ := by
  unfold alphaOf
  exact le_sup_of_le_left (le_iSup₂_of_le c hcA (le_iSup_of_le hc1 le_rfl))

namespace TwinPair

variable [Finite G] (d : TwinPair p f Ω K K' z)
include d

omit [Finite G] in
theorem isSubnormal : IsSubnormal K (Subgroup.centralizer ({z} : Set G)) := by
  obtain ⟨z', hz'⟩ := d.hyp.classical K d.mem
  have hz'2 : z' * z' = 1 := by
    have := pow_orderOf_eq_one z'
    rw [hz'.orderOf_eq_two] at this
    simpa [sq] using this
  have hz'1 : z' ≠ 1 := by
    intro h
    have := hz'.orderOf_eq_two
    rw [h] at this
    simp at this
  rcases d.hz.unique z' hz'.mem hz'2 with h | h
  · exact absurd h hz'1
  · rw [← h]
    exact hz'.subnormal

theorem oddProd_le_centralizer_of_alphaOf_bot {u : G}
    (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥) :
    oddProd K K' ≤ Subgroup.centralizer ({u} : Set G) := by
  set A₀ : Subgroup G := Subgroup.closure ({u, z} : Set G) with hA₀
  have hzA : z ∈ A₀ := Subgroup.subset_closure (by simp)
  have huA : u ∈ A₀ := Subgroup.subset_closure (by simp)
  have hcomm := commutator_oddCore_centralizer_le_alphaOf d.hz.ne_one A₀ hzA
  rw [hα] at hcomm
  have hcent : ∀ {L : Subgroup G}, IsSubnormal L (Subgroup.centralizer ({z} : Set G)) →
      oddCoreOf L ≤ Subgroup.centralizer ({u} : Set G) := by
    intro L hL n hn
    have hn' : n ∈ oddCoreOf (Subgroup.centralizer ({z} : Set G)) :=
      Balance.oddCoreIn_le_of_isSubnormal hL hn
    have h1 : ⁅n, u⁆ ∈ ⁅oddCoreOf (Subgroup.centralizer ({z} : Set G)), A₀⁆ :=
      Subgroup.commutator_mem_commutator hn' huA
    have h2 : ⁅n, u⁆ = 1 := Subgroup.mem_bot.mp (hcomm h1)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact commutatorElement_eq_one_iff_mul_comm.mp h2
  exact sup_le (hcent d.isSubnormal) (hcent d.symm.isSubnormal)

theorem sup_le_centralizer_of_alphaOf_bot {u : G} (hu : u ∈ K ⊔ K') (hu2 : u * u = 1)
    (hu1 : u ≠ 1) (huz : u ≠ z) (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥) :
    K ⊔ K' ≤ Subgroup.centralizer (oddProd K K' : Set G) :=
  d.sup_le_centralizer_oddProd hu hu2 hu1 huz (d.oddProd_le_centralizer_of_alphaOf_bot hα)

theorem oddCoreOf_le_centralizer_of_alphaOf_bot {u : G} (hu : u ∈ K ⊔ K') (hu2 : u * u = 1)
    (hu1 : u ≠ 1) (huz : u ≠ z) (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥) :
    oddCoreOf K ≤ Subgroup.centralizer (K : Set G) := by
  intro n hn
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have h := d.sup_le_centralizer_of_alphaOf_bot hu hu2 hu1 huz hα (Subgroup.mem_sup_left hk)
  exact (Subgroup.mem_centralizer_iff.mp h n (Subgroup.mem_sup_left hn)).symm

theorem oddCoreOf_le_centralizer_of_alphaOf_bot' {u : G} (hu : u ∈ K ⊔ K') (hu2 : u * u = 1)
    (hu1 : u ≠ 1) (huz : u ≠ z) (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥) :
    oddCoreOf K' ≤ Subgroup.centralizer (K' : Set G) := by
  intro n hn
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have h := d.sup_le_centralizer_of_alphaOf_bot hu hu2 hu1 huz hα (Subgroup.mem_sup_right hk)
  exact (Subgroup.mem_centralizer_iff.mp h n (Subgroup.mem_sup_right hn)).symm

omit [Finite G] in
theorem isQuasisimple_of_oddCoreOf_le_centralizer
    (hc : oddCoreOf K ≤ Subgroup.centralizer (K : Set G)) : CFSG.Open.IsQuasisimple K := by
  obtain ⟨z₀, hz₀⟩ := d.hyp.classical K d.mem
  obtain ⟨e⟩ := hz₀.nonempty_equiv
  have hKq : CFSG.Open.IsQuasisimple (K ⧸ componentClassificationOddCore K) :=
    Components.quasisimple_of_equiv e d.isQuasisimple_sl2
  have : Group.IsPerfect K := hz₀.perfect
  refine CentralExtensions.quasisimple_of_surjective hKq (QuotientGroup.mk' _)
    (QuotientGroup.mk'_surjective _) ?_
  rw [QuotientGroup.ker_mk']
  intro o ho
  rw [Subgroup.mem_center_iff]
  intro k
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hc ⟨o, ho, rfl⟩) k k.2)

theorem isQuasisimple_of_alphaOf_bot {u : G} (hu : u ∈ K ⊔ K') (hu2 : u * u = 1)
    (hu1 : u ≠ 1) (huz : u ≠ z) (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥) :
    CFSG.Open.IsQuasisimple K :=
  d.isQuasisimple_of_oddCoreOf_le_centralizer
    (d.oddCoreOf_le_centralizer_of_alphaOf_bot hu hu2 hu1 huz hα)

end TwinPair

theorem exactMembers_of_alphaOf_twin [Finite G] (d : TwinPair p f Ω K K' z) (h9 : p ^ f ≠ 9)
    (hΩ : InClass p f Ω) (hsingle : ∃ L ∈ Ω, ∀ M ∈ Ω, ∃ g : G, M = conjSub g L) {u : G}
    (hu : u ∈ K ⊔ K') (hu2 : u * u = 1) (hu1 : u ≠ 1) (huz : u ≠ z)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥) : ExactMembers Ω := by
  have hf : 0 < f := Nat.pos_of_ne_zero (by rintro rfl; simpa using d.five)
  exact Balance.exactMembers_of_isQuasisimple d.odd hf h9 hΩ hsingle d.mem
    (d.isQuasisimple_of_alphaOf_bot hu hu2 hu1 huz hα)

theorem exactMembers_of_alphaOf_twin_stand [Finite G] (hst : AscStand p f Ω K) (h9 : p ^ f ≠ 9)
    (hz : IsUniqueInvolution K z) (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K) {u : G}
    (hu : u ∈ K ⊔ K') (hu2 : u * u = 1) (hu1 : u ≠ 1) (huz : u ≠ z)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥) : ExactMembers Ω :=
  exactMembers_of_alphaOf_twin
    (TwinPair.of_twinSet hst.odd hst.five hst.hyp hst.mem hz hK' hne.symm) h9
    ⟨⟨K, hst.mem⟩, hst.hyp.conjInvariant, hst.gen, hst.hyp.classical⟩
    ⟨K, hst.mem, fun M hM => by
      obtain ⟨g, hg⟩ := hst.trans M hM
      exact ⟨g, hg.symm⟩⟩ hu hu2 hu1 huz hα

end CFSG.ClassicalInvolution.Asc77.ExactD
