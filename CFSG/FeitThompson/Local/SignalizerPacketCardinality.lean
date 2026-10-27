module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.PacketConjugationDescription
import CFSG.FeitThompson.Local.SigmaOvergroupConjugacy
import CFSG.FeitThompson.Local.SignalizerCosetsDisjoint
import CFSG.FeitThompson.Local.SigmaCoreNontrivial
import CFSG.FeitThompson.OddOrder.MaximalSubgroupsSelfNormalizing
import CFSG.FeitThompson.OddOrder.SigmaCentralizerTransitivity
import CFSG.FeitThompson.Local.SigmaCoreConjugation

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise MulAction
open _root_.CFSG.FeitThompson

variable {G : Type*} [Group G]

theorem finsum_mem_const_nsmul {α : Type*} {M : Type*} [AddCommMonoid M] {s : Set α}
    (hs : s.Finite) (c : M) : ∑ᶠ _ ∈ s, c = s.ncard • c := by
  rw [finsum_mem_eq_finite_toFinset_sum _ hs, Finset.sum_const, Set.ncard_eq_toFinset_card s hs]

theorem finsum_ncard_sep_comm {α β : Type*} [Finite α] [Finite β] (s : Set α) (t : Set β)
    (r : α → β → Prop) :
    ∑ᶠ a ∈ s, {b ∈ t | r a b}.ncard = ∑ᶠ b ∈ t, {a ∈ s | r a b}.ncard := by
  classical
  have hs : s.Finite := Set.toFinite s
  have ht : t.Finite := Set.toFinite t
  have h1 : ∀ a : α, {b ∈ t | r a b}.ncard = (ht.toFinset.bipartiteAbove r a).card := by
    intro a
    rw [← Set.ncard_coe_finset]
    congr 1
    ext b
    simp [Finset.bipartiteAbove, ht.mem_toFinset]
  have h2 : ∀ b : β, {a ∈ s | r a b}.ncard = (hs.toFinset.bipartiteBelow r b).card := by
    intro b
    rw [← Set.ncard_coe_finset]
    congr 1
    ext a
    simp [Finset.bipartiteBelow, hs.mem_toFinset]
  rw [finsum_mem_eq_finite_toFinset_sum _ hs, finsum_mem_eq_finite_toFinset_sum _ ht]
  simp only [h1, h2]
  exact Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow r

theorem conjSub_eq_conjSubgroup (Y : Subgroup G) (g : G) :
    Prep09.conjSub g Y = Prep08.conjSubgroup Y g := (rfl)

theorem conjSubgroup_conjSubgroup (Y : Subgroup G) (g h : G) :
    Prep08.conjSubgroup (Prep08.conjSubgroup Y g) h = Prep08.conjSubgroup Y (g * h) := by
  ext x
  simp only [Prep08.mem_conjSubgroup_iff]
  rw [show g * h * x * (g * h)⁻¹ = g * (h * x * h⁻¹) * g⁻¹ from by group]

theorem isCoatom_conjSubgroup {M : Subgroup G} (hM : IsCoatom M) (g : G) :
    IsCoatom (Prep08.conjSubgroup M g) := isCoatom_conj_smul hM g⁻¹

theorem natCard_sigmaCore_conjSubgroup [Finite G] (M : Subgroup G) (g : G) :
    Nat.card ↥(sigmaCore (Prep08.conjSubgroup M g)) = Nat.card ↥(sigmaCore M) := by
  rw [Prep08.conjSubgroup, sigmaCore_conj_smul]
  exact (Nat.card_congr (Subgroup.equivSMul (MulAut.conj g⁻¹) (sigmaCore M)).toEquiv).symm

@[expose]
def conjugatesOfSubgroup (M : Subgroup G) : Set (Subgroup G) :=
  {T : Subgroup G | ∃ g : G, T = Prep08.conjSubgroup M g}

theorem mem_conjugatesOfSubgroup {M T : Subgroup G} :
    T ∈ conjugatesOfSubgroup M ↔ ∃ g : G, T = Prep08.conjSubgroup M g := Iff.rfl

theorem conjSubgroup_mem_conjugatesOfSubgroup (M : Subgroup G) (g : G) :
    Prep08.conjSubgroup M g ∈ conjugatesOfSubgroup M := ⟨g, rfl⟩

theorem self_mem_conjugatesOfSubgroup (M : Subgroup G) : M ∈ conjugatesOfSubgroup M :=
  ⟨1, by rw [Prep08.conjSubgroup_one]⟩

theorem isCoatom_of_mem_conjugatesOfSubgroup {M T : Subgroup G} (hM : IsCoatom M)
    (hT : T ∈ conjugatesOfSubgroup M) : IsCoatom T := by
  obtain ⟨g, rfl⟩ := hT; exact isCoatom_conjSubgroup hM g

theorem natCard_sigmaCore_of_mem_conjugatesOfSubgroup [Finite G] {M T : Subgroup G}
    (hT : T ∈ conjugatesOfSubgroup M) :
    Nat.card ↥(sigmaCore T) = Nat.card ↥(sigmaCore M) := by
  obtain ⟨g, rfl⟩ := hT; exact natCard_sigmaCore_conjSubgroup M g

theorem conjugatesOfSubgroup_conjSubgroup (M : Subgroup G) (g : G) :
    conjugatesOfSubgroup (Prep08.conjSubgroup M g) = conjugatesOfSubgroup M := by
  ext T
  simp only [mem_conjugatesOfSubgroup, conjSubgroup_conjSubgroup]
  exact ⟨fun ⟨h, hh⟩ => ⟨g * h, hh⟩, fun ⟨h, hh⟩ => ⟨g⁻¹ * h, by rw [hh, mul_inv_cancel_left]⟩⟩

theorem conjugatesOfSubgroup_eq_of_mem {M T : Subgroup G} (hT : T ∈ conjugatesOfSubgroup M) :
    conjugatesOfSubgroup T = conjugatesOfSubgroup M := by
  obtain ⟨g, rfl⟩ := hT; exact conjugatesOfSubgroup_conjSubgroup M g

theorem ncard_conjugatesOfSubgroup [Finite G] [IsSimpleGroup G] (hna : ¬ IsMulCommutative G)
    {M : Subgroup G} (hM : IsCoatom M) : (conjugatesOfSubgroup M).ncard = M.index := by
  have hstab : (MulAction.stabilizer (ConjAct G) M).comap
      (ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom = M := by
    ext g
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAction.mem_stabilizer_iff,
      Subgroup.conjAct_pointwise_smul_iff, normalizer_coe_eq_of_isCoatom hna hM]
  have hconj : ∀ Y : Subgroup G, ∀ g : G,
      Prep08.conjSubgroup Y g = ConjAct.toConjAct g⁻¹ • Y := by
    intro Y g
    ext x
    rw [Prep08.mem_conjSubgroup_iff, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [ConjAct.smul_def]
  have horb : conjugatesOfSubgroup M = MulAction.orbit (ConjAct G) M := by
    ext T
    refine ⟨?_, ?_⟩
    · rintro ⟨g, rfl⟩
      exact ⟨ConjAct.toConjAct g⁻¹, (hconj M g).symm⟩
    · rintro ⟨c, rfl⟩
      exact ⟨(ConjAct.ofConjAct c)⁻¹, by rw [hconj]; simp⟩
  rw [horb, ← MulAction.index_stabilizer]
  conv_rhs => rw [← hstab]
  rw [Subgroup.index_comap_of_surjective _ (ConjAct.toConjAct (G := G)).surjective]

@[expose]
def sigmaCoreSaturation (G : Type*) [Group G] [Finite G] (M : Subgroup G) : Set G :=
  ⋃ g : G, Prep08.conjSet ((sigmaCore M : Set G) \ {1}) g

theorem sigmaCoreSaturation_eq [Finite G] (M : Subgroup G) :
    sigmaCoreSaturation G M = ⋃ g : G, Prep08.conjSet ((sigmaCore M : Set G) \ {1}) g := (rfl)

theorem sigmaCoreSaturation_eq_biUnion [Finite G] (M : Subgroup G) :
    sigmaCoreSaturation G M = ⋃ T ∈ conjugatesOfSubgroup M, ((sigmaCore T : Set G) \ {1}) := by
  rw [sigmaCoreSaturation_eq]
  apply le_antisymm
  · refine Set.iUnion_subset fun g => ?_
    rw [conjSet_sdiff_one, ← coe_sigmaCore_conjSubgroup]
    exact Set.subset_biUnion_of_mem (s := conjugatesOfSubgroup M)
      (u := fun T : Subgroup G => (sigmaCore T : Set G) \ {1}) ⟨g, rfl⟩
  · refine Set.iUnion₂_subset fun T hT => ?_
    obtain ⟨g, rfl⟩ := hT
    refine Set.subset_iUnion_of_subset g ?_
    rw [conjSet_sdiff_one, ← coe_sigmaCore_conjSubgroup]

theorem mem_sigmaCoreSaturation [Finite G] {M : Subgroup G} {x : G} :
    x ∈ sigmaCoreSaturation G M ↔
      (∃ T ∈ conjugatesOfSubgroup M, x ∈ sigmaCore T) ∧ x ≠ 1 := by
  rw [sigmaCoreSaturation_eq_biUnion]
  simp only [Set.mem_iUnion, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe, exists_prop]
  aesop

theorem mem_sigmaSupport_of_mem_sigmaCoreSaturation [Finite G] {M : Subgroup G}
    (hM : IsCoatom M) {x : G} (hx : x ∈ sigmaCoreSaturation G M) : x ∈ sigmaSupport G := by
  obtain ⟨⟨T, hT, hxT⟩, hx1⟩ := mem_sigmaCoreSaturation.1 hx
  exact mem_sigmaSupport.2 ⟨T, isCoatom_of_mem_conjugatesOfSubgroup hM hT, hxT, hx1⟩

theorem sep_sigmaCoreSaturation_mem_sigmaCore [Finite G] {M T : Subgroup G}
    (hT : T ∈ conjugatesOfSubgroup M) :
    {x ∈ sigmaCoreSaturation G M | x ∈ sigmaCore T} = (sigmaCore T : Set G) \ {1} := by
  ext x
  constructor
  · rintro ⟨hx, hxT⟩
    exact ⟨hxT, (mem_sigmaCoreSaturation.1 hx).2⟩
  · rintro ⟨hxT, hx1⟩
    exact ⟨mem_sigmaCoreSaturation.2 ⟨⟨T, hT, hxT⟩, hx1⟩, hxT⟩

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open Subgroup Pointwise CFSG.FeitThompson
  CFSG.FeitThompson
  CFSG.FeitThompson.Prep08

universe u

theorem FTS_packet_cardinality
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FTS_canonical_signalizer_structure.{u})
    (h₃ : Statements.FTS_sigma_prime_separation.{u}) :
    Statements.FTS_packet_cardinality.{u} := by
  intro G _ _ hG M hM
  have hsimple : IsSimpleGroup G := hG.isSimpleGroup
  have hna := hG.not_isMulCommutative
  have hamb : IsFTAmbient G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable_of_ne_top⟩
  have hG09 : Prep09.IsMinimalSimpleOddOrder G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hfin : Fintype G := Fintype.ofFinite G
  have hG02 : IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  obtain ⟨hDunion, -, -, -, -⟩ := FTS_packet_conjugation_description h₂ h₃ G hG M hM
    (sigmaCoreSaturation G M) (sigmaCoreSaturation_eq M)
  have hdisj : (sigmaCoreSaturation G M).PairwiseDisjoint
      fun x : G => x • (sigmaCoreSignalizer G x : Set G) := by
    intro x hx y hy hxy
    have hx' := mem_sigmaSupport_of_mem_sigmaCoreSaturation hM hx
    have hy' := mem_sigmaSupport_of_mem_sigmaCoreSaturation hM hy
    have hd := FTS_signalizer_cosets_disjoint h₂ h₃ G hG09 x hx' y hy' hxy
    change Disjoint (x • (sigmaCoreSignalizer G x : Set G))
      (y • (sigmaCoreSignalizer G y : Set G))
    rw [Set.disjoint_iff_inter_eq_empty]
    simpa only [sigmaCoreSignalizer_eq_sigmaSignalizer] using hd
  have hcoset : ∀ x ∈ sigmaCoreSaturation G M, (x • (sigmaCoreSignalizer G x : Set G)).ncard
      = (sigmaSupportingMaximals (G := G) x).ncard := by
    intro x hx
    have hx' := mem_sigmaSupport_of_mem_sigmaCoreSaturation hM hx
    rw [Set.ncard_smul_set, sigmaCoreSignalizer_eq_sigmaSignalizer, ← Nat.card_coe_set_eq,
      SetLike.coe_sort_coe, (h₂ G hamb x hx').2.2.1, sigmaMultiplicity_eq_ncard]
  have hmult : ∀ x ∈ sigmaCoreSaturation G M, (sigmaSupportingMaximals (G := G) x).ncard
      = {T ∈ conjugatesOfSubgroup M | x ∈ sigmaCore T}.ncard := by
    intro x hx
    obtain ⟨⟨T, hT, hxT⟩, hx1⟩ := mem_sigmaCoreSaturation.1 hx
    have hTco : IsCoatom T := isCoatom_of_mem_conjugatesOfSubgroup hM hT
    have hoc := (FTS_sigma_overgroup_conjugacy h₃ G hG09 T hTco x hxT hx1).1
    congr 1
    ext N
    rw [mem_sigmaSupportingMaximals]
    constructor
    · rintro ⟨hNco, hxN⟩
      refine ⟨?_, hxN⟩
      have hNmem : N ∈ sigmaSupportingMaximals (G := G) x :=
        mem_sigmaSupportingMaximals.2 ⟨hNco, hxN⟩
      rw [hoc] at hNmem
      obtain ⟨g, rfl, -⟩ := hNmem
      rw [conjSub_eq_conjSubgroup, ← conjugatesOfSubgroup_eq_of_mem hT]
      exact ⟨g, rfl⟩
    · rintro ⟨hNc, hxN⟩
      exact ⟨isCoatom_of_mem_conjugatesOfSubgroup hM hNc, hxN⟩
  have hDcard : (sigmaPacketSupport G M).ncard
      = ∑ᶠ x ∈ sigmaCoreSaturation G M,
          {T ∈ conjugatesOfSubgroup M | x ∈ sigmaCore T}.ncard := by
    rw [hDunion, Set.Finite.ncard_biUnion (Set.toFinite _) (fun x _ => Set.toFinite _) hdisj]
    exact finsum_mem_congr rfl fun x hx => by rw [hcoset x hx, hmult x hx]
  have hswap : ∑ᶠ x ∈ sigmaCoreSaturation G M,
        {T ∈ conjugatesOfSubgroup M | x ∈ sigmaCore T}.ncard
      = ∑ᶠ T ∈ conjugatesOfSubgroup M,
          {x ∈ sigmaCoreSaturation G M | x ∈ sigmaCore T}.ncard :=
    finsum_ncard_sep_comm _ _ fun x T => x ∈ sigmaCore T
  have hcol : ∀ T ∈ conjugatesOfSubgroup M,
      {x ∈ sigmaCoreSaturation G M | x ∈ sigmaCore T}.ncard
        = Nat.card ↥(sigmaCore M) - 1 := by
    intro T hT
    rw [sep_sigmaCoreSaturation_mem_sigmaCore hT,
      Set.ncard_sdiff_singleton_of_mem (by simp), ← Nat.card_coe_set_eq, SetLike.coe_sort_coe,
      natCard_sigmaCore_of_mem_conjugatesOfSubgroup hT]
  have hcount : (sigmaPacketSupport G M).ncard = (Nat.card ↥(sigmaCore M) - 1) * M.index := by
    rw [hDcard, hswap, finsum_mem_congr rfl hcol,
      finsum_mem_const_nsmul (Set.toFinite (conjugatesOfSubgroup M)),
      ncard_conjugatesOfSubgroup hna hM, smul_eq_mul, Nat.mul_comm]
  refine ⟨hcount, Set.nonempty_of_ncard_ne_zero ?_⟩
  rw [hcount]
  have hSne : sigmaCore M ≠ ⊥ := (FBG_sigma_core_nontrivial h₁ G hG02 M hM).2
  have hS1 : 1 < Nat.card ↥(sigmaCore M) := (sigmaCore M).one_lt_card_iff_ne_bot.2 hSne
  exact Nat.mul_ne_zero (by omega) Subgroup.index_ne_zero_of_finite

end

end CFSG.FeitThompson.Proofs
