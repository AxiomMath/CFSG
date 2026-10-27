
module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks
public import CFSG.Quasithin.Background.C1GNC128

public section

namespace CFSG.QuasithinUnique

open CFSG.Quasithin CFSG.Open

namespace L246

variable {G : Type} [Group G]

theorem blockQ_eq_map (L : Subgroup G) : blockQ L = (CFSG.pCore 2 ↥L).map L.subtype := by
  unfold blockQ pCoreOf
  try with_reducible rfl

theorem mem_blockQ_iff {L : Subgroup G} (l : ↥L) : (l : G) ∈ blockQ L ↔ l ∈ CFSG.pCore 2 ↥L := by
  rw [blockQ_eq_map]
  exact Subgroup.mem_map_iff_mem (f := L.subtype) L.subtype_injective

section Kernel

variable [Finite G] {X T L : Subgroup G}

theorem pCoreOf_le_centralizer_VZ (hX : CharTwo X) (hT : IsSylowTwoOf T X) :
    pCoreOf 2 X ≤ Subgroup.centralizer (VZ T X : Set G) := by
  have hred : IsTwoReducedIn X (VZ T X) := C1GN.isTwoReducedIn_VZ hX hT
  refine hred.2.2.2 (pCoreOf 2 X) (CFSG.LieType.BorelTits.pCoreOf_le 2 X)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X) ?_
  intro d hd
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X ⟨d, hd⟩
  refine ⟨k, ?_⟩
  have h1 : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  rw [h1]
  exact Subgroup.one_mem _

theorem blockQ_le_centralizer_VZ (hX : CharTwo X) (hT : IsSylowTwoOf T X) (hL : IsBlock2 X L) :
    blockQ L ≤ Subgroup.centralizer (VZ T X : Set G) :=
  (A4.pCoreOf_le_of_subnormal 2 (C1GN.isSubnormal_of_isBlock2 hL)).trans
    (pCoreOf_le_centralizer_VZ hX hT)

theorem centralizer_subgroupOf_eq_pCore (hX : CharTwo X) (hT : IsSylowTwoOf T X) (hL : IsBlock2 X L)
    (hUV : blockU L ≤ VZ T X) :
    (Subgroup.centralizer (VZ T X : Set G)).subgroupOf L = CFSG.pCore 2 ↥L := by
  ext l
  rw [Subgroup.mem_subgroupOf, ← mem_blockQ_iff]
  constructor
  · intro hc
    refine C1.inf_centralizer_blockU_le hL.1 ⟨l.2, Subgroup.mem_centralizer_iff.2 fun u hu => ?_⟩
    exact Subgroup.mem_centralizer_iff.1 hc u (hUV hu)
  · intro hq
    exact blockQ_le_centralizer_VZ hX hT hL hq

theorem exists_alt_pCore (hX : CharTwo X) (hT : IsSylowTwoOf T X) (hL : IsBlock2 X L)
    (hUV : blockU L ≤ VZ T X) {m : ℕ}
    (h : IsAltQuotient L (Subgroup.centralizer (VZ T X : Set G)) m) :
    ∃ α : ↥L →* alternatingGroup (Fin m),
      Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥L := by
  obtain ⟨φ, hφ, hker⟩ := h
  exact ⟨φ, hφ, hker.trans (centralizer_subgroupOf_eq_pCore hX hT hL hUV)⟩

omit [Finite G] in
theorem card_quotient_pCore_of_alt {L : Subgroup G} {m : ℕ} (α : ↥L →* alternatingGroup (Fin m))
    (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥L) :
    Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = Nat.card (alternatingGroup (Fin m)) := by
  have e1 : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* (↥L ⧸ α.ker) := QuotientGroup.quotientMulEquivOfEq hker.symm
  exact Nat.card_congr (e1.trans (QuotientGroup.quotientKerEquivOfSurjective α hα)).toEquiv

theorem three_le_pRank_of_alt {L : Subgroup G} {m : ℕ} (hm : 9 ≤ m)
    (α : ↥L →* alternatingGroup (Fin m)) (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥L) : 3 ≤ CFSG.Open.pRank 3 L :=
  C1GN.le_pRank_three_of_alt_quotient α hα hker (CFSG.SectionRank.three_le_pRank_alternating hm)

end Kernel

end L246

end CFSG.QuasithinUnique
