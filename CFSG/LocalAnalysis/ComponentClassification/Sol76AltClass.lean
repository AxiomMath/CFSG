module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78AltWide

public section

namespace CFSG.ComponentClassification.Sol76

open CFSG Subgroup FooteLit

variable {X : Type} [Group X]

theorem solomonLink_symm {L K : Subgroup X} (h : SolomonLink L K) : SolomonLink K L :=
  ⟨h.1.map MulEquiv.symm, h.2.symm⟩

theorem reflTransGen_solomonLink_symm {L K : Subgroup X}
    (h : Relation.ReflTransGen SolomonLink L K) : Relation.ReflTransGen SolomonLink K L :=
  by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hlink ih => exact Relation.ReflTransGen.head (solomonLink_symm hlink) ih

theorem nonempty_fusionZStar_equiv_of_reflTransGen {L K : Subgroup X}
    (h : Relation.ReflTransGen SolomonLink L K) :
    Nonempty (L ⧸ Open.fusionZStar L ≃* K ⧸ Open.fusionZStar K) := by
  induction h with
  | refl => exact ⟨MulEquiv.refl _⟩
  | tail _ hlink ih =>
    obtain ⟨e₁⟩ := ih
    obtain ⟨e₂⟩ := hlink.1
    exact ⟨e₁.trans e₂⟩

theorem isSolomonMember_of_reflTransGen {L K : Subgroup X} (hL : IsSolomonMember L)
    (h : Relation.ReflTransGen SolomonLink L K) : IsSolomonMember K := by
  induction h with
  | refl => exact hL
  | tail _ hlink _ =>
    rcases hlink.2 with h | h
    · exact h.2.1
    · exact h.1

theorem mem_solomonKStar_of_solomonEquiv {L K : Subgroup X} (hL : L ∈ solomonKStar X)
    (h : SolomonEquiv L K) : K ∈ solomonKStar X := by
  have hK := isSolomonMember_of_reflTransGen h.1 h.2
  have hKL := reflTransGen_solomonLink_symm h.2
  refine ⟨⟨hK, fun K' K₁ hK' hlt => ?_⟩, ⟨hK, fun K' hK' => ?_⟩⟩
  · exact ⟨hK, hKL.trans (hL.1.2 K' K₁ ⟨hL.1.1, h.2.trans hK'.2⟩ hlt).2⟩
  · exact hL.2.2 K' ⟨hL.1.1, h.2.trans hK'.2⟩

variable [Finite X]

theorem three_le_pRank_of_solomonEquiv (hS : SolAltLit.SchurAlternatingMultiplierInput)
    {L K : Subgroup X} (h : SolomonEquiv L K) {n : ℕ} (hn : 8 ≤ n)
    (e : L ⧸ Open.fusionZStar L ≃* alternatingGroup (Fin n)) : 3 ≤ CFSG.pRank 2 K := by
  obtain ⟨e'⟩ := nonempty_fusionZStar_equiv_of_reflTransGen h.2
  have hK := isSolomonMember_of_reflTransGen h.1 h.2
  have : Group.IsPerfect K := Subgroup.isPerfect_iff.mpr hK.1
  exact Sol78.three_le_pRank_of_fusionZStar hS hn (e'.symm.trans e)

theorem isSolomonWide_of_fusionZStar (hS : SolAltLit.SchurAlternatingMultiplierInput)
    {L : Subgroup X} (hL : IsSolomonMember L) {n : ℕ} (hn : 8 ≤ n)
    (e : L ⧸ Open.fusionZStar L ≃* alternatingGroup (Fin n)) : IsSolomonWide L :=
  ⟨hL, fun _ hK => le_trans (by norm_num) (three_le_pRank_of_solomonEquiv hS hK hn e)⟩

theorem isSolomonMember_of_isTwoComponentIn_centralizer {y : X} (hy : orderOf y = 2)
    {K : Subgroup X} (hK : IsTwoComponentIn K (centralizer ({y} : Set X))) :
    IsSolomonMember K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hKC, hKp⟩ := hK
  set C := centralizer ({y} : Set X) with hC
  have hCT : centralizer ((zpowers y : Subgroup X) : Set X) = C := by
    rw [zpowers_eq_closure, centralizer_closure]
  have hKinf : K ⊓ C = K := inf_eq_left.mpr hKC
  refine ⟨UnbalancedCorr.commutator_eq_of_isPComponent hKC hKp, zpowers y, ?_, ?_, ?_, ?_⟩
  · intro h
    rw [zpowers_eq_bot] at h
    rw [h, orderOf_one] at hy
    norm_num at hy
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  · rw [zpowers_le]
    exact Sol78.mem_coreActionKernel_of_commute fun k hk =>
      mem_centralizer_singleton_iff.mp (hKC hk)
  · rw [hCT, hKinf, Sol78.oddResidualIn_eq_oPrimeResidualOf]
    change GH74.GLS.IsPCompIn 2 C (GH74.GLS.oPrimeResidualOf 2 (GH74.GLS.pPrimeCoreOf 2 C ⊔ K))
    rw [Sol78.oPrimeResidualOf_core_sup_eq hKC hKp]
    exact ⟨hKC, hKp⟩

theorem twoLayerIn_eq_self_of_isTwoComponentIn {K C : Subgroup X} (hK : IsTwoComponentIn K C) :
    twoLayerIn K = K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKK : IsPComponent 2 (K.subgroupOf K) :=
    CatalogueBPrimeJoin.pComponent_subgroupOf_of_le le_rfl hK.1 hK.2
  rw [subgroupOf_self] at hKK
  have htop : pLayer ↥K 2 = ⊤ := eq_top_iff.mpr (le_sSup hKK)
  rw [twoLayerIn, htop, ← MonoidHom.range_eq_map, range_subtype]

end CFSG.ComponentClassification.Sol76
