module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76S5Sub
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicOddCoreBasic
public import CFSG.Quasithin.EmptyFaithful.S14110AuxCommuteSub
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Sporadic.Schreier.J4SSylowBase
public import CFSG.Walter.AStar.Subnormal

public noncomputable section

namespace CFSG.ComponentClassification.Sol78.F514

open CFSG Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.Asc76 CFSG.ComponentClassification.Asc76.Sec5 CFSG.Open
  CFSG.ComponentClassification.RankTwoSporadic

variable {Y : Type} [Group Y] [Finite Y]

theorem isSubnormal_ncChain (K₀ : Subgroup Y) : ∀ n, (ncChain K₀ n).IsSubnormal
  | 0 => by rw [ncChain_zero]; exact IsSubnormal.top
  | n + 1 => IsSubnormal.step _ _ (ncChain_succ_le K₀ n) (isSubnormal_ncChain K₀ n)
      ((normal_subgroupOf_iff_le_normalizer (ncChain_succ_le K₀ n)).mpr
        (ncChain_le_normalizer_succ K₀ n))

omit [Finite Y] in
theorem isPGroup_normalClosure {U : Subgroup Y} (hU : IsPGroup 2 U)
    (hc : IsMulCommutative (normalClosure (U : Set Y))) :
    IsPGroup 2 (normalClosure (U : Set Y)) := by
  have key : ∀ x ∈ normalClosure (U : Set Y), ∃ k : ℕ, x ^ 2 ^ k = 1 := by
    intro x hx
    induction hx using closure_induction with
    | mem x hx =>
      obtain ⟨a, ha, hc⟩ := Group.mem_conjugatesOfSet_iff.mp hx
      obtain ⟨g, rfl⟩ := isConj_iff.mp hc
      obtain ⟨k, hk⟩ := hU ⟨a, ha⟩
      refine ⟨k, ?_⟩
      have h1 : a ^ 2 ^ k = 1 := by
        have := congrArg Subtype.val hk
        rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
      rw [conj_pow, h1, mul_one, mul_inv_cancel]
    | one => exact ⟨0, one_pow _⟩
    | mul x y hx hy ihx ihy =>
      obtain ⟨a, ha⟩ := ihx
      obtain ⟨b, hb⟩ := ihy
      have hxy : x * y = y * x := by
        have := hc.1.comm ⟨x, hx⟩ ⟨y, hy⟩
        exact congrArg Subtype.val this
      refine ⟨a + b, ?_⟩
      rw [(show Commute x y from hxy).mul_pow, pow_add, pow_mul, ha, one_pow, one_mul,
        mul_comm (2 ^ a) (2 ^ b), pow_mul, hb, one_pow]
    | inv x hx ih =>
      obtain ⟨a, ha⟩ := ih
      exact ⟨a, by rw [inv_pow, ha, inv_one]⟩
  intro x
  obtain ⟨k, hk⟩ := key x x.2
  exact ⟨k, Subtype.ext (by rw [Subgroup.coe_pow, hk, Subgroup.coe_one])⟩

omit [Finite Y] in
theorem pPrimeCore_eq_top_of_odd {X : Type*} [Group X] (h : Odd (Nat.card X)) :
    pPrimeCore 2 X = ⊤ :=
  eq_top_iff.mpr (le_sSup ⟨inferInstance, by rw [card_top]; exact Nat.coprime_two_left.mpr h⟩)

theorem le_standardComponentOddCore_of_isSubnormal {W : Subgroup Y} (hW : W.IsSubnormal)
    (hodd : Odd (Nat.card W)) : W ≤ standardComponentOddCore Y := by
  have h1 := Walter.map_pPrimeCore_le_of_isSubnormal hW
  rw [pPrimeCore_eq_top_of_odd hodd, Subgroup.map_top, range_subtype] at h1
  exact h1.trans (le_standardComponentOddCore pPrimeCore_normal
    (Nat.coprime_two_left.mp pPrimeCore_coprime_card))

omit [Finite Y] in
theorem exists_mul_self_ne_one_of_dihedral {R : Subgroup Y}
    (hRd : AschbacherTheorem3.IsDihedralTwoGroup R) (h4 : 4 < Nat.card R) :
    ∃ u ∈ R, u * u ≠ 1 := by
  obtain ⟨k, hk, ⟨e⟩⟩ := hRd
  have hcard : Nat.card R = 2 * 2 ^ (k - 1) := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hm : 2 < 2 ^ (k - 1) := by omega
  have : NeZero (2 ^ (k - 1)) := ⟨by positivity⟩
  refine ⟨e.symm (DihedralGroup.r 1), (e.symm (DihedralGroup.r 1)).2, fun h => ?_⟩
  have h1 : (e.symm (DihedralGroup.r 1)) ^ 2 = 1 := Subtype.ext (by rw [sq]; exact h)
  have h2 := orderOf_dvd_of_pow_eq_one h1
  rw [MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  omega

theorem exists_mem_pCore (h3 : Asc76Theorem3Large) {K R W : Subgroup Y}
    (hO : standardComponentOddCore Y = ⊥) (hK : TightlyEmbedded K) (hR : IsSylowOf 2 R K)
    (hRd : AschbacherTheorem3.IsDihedralTwoGroup R) (h4 : 4 < Nat.card R)
    (hWK : W ≤ K) (hKW : K ≤ normalizer (W : Set Y)) (hWodd : Odd (Nat.card W))
    (hKRW : K ≤ R ⊔ W) :
    ∃ u ∈ R, u ∈ CFSG.Open.pCore 2 Y ∧ u * u ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := exists_ncChain_succ_eq K
  set H := ncChain K n with hH
  have hst : ncIn K H = H := hn
  have hKH : K ≤ H := le_ncChain K n
  have hRH : R ≤ H := hR.le.trans hKH
  have hHs : H.IsSubnormal := isSubnormal_ncChain K n
  have hK' : TightlyEmbedded (K.subgroupOf H) := tightlyEmbedded_subgroupOf hK hKH
  have hG' : normalClosure ((K.subgroupOf H : Subgroup H) : Set H) = ⊤ :=
    normalClosure_subgroupOf_eq_top hKH hst
  have hO' : standardComponentOddCore H = ⊥ :=
    standardComponentOddCore_eq_bot_of (eq_bot_of_odd_of_le_ncChain K hO n)
  have hR' : IsSylowOf 2 (R.subgroupOf H) (K.subgroupOf H) :=
    (isSylowOf_subgroupOf_iff hRH hKH).mpr hR
  have hRd' : AschbacherTheorem3.IsDihedralTwoGroup (R.subgroupOf H) := by
    obtain ⟨k, hk, ⟨e⟩⟩ := hRd
    exact ⟨k, hk, ⟨(subgroupOfEquivOfLe hRH).trans e⟩⟩
  have hcardR' : Nat.card (R.subgroupOf H) = Nat.card R := card_subgroupOf hRH
  rcases h3 H (K.subgroupOf H) hK' hG' hO' (R.subgroupOf H) hR' hRd' (by rw [hcardR']; exact h4)
    with hn' | ⟨-, h4', -⟩ | ⟨U, hUR, hUc, hUidx, hUab⟩
  ·
    have hKs : K.IsSubnormal := IsSubnormal.step K H hKH hHs hn'
    have hWs : W.IsSubnormal := IsSubnormal.step W K hWK hKs
      ((normal_subgroupOf_iff_le_normalizer hWK).mpr hKW)
    have hW1 : W = ⊥ := by
      have h1 := le_standardComponentOddCore_of_isSubnormal hWs hWodd
      rwa [hO, le_bot_iff] at h1
    have hKR : K ≤ R := by rw [hW1, sup_bot_eq] at hKRW; exact hKRW
    have hKp : K ≤ CFSG.Open.pCore 2 Y :=
      Quasithin.S14110.Commute.le_pCore_of_isSubnormal 2 hKs le_rfl
        (by rw [subgroupOf_self]; exact Subgroup.normal_top) (hR.isPGroup.to_le hKR)
    obtain ⟨u, huR, hu⟩ := exists_mul_self_ne_one_of_dihedral hRd h4
    exact ⟨u, huR, hKp (hR.le huR), hu⟩
  · rw [hcardR'] at h4'
    omega
  ·
    have hUp : IsPGroup 2 U := hR'.isPGroup.to_le hUR
    set X := normalClosure (U : Set H) with hX
    have hXp : IsPGroup 2 X := isPGroup_normalClosure hUp hUab
    have hXn : X.Normal := normalClosure_normal
    have hX' : (X.map H.subtype).subgroupOf H = X :=
      comap_map_eq_self_of_injective H.subtype_injective X
    have hXY : X.map H.subtype ≤ CFSG.Open.pCore 2 Y :=
      Quasithin.S14110.Commute.le_pCore_of_isSubnormal 2 hHs (map_subtype_le X)
        (by rw [hX']; exact hXn) (hXp.map H.subtype)
    obtain ⟨g, hg⟩ := hUc.exists_generator
    have hog : orderOf g = Nat.card U := orderOf_eq_card_of_forall_mem_zpowers hg
    have hcU : 2 * Nat.card U = Nat.card R := by
      have h1 := Subgroup.relIndex_mul_card U (R.subgroupOf H)
      rw [hUidx, inf_eq_left.mpr hUR, hcardR'] at h1
      exact h1
    refine ⟨((g : H) : Y), hUR g.2, hXY ⟨g, subset_normalClosure g.2, rfl⟩, fun h => ?_⟩
    have h1 : g ^ 2 = 1 := Subtype.ext (Subtype.ext (by rw [sq]; exact h))
    have h2 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h1)
    omega

end CFSG.ComponentClassification.Sol78.F514
