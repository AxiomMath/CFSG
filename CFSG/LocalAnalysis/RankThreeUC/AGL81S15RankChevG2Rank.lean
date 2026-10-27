module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTable
public import CFSG.Blueprint.Chevalley
public import CFSG.Open.StatedDefs
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankArith
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevToral
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevLin
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67A2Hom
import CFSG.LieType.Chevalley.GraphFixedF4GroupRestriction
import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
import CFSG.LargeExtraspecial.DWFldLinear
import CFSG.Open.StatedAPI
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.Reduction
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.LargeExtraspecial.Types
import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
import CFSG.RankThree.GroupTheory.ClassTwoThree
import CFSG.RankThree.OrthogonalInvolutions.SuzukiTypes
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Utils
import CFSG.Timmesfeld.Outcome

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.SectionRank in
theorem pRank_top_eq_of_injective_of_not_dvd_index {H G : Type*} [Group H] [Group G] [Finite H]
    [Finite G] {r : ℕ} [hr : Fact r.Prime] (f : H →* G) (hf : Function.Injective f)
    (hidx : ¬ r ∣ f.range.index) :
    CFSG.Open.pRank r (⊤ : Subgroup H) = CFSG.Open.pRank r (⊤ : Subgroup G) := by
  have hp1 : 1 < r := hr.out.one_lt
  refine le_antisymm (pRank_top_le_of_injective hp1 f hf) ?_
  obtain ⟨E, -, hE, hcard⟩ := exists_pRank hp1 (⊤ : Subgroup G)
  obtain ⟨Q₀⟩ := (inferInstance : Nonempty (Sylow r f.range))
  have hpQ : IsPGroup r (Q₀.map f.range.subtype) := Q₀.2.map f.range.subtype
  have hQ : ¬ r ∣ (Q₀.map f.range.subtype).index := by
    rw [Subgroup.index_map_subtype Q₀.1]
    exact Nat.Prime.not_dvd_mul hr.out Q₀.not_dvd_index hidx
  have hEp : IsPGroup r E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨S', hS'⟩ := hEp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (hpQ.toSylow hQ) S'
  have hmem : ∀ x : E, g⁻¹ * (x : G) * g ∈ f.range := by
    intro x
    have h1 : (x : G) ∈ ((g • hpQ.toSylow hQ : Sylow r G) : Subgroup G) := by
      rw [hg]
      exact hS' x.2
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
    have h2 : g⁻¹ * (x : G) * g ∈ Q₀.map f.range.subtype := by
      simpa [MulAut.smul_def] using h1
    obtain ⟨y, -, hy⟩ := h2
    rw [← hy]
    exact y.2
  let φ : E →* G := (MulAut.conj g⁻¹).toMonoidHom.comp E.subtype
  have hφapp : ∀ x : E, φ x = g⁻¹ * (x : G) * g := fun x => by
    simp [φ, MulAut.conj_apply]
  have hφinj : Function.Injective φ :=
    (MulAut.conj g⁻¹).injective.comp Subtype.val_injective
  have hrange : ∀ x : E, φ x ∈ f.range := fun x => by
    rw [hφapp]
    exact hmem x
  let ψ : E →* H := ((MonoidHom.ofInjective hf).symm : f.range ≃* H).toMonoidHom.comp
    (φ.codRestrict f.range hrange)
  have hψ : Function.Injective ψ := fun x y hxy =>
    hφinj (congrArg Subtype.val ((MonoidHom.ofInjective hf).symm.injective hxy))
  exact le_pRank_of_injective hp1 (fun a b => hE.1.is_comm.comm a b)
    (fun a => Subtype.ext (by simpa using hE.2 a a.2)) hcard ψ hψ le_top

namespace RankChevG2Proof

open CFSG.Open CFSG.SectionRank

theorem two_ne_zero_zmod {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) : (2 : ZMod r) ≠ 0 := by
  intro h
  have h1 : ((2 : ℕ) : ZMod r) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h1
  exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h1)

theorem sq_add_one_ne_zero {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {x : ZMod r} (h6 : x ^ 6 = 1) :
    x ^ 2 + 1 ≠ 0 := by
  intro h
  apply two_ne_zero_zmod hr hr2
  linear_combination (x ^ 4 - x ^ 2 + 1) * h - h6

theorem cast_pow_six_eq_one {r q : ℕ} (hq : 1 ≤ q) (h : r ∣ q ^ 6 - 1) :
    ((q : ZMod r)) ^ 6 = 1 := by
  have h1 := (ZMod.natCast_eq_zero_iff (q ^ 6 - 1) r).2 h
  rw [Nat.cast_sub (Nat.one_le_pow _ _ hq), Nat.cast_pow, Nat.cast_one, sub_eq_zero] at h1
  exact h1

theorem not_dvd_indices {r q : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hq1 : 1 ≤ q) (hrq : ¬ r ∣ q)
    (h : r ∣ q ^ 6 - 1) :
    ¬ r ∣ q ^ 6 * (q ^ 6 + 1) ∧ ¬ r ∣ q ^ 6 * (q ^ 6 + 1) * (q ^ 2 + 1) := by
  haveI : Fact r.Prime := ⟨hr⟩
  have h6 := cast_pow_six_eq_one hq1 h
  have h2 := two_ne_zero_zmod hr hr2
  have h3 := sq_add_one_ne_zero hr hr2 h6
  have hx : ((q : ZMod r)) ≠ 0 := fun h0 => hrq ((ZMod.natCast_eq_zero_iff q r).1 h0)
  have key : ((q ^ 6 * (q ^ 6 + 1) : ℕ) : ZMod r) = 2 := by
    push_cast
    rw [h6]
    norm_num
  refine ⟨fun hd => h2 (key ▸ (ZMod.natCast_eq_zero_iff _ r).2 hd), fun hd => ?_⟩
  have h4 := (ZMod.natCast_eq_zero_iff _ r).2 hd
  rw [Nat.cast_mul, key] at h4
  push_cast at h4
  rcases mul_eq_zero.1 h4 with h5 | h5
  · exact h2 h5
  · exact h3 h5

theorem ordG2_sq_eq {q : ℕ} (hq : 1 ≤ q) :
    ordG2 (q ^ 2) = ordG2 q * (q ^ 6 * (q ^ 6 + 1) * (q ^ 2 + 1)) := by
  have h1 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ hq
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
  have h3 : 1 ≤ (q ^ 2) ^ 6 := Nat.one_le_pow _ _ h2
  have h4 : 1 ≤ (q ^ 2) ^ 2 := Nat.one_le_pow _ _ h2
  unfold ordG2
  zify [h1, h2, h3, h4]
  ring

theorem ordG2_sq_eq_SL3 {q : ℕ} (hq : 1 ≤ q) :
    ordG2 (q ^ 2) =
      (q ^ 2) ^ 3 * (((q ^ 2) ^ 2 - 1) * ((q ^ 2) ^ 3 - 1)) * (q ^ 6 * (q ^ 6 + 1)) := by
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
  have h3 : 1 ≤ (q ^ 2) ^ 6 := Nat.one_le_pow _ _ h2
  have h4 : 1 ≤ (q ^ 2) ^ 2 := Nat.one_le_pow _ _ h2
  have h5 : 1 ≤ (q ^ 2) ^ 3 := Nat.one_le_pow _ _ h2
  unfold ordG2
  zify [h2, h3, h4, h5]
  ring

theorem dvd_of_cast_pow_six_eq_one {r q : ℕ} (hq : 1 ≤ q) (h : ((q : ZMod r)) ^ 6 = 1) :
    r ∣ q ^ 6 - 1 := by
  refine (ZMod.natCast_eq_zero_iff (q ^ 6 - 1) r).1 ?_
  rw [Nat.cast_sub (Nat.one_le_pow _ _ hq), Nat.cast_pow, Nat.cast_one, h, sub_self]

theorem index_range_eq {H G : Type*} [Group H] [Group G] (f : H →* G)
    (hf : Function.Injective f) {a b : ℕ} (hH : Nat.card H = a) (hG : Nat.card G = a * b)
    (ha : 0 < a) : f.range.index = b := by
  have h1 : Nat.card f.range = Nat.card H :=
    (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm
  have h2 := Subgroup.card_mul_index f.range
  rw [h1, hH, hG] at h2
  exact Nat.eq_of_mul_eq_mul_left ha h2

theorem pRank_eq_zero_of_not_dvd_card {G : Type*} [Group G] [Finite G] {r : ℕ} [hr : Fact r.Prime]
    (h : ¬ r ∣ Nat.card G) : CFSG.Open.pRank r (⊤ : Subgroup G) = 0 := by
  obtain ⟨E, -, -, hcard⟩ := exists_pRank hr.out.one_lt (⊤ : Subgroup G)
  by_contra hk
  apply h
  have h1 : r ∣ Nat.card E := by
    rw [hcard]
    exact dvd_pow_self r hk
  exact dvd_trans h1 (Subgroup.card_subgroup_dvd_card E)

theorem not_dvd_card_of_charP_two {L : Type} [Field L] [Finite L] [CharP L 2] {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) : ¬ r ∣ Nat.card L := by
  haveI : Fintype L := Fintype.ofFinite L
  obtain ⟨m, -, hm⟩ := FiniteField.card L 2
  rw [Nat.card_eq_fintype_card, hm]
  exact fun h => hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h))

theorem pRank_statedSL_three_charTwo {L : Type} [Field L] [Finite L] [CharP L 2] {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) :
    CFSG.Open.pRank r (⊤ : Subgroup ↥(CFSG.Open.StatedSL 3 L)) =
      if r ∣ Nat.card L - 1 then 2 else 3 / orderOf (Nat.card L : ZMod r) := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fintype L := Fintype.ofFinite L
  by_cases h : r ∣ Nat.card L - 1
  · rw [if_pos h]
    have hrL : (r : L) ≠ 0 := fun h0 => hr2
      ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hr).1 ((CharP.cast_eq_zero_iff L 2 r).1 h0)).symm
    exact pRank_top_statedSL_eq_pred (by norm_num) hrL h
  · rw [if_neg h]
    have hrp : ¬ r ∣ Fintype.card L := by
      rw [← Nat.card_eq_fintype_card]
      exact not_dvd_card_of_charP_two hr hr2
    have hrF : ¬ r ∣ Fintype.card L - 1 := by
      rwa [← Nat.card_eq_fintype_card]
    rw [pRank_statedSL_of_not_dvd hr hr2 hrp hrF 3, Nat.card_eq_fintype_card]

theorem sq_sub_one_dvd_pow_six_sub_one (q : ℕ) : q ^ 2 - 1 ∣ q ^ 6 - 1 :=
  Nat.pow_sub_one_dvd_pow_sub_one q (by norm_num)

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley in
theorem exists_injective_baseChange
    {K L : Type} [Field K] [Field L] (f : K →+* L) :
    ∃ ι : adjointGroup .G2 K →* adjointGroup .G2 L, Function.Injective ι :=
  ⟨((baseChangeGL f).comp (adjointGroup .G2 K).subtype).codRestrict (adjointGroup .G2 L)
      fun u => baseChangeGL_mem_adjointGroup f u.2,
    fun u v h => Subtype.ext (baseChangeGL_injective f (congrArg Subtype.val h))⟩

section Certified


open CFSG.Blueprint.Chevalley CFSG.Open.StatedAPI in
theorem exists_injective_statedSL_three (L : Type) [Field L] [Finite L] :
    ∃ ι : StatedSL 3 L →* adjointGroup .G2 L, Function.Injective ι := by
  obtain ⟨φ, hφ, -⟩ := CFSG.GH74.GLS.Stage2.Bender.Thm1.exists_a2Hom_injective (K := L)
  let e : Matrix.SpecialLinearGroup (Fin 3) L ≃* StatedSL 3 L :=
    (MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective).trans
      (MulEquiv.subgroupCongr (statedSL_eq_range_toGL 3 L).symm)
  exact ⟨φ.comp e.symm.toMonoidHom, hφ.comp e.symm.injective⟩

open CFSG.Blueprint.Chevalley CFSG.Open.StatedAPI CFSG.Timmesfeld.ExceptionalOrders in
theorem pRank_adjointG2_eq_statedSL_three (K : Type) [Field K] [Fintype K] [CharP K 2] {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (h6 : r ∣ Fintype.card K ^ 6 - 1) :
    ∃ (L : Type) (_ : Field L) (_ : Finite L) (_ : CharP L 2),
      Nat.card L = Fintype.card K ^ 2 ∧
      CFSG.Open.pRank r (⊤ : Subgroup ↥(adjointGroup .G2 K)) =
        CFSG.Open.pRank r (⊤ : Subgroup ↥(StatedSL 3 L)) := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hq1 : 1 ≤ Fintype.card K := Fintype.card_pos
  have hrq : ¬ r ∣ Fintype.card K := by
    rw [← Nat.card_eq_fintype_card]
    exact not_dvd_card_of_charP_two hr hr2
  let L := FiniteField.Extension K 2 2
  haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have hLc : Nat.card L = Fintype.card K ^ 2 := by
    rw [FiniteField.natCard_extension, Nat.card_eq_fintype_card]
  refine ⟨L, inferInstance, inferInstance, inferInstance, hLc, ?_⟩
  obtain ⟨ι₁, hι₁⟩ := exists_injective_baseChange (algebraMap K L)
  obtain ⟨ι₂, hι₂⟩ := exists_injective_statedSL_three L
  have hG2L : Nat.card ↥(adjointGroup .G2 L) = ordG2 (Fintype.card K ^ 2) := by
    rw [card_adjointGroup_G2, hLc]
  have hG2K : Nat.card ↥(adjointGroup .G2 K) = ordG2 (Fintype.card K) := by
    rw [card_adjointGroup_G2, Nat.card_eq_fintype_card]
  have hSL : Nat.card ↥(StatedSL 3 L) = (Fintype.card K ^ 2) ^ 3 *
      (((Fintype.card K ^ 2) ^ 2 - 1) * ((Fintype.card K ^ 2) ^ 3 - 1)) := by
    rw [card_statedSL_three, hLc]
  obtain ⟨hidx2, hidx1⟩ := not_dvd_indices hr hr2 hq1 hrq h6
  have e1 : ι₁.range.index = Fintype.card K ^ 6 * (Fintype.card K ^ 6 + 1) *
      (Fintype.card K ^ 2 + 1) :=
    index_range_eq ι₁ hι₁ hG2K (by rw [hG2L, ordG2_sq_eq hq1]) (hG2K ▸ Nat.card_pos)
  have e2 : ι₂.range.index = Fintype.card K ^ 6 * (Fintype.card K ^ 6 + 1) :=
    index_range_eq ι₂ hι₂ hSL (by rw [hG2L]; exact ordG2_sq_eq_SL3 hq1) (hSL ▸ Nat.card_pos)
  rw [pRank_top_eq_of_injective_of_not_dvd_index ι₁ hι₁ (e1 ▸ hidx1),
    ← pRank_top_eq_of_injective_of_not_dvd_index ι₂ hι₂ (e2 ▸ hidx2)]

end Certified

end RankChevG2Proof

open CFSG.Blueprint.Chevalley in
theorem pRank_adjointG2_eq
    (K : Type) [Field K] [Fintype K] {n : ℕ} (hK : Fintype.card K = 2 ^ n) (hn : 2 ≤ n)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    CFSG.Open.pRank r (⊤ : Subgroup ↥(adjointGroup .G2 K)) = rkG2 (Fintype.card K) r := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hq1 : 1 ≤ Fintype.card K := Fintype.card_pos
  haveI : CharP K 2 := CFSG.LargeExtraspecial.DW.charP_two_of_card_eq (f := n)
    (by rw [Nat.card_eq_fintype_card, hK])
  have hrq : ¬ r ∣ Fintype.card K := by
    rw [← Nat.card_eq_fintype_card]
    exact RankChevG2Proof.not_dvd_card_of_charP_two hr hr2
  by_cases h6 : r ∣ Fintype.card K ^ 6 - 1
  · obtain ⟨L, instF, instFin, instC, hL, hrank⟩ :=
      RankChevG2Proof.pRank_adjointG2_eq_statedSL_three K hr hr2 h6
    rw [hrank, RankChevG2Proof.pRank_statedSL_three_charTwo hr hr2, hL]
    have h6' := RankChevG2Proof.cast_pow_six_eq_one hq1 h6
    have hdvd3 : eS (Fintype.card K) r ∣ 3 := by
      unfold eS
      exact orderOf_dvd_of_pow_eq_one (by rw [← pow_mul]; exact h6')
    unfold rkG2
    by_cases h2 : r ∣ Fintype.card K ^ 2 - 1
    · rw [if_pos h2, if_pos ((eS_eq_one_iff hq1).2 h2)]
    · have h1 : eS (Fintype.card K) r ≠ 1 := fun h => h2 ((eS_eq_one_iff hq1).1 h)
      have h3 : eS (Fintype.card K) r = 3 :=
        ((Nat.dvd_prime Nat.prime_three).1 hdvd3).resolve_left h1
      have h4 : orderOf (((Fintype.card K ^ 2 : ℕ)) : ZMod r) = 3 := by
        rw [Nat.cast_pow]
        exact h3
      rw [if_neg h2, if_neg h1, if_pos h3, h4]
  · have hnd : ¬ r ∣ Nat.card ↥(adjointGroup .G2 K) := by
      rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, Nat.card_eq_fintype_card]
      intro hd
      unfold CFSG.Open.ordG2 at hd
      rcases (Nat.Prime.dvd_mul hr).1 hd with hd | hd
      · rcases (Nat.Prime.dvd_mul hr).1 hd with hd | hd
        · exact hrq (hr.dvd_of_dvd_pow hd)
        · exact h6 hd
      · exact h6 (hd.trans (RankChevG2Proof.sq_sub_one_dvd_pow_six_sub_one _))
    rw [RankChevG2Proof.pRank_eq_zero_of_not_dvd_card hnd]
    have h1 : eS (Fintype.card K) r ≠ 1 := fun h =>
      h6 (((eS_eq_one_iff hq1).1 h).trans (RankChevG2Proof.sq_sub_one_dvd_pow_six_sub_one _))
    have h3 : eS (Fintype.card K) r ≠ 3 := fun h => by
      refine h6 (RankChevG2Proof.dvd_of_cast_pow_six_eq_one hq1 ?_)
      have h5 := pow_orderOf_eq_one ((Fintype.card K : ZMod r) ^ 2)
      change ((Fintype.card K : ZMod r) ^ 2) ^ eS (Fintype.card K) r = 1 at h5
      rw [h, ← pow_mul] at h5
      exact h5
    unfold rkG2
    rw [if_neg h1, if_neg h3]

end CFSG.LocalAnalysis.RankThreeUC.S15
