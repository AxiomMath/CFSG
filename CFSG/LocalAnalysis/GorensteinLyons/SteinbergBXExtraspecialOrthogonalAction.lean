module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXExtraspecialOddAction
public import CFSG.Quasithin.SteinbergBKCharTwoFrattiniAction
public import CFSG.LocalAnalysis.PreuniquenessRankFour.BinaryRank
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXCyclicCenterFixed
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXWeakClosureFusionRank
public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasAFaithful

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup CFSG.Open
open scoped commutatorElement
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom)

@[expose] def extraspecialOrthogonalGroup {Q : Type*} [Group Q] (z : Q) :
    Subgroup (MulAut (Q ⧸ center Q)) where
  carrier := {f | ∀ v, sqVal z (f v) = sqVal z v}
  mul_mem' := fun {f g} hf hg v => by
    simp only [Set.mem_ofPred_eq] at hf hg ⊢
    rw [MulAut.mul_apply, hf, hg]
  one_mem' := fun v => rfl
  inv_mem' := fun {f} hf v => by
    simp only [Set.mem_ofPred_eq] at hf ⊢
    have := hf (f⁻¹ v)
    rw [MulAut.apply_inv_self] at this
    exact this.symm

theorem extraspecial_centralizer_orthogonal_action {H : Type*} [Group H] [Finite H]
    (hH : CFSG.IsCharacteristicP 2 H) (hQ : IsExtraspecialPGroup 2 (CFSG.pCore 2 H))
    {z : CFSG.pCore 2 H} (hz : center (CFSG.pCore 2 H) = zpowers z) :
    CFSG.IsElementaryAbelian 2 (CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H)) ∧
      (∃! w : ℕ, 1 ≤ w ∧ Nat.card (CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H)) = 2 ^ (2 * w)) ∧
      (∀ w : ℕ, Nat.card (CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H)) = 2 ^ (2 * w) →
        Nat.card (CFSG.pCore 2 H) = 2 ^ (1 + 2 * w)) ∧
      (∀ (x : CFSG.pCore 2 H) (ε : ZMod 2), x ^ 2 = z ^ ε.val →
        sqVal z (x : CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H)) = ε) ∧
      sqVal z 1 = 0 ∧
      (∀ u v, sqVal z (u * v) = sqVal z u + sqVal z v + commVal z u v) ∧
      (∀ x y : CFSG.pCore 2 H,
        ⁅x, y⁆ = z ^ (commVal z (x : CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H)) y).val) ∧
      (∀ u v t, commVal z (u * v) t = commVal z u t + commVal z v t) ∧
      (∀ u v t, commVal z u (v * t) = commVal z u v + commVal z u t) ∧
      (∀ u, commVal z u u = 0) ∧ (∀ u, (∀ v, commVal z u v = 0) → u = 1) ∧
      (∀ (h : H) v, sqVal z (centerQuotientHom (CFSG.pCore 2 H) (MulAut.conjNormal h) v) =
        sqVal z v) ∧
      (∃ ι : H ⧸ CFSG.pCore 2 H →* extraspecialOrthogonalGroup z, Function.Injective ι ∧
        ∀ h : H, ((ι h : extraspecialOrthogonalGroup z) : MulAut _) =
          centerQuotientHom (CFSG.pCore 2 H) (MulAut.conjNormal h)) ∧
      ∀ (B : Subgroup H) (r : ℕ), IsElemAbelian 3 B → Nat.card B = 3 ^ r →
        (∀ b ∈ B, centerQuotientHom (CFSG.pCore 2 H) (MulAut.conjNormal b) = 1 → b = 1) ∧
        ∀ w : ℕ, Nat.card (CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H)) = 2 ^ (2 * w) → r ≤ w := by
  classical
  have := Fact.mk Nat.prime_two
  have HQ := commPairHyp_of_extraspecial hQ hz
  have hV := HQ.isElementaryAbelian_quotient
  have hzo : orderOf z = 2 := HQ.orderOf_eq
  have hz1 : z ≠ 1 := HQ.z_ne_one
  obtain ⟨m, -, hm, -⟩ := HQ.exists_symplectic_basis
  have hcen2 : Nat.card (center (CFSG.pCore 2 H)) = 2 := by rw [hz, Nat.card_zpowers, hzo]
  have hcardQ : ∀ w : ℕ, Nat.card ((CFSG.pCore 2 H) ⧸ center (CFSG.pCore 2 H)) = 2 ^ (2 * w) →
      Nat.card (CFSG.pCore 2 H) = 2 ^ (1 + 2 * w) := by
    intro w hw
    rw [card_eq_card_quotient_mul_card_subgroup (center (CFSG.pCore 2 H)), hw, hcen2, pow_add,
      pow_one,
      mul_comm]
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · exfalso
      rw [h0, mul_zero, pow_zero] at hm
      have htop : center (CFSG.pCore 2 H) = ⊤ := by
        rw [← QuotientGroup.ker_mk' (center (CFSG.pCore 2 H)), eq_top_iff]
        intro x _
        rw [MonoidHom.mem_ker]
        have : Subsingleton ((CFSG.pCore 2 H) ⧸ center (CFSG.pCore 2 H)) :=
          Finite.card_le_one_iff_subsingleton.mp (by rw [hm])
        exact Subsingleton.elim _ _
      have hcomm : commutator (CFSG.pCore 2 H) = ⊥ := by
        rw [_root_.commutator_def, commutator_eq_bot_iff_le_centralizer]
        intro x _
        rw [mem_centralizer_iff]
        intro y _
        have hy : y ∈ center (CFSG.pCore 2 H) := htop ▸ mem_top y
        exact (mem_center_iff.mp hy x).symm
      have h2 := hQ.2.1
      rw [hcomm] at h2
      rw [← h2, card_bot] at hcen2
      exact absurd hcen2 (by norm_num)
    · exact h0
  have hsq : ∀ (x : (CFSG.pCore 2 H)) (ε : ZMod 2), x ^ 2 = z ^ ε.val →
      sqVal z (x : (CFSG.pCore 2 H) ⧸ center (CFSG.pCore 2 H)) = ε := by
    intro x ε hx
    have h1 := HQ.sq_eq_zpow_sqVal hz x
    rw [hx] at h1
    rcases zmod_two_eq_zero_or_one ε with h | h <;>
      rcases zmod_two_eq_zero_or_one (sqVal z (x : (CFSG.pCore 2 H) ⧸ center (CFSG.pCore 2 H)))
        with h' | h'
    · rw [h, h']
    · exfalso
      rw [h, h', show (0 : ZMod 2).val = 0 from rfl, show (1 : ZMod 2).val = 1 from rfl,
        pow_zero, pow_one] at h1
      exact hz1 h1.symm
    · exfalso
      rw [h, h', show (0 : ZMod 2).val = 0 from rfl, show (1 : ZMod 2).val = 1 from rfl,
        pow_zero, pow_one] at h1
      exact hz1 h1
    · rw [h, h']
  have hsq1 : sqVal z (1 : (CFSG.pCore 2 H) ⧸ center (CFSG.pCore 2 H)) = 0 := by
    rw [← QuotientGroup.mk_one, HQ.sqVal_mk hz, one_pow, HQ.zlog_one]
  have hpres : ∀ (h : H) v,
      sqVal z (centerQuotientHom (CFSG.pCore 2 H) (MulAut.conjNormal h) v) = sqVal z v := by
    intro h v
    induction v using QuotientGroup.induction_on with | H x =>
    rw [CFSG.ComponentClassification.CentralCover.centerQuotientHom_apply_mk, HQ.sqVal_mk hz,
      HQ.sqVal_mk hz, ← map_pow]
    rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two hzo (hz ▸ HQ.sq_mem_center x) with
      h1 | h1 <;> rw [h1]
    · rw [map_one]
    · rw [mulAut_apply_eq_of_center_eq hz hzo]
  set ρ : H →* MulAut ((CFSG.pCore 2 H) ⧸ center (CFSG.pCore 2 H)) :=
    (centerQuotientHom (CFSG.pCore 2 H)).comp MulAut.conjNormal with hρ
  have hker : ρ.ker = (CFSG.pCore 2 H) := by
    have hCLS := (CFSG.Quasithin.SteinbergBK.characteristic_two_core_frattini_action_and_small_ranks
      hH).1
    refine Eq.trans ?_ hCLS
    ext h
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    change centerQuotientHom (CFSG.pCore 2 H) (MulAut.conjNormal h) = 1 ↔
      MulAut.conjNormal h ∈ (CFSG.SectionRank.Ccomm.autQuotient (frattini (CFSG.pCore 2 H))).ker
    rw [CFSG.SectionRank.Ccomm.mem_ker_autQuotient, hQ.2.2.1]
    constructor
    · intro h1 x
      have h2 := congrArg (fun σ : MulAut ((CFSG.pCore 2 H) ⧸ center (CFSG.pCore 2 H)) =>
        σ (x : (CFSG.pCore 2 H) ⧸ center (CFSG.pCore 2 H))) h1
      simp only [CFSG.ComponentClassification.CentralCover.centerQuotientHom_apply_mk,
        MulAut.one_apply] at h2
      have h3 := QuotientGroup.eq.mp h2.symm
      exact h3
    · intro h1
      ext v
      induction v using QuotientGroup.induction_on with | H x =>
      rw [CFSG.ComponentClassification.CentralCover.centerQuotientHom_apply_mk, MulAut.one_apply]
      exact (QuotientGroup.eq.mpr (h1 x)).symm
  set ρ' : H →* extraspecialOrthogonalGroup z := ρ.codRestrict _ fun h v => hpres h v with hρ'
  have hker' : ρ'.ker = (CFSG.pCore 2 H) := by
    refine Eq.trans ?_ hker
    ext h
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    exact ⟨fun h1 => congrArg Subtype.val h1, fun h1 => Subtype.ext h1⟩
  let ι : H ⧸ (CFSG.pCore 2 H) →* extraspecialOrthogonalGroup z :=
    (QuotientGroup.kerLift ρ').comp (QuotientGroup.quotientMulEquivOfEq hker'.symm).toMonoidHom
  have hι : Function.Injective ι :=
    (QuotientGroup.kerLift_injective ρ').comp (QuotientGroup.quotientMulEquivOfEq _).injective
  refine ⟨hV, ⟨m, ⟨hm1, hm⟩, fun w hw => ?_⟩, hcardQ, hsq, hsq1, HQ.sqVal_mul hz,
    HQ.commutatorElement_eq_zpow, HQ.commVal_mul_left, HQ.commVal_mul_right, HQ.commVal_self,
    fun u hu => HQ.eq_one_of_forall_commVal_eq_zero hu, hpres, ⟨ι, hι, fun h => rfl⟩,
    fun B r hB hBr => ?_⟩
  · have h1 := hw.2
    rw [hm] at h1
    have := Nat.pow_right_injective (le_refl 2) h1
    omega
  have hfaith : ∀ b ∈ B, ρ b = 1 → b = 1 := by
    intro b hb hρb
    have hbQ : b ∈ (CFSG.pCore 2 H) := hker ▸ (MonoidHom.mem_ker.mpr hρb)
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp (CFSG.pCore_isPGroup (p := 2) (G := H))) ⟨b, hbQ⟩
    have hk' : orderOf b = 2 ^ k := by rw [← hk, Subgroup.orderOf_mk]
    have h3 : orderOf b ∣ 3 := orderOf_dvd_of_pow_eq_one (hB.2 b hb)
    rw [hk'] at h3
    rcases k with _ | k
    · rw [pow_zero] at hk'
      exact orderOf_eq_one_iff.mp hk'
    · exfalso
      have : 2 ∣ 3 := (dvd_pow_self 2 (Nat.succ_ne_zero k)).trans h3
      omega
  refine ⟨hfaith, fun w hw => ?_⟩
  have : IsMulCommutative ((CFSG.pCore 2 H) ⧸ center (CFSG.pCore 2 H)) := hV.toIsMulCommutative
  let : CommGroup ((CFSG.pCore 2 H) ⧸ center (CFSG.pCore 2 H)) := IsMulCommutative.instCommGroup
  have hV2 : ∀ v : (CFSG.pCore 2 H) ⧸ center (CFSG.pCore 2 H), v ^ 2 = 1 := fun v =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (CFSG.IsElementaryAbelian.exponent_dvd_p 2 _) v
  let : Module (ZMod 2) (Additive ((CFSG.pCore 2 H) ⧸ center (CFSG.pCore 2 H))) :=
    AddCommGroup.zmodModule (n := 2) fun v => by
      change Additive.ofMul (Additive.toMul v ^ 2) = 0
      rw [hV2]
      rfl
  let : MulDistribMulAction B ((CFSG.pCore 2 H) ⧸ center (CFSG.pCore 2 H)) :=
    MulDistribMulAction.compHom ((CFSG.pCore 2 H) ⧸ center (CFSG.pCore 2 H)) (ρ.comp B.subtype)
  have hinj : Function.Injective
      (MulDistribMulAction.toMulAut B ((CFSG.pCore 2 H) ⧸ center (CFSG.pCore 2 H))) := by
    intro b c hbc
    have h1 : ρ (b : H) = ρ (c : H) := by
      ext v
      exact congrArg (fun σ : MulAut ((CFSG.pCore 2 H) ⧸ center (CFSG.pCore 2 H)) => σ v) hbc
    have h2 : ρ ((b : H) * (c : H)⁻¹) = 1 := by rw [map_mul, map_inv, h1, mul_inv_cancel]
    have h3 := hfaith _ (mul_mem b.2 (inv_mem c.2)) h2
    exact Subtype.ext (mul_inv_eq_one.mp h3)
  have hbound := CFSG.PreuniquenessRankFour.Helpers.faithful_binary_multiplicative_action_rank_bound
    (acting := B) (source := (CFSG.pCore 2 H) ⧸ center (CFSG.pCore 2 H)) 3 (by norm_num) hinj
  have hrank : r ≤ CFSG.Open.pRank 3 (⊤ : Subgroup B) := by
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top, pRank_eq_of_elementary (by norm_num) hB hBr]
  have hfin : Module.finrank (ZMod 2) (Additive ((CFSG.pCore 2 H) ⧸ center (CFSG.pCore 2 H))) =
      2 * w := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := Additive ((CFSG.pCore 2 H) ⧸ center (CFSG.pCore 2 H)))
    rw [Nat.card_zmod] at h1
    have h2 : Nat.card (Additive ((CFSG.pCore 2 H) ⧸ center (CFSG.pCore 2 H))) =
        Nat.card ((CFSG.pCore 2 H) ⧸ center (CFSG.pCore 2 H)) :=
      Nat.card_congr Additive.toMul
    rw [h2, hw] at h1
    exact (Nat.pow_right_injective (le_refl 2) h1).symm
  omega

end CFSG.LocalAnalysis.GorensteinLyons
