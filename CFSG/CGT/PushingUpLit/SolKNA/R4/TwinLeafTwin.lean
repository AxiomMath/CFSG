module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafBasic

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.CGT.PushingUpLit.SolKNA.R4 CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall
open scoped commutatorElement

theorem card_oddCoreOf_odd {Y : Type} [Group Y] [Finite Y] (H : Subgroup Y) :
    Odd (Nat.card (oddCoreOf H)) := by
  have h := CFSG.ComponentClassification.OddCore.odd_card ↥H
  have e : ↥(classicalInvolutionOddCore ↥H) ≃* ↥(oddCoreOf H) :=
    Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective
  rw [← Nat.card_congr e.toEquiv]
  exact h

theorem oddCoreOf_le' {Y : Type} [Group Y] (H : Subgroup Y) : oddCoreOf H ≤ H :=
  Subgroup.map_subtype_le _

theorem le_normalizer_of_commutator_le {Y : Type} [Group Y] {K K' : Subgroup Y}
    (h : ⁅K, K'⁆ ≤ K') : K ≤ Subgroup.normalizer (K' : Set Y) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have h1 : ⁅x, y⁆ ∈ K' := h (Subgroup.commutator_mem_commutator hx hy)
    have : x * y * x⁻¹ = ⁅x, y⁆ * y := by simp only [commutatorElement_def]; group
    rw [this]
    exact K'.mul_mem h1 hy
  · intro hy
    have h1 : ⁅x⁻¹, x * y * x⁻¹⁆ ∈ K' :=
      h (Subgroup.commutator_mem_commutator (K.inv_mem hx) hy)
    have : y = ⁅x⁻¹, x * y * x⁻¹⁆ * (x * y * x⁻¹) := by simp only [commutatorElement_def]; group
    rw [this]
    exact K'.mul_mem h1 hy

theorem exists_commuting_sylow2 {Y : Type} [Group Y] [Finite Y] {K K' : Subgroup Y}
    (hK : K' ≤ Subgroup.normalizer (K : Set Y)) (hK' : K ≤ Subgroup.normalizer (K' : Set Y))
    {O : Subgroup Y} (hO : Odd (Nat.card O)) (hcomm : ⁅K, K'⁆ ≤ O) :
    ∃ R₀ R₀' : Subgroup Y, IsSylow2In R₀ K ∧ IsSylow2In R₀' K' ∧
      ∀ x ∈ R₀, ∀ y ∈ R₀', x * y = y * x := by
  obtain ⟨T, hT, -⟩ := IsSylow2In.exists_ge (P := K ⊔ K') (T := ⊥) IsPGroup.of_bot bot_le
  refine ⟨T ⊓ K, T ⊓ K',
    AscP1Nine3.isSylow2In_inf_of_le_normalizer' hT le_sup_left
      (sup_le Subgroup.le_normalizer hK),
    AscP1Nine3.isSylow2In_inf_of_le_normalizer' hT le_sup_right
      (sup_le hK' Subgroup.le_normalizer), ?_⟩
  intro x hx y hy
  have hc : ⁅x, y⁆ ∈ T ⊓ O := by
    refine ⟨?_, hcomm (Subgroup.commutator_mem_commutator hx.2 hy.2)⟩
    simp only [commutatorElement_def]
    exact T.mul_mem (T.mul_mem (T.mul_mem hx.1 hy.1) (T.inv_mem hx.1)) (T.inv_mem hy.1)
  obtain ⟨k, hk⟩ := hT.2.1 ⟨_, hc.1⟩
  have hk' : ⁅x, y⁆ ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have h2 : orderOf ⁅x, y⁆ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h3 : orderOf ⁅x, y⁆ ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O hc.2
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
  have hj0 : j = 0 := by
    by_contra hj0
    have : 2 ∣ Nat.card O := by
      refine (Dvd.dvd.trans ?_ h3)
      rw [hj]
      exact dvd_pow_self 2 hj0
    exact (Nat.not_even_iff_odd.mpr hO) ((even_iff_two_dvd).mpr this)
  rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
  exact commutatorElement_eq_one_iff_mul_comm.mp hj

theorem nonempty_mulEquiv_of_isSylow2In {Y : Type} [Group Y] [Finite Y] {K P R : Subgroup Y}
    (hP : IsSylow2In P K) (hR : IsSylow2In R K) : Nonempty (↥P ≃* ↥R) := by
  obtain ⟨x, -, hx⟩ := exists_conjSub_eq_of_isSylow2In hP hR
  exact ⟨(Subgroup.equivMapOfInjective P (MulAut.conj x).toMonoidHom
    (MulAut.conj x).injective).trans (MulEquiv.subgroupCongr hx)⟩


theorem exists_q16Q16_of_perp {r n : ℕ} (hr : 4 ≤ r) {Y : Type} [Group Y] [Finite Y]
    {R : Subgroup Y} {S : Sylow 2 R} {t : Y} (h : PerpHypR r n Y R S t) :
    ∃ (K' : Subgroup Y) (x y x' y' : Y), K' ≠ tightCore R ∧
      (∃ g : Y, conjSub g (tightCore R) = K') ∧
      IsUniqueInvolution K' t ∧ CFSG.Open.IsSubnormal K' (Subgroup.centralizer ({t} : Set Y)) ∧
      x ∈ tightCore R ∧ y ∈ tightCore R ∧ x' ∈ K' ∧ y' ∈ K' ∧ Q16Q16 x y x' y' := by
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := h.core.hyp
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core h.core.datum
  obtain ⟨K', hK'tw, hne⟩ := h.core.twin
  obtain ⟨hK'Ω, z', hz'0, hz'⟩ := hK'tw
  have hzt : t = z' := hz.eq hz'0
  rw [← hzt] at hz'
  obtain ⟨g, hg⟩ := hK'Ω
  set K : Subgroup Y := tightCore R with hKdef
  have h4 := hΩ.omega4 K (CoreAssembly.mem_conjClass_self _) K' ⟨g, hg⟩ (Ne.symm hne)
  have ht2 : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  have hdvd : 2 ^ 1 ∣ Nat.card ↥(K ⊓ K') := by
    have := Subgroup.orderOf_dvd_natCard (K ⊓ K') (Subgroup.mem_inf.mpr ⟨hz.mem, hz'.mem⟩)
    rw [ht2] at this
    simpa using this
  have h1 : 1 ≤ padicValNat 2 (Nat.card ↥(K ⊓ K')) :=
    (padicValNat_dvd_iff_le (p := 2) Nat.card_pos.ne').mp hdvd
  have hcomm : ⁅K, K'⁆ ≤ oddCoreOf K ⊓ oddCoreOf K' := h4.2 (le_antisymm h4.1 h1)
  have hKK' : ⁅K, K'⁆ ≤ K' := hcomm.trans (inf_le_right.trans (oddCoreOf_le' K'))
  have hK'K : ⁅K', K⁆ ≤ K := by
    rw [Subgroup.commutator_comm]
    exact hcomm.trans (inf_le_left.trans (oddCoreOf_le' K))
  obtain ⟨R₀, R₀', hR₀, hR₀', hcom⟩ := exists_commuting_sylow2
    (le_normalizer_of_commutator_le hK'K) (le_normalizer_of_commutator_le hKK')
    (card_oddCoreOf_odd K) (hcomm.trans inf_le_left)
  have hP : IsSylow2In ((S : Subgroup R).map R.subtype) K := h.core.datum.sylow_core
  obtain ⟨e⟩ := h.core.quat
  let e₁ : ↥((S : Subgroup R).map R.subtype) ≃* QuaternionGroup (2 ^ (r - 2)) :=
    ((S : Subgroup R).equivMapOfInjective R.subtype R.subtype_injective).symm.trans e
  obtain ⟨φ₀⟩ := nonempty_mulEquiv_of_isSylow2In hP hR₀
  obtain ⟨x, hxR, y, hyR, hxy⟩ := exists_q16Pair_mem hr (φ₀.symm.trans e₁)
  have hP' : IsSylow2In (conjSub g ((S : Subgroup R).map R.subtype)) K' := by
    have := hP.conj g
    rwa [show conjSub g K = K' from hg] at this
  obtain ⟨φ₀'⟩ := nonempty_mulEquiv_of_isSylow2In hP' hR₀'
  let e₂ : ↥((S : Subgroup R).map R.subtype) ≃* ↥(conjSub g ((S : Subgroup R).map R.subtype)) :=
    Subgroup.equivMapOfInjective _ (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  obtain ⟨x', hx'R, y', hy'R, hxy'⟩ :=
    exists_q16Pair_mem hr ((e₂.trans φ₀').symm.trans e₁)
  have hxK : x ∈ K := hR₀.1 hxR
  have hx'K' : x' ∈ K' := hR₀'.1 hx'R
  have hx4 : x ^ 4 = t := by
    refine (hz.unique _ (K.pow_mem hxK 4) ?_).resolve_left hxy.1
    rw [← pow_add]
    exact hxy.2.1
  have hx4' : x' ^ 4 = t := by
    refine (hz'.unique _ (K'.pow_mem hx'K' 4) ?_).resolve_left hxy'.1
    rw [← pow_add]
    exact hxy'.2.1
  exact ⟨K', x, y, x', y', hne, ⟨g, hg⟩, hz',
    isSubnormal_of_hypOmegaGen hΩ ⟨g, hg⟩ hz', hxK, hR₀.1 hyR, hx'K', hR₀'.1 hy'R,
    hxy, hxy', by rw [hx4, hx4'], hcom x hxR x' hx'R, hcom x hxR y' hy'R, hcom y hyR x' hx'R,
    hcom y hyR y' hy'R⟩

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf
