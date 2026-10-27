module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverList
import CFSG.LocalAnalysis.AGLEmbedding.CompCenterNineOrbit
import CFSG.LocalAnalysis.AGLEmbedding.CompCenterNineU43
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanAlphaThreeWeakMult
import CFSG.RankThree.PartTwo.Sec4.Census.Item43Narrow

public section

namespace CFSG.AGLEmbedding.CompCenterNine

open TauCeti CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Models CFSG.Blueprint.Multiplier
open CFSG.RankThree.PerfectCover (hopfMultiplier hopfMultiplierToKer
  hopfMultiplierToKer_surjective centralQuotientMap centralQuotientMap_surjective
  centralQuotientMap_ker hopfMultiplier_le_center hopfMultiplierEquivGriess)
open CFSG.RankThree.PartTwo.Sec4.Census (SporadicMultipliers sporadicMultiplierOrder tableOrder
  card_center_dvd_tableOrder tripleCoverLie_of_griess lieModel_of_namesTag
  lieModel_of_statedClassicalModel)
open CFSG.AGLEmbedding.KFactProofs.ThreeWeak (hopf_threeTorsion_le_of_linuni
  hopf_threeTorsion_le_of_e6 hopf_threeTorsion_le_of_twistedE6 eq_one_of_pow_three_eq_one
  card_pow_three_le_zmod)
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.Helpers (quasisimple_central_quotient_nonabelian)

theorem card_cubeRoots_center_le {K S : Type} [Group K] [Finite K] [Group S]
    (hq : Open.IsQuasisimple K) (e : K ⧸ Subgroup.center K ≃* S) [Finite (hopfMultiplier S)] :
    Nat.card {z : Subgroup.center K // z ^ 3 = 1} ≤
      Nat.card {m : hopfMultiplier S // m ^ 3 = 1} := by
  have : Group.IsPerfect K := ⟨hq.1⟩
  have hker := centralQuotientMap_ker e
  have hle := card_pow_eq_one_le_of_surjective
    (fun a b : hopfMultiplier S =>
      Subtype.ext (Subgroup.mem_center_iff.mp (hopfMultiplier_le_center b.2) a))
    (hopfMultiplierToKer (centralQuotientMap e) (centralQuotientMap_surjective e) hker.le)
    (hopfMultiplierToKer_surjective _ _ _) 3
  refine le_trans (le_of_eq (Nat.card_congr ((MulEquiv.subgroupCongr hker.symm).toEquiv.subtypeEquiv
    fun z => ?_))) hle
  change z ^ 3 = 1 ↔ MulEquiv.subgroupCongr hker.symm z ^ 3 = 1
  rw [← map_pow, MulEquiv.map_eq_one_iff]

theorem card_pow_three_le_nine {a b c d : ℕ} (ha : ¬ 3 ∣ a) (hb : ¬ 3 ∣ b) (hc : 0 < c)
    (hd : 0 < d) :
    Nat.card {x : (Multiplicative (ZMod a) × Multiplicative (ZMod b)) ×
      (Multiplicative (ZMod c) × Multiplicative (ZMod d)) // x ^ 3 = 1} ≤ 9 := by
  have : NeZero c := ⟨hc.ne'⟩
  have : NeZero d := ⟨hd.ne'⟩
  let φ : {x : (Multiplicative (ZMod a) × Multiplicative (ZMod b)) ×
      (Multiplicative (ZMod c) × Multiplicative (ZMod d)) // x ^ 3 = 1} →
      {y : Multiplicative (ZMod c) // y ^ 3 = 1} × {y : Multiplicative (ZMod d) // y ^ 3 = 1} :=
    fun x => (⟨x.1.2.1, by simpa using congrArg (fun z => z.2.1) x.2⟩,
      ⟨x.1.2.2, by simpa using congrArg (fun z => z.2.2) x.2⟩)
  have hφ : Function.Injective φ := by
    intro x y hxy
    have h1 : x.1.2.1 = y.1.2.1 := congrArg (fun z => z.1.1) hxy
    have h2 : x.1.2.2 = y.1.2.2 := congrArg (fun z => z.2.1) hxy
    have hx1 := eq_one_of_pow_three_eq_one ha _ (by simpa using congrArg (fun z => z.1.1) x.2)
    have hy1 := eq_one_of_pow_three_eq_one ha _ (by simpa using congrArg (fun z => z.1.1) y.2)
    have hx2 := eq_one_of_pow_three_eq_one hb _ (by simpa using congrArg (fun z => z.1.2) x.2)
    have hy2 := eq_one_of_pow_three_eq_one hb _ (by simpa using congrArg (fun z => z.1.2) y.2)
    exact Subtype.ext (Prod.ext (Prod.ext (hx1.trans hy1.symm) (hx2.trans hy2.symm))
      (Prod.ext h1 h2))
  refine (Nat.card_le_card_of_injective φ hφ).trans ?_
  rw [Nat.card_prod]
  exact Nat.mul_le_mul (card_pow_three_le_zmod hc) (card_pow_three_le_zmod hd)

theorem exceptionalOrders_pos (t : StatedLieTag) (n p f : ℕ) :
    0 < (exceptionalOrders t n p f).1 ∧ 0 < (exceptionalOrders t n p f).2 := by
  unfold exceptionalOrders
  split <;> norm_num

theorem finite_and_cubeRoots_le_nine (hGA : GriessMultipliersAllModels) {X : Type} [Group X]
    {t : StatedLieTag} {n p f : ℕ} (hm : LieModel X t n p f)
    (ha : ¬ 3 ∣ (genericOrders t n p f).1) (hb : ¬ 3 ∣ (genericOrders t n p f).2) :
    Finite (hopfMultiplier X) ∧ Nat.card {m : hopfMultiplier X // m ^ 3 = 1} ≤ 9 := by
  obtain ⟨-, ⟨eg⟩⟩ := hGA X t n p f hm
  obtain ⟨hc, hd⟩ := exceptionalOrders_pos t n p f
  let e : hopfMultiplier X ≃* generic t n p f × exceptional t n p f :=
    (hopfMultiplierEquivGriess X).symm.trans eg
  have : NeZero (genericOrders t n p f).1 := ⟨fun h0 => ha (h0 ▸ dvd_zero 3)⟩
  have : NeZero (genericOrders t n p f).2 := ⟨fun h0 => hb (h0 ▸ dvd_zero 3)⟩
  have : NeZero (exceptionalOrders t n p f).1 := ⟨hc.ne'⟩
  have : NeZero (exceptionalOrders t n p f).2 := ⟨hd.ne'⟩
  refine ⟨Finite.of_equiv _ e.symm.toEquiv, ?_⟩
  refine le_trans (le_of_eq (Nat.card_congr (e.toEquiv.subtypeEquiv fun m => ?_)))
    (card_pow_three_le_nine ha hb hc hd)
  change m ^ 3 = 1 ↔ e m ^ 3 = 1
  rw [← map_pow, MulEquiv.map_eq_one_iff]

theorem p_eq_three_of_card {q : PrimePower} (hq : q.card = 3) : q.p = 3 ∧ q.exponent = 1 := by
  have hq' : q.p ^ q.exponent = 3 := by rwa [PrimePower.card_def] at hq
  have hf := exponent_eq_one_of_pow_eq_three q.prime_p q.exponent_pos hq'
  rw [hf, pow_one] at hq'
  exact ⟨hq', hf⟩

theorem lie_center_nine (hGA : GriessMultipliersAllModels) {K : Type} [Group K] [Finite K]
    (hq : Open.IsQuasisimple K) (d : ValidLieTypeIndex)
    (e : K ⧸ Subgroup.center K ≃* (CFSGIndex.lie d).Group) (h9 : 9 ∣ Nat.card (Subgroup.center K))
    (hc : 9 ≤ Nat.card {z : Subgroup.center K // z ^ 3 = 1}) :
    Nat.card {z : Subgroup.center K // z ^ 3 = 1} ≤ 9 ∧
      Nat.card (Outer (K ⧸ Subgroup.center K)) = 8 ∧
      ∃ a b : Outer (K ⧸ Subgroup.center K), a ≠ 1 ∧ b ≠ 1 ∧ a ^ 2 = 1 ∧ b ^ 2 = 1 ∧ a ≠ b := by
  have hq' : CFSG.IsQuasisimple K :=
    ⟨⟨hq.1⟩, hq.2, quasisimple_central_quotient_nonabelian K hq⟩
  have h3 : 3 ∣ Nat.card (Subgroup.center K) := (by norm_num : 3 ∣ 9).trans h9
  have hidx := tripleCoverLie_of_griess hGA d K ⟨hq', h3, ⟨e⟩⟩
  have key3 : ∀ [Finite (hopfMultiplier (CFSGIndex.lie d).Group)],
      Nat.card {m : hopfMultiplier (CFSGIndex.lie d).Group // m ^ 3 = 1} ≤ 3 → False :=
    fun hM => by
      have := card_cubeRoots_center_le hq e
      omega
  obtain ⟨dd, hv⟩ := d
  cases dd with
  | A r q =>
    obtain ⟨hfin, hM⟩ := hopf_threeTorsion_le_of_linuni hGA ⟨.A r q, hv⟩ hidx
    exact (key3 hM).elim
  | twistedA r q =>
    rcases hidx with hidx | ⟨rfl, hq3⟩
    · obtain ⟨hfin, hM⟩ := hopf_threeTorsion_le_of_linuni hGA ⟨.twistedA r q, hv⟩ hidx
      exact (key3 hM).elim
    · have hq3' : q.p ^ q.exponent = 3 := by rwa [PrimePower.card_def] at hq3
      have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv (MulEquiv.refl _)
      obtain ⟨hfin, hM⟩ := finite_and_cubeRoots_le_nine hGA (lieModel_of_statedClassicalModel hm)
        (by
          change ¬ 3 ∣ Nat.gcd (3 + 1) (q.p ^ q.exponent + 1)
          rw [hq3']
          norm_num)
        (by simp [genericOrders])
      obtain ⟨-, F, _, _, hF, ⟨e'⟩⟩ := hm
      have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData q.p q.exponent F :=
        ⟨q.prime_p, q.exponent_pos, by rw [hF, ← pow_mul, mul_comm]⟩
      exact ⟨(card_cubeRoots_center_le hq e).trans hM, outer_facts_of_psu43 hU hq3' (e.trans e')⟩
  | B r q =>
    exfalso
    obtain ⟨rfl, hq3⟩ := hidx
    obtain ⟨hp, hf⟩ := p_eq_three_of_card hq3
    have hm := lieModel_of_statedClassicalModel
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd 3 q hv (by omega) le_rfl
        (MulEquiv.refl _))
    have h6 := card_center_dvd_tableOrder hGA hq' e hm
    rw [hp, hf] at h6
    have h9' := h9.trans h6
    revert h9'
    decide
  | G2 q =>
    exfalso
    obtain ⟨hp, hf⟩ := p_eq_three_of_card hidx
    have h3q : 3 ≤ q.p ^ q.exponent := by rw [hp, hf]; norm_num
    have hm := lieModel_of_namesTag (t := .G2) ⟨.G2 q, hv⟩ ⟨rfl, rfl⟩
      ⟨q.prime_p, q.exponent_pos, rfl, h3q⟩
    have h6 := card_center_dvd_tableOrder hGA hq' e hm
    rw [hp, hf] at h6
    have h9' := h9.trans h6
    revert h9'
    decide
  | E6 q =>
    obtain ⟨hfin, hM⟩ := hopf_threeTorsion_le_of_e6 hGA q hv
    exact (key3 hM).elim
  | twistedE6 q =>
    obtain ⟨hfin, hM⟩ := hopf_threeTorsion_le_of_twistedE6 hGA q hv
    exact (key3 hM).elim
  | _ => exact hidx.elim

theorem center_nine_cases (hGA : GriessMultipliersAllModels)
    (hSpM : SporadicMultipliers) {K : Type} [Group K] [Finite K] (hq : Open.IsQuasisimple K)
    (hcat : IsCatalogGroup (K ⧸ Subgroup.center K)) (h9 : 9 ∣ Nat.card (Subgroup.center K))
    (hc : 9 ≤ Nat.card {z : Subgroup.center K // z ^ 3 = 1}) :
    Nat.card {z : Subgroup.center K // z ^ 3 = 1} ≤ 9 ∧
      Nat.card (Outer (K ⧸ Subgroup.center K)) = 8 ∧
      ∃ a b : Outer (K ⧸ Subgroup.center K), a ≠ 1 ∧ b ≠ 1 ∧ a ^ 2 = 1 ∧ b ^ 2 = 1 ∧ a ≠ b := by
  have hq' : CFSG.IsQuasisimple K :=
    ⟨⟨hq.1⟩, hq.2, quasisimple_central_quotient_nonabelian K hq⟩
  obtain ⟨i, ⟨e⟩⟩ := hcat
  cases i with
  | cyclic r hr =>
    exfalso
    obtain ⟨a, b, hab⟩ := hq'.2.2
    apply hab
    apply e.injective
    rw [map_mul, map_mul]
    exact mul_comm (G := Multiplicative (ZMod r)) _ _
  | alternating n hn =>
    exfalso
    have hdvd := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hq' e
    rw [(CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput n hn).2] at hdvd
    have h9' := h9.trans hdvd
    split_ifs at h9' <;> omega
  | sporadic s =>
    exfalso
    have hdvd := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hq' e
    have h9' : 9 ∣ sporadicMultiplierOrder s := (hSpM.1 s) ▸ h9.trans hdvd
    revert h9'
    cases s <;> decide
  | lie d => exact lie_center_nine hGA hq d e h9 hc

end CFSG.AGLEmbedding.CompCenterNine
