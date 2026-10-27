module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanAlphaThreeWeakLift
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanAlphaThreeWeakRes
public import CFSG.RankThree.PerfectCover.HopfFormula
public import CFSG.LocalAnalysis.ComponentClassification.TBLitInputs
import CFSG.RankThree.PartTwo.Sec4.Census.Item43Narrow

public section

namespace CFSG.AGLEmbedding.KFactProofs.ThreeWeak

open TauCeti CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier CFSG.Models
  CFSG.RankThree.PerfectCover CFSG.RankThree.PartTwo.Sec4.Census
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)

theorem eq_one_of_pow_three_eq_one {m : ℕ} (hm : ¬ 3 ∣ m) (x : Multiplicative (ZMod m))
    (hx : x ^ 3 = 1) : x = 1 := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero 3)
  have : NeZero m := ⟨hm0⟩
  have h1 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx
  have h2 : orderOf x ∣ m := by
    have := orderOf_dvd_natCard x
    rwa [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod] at this
  have hcop : Nat.Coprime 3 m := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hm
  have h3 : orderOf x ∣ Nat.gcd 3 m := Nat.dvd_gcd h1 h2
  rw [hcop.gcd_eq_one] at h3
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

theorem card_pow_three_le_zmod {a : ℕ} (ha : 0 < a) :
    Nat.card {x : Multiplicative (ZMod a) // x ^ 3 = 1} ≤ 3 := by
  have : NeZero a := ⟨ha.ne'⟩
  classical
  have h := IsCyclic.card_pow_eq_one_le (α := Multiplicative (ZMod a)) (n := 3) (by norm_num)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact h

theorem card_pow_three_le_prod {a b c d : ℕ} (ha : 0 < a) (hb : ¬ 3 ∣ b) (hc : ¬ 3 ∣ c)
    (hd : ¬ 3 ∣ d) :
    Nat.card {x : (Multiplicative (ZMod a) × Multiplicative (ZMod b)) ×
      (Multiplicative (ZMod c) × Multiplicative (ZMod d)) // x ^ 3 = 1} ≤ 3 := by
  have : NeZero a := ⟨ha.ne'⟩
  have h12 : ∀ x : {x : (Multiplicative (ZMod a) × Multiplicative (ZMod b)) ×
      (Multiplicative (ZMod c) × Multiplicative (ZMod d)) // x ^ 3 = 1},
      x.1.1.2 = 1 ∧ x.1.2.1 = 1 ∧ x.1.2.2 = 1 := fun x => by
    have h := x.2
    have e1 := congrArg (fun z => z.1.2) h
    have e2 := congrArg (fun z => z.2.1) h
    have e3 := congrArg (fun z => z.2.2) h
    simp only [Prod.pow_fst, Prod.pow_snd, Prod.fst_one, Prod.snd_one] at e1 e2 e3
    exact ⟨eq_one_of_pow_three_eq_one hb _ e1, eq_one_of_pow_three_eq_one hc _ e2,
      eq_one_of_pow_three_eq_one hd _ e3⟩
  refine le_trans (Nat.card_le_card_of_injective
    (fun x => (⟨x.1.1.1, ?_⟩ : {y : Multiplicative (ZMod a) // y ^ 3 = 1})) ?_)
    (card_pow_three_le_zmod ha)
  · have e := congrArg (fun z => z.1.1) x.2
    simpa only [Prod.pow_fst, Prod.fst_one] using e
  · intro x y hxy
    have hxy' : x.1.1.1 = y.1.1.1 := congrArg Subtype.val hxy
    obtain ⟨hx1, hx2, hx3⟩ := h12 x
    obtain ⟨hy1, hy2, hy3⟩ := h12 y
    exact Subtype.ext (Prod.ext (Prod.ext hxy' (hx1.trans hy1.symm))
      (Prod.ext (hx2.trans hy2.symm) (hx3.trans hy3.symm)))

theorem finite_and_threeTorsion_le (hGA : GriessMultipliersAllModels) {X : Type} [Group X]
    {t : StatedLieTag} {n p f : ℕ} (hm : LieModel X t n p f)
    (ha : 0 < (genericOrders t n p f).1) (hb : ¬ 3 ∣ (genericOrders t n p f).2)
    (hc : ¬ 3 ∣ (exceptionalOrders t n p f).1) (hd : ¬ 3 ∣ (exceptionalOrders t n p f).2) :
    Finite (hopfMultiplier X) ∧ Nat.card {m : hopfMultiplier X // m ^ 3 = 1} ≤ 3 := by
  obtain ⟨-, ⟨eg⟩⟩ := hGA X t n p f hm
  let e : hopfMultiplier X ≃* generic t n p f × exceptional t n p f :=
    (hopfMultiplierEquivGriess X).symm.trans eg
  have : NeZero (genericOrders t n p f).1 := ⟨ha.ne'⟩
  have : NeZero (genericOrders t n p f).2 := ⟨fun h0 => hb (h0 ▸ dvd_zero 3)⟩
  have : NeZero (exceptionalOrders t n p f).1 := ⟨fun h0 => hc (h0 ▸ dvd_zero 3)⟩
  have : NeZero (exceptionalOrders t n p f).2 := ⟨fun h0 => hd (h0 ▸ dvd_zero 3)⟩
  refine ⟨Finite.of_equiv _ e.symm.toEquiv, ?_⟩
  have h := card_pow_three_le_prod ha hb hc hd
  refine le_trans (le_of_eq (Nat.card_congr (e.toEquiv.subtypeEquiv fun m => ?_))) h
  show m ^ 3 = 1 ↔ e m ^ 3 = 1
  rw [← map_pow, ← map_one e, e.injective.eq_iff]

theorem not_three_dvd_exceptional {t : StatedLieTag} {n p f : ℕ}
    (h : ¬ ((t = .PSL ∧ n = 2 ∧ p = 3 ∧ f = 2) ∨ (t = .POmegaOdd ∧ n = 3 ∧ p = 3 ∧ f = 1) ∨
      (t = .G2 ∧ n = 0 ∧ p = 3 ∧ f = 1) ∨ (t = .PSU ∧ n = 4 ∧ p = 3 ∧ f = 1))) :
    ¬ 3 ∣ (exceptionalOrders t n p f).1 ∧ ¬ 3 ∣ (exceptionalOrders t n p f).2 :=
  ⟨fun h3 => h (three_dvd_exceptionalOrders_cases (h3.mul_right _)),
    fun h3 => h (three_dvd_exceptionalOrders_cases (h3.mul_left _))⟩

theorem hopf_threeTorsion_le_of_linuni (hGA : GriessMultipliersAllModels)
    (d : ValidLieTypeIndex) (hd : IsLinUniIndex3 d.1) :
    Finite (hopfMultiplier (CFSGIndex.lie d).Group) ∧
      Nat.card {m : hopfMultiplier (CFSGIndex.lie d).Group // m ^ 3 = 1} ≤ 3 := by
  obtain ⟨dd, hv⟩ := d
  cases dd with
  | A r q =>
    obtain ⟨hr, -⟩ := hd
    refine finite_and_threeTorsion_le hGA (lieModel_typeA r q hv)
      (Nat.gcd_pos_of_pos_left _ (Nat.succ_pos r)) (by simp [genericOrders])
      (not_three_dvd_exceptional ?_).1 (not_three_dvd_exceptional ?_).2 <;>
    · rintro (⟨-, h2, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩)
      · omega
      all_goals exact absurd h (by decide)
  | twistedA r q =>
    obtain ⟨hr, -⟩ := hd
    refine finite_and_threeTorsion_le hGA (lieModel_of_statedClassicalModel
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv (MulEquiv.refl _)))
      (Nat.gcd_pos_of_pos_left _ (Nat.succ_pos r)) (by simp [genericOrders])
      (not_three_dvd_exceptional ?_).1 (not_three_dvd_exceptional ?_).2 <;>
    · rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h2, -⟩)
      all_goals first | omega | exact absurd h (by decide)
  | _ => exact hd.elim

theorem hopf_threeTorsion_le_of_e6 (hGA : GriessMultipliersAllModels) (q : PrimePower)
    (hv : (LieTypeIndex.E6 q).Valid) :
    Finite (hopfMultiplier (CFSGIndex.lie ⟨.E6 q, hv⟩).Group) ∧
      Nat.card {m : hopfMultiplier (CFSGIndex.lie ⟨.E6 q, hv⟩).Group // m ^ 3 = 1} ≤ 3 := by
  refine finite_and_threeTorsion_le hGA (lieModel_of_namesTag (t := .E6) ⟨.E6 q, hv⟩ ⟨rfl, rfl⟩
    ⟨q.prime_p, q.exponent_pos, rfl⟩) (Nat.gcd_pos_of_pos_left _ (by norm_num))
    (by simp [genericOrders]) (not_three_dvd_exceptional ?_).1 (not_three_dvd_exceptional ?_).2 <;>
  · rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩) <;> exact absurd h (by decide)

theorem hopf_threeTorsion_le_of_twistedE6 (hGA : GriessMultipliersAllModels) (q : PrimePower)
    (hv : (LieTypeIndex.twistedE6 q).Valid) :
    Finite (hopfMultiplier (CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group) ∧
      Nat.card {m : hopfMultiplier (CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group // m ^ 3 = 1} ≤ 3 := by
  refine finite_and_threeTorsion_le hGA (lieModel_of_namesTag (t := .twistedE6)
    ⟨.twistedE6 q, hv⟩ ⟨rfl, rfl⟩ ⟨q.prime_p, q.exponent_pos, rfl⟩)
    (Nat.gcd_pos_of_pos_left _ (by norm_num)) (by simp [genericOrders])
    (not_three_dvd_exceptional ?_).1 (not_three_dvd_exceptional ?_).2 <;>
  · rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩) <;> exact absurd h (by decide)

theorem not_kOutTwoGroup_of_cover {K X : Type} [Group K] [Finite K] [Group X]
    (hq : Open.IsQuasisimple K) (hZp : IsPGroup 3 (Subgroup.center K))
    (e : K ⧸ Subgroup.center K ≃* X) [Finite (hopfMultiplier X)]
    (hM : Nat.card {m : hopfMultiplier X // m ^ 3 = 1} ≤ 3) (hdiag : HasDiagOuterThree X) :
    ¬ KOutTwoGroup K := by
  have : Group.IsPerfect K := ⟨hq.1⟩
  let π : K →* X := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center K := by
    ext x
    simp [π]
  obtain ⟨j, hj⟩ := hZp.exists_card_eq
  exact not_kOutTwoGroup_of_diagOuter π hπ hker.le Nat.prime_three
    (by rw [hker]; exact hj) hM hdiag

theorem not_kOutTwoGroup_linuni (hGA : GriessMultipliersAllModels) (hR0 : DiagOuterLinUni)
    {K : Type} [Group K] [Finite K] (hq : Open.IsQuasisimple K)
    (hZp : IsPGroup 3 (Subgroup.center K)) (d : ValidLieTypeIndex) (hd : IsLinUniIndex3 d.1)
    (e : K ⧸ Subgroup.center K ≃* (CFSGIndex.lie d).Group) : ¬ KOutTwoGroup K := by
  obtain ⟨hfin, hM⟩ := hopf_threeTorsion_le_of_linuni hGA d hd
  have := hfin
  exact not_kOutTwoGroup_of_cover hq hZp e hM (hR0 d hd)

theorem not_kOutTwoGroup_e6 (hGA : GriessMultipliersAllModels) (hR1 : DiagOuterE6)
    {K : Type} [Group K] [Finite K] (hq : Open.IsQuasisimple K)
    (hZp : IsPGroup 3 (Subgroup.center K)) (q : PrimePower) (hv : (LieTypeIndex.E6 q).Valid)
    (h3 : 3 ∣ q.card - 1) (e : K ⧸ Subgroup.center K ≃* (CFSGIndex.lie ⟨.E6 q, hv⟩).Group) :
    ¬ KOutTwoGroup K := by
  obtain ⟨hfin, hM⟩ := hopf_threeTorsion_le_of_e6 hGA q hv
  have := hfin
  exact not_kOutTwoGroup_of_cover hq hZp e hM (hR1 q hv h3)

theorem not_kOutTwoGroup_twistedE6 (hGA : GriessMultipliersAllModels)
    (hR1 : DiagOuterTwistedE6) {K : Type} [Group K] [Finite K] (hq : Open.IsQuasisimple K)
    (hZp : IsPGroup 3 (Subgroup.center K)) (q : PrimePower)
    (hv : (LieTypeIndex.twistedE6 q).Valid) (h3 : 3 ∣ q.card + 1)
    (e : K ⧸ Subgroup.center K ≃* (CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group) :
    ¬ KOutTwoGroup K := by
  obtain ⟨hfin, hM⟩ := hopf_threeTorsion_le_of_twistedE6 hGA q hv
  have := hfin
  exact not_kOutTwoGroup_of_cover hq hZp e hM (hR1 q hv h3)

end CFSG.AGLEmbedding.KFactProofs.ThreeWeak
