module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212InputsProofCover
public import CFSG.Open.GriessAllModelsStatement
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.CenterCyclic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint.Multiplier (genericOrders exceptionalOrders)
open CFSG.RankThree.PerfectCover (hopfMultiplier hopfMultiplierEquivGriess)

theorem exists_char_pow_card (K : Type) [Field K] [Finite K] :
    ∃ r f : ℕ, r.Prime ∧ CharP K r ∧ 1 ≤ f ∧ Nat.card K = r ^ f := by
  have := Fintype.ofFinite K
  obtain ⟨r, hchar⟩ := CharP.exists K
  have hr : r.Prime := CharP.char_is_prime K r
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨n, -, hn⟩ := FiniteField.card K r
  exact ⟨r, n, hr, hchar, n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩

theorem exists_card_hopfMultiplier_eq (hGA : CFSG.Open.GriessAllModelsStatement) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) {J : Type} [Group J]
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n r f : ℕ} (hm : CFSG.Models.LieModel J t n r f) :
    ∃ m : ℕ, ¬ p ∣ m ∧ Nat.card (hopfMultiplier J) = (genericOrders t n r f).1 * m := by
  obtain ⟨-, ⟨g⟩⟩ := hGA J t n r f hm
  have hcard : Nat.card (hopfMultiplier J) =
      ((genericOrders t n r f).1 * (genericOrders t n r f).2) *
        ((exceptionalOrders t n r f).1 * (exceptionalOrders t n r f).2) := by
    rw [← Nat.card_congr (hopfMultiplierEquivGriess J).toEquiv, Nat.card_congr g.toEquiv,
      Nat.card_prod]
    unfold CFSG.Blueprint.Multiplier.generic CFSG.Blueprint.Multiplier.exceptional
    simp only [Nat.card_prod, Nat.card_zmod, Nat.card_congr (Multiplicative.toAdd : _ ≃ _)]
  refine ⟨(genericOrders t n r f).2 * ((exceptionalOrders t n r f).1 *
    (exceptionalOrders t n r f).2), not_dvd_multiplierOrders_of_five_le hp hp5 t n r f, ?_⟩
  rw [hcard]
  ring

theorem card_scalars_eq_gcd {n : ℕ} (hn : 1 ≤ n) (K : Type) [Field K] [Finite K] :
    Nat.card (LinearFlag.scalars n K) = Nat.gcd n (Nat.card K - 1) := by
  have hmax : max (Fintype.card (Fin n)) 1 = n := by
    rw [Fintype.card_fin]
    omega
  have : NeZero n := ⟨by omega⟩
  rw [LinearFlag.scalars_eq_center,
    Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity (n := Fin n)
      (R := K)).toEquiv, hmax]
  have h : rootsOfUnity n K = (powMonoidHom n : Kˣ →* Kˣ).ker := by
    ext x
    rw [mem_rootsOfUnity, MonoidHom.mem_ker, powMonoidHom_apply]
  rw [h, IsCyclic.card_powMonoidHom_ker, Nat.card_units, Nat.gcd_comm]

@[expose] noncomputable def l212in_projectiveSLEquivStated (n : ℕ) (K : Type) [Field K] :
    LinearFlag.projectiveSL n K ≃*
      CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL n K) :=
  (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K).symm.trans
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n K)

theorem exists_cover_linear {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hGA : CFSG.Open.GriessAllModelsStatement) {L : Type} [Group L] [Finite L]
    (hL : CFSG.Open.IsQuasisimple L) (hZp : IsPGroup p (center L)) {n : ℕ} (hn : 3 ≤ n)
    {K : Type} [Field K] [Finite K] (e : L ⧸ center L ≃* LinearFlag.projectiveSL n K) :
    ∃ φ : Matrix.SpecialLinearGroup (Fin n) K →* L, Function.Surjective φ ∧
      ∀ s, e (QuotientGroup.mk (φ s)) = LinearFlag.proj n K s := by
  obtain ⟨r, f, hr, -, hf, hcard⟩ := exists_char_pow_card K
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL n r f := by
    refine ⟨hr, hf, by omega, ?_, ?_⟩
    · intro h
      simp only [Prod.mk.injEq] at h
      omega
    · intro h
      simp only [Prod.mk.injEq] at h
      omega
  have hlm : CFSG.Models.LieModel (LinearFlag.projectiveSL n K) .PSL n r f :=
    ⟨hadm, Or.inl ⟨hadm, K, inferInstance, inferInstance, hcard,
      ⟨l212in_projectiveSLEquivStated n K⟩⟩⟩
  obtain ⟨m, hpm, hmcard⟩ := exists_card_hopfMultiplier_eq hGA hp hp5 hlm
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin n) K) :=
    LinearGroups.special_linear_isPerfect (by omega) (Or.inl hn)
  refine exists_cover_of_card hp hL hZp hperf (LinearFlag.proj n K)
    (LinearFlag.proj_surjective n K) ?_ e ⟨m, hpm, ?_⟩
  · rw [LinearFlag.ker_proj]
    exact LinearFlag.scalars_le_center n K
  · rw [hmcard, LinearFlag.ker_proj, card_scalars_eq_gcd (by omega), hcard]
    rfl

end CFSG.LocalAnalysis.RankFourTheoremC
