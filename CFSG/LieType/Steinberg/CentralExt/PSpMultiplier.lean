module

public import CFSG.LieType.Steinberg.CentralExt.SpCentrallyClosed
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticModelOuterTwoPart
public import CFSG.ClassicalGroups.Symplectic.Perfect
public import CFSG.RankThree.PerfectCover.HopfFormula

public section

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial

namespace CFSG.LieType.Steinberg.CentralExt.SpClosed

theorem isPerfect_statedSp (n : ℕ) (K : Type) [Field K] (hK : 4 ≤ Nat.card K) :
    Group.IsPerfect (StatedSp n K) := by
  have : Group.IsPerfect (TauCeti.GLSymplecticFin n K) :=
    CFSG.ClassicalGroups.Symplectic.isPerfect_GLSymplecticFin K n (Or.inl (Or.inr hK))
  let e : TauCeti.GLSymplecticFin n K ≃* StatedSp n K :=
    (TauCeti.GLSymplecticFin.mulEquivGLSymplectic n K).trans
      (MulEquiv.subgroupCongr (CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic
        (n := n) (K := K)).symm)
  exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

theorem psp_hopfMultiplier {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n)
    (hK : 5 ≤ Nat.card K) :
    commutator (StatedProj (StatedSp n K)) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier (StatedProj (StatedSp n K)) ≃*
        Multiplicative (ZMod (Nat.gcd 2 (Nat.card K - 1)))) := by
  set Z := SymplecticHigher.spScalars n K
  set q : StatedSp n K →* StatedProj (StatedSp n K) := QuotientGroup.mk' Z
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hker : q.ker = Z := QuotientGroup.ker_mk' _
  have hZc : Z ≤ Subgroup.center (StatedSp n K) := SymplecticHigher.spScalars_le_center
  have : Group.IsPerfect (StatedSp n K) :=
    isPerfect_statedSp n K (by omega)
  have hperf : Group.IsPerfect (StatedProj (StatedSp n K)) := Group.IsPerfect.ofSurjective hq
  refine ⟨Group.IsPerfect.commutator_eq_top, ?_⟩
  have e1 : CFSG.RankThree.PerfectCover.hopfMultiplier (StatedProj (StatedSp n K)) ≃* q.ker :=
    MulEquiv.ofBijective _ (SL2Closed.hopfMultiplierToKer_bijective q hq (hker ▸ hZc)
      fun π hπ hcen => sp_exists_section_of_central hn hK hπ hcen)
  have hcard : Nat.card Z = Nat.gcd 2 (Nat.card K - 1) :=
    card_spScalars_eq_gcd K (by omega)
  have hcyc : IsCyclic Z := by
    have h2 : Nat.gcd 2 (Nat.card K - 1) = 1 ∨ Nat.gcd 2 (Nat.card K - 1) = 2 := by
      have hle := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 2 (Nat.card K - 1))
      have hpos := Nat.gcd_pos_of_pos_left (Nat.card K - 1) (show 0 < 2 by norm_num)
      omega
    rcases h2 with h1 | h2
    · have : Subsingleton Z := by
        have := (Nat.card_eq_one_iff_unique (α := Z)).1 (hcard.trans h1)
        exact this.1
      exact isCyclic_of_subsingleton
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact isCyclic_of_prime_card (hcard.trans h2)
  rw [← hcard]
  exact ⟨(CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).trans
    (e1.trans ((MulEquiv.subgroupCongr hker).trans (zmodCyclicMulEquiv hcyc).symm))⟩

end CFSG.LieType.Steinberg.CentralExt.SpClosed
