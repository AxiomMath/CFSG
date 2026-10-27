module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActUnitary
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsExcAux.SuN
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KD147cMat
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTame.Order216

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LieType.AlgebraicGroups CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.PerfectAutomorphisms CFSG.GroupActions
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open scoped Pointwise commutatorElement


theorem suN_not_small_of_isQuasisimple {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    [CharP L 2] {p₀ : ℕ} (S : LangSetup τ L p₀) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hTp : rootDiagUnit τ a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (hkind : twistKind S.ρ (rootCharHom a) i = .suN)
    (hQS : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    ¬ (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 2 ∧
      (componentRoots (rootCharHom a) i).ncard = 6) := by
  classical
  rintro ⟨hQ2, hn6⟩
  have hpL : ((p : ℕ) : L) ≠ 0 := by
    intro h
    have hd : 2 ∣ p := (CharP.cast_eq_zero_iff L 2 p).1 h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 hd).symm
  obtain ⟨h2, hn⟩ := suN_rank_ncard hkind
  obtain ⟨ν, ψ, σf, κ, hν, hψ, hκ, hnorm, hΨ⟩ :=
    exists_frame_of_typeA_tag_T_of_prime g2LongA2Frame_proved S hp hpL hTp i h2 hn
  have hν3 : ν = 3 := by
    have hc := CFSG.LocalAnalysis.GLTheoremA.kd147c_frameRoots_ncard hψ hκ hnorm
    rw [← hΨ, hn6] at hc
    have hνle : ν ≤ 6 := by
      by_contra h
      have h7 : 7 ≤ ν := by omega
      have h1 : 6 ≤ ν - 1 := by omega
      have hmono : 7 * 6 ≤ ν * (ν - 1) := Nat.mul_le_mul h7 h1
      omega
    interval_cases ν <;> norm_num at hc
    rfl
  obtain ⟨π, hπ⟩ :=
    CFSG.HardMathSupport.Dickson.Sec6.ssexc_suN_perm S hT i hkind hν hψ hκ hnorm hΨ
  obtain ⟨-, h216⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.rationalComponent_of_unitary_frame_T
      S hT i hν hψ hΨ π hπ
  have hdiv : Nat.card (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∣ 216 :=
    h216 (Prod.ext hν3 hQ2)
  have hsolv : Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    isSolvable_of_card_dvd_216 hdiv
  haveI : Group.IsPerfect (rationalComponent S.ρ S.Γ (rootCharHom a) i) := hQS.1
  haveI : Nontrivial (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    obtain ⟨u, v, huv⟩ := hQS.2.2
    exact huv (Subsingleton.elim (u * v) (v * u))
  exact Group.IsPerfect.not_isSolvable _ hsolv

theorem centerQuotientHom_mem_innAutDerived_unitaryKind_of_elementOrder
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) (hp2 : p ≠ 2)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hTp : rootDiagUnit τ a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (hkind : twistKind S.ρ (rootCharHom a) i = .suN)
    (hnot : ¬ (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 2 ∧
      (componentRoots (rootCharHom a) i).ncard = 6))
    {y : ModGL τ L}
    (hyZ : y ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)))
    (hyF : S.D.step y = y)
    (hyStab : MulAut.conj y ∈ subgroupStabAut
      (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    centerQuotientHom ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)
        (subgroupStabRestrict (rationalComponent S.ρ S.Γ (rootCharHom a) i)
          ⟨MulAut.conj y, hyStab⟩) ∈
      innAutDerived (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  classical
  have hpL : ((p : ℕ) : L) ≠ 0 := by
    intro h
    have hd : 2 ∣ p := (CharP.cast_eq_zero_iff L 2 p).1 h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 hd).symm
  obtain ⟨h2, hn⟩ := suN_rank_ncard hkind
  obtain ⟨ν, ψ, σf, κ, hν, hψ, hκ, hnorm, hΨ⟩ :=
    exists_frame_of_typeA_tag_T_of_prime g2LongA2Frame_proved S hp hpL hTp i h2 hn
  obtain ⟨π, hπ⟩ :=
    CFSG.HardMathSupport.Dickson.Sec6.ssexc_suN_perm S hT i hkind hν hψ hκ hnorm hΨ
  have h32 : (ν, S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) ≠
      (3, 2) := by
    rintro h
    have hν3 : ν = 3 := congrArg Prod.fst h
    have hq2 : S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 2 :=
      congrArg Prod.snd h
    apply hnot
    refine ⟨hq2, ?_⟩
    rw [hΨ, CFSG.LocalAnalysis.GLTheoremA.kd147c_frameRoots_ncard hψ hκ hnorm, hν3]
  exact centerQuotientHom_mem_innAutDerived_unitaryFrame S hT i hν hψ hΨ π hπ h32 hyZ hyF hyStab

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
