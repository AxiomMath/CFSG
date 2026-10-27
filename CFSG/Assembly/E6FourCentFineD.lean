module

public import CFSG.Assembly.E6FourFineComp
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTypeA

public section

namespace CFSG.Assembly

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.KD4T
  CFSG.RankThree.Lattice CFSG.LieType.SeitzGeneration
open scoped Matrix


theorem e6Four_rho_sq_of_table {L : Type} [Field L] [IsAlgClosed L] (S : LangSetup Tag.E6 L 5)
    (hρ : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = (wordMat Tag.E6 e6TwoWord) *ᵥ γ) :
    ∀ γ, IsRoot Tag.E6 γ → S.ρ (S.ρ γ) = γ := by
  intro γ hγ
  have hγ' : IsRoot Tag.E6 (S.ρ γ) := (S.frob.isRoot_iff γ).2 hγ
  rw [hρ (S.ρ γ) hγ', hρ γ hγ, Matrix.mulVec_mulVec, ← pow_two, e6Two_pow,
    Matrix.one_mulVec]

theorem e6Four_D4_fine {L : Type} [Field L] [IsAlgClosed L] (S : LangSetup Tag.E6 L 5)
    (hq : S.D.q = 4)
    (hρ2 : ∀ γ, IsRoot Tag.E6 γ → S.ρ (S.ρ γ) = γ)
    (hΦ : ∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = Units.map (entrywiseHom Fr))
    {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (hap : ∀ j, a j ^ 5 = 1) (h1 : rootDiagUnit Tag.E6 a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 4)
    (hn : (componentRoots (rootCharHom a) i).ncard = 24)
    (hs : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1)
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _))) :
    LieModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) .POmegaMinus 4 2 2 := by
  classical
  have hℓp : ringChar L ≠ 5 :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_ne_of_pow_eq_one
      Nat.prime_five hap h1
  have hpL : ((5 : ℕ) : L) ≠ 0 :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.natCast_ne_zero_of_ringChar_ne
      Nat.prime_five hℓp
  have hTp : rootDiagUnit Tag.E6 a ^ 5 = 1 :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.rootDiagUnit_pow_eq_one_of_forall hap
  have hE6 := e6FixDNAll_proved
  obtain ⟨v, hv, hρ'⟩ := S.d4_pinnedT_of_prime Nat.prime_five hpL facts_E6 kacCount_E6_four
    (by decide) (by decide)
    (fun y hy => far_d4_E6 y fun z hz => by
      have h := hy z hz
      rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
    ⟨none, by decide⟩ (lt_of_eq_of_lt kacCount_far_E6 (by decide)) hT hTp i hr hn
  obtain ⟨Fr, hFr, hΦ'⟩ := hΦ
  obtain ⟨w, hnw⟩ := S.D.n_weyl
  have hρw : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = w • γ :=
    fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ' hnw hγ
  obtain ⟨r, e, hr, hchar, he, hq'⟩ := exists_char_pow S
  have hre : r ^ e = 4 := by rw [← hq', hq]
  have hr2 : r = 2 := by
    have hdvd : r ∣ 4 := by rw [← hre]; exact dvd_pow_self r (Nat.ne_of_gt he)
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num] at hdvd
    exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow hdvd)
  have he2 : e = 2 := by
    have h2 : (2 : ℕ) ^ e = 2 ^ 2 := by
      rw [hr2] at hre
      rw [hre]; norm_num
    exact Nat.pow_right_injective (a := 2) (by norm_num) h2
  subst r; subst e
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP L 2 := hchar
  have hq2 : S.D.q = 2 ^ 2 := by rw [hq]; norm_num
  have hnin : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _) ^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]) := by
    rw [hs, Function.iterate_one]
    exact hout
  exact
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.E6FourFine.fine_rationalComponent_of_d4_outer
      (ℓ := 2) (f := 2) d4Base_E6 (d4SwapLayer_E6 hE6)
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.E6FourFine.d4SwapLayerFine_E6
      S hFr hΦ' hnw hρw hρ2 i v hv hρ' hnin (by norm_num) hq2

end CFSG.Assembly

end
