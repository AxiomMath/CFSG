module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcSuNArith
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcSuNCentre
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KD147cMat
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24A2CubeCentre
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcSuN
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcRDE7
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcRDE8
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcRDF4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419E

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.LocalAnalysis.GLTheoremB
  CFSG.RankThree.Classical2 CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Dickson.Sec6.Up34Exc
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24
open scoped MatrixGroups

section Tags


theorem l3u3_suN_rdSize {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) : RDSize τ := by
  rcases hτ with rfl | rfl | rfl | rfl
  exacts [rdSize_F4, rdSize_E6, rdSize_E7, rdSize_E8]

theorem l3u3_suN_rdGlue {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) : RDGlue τ := by
  rcases hτ with rfl | rfl | rfl | rfl
  exacts [rdGlue_F4, rdGlue_E6, rdGlue_E7, rdGlue_E8]

end Tags

section Main


theorem char2L3U3_suN (hF : L3U3Facts) {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) : Char2L3U3 τ .suN := by
  classical
  intro L _ _ _ p₀ S a hT hap h1 i hk _ hL
  have hTp : rootDiagUnit τ a ^ 3 = 1 := rootDiagUnit_pow_eq_one_of_forall hap
  obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)
  obtain ⟨h2', hn⟩ := suN_rank_ncard hk
  have h3L : ((3 : ℕ) : L) ≠ 0 := by
    have h2 : ((2 : ℕ) : L) = 0 := CharP.cast_eq_zero L 2
    have h3 : ((3 : ℕ) : L) = 1 := by
      have : (3 : ℕ) = 2 + 1 := rfl
      rw [this, Nat.cast_add, h2, zero_add, Nat.cast_one]
    rw [h3]
    exact one_ne_zero
  obtain ⟨ν, ψ, σ, κ, hν, hψ, hκ, hnorm, hΨ⟩ :=
    exists_frame_of_typeA_tag_T_of_prime g2LongA2Frame_proved S Nat.prime_three h3L hTp i h2' hn
  obtain ⟨π, hπ⟩ := two_suN_perm S hT i hk hν hψ hκ hnorm hΨ
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  have hr2 : r = 2 := CharP.eq L hchar (by assumption)
  subst hr2
  obtain ⟨σQ, hσc, z, hzd, f, hf1, hfker, hf2, hfs⟩ :=
    CubeCentre.exists_suN_hom_norm S hT i hν hψ hΨ π hπ hr hchar he hq
  haveI : Fact (Nat.Prime 2) := ⟨hr⟩
  have hes : 0 < e * s := Nat.mul_pos he hs0
  obtain ⟨hfin, hqsC, hc216⟩ := stdUnitary_fixSubgroup (ν := ν) hr hes σQ hσc hν
  haveI := hfin
  haveI : Finite ↥f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  haveI : Finite ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    Finite.of_injective (Subgroup.inclusion hf1) (Subgroup.inclusion_injective hf1)
  have hN : L3U3Order (Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))) := hF.order _ hL
  have hncard : (componentRoots (rootCharHom a) i).ncard = ν * (ν - 1) := by
    rw [hΨ]
    exact kd147c_frameRoots_ncard hψ hκ hnorm
  by_cases h32 : (ν, 2 ^ (e * s)) = (3, 2)
  ·
    exfalso
    have h216 := hc216 h32
    have hR1 : 20160 ≤ Nat.card ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
      hN.ge_20160.trans (Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _))
    have hR2 : Nat.card ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ≤ Nat.card ↥f.range :=
      Subgroup.card_le_of_le hf1
    have hR3 : Nat.card ↥f.range ≤ 216 := by
      rw [← h216]
      exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_range_dvd f)
    omega
  · have hCperf : Group.IsPerfect ↥(fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)) :=
      (hqsC h32).1
    have hRf : f.range = rationalComponent S.ρ S.Γ (rootCharHom a) i :=
      le_antisymm (hf2 hCperf) hf1
    let g : ↥(fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)) →*
        ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
      f.codRestrict _ (fun c => hRf ▸ ⟨c, rfl⟩)
    have hgsurj : Function.Surjective g := by
      rintro ⟨x, hx⟩
      obtain ⟨c, hc⟩ : x ∈ f.range := hRf ▸ hx
      exact ⟨c, Subtype.ext hc⟩
    have hgker : g.ker ≤ Subgroup.center ↥(fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)) := by
      intro c hc
      apply hfker
      rw [MonoidHom.mem_ker] at hc ⊢
      exact congrArg Subtype.val hc
    obtain ⟨eQ⟩ := CFSG.Goldschmidt.G37.nonempty_centerQuotientEquiv hCperf g hgsurj hgker
    have hcardC : Nat.card ↥(fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)) =
        Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) *
        Nat.card ↥(Subgroup.center ↥(fixSubgroup (stdUnitaryEquiv (ν := ν) σQ))) := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
        (Subgroup.center ↥(fixSubgroup (stdUnitaryEquiv (ν := ν) σQ))), Nat.card_congr eQ.toEquiv]
    obtain ⟨F, hFcard, ⟨eC⟩⟩ := two_suN_exists_equiv hr hes σQ hσc hν
    haveI : Finite ↥F := Nat.finite_of_card_ne_zero (by
      rw [hFcard]
      exact (pow_pos (pow_pos Nat.two_pos _) 2).ne')
    haveI : CharP ↥F 2 := inferInstance
    have hU : UnitaryFieldData 2 (e * s) ↥F :=
      ⟨hr, hes, by rw [hFcard, ← pow_mul, mul_comm]⟩
    have hint := CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_statedSU_int hU (n := ν) (by omega)
    have hZ := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 2)
      (f := e * s) hFcard hν h32).2
    have hodd : Odd (Nat.card ↥(Subgroup.center ↥(fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)))) := by
      rw [← Nat.card_congr (Subgroup.centerCongr eC).toEquiv]
      exact two_suN_center_odd (by omega) hZ
    rw [Nat.card_congr eC.toEquiv, hcardC] at hint
    have hes1 : 1 ≤ e * s := by omega
    rcases (by omega : ν = 3 ∨ ν = 4 ∨ 5 ≤ ν) with h3 | h4 | h5
    ·
      subst h3
      obtain ⟨hm2, hm3⟩ := l3u3_suN_three_arith hN hes1 hodd hint
      have hQ3 : 3 ∣ 2 ^ (e * s) + 1 := l3u3_suN_three_dvd_two_pow_add_one hm2
      have hs3 : ¬ 3 ∣ s := fun h => hm3 (Dvd.dvd.mul_left h e)
      have hi6 : (componentRoots (rootCharHom a) i).ncard = 6 := by rw [hncard]
      obtain ⟨X₀, hX₀c, hψX₀⟩ :=
        l3u3_suN_exists_central_frame (l3u3_suN_rdGlue hτ) hap h1 i hi6 hψ hΨ
      have hX₀C := CubeCentre.center_le_fixSubgroup σQ hσc hQ3 hX₀c
      have hzX : z * ψ X₀ * z⁻¹ = ψ X₀ := by
        rw [hψX₀, ← hzd, mul_inv_cancel_right]
      have hstepX : S.D.step (z * ψ X₀ * z⁻¹) = z * ψ X₀ * z⁻¹ := by
        rw [hzX, hψX₀]
        exact CubeCentre.step_rootDiagUnit S hT
      have hfX : f ⟨X₀, hX₀C⟩ = (z * ψ X₀ * z⁻¹) ^ s := hfs ⟨X₀, hX₀C⟩ hstepX
      rw [hzX, hψX₀] at hfX
      refine ⟨rootDiagUnit τ a ^ s, ?_, ?_, ?_, ?_⟩
      · rw [← hRf]
        exact ⟨⟨X₀, hX₀C⟩, hfX⟩
      · intro g' hg'
        have hgc := ((langSubnormal_of_mem_torus S hT i).1 hg').2
        have h := Subgroup.mem_centralizer_singleton_iff.1 hgc
        exact (Commute.pow_right (show Commute g' (rootDiagUnit τ a) from h) s).eq
      · rw [← pow_mul, mul_comm, pow_mul, hTp, one_pow]
      · intro hw
        apply h1
        have h3d : orderOf (rootDiagUnit τ a) ∣ 3 := orderOf_dvd_of_pow_eq_one hTp
        have hsd : orderOf (rootDiagUnit τ a) ∣ s := orderOf_dvd_of_pow_eq_one hw
        have hcop : Nat.Coprime 3 s := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hs3
        have hdg := Nat.dvd_gcd h3d hsd
        rw [hcop] at hdg
        exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hdg)
    ·
      exfalso
      have hsz := l3u3_suN_rdSize hτ L a hap i
      rw [hncard, h4] at hsz
      omega
    · exact (l3u3_suN_ge_five_arith h5 hN hes1 hodd hint).elim

end Main

end CFSG.LocalAnalysis.GLTheoremA.K1419E

end
