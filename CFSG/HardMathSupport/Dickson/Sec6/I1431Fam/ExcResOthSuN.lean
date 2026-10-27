module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResOthSUFin
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResComp
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PspHBasic
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsExcAux.SuN
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResDefs

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.ClassicalGroups.Unitary
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open Matrix CFSG.RankThree.Classical CFSG.RankThree.Classical2 CFSG.SectionRank.OddCover
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement MatrixGroups

set_option linter.unusedSectionVars false

theorem excOth_rootDiagUnit_pow_eq_one {τ : Tag} {L : Type} [Field L] {p : ℕ}
    {a : Fin τ.rank → Lˣ} (hap : ∀ i, a i ^ p = 1) : rootDiagUnit τ a ^ p = 1 := by
  have key : ∀ n : ℕ, rootDiagUnit τ a ^ n = rootDiagUnit τ (a ^ n) := by
    intro n
    induction n with
    | zero => rw [pow_zero, pow_zero, rootDiagUnit_one]
    | succ n ih => rw [pow_succ, ih, ← rootDiagUnit_mul, ← pow_succ]
  rw [key p, show a ^ p = 1 from funext fun i => by simpa using hap i, rootDiagUnit_one]

section SuN


theorem excTLKind_suN {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    ExcTLKind .suN τ := by
  intro L _ _ p₀ S a hT ha3 h1 i hk hQS q hq10 hq
  classical
  have hL3 : (3 : L) ≠ 0 := by
    intro h3
    apply h1
    have ha1 : ∀ j, a j = 1 := by
      intro j
      have h' : ((a j : L)) ^ 3 = 1 := by
        have := congrArg Units.val (ha3 j)
        simpa using this
      have h0 : ((a j : L) - 1) ^ 3 = 0 := by
        linear_combination h' + (-(a j : L) ^ 2 + (a j : L)) * h3
      exact Units.ext (sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h0))
    have : a = 1 := funext ha1
    rw [this, rootDiagUnit_one]
  have hTp : rootDiagUnit τ a ^ 3 = 1 := excOth_rootDiagUnit_pow_eq_one ha3
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  obtain ⟨h2', hn⟩ := suN_rank_ncard hk
  obtain ⟨ν, ψ, σ, κ, hν, hψ, hκ, hnorm, hΨ⟩ :=
    exists_frame_of_typeA_tag_T_of_prime g2LongA2Frame_proved S Nat.prime_three hL3 hTp i h2' hn
  obtain ⟨π, hπ⟩ := ssexc_suN_perm S hT i hk hν hψ hκ hnorm hΨ
  obtain ⟨r, e, hr, hchar, he, hq'⟩ := exists_char_pow S
  obtain ⟨σQ, hσc, f, hf1, hfker, hf2⟩ :=
    ssexc_suN_exists_hom S hT i hν hψ hΨ π hπ hr hchar he hq'
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP L r := hchar
  have hes : 0 < e * s := Nat.mul_pos he hs0
  obtain ⟨hfin, hqsC, hcard⟩ := stdUnitary_fixSubgroup (ν := ν) hr hes σQ hσc hν
  haveI := hfin
  haveI : Finite ↥f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  haveI : Finite ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    Finite.of_injective (Subgroup.inclusion hf1) (Subgroup.inclusion_injective hf1)
  by_cases hne : (ν, r ^ (e * s)) = (3, 2)
  ·
    have h216 := hcard hne
    have hle : Nat.card ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ≤ 216 := by
      calc Nat.card ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ≤ Nat.card ↥f.range :=
            Subgroup.card_le_of_le hf1
        _ ≤ Nat.card ↥(fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)) :=
            Nat.card_le_card_of_surjective _ f.rangeRestrict_surjective
        _ = 216 := h216
    exact t6psph_not_isTypeL2_of_card_lt hq10 (by omega) hq
  · have hCperf : Group.IsPerfect ↥(fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)) := (hqsC hne).1
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
    have hqC := (excres_isTypeL2_of_central_surjection hCperf g hgsurj hgker).1 hq
    obtain ⟨F, hFcard, ⟨e'⟩⟩ := ssexc_suN_exists_equiv hr hes σQ hσc hν
    have hqS := p6_isTypeL2_of_equiv e'.symm hqC
    haveI : Finite F := Nat.finite_of_card_ne_zero (by
      rw [hFcard]
      exact (pow_pos (pow_pos hr.pos _) 2).ne')
    haveI : CharP F r := charP_of_card_sq hFcard
    have hSU : SUid (unitaryInvolution F r (e * s)) ν = StatedSU ν (r ^ (e * s)) F :=
      SUid_eq_statedSU hFcard ν
    have hqS' := p6_isTypeL2_of_equiv (MulEquiv.subgroupCongr hSU.symm) hqS
    obtain ⟨F', _, _, _, ⟨φ⟩⟩ := hqS'
    exact excOth_suid_no_psl2 hFcard hν hne φ

end SuN

end CFSG.HardMathSupport.Dickson.Sec6.I1431
