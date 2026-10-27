module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongGammaDefs
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPSL
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPSp
public import CFSG.HardMathSupport.Lang.Proving.FixedOrderCongruence
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421LinGrp
public import CFSG.Adapters.LinearCatalogStated
public import CFSG.RankThree.PartOne.FOC.PSLTwoOuter
public import CFSG.RankThree.PartTwo.KFacts.K71OddChar
public import CFSG.SignalizerFunctorTheorem.NonLocal.SpTwoTwo
public import CFSG.RankThree.PartOne.S11d.PSpGood

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongFieldAut

open CFSG.Open Subgroup
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedProj StatedSL StatedSp StatedSU)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem not_pSolvable_fixed_of_equiv {J : Type*} [Group J] [Finite J] {p : ℕ} (hp : p.Prime)
    (hpJ : p ∣ Nat.card J) (α : MulAut J) (hα : α ^ p = 1) {S : Type*} [Group S]
    (e : ↥(fixedSubgroup α) ≃* S)
    (hS : p ∣ Nat.card S → ¬ CFSG.HallHigman.IsPSolvable p S) :
    ¬ CFSG.HallHigman.IsPSolvable p ↥(fixedSubgroup α) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  intro hsolv
  have hmod := CFSG.HardMathSupport.Lang.Proving.card_modEq_card_fixedPoints_of_pow_prime α hα
  have h1 : p ∣ Nat.card ↥(fixedSubgroup α) := by
    have h2 : Nat.card ↥(fixedSubgroup α) ≡ 0 [MOD p] :=
      (show Nat.card ↥(fixedSubgroup α) ≡ Nat.card J [MOD p] from hmod.symm).trans
        ((Nat.modEq_zero_iff_dvd).2 hpJ)
    exact (Nat.modEq_zero_iff_dvd).1 h2
  have h3 : p ∣ Nat.card S := by
    rw [← Nat.card_congr e.toEquiv]
    exact h1
  exact hS h3
    (CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
      e hsolv)

theorem not_pSolvable_of_simple_nonabelian {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnc : ¬ ∀ a b : S, a * b = b * a) {p : ℕ} (hp : p.Prime) :
    p ∣ Nat.card S → ¬ CFSG.HallHigman.IsPSolvable p S := by
  intro hpS hsolv
  haveI : Fact p.Prime := ⟨hp⟩
  have hne : Nat.card S ≠ p := by
    intro hc
    haveI : Fact (Nat.card S).Prime := ⟨hc ▸ hp⟩
    haveI := isCyclic_of_prime_card hc
    exact hnc fun a b => (IsCyclic.commGroup (α := S)).mul_comm a b
  exact CFSG.LocalAnalysis.RankThreeUC.S15.K421GrpProof.not_isPSolvable_of_simple hS hp hpS hne
    hsolv

def fixedSubgroupEquivOfIntertwine {G H : Type*} [Group G] [Group H] (v : G ≃* H)
    (α : MulAut G) (β : MulAut H) (hβ : ∀ x, β (v x) = v (α x)) :
    fixedSubgroup α ≃* fixedSubgroup β where
  toFun x := ⟨v x, by
    have hx : α x = x := x.2
    change β (v x) = v x
    rw [hβ, hx]⟩
  invFun y := ⟨v.symm y, by
    have hy : β y = y := y.2
    change α (v.symm y) = v.symm y
    apply v.injective
    rw [← hβ, v.apply_symm_apply, hy]⟩
  left_inv x := Subtype.ext (v.symm_apply_apply x)
  right_inv y := Subtype.ext (v.apply_symm_apply y)
  map_mul' x y := Subtype.ext (map_mul v (x : G) (y : G))

theorem not_pSolvable_fixed_of_simple {J : Type*} [Group J] [Finite J] {p : ℕ} (hp : p.Prime)
    (hpJ : p ∣ Nat.card J) (α : MulAut J) (hα : α ^ p = 1) {S : Type} [Group S] [Finite S]
    (hS : IsSimpleGroup S) (hnc : ¬ ∀ a b : S, a * b = b * a)
    (e : ↥(fixedSubgroup α) ≃* S) : ¬ CFSG.HallHigman.IsPSolvable p ↥(fixedSubgroup α) :=
  not_pSolvable_fixed_of_equiv hp hpJ α hα e (not_pSolvable_of_simple_nonabelian hS hnc hp)

theorem not_comm_of_simple_of_not_prime {S : Type} [Group S] [IsSimpleGroup S]
    (hc : ¬ (Nat.card S).Prime) : ¬ ∀ a b : S, a * b = b * a := by
  intro h
  letI : CommGroup S := { ‹Group S› with mul_comm := h }
  exact hc (IsSimpleGroup.prime_card (α := S))

theorem fixed_not_pSolvable_PSL_two {K : Type} [Group K] [Finite K] {ℓ f : ℕ}
    (hcl : StatedClassicalModel K .PSL 2 ℓ f) (hℓ2 : ℓ = 2) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpK : p ∣ Nat.card K) (α : MulAut K) (hαp : α ^ p = 1) (hαin : α ∉ inner K) :
    ¬ CFSG.HallHigman.IsPSolvable p ↥(fixedSubgroup α) := by
  classical
  obtain ⟨⟨hℓ, hf, -⟩, F, hF, hFin, hFcard, ⟨e⟩⟩ := hcl
  subst hℓ2
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  let ψ : K ≃* CFSG.ComponentClassification.CatalogueSchreierLinearTwo.coordinateG F :=
    (e.trans (CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.statedProjSLEquiv 2 F)).trans
      ((CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        2 F).symm.trans
        (CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pslEquivCoordinateG F))
  have hαord : orderOf α = p := by
    refine orderOf_eq_prime hαp ?_
    intro h1
    exact hαin (h1 ▸ (CFSG.ComponentClassification.OuterAutomorphisms.inner K).one_mem)
  obtain ⟨hpf, k, hkcard, ⟨eX⟩⟩ :=
    CFSG.RankThree.PartOne.FOC.psl_two_fixSub_equiv_gen hℓ hp hp2 hf hFcard ψ hαord hαin
  have e1 : ↥(fixedSubgroup α) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) ↥k :=
    (MulEquiv.subgroupCongr (Subgroup.ext fun _ => Iff.rfl :
        fixedSubgroup α = CFSG.RankThree.PartOne.Sec66T.fixSub α)).trans
      (eX.trans
        (CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pslEquivCoordinateG ↥k).symm)
  have hf1 : 0 < f / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) hp.pos
  have hdvd2 : 2 ∣ Nat.card ↥k := by
    rw [hkcard]
    exact dvd_pow_self 2 (by omega)
  have hq : Nat.card ↥k = 2 ∨ 4 ≤ Nat.card ↥k := by
    rw [hkcard]
    rcases Nat.lt_or_ge (f / p) 2 with hlt | hge
    · left
      norm_num [show f / p = 1 by omega]
    · right
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (f / p) := Nat.pow_le_pow_right (by norm_num) hge
  have hcard := CFSG.RankThree.PartTwo.KFacts.card_psl_mul_gcd (K := ↥k) (n := 2) (by norm_num)
  have hS : p ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) ↥k) →
      ¬ CFSG.HallHigman.IsPSolvable p (Matrix.ProjectiveSpecialLinearGroup (Fin 2) ↥k) := by
    rcases hq with h2 | h4
    · rw [h2] at hcard
      norm_num at hcard
      intro hpS
      rw [hcard] at hpS
      have hp6 : p ≤ 6 := Nat.le_of_dvd (by norm_num) hpS
      interval_cases p
      · norm_num at hpS
      · norm_num at hp
    · have hne2 : Nat.card ↥k ≠ 2 := by omega
      have hne3 : Nat.card ↥k ≠ 3 := by omega
      have hsimple : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) ↥k) :=
        CFSG.BenderSuzuki.External.huppert_II_6_13 (K := ↥k) 2 (by norm_num)
          (Or.inr hne2) (Or.inr hne3)
      have hodd : ¬ 2 ∣ Nat.card ↥k - 1 := by omega
      have hgcd : Nat.gcd (Nat.card ↥k - 1) 2 = 1 :=
        Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd).symm
      have hcard' : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) ↥k) =
          Nat.card ↥k * (Nat.card ↥k ^ 2 - 1) := by
        rw [hgcd, mul_one] at hcard
        simpa [Finset.prod_singleton] using hcard
      have hnp : ¬ (Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) ↥k)).Prime := by
        intro hpr
        have hdvd : Nat.card ↥k ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) ↥k) :=
          ⟨Nat.card ↥k ^ 2 - 1, hcard'⟩
        rcases hpr.eq_one_or_self_of_dvd _ hdvd with h1 | h1
        · omega
        · rw [hcard'] at h1
          have h16 : 16 ≤ Nat.card ↥k ^ 2 := by nlinarith
          have hr : 2 ≤ Nat.card ↥k ^ 2 - 1 := by omega
          have hm := Nat.mul_le_mul_left (Nat.card ↥k) hr
          omega
      have hnc : ¬ ∀ a b : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ↥k, a * b = b * a :=
        not_comm_of_simple_of_not_prime hnp
      intro hpS
      exact not_pSolvable_of_simple_nonabelian hsimple hnc hp hpS
  exact not_pSolvable_fixed_of_equiv hp hpK α hαp e1 hS

theorem fixed_not_pSolvable_PSL_three {K : Type} [Group K] [Finite K] {ℓ f : ℕ}
    (hcl : StatedClassicalModel K .PSL 3 ℓ f) (hℓ2 : ℓ = 2) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpK : p ∣ Nat.card K) (α : MulAut K) (hαp : α ^ p = 1) (hαin : α ∉ inner K) :
    ¬ CFSG.HallHigman.IsPSolvable p ↥(fixedSubgroup α) := by
  open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
    CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCLinearSubfield
    CFSG.HardMathSupport.Lang.Coordinator CFSG.HardMathSupport.Lang.UnitaryAutomorphisms in
  open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield) in
  classical
  subst hℓ2
  obtain ⟨⟨hℓ, hf, -, -, -⟩, F, hF, hFin, hFcard, ⟨e⟩⟩ := hcl
  have : Fact (Nat.Prime 2) := ⟨hℓ⟩
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype F := Fintype.ofFinite F
  have hFcard' : Fintype.card F = 2 ^ f := by rw [← Nat.card_eq_fintype_card]; exact hFcard
  have : CharP F 2 := charP_of_card_eq_prime_pow hFcard'
  have hdiv : ¬ p ∣ Nat.gcd 3 (Nat.card F - 1) := fun h => by
    have h3 : p ∣ 3 := h.trans (Nat.gcd_dvd_left _ _)
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  let θ : K ≃* projectiveSL 3 F := e.trans (statedProjSLEquiv 3 F)
  set β := MulAut.congr θ α with hβdef
  have hβp : β ^ p = 1 := by rw [hβdef, ← map_pow, hαp, map_one]
  have hβout : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL 3 F) :=
    fun hin => hαin ((CFSG.HardMathSupport.Lang.Coordinator.congr_mem_inner_iff θ α).mp hin)
  have hβ1 : β ≠ 1 := fun h1 => hβout (h1 ▸
    (CFSG.ComponentClassification.OuterAutomorphisms.inner _).one_mem)
  have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
  have hβE : β ∈ semilinearAutGroup 3 F :=
    CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.mem_semilinearAutGroup_of_pow
      (by norm_num) (hp.odd_of_ne_two (by omega)) hβp
  by_cases hD : β ∈ linearAutGroup 3 F
  · exfalso
    exact hβout (CFSG.RankThree.PartOne.OutStructure.linear_D2 hp (by norm_num) hdiv β hD 1
      (by
        rw [pow_one, hβp]
        exact (CFSG.ComponentClassification.OuterAutomorphisms.inner _).one_mem))
  obtain ⟨-, σ, hσord, ⟨h, hh, hβh⟩, -⟩ :=
    higher_linear_prime_semilinear_field_descent' hℓ hf (by norm_num) hFcard hp β hβE hD hβord
  have hconj : ∃ v : MulAut (projectiveSL 3 F), ∀ x, β (v x) = v ((fieldAut 3 F σ) x) := by
    obtain ⟨H, rfl⟩ := mem_linearAutGroup_iff.mp hh
    refine ⟨conjAut 3 F H, fun x => ?_⟩
    rw [hβh]
    simp [MulAut.mul_apply]
  obtain ⟨v, hv⟩ := hconj
  let hequiv1 : fixedSubgroup (fieldAut 3 F σ) ≃* fixedSubgroup β :=
    fixedSubgroupEquivOfIntertwine v (fieldAut 3 F σ) β hv
  have hfix : fixedSubgroup (fieldAut 3 F σ) =
      (linearSubfieldInclusion 3 (semilinearFixedSubfield σ)).range :=
    SetLike.coe_injective (fixedSubgroup_fieldAut_eq_range hp (by norm_num) hdiv σ hσord)
  have hinj := linearSubfieldInclusion_injective (K := F) (n := 3) (by norm_num)
    (semilinearFixedSubfield σ)
  let e1 : ↥(fixedSubgroup α) ≃* projectiveSL 3 ↥(semilinearFixedSubfield σ) :=
    (CFSG.Sporadic.HeldB.fixedSubgroupCongr θ α).trans (hequiv1.symm.trans
      ((MulEquiv.subgroupCongr hfix).trans (MonoidHom.ofInjective hinj).symm))
  have hsimple : IsSimpleGroup (projectiveSL 3 ↥(semilinearFixedSubfield σ)) :=
    CFSG.RankThree.PartOne.KCLinearSubfield.isSimpleGroup_projectiveSL (by norm_num)
  have hnc : ¬ ∀ a b : projectiveSL 3 ↥(semilinearFixedSubfield σ), a * b = b * a :=
    CFSG.RankThree.PartOne.KCLinearSubfield.not_commutative_projectiveSL (by norm_num)
  haveI : Finite (projectiveSL 3 ↥(semilinearFixedSubfield σ)) :=
    Finite.of_equiv _ e1.toEquiv
  exact not_pSolvable_fixed_of_simple hp hpK α hαp hsimple hnc e1

theorem not_pSolvable_statedProj_sp_two_two {k : Type} [Field k] [Finite k] (hk : Nat.card k = 2)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpd : p ∣ Nat.card (StatedProj (StatedSp 2 k))) :
    ¬ CFSG.HallHigman.IsPSolvable p (StatedProj (StatedSp 2 k)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hinj : Function.Injective (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj 2 k) :=
    CFSG.RankThree.PartOne.proj_injective_sp (r := 2) (K := k) (f := 1) (by simp [hk]) le_rfl
      (by norm_num)
  have hsurj : Function.Surjective (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj 2 k) :=
    CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.proj_surjective
  let eP : StatedSp 2 k ≃* StatedProj (StatedSp 2 k) :=
    MulEquiv.ofBijective (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj 2 k)
      ⟨hinj, hsurj⟩
  have hcard : Nat.card (StatedProj (StatedSp 2 k)) = 720 := by
    rw [← Nat.card_congr eP.toEquiv,
      CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp_two, hk]
    all_goals norm_num
  haveI : Finite (StatedProj (StatedSp 2 k)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hp360 : p ∣ 360 := by
    have hcop : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).2 (by omega)
    refine Nat.Coprime.dvd_of_dvd_mul_left hcop ?_
    rw [show (2 : ℕ) * 360 = 720 by norm_num, ← hcard]
    exact hpd
  intro hsolv
  let f : ↥(commutator (StatedSp 2 k)) →* StatedProj (StatedSp 2 k) :=
    (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj 2 k).comp
      (commutator (StatedSp 2 k)).subtype
  have hfinj : Function.Injective f := hinj.comp (Subgroup.subtype_injective _)
  let eT : ↥f.range ≃* alternatingGroup (Fin 6) :=
    (MonoidHom.ofInjective hfinj).symm.trans
      (CFSG.SignalizerFunctorTheorem.NonLocal.commutatorSpTwoEquiv hk)
  have hsolvTop : CFSG.HallHigman.IsPSolvable p ↥(⊤ : Subgroup (StatedProj (StatedSp 2 k))) :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
      Subgroup.topEquiv.symm hsolv
  have hT : CFSG.HallHigman.IsPSolvable p ↥f.range :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_of_le hsolvTop
      le_top
  have hA6 : CFSG.HallHigman.IsPSolvable p (alternatingGroup (Fin 6)) :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
      eT hT
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hnc : ¬ ∀ a b : alternatingGroup (Fin 6), a * b = b * a := by
    intro h
    have hc : IsMulCommutative (alternatingGroup (Fin 6)) := ⟨⟨fun a b => h a b⟩⟩
    have h3 := (alternatingGroup.isMulCommutative_iff_card_le_three (α := Fin 6)).1 hc
    simp at h3
  have h360 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num [Nat.factorial]
  exact not_pSolvable_of_simple_nonabelian hsimple hnc hp (by rw [h360]; exact hp360) hA6

theorem fixed_not_pSolvable_PSp_two {K : Type} [Group K] [Finite K] {ℓ f : ℕ}
    (hcl : StatedClassicalModel K .PSp 2 ℓ f) (hℓ2 : ℓ = 2) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpK : p ∣ Nat.card K) (α : MulAut K) (hαp : α ^ p = 1) (hαin : α ∉ inner K) :
    ¬ CFSG.HallHigman.IsPSolvable p ↥(fixedSubgroup α) := by
  classical
  subst hℓ2
  obtain ⟨⟨hℓ, hf, hn, -⟩, F, hF, hFin, hFcard, ⟨e⟩⟩ := hcl
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨-, -, -, -, -, -, -, hidx, hDH, hdesc⟩ :=
    CFSG.RankThree.Classical.SteinbergBY.symplectic_prime_semilinear_field_descent hℓ hf hn hFcard
  set β := MulAut.congr e α with hβdef
  have hβp : β ^ p = 1 := by rw [hβdef, ← map_pow, hαp, map_one]
  have hβout : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (StatedProj (StatedSp 2 F)) :=
    fun hin => hαin ((CFSG.HardMathSupport.Lang.Coordinator.congr_mem_inner_iff e α).mp hin)
  have hβ1 : β ≠ 1 := fun h1 =>
    hβout (h1 ▸ (CFSG.ComponentClassification.OuterAutomorphisms.inner _).one_mem)
  have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
  have hβE : β ∈ CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spSemilinearAutGroup 2 F :=
    CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.mem_of_pow_eq_one_of_index_dvd_two
      hidx hp hp2 hβp
  by_cases hD : β ∈ CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spLinearAutGroup 2 F
  · exfalso
    haveI := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal
      (StatedProj (StatedSp 2 F))
    exact hβout
      (CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.mem_of_pow_eq_one_of_relIndex_dvd_two
        (H := CFSG.ComponentClassification.OuterAutomorphisms.inner (StatedProj (StatedSp 2 F)))
        (D := CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spLinearAutGroup 2 F)
        (hDH.trans (Nat.gcd_dvd_left 2 _)) hp hp2 hD hβp)
  obtain ⟨-, σ, hσord, hcardk, h, -, hβh⟩ := hdesc p hp β hβE hD hβord
  set k := CFSG.ComponentClassification.UnbalancedCatalog.descentField σ
  have hk : Nat.card k = 2 ^ (f / p) := hcardk
  have hint : ∀ x : StatedProj (StatedSp 2 F),
      β (h x) = h (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldAut 2 F σ x) := by
    intro x
    rw [hβh]
    simp [MulAut.mul_apply]
  have eβ : fixedSubgroup β ≃*
      fixedSubgroup (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldAut 2 F σ) :=
    (fixedSubgroupEquivOfIntertwine h
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldAut 2 F σ) β hint).symm
  have hfix : fixedSubgroup (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldAut 2 F σ) =
      (CFSG.RankThree.CASymplecticSubfield.subfieldSpProj 2 k).range :=
    Subgroup.ext fun x => CFSG.RankThree.CASymplecticSubfield.fieldAut_apply_eq_self_iff
      (by norm_num) (by rw [hσord]; exact hp.odd_of_ne_two hp2) x
  have hinj := CFSG.RankThree.CASymplecticSubfield.subfieldSpProj_injective (K := F) (r := 2)
    (by norm_num) k
  have eσ : fixedSubgroup (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldAut 2 F σ) ≃*
      StatedProj (StatedSp 2 ↥k) :=
    (MulEquiv.subgroupCongr hfix).trans (MonoidHom.ofInjective hinj).symm
  have e1 : ↥(fixedSubgroup α) ≃* StatedProj (StatedSp 2 ↥k) :=
    ((CFSG.Sporadic.HeldB.fixedSubgroupCongr e α).trans eβ).trans eσ
  have hS : p ∣ Nat.card (StatedProj (StatedSp 2 ↥k)) →
      ¬ CFSG.HallHigman.IsPSolvable p (StatedProj (StatedSp 2 ↥k)) := by
    by_cases hk2 : Nat.card ↥k = 2
    · exact not_pSolvable_statedProj_sp_two_two hk2 hp hp5
    · have hk4 : 4 ≤ Nat.card ↥k := by
        have h1 : 1 < Nat.card ↥k := Finite.one_lt_card
        rw [hk] at h1 hk2 ⊢
        generalize f / p = m at h1 hk2 ⊢
        rcases Nat.lt_or_ge m 2 with h2 | h2
        · interval_cases m
          · norm_num at h1
          · norm_num at hk2
        · exact (by norm_num : (4 : ℕ) = 2 ^ 2).trans_le (Nat.pow_le_pow_right (by norm_num) h2)
      haveI : Fintype ↥k := Fintype.ofFinite _
      have hsub : ∃ t : Finset ↥k, t.card = 4 := by
        obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq
          (show 4 ≤ (Finset.univ : Finset ↥k).card by
            rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hk4)
        exact ⟨t, ht⟩
      have hsimple := CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp
        ↥k 2 (by norm_num) (Or.inl (Or.inr hk4))
      have hperf := CFSG.ClassicalGroups.Symplectic.symplectic_projective_perfect 2 ↥k
        (Or.inl hsub)
      have hnc : ¬ ∀ a b : StatedProj (StatedSp 2 ↥k), a * b = b * a :=
        fun hcomm => Group.IsPerfect.not_isSolvable _ (Group.isSolvable_of_comm hcomm)
      haveI : Finite (StatedProj (StatedSp 2 ↥k)) := inferInstance
      exact not_pSolvable_of_simple_nonabelian hsimple hnc hp
  exact not_pSolvable_fixed_of_equiv hp hpK α hαp e1 hS

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.Coordinator in
theorem psu_four_fixed_equiv_simple {K : Type} [Group K] [Finite K] {ℓ f : ℕ}
    (hcl : StatedClassicalModel K .PSU 4 ℓ f) (hℓ2 : ℓ = 2) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpK : p ∣ Nat.card K) (α : MulAut K) (hαp : α ^ p = 1) (hαin : α ∉ inner K) :
    ∃ (S : Type) (_ : Group S) (_ : Finite S), IsSimpleGroup S ∧ (¬ ∀ a b : S, a * b = b * a) ∧
      Nonempty (↥(fixedSubgroup α) ≃* S) := by
  subst hℓ2
  obtain ⟨⟨hℓ, hf, hn, -⟩, F, hF, hFin, hFcard, ⟨e⟩⟩ := hcl
  have hne' : ¬(4 = 3 ∧ 2 ^ f = 2) := fun h1 => absurd h1.1 (by norm_num)
  have h : UnitaryFieldData 2 f F := ⟨hℓ, hf, by rw [hFcard, ← pow_mul, mul_comm]⟩
  have : Fact p.Prime := ⟨hp⟩
  have hC1 : IsPrimeFormGram (1 : GL (Fin 4) F) := isPrimeFormGram_one
  have hdiv' : ¬ p ∣ Nat.gcd 4 (2 ^ f + 1) := fun hd => by
    have h4 : p ∣ 4 := dvd_trans hd (Nat.gcd_dvd_left 4 _)
    have := Nat.le_of_dvd (by norm_num) h4
    omega
  have hp2 : p ≠ 2 := by omega
  obtain ⟨θ⟩ : Nonempty (K ≃* primeFormP h ((1 : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) :=
    ⟨(e.trans (unitaryPSUEquiv (n := 4) h (by norm_num)).symm).trans
      (Classical.choice (unitary_prime_form_full_semilinear_realization h hC1 hn hne').1).symm⟩
  set β := MulAut.congr θ α with hβdef
  have hβp : β ^ p = 1 := by rw [hβdef, ← map_pow, hαp, map_one]
  have hβout : β ∉ inner (primeFormP h ((1 : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) :=
    fun hin => hαin ((congr_mem_inner_iff θ α).mp hin)
  have hβ1 : β ≠ 1 := fun h1 =>
    hβout (h1 ▸ (CFSG.ComponentClassification.OuterAutomorphisms.inner _).one_mem)
  have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
  set σ := primeFormFieldFactor h hC1 hn hne' β with hσdef
  have hσp : σ ^ p = 1 := by rw [hσdef, ← map_pow, hβp, map_one]
  have hσ1 : σ ≠ 1 := by
    intro hσ1
    have hD : β ∈ primeFormD h ((1 : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
      rw [← ker_primeFormFieldFactor h hC1 hn hne']
      exact hσ1
    exact hβout (mem_inner_of_mem_primeFormD h hn hne' hp hdiv' hD hβp)
  have hσord : orderOf σ = p := orderOf_eq_prime hσp hσ1
  obtain ⟨-, -, -, -, -, M, hM⟩ :=
    unitary_prime_semilinear_field_descent' h hn hne' hp hp2 β hβord σ hσdef.symm hσord
  set u := primeFormConjHom h ((1 : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) M
  set fσ := primeFormFieldHom h (isPrimeFormGram_one (n := 4)) σ
  have hβu : β * u = u * fσ := by
    rw [← hM]
    group
  have hint : ∀ x, β (u x) = u (fσ x) := fun x => congrArg (fun g : MulAut _ => g x) hβu
  have hZ' : ¬ p ∣ Nat.card (normOneScalars h
      (gramSU h ((1 : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) 4) := by
    rw [card_normOneScalars_one (n := 4) h (by norm_num)]
    exact hdiv'
  obtain ⟨-, -, -, -, -, -, -, -, -, hsimpC, -⟩ :=
    prime_subfield_fixed_group_package h hp hp2 hσord 4 hn hne' hZ'
  obtain ⟨hS, hnc, -⟩ := hsimpC (fun h1 => absurd h1.1 (by norm_num))
  have e1 : ↥(fixedSubgroup α) ≃* ↥(fieldFixedPSU h 4 σ) :=
    (CFSG.Sporadic.HeldB.fixedSubgroupCongr θ α).trans
      (fixedSubgroupEquivOfIntertwine (u : _ ≃* _) fσ β hint).symm
  have hfin : Finite ↥(fieldFixedPSU h 4 σ) := Finite.of_equiv ↥(fixedSubgroup α) e1.toEquiv
  exact ⟨↥(fieldFixedPSU h 4 σ), inferInstance, hfin, hS, hnc, ⟨e1⟩⟩

theorem fixed_not_pSolvable_PSU_four {K : Type} [Group K] [Finite K] {ℓ f : ℕ}
    (hcl : StatedClassicalModel K .PSU 4 ℓ f) (hℓ2 : ℓ = 2) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpK : p ∣ Nat.card K) (α : MulAut K) (hαp : α ^ p = 1) (hαin : α ∉ inner K) :
    ¬ CFSG.HallHigman.IsPSolvable p ↥(fixedSubgroup α) := by
  obtain ⟨S, instS, instF, hS, hnc, ⟨e⟩⟩ :=
    psu_four_fixed_equiv_simple hcl hℓ2 hp hp5 hpK α hαp hαin
  exact not_pSolvable_fixed_of_simple hp hpK α hαp hS hnc e

theorem _root_.CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.kFactFieldAutLieE3_holds :
    CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.KFactFieldAutLieE3 := by
  intro J _ _ d p hc hs hE ⟨e⟩ hp hp5 hrk hpJ α hαp hαin
  obtain ⟨d', hv⟩ := d
  cases d' with
  | A r q =>
    have hq2 : q.p = 2 := by simpa [TauCeti.LieTypeIndex.characteristic_A] using hc
    have hcl := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
    rcases r with _ | _ | _ | r
    · exact absurd hE (by simp [CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.IsE3LeviIndex])
    · exact fixed_not_pSolvable_PSL_two hcl hq2 hp hp5 hpJ α hαp hαin
    · exact fixed_not_pSolvable_PSL_three hcl hq2 hp hp5 hpJ α hαp hαin
    · exact absurd hE (by simp [CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.IsE3LeviIndex])
  | B r q =>
    have hq2 : q.p = 2 := by simpa [TauCeti.LieTypeIndex.characteristic_B] using hc
    rcases r with _ | _ | _ | r
    · exact absurd hE (by simp [CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.IsE3LeviIndex])
    · exact absurd hE (by simp [CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.IsE3LeviIndex])
    · have hcl := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
      exact fixed_not_pSolvable_PSp_two hcl hq2 hp hp5 hpJ α hαp hαin
    · exact absurd hE (by simp [CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.IsE3LeviIndex])
  | C r q =>
    have hq2 : q.p = 2 := by simpa [TauCeti.LieTypeIndex.characteristic_C] using hc
    have hr : 3 ≤ r :=
      ((TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).1
    rcases r with _ | _ | _ | r
    · exact absurd hE (by simp [CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.IsE3LeviIndex])
    · exact absurd hE (by simp [CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.IsE3LeviIndex])
    · exact absurd hr (by decide)
    · exact absurd hE (by simp [CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.IsE3LeviIndex])
  | twistedA r q =>
    have hq2 : q.p = 2 := by simpa [TauCeti.LieTypeIndex.characteristic_twistedA] using hc
    rcases r with _ | _ | _ | _ | r
    · exact absurd hE (by simp [CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.IsE3LeviIndex])
    · exact absurd hE (by simp [CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.IsE3LeviIndex])
    · exact absurd hE (by simp [CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.IsE3LeviIndex])
    · have hcl := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv e
      exact fixed_not_pSolvable_PSU_four hcl hq2 hp hp5 hpJ α hαp hαin
    · exact absurd hE (by simp [CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.IsE3LeviIndex])
  | _ => exact absurd hE (by simp [CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.IsE3LeviIndex])

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongFieldAut
