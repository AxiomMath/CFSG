module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FourteenThirteenSylow
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.A11TwoSetPerm
import CFSG.HardMathSupport.RichardWeiss.Coordinator.AltNormalizerSq.PerfectCyclic

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private noncomputable def rhoOf {K M : Subgroup G}
    (e : threeStar K ≃* alternatingGroup (Fin 11)) :
    ↥(K ⊓ M) →* alternatingGroup (Fin 11) :=
  e.toMonoidHom.comp ((QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)).comp
    (Subgroup.inclusion (inf_le_left : K ⊓ M ≤ K)))

private lemma rhoOf_range {K M : Subgroup G}
    (e : threeStar K ≃* alternatingGroup (Fin 11)) {i j : Fin 11}
    (hI : ((((K ⊓ M).subgroupOf K).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K))).map e.toMonoidHom) =
      a11TwoSetStab i j) :
    (rhoOf (M := M) e).range = a11TwoSetStab i j := by
  rw [rhoOf, MonoidHom.range_comp, MonoidHom.range_comp, Subgroup.inclusion_range]
  exact hI

private noncomputable def thetaOf {K M : Subgroup G}
    (e : threeStar K ≃* alternatingGroup (Fin 11)) {i j : Fin 11} (hij : i ≠ j)
    (hI : ((((K ⊓ M).subgroupOf K).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K))).map e.toMonoidHom) =
      a11TwoSetStab i j) :
    ↥(K ⊓ M) →* Equiv.Perm (Fin 9) :=
  (nonempty_a11TwoSetStab_mulEquiv hij).some.toMonoidHom.comp
    ((rhoOf (M := M) e).codRestrict (a11TwoSetStab i j)
      (fun x => (rhoOf_range e hI) ▸ MonoidHom.mem_range.mpr ⟨x, rfl⟩))

private lemma thetaOf_surjective {K M : Subgroup G}
    (e : threeStar K ≃* alternatingGroup (Fin 11)) {i j : Fin 11} (hij : i ≠ j)
    (hI : ((((K ⊓ M).subgroupOf K).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K))).map e.toMonoidHom) =
      a11TwoSetStab i j) :
    Function.Surjective (thetaOf (M := M) e hij hI) := by
  have hρS : Function.Surjective ((rhoOf (M := M) e).codRestrict (a11TwoSetStab i j)
      (fun x => (rhoOf_range e hI) ▸ MonoidHom.mem_range.mpr ⟨x, rfl⟩)) := by
    intro y
    have hy : (y : alternatingGroup (Fin 11)) ∈ (rhoOf (M := M) e).range := by
      rw [rhoOf_range e hI]
      exact y.2
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hy
    exact ⟨x, Subtype.ext hx⟩
  have h := (nonempty_a11TwoSetStab_mulEquiv hij).some.surjective.comp hρS
  simpa [thetaOf] using h

private lemma thetaOf_ker_eq {K M : Subgroup G}
    (e : threeStar K ≃* alternatingGroup (Fin 11)) {i j : Fin 11} (hij : i ≠ j)
    (hI : ((((K ⊓ M).subgroupOf K).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K))).map e.toMonoidHom) =
      a11TwoSetStab i j) :
    (thetaOf (M := M) e hij hI).ker = (rhoOf (M := M) e).ker := by
  ext x
  simp [thetaOf, MonoidHom.codRestrict_apply, MulEquiv.map_eq_one_iff]

private lemma rhoOf_ker_eq {K M : Subgroup G}
    (e : threeStar K ≃* alternatingGroup (Fin 11)) :
    (rhoOf (M := M) e).ker =
      Subgroup.comap (Subgroup.inclusion (inf_le_left : K ⊓ M ≤ K))
        (CFSG.pPrimeCore 3 ↥K) := by
  ext x
  simp [rhoOf, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]

private lemma isPGroup_pPrimeCore_three_kSub {M H E Q : Subgroup G}
    (h : S14Choice G M H E Q (kSub 3 M H)) (h2 : CaseTwo M H) :
    IsPGroup 2 (CFSG.pPrimeCore 3 ↥(kSub 3 M H)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEq : CFSG.pCore 2 ↥(kSub 3 M H) = CFSG.pPrimeCore 3 ↥(kSub 3 M H) := by
    apply Subgroup.map_injective (kSub 3 M H).subtype_injective
    simpa [pCoreOf] using h.pCoreOf_two_kSub_eq_caseTwo h2
  rw [← hEq]
  exact CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥(kSub 3 M H)) 2

private lemma thetaOf_ker_isPGroup {M H E Q : Subgroup G}
    (h : S14Choice G M H E Q (kSub 3 M H)) (h2 : CaseTwo M H)
    (e : threeStar (kSub 3 M H) ≃* alternatingGroup (Fin 11)) {i j : Fin 11} (hij : i ≠ j)
    (hI : ((((kSub 3 M H ⊓ M).subgroupOf (kSub 3 M H)).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(kSub 3 M H)))).map e.toMonoidHom) =
      a11TwoSetStab i j) :
    IsPGroup 2 (thetaOf (M := M) e hij hI).ker := by
  rw [thetaOf_ker_eq, rhoOf_ker_eq]
  exact IsPGroup.comap_of_injective (isPGroup_pPrimeCore_three_kSub h h2)
    (Subgroup.inclusion (inf_le_left : kSub 3 M H ⊓ M ≤ kSub 3 M H))
    (Subgroup.inclusion_injective _)

private lemma ker_piJ_le_thetaOf_ker {M H E Q : Subgroup G}
    (h : S14Choice G M H E Q (kSub 3 M H)) (h2 : CaseTwo M H) (hK : KNormalAt M)
    (hU : NineNineOneAt M) (hL : PLayerNotLeAt M) (hKF : KFactA11GammaTwoSet)
    (e : threeStar (kSub 3 M H) ≃* alternatingGroup (Fin 11)) {i j : Fin 11} (hij : i ≠ j)
    (hI : ((((kSub 3 M H ⊓ M).subgroupOf (kSub 3 M H)).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(kSub 3 M H)))).map e.toMonoidHom) =
      a11TwoSetStab i j) :
    ((QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M)).comp
      (Subgroup.inclusion (inf_le_right : kSub 3 M H ⊓ M ≤ M))).ker ≤
      (thetaOf (M := M) e hij hI).ker := by
  rw [thetaOf_ker_eq, rhoOf_ker_eq]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  rw [Subgroup.mem_comap]
  have hxM : (Subgroup.inclusion (inf_le_right : kSub 3 M H ⊓ M ≤ M)) x ∈
      CFSG.pPrimeCore 3 ↥M :=
    (QuotientGroup.eq_one_iff (N := CFSG.pPrimeCore 3 ↥M) _).mp hx
  have hxD : (x : G) ∈ (CFSG.pPrimeCore 3 ↥M).map M.subtype :=
    Subgroup.mem_map_of_mem M.subtype hxM
  have hxP : (x : G) ∈
      (CFSG.pPrimeCore 3 ↥(kSub 3 M H)).map (kSub 3 M H).subtype :=
    h.pPrimeCore_inf_kSub_le h2 hK hU hL hKF ⟨hxD, x.2.1⟩
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxP
  have hν : (Subgroup.inclusion (inf_le_left : kSub 3 M H ⊓ M ≤ kSub 3 M H)) x = y := by
    apply Subtype.ext
    exact hyx.symm
  rwa [hν]

theorem perfectResidual_map_eq_alternatingGroup {X : Type*} [Group X] [Finite X]
    {α : Type*} [Fintype α] [DecidableEq α] (h5 : 5 ≤ Fintype.card α)
    (θ : X →* Equiv.Perm α) (hθ : Function.Surjective θ) :
    (CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual X).map θ = alternatingGroup α := by
  obtain ⟨n, hn⟩ :=
    CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_eq_derivedSeries (G := X)
  let N : ℕ := max n 1
  have hN : 1 ≤ N := le_max_right n 1
  have hX : CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual X = derivedSeries X N := by
    refine le_antisymm (iInf_le _ N) ?_
    rw [hn]
    exact derivedSeries_antitone X (le_max_left n 1)
  rw [hX, map_derivedSeries_eq hθ N]
  exact CFSG.HardMathSupport.RichardWeiss.Coordinator.derivedSeries_perm_eq_alternatingGroup
    (α := α) h5 hN

private lemma exists_factor_of_ker_le {A B C : Type*} [Group A] [Group B] [Group C]
    (φ : A →* B) (hφ : Function.Surjective φ) (g : A →* C)
    (hg : Function.Surjective g) (h : φ.ker ≤ g.ker) :
    ∃ f : B →* C, Function.Surjective f ∧ f.ker = g.ker.map φ := by
  let f : B →* C := MonoidHom.liftOfSurjective φ hφ ⟨g, h⟩
  have hfφ : ∀ a, f (φ a) = g a := fun a =>
    MonoidHom.liftOfRightInverse_comp_apply φ (Function.surjInv hφ)
      (Function.rightInverse_surjInv hφ) ⟨g, h⟩ a
  have hcomp : f.comp φ = g := MonoidHom.ext hfφ
  refine ⟨f, ?_, ?_⟩
  · have hg' : Function.Surjective (f.comp φ) := by rwa [hcomp]
    exact Function.Surjective.of_comp hg'
  · rw [← hcomp, ← MonoidHom.comap_ker f φ,
      Subgroup.map_comap_eq_self_of_surjective hφ]

theorem S14Choice.exists_perfect_map_onto_a9 {M H E Q : Subgroup G}
    (h : S14Choice G M H E Q (kSub 3 M H)) (h2 : CaseTwo M H) (hK : KNormalAt M)
    (hU : NineNineOneAt M) (hL : PLayerNotLeAt M) (hKF : KFactA11GammaTwoSet) :
    ∃ I : Subgroup (↥M ⧸ CFSG.pPrimeCore 3 ↥M), ⁅I, I⁆ = I ∧
      ∃ f : ↥I →* alternatingGroup (Fin 9), Function.Surjective f ∧ IsPGroup 2 f.ker := by
  classical
  obtain ⟨e, i, j, hij, hI⟩ := h.exists_twoSet h2 hK hU hL hKF
  let K : Subgroup G := kSub 3 M H
  let J : Subgroup G := K ⊓ M
  let πM : ↥M →* (↥M ⧸ CFSG.pPrimeCore 3 ↥M) := QuotientGroup.mk' _
  let πJ : ↥J →* (↥M ⧸ CFSG.pPrimeCore 3 ↥M) :=
    πM.comp (Subgroup.inclusion (inf_le_right : J ≤ M))
  let θ : ↥J →* Equiv.Perm (Fin 9) := thetaOf (K := K) (M := M) e hij hI
  have hθsurj : Function.Surjective θ := thetaOf_surjective e hij hI
  have hθker : IsPGroup 2 θ.ker := thetaOf_ker_isPGroup h h2 e hij hI
  have hπJker : πJ.ker ≤ θ.ker := ker_piJ_le_thetaOf_ker h h2 hK hU hL hKF e hij hI
  let I₀ : Subgroup ↥J := CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual ↥J
  have hI0map : I₀.map θ = alternatingGroup (Fin 9) :=
    perfectResidual_map_eq_alternatingGroup (by norm_num) θ hθsurj
  let Ibar : Subgroup (↥M ⧸ CFSG.pPrimeCore 3 ↥M) := I₀.map πJ
  have hIbarperf : ⁅Ibar, Ibar⁆ = Ibar := by
    change ⁅I₀.map πJ, I₀.map πJ⁆ = I₀.map πJ
    rw [← Subgroup.map_commutator]
    exact congrArg (Subgroup.map πJ) (Subgroup.isPerfect_iff.mp
      (CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_isPerfect (G := ↥J)))
  let φ : ↥I₀ →* ↥Ibar :=
    (πJ.comp I₀.subtype).codRestrict Ibar (fun x =>
      Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩)
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
    refine ⟨⟨x, hx⟩, ?_⟩
    exact Subtype.ext hxy
  let g : ↥I₀ →* alternatingGroup (Fin 9) :=
    (θ.comp I₀.subtype).codRestrict _ (fun x => by
      have hx : θ (x : ↥J) ∈ I₀.map θ := Subgroup.mem_map_of_mem θ x.2
      rwa [hI0map] at hx)
  have hgsurj : Function.Surjective g := by
    intro y
    have hy : (y : Equiv.Perm (Fin 9)) ∈ I₀.map θ := by
      rw [hI0map]
      exact y.2
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hgker : g.ker = θ.ker.comap I₀.subtype := by
    ext x
    rw [Subgroup.mem_comap, MonoidHom.mem_ker]
    change ((θ.comp I₀.subtype).codRestrict (alternatingGroup (Fin 9)) _) x = 1 ↔
      θ (x : ↥J) = 1
    rw [Subtype.ext_iff]
    rfl
  have hgkerP : IsPGroup 2 g.ker := by
    rw [hgker]
    exact IsPGroup.comap_subtype hθker
  have hker : φ.ker ≤ g.ker := by
    intro x hx
    have hxπ : (x : ↥J) ∈ πJ.ker := by
      refine MonoidHom.mem_ker.mpr ?_
      have hval := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      simpa [φ] using hval
    have hxθ : θ (x : ↥J) = 1 := MonoidHom.mem_ker.mp (hπJker hxπ)
    exact MonoidHom.mem_ker.mpr (Subtype.ext hxθ)
  obtain ⟨f, hfsurj, hfker⟩ := exists_factor_of_ker_le φ hφsurj g hgsurj hker
  refine ⟨Ibar, hIbarperf, f, hfsurj, ?_⟩
  rw [hfker]
  exact IsPGroup.map hgkerP φ

theorem S14Choice.exists_surjection_perm_nine {M H E Q : Subgroup G}
    (h : S14Choice G M H E Q (kSub 3 M H)) (h2 : CaseTwo M H) (hK : KNormalAt M)
    (hU : NineNineOneAt M) (hL : PLayerNotLeAt M) (hKF : KFactA11GammaTwoSet) :
    ∃ θ : ↥(kSub 3 M H ⊓ M) →* Equiv.Perm (Fin 9),
      Function.Surjective θ ∧
        ((QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M)).comp
          (Subgroup.inclusion (inf_le_right : kSub 3 M H ⊓ M ≤ M))).ker ≤ θ.ker := by
  obtain ⟨e, i, j, hij, hI⟩ := h.exists_twoSet h2 hK hU hL hKF
  exact ⟨thetaOf (K := kSub 3 M H) (M := M) e hij hI,
    thetaOf_surjective (K := kSub 3 M H) (M := M) e hij hI,
    ker_piJ_le_thetaOf_ker h h2 hK hU hL hKF e hij hI⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
