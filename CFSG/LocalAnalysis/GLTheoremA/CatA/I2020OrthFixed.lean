module

public import CFSG.LinearAlgebra.MovedSpanFixSub
public import CFSG.LinearAlgebra.QuadraticDoubleSign
public import CFSG.LinearAlgebra.QuadraticOrthogonalBasisNorms
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquareSignChange
public import CFSG.RankThree.PartOne.KC.OrthogonalRegularQuasisimple
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.OrtHFixed
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupOddOrthogonal

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2020

open Polynomial Module QuadraticMap CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.LinearAlgebra
open CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
open CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquare
open CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks
open scoped commutatorElement

variable {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

private theorem three_le_finrank_fixedSpace (hx : OddOrderIsometry Q p x)
    (hQ : (polarBilin Q).Nondegenerate) {F : Subgroup (V ≃ₗ[K] V)}
    (hFq : CFSG.IsQuasisimple ↥F) (hFle : F ≤ supportedFixedDerived Q x) :
    3 ≤ Module.finrank K ↥(fixedSpace x) := by
  classical
  by_contra h3
  have h2 : Module.finrank K ↥(fixedSpace x) ≤ 2 := by omega
  have hcommΩ : ∀ g h : ↥(fixedSpace x) ≃ₗ[K] ↥(fixedSpace x),
      g ∈ orthDerived (Q.comp (fixedSpace x).subtype) →
      h ∈ orthDerived (Q.comp (fixedSpace x).subtype) → g * h = h * g :=
    fun _ _ hg hh =>
      CFSG.HardMathSupport.Dickson.Sec6.I1431.t6orth_commute_orthDerived_of_finrank_le_two
        hx.polarBilin_fixed_nondegenerate h2 hg hh
  have hFcomm' : ∀ f ∈ F, ∀ f' ∈ F, f * f' = f' * f := by
    intro f hf f' hf'
    have hbf : f ∈ supportedBlock Q x (X - 1) := supportedFixedDerived_le_supportedBlock (hFle hf)
    have hbf' : f' ∈ supportedBlock Q x (X - 1) :=
      supportedFixedDerived_le_supportedBlock (hFle hf')
    have ha : restrictFixed Q x ⟨f, hbf⟩ ∈ orthDerived (Q.comp (fixedSpace x).subtype) :=
      (mem_supportedFixedDerived.mp (hFle hf)).2
    have hb : restrictFixed Q x ⟨f', hbf'⟩ ∈ orthDerived (Q.comp (fixedSpace x).subtype) :=
      (mem_supportedFixedDerived.mp (hFle hf')).2
    have hcomm := hcommΩ _ _ ha hb
    have h1 : restrictFixed Q x ⟨f * f', mul_mem hbf hbf'⟩ =
        restrictFixed Q x ⟨f, hbf⟩ * restrictFixed Q x ⟨f', hbf'⟩ :=
      map_mul (restrictFixed Q x) ⟨f, hbf⟩ ⟨f', hbf'⟩
    have h2' : restrictFixed Q x ⟨f' * f, mul_mem hbf' hbf⟩ =
        restrictFixed Q x ⟨f', hbf'⟩ * restrictFixed Q x ⟨f, hbf⟩ :=
      map_mul (restrictFixed Q x) ⟨f', hbf'⟩ ⟨f, hbf⟩
    have heq : (⟨f * f', mul_mem hbf hbf'⟩ : ↥(supportedBlock Q x (X - 1))) =
        ⟨f' * f, mul_mem hbf' hbf⟩ :=
      restrictFixed_injective hx (by rw [h1, h2', hcomm])
    exact congrArg Subtype.val heq
  have hFcomm : ∀ a b : ↥F, a * b = b * a := fun a b =>
    Subtype.ext (hFcomm' a.1 a.2 b.1 b.2)
  haveI : Group.IsPerfect ↥F := hFq.1
  haveI : IsMulCommutative ↥F := IsMulCommutative.of_comm hFcomm
  haveI : Subsingleton ↥F := inferInstance
  obtain ⟨a, b, hab⟩ := hFq.2.2
  exact hab (Subsingleton.elim _ _)

private theorem eq_supportedFixedDerived_of_quasisimple_normal (hx : OddOrderIsometry Q p x)
    (hQ : (polarBilin Q).Nondegenerate) (hdim0 : Module.finrank K ↥(fixedSpace x) ≠ 4)
    {F : Subgroup (V ≃ₗ[K] V)} (hFq : CFSG.IsQuasisimple ↥F)
    (hFle : F ≤ supportedFixedDerived Q x)
    (hFn : (F.subgroupOf (supportedFixedDerived Q x)).Normal) :
    F = supportedFixedDerived Q x := by
  classical
  have h3 : 3 ≤ Module.finrank K ↥(fixedSpace x) := three_le_finrank_fixedSpace hx hQ hFq hFle
  set Ω := supportedFixedDerived Q x with hΩdef
  have hqs : CFSG.IsQuasisimple ↥Ω := by
    by_cases hSE : SmallFixedException (Q.comp (fixedSpace x).subtype)
    · exfalso
      have hsol : Group.IsSolvable
          ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)) :=
        isSolvable_orthogonalGroup_of_smallFixedException
          _ hx.polarBilin_fixed_nondegenerate h3 hSE
      have hFB : Ω ≤ supportedBlock Q x (X - 1) := supportedFixedDerived_le_supportedBlock
      let ψ : ↥F →* (↥(fixedSpace x) ≃ₗ[K] ↥(fixedSpace x)) :=
        (restrictFixed Q x).comp (Subgroup.inclusion (hFle.trans hFB))
      let φ : ↥F →* ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)) :=
        ψ.codRestrict _ fun f => restrictFixed_mem_orthogonalGroup (Q := Q) (x := x) _
      have hinj : Function.Injective φ := by
        intro a b hab
        have h1 : restrictFixed Q x (Subgroup.inclusion (hFle.trans hFB) a) =
            restrictFixed Q x (Subgroup.inclusion (hFle.trans hFB) b) := congrArg Subtype.val hab
        exact Subtype.ext (congrArg (fun z : ↥(supportedBlock Q x (X - 1)) => (z : V ≃ₗ[K] V))
          (restrictFixed_injective hx h1))
      haveI : Group.IsSolvable
          ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)) := hsol
      have hFsol : Group.IsSolvable ↥F := Group.isSolvable_of_isSolvable_injective hinj
      haveI : Group.IsPerfect ↥F := hFq.1
      haveI : Nontrivial ↥F := by
        rcases hFq with ⟨-, -, a, b, hab⟩
        by_contra hnt
        haveI : Subsingleton ↥F := not_nontrivial_iff_subsingleton.mp hnt
        haveI : Subsingleton (↥F ⧸ Subgroup.center ↥F) := inferInstance
        exact hab (Subsingleton.elim _ _)
      exact Group.IsPerfect.not_isSolvable ↥F hFsol
    · have hns : ¬ (Module.finrank K ↥(fixedSpace x) = 4 ∧
          ∃ S : Submodule K ↥(fixedSpace x), Module.finrank K S = 2 ∧
            ∀ y ∈ S, (Q.comp (fixedSpace x).subtype) y = 0) := by
        rintro ⟨h4, -⟩
        exact hdim0 h4
      have hqsb : CFSG.IsQuasisimple
          ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype))) :=
        orthogonal_regular_space_derived_quasisimple (Q.comp (fixedSpace x).subtype)
          hx.polarBilin_fixed_nondegenerate h3 hSE hns
      have hmap : (commutator
            ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype))).map
          (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)).subtype =
          orthDerived (Q.comp (fixedSpace x).subtype) :=
        Subgroup.map_subtype_commutator _
      have hqsb' : CFSG.IsQuasisimple
          ↥((commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
            (Q.comp (fixedSpace x).subtype))).map
            (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)).subtype) :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv
          (Subgroup.equivMapOfInjective _ _ Subtype.coe_injective) hqsb
      have hqsb'' : CFSG.IsQuasisimple ↥(orthDerived (Q.comp (fixedSpace x).subtype)) :=
        hmap ▸ hqsb'
      exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (supportedFixedDerivedEquiv hx).symm hqsb''
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hqs hFn with htop | hcenter
  · exact le_antisymm hFle (Subgroup.subgroupOf_eq_top.mp htop)
  · exfalso
    have hFcomm' : ∀ f ∈ F, ∀ f' ∈ F, f * f' = f' * f := by
      intro f hf f' hf'
      have h1 : (⟨f, hFle hf⟩ : ↥Ω) ∈ Subgroup.center ↥Ω :=
        hcenter (Subgroup.mem_subgroupOf.mpr hf)
      have h2 : (⟨f', hFle hf'⟩ : ↥Ω) ∈ Subgroup.center ↥Ω :=
        hcenter (Subgroup.mem_subgroupOf.mpr hf')
      have h3 : (⟨f, hFle hf⟩ : ↥Ω) * ⟨f', hFle hf'⟩ = ⟨f', hFle hf'⟩ * ⟨f, hFle hf⟩ :=
        (Subgroup.mem_center_iff.mp h1 _).symm
      exact congrArg Subtype.val h3
    have hFcomm : ∀ a b : ↥F, a * b = b * a := fun a b =>
      Subtype.ext (hFcomm' a.1 a.2 b.1 b.2)
    haveI : Group.IsPerfect ↥F := hFq.1
    haveI : IsMulCommutative ↥F := IsMulCommutative.of_comm hFcomm
    haveI : Subsingleton ↥F := inferInstance
    obtain ⟨a, b, hab⟩ := hFq.2.2
    exact hab (Subsingleton.elim _ _)

theorem commute_of_fixedFactor (hx : OddOrderIsometry Q p x)
    (hK : Odd (Nat.card K)) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim0 : Module.finrank K ↥(fixedSpace x) ≠ 4)
    {F : Subgroup (V ≃ₗ[K] V)} (hFq : CFSG.IsQuasisimple ↥F) (hFle : F ≤ supportedFixedDerived Q x)
    (hFn : (F.subgroupOf (supportedFixedDerived Q x)).Normal)
    {T : Subgroup (V ≃ₗ[K] V)} (hT : T ≤ F) (hT2 : IsPGroup 2 T)
    (hTodd : ¬ 2 ∣ (T.subgroupOf F).index)
    {S : Subgroup (V ≃ₗ[K] V)} (hST : ∀ s ∈ S, ∀ t ∈ T, s * t = t * s) :
    ∀ g ∈ ⁅S, Subgroup.zpowers x⁆, ∀ f ∈ F, g * f = f * g := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun g : V ≃ₗ[K] V => (g : V → V)) fun a b h => LinearEquiv.ext (congrFun h)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK' : Fintype.card K % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.odd_iff.mp hK
  have h2 : (2 : K) ≠ 0 := CFSG.RankThree.Classical.two_ne_zero_of_card_odd hK'
  have hW₀nd := hx.polarBilin_fixed_nondegenerate
  have h3 : 3 ≤ Module.finrank K ↥(fixedSpace x) := three_le_finrank_fixedSpace hx hQ hFq hFle
  have hFeq : F = supportedFixedDerived Q x :=
    eq_supportedFixedDerived_of_quasisimple_normal hx hQ hdim0 hFq hFle hFn
  obtain ⟨b, hborth, hbpair⟩ :=
    exists_orthogonal_basis_quad_eq_repeated hK (d := Module.finrank K ↥(fixedSpace x)) rfl h3
      hdim0 (Q.comp (fixedSpace x).subtype) hW₀nd
  choose j hj t ht hval using hbpair
  have hbne : ∀ i, (Q.comp (fixedSpace x).subtype) (b i) ≠ 0 := by
    intro i hi
    have horth : LinearMap.BilinForm.iIsOrtho
        (polarBilin (Q.comp (fixedSpace x).subtype)) b := fun k l hkl => hborth k l hkl
    have h := LinearMap.BilinForm.iIsOrtho.not_isOrtho_basis_self_of_nondegenerate
      horth hW₀nd i
    rw [polarBilin_apply_apply, polar_self, hi, smul_zero] at h
    exact h rfl
  have hsign : ∀ i, ∃ g ∈ orthDerived (Q.comp (fixedSpace x).subtype),
      g (b i) = -b i ∧ g (b (j i)) = -b (j i) ∧
        ∀ y, polar (Q.comp (fixedSpace x).subtype) (b i) y = 0 →
          polar (Q.comp (fixedSpace x).subtype) (b (j i)) y = 0 → g y = y := by
    intro i
    exact exists_mem_orthDerived_double_sign_of_sq_mul (Q := Q.comp (fixedSpace x).subtype) h2
      rfl rfl (hbne i) (ht i) (hval i) (hborth i (j i) (hj i).symm)
  choose g hgmem hgi hgj hgfix using hsign
  have hgD : ∀ i, g i ∈ signChangeSubgroup b := by
    intro i
    refine ⟨{i, j i}, ?_⟩
    refine b.ext' fun k => ?_
    rw [CFSG.LocalAnalysis.ComponentInitial.OddOrthogonal.signEquiv_apply_basis]
    by_cases hk : k = i
    · rw [hk, hgi i]
      simp
    · by_cases hkj : k = j i
      · rw [hkj, hgj i]
        simp [hj i]
      · rw [hgfix i (b k) (hborth i k (Ne.symm hk)) (hborth (j i) k (Ne.symm hkj))]
        simp [hk, hkj]
  set Ω := supportedFixedDerived Q x with hΩdef
  have hΩB : Ω ≤ supportedBlock Q x (X - 1) := supportedFixedDerived_le_supportedBlock
  let ρ : ↥Ω →* (↥(fixedSpace x) ≃ₗ[K] ↥(fixedSpace x)) :=
    (restrictFixed Q x).comp (Subgroup.inclusion hΩB)
  have hρinj : Function.Injective ρ :=
    (restrictFixed_injective hx).comp (Subgroup.inclusion_injective hΩB)
  have hlift : ∀ i, ∃ ĝ : ↥Ω, ρ ĝ = g i := by
    intro i
    obtain ⟨h, hh⟩ := restrictFixed_surjective hx (g i)
      (orthDerived_le_orthogonalGroup (Q := Q.comp (fixedSpace x).subtype) (hgmem i))
    have hmem : h.1 ∈ Ω := by
      refine mem_supportedFixedDerived.mpr ⟨h.2, ?_⟩
      have hh' : restrictFixed Q x ⟨h.1, h.2⟩ = restrictFixed Q x h := rfl
      rw [hh', hh]
      exact hgmem i
    exact ⟨⟨h.1, hmem⟩, by
      show restrictFixed Q x ⟨h.1, hΩB hmem⟩ = g i
      rw [show (⟨h.1, hΩB hmem⟩ : ↥(supportedBlock Q x (X - 1))) = h from Subtype.ext rfl]
      exact hh⟩
  choose ĝ hĝ using hlift
  set D : Subgroup (↥(fixedSpace x) ≃ₗ[K] ↥(fixedSpace x)) := signChangeSubgroup b with hDdef
  let E : Subgroup ↥Ω := D.comap ρ
  have hE2 : IsPGroup 2 E := by
    have hdom : IsPGroup 2 ↥D := isPGroup_signChangeSubgroup b
    let φ : ↥E →* ↥D :=
      { toFun := fun e => ⟨ρ e.1, Subgroup.mem_comap.mp e.2⟩
        map_one' := Subtype.ext rfl
        map_mul' := fun a b => Subtype.ext rfl }
    refine hdom.of_injective φ fun a b hab => Subtype.ext ?_
    exact hρinj (congrArg (fun z : ↥D => (z : ↥(fixedSpace x) ≃ₗ[K] ↥(fixedSpace x))) hab)
  have hEfix : ∀ v : ↥(fixedSpace x), (∀ e ∈ E, ρ e v = v) → v = 0 := by
    intro v hv
    by_contra hv0
    obtain ⟨i, hi⟩ : ∃ i, b.coord i v ≠ 0 := by
      by_contra h
      push Not at h
      exact hv0 (b.forall_coord_eq_zero_iff.mp h)
    have hmem : ĝ i ∈ E := by
      rw [Subgroup.mem_comap, hĝ i]
      exact hgD i
    have hfix := hv (ĝ i) hmem
    have hcoord : b.coord i (g i v) = - b.coord i v := by
      have hfun : ∀ k, b.coord i (g i (b k)) = - b.coord i (b k) := by
        intro k
        by_cases hk : k = i
        · rw [hk, hgi i]
          simp
        · by_cases hkj : k = j i
          · rw [hkj, hgj i, map_neg]
          · rw [hgfix i (b k) (hborth i k (Ne.symm hk)) (hborth (j i) k (Ne.symm hkj)),
              Basis.coord_apply, Basis.repr_self_apply]
            simp [hk]
      have hlin : b.coord i ∘ₗ (g i : ↥(fixedSpace x) →ₗ[K] ↥(fixedSpace x)) = - b.coord i := by
        refine b.ext fun k => ?_
        simpa using hfun k
      have := congrArg (fun f : ↥(fixedSpace x) →ₗ[K] K => f v) hlin
      simpa using this
    rw [← hĝ i] at hcoord
    rw [hfix] at hcoord
    have h2' : (2 : K) * b.coord i v = 0 := by linear_combination hcoord
    exact hi ((mul_eq_zero.mp h2').resolve_left h2)
  have hTΩ : T ≤ Ω := hFeq ▸ hT
  have hTid : ¬ 2 ∣ (T.subgroupOf Ω).index := by
    rw [← hFeq]
    exact hTodd
  have hT2' : IsPGroup 2 (T.subgroupOf Ω) :=
    hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTΩ).symm
  have hCT : ∀ v : ↥(fixedSpace x), (∀ t ∈ T.subgroupOf Ω, ρ t v = v) → v = 0 := by
    intro v hv
    exact eq_zero_of_fixed_by_subgroup_of_not_dvd_index (E := E) (T := T.subgroupOf Ω) ρ
      Nat.prime_two hE2 hEfix hT2' hTid hv
  have hCfix : ∀ v ∈ fixedSpace x, (∀ t ∈ T, (t : V ≃ₗ[K] V) v = v) → v = 0 := by
    intro v hv hfix
    have h1 : (⟨v, hv⟩ : ↥(fixedSpace x)) = 0 := by
      refine hCT ⟨v, hv⟩ ?_
      intro u hu
      have huT : (u : ↥Ω).1 ∈ T := Subgroup.mem_subgroupOf.mp hu
      have h2' : ρ u ⟨v, hv⟩ = ⟨v, hv⟩ := by
        refine Subtype.ext ?_
        show (restrictFixed Q x (Subgroup.inclusion hΩB u) ⟨v, hv⟩ : V) = v
        rw [coe_restrictFixed]
        exact hfix _ huT
      exact h2'
    exact congrArg Subtype.val h1
  haveI : Fintype ↥T := Fintype.ofFinite ↥T
  have hcard : (Fintype.card T : K) ≠ 0 := by
    obtain ⟨n, hn⟩ := hT2.exists_card_eq
    rw [← Nat.card_eq_fintype_card, hn, Nat.cast_pow]
    exact pow_ne_zero n h2
  have hcompl : IsCompl (fixedSpace x) (othersSpace x.toLinearMap (X - 1)) := hx.fixed_others.1
  have hWpres : ∀ u ∈ T, ∀ w ∈ fixedSpace x, u w ∈ fixedSpace x := by
    intro u hu w hw
    have hbf : u ∈ supportedBlock Q x (X - 1) := supportedFixedDerived_le_supportedBlock (hTΩ hu)
    have hc : u ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) :=
      (Subgroup.mem_inf.mp (mem_supportedBlock.mp hbf).1).2
    exact mem_fixedSpace_of_apply hc hw
  have hWfix : ∀ u ∈ T, ∀ w ∈ othersSpace x.toLinearMap (X - 1), u w = w := by
    intro u hu w hw
    exact (mem_supportedBlock.mp (supportedFixedDerived_le_supportedBlock (hTΩ hu))).2 w hw
  have hinf : fixedSpace x ⊓ fixSub T = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot]
    exact hCfix v hv.1 fun u hu => hv.2 u hu
  obtain ⟨hmoved, hfixsub⟩ :=
    movedSpan_eq_of_isCompl_fixSub (T := T) hcard hcompl hWpres hWfix hinf
  have hcent : ∀ s ∈ S, ∀ u ∈ T, Commute s u := fun s hs u hu => hST s hs u hu
  have hxT : ∀ u ∈ T, Commute x u := by
    intro u hu
    have hbf : u ∈ supportedBlock Q x (X - 1) := supportedFixedDerived_le_supportedBlock (hTΩ hu)
    have hc : u ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) :=
      (Subgroup.mem_inf.mp (mem_supportedBlock.mp hbf).1).2
    exact (Subgroup.mem_centralizer_singleton_iff.mp hc).symm
  have hxscalar : ∀ w ∈ movedSpan T, x w = (1 : K) • w := by
    intro w hw
    rw [hmoved] at hw
    rw [mem_fixedSpace] at hw
    rw [one_smul]
    exact hw
  intro g' hg' f hf
  exact commutator_commute_of_scalar_on_movedSpan (T := T) (S₁ := S) (x := x) (c := 1)
    hcard hcent hxT hxscalar g' hg' f
    (fun w hw => by
      rw [hfixsub] at hw
      exact (mem_supportedBlock.mp (supportedFixedDerived_le_supportedBlock (hFle hf))).2 w hw)
    (fun w hw => by
      rw [hmoved] at hw ⊢
      have hbf : f ∈ supportedBlock Q x (X - 1) :=
        supportedFixedDerived_le_supportedBlock (hFle hf)
      have hc : f ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) :=
        (Subgroup.mem_inf.mp (mem_supportedBlock.mp hbf).1).2
      exact mem_fixedSpace_of_apply hc hw)

end CFSG.LocalAnalysis.GLTheoremA.I2020

end
