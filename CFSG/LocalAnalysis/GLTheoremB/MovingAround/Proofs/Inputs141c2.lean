module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs141c
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearInner
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoPglFaithful
import CFSG.HardMathSupport.Dickson.SuzukiReeB.Helpers
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofReeConj
import CFSG.RankThree.PartTwo.Sec8.Item87ProofGamma
import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalLargeReeMain
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LnAut
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LinearTwo

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141c

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)

open Polynomial CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification
open CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.CALinearPrimary
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple (glA specialFactor IsGoodFactor
  squarefree_minpoly_glA mem_fixSubgroup_slConjugation_iff specialFactor_le_fixSubgroup)

section Blocks

variable {n : ℕ} {k : Type} [Field k] [Finite k]

@[expose] noncomputable def blockPiHom {A : GL (Fin n) k}
    (hsq : Squarefree (minpoly k (glA A : Module.End k (Fin n → k)))) :
    ↥(fixSubgroup (CatalogueBHigherLinearAction.slConjugation n k A)) →*
      ((b : primaryFactors (glA A : Module.End k (Fin n → k))) →
        blockGL (glA A : Module.End k (Fin n → k)) b) :=
  (glCentralizerEquivPi (x := glA A) hsq).toMonoidHom.comp
    (((slGL n k).comp (fixSubgroup (CatalogueBHigherLinearAction.slConjugation n k A)).subtype
      ).codRestrict (gl_centralizer (glA A)) fun g => mem_fixSubgroup_slConjugation_iff.1 g.2)

theorem blockPiHom_apply {A : GL (Fin n) k}
    (hsq : Squarefree (minpoly k (glA A : Module.End k (Fin n → k))))
    (g : ↥(fixSubgroup (CatalogueBHigherLinearAction.slConjugation n k A))) :
    blockPiHom hsq g = glCentralizerEquivPi hsq
      ⟨slGL n k (g : Matrix.SpecialLinearGroup (Fin n) k), mem_fixSubgroup_slConjugation_iff.1 g.2⟩ :=
  rfl

theorem blockPiHom_injective {A : GL (Fin n) k}
    (hsq : Squarefree (minpoly k (glA A : Module.End k (Fin n → k)))) :
    Function.Injective (blockPiHom hsq) := by
  intro g₁ g₂ h
  rw [blockPiHom_apply, blockPiHom_apply] at h
  have h1 := congrArg Subtype.val ((glCentralizerEquivPi hsq).injective h)
  exact Subtype.ext (slGL_injective h1)

theorem blockPiHom_eq_one_of_mem {A : GL (Fin n) k}
    (hsq : Squarefree (minpoly k (glA A : Module.End k (Fin n → k))))
    {b j : primaryFactors (glA A : Module.End k (Fin n → k))} (hjb : j ≠ b)
    (g : ↥(fixSubgroup (CatalogueBHigherLinearAction.slConjugation n k A)))
    (hg : (g : Matrix.SpecialLinearGroup (Fin n) k) ∈ specialFactor A b) : blockPiHom hsq g j = 1 := by
  obtain ⟨-, ht, -⟩ := hg
  have hjb' : (j : k[X]) ≠ (b : k[X]) := fun h => hjb (Subtype.ext h)
  apply Units.ext
  refine LinearMap.ext fun w => Subtype.ext ?_
  show blockApply (blockPiHom hsq g j) (w : Fin n → k) w.2 = (w : Fin n → k)
  rw [blockPiHom_apply, blockApply_glCentralizerEquivPi]
  exact ht j j.2 hjb' w w.2

theorem blockPiHom_eq_mulSingle {A : GL (Fin n) k}
    (hsq : Squarefree (minpoly k (glA A : Module.End k (Fin n → k))))
    [DecidableEq ↥(primaryFactors (glA A : Module.End k (Fin n → k)))]
    {b : primaryFactors (glA A : Module.End k (Fin n → k))}
    (g : ↥(fixSubgroup (CatalogueBHigherLinearAction.slConjugation n k A)))
    (hg : (g : Matrix.SpecialLinearGroup (Fin n) k) ∈ specialFactor A b) :
    blockPiHom hsq g = Pi.mulSingle b (blockPiHom hsq g b) := by
  funext j
  by_cases hjb : j = b
  · subst hjb
    rw [Pi.mulSingle_eq_same]
  · rw [Pi.mulSingle_eq_of_ne hjb, blockPiHom_eq_one_of_mem hsq hjb g hg]

theorem specialFactor_comm {A : GL (Fin n) k}
    (hsq : Squarefree (minpoly k (glA A : Module.End k (Fin n → k))))
    {b b' : primaryFactors (glA A : Module.End k (Fin n → k))} (hbb' : b ≠ b')
    {x y : Matrix.SpecialLinearGroup (Fin n) k} (hx : x ∈ specialFactor A b) (hy : y ∈ specialFactor A b') :
    x * y = y * x := by
  classical
  set x' : ↥(fixSubgroup (CatalogueBHigherLinearAction.slConjugation n k A)) :=
    ⟨x, specialFactor_le_fixSubgroup A b hx⟩ with hx'
  set y' : ↥(fixSubgroup (CatalogueBHigherLinearAction.slConjugation n k A)) :=
    ⟨y, specialFactor_le_fixSubgroup A b' hy⟩ with hy'
  have h1 : blockPiHom hsq (x' * y') = blockPiHom hsq (y' * x') := by
    rw [map_mul, map_mul, blockPiHom_eq_mulSingle hsq x' hx, blockPiHom_eq_mulSingle hsq y' hy]
    exact (Pi.mulSingle_commute hbb' _ _).eq
  have h2 := congrArg Subtype.val (blockPiHom_injective hsq h1)
  exact h2

theorem symm_mulSingle_mem_linearSpecialBlock' {K : Type*} [Field K] {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {x : LinearMap.GeneralLinearGroup K V}
    [DecidableEq (primaryFactors (x : Module.End K V))]
    (hsq : Squarefree (minpoly K (x : Module.End K V)))
    (b : primaryFactors (x : Module.End K V)) (c : blockGL (x : Module.End K V) (b : K[X]))
    (hc : LinearMap.det (c : Module.End (AdjoinRoot (b : K[X]))
      (primaryComponent (x : Module.End K V) (b : K[X]))) = 1) :
    (((glCentralizerEquivPi hsq).symm (Pi.mulSingle b c) : gl_centralizer x) :
      LinearMap.GeneralLinearGroup K V) ∈ linearSpecialBlock x (b : K[X]) := by
  set g := (glCentralizerEquivPi hsq).symm (Pi.mulSingle b c) with hgdef
  have hgapp : ∀ (j : primaryFactors (x : Module.End K V)) (v : V)
      (hv : v ∈ primaryComponent (x : Module.End K V) (j : K[X])),
      ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v =
        blockApply ((Pi.mulSingle b c : (j : primaryFactors (x : Module.End K V)) →
          blockGL (x : Module.End K V) (j : K[X])) j) v hv := by
    intro j v hv
    rw [← blockApply_glCentralizerEquivPi hsq g j v hv, hgdef, MulEquiv.apply_symm_apply]
  refine ⟨g.2, fun j hj hjh v hv => ?_, ?_⟩
  · rw [hgapp ⟨j, hj⟩ v hv, Pi.mulSingle_eq_of_ne (fun h' => hjh (congrArg Subtype.val h'))]
    rfl
  · have heq : commutantRestrict (b : K[X]) ⟨((g : LinearMap.GeneralLinearGroup K V) :
        Module.End K V), mem_commutant_of_mem_gl_centralizer g.2⟩ =
        (c : Module.End (AdjoinRoot (b : K[X]))
          (primaryComponent (x : Module.End K V) (b : K[X]))) :=
      LinearMap.ext fun v => Subtype.ext
        ((hgapp b v v.2).trans (by rw [Pi.mulSingle_eq_same]; rfl))
    rw [heq]
    exact hc

theorem eq_one_of_pow_two_pow_eq_one {E : Type*} [Field E] [CharP E 2] {u : E} {m : ℕ}
    (hu : u ^ (2 ^ m) = 1) : u = 1 := by
  have h1 : (u - 1) ^ (2 ^ m) = 0 := by rw [sub_pow_char_pow, hu, one_pow, sub_self]
  exact sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero m two_ne_zero) |>.1 h1)

theorem mem_iSup_specialFactor_of_two [CharP k 2] {A : GL (Fin n) k}
    (hsq : Squarefree (minpoly k (glA A : Module.End k (Fin n → k))))
    (g : ↥(fixSubgroup (CatalogueBHigherLinearAction.slConjugation n k A))) {m : ℕ} (hgm : g ^ (2 ^ m) = 1) :
    (g : Matrix.SpecialLinearGroup (Fin n) k) ∈
      ⨆ b : primaryFactors (glA A : Module.End k (Fin n → k)), specialFactor A b := by
  classical
  have hdet : ∀ b : primaryFactors (glA A : Module.End k (Fin n → k)),
      LinearMap.det ((blockPiHom hsq g b : blockGL (glA A : Module.End k (Fin n → k)) b) :
        Module.End (AdjoinRoot (b : k[X]))
          (primaryComponent (glA A : Module.End k (Fin n → k)) (b : k[X]))) = 1 := by
    intro b
    haveI : Fact (Irreducible (b : k[X])) := ⟨irreducible_of_mem_primaryFactors b.2⟩
    haveI : CharP (AdjoinRoot (b : k[X])) 2 :=
      charP_of_injective_algebraMap (algebraMap k (AdjoinRoot (b : k[X]))).injective 2
    have h1 : (blockPiHom hsq g b) ^ (2 ^ m) = 1 := by
      rw [← Pi.pow_apply, ← map_pow, hgm, map_one, Pi.one_apply]
    refine eq_one_of_pow_two_pow_eq_one (m := m) ?_
    rw [← map_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, map_one]
  set W : Subgroup (Matrix.SpecialLinearGroup (Fin n) k) :=
    ⨆ b : primaryFactors (glA A : Module.End k (Fin n → k)), specialFactor A b
  have key : blockPiHom hsq g ∈ (W.subgroupOf
      (fixSubgroup (CatalogueBHigherLinearAction.slConjugation n k A))).map (blockPiHom hsq) := by
    refine Subgroup.pi_mem_of_mulSingle_mem _ fun b => ?_
    have hγ := symm_mulSingle_mem_linearSpecialBlock' (x := glA A) hsq b (blockPiHom hsq g b) (hdet b)
    obtain ⟨s, hs⟩ := mem_range_slGL (det_eq_one_of_mem_linearSpecialBlock hsq b.2 hγ)
    have hsmem : s ∈ specialFactor A b := by
      rw [specialFactor, Subgroup.mem_comap, hs]
      exact hγ
    have hsfix : s ∈ fixSubgroup (CatalogueBHigherLinearAction.slConjugation n k A) :=
      mem_fixSubgroup_slConjugation_iff.2 (by rw [hs]; exact hγ.1)
    have hθs : blockPiHom hsq ⟨s, hsfix⟩ = Pi.mulSingle b (blockPiHom hsq g b) := by
      rw [blockPiHom_apply]
      exact (glCentralizerEquivPi hsq).eq_symm_apply.1 (Subtype.ext hs)
    rw [← hθs]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 (Subgroup.mem_iSup_of_mem b hsmem))
  obtain ⟨w, hw, hwg⟩ := key
  rw [← blockPiHom_injective hsq hwg]
  exact Subgroup.mem_subgroupOf.1 hw

end Blocks

section Projective

variable {n : ℕ} {k : Type} [Field k] [Finite k] [CharP k 2]

theorem coprime_two_card_ker_proj (hn : 1 ≤ n) : Nat.Coprime 2 (Nat.card (LinearFlag.proj n k).ker) := by
  rw [LinearFlag.ker_proj, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
  intro h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h
  have hz2 : z ^ 2 = 1 := hz ▸ pow_orderOf_eq_one z
  obtain ⟨c, -, hzc⟩ := z.2
  have hc2 : (c : k) ^ (2 ^ 1) = 1 := by
    have h1 := congrArg (fun w : ↥(LinearFlag.scalars n k) =>
      ((w : Matrix.SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) ⟨0, hn⟩ ⟨0, hn⟩) hz2
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one, Matrix.SpecialLinearGroup.coe_pow,
      Matrix.SpecialLinearGroup.coe_one] at h1
    rw [hzc, ← map_pow, Matrix.scalar_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h1
    simpa using h1
  have hc1 : (c : k) = 1 := eq_one_of_pow_two_pow_eq_one hc2
  have hz1 : z = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    rw [hzc, hc1, map_one]
    rfl
  rw [hz1, orderOf_one] at hz
  exact absurd hz (by norm_num)

theorem ker_proj_le_center : (LinearFlag.proj n k).ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) k) := by
  rw [LinearFlag.ker_proj]
  exact LinearFlag.scalars_le_center n k

theorem three_ne_zero_of_charTwo : ((3 : ℕ) : k) ≠ 0 := by
  have h2 : ((2 : ℕ) : k) = 0 := CharP.cast_eq_zero k 2
  have e : ((3 : ℕ) : k) = ((2 : ℕ) : k) + 1 := by push_cast; ring
  rw [e, h2, zero_add]
  exact one_ne_zero

theorem structAt_conjAut (hn : 1 ≤ n) {A : GL (Fin n) k} {c : kˣ}
    (hA : A ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) c) {J : Subgroup (LinearFlag.projectiveSL n k)}
    (hJ : GLAPComponent 3 (fixSubgroup (LinearFlag.conjAut n k A)) J) :
    StructAt (LinearFlag.conjAut n k A) J := by
  have h3 : ((3 : ℕ) : k) ≠ 0 := three_ne_zero_of_charTwo
  have hsq := squarefree_minpoly_glA h3 hA
  have hαβ : ∀ x, LinearFlag.proj n k (CatalogueBHigherLinearAction.slConjugation n k A x) =
      LinearFlag.conjAut n k A (LinearFlag.proj n k x) := fun x => (LinearFlag.conjAut_proj A x).symm
  refine ⟨Set.range fun b : primaryFactors (glA A : Module.End k (Fin n → k)) =>
    (specialFactor A b).map (LinearFlag.proj n k), ?_, ?_, ?_⟩
  · rintro _ ⟨b, rfl⟩ _ ⟨b', rfl⟩ hne _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have hbb' : b ≠ b' := fun h => hne (by rw [h])
    rw [← map_mul, ← map_mul, specialFactor_comm hsq hbb' hx hy]
  · intro x hx hx2
    obtain ⟨g, hg, hg2, rfl⟩ := exists_two_lift (LinearFlag.proj n k) (LinearFlag.proj_surjective n k)
      ker_proj_le_center (coprime_two_card_ker_proj hn) _ _ hαβ hx hx2
    obtain ⟨m, hm⟩ := hg2 ⟨g, Subgroup.mem_zpowers g⟩
    have hgm : (⟨g, hg⟩ : ↥(fixSubgroup (CatalogueBHigherLinearAction.slConjugation n k A))) ^ (2 ^ m) = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hm)
    have h1 := mem_iSup_specialFactor_of_two hsq ⟨g, hg⟩ hgm
    have h2 : (⨆ b : primaryFactors (glA A : Module.End k (Fin n → k)), specialFactor A b) ≤
        (sSup (Set.range fun b : primaryFactors (glA A : Module.End k (Fin n → k)) =>
          (specialFactor A b).map (LinearFlag.proj n k))).comap (LinearFlag.proj n k) :=
      iSup_le fun b => Subgroup.map_le_iff_le_comap.1 (le_sSup ⟨b, rfl⟩)
    exact h2 h1
  · have hlay := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfectInLayer_conjAut h3 hA J hJ.1
      (glaPComponent_perfect hJ)
    refine hlay.trans (sSup_le fun K hK => ?_)
    obtain ⟨h, rfl⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.linear_inner_components h3 hA K hK
    exact le_iSup₂_of_le _ ⟨h.1, rfl⟩ (le_iSup_of_le hK le_rfl)

theorem false_of_glaPComponent_of_isSolvable {G : Type} [Group G] [Finite G] {C J : Subgroup G}
    (hC : Group.IsSolvable ↥C) (hJ : GLAPComponent 3 C J) : False := by
  have hJC : J ≤ C := hJ.1
  haveI : Group.IsSolvable ↥J :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hJC) (Subgroup.inclusion_injective hJC)
  have hperf : commutator ↥J = ⊤ := by
    have h1 : (commutator ↥J).map J.subtype = ⁅J, J⁆ := by
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [glaPComponent_perfect hJ] at h1
    rw [eq_top_iff]
    intro x _
    have hx : (x : G) ∈ (commutator ↥J).map J.subtype := by
      rw [h1]
      exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    rwa [Subtype.ext hyx] at hy
  obtain ⟨m, hm⟩ := (‹Group.IsSolvable ↥J›).solvable
  have htop : ∀ i, derivedSeries ↥J i = ⊤ := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih => rw [derivedSeries_succ, ih, ← commutator_def, hperf]
  have hJbot : J = ⊥ := by
    have h1 := htop m
    rw [hm] at h1
    rw [eq_bot_iff]
    intro x hx
    have h2 : (⟨x, hx⟩ : ↥J) ∈ (⊥ : Subgroup ↥J) := h1 ▸ Subgroup.mem_top _
    rw [Subgroup.mem_bot] at h2
    exact Subgroup.mem_bot.2 (congrArg Subtype.val h2)
  exact Input183.glaPComponent_ne_bot' hJ hJbot

open Matrix in
theorem injective_map_subtype' (k₀ : Subfield k) :
    Function.Injective (SpecialLinearGroup.map k₀.subtype :
      SpecialLinearGroup (Fin n) k₀ →* SpecialLinearGroup (Fin n) k) := by
  intro g g' hgg'
  refine Subtype.ext (Matrix.ext fun a b => Subtype.val_injective ?_)
  have h1 := congrArg (fun x : SpecialLinearGroup (Fin n) k =>
    (x : Matrix (Fin n) (Fin n) k) a b) hgg'
  simpa [SpecialLinearGroup.map_apply_coe] using h1

open Matrix in
theorem fixSubgroup_slFieldAut_eq_range' {k₀ : Subfield k} {σ : k ≃+* k}
    (hk : ∀ x, x ∈ k₀ ↔ σ x = x) :
    fixSubgroup (CatalogueBHigherLinearField.slFieldAut (Fin n) k σ) =
      (SpecialLinearGroup.map k₀.subtype :
        SpecialLinearGroup (Fin n) k₀ →* SpecialLinearGroup (Fin n) k).range := by
  ext g
  rw [mem_fixSubgroup]
  constructor
  · intro hg
    have hent : ∀ a b, σ ((g : Matrix (Fin n) (Fin n) k) a b) =
        (g : Matrix (Fin n) (Fin n) k) a b := fun a b =>
      congrArg (fun x : SpecialLinearGroup (Fin n) k => (x : Matrix (Fin n) (Fin n) k) a b) hg
    let g₀ : Matrix (Fin n) (Fin n) k₀ := Matrix.of fun a b => ⟨_, (hk _).2 (hent a b)⟩
    have hg₀ : g₀.map k₀.subtype = g := Matrix.ext fun _ _ => rfl
    have hdet : g₀.det = 1 := Subtype.val_injective (by
      change k₀.subtype g₀.det = k₀.subtype 1
      rw [RingHom.map_det, map_one]
      change (g₀.map k₀.subtype).det = 1
      rw [hg₀]
      exact g.2)
    exact ⟨⟨g₀, hdet⟩, Subtype.ext hg₀⟩
  · rintro ⟨g₀, rfl⟩
    refine Subtype.ext (Matrix.ext fun a b => ?_)
    exact (hk _).1 ((g₀ : Matrix (Fin n) (Fin n) k₀) a b).2

theorem structAt_fieldAut (hn : 2 ≤ n) (σ : k ≃+* k) {J : Subgroup (LinearFlag.projectiveSL n k)}
    (hJ : GLAPComponent 3 (fixSubgroup (LinearFlag.fieldAut n k σ)) J) :
    StructAt (LinearFlag.fieldAut n k σ) J := by
  have hαβ : ∀ x, LinearFlag.proj n k (CatalogueBHigherLinearField.slFieldAut (Fin n) k σ x) =
      LinearFlag.fieldAut n k σ (LinearFlag.proj n k x) :=
    fun x => (LinearFlag.descendAut_proj n k _ x).symm
  refine structAt_of_cover (LinearFlag.proj n k) (LinearFlag.proj_surjective n k) ker_proj_le_center
    (coprime_two_card_ker_proj (by omega)) _ _ hαβ hJ fun J₀ hJ₀ _ => ?_
  have hk : ∀ x, x ∈ CFSG.GH74.GLS.IVK.fixedField σ ↔ σ x = x := CFSG.GH74.GLS.IVK.mem_fixedField_iff σ
  have hC := fixSubgroup_slFieldAut_eq_range' (n := n) hk
  let e : Matrix.SpecialLinearGroup (Fin n) (CFSG.GH74.GLS.IVK.fixedField σ) ≃*
      ↥(fixSubgroup (CatalogueBHigherLinearField.slFieldAut (Fin n) k σ)) :=
    (MonoidHom.ofInjective (injective_map_subtype' _)).trans (MulEquiv.subgroupCongr hC.symm)
  by_cases hperf : 3 ≤ n ∨ 4 ≤ Nat.card (CFSG.GH74.GLS.IVK.fixedField σ)
  · have hq : CFSG.IsQuasisimple ↥(fixSubgroup (CatalogueBHigherLinearField.slFieldAut (Fin n) k σ)) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv e
        (CFSG.SeitzReduction.LinearPilot.isQuasisimple_specialLinearGroup_of_le hn hperf)
    exact structAt_of_isQuasisimple_fixSubgroup ⟨hq.1.1, hq.2.1⟩ hJ₀.1
  · exfalso
    obtain rfl : n = 2 := by omega
    have hcard : Nat.card (CFSG.GH74.GLS.IVK.fixedField σ) = 2 ∨
        Nat.card (CFSG.GH74.GLS.IVK.fixedField σ) = 3 := by
      have : 1 < Nat.card (CFSG.GH74.GLS.IVK.fixedField σ) := Finite.one_lt_card
      omega
    haveI : Group.IsSolvable (GL (Fin 2) (CFSG.GH74.GLS.IVK.fixedField σ)) :=
      CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable _ hcard
    haveI : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) (CFSG.GH74.GLS.IVK.fixedField σ)) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 2) _ →* _))
        Matrix.SpecialLinearGroup.toGL_injective
    have hsolv : Group.IsSolvable ↥(fixSubgroup (CatalogueBHigherLinearField.slFieldAut (Fin 2) k σ)) :=
      Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective
    exact false_of_glaPComponent_of_isSolvable hsolv hJ₀

end Projective

section Cases

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

theorem projectiveSL_cases_of_three_le {n : ℕ} (hn : 3 ≤ n) {K : Type} [Field K] [Finite K]
    (hK3 : ringChar K ≠ 3) (β : MulAut (LinearFlag.projectiveSL n K)) (hβ : β ^ 3 = 1) :
    (∃ (A : GL (Fin n) K) (c : Kˣ), A ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) c ∧
      β = LinearFlag.conjAut n K A) ∨
    (∃ (h : MulAut (LinearFlag.projectiveSL n K)) (σ : K ≃+* K), orderOf σ = 3 ∧
      β = h * LinearFlag.fieldAut n K σ * h⁻¹) := by
  obtain ⟨f, hf, hℓ, hK⟩ : ∃ f : ℕ, 1 ≤ f ∧ (ringChar K).Prime ∧ Nat.card K = ringChar K ^ f := by
    have := Fintype.ofFinite K
    obtain ⟨f, hℓ, hK⟩ := FiniteField.card K (ringChar K)
    exact ⟨f, f.pos, hℓ, by rw [Nat.card_eq_fintype_card, hK]⟩
  have hdesc := CFSG.RankThree.LinearDescent.higher_linear_prime_semilinear_field_descent hℓ hf hn hK
  by_cases hlin : β ∈ LinearFlag.linearAutGroup n K
  · left
    have hrange : LinearFlag.linearAutGroup n K = (LinearFlag.conjAut n K).range := by
      rw [LinearFlag.linearAutGroup, ← MonoidHom.coe_range, Subgroup.closure_eq]
    rw [hrange] at hlin
    obtain ⟨A, rfl⟩ := hlin
    have hAp : A ^ 3 ∈ (LinearFlag.conjAut n K).ker := by rw [MonoidHom.mem_ker, map_pow, hβ]
    rw [hdesc.1] at hAp
    obtain ⟨c, hc⟩ := hAp
    exact ⟨A, c, hc.symm, rfl⟩
  · right
    obtain ⟨A, σ, rfl⟩ := CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.exists_conj_field_of_odd hn
      (by decide : Odd 3) hβ
    have hmem : LinearFlag.conjAut n K A * LinearFlag.fieldAut n K σ ∈
        LinearFlag.semilinearAutGroup n K :=
      mul_mem (LinearFlag.linearAutGroup_le_semilinearAutGroup
        (LinearFlag.conjAut_mem_linearAutGroup A))
        (LinearFlag.fieldAut_mem_semilinearAutGroup σ)
    have hne : LinearFlag.conjAut n K A * LinearFlag.fieldAut n K σ ≠ 1 := fun h =>
      hlin (h ▸ one_mem _)
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hord : orderOf (LinearFlag.conjAut n K A * LinearFlag.fieldAut n K σ) = 3 :=
      orderOf_eq_prime hβ hne
    obtain ⟨-, τ, hτ, ⟨h, -, hβτ⟩, -⟩ :=
      hdesc.2.2.2.2.2.2.2 3 Nat.prime_three (fun h => hK3 h.symm) _ hmem hlin hord
    exact ⟨h, τ, hτ, hβτ⟩

theorem projectiveSL_cases_two {K : Type} [Field K] [Finite K]
    (β : MulAut (LinearFlag.projectiveSL 2 K)) (hβ : β ^ 3 = 1) :
    (∃ (A : GL (Fin 2) K) (c : Kˣ), A ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 2) c ∧
      β = LinearFlag.conjAut 2 K A) ∨
    (∃ (h : MulAut (LinearFlag.projectiveSL 2 K)) (σ : K ≃+* K), orderOf σ = 3 ∧
      β = h * LinearFlag.fieldAut 2 K σ * h⁻¹) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨β₀, hββ₀⟩ : ∃ β₀ : MulAut (PSL2 K), MulAut.congr (psl2Equiv K) β₀ = β :=
    ⟨(MulAut.congr (psl2Equiv K)).symm β, (MulAut.congr (psl2Equiv K)).apply_symm_apply β⟩
  have hβ₀p : β₀ ^ 3 = 1 :=
    (MulAut.congr (psl2Equiv K)).injective (by rw [map_pow, hββ₀, hβ, map_one])
  by_cases hD : β₀ ∈ (pglAction K).range
  · left
    obtain ⟨g, hg⟩ := hD
    obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
    have hβA : β = LinearFlag.conjAut 2 K A := by
      rw [← hββ₀, ← hg]
      exact congr_pglAction_mk A
    have hAp : A ^ 3 ∈ Subgroup.center (GL (Fin 2) K) := by
      have h1 : pglAction K (Matrix.ProjGenLinGroup.mk (A ^ 3)) = pglAction K 1 := by
        rw [map_pow, map_pow, hg, hβ₀p, map_one]
      exact Matrix.ProjGenLinGroup.mk_eq_one.1
        (CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglAction_injective K h1)
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hAp
    obtain ⟨c, hc⟩ := hAp
    exact ⟨A, c, hc.symm, hβA⟩
  · right
    have hne : β₀ ≠ 1 := fun h => hD ⟨1, by rw [map_one, h]⟩
    have hord : orderOf β₀ = 3 := orderOf_eq_prime hβ₀p hne
    obtain ⟨σ, hσ, g, hgσ⟩ :=
      CFSG.RankThree.PartTwo.KFacts.linear_two_prime_order_field_descent Nat.prime_three β₀ hord hD
    obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
    have hcongr : MulAut.congr (psl2Equiv K)
        (pglAction K (Matrix.ProjGenLinGroup.mk A)) = LinearFlag.conjAut 2 K A :=
      congr_pglAction_mk A
    refine ⟨LinearFlag.conjAut 2 K A, σ, hσ, ?_⟩
    rw [← hββ₀, hgσ, map_mul, map_mul, map_inv, hcongr, congr_psl2FieldAut]

end Cases

section Linear

theorem glaPComponent_congr {Q Q' : Type} [Group Q] [Group Q'] [Finite Q] (e : Q ≃* Q') {β : MulAut Q}
    {J : Subgroup Q} (hJ : GLAPComponent 3 (fixSubgroup β) J) :
    GLAPComponent 3 (fixSubgroup (MulAut.congr e β)) (J.map e.toMonoidHom) := by
  rw [fixSubgroup_congr]
  refine glaPComponent_map Nat.prime_three e.toMonoidHom ?_ hJ
  have h1 : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).2 e.injective
  rw [h1, inf_bot_eq, Subgroup.card_bot]
  exact Nat.coprime_one_right 3

theorem structAt_projectiveSL {n : ℕ} (hn : 2 ≤ n) {k : Type} [Field k] [Finite k] [CharP k 2]
    (β : MulAut (LinearFlag.projectiveSL n k)) (hβ : β ^ 3 = 1) {J : Subgroup (LinearFlag.projectiveSL n k)}
    (hJ : GLAPComponent 3 (fixSubgroup β) J) : StructAt β J := by
  have hcases : (∃ (A : GL (Fin n) k) (c : kˣ), A ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) c ∧
      β = LinearFlag.conjAut n k A) ∨
      (∃ (h : MulAut (LinearFlag.projectiveSL n k)) (σ : k ≃+* k), orderOf σ = 3 ∧
        β = h * LinearFlag.fieldAut n k σ * h⁻¹) := by
    rcases Nat.lt_or_ge n 3 with hn3 | hn3
    · obtain rfl : n = 2 := by omega
      exact projectiveSL_cases_two β hβ
    · refine projectiveSL_cases_of_three_le hn3 ?_ β hβ
      rw [ringChar.eq k 2]
      norm_num
  rcases hcases with ⟨A, c, hA, rfl⟩ | ⟨h, σ, -, rfl⟩
  · exact structAt_conjAut (by omega) hA hJ
  · have hc : MulAut.congr (h⁻¹ : MulAut (LinearFlag.projectiveSL n k)) (h * LinearFlag.fieldAut n k σ * h⁻¹) =
        LinearFlag.fieldAut n k σ := by
      have e1 : MulAut.congr (h⁻¹ : MulAut (LinearFlag.projectiveSL n k)) (h * LinearFlag.fieldAut n k σ * h⁻¹) =
          h⁻¹ * (h * LinearFlag.fieldAut n k σ * h⁻¹) * h⁻¹⁻¹ := by
        ext y
        rfl
      rw [e1]
      group
    refine structAt_of_congr (h⁻¹ : MulAut (LinearFlag.projectiveSL n k)) ?_
    have hJ' := glaPComponent_congr (h⁻¹ : MulAut (LinearFlag.projectiveSL n k)) hJ
    rw [hc] at hJ' ⊢
    exact structAt_fieldAut hn σ hJ'

theorem input14_1StructFor_linear : Input14_1StructFor fun d => ∃ r q, d = TauCeti.LieTypeIndex.A r q := by
  intro S _ _ _ _ d hd hchar he β hβ3 _ J hJ _
  obtain ⟨d, hv⟩ := d
  obtain ⟨r, q, rfl⟩ := hd
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hq2 : q.p = 2 := by
    have h1 : (TauCeti.LieTypeIndex.A r q).characteristic = q.p := TauCeti.LieTypeIndex.characteristic_A r q
    rw [← h1]
    exact hchar
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  obtain ⟨e⟩ := he
  let e' : S ≃* LinearFlag.projectiveSL (r + 1) (GaloisField q.p q.exponent) :=
    e.trans ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (r + 1) _))
  haveI : CharP (GaloisField q.p q.exponent) 2 := by
    rw [← hq2]
    infer_instance
  refine structAt_of_congr e' (structAt_projectiveSL (by omega) _ ?_ (glaPComponent_congr e' hJ))
  rw [← map_pow, hβ3, map_one]

end Linear

section SuzukiReeTitsFree

open CFSG.LieType.Ree CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley

theorem not_three_dvd_suzuki_order' (a : ℕ) :
    ¬ 3 ∣ (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
  have hq : 2 ^ (2 * a + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  generalize 2 ^ (2 * a + 1) = q at hq ⊢
  have hq2 : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hq]
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
    · have := Nat.prime_three.dvd_of_dvd_pow h
      omega
    · omega
  · omega

theorem card_dvd_card_of_isLThreeFour {S : Type} [Group S] [Finite S] {C J : Subgroup S}
    (hJ : GLAPComponent 3 C J) (hJt : IsLThreeFour (barOf 3 J ⧸ Subgroup.center (barOf 3 J))) :
    20160 ∣ Nat.card S :=
  ((card_dvd_of_isLThreeFour hJt).trans (Subgroup.card_dvd_of_le hJ.1)).trans (Subgroup.card_subgroup_dvd_card C)

theorem commutator_eq_top_of_glaPComponent {G : Type} [Group G] {C J : Subgroup G} (hJ : GLAPComponent 3 C J) :
    commutator ↥J = ⊤ := by
  have h1 : (commutator ↥J).map J.subtype = ⁅J, J⁆ := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [glaPComponent_perfect hJ] at h1
  rw [eq_top_iff]
  intro x _
  have hx : (x : G) ∈ (commutator ↥J).map J.subtype := by
    rw [h1]
    exact x.2
  obtain ⟨y, hy, hyx⟩ := hx
  rwa [Subtype.ext hyx] at hy

theorem input14_1StructFor_suzuki :
    Input14_1StructFor fun d => ∃ m, d = TauCeti.LieTypeIndex.suzuki m := by
  intro S _ _ _ _ d hd _ he β _ _ J hJ hJt
  exfalso
  obtain ⟨d, hv⟩ := d
  obtain ⟨m, rfl⟩ := hd
  obtain ⟨e⟩ := he
  obtain ⟨-, a, -, K, _, _, hf, hK', ⟨θ⟩⟩ := CFSG.RankThree.PartTwo.Sec4.Census.suzukiModel_of_index m hv
  have hK : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK', hf]
  have hS := card_dvd_card_of_isLThreeFour hJ hJt
  rw [Nat.card_congr (e.trans θ).toEquiv, CFSG.LieType.Ree.suzuki_order hK] at hS
  exact not_three_dvd_suzuki_order' a ((by norm_num : 3 ∣ 20160).trans hS)

end SuzukiReeTitsFree

section SuzukiReeTits

set_option linter.unusedSectionVars false

open CFSG.LieType.Ree CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley

theorem input14_1StructFor_tits : Input14_1StructFor fun d => d = TauCeti.LieTypeIndex.tits := by
  intro S _ _ _ _ d hd _ he β _ _ J hJ hJt
  exfalso
  obtain ⟨d, hv⟩ := d
  subst hd
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv S 2 1
    (CFSG.RankThree.PartOne.CTP.reeTitsModel_tits (S := S) ⟨hv, he⟩)
  have hS := card_dvd_card_of_isLThreeFour hJ hJt
  rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Schreier.Tits.card_titsD] at hS
  norm_num at hS

theorem structAt_fieldAut_reeGamma {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (σ : K ≃+* K) (hσ : orderOf σ = 3)
    {J : Subgroup (ReeTag.F4.reeGamma K a)}
    (hJ : GLAPComponent 3 (fixSubgroup (ReeTag.F4.reeGammaFieldAut K a σ)) J) (hJ7 : 7 ∣ Nat.card ↥J) :
    StructAt (ReeTag.F4.reeGammaFieldAut K a σ) J := by
  classical
  obtain ⟨b, -, hkcard, hfixed⟩ :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.largeRee_fixed_data_odd hK Nat.prime_three (by norm_num) σ hσ
  have : Finite (fixSubfield σ) := Subtype.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP (fixSubfield σ) ReeTag.F4.prime := by
    have : Fintype (fixSubfield σ) := Fintype.ofFinite _
    exact charP_of_card_eq_prime_pow (f := 2 * b + 1) (by
      rw [← Nat.card_eq_fintype_card, hkcard]
      rfl)
  have hFix : fixSubgroup (ReeTag.F4.reeGammaFieldAut K a σ) =
      (ReeTag.F4.reeGammaFieldAut K a σ).toMonoidHom.eqLocus (MonoidHom.id _) := rfl
  let eC : fixSubgroup (ReeTag.F4.reeGammaFieldAut K a σ) ≃* ReeTag.F4.reeGamma (fixSubfield σ) b :=
    (((fixSubgroup (ReeTag.F4.reeGammaFieldAut K a σ)).equivMapOfInjective
      (ReeTag.F4.reeGamma K a).subtype (ReeTag.F4.reeGamma K a).subtype_injective).trans
      (MulEquiv.subgroupCongr (by rw [hFix]; exact hfixed))).trans
    ((ReeTag.F4.reeGamma (fixSubfield σ) b).equivMapOfInjective _
      (baseChangeGL_injective (τ := ReeTag.F4.tag) (fixSubfield σ).subtype)).symm
  rcases Nat.eq_zero_or_pos b with hb0 | hb
  · exfalso
    subst hb0
    have hk2 : Nat.card (fixSubfield σ) = 2 := by simpa using hkcard
    haveI : Fact (Nat.card (fixSubfield σ) = 2) := ⟨hk2⟩
    let E : fixSubgroup (ReeTag.F4.reeGammaFieldAut K a σ) ≃* reeFixed ReeTag.F4 (fixSubfield σ) 0 :=
      eC.trans (ReeTag.reeFixedEquivReeGamma (fixSubfield σ) 0).symm
    let φ : ↥J →* reeFixed ReeTag.F4 (fixSubfield σ) 0 := E.toMonoidHom.comp (Subgroup.inclusion hJ.1)
    have hφ : Function.Injective φ := E.injective.comp (Subgroup.inclusion_injective hJ.1)
    have hperf := commutator_eq_top_of_glaPComponent hJ
    have hle : φ.range ≤ commutator (reeFixed ReeTag.F4 (fixSubfield σ) 0) := by
      rw [MonoidHom.range_eq_map, ← hperf]
      calc (commutator ↥J).map φ = ⁅(⊤ : Subgroup ↥J).map φ, (⊤ : Subgroup ↥J).map φ⁆ := by
            rw [commutator_def, Subgroup.map_commutator]
        _ ≤ ⁅(⊤ : Subgroup (reeFixed ReeTag.F4 (fixSubfield σ) 0)), ⊤⁆ := Subgroup.commutator_mono le_top le_top
        _ = commutator (reeFixed ReeTag.F4 (fixSubfield σ) 0) := (commutator_def _).symm
    have hcard : Nat.card ↥J ∣ 17971200 := by
      have h1 : Nat.card φ.range = Nat.card ↥J := by
        rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hφ, Subgroup.card_top]
      have h2 := Subgroup.card_dvd_of_le hle
      rw [h1, Nat.card_congr (CFSG.Sporadic.Schreier.Tits.titsDerivedIso (K := fixSubfield σ)).toEquiv,
        CFSG.Sporadic.Schreier.Tits.card_titsD] at h2
      exact h2
    have h7 := hJ7.trans hcard
    norm_num at h7
  · have hs : IsSimpleGroup (ReeTag.F4.reeGamma (fixSubfield σ) b) :=
      CFSG.SignalizerFunctorTheorem.CatalogBridge.isSimpleGroup_reeGamma_F4 hb hkcard
    have hperf : commutator (ReeTag.F4.reeGamma (fixSubfield σ) b) = ⊤ :=
      ReeTag.commutator_reeGamma_eq_top (t := ReeTag.F4) hb hkcard
    have hnc : ∃ x y : ReeTag.F4.reeGamma (fixSubfield σ) b, x * y ≠ y * x := by
      by_contra hab
      push Not at hab
      have hc : commutator (ReeTag.F4.reeGamma (fixSubfield σ) b) = ⊥ := by
        rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x _
        rw [Subgroup.mem_centralizer_iff]
        intro y _
        exact hab y x
      rw [hperf] at hc
      exact top_ne_bot hc
    have hq := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1
    have hqC : CFSG.IsQuasisimple ↥(fixSubgroup (ReeTag.F4.reeGammaFieldAut K a σ)) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv eC.symm hq
    exact structAt_of_isQuasisimple_fixSubgroup ⟨hqC.1.1, hqC.2.1⟩ hJ.1

theorem structAt_reeGamma {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {β : MulAut (ReeTag.F4.reeGamma K a)} (hβ : β ^ 3 = 1) (hβ1 : β ≠ 1)
    {J : Subgroup (ReeTag.F4.reeGamma K a)} (hJ : GLAPComponent 3 (fixSubgroup β) J)
    (hJ7 : 7 ∣ Nat.card ↥J) : StructAt β J := by
  classical
  haveI : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  haveI : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hNF, ⟨Ψ, hΨ⟩, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.large_Ree_full_inner_field_automorphism_normal_form a ha K hK
  obtain ⟨⟨x, σ⟩, hxσ, -⟩ := hNF β
  have hΨα : Ψ ⟨x, σ⟩ = β := by rw [hΨ x σ]; exact hxσ.symm
  let Θ : MulAut (ReeTag.F4.reeGamma K a) →* (K ≃+* K) :=
    SemidirectProduct.rightHom.comp Ψ.symm.toMonoidHom
  have hΘ : Θ β = σ := by
    show SemidirectProduct.rightHom (Ψ.symm β) = σ
    rw [← hΨα, MulEquiv.symm_apply_apply]
    rfl
  have hσp : σ ^ 3 = 1 := by rw [← hΘ, ← map_pow, hβ, map_one]
  have hone : ReeTag.F4.reeGammaFieldAut K a 1 = 1 := map_one (ReeTag.F4.reeGammaFieldAutHom K a)
  by_cases hσ1 : σ = 1
  · have hβx : β = MulAut.conj x := by
      rw [hxσ]
      change MulAut.conj x * ReeTag.F4.reeGammaFieldAut K a σ = _
      rw [hσ1, hone, mul_one]
    have hZ : Subgroup.center (ReeTag.F4.reeGamma K a) = ⊥ := ReeTag.large_Ree_fixed_group_center_trivial a K hK
    obtain ⟨y, hy, hyp, hy1⟩ :=
      CFSG.HardMathSupport.Dickson.SuzukiReeB.exists_eq_conj_of_mem_range hZ ⟨x, hβx.symm⟩ hβ hβ1
    have hyo : orderOf y = 3 := orderOf_eq_prime hyp hy1
    obtain ⟨eC⟩ := CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.centralizer_mulEquiv_unitarySU a K hK y hyo
    have hK' : Nat.card (GaloisField 2 (2 * (2 * a + 1))) = (2 ^ (2 * a + 1)) ^ 2 := by
      rw [GaloisField.card 2 _ (by omega), ← pow_mul, mul_comm]
    have hq := (CFSG.RankThree.PartTwo.Sec8.Item87Proof.isQuasisimple_statedSU_three
      (F := GaloisField 2 (2 * (2 * a + 1))) (f := 2 * a + 1) hK' (by omega)).1
    have hqC : CFSG.IsQuasisimple ↥(fixSubgroup β) := by
      rw [hy, CFSG.HardMathSupport.Dickson.SuzukiReeB.fixSubgroup_conj]
      exact CFSG.LocalCores.isQuasisimple_of_mulEquiv eC.symm hq
    exact structAt_of_isQuasisimple_fixSubgroup ⟨hqC.1.1, hqC.2.1⟩ hJ.1
  · have hσo : orderOf σ = 3 := orderOf_eq_prime hσp hσ1
    obtain ⟨g, hg⟩ := CFSG.RankThree.PartOne.RF4.largeRee_fieldAut_coset_conj a hK Nat.prime_three σ hσo β hβ
      ⟨x, hxσ⟩
    set φ : MulAut (ReeTag.F4.reeGamma K a) := MulAut.conj g with hφ
    have hc : MulAut.congr (φ⁻¹ : MulAut (ReeTag.F4.reeGamma K a)) β = ReeTag.F4.reeGammaFieldAut K a σ := by
      have e1 : MulAut.congr (φ⁻¹ : MulAut (ReeTag.F4.reeGamma K a)) β = φ⁻¹ * β * φ⁻¹⁻¹ := by
        ext y
        rfl
      rw [e1, hg]
      group
    refine structAt_of_congr (φ⁻¹ : MulAut (ReeTag.F4.reeGamma K a)) ?_
    have hJ' := glaPComponent_congr (φ⁻¹ : MulAut (ReeTag.F4.reeGamma K a)) hJ
    have hJ'7 : 7 ∣ Nat.card ↥(J.map (φ⁻¹ : MulAut (ReeTag.F4.reeGamma K a)).toMonoidHom) := by
      rw [Subgroup.card_map_of_injective (φ⁻¹ : MulAut (ReeTag.F4.reeGamma K a)).injective]
      exact hJ7
    rw [hc] at hJ' ⊢
    exact structAt_fieldAut_reeGamma hK σ hσo hJ' hJ'7

theorem input14_1StructFor_reeF4 : Input14_1StructFor fun d => ∃ m, d = TauCeti.LieTypeIndex.reeF4 m := by
  intro S _ _ _ _ d hd _ he β hβ3 hβ1 J hJ hJt
  obtain ⟨d, hv⟩ := d
  obtain ⟨m, rfl⟩ := hd
  obtain ⟨e0⟩ := he
  have hR := CFSG.HardMathSupport.Timmesfeld.DefChar.lot_reeTitsModel_twistedF4_of_index m hv e0
  obtain ⟨-, a, ha, -, K, _, _, _, hK, ⟨e⟩⟩ := CFSG.RankThree.PartTwo.Sec4.exists_mulEquiv_reeGamma hR
  have hJ7 : 7 ∣ Nat.card ↥(J.map e.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact (by norm_num : 7 ∣ 20160).trans (card_dvd_of_isLThreeFour hJt)
  refine structAt_of_congr e (structAt_reeGamma ha hK ?_ ?_ (glaPComponent_congr e hJ) hJ7)
  · rw [← map_pow, hβ3, map_one]
  · intro h
    exact hβ1 ((MulAut.congr e).injective (h.trans (map_one _).symm))

theorem input14_1StructFor_suzukiReeTits :
    Input14_1StructFor fun d =>
      CFSG.Yardstones.Md42047359a2a.lieFamily d = CFSG.Yardstones.Md42047359a2a.LieFamily.suzukiReeTits := by
  intro S _ _ hS hnc d hd hchar
  obtain ⟨d, hv⟩ := d
  cases d with
  | suzuki m => exact input14_1StructFor_suzuki S hS hnc ⟨_, hv⟩ ⟨m, rfl⟩ hchar
  | reeF4 m => exact input14_1StructFor_reeF4 S hS hnc ⟨_, hv⟩ ⟨m, rfl⟩ hchar
  | tits => exact input14_1StructFor_tits S hS hnc ⟨_, hv⟩ rfl hchar
  | reeG2 m =>
    exfalso
    have h3 : (TauCeti.LieTypeIndex.reeG2 m).characteristic = 3 := TauCeti.LieTypeIndex.characteristic_reeG2 m
    have h2 : (TauCeti.LieTypeIndex.reeG2 m).characteristic = 2 := hchar
    omega
  | _ => simp [CFSG.Yardstones.Md42047359a2a.lieFamily] at hd

theorem input14_1CoreCyc_of_rest
    (hU : Input14_1CoreFor fun d => ∃ r q, d = TauCeti.LieTypeIndex.twistedA r q)
    (hSO : Input14_1CoreFor fun d =>
      CFSG.Yardstones.Md42047359a2a.lieFamily d = CFSG.Yardstones.Md42047359a2a.LieFamily.symplecticOrthogonal)
    (hE : Input14_1CoreFor fun d =>
      CFSG.Yardstones.Md42047359a2a.lieFamily d = CFSG.Yardstones.Md42047359a2a.LieFamily.exceptional) :
    Inputs141.Input14_1CoreCyc := by
  refine input14_1CoreCyc_of_coreFamilies fun F => ?_
  cases F with
  | linearUnitary =>
    intro S _ _ hS hnc d hd
    obtain ⟨d, hv⟩ := d
    cases d with
    | A r q => exact input14_1CoreFor_of_struct input14_1StructFor_linear S hS hnc ⟨_, hv⟩ ⟨r, q, rfl⟩
    | twistedA r q => exact hU S hS hnc ⟨_, hv⟩ ⟨r, q, rfl⟩
    | _ => simp [CFSG.Yardstones.Md42047359a2a.lieFamily] at hd
  | symplecticOrthogonal => exact hSO
  | exceptional => exact hE
  | suzukiReeTits => exact input14_1CoreFor_of_struct input14_1StructFor_suzukiReeTits

end SuzukiReeTits

@[expose] def Input14_1CoreRest : Prop :=
  (Input14_1CoreFor fun d => ∃ r q, d = TauCeti.LieTypeIndex.twistedA r q) ∧
  (Input14_1CoreFor fun d =>
    CFSG.Yardstones.Md42047359a2a.lieFamily d = CFSG.Yardstones.Md42047359a2a.LieFamily.symplecticOrthogonal) ∧
  (Input14_1CoreFor fun d =>
    CFSG.Yardstones.Md42047359a2a.lieFamily d = CFSG.Yardstones.Md42047359a2a.LieFamily.exceptional)

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141c

end
