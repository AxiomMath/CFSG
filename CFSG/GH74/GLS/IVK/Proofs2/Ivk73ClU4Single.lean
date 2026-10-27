module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73ClU4Glue

public noncomputable section

namespace CFSG.GH74.GLS.IVK

open Subgroup Module Matrix CFSG.ComponentClassification.RestrictedStd
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.OddClassSelector
open CFSG.LocalAnalysis.ComponentInitial.CentralQuotientLift
open CFSG.ComponentClassification.CatalogueBUnitaryIsometry
open CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.CatalogueBUnitaryB


section FieldPart

variable {p f : ℕ} {K : Type} [Field K]


theorem ringEquiv_mul_comm (h : UnitaryFieldData p f K) (σ τ : K ≃+* K) : σ * τ = τ * σ := by
  classical
  obtain ⟨φ, -, -, hzp, hcard, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality h.prime (by have := h.one_le; omega) h.card
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcard]; have := h.one_le; omega)
  have : Fintype (K ≃+* K) := Fintype.ofFinite _
  have : IsCyclic (K ≃+* K) := ⟨⟨φ, fun x =>
    Subgroup.mem_zpowers_iff.mp (by rw [hzp]; exact Subgroup.mem_top x)⟩⟩
  let _ := IsCyclic.commGroup (α := K ≃+* K)
  exact mul_comm σ τ

@[expose] def fieldPart (h : UnitaryFieldData p f K) {r ε : ℕ} (hr : 1 ≤ r) (hε : ε ≤ 1) (hn : 3 ≤ 2 * r + ε)
    (hp : p ≠ 2) : MulAut (hypPSU h r ε) →* (K ≃+* K) :=
  MonoidHom.liftOfRightInverse (semilinearAutHom h hr hε)
    (Function.surjInv (semilinearAutHom_surjective h hr hε hp hn))
    (Function.rightInverse_surjInv (semilinearAutHom_surjective h hr hε hp hn))
    ⟨(SemidirectProduct.rightHom : SemiGL (HypIndex r ε) K →* (K ≃+* K)).comp
      (semilinearSimilitudes h r ε).subtype, by
      intro x hx
      exact ((semilinearAutHom_eq_one_iff h hr hε hn x).mp hx).1⟩

theorem fieldPart_apply (h : UnitaryFieldData p f K) {r ε : ℕ} (hr : 1 ≤ r) (hε : ε ≤ 1)
    (hn : 3 ≤ 2 * r + ε) (hp : p ≠ 2) (x : semilinearSimilitudes h r ε) :
    fieldPart h hr hε hn hp (semilinearAutHom h hr hε x) = (x : SemiGL (HypIndex r ε) K).right := by
  unfold fieldPart
  exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x

theorem su4_rep_linear_of_commutator (hud : UnitaryFieldData p f K) (hp : p ≠ 2)
    (α : MulAut (hypPSU hud 2 0)) (hα : orderOf α = 2)
    (hc : α ∈ ⁅(⊤ : Subgroup (MulAut (hypPSU hud 2 0))), (⊤ : Subgroup (MulAut (hypPSU hud 2 0)))⁆) :
    ∃ (A : GL (HypIndex 2 0) K) (hA : A ∈ hypUnitary hud 2 0)
      (hx : (⟨A, RingEquiv.refl K⟩ : SemiGL (HypIndex 2 0) K) ∈ semilinearSimilitudes hud 2 0),
      semilinearAutHom hud (r := 2) (ε := 0) (by norm_num) (by norm_num) ⟨_, hx⟩ = α ∧
      orderOf (QuotientGroup.mk ⟨A, hA⟩ : hypUnitaryMod hud 2 0) = 2 := by
  rcases su4_rep hud hp α hα with h1 | ⟨A, σ, hσ, hA, hx, c, hc0, hΦ, hAc⟩
  · exact h1
  · exfalso
    have hker : fieldPart hud (r := 2) (ε := 0) (by norm_num) (by norm_num) (by norm_num) hp α = 1 := by
      have : ⁅(⊤ : Subgroup (MulAut (hypPSU hud 2 0))), (⊤ : Subgroup (MulAut (hypPSU hud 2 0)))⁆ ≤
          (fieldPart hud (r := 2) (ε := 0) (by norm_num) (by norm_num) (by norm_num) hp).ker := by
        rw [Subgroup.commutator_le]
        intro g _ g' _
        rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact ringEquiv_mul_comm hud _ _
      exact this hc
    have h2 := fieldPart_apply hud (r := 2) (ε := 0) (by norm_num) (by norm_num) (by norm_num) hp ⟨_, hx⟩
    rw [hΦ, hker] at h2
    obtain ⟨c₀, hc₀⟩ := hud.exists_bar_ne
    have h3 := RingEquiv.congr_fun h2 c₀
    change c₀ = σ c₀ at h3
    exact hc₀ (by rw [← hσ c₀, ← h3])


end FieldPart

section Paired

variable {p f : ℕ} {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V]
  [FiniteDimensional E V]


theorem su4_linear_paired_sl (h : UnitaryFieldData p f E) (hp : p ≠ 2) (hn : finrank E V = 4)
    {B : V →ₛₗ[h.bar] V →ₗ[E] E} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    {T : sesqUnitaryGroup B} (hT : orderOf (QuotientGroup.mk T : sesqProjUnitary h B) = 2)
    {Y : Subgroup (sesqUnitaryGroup B)}
    (hY : CFSG.Assembly.IsComponentOf Y (centralizer ({T} : Set (sesqUnitaryGroup B))))
    {X' : Type} [Group X'] {X : Subgroup X'} (σ : Y →* X) (hσs : Function.Surjective σ)
    (hσk : σ.ker ≤ center Y)
    (hker : ∀ y : Y, σ y = 1 → (y : sesqUnitaryGroup B) ∈ sesqNormOneScalars h B)
    (hs : SmallSource X) :
    ∃ (P : PairedSL h B Y) (τ : Matrix.SpecialLinearGroup (Fin 2) E ≃* Y), P.T = T ∧
      ∀ (g : Matrix.SpecialLinearGroup (Fin 2) E) (u : Fin 2 → E),
        P.vec ((g : Matrix (Fin 2) (Fin 2) E) *ᵥ u) = unitaryOp (τ g : sesqUnitaryGroup B) (P.vec u) := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.finite
  obtain ⟨l, hl0, hAA, hN, hP, hM, hc, hsplit, hpaired, -⟩ :=
    projective_unitary_involution_centralizer_matrix_structure h hp (by omega) hB hBl hT
  have hY₁ := (isComponentOf_iff_isComponent_subgroupOf hY.1).mp hY
  let eY : Y.subgroupOf (centralizer ({T} : Set (sesqUnitaryGroup B))) ≃* Y :=
    Subgroup.subgroupOfEquivOfLe hY.1
  rcases hN with hN | hN
  ·
    exfalso
    have hσ₁k := ker_comp_le_center eY.toMonoidHom eY.injective σ hσk
    obtain ⟨-, hsepP, hsepM, e, he⟩ := hsplit hN
    have hsymm : ∀ P : Submodule E V, (B.domRestrict₁₂ P P).IsSymm := fun P =>
      ⟨fun x y => hB.eq (x : V) (y : V)⟩
    rcases fst_eq_or_snd_eq_of_isComponent_prod (isComponent_map_of_isComponent e hY₁) with
      h2 | h1
    · have h2' : ∀ x ∈ Y.subgroupOf (centralizer ({T} : Set (sesqUnitaryGroup B))),
          (e x).2 = 1 := fun x hx => h2 _ (mem_map_of_mem _ hx)
      obtain ⟨ρ₁, hρ₁i, hρ₁c, -⟩ := restrict_component e hY₁ h2'
      have hYF : ∀ y ∈ Y, ∀ w ∈ eigenMinus l (unitaryOp T), unitaryOp y w = w := by
        intro y hy w hw
        have h4 := LinearMap.congr_fun (he (eY.symm ⟨y, hy⟩)).2 ⟨w, hw⟩
        rw [h2' _ (eY.symm ⟨y, hy⟩).2] at h4
        exact h4.symm
      refine su_half_false h hp (hsymm _) hsepP (Submodule.one_le_finrank_iff.mpr hP) hM hYF
        (ρ₁.comp eY.symm.toMonoidHom) (hρ₁i.comp eY.symm.injective) ?_ σ hσs hσk hker hs
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eY.symm.surjective,
        ← MonoidHom.range_eq_map]
      exact hρ₁c
    · have h1' : ∀ x ∈ Y.subgroupOf (centralizer ({T} : Set (sesqUnitaryGroup B))),
          ((e.trans MulEquiv.prodComm) x).2 = 1 := fun x hx => h1 _ (mem_map_of_mem _ hx)
      obtain ⟨ρ₁, hρ₁i, hρ₁c, -⟩ := restrict_component (e.trans MulEquiv.prodComm) hY₁ h1'
      have hYF : ∀ y ∈ Y, ∀ w ∈ eigenPlus l (unitaryOp T), unitaryOp y w = w := by
        intro y hy w hw
        have h4 := LinearMap.congr_fun (he (eY.symm ⟨y, hy⟩)).1 ⟨w, hw⟩
        rw [show (e (eY.symm ⟨y, hy⟩)).1 = 1 from h1' _ (eY.symm ⟨y, hy⟩).2] at h4
        exact h4.symm
      refine su_half_false h hp (hsymm _) hsepM (Submodule.one_le_finrank_iff.mpr hM) hP hYF
        (ρ₁.comp eY.symm.toMonoidHom) (hρ₁i.comp eY.symm.injective) ?_ σ hσs hσk hker hs
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eY.symm.surjective,
        ← MonoidHom.range_eq_map]
      exact hρ₁c
  ·
    obtain ⟨hisoP, -, -, hdim2, -, hpairM, e, hecompat, -, -⟩ := hpaired hN
    have hfin2 : finrank E (eigenPlus l (unitaryOp T)) = 2 := by omega
    let bP : Basis (Fin 2) E (eigenPlus l (unitaryOp T)) := Module.finBasisOfFinrankEq E _ hfin2
    let e' : centralizer ({T} : Set (sesqUnitaryGroup B)) ≃* Matrix.GeneralLinearGroup (Fin 2) E :=
      e.trans (Units.mapEquiv (LinearMap.toMatrixAlgEquiv bP).toMulEquiv)
    have hL' := isComponent_map_of_isComponent e' hY₁
    have : Group.IsPerfect ((Y.subgroupOf (centralizer ({T} : Set (sesqUnitaryGroup B)))).map
        e'.toMonoidHom) := hL'.1.1
    have : Nontrivial ((Y.subgroupOf (centralizer ({T} : Set (sesqUnitaryGroup B)))).map
        e'.toMonoidHom) := CFSG.LocalCores.isQuasisimple_nontrivial hL'.1
    have hcard : Nat.card E = p ^ (2 * f) := h.card
    have hp3 : 3 ≤ p := by
      have := h.prime.two_le
      omega
    have hq : 9 ≤ Nat.card E := by
      rw [hcard]
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
        _ ≤ p ^ (2 * f) := Nat.pow_le_pow_right h.prime.pos (by have := h.one_le; omega)
    have hSL : (Y.subgroupOf (centralizer ({T} : Set (sesqUnitaryGroup B)))).map e'.toMonoidHom =
        CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinearRange 2 E :=
      CFSG.ComponentClassification.CatalogueBGeneralLinear.perfect_subnormal_eq_specialLinearRange
        2 E (by norm_num) (Or.inr (by omega)) (Or.inr (by omega)) _ hL'.2
    let ι₀ : Y →* Matrix.GeneralLinearGroup (Fin 2) E :=
      e'.toMonoidHom.comp (Subgroup.inclusion hY.1)
    have hι₀ : ∀ y : Y, ι₀ y ∈ CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinearRange 2 E := by
      intro y
      rw [← hSL]
      exact ⟨⟨y, hY.1 y.2⟩, Subgroup.mem_subgroupOf.mpr y.2, rfl⟩
    let ι : Y →* Matrix.SpecialLinearGroup (Fin 2) E :=
      ((CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinearEquivRange 2 E).symm.toMonoidHom).comp
        (ι₀.codRestrict _ hι₀)
    have hιval : ∀ y : Y, Matrix.SpecialLinearGroup.toGL (ι y) = ι₀ y := by
      intro y
      have := CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinearEquivRange_val 2 E
        ((CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinearEquivRange 2 E).symm
          ⟨ι₀ y, hι₀ y⟩)
      rw [MulEquiv.apply_symm_apply] at this
      exact this.symm
    have hιinj : Function.Injective ι := by
      intro y y' hyy
      have h1 : ι₀ y = ι₀ y' := by rw [← hιval, ← hιval, hyy]
      have h2 := e'.injective h1
      have h3 : (y : sesqUnitaryGroup B) = (y' : sesqUnitaryGroup B) :=
        congrArg (fun z : centralizer ({T} : Set (sesqUnitaryGroup B)) => (z : sesqUnitaryGroup B)) h2
      exact Subtype.ext h3
    have hιsurj : Function.Surjective ι := by
      intro g
      have h1 : Matrix.SpecialLinearGroup.toGL g ∈
          (Y.subgroupOf (centralizer ({T} : Set (sesqUnitaryGroup B)))).map e'.toMonoidHom := by
        rw [hSL]
        exact ⟨g, rfl⟩
      obtain ⟨x, hx, hxg⟩ := h1
      refine ⟨⟨(x : sesqUnitaryGroup B), Subgroup.mem_subgroupOf.mp hx⟩, ?_⟩
      apply Matrix.SpecialLinearGroup.toGL_injective
      rw [hιval]
      exact hxg
    let τ : Matrix.SpecialLinearGroup (Fin 2) E ≃* Y := (MulEquiv.ofBijective ι ⟨hιinj, hιsurj⟩).symm
    have hrel : ∀ (g₀ : Matrix.SpecialLinearGroup (Fin 2) E) (u : Fin 2 → E),
        ((bP.equivFun.symm ((g₀ : Matrix (Fin 2) (Fin 2) E) *ᵥ u) : eigenPlus l (unitaryOp T)) : V) =
          unitaryOp (τ g₀ : sesqUnitaryGroup B) ((bP.equivFun.symm u : eigenPlus l (unitaryOp T)) : V) := by
      intro g₀ u
      set y : Y := τ g₀ with hy
      have hιy : ι y = g₀ := by
        rw [hy]
        exact (MulEquiv.ofBijective ι ⟨hιinj, hιsurj⟩).apply_symm_apply g₀
      set x : centralizer ({T} : Set (sesqUnitaryGroup B)) := ⟨(y : sesqUnitaryGroup B), hY.1 y.2⟩ with hx
      have hxg : e' x = Matrix.SpecialLinearGroup.toGL g₀ := by
        rw [← hιy, hιval]
        rfl
      have hmat : LinearMap.toMatrix bP bP
          (((e x : LinearMap.GeneralLinearGroup E (eigenPlus l (unitaryOp T))) :
            Module.End E (eigenPlus l (unitaryOp T)))) = (g₀ : Matrix (Fin 2) (Fin 2) E) := by
        have := congrArg (fun z : Matrix.GeneralLinearGroup (Fin 2) E => (z : Matrix (Fin 2) (Fin 2) E)) hxg
        exact this
      have hrepr : ∀ v : eigenPlus l (unitaryOp T),
          bP.equivFun (((e x : LinearMap.GeneralLinearGroup E (eigenPlus l (unitaryOp T))) :
            Module.End E (eigenPlus l (unitaryOp T))) v) =
            (g₀ : Matrix (Fin 2) (Fin 2) E) *ᵥ bP.equivFun v := by
        intro v
        rw [Basis.equivFun_apply, Basis.equivFun_apply, ← hmat]
        exact (LinearMap.toMatrix_mulVec_repr bP bP _ v).symm
      have h2 : ((e x : LinearMap.GeneralLinearGroup E (eigenPlus l (unitaryOp T))) :
          Module.End E (eigenPlus l (unitaryOp T))) (bP.equivFun.symm u) =
            bP.equivFun.symm ((g₀ : Matrix (Fin 2) (Fin 2) E) *ᵥ u) := by
        apply bP.equivFun.injective
        rw [hrepr, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
      have h3 := LinearMap.congr_fun (hecompat x) (bP.equivFun.symm u)
      rw [LinearMap.comp_apply, LinearMap.comp_apply, h2] at h3
      exact h3
    refine ⟨{
      T := T
      l := l
      l_ne := hl0
      norm_l := hN
      Vp := eigenPlus l (unitaryOp T)
      Vm := eigenMinus l (unitaryOp T)
      isCompl := hc
      Vm_ne := hM
      T_p := fun v hv => (mem_eigenPlus_iff' hl0).1 hv
      T_m := fun v hv => (mem_eigenMinus_iff' hl0).1 hv
      iso_p := hisoP
      pair_m := hpairM
      cp := bP.equivFun
      surj := fun g₀ => ⟨(τ g₀ : sesqUnitaryGroup B), (τ g₀).2, hrel g₀⟩ }, τ, rfl, hrel⟩


end Paired

section Levels

variable {p f : ℕ} {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V]
  [FiniteDimensional E V]

section DLevel

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.OddClassSelector (map_conj_eq_of_le_center onQuotient_conj)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

omit [FiniteDimensional E V] in
theorem tau_mem_scalars_iff (h : UnitaryFieldData p f E) (hp : p ≠ 2)
    {B : V →ₛₗ[h.bar] V →ₗ[E] E} {T : sesqUnitaryGroup B} {Y : Subgroup (sesqUnitaryGroup B)}
    (hYT : Y ≤ centralizer ({T} : Set (sesqUnitaryGroup B)))
    (P : PairedSL h B Y) (hPT : P.T = T) (τ : Matrix.SpecialLinearGroup (Fin 2) E ≃* Y)
    (hrel : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) E) (u : Fin 2 → E),
      P.vec ((g : Matrix (Fin 2) (Fin 2) E) *ᵥ u) = unitaryOp (τ g : sesqUnitaryGroup B) (P.vec u))
    (g : Matrix.SpecialLinearGroup (Fin 2) E) :
    (τ g : sesqUnitaryGroup B) ∈ sesqNormOneScalars h B ↔ g ∈ scalars 2 E := by
  have h2 := two_ne_zero_of_odd h hp
  constructor
  · rintro ⟨c, hc, hyc⟩
    have hc0 : c ≠ 0 := ne_zero_of_norm_eq_one h hc
    have hmul : ∀ u : Fin 2 → E, (g : Matrix (Fin 2) (Fin 2) E) *ᵥ u = c • u := by
      intro u
      apply P.vec_injective
      rw [hrel g u, P.vec_smul]
      have := LinearMap.congr_fun hyc (P.vec u)
      simpa using this
    have hgc : (g : Matrix (Fin 2) (Fin 2) E) = Matrix.scalar (Fin 2) c := by
      refine Matrix.ext_iff_mulVec.mpr fun u => ?_
      rw [hmul]
      funext i
      simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
    have hdet : c * c = 1 := by
      have h1 := g.2
      rw [hgc, Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_two] at h1
      exact h1
    refine ⟨Units.mk0 c hc0, ?_, hgc⟩
    ext
    simpa [pow_two] using hdet
  · rintro ⟨c, hc2, hgc⟩
    have hmul : ∀ u : Fin 2 → E, (g : Matrix (Fin 2) (Fin 2) E) *ᵥ u = (c : E) • u := by
      intro u
      rw [hgc]
      funext i
      simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
    have hcc : (c : E) * c = 1 := by
      have := congrArg (fun z : Eˣ => (z : E)) hc2
      simpa [pow_two] using this
    have hbar : h.bar (c : E) = c := by
      rcases mul_self_eq_one_iff.mp hcc with h1 | h1
      · rw [h1, map_one]
      · rw [h1, map_neg, map_one]
    set y : sesqUnitaryGroup B := (τ g : sesqUnitaryGroup B) with hy
    have hyP : ∀ v ∈ P.Vp, unitaryOp y v = (c : E) • v := by
      intro v hv
      obtain ⟨u, rfl⟩ := P.exists_vec hv
      rw [← hrel g u, hmul u, P.vec_smul]
    have hcomm : ∀ v, unitaryOp y (unitaryOp P.T v) = unitaryOp P.T (unitaryOp y v) := by
      intro v
      have hyc : (y : sesqUnitaryGroup B) ∈ centralizer ({T} : Set (sesqUnitaryGroup B)) := hYT (τ g).2
      have := Subgroup.mem_centralizer_singleton_iff.mp hyc
      rw [hPT]
      exact LinearMap.congr_fun (congrArg unitaryOp this) v
    have hSY : ∀ y' ∈ Y, ∀ v, unitaryOp y (unitaryOp y' v) = unitaryOp y' (unitaryOp y v) := by
      intro y' hy' v
      obtain ⟨g', hg'⟩ := τ.surjective ⟨y', hy'⟩
      have hy'eq : y' = (τ g' : sesqUnitaryGroup B) := congrArg Subtype.val hg'.symm
      rw [hy'eq]
      have hgg : g * g' = g' * g := by
        apply Subtype.ext
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hgc]
        exact (Matrix.scalar_commute (c : E) (fun r => Commute.all _ _) _).eq
      have h1 : (τ g : sesqUnitaryGroup B) * (τ g' : sesqUnitaryGroup B) =
          (τ g' : sesqUnitaryGroup B) * (τ g : sesqUnitaryGroup B) := by
        have := congrArg (fun z => (τ z : sesqUnitaryGroup B)) hgg
        simpa [map_mul] using this
      exact LinearMap.congr_fun (congrArg unitaryOp h1) v
    obtain ⟨c', hc'0, hc'P, hc'M⟩ := P.keep_diag h2 hSY hcomm
    obtain ⟨v₀, hv₀, hv₀0⟩ := P.exists_ne_zero
    have hcc' : c' = (c : E) := by
      have h1 := hc'P v₀ hv₀
      rw [hyP v₀ hv₀] at h1
      exact (smul_left_injective E hv₀0 h1).symm
    refine ⟨c, ?_, ?_⟩
    · rw [UnitaryFieldData.norm, hbar]
      exact hcc
    · refine LinearMap.ext fun v => ?_
      obtain ⟨a, ha, b, hb, rfl⟩ := P.decomp v
      rw [map_add, hyP a ha, hc'M b hb, hcc', hbar, inv_eq_of_mul_eq_one_right hcc, LinearMap.smul_apply,
        Module.End.one_apply, smul_add]

end DLevel

section DLevel2

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.OddClassSelector (map_conj_eq_of_le_center onQuotient_conj)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBUnitaryB

theorem su4_single_D (h : UnitaryFieldData p f E) (hp : p ≠ 2)
    (hn : finrank E V = 4) {B : V →ₛₗ[h.bar] V →ₗ[E] E} [Finite (sesqUnitaryGroup B)]
    (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    {X₂ : Subgroup (sesqProjUnitary h B)} (hs : SmallSource X₂)
    {T : sesqUnitaryGroup B} (hT : orderOf (QuotientGroup.mk T : sesqProjUnitary h B) = 2)
    (hXT : CFSG.Assembly.IsComponentOf X₂
      (fixedSubgroup (MulAut.conj (QuotientGroup.mk' (sesqNormOneScalars h B) T)))) :
    Nonempty (X₂ ≃* projectiveSL 2 E) := by
  classical
  have hZc := sesqNormOneScalars_le_center h B
  have hTT : T * T ∈ sesqNormOneScalars h B := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, ← pow_two, ← hT, pow_orderOf_eq_one]
  have hφφ : ∀ g, MulAut.conj T (MulAut.conj T g) = g := by
    intro g
    rw [MulAut.conj_apply, MulAut.conj_apply]
    have h1 := mem_center_iff.mp (hZc hTT) g
    calc T * (T * g * T⁻¹) * T⁻¹ = (T * T) * g * (T * T)⁻¹ := by group
      _ = g := by rw [← h1, mul_inv_cancel_right]
  have hφZT := map_conj_eq_of_le_center hZc T
  rw [← onQuotient_conj T hφZT] at hXT
  obtain ⟨hYT, hYm, -⟩ := liftY_data (MulAut.conj T) hφZT hφφ hXT
  rw [fixedSubgroup_conj] at hYT
  obtain ⟨P, τ, hPT, hrel⟩ := su4_linear_paired_sl h hp hn hB hBl hT hYT (liftHom X₂ hYm)
    (liftHom_surjective X₂ hYm) (liftHom_ker_le_center X₂ hYm) (liftHom_ker_le_scalars X₂ hYm) hs
  have hker : ∀ g : Matrix.SpecialLinearGroup (Fin 2) E,
      τ g ∈ (liftHom X₂ hYm).ker ↔ g ∈ scalars 2 E := by
    intro g
    rw [MonoidHom.mem_ker, ← tau_mem_scalars_iff h hp hYT.1 P hPT τ hrel g]
    constructor
    · intro h1
      exact liftHom_ker_le_scalars X₂ hYm _ h1
    · intro h1
      apply Subtype.ext
      change QuotientGroup.mk' (sesqNormOneScalars h B) ((τ g : liftY X₂) : sesqUnitaryGroup B) = 1
      exact (QuotientGroup.eq_one_iff _).mpr h1
  have hmap : (liftHom X₂ hYm).ker.map τ.symm.toMonoidHom = scalars 2 E := by
    ext g
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm]
    exact hker g
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective _ (liftHom_surjective X₂ hYm)).symm.trans
    (QuotientGroup.congr _ _ τ.symm hmap)⟩

end DLevel2


end Levels

section PLevelWrap

variable {p f : ℕ}

section PLevel

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.CatalogueBUnitaryB
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem su4_single_P {K : Type} [Field K] (hud : UnitaryFieldData p f K) (hp : p ≠ 2)
    {X : Subgroup (hypPSU hud 2 0)} (hs : SmallSource X) {α : MulAut (hypPSU hud 2 0)}
    (hα : orderOf α = 2)
    (hc : α ∈ ⁅(⊤ : Subgroup (MulAut (hypPSU hud 2 0))), (⊤ : Subgroup (MulAut (hypPSU hud 2 0)))⁆)
    (hXα : CFSG.Assembly.IsComponentOf X (fixedSubgroup α)) :
    Nonempty (X ≃* projectiveSL 2 K) := by
  classical
  have : Fact p.Prime := ⟨hud.prime⟩
  have := hud.finite
  obtain ⟨A, hA, hx, hΦ, hid⟩ := su4_rep_linear_of_commutator hud hp α hα hc
  set T := hypUnitaryEquiv hud ⟨A, hA⟩ with hTdef
  have hT : orderOf (QuotientGroup.mk T : sesqProjUnitary hud (hypForm hud 2 0)) = 2 := by
    rw [hTdef, ← hypUnitaryModEquiv_mk, MulEquiv.orderOf_eq]
    exact hid
  have heα := linear_intertwine hud (by norm_num) (by norm_num) A hA hx α hΦ
  have hXT := key_component hud 2 0 α _ heα hXα
  have hs₂ : SmallSource (X.map (hypIota hud 2 0)) :=
    smallSource_of_mulEquiv (X.equivMapOfInjective (hypIota hud 2 0)
      (hypIota_injective hud 2 0)) hs
  obtain ⟨e₁⟩ := su4_single_D (V := HypIndex 2 0 → K) hud hp (by rw [UnitaryHigher.finrank_hypIndex_fun])
    (hypForm_isSymm hud) (hypForm_separatingLeft hud) hs₂ hT hXT
  exact ⟨(X.equivMapOfInjective (hypIota hud 2 0) (hypIota_injective hud 2 0)).trans e₁⟩

end PLevel

end PLevelWrap

section Socle

open CFSG CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.OddClassSelector

theorem su4_single_rowS {A : Type} [Group A] [Finite A] {W : Subgroup A} [W.Normal]
    (hWs : IsSimpleGroup W) (hWnab : ∃ x y : W, x * y ≠ y * x)
    (hCW : centralizer (W : Set A) = ⊥) {a : A} (ha : orderOf a = 2)
    (hcomm : a ∈ ⁅(⊤ : Subgroup A), (⊤ : Subgroup A)⁆) {L : Subgroup A}
    (hLa : CFSG.Assembly.IsComponentOf L (W ⊓ centralizer {a})) (hs : SmallSource L)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 2) (e : W ≃* StatedProj (StatedSU 4 (p ^ f) K)) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E), Nat.card E = (p ^ f) ^ 2 ∧
      Nonempty (L ≃* projectiveSL 2 E) := by
  classical
  have hud : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨R, hR⟩ := (unitary_hyperbolic_model_transport hud (r := 2) (ε := 0) (by norm_num)
    (by norm_num)).1
  let θ : W ≃* hypPSU hud 2 0 := (e.trans (unitaryPSUEquiv hud (by norm_num)).symm).trans
    (hypProjTransport hud (R := R) hR).symm
  have : IsSimpleGroup (hypPSU hud 2 0) := θ.symm.isSimpleGroup
  have hnab : ∃ x y : hypPSU hud 2 0, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hWnab
    refine ⟨θ x, θ y, fun h => hxy (θ.injective ?_)⟩
    rw [map_mul, map_mul, h]
  have hZ := CFSG.ComponentClassification.OutcomeLocal.center_eq_bot_of_isSimpleGroup hnab
  have hcj := conj_injective hZ
  obtain ⟨ρ, hinj, hρW, -, -⟩ :=
    CFSG.ComponentClassification.OutcomeLocal.socle_extension hCW θ hZ
  obtain ⟨hWimg, hCWimg, -⟩ :=
    CFSG.ComponentClassification.OutcomeLocal.socle_images hinj θ hρW a
  have hL₁ := CFSG.ComponentClassification.SymmetricLocal.isComponentOf_map_of_injective ρ hinj hLa
  rw [hCWimg] at hL₁
  obtain ⟨hX, hXmap⟩ := isComponentOf_comap_conj hcj hL₁
  let eLX : L ≃* ((L.map ρ).comap MulAut.conj) :=
    (L.equivMapOfInjective ρ hinj).trans ((MulEquiv.subgroupCongr hXmap.symm).trans
      (((L.map ρ).comap MulAut.conj).equivMapOfInjective _ hcj).symm)
  have hsX := smallSource_of_mulEquiv eLX hs
  have hα : orderOf (ρ a) = 2 := (orderOf_injective ρ hinj a).trans ha
  have hc : ρ a ∈ ⁅(⊤ : Subgroup (MulAut (hypPSU hud 2 0))),
      (⊤ : Subgroup (MulAut (hypPSU hud 2 0)))⁆ := by
    have h1 : ρ a ∈ (⁅(⊤ : Subgroup A), (⊤ : Subgroup A)⁆).map ρ := Subgroup.mem_map_of_mem ρ hcomm
    rw [Subgroup.map_commutator] at h1
    exact Subgroup.commutator_mono le_top le_top h1
  obtain ⟨e₁⟩ := su4_single_P hud hp2 hsX hα hc hX
  exact ⟨K, inferInstance, inferInstance, hK, ⟨eLX.trans e₁⟩⟩

end Socle

end CFSG.GH74.GLS.IVK
