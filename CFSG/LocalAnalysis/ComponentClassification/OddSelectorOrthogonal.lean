module

public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorSymplectic
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmas
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalLowDimCoverage

public noncomputable section

namespace CFSG.ComponentClassification.OddSelector

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.OutcomeLocal

theorem map_mem_commutator_of_isPerfect {H G : Type*} [Group H] [Group G] [Group.IsPerfect H]
    (f : H →* G) (x : H) : f x ∈ commutator G := by
  have hle : (commutator H).map f ≤ commutator G := by
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  exact hle ⟨x, Group.IsPerfect.mem_commutator, rfl⟩

theorem isPerfect_statedSp {k : Type} [Field k] [Finite k] {r : ℕ} (hr : 2 ≤ r)
    (hodd : Odd (Nat.card k)) : Group.IsPerfect (StatedSp r k) := by
  have heq := CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic (n := r) (K := k)
  have hq := CatalogueBAlternatingIsometry.symplectic_quasisimple k r (by omega) hodd
    (Or.inl (by omega))
  have : Group.IsPerfect (TauCeti.GLSymplectic (Fin r) k) := hq.1
  exact Group.IsPerfect.ofSurjective (f := (MulEquiv.subgroupCongr heq.symm).toMonoidHom)
    (MulEquiv.subgroupCongr heq.symm).surjective

section Quadratic

variable {k : Type} [Field k] [Finite k] {V : Type} [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

theorem commutator_orthogonalGroup_quasisimple (hodd : Odd (Nat.card k))
    (Q : QuadraticForm k V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : 5 ≤ Module.finrank k V) :
    CFSG.IsQuasisimple (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)) := by
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  by_cases hT : ∃ T : Submodule k V, Module.finrank k T = 3 ∧ ∀ x ∈ T, Q x = 0
  · obtain ⟨T, hT3, hTQ⟩ := hT
    exact CatalogueBOrthogonal.derived_quasisimple Q h2 hQ hT3.ge hTQ
  · have hb := CatalogueBOddQuadratic.finrank_le_six_of_no_totallySingular_three hodd Q hQ hT
    have hcase : (Odd (Nat.card k) ∧ (Module.finrank k V = 3 ∨ Module.finrank k V = 4 ∨
          Module.finrank k V = 5)) ∨
        (Odd (Nat.card k) ∧ Module.finrank k V = 6 ∧
          ¬ ∃ T : Submodule k V, Module.finrank k T = 3 ∧ ∀ x ∈ T, Q x = 0) ∨
        (Module.finrank k V = 4 ∧
          ∃ S : Submodule k V, Module.finrank k S = 2 ∧ ∀ x ∈ S, Q x = 0) := by
      rcases (show Module.finrank k V = 5 ∨ Module.finrank k V = 6 by omega) with hd | hd
      · exact Or.inl ⟨hodd, Or.inr (Or.inr hd)⟩
      · exact Or.inr (Or.inl ⟨hodd, hd, hT⟩)
    obtain ⟨-, -, -, -, -, h5, h6⟩ :=
      orthogonal_low_dimensional_fixed_derived_component_coverage Q hQ hcase
    rcases (show Module.finrank k V = 5 ∨ Module.finrank k V = 6 by omega) with hd | hd
    · obtain ⟨-, -, -, -, -, -, hq⟩ := h5 hodd hd
      exact hq
    · obtain ⟨-, -, -, -, -, -, -, -, hq⟩ := h6 hodd hd hT
      exact hq

omit [Finite k] in
theorem exists_nondegenerate_five (h2 : (2 : k) ≠ 0) (Q : QuadraticForm k V)
    (hQ : Q.polarBilin.Nondegenerate) (hdim : 5 ≤ Module.finrank k V) :
    ∃ U W : Submodule k V, IsCompl U W ∧ (∀ u ∈ U, ∀ w ∈ W, QuadraticMap.polar Q u w = 0) ∧
      Module.finrank k U = 5 ∧ (Q.comp U.subtype).polarBilin.Nondegenerate := by
  classical
  let : Invertible (2 : k) := invertibleOfNonzero h2
  have hsymm : Q.polarBilin.IsSymm := ⟨fun x y => QuadraticMap.polar_comm Q x y⟩
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis hsymm
  set f : Fin 5 → Fin (Module.finrank k V) := Fin.castLE hdim with hf
  set s : Set (Fin (Module.finrank k V)) := Set.range f with hs
  set U := Submodule.span k (v '' s) with hU
  set W := Submodule.span k (v '' sᶜ) with hW
  have hUW : IsCompl U W := v.linearIndependent.isCompl_span_image v.span_eq isCompl_compl
  have hortho : ∀ i j, i ≠ j → QuadraticMap.polar Q (v i) (v j) = 0 := fun i j hij => hv hij
  have horth : ∀ u ∈ U, ∀ w ∈ W, QuadraticMap.polar Q u w = 0 := by
    intro u hu w hw
    have h1 : ∀ i ∈ s, QuadraticMap.polar Q (v i) w = 0 := by
      intro i hi
      have hle : W ≤ LinearMap.ker (Q.polarBilin (v i)) := by
        rw [hW, Submodule.span_le]
        rintro _ ⟨j, hj, rfl⟩
        rw [SetLike.mem_coe, LinearMap.mem_ker]
        exact hortho i j fun h => hj (h ▸ hi)
      exact LinearMap.mem_ker.mp (hle hw)
    have hle : U ≤ LinearMap.ker (Q.polarBilin.flip w) := by
      rw [hU, Submodule.span_le]
      rintro _ ⟨i, hi, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      exact h1 i hi
    exact LinearMap.mem_ker.mp (hle hu)
  have hfin : Module.finrank k U = 5 := by
    rw [hU, hs, ← Set.range_comp,
      finrank_span_eq_card (v.linearIndependent.comp f (Fin.castLE_injective hdim)),
      Fintype.card_fin]
  refine ⟨U, W, hUW, horth, hfin, ?_⟩
  have hrefl : (Q.comp U.subtype).polarBilin.IsRefl := fun x y hxy => by
    change QuadraticMap.polar (Q.comp U.subtype) y x = 0
    rw [QuadraticMap.polar_comm]
    exact hxy
  refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft hrefl).mpr fun x hx => ?_
  apply Subtype.ext
  apply hQ.1
  intro z
  obtain ⟨u, w, rfl⟩ := exists_add_of_isCompl hUW z
  have hxu : QuadraticMap.polar Q x u = 0 := hx u
  change QuadraticMap.polar Q x (u + w) = 0
  rw [QuadraticMap.polar_add_right, hxu, horth x x.2 w w.2, add_zero]

theorem exists_sp_four_hom (hodd : Odd (Nat.card k)) (Q : QuadraticForm k V)
    (hQ : Q.polarBilin.Nondegenerate) (hdim : 5 ≤ Module.finrank k V) :
    ∃ τ : StatedSp 2 k →* TauCeti.QuadraticMap.orthogonalGroup Q,
      ∀ x : StatedSp 2 k, (∀ y, τ y * τ x = τ x * τ y) → x ∈ center (StatedSp 2 k) := by
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  obtain ⟨U, W, hUW, horth, hU5, hQU⟩ := exists_nondegenerate_five h2 Q hQ hdim
  obtain ⟨-, -, e, -, -, -⟩ :=
    CatalogueBOrthogonalFive.finite_odd_five_selfAdjoint_form_similarity hodd
      (Q.comp U.subtype) hQU hU5
  obtain ⟨hinj5, hmem5, -, -⟩ := orthogonal_complement_elementary_embedding Q hUW horth
  set τ₅ : TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype) →*
      TauCeti.QuadraticMap.orthogonalGroup Q :=
    ((orthExtend hUW).comp (TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype)).subtype)
      |>.codRestrict _ (fun g => hmem5 g g.2) with hτ₅
  have hτ₅i : Function.Injective τ₅ := fun g h hgh =>
    Subtype.ext (hinj5 (congrArg Subtype.val hgh))
  set τ₃ := CatalogueBOrthogonalFive.selfAdjointSymplecticAction (K := k) h2 with hτ₃
  set ε : StatedSp 2 k ≃* (CatalogueBOrthogonalFive.symplecticMultiplier (K := k)).ker :=
    (MulEquiv.subgroupCongr
      (CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic (n := 2) (K := k))).trans
      CatalogueBOrthogonalFive.symplecticKernelEquiv.symm with hε
  set ι := τ₅.comp e.symm.toMonoidHom with hι
  have hιi : Function.Injective ι := hτ₅i.comp e.symm.injective
  refine ⟨(ι.comp τ₃).comp ε.toMonoidHom, fun x hx => ?_⟩
  have : Group.IsPerfect (CatalogueBOrthogonalFive.symplecticMultiplier (K := k)).ker :=
    (CatalogueBOrthogonalFive.symplecticKernel_quasisimple hodd).1
  have hc : τ₃.rangeRestrict (ε x) ∈ center τ₃.range := by
    rw [mem_center_iff]
    rintro ⟨_, z, rfl⟩
    obtain ⟨y, rfl⟩ := ε.surjective z
    apply Subtype.ext
    apply hιi
    have := hx y
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_mul,
      MonoidHom.coe_rangeRestrict, Subgroup.coe_mul] using this
  have hkerc : τ₃.rangeRestrict.ker ≤ center _ := by
    rw [MonoidHom.ker_rangeRestrict]
    exact CatalogueBOrthogonalFive.selfAdjointSymplecticAction_kernel_le_center h2
  have hz := mem_center_of_map_mem_center τ₃.rangeRestrict hkerc hc
  rw [mem_center_iff] at hz ⊢
  intro y
  apply ε.injective
  rw [map_mul, map_mul]
  exact hz (ε y)

end Quadratic

variable {k : Type} [Field k] [Finite k] {m : ℕ}

@[expose] def matrixOrthogonalEquiv (hk2 : ringChar k ≠ 2) (R : GL (Fin m) k)
    (hR : (R : Matrix (Fin m) (Fin m) k)ᵀ = R) :
    TauCeti.QuadraticMap.orthogonalGroup (CatalogueBLinearHigherB.matrixQuadraticForm R) ≃*
      CatalogueBGraphForm.isometryGroup m k R :=
  (MulEquiv.subgroupCongr
    (CatalogueBLinearHigherB.orthogonalGroup_matrixQuadraticForm hk2 R hR)).trans
    (CatalogueBLinearHigherB.isometryGroupEquiv R)

variable {A : Type} [Group A] {a : A} {L : Subgroup A}

theorem orthogonal_case_false {ℓ e : ℕ} (hm : 5 ≤ m) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hk : Nat.card k = ℓ ^ e) {ρ : A →* MulAut (projectiveSL m k)} (hinj : Function.Injective ρ)
    (hL₁ : CFSG.Assembly.IsComponentOf (L.map ρ)
      (OuterAutomorphisms.inner (projectiveSL m k) ⊓ centralizer {ρ a}))
    {B : GL (Fin m) k} (hρa : ρ a = conjAut m k B * dualAut m k)
    (hB : (B : Matrix (Fin m) (Fin m) k)ᵀ = B) {p f : ℕ} (hp2 : p ≠ 2)
    (hsrc : StatedClassicalModel (L ⧸ center L) .PSL 2 p f ∨
      Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)) ∨
      StatedClassicalModel (L ⧸ center L) .PSL 3 2 2) : False := by
  classical
  have : CharP k ℓ := finite_field_prime_power_characteristic hℓ he hk
  have hk2 : ringChar k ≠ 2 := by rw [ringChar.eq k ℓ]; exact hℓ2
  have hodd : Odd (Nat.card k) := by rw [hk]; exact (hℓ.odd_of_ne_two hℓ2).pow
  have hm3 : 3 ≤ m := by omega
  rw [hρa] at hL₁
  obtain ⟨hXh, hmap, -⟩ := graph_component_lift hm3 B hL₁
  set Xh := ⁅(L.map ρ).comap (conjAut m k), (L.map ρ).comap (conjAut m k)⁆ with hXhdef
  set R : GL (Fin m) k := B⁻¹ with hRdef
  set O := CatalogueBGraphForm.isometryGroup m k R with hOdef
  have hR : (R : Matrix (Fin m) (Fin m) k)ᵀ = R := by
    set Rm : Matrix (Fin m) (Fin m) k := (R : Matrix (Fin m) (Fin m) k) with hRm
    set Bm : Matrix (Fin m) (Fin m) k := (B : Matrix (Fin m) (Fin m) k) with hBm
    have hBR : Bm * Rm = 1 := by
      rw [hBm, hRm, hRdef, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc Rmᵀ = Rmᵀ * (Bm * Rm) := by rw [hBR, Matrix.mul_one]
      _ = (Bm * Rm)ᵀ * Rm := by rw [transpose_mul, hB, Matrix.mul_assoc]
      _ = Rm := by rw [hBR, transpose_one, Matrix.one_mul]
  set Q := CatalogueBLinearHigherB.matrixQuadraticForm R with hQdef
  have hQ : Q.polarBilin.Nondegenerate :=
    CatalogueBLinearHigherB.polarBilin_matrixQuadraticForm_nondegenerate hk2 R hR
  have hdim : 5 ≤ Module.finrank k (Fin m → k) := by rwa [Module.finrank_fin_fun]
  set eO := matrixOrthogonalEquiv hk2 R hR with heO
  have hcommO : (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)).map eO.toMonoidHom =
      commutator O := by
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ eO.surjective]
  have hqO : CFSG.IsQuasisimple (commutator O) := by
    have hq := commutator_orthogonalGroup_quasisimple hodd Q hQ hdim
    refine (isQuasisimple_congr (((commutator _).equivMapOfInjective eO.toMonoidHom
      eO.injective).trans (MulEquiv.subgroupCongr hcommO))).1 hq
  set D : Subgroup (GL (Fin m) k) := ⁅O, O⁆ with hDdef
  have hDmap : (commutator O).map O.subtype = D := Subgroup.map_subtype_commutator O
  have hqD : CFSG.IsQuasisimple D :=
    (isQuasisimple_congr (((commutator O).equivMapOfInjective O.subtype
      O.subtype_injective).trans (MulEquiv.subgroupCongr hDmap))).1 hqO
  have hXhD : Xh ≤ D := by
    have : Group.IsPerfect Xh := ⟨hXh.2.2.1⟩
    rw [← Subgroup.commutator_eq_self (H := Xh)]
    exact Subgroup.commutator_mono hXh.1 hXh.1
  have hDO : D ≤ O := by
    rw [← hDmap]
    exact Subgroup.map_subtype_le _
  have hXD : Xh = D := by
    have hc := isComponentOf_of_le hXh hXhD hDO
    have hcomp := (isComponentOf_iff_isComponent_subgroupOf hXhD).mp hc
    have htop := eq_top_of_isComponent_quasisimple hqD hcomp
    exact le_antisymm hXhD fun x hx => by
      have : (⟨x, hx⟩ : D) ∈ Xh.subgroupOf D := htop ▸ mem_top _
      exact this
  obtain ⟨τ, hτ⟩ := exists_sp_four_hom hodd Q hQ hdim
  set ι : StatedSp 2 k →* O := eO.toMonoidHom.comp τ with hι
  have : Group.IsPerfect (StatedSp 2 k) := isPerfect_statedSp le_rfl hodd
  have hιD : ∀ x, (ι x : GL (Fin m) k) ∈ Xh := by
    intro x
    rw [hXD, ← hDmap]
    exact ⟨ι x, map_mem_commutator_of_isPerfect ι x, rfl⟩
  have hσL : ∀ x : StatedSp 2 k, conjAut m k (ι x : GL (Fin m) k) ∈ L.map ρ := by
    intro x
    rw [← hmap]
    exact ⟨ι x, hιD x, rfl⟩
  set σ : StatedSp 2 k →* L := (L.equivMapOfInjective ρ hinj).symm.toMonoidHom.comp
    (((conjAut m k).comp (O.subtype.comp ι)).codRestrict (L.map ρ) hσL) with hσ
  have hker : σ.ker ≤ center (StatedSp 2 k) := by
    intro x hx
    have h1 : conjAut m k (ι x : GL (Fin m) k) = 1 := by
      have : (L.equivMapOfInjective ρ hinj).symm
          ((((conjAut m k).comp (O.subtype.comp ι)).codRestrict (L.map ρ) hσL) x) = 1 := hx
      rw [MulEquiv.map_eq_one_iff] at this
      exact congrArg Subtype.val this
    have h2 := ker_conjAut_le_center hm3 h1
    refine hτ x fun y => eO.injective ?_
    have h3 := mem_center_iff.mp h2 (ι y : GL (Fin m) k)
    rw [map_mul, map_mul]
    exact Subtype.ext h3
  exact false_of_not_small_source
    (not_small_source_of_sp_cover le_rfl hℓ hℓ2 he hk σ hker) hp2 hsrc

end CFSG.ComponentClassification.OddSelector
