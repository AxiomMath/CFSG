module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OILa
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4EForms
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4EType
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitGeneral

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.C3

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OddSelector CFSG.ComponentClassification.CatFactsL4U4
open CFSG.ComponentClassification.CatFactsL4U4.OutInv

section Commute

variable {X : Type*} [Group X] {φ γ : MulAut X}

theorem apply_mem_fixSub (h : γ * φ = φ * γ) {y : X} (hy : y ∈ fixSub φ) : γ y ∈ fixSub φ := by
  rw [mem_fixSub] at hy ⊢
  have h1 := congrArg (fun f : MulAut X => f y) h
  simp only [MulAut.mul_apply, hy] at h1
  exact h1.symm

theorem isComponent_map_of_commute (h : γ * φ = φ * γ) {R : Subgroup X} (hRφ : R ≤ fixSub φ)
    (hR : IsComponent (R.subgroupOf (fixSub φ))) :
    R.map γ.toMonoidHom ≤ fixSub φ ∧ IsComponent ((R.map γ.toMonoidHom).subgroupOf (fixSub φ)) := by
  have hle : R.map γ.toMonoidHom ≤ fixSub φ := by
    rintro _ ⟨y, hy, rfl⟩
    exact apply_mem_fixSub h (hRφ hy)
  have h' : γ⁻¹ * φ = φ * γ⁻¹ := by
    calc γ⁻¹ * φ = γ⁻¹ * (φ * γ) * γ⁻¹ := by group
      _ = γ⁻¹ * (γ * φ) * γ⁻¹ := by rw [h]
      _ = φ * γ⁻¹ := by group
  let f : ↥(fixSub φ) →* ↥(fixSub φ) :=
    { toFun := fun y => ⟨γ (y : X), apply_mem_fixSub h y.2⟩
      map_one' := Subtype.ext (map_one γ)
      map_mul' := fun a b => Subtype.ext (map_mul γ (a : X) b) }
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    refine ⟨⟨γ⁻¹ y, apply_mem_fixSub h' hy⟩, Subtype.ext ?_⟩
    change γ (γ⁻¹ y) = y
    rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  have hmap : (R.subgroupOf (fixSub φ)).map f = (R.map γ.toMonoidHom).subgroupOf (fixSub φ) := by
    ext ⟨y, hy⟩
    constructor
    · rintro ⟨z, hz, hzy⟩
      exact ⟨z, hz, congrArg Subtype.val hzy⟩
    · rintro ⟨z, hz, hzy⟩
      exact ⟨⟨z, hRφ hz⟩, hz, Subtype.ext hzy⟩
  refine ⟨hle, ?_, ?_⟩
  · have hRq : IsQuasisimple ↥R :=
      LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hRφ) hR.1
    exact LocalCores.isQuasisimple_of_mulEquiv
      ((R.equivMapOfInjective γ.toMonoidHom γ.injective).trans
        (subgroupOfEquivOfLe hle).symm) hRq
  · rw [← hmap]
    exact hR.2.map hf

end Commute

variable {k : Type} [Field k] [Finite k]

theorem false_of_swap {φ γ : MulAut (projectiveSL 4 k)} (hγφ : γ * φ = φ * γ)
    {J' : Subgroup (projectiveSL 4 k)} (hJφ : J' ≤ fixSub φ)
    (hJ : IsComponent (J'.subgroupOf (fixSub φ)))
    (huniq : ∀ R : Subgroup (projectiveSL 4 k), R ≤ fixSub φ →
      IsComponent (R.subgroupOf (fixSub φ)) → R ≤ J')
    (hJna : ∃ a b : ↥J', a * b ≠ b * a) {A₁ A₂ : Subgroup (MulAut (projectiveSL 4 k))}
    (hJA : J'.map MulAut.conj = A₁) (hswap : ∀ a ∈ A₁, γ * a * γ⁻¹ ∈ A₂)
    (hcomm : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a) : False := by
  obtain ⟨hle, hc⟩ := isComponent_map_of_commute hγφ hJφ hJ
  have hJJ := huniq _ hle hc
  have hconj : ∀ z ∈ J', MulAut.conj (γ z) ∈ A₁ ⊓ A₂ := by
    intro z hz
    refine ⟨hJA ▸ mem_map_of_mem _ (hJJ ⟨z, hz, rfl⟩), ?_⟩
    rw [← CSL.mul_conj_mul_inv]
    exact hswap _ (hJA ▸ mem_map_of_mem _ hz)
  obtain ⟨a, b, hab⟩ := hJna
  apply hab
  apply Subtype.ext
  apply γ.injective
  apply CSL.conj_injective
  have h1 := hconj a a.2
  have h2 := hconj b b.2
  rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul, map_mul, map_mul]
  exact (hcomm _ h2.1 _ h1.2).symm

omit [Finite k] in
theorem transpose_mul_mul_eq_of_dotProduct {M R : Matrix (Fin 4) (Fin 4) k}
    (h : ∀ u v, (M *ᵥ u) ⬝ᵥ (R *ᵥ (M *ᵥ v)) = u ⬝ᵥ (R *ᵥ v)) : Mᵀ * R * M = R := by
  apply Matrix.ext_of_mulVec_single
  intro j
  apply dotProduct_eq
  intro u
  rw [dotProduct_comm, dotProduct_comm (R *ᵥ _), ← h u (Pi.single j 1), Matrix.mul_assoc,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

theorem split_false (hk2 : ringChar k ≠ 2) {φ : MulAut (projectiveSL 4 k)}
    {J' : Subgroup (projectiveSL 4 k)} (hJφ : J' ≤ fixSub φ)
    (hJ : IsComponent (J'.subgroupOf (fixSub φ)))
    (huniq : ∀ R : Subgroup (projectiveSL 4 k), R ≤ fixSub φ →
      IsComponent (R.subgroupOf (fixSub φ)) → R ≤ J')
    (hJna : ∃ a b : ↥J', a * b ≠ b * a) {B : GL (Fin 4) k}
    (hφB : φ = conjAut 4 k B * dualAut 4 k) (hB : (B : Matrix (Fin 4) (Fin 4) k)ᵀ = B)
    {ψ : (Fin 4 → k) ≃ₗ[k] Matrix (Fin 2) (Fin 2) k}
    (hψ : ∀ v, v ⬝ᵥ (((B⁻¹ : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k) *ᵥ v) = (ψ v).det)
    (hfac : J'.map MulAut.conj = (splitLeftHom ψ).range.map (conjAut 4 k) ∨
      J'.map MulAut.conj = (splitRightHom ψ).range.map (conjAut 4 k)) : False := by
  have htwo : (2 : k) ≠ 0 := Ring.two_ne_zero hk2
  set T : Matrix (Fin 2) (Fin 2) k ≃ₗ[k] Matrix (Fin 2) (Fin 2) k :=
    Matrix.transposeLinearEquiv (Fin 2) (Fin 2) k k with hT
  set g : GL (Fin 4) k := linearConjGL ψ T with hg
  have hgv : ∀ v, (g : Matrix (Fin 4) (Fin 4) k) *ᵥ v = ψ.symm (ψ v)ᵀ := fun v => by
    rw [hg, linearConjGL_mulVec]
    rfl
  have hR : ((B⁻¹ : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k)ᵀ = (B⁻¹ : GL (Fin 4) k) :=
    transpose_inv_eq_of_transpose_eq hB
  have hgI : g ∈ CatalogueBGraphForm.isometryGroup 4 k B⁻¹ := by
    rw [CatalogueBGraphForm.mem_isometryGroup]
    apply transpose_mul_mul_eq_of_dotProduct
    intro u v
    have h1 := Catalog7L4E.two_mul_dotProduct_eq ψ hR hψ u v
    have h2 := Catalog7L4E.two_mul_dotProduct_eq ψ hR hψ ((g : Matrix (Fin 4) (Fin 4) k) *ᵥ u)
      ((g : Matrix (Fin 4) (Fin 4) k) *ᵥ v)
    rw [hgv, hgv, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h2
    have h3 : Catalog7L4E.detPolar (ψ u)ᵀ (ψ v)ᵀ = Catalog7L4E.detPolar (ψ u) (ψ v) := by
      rw [Catalog7L4E.detPolar, Catalog7L4E.detPolar, ← Matrix.transpose_add, det_transpose,
        det_transpose, det_transpose]
    rw [h3, ← h1] at h2
    rw [hgv, hgv]
    exact mul_left_cancel₀ htwo h2
  have hγφ : conjAut 4 k g * φ = φ * conjAut 4 k g := by
    have h := isometryGroup_le_comap_centralizer B hgI
    rw [mem_comap, mem_centralizer_singleton_iff] at h
    rw [hφB]
    exact h
  have hLR : ∀ U : SpecialLinearGroup (Fin 2) k,
      g * splitLeftHom ψ U * g⁻¹ = splitRightHom ψ (SpecialLinearGroup.transpose U)⁻¹ := by
    intro U
    have key : g * splitLeftHom ψ U = splitRightHom ψ (SpecialLinearGroup.transpose U)⁻¹ * g :=
      eq_of_mulVec_eq fun v => by
        simp only [Units.val_mul, ← Matrix.mulVec_mulVec, hgv, splitLeftHom_mulVec,
          splitRightHom_mulVec, LinearEquiv.apply_symm_apply, inv_inv, Matrix.transpose_mul]
        rfl
    rw [key, mul_inv_cancel_right]
  have hRL : ∀ W : SpecialLinearGroup (Fin 2) k,
      g * splitRightHom ψ W * g⁻¹ = splitLeftHom ψ (SpecialLinearGroup.transpose W⁻¹) := by
    intro W
    have key : g * splitRightHom ψ W = splitLeftHom ψ (SpecialLinearGroup.transpose W⁻¹) * g :=
      eq_of_mulVec_eq fun v => by
        simp only [Units.val_mul, ← Matrix.mulVec_mulVec, hgv, splitLeftHom_mulVec,
          splitRightHom_mulVec, LinearEquiv.apply_symm_apply, Matrix.transpose_mul]
        rfl
    rw [key, mul_inv_cancel_right]
  have hcomm : ∀ a ∈ (splitLeftHom ψ).range.map (conjAut 4 k),
      ∀ b ∈ (splitRightHom ψ).range.map (conjAut 4 k), a * b = b * a := by
    rintro _ ⟨_, ⟨U, rfl⟩, rfl⟩ _ ⟨_, ⟨W, rfl⟩, rfl⟩
    rw [← map_mul, ← map_mul, splitLeftHom_commute]
  rcases hfac with h | h
  · refine false_of_swap hγφ hJφ hJ huniq hJna h ?_ hcomm
    rintro _ ⟨_, ⟨U, rfl⟩, rfl⟩
    rw [← map_inv, ← map_mul, ← map_mul, hLR]
    exact mem_map_of_mem _ ⟨_, rfl⟩
  · refine false_of_swap hγφ hJφ hJ huniq hJna h ?_ fun a ha b hb => (hcomm b hb a ha).symm
    rintro _ ⟨_, ⟨W, rfl⟩, rfl⟩
    rw [← map_inv, ← map_mul, ← map_mul, hRL]
    exact mem_map_of_mem _ ⟨_, rfl⟩

theorem rowS_or_rowO {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hk : Nat.card k = ℓ ^ e) {φ : MulAut (projectiveSL 4 k)} (hφ2 : φ ^ 2 = 1) (hφ1 : φ ≠ 1)
    {J' : Subgroup (projectiveSL 4 k)} (hJφ : J' ≤ fixSub φ)
    (hJ : IsComponent (J'.subgroupOf (fixSub φ)))
    (huniq : ∀ R : Subgroup (projectiveSL 4 k), R ≤ fixSub φ →
      IsComponent (R.subgroupOf (fixSub φ)) → R ≤ J')
    {m : ℕ} (hJm : Blueprint.LieModel ↥J' .PSL 2 ℓ m) :
    m = 2 * e ∧
      (SelectorRowS 4 k (MonoidHom.id (MulAut (projectiveSL 4 k)))
          (OuterAutomorphisms.inner (projectiveSL 4 k)) φ (J'.map MulAut.conj) ∨
        SelectorRowO 4 k (MonoidHom.id (MulAut (projectiveSL 4 k)))
          (OuterAutomorphisms.inner (projectiveSL 4 k)) φ (J'.map MulAut.conj)) := by
  classical
  set ρ := MonoidHom.id (MulAut (projectiveSL 4 k)) with hρ
  have hinj : Function.Injective ρ := Function.injective_id
  set L := J'.map (MulAut.conj : projectiveSL 4 k →* MulAut (projectiveSL 4 k)) with hL
  have ha : orderOf φ = 2 := orderOf_eq_prime hφ2 hφ1
  have hodd : Odd (Nat.card k) := by rw [hk]; exact (hℓ.odd_of_ne_two hℓ2).pow
  have : CharP k ℓ := finite_field_prime_power_characteristic hℓ he hk
  have hk2 : ringChar k ≠ 2 := by rw [ringChar.eq k ℓ]; exact hℓ2
  have htwo : (2 : k) ≠ 0 := Ring.two_ne_zero hk2
  have hJc : CFSG.Assembly.IsComponentOf J' (fixSub φ) :=
    (isComponentOf_iff_isComponent_subgroupOf hJφ).2 hJ
  have hL₁ : CFSG.Assembly.IsComponentOf (L.map ρ)
      (OuterAutomorphisms.inner (projectiveSL 4 k) ⊓ centralizer {ρ φ}) := by
    have h1 := isComponentOf_map_of_injective hJc MulAut.conj CSL.conj_injective
    rw [OIL.map_conj_fixSub] at h1
    rw [hρ, Subgroup.map_id]
    exact h1
  let eJL : ↥J' ≃* ↥L := J'.equivMapOfInjective _ CSL.conj_injective
  have hJq : IsQuasisimple ↥J' :=
    LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hJφ) hJ.1
  have hJna := FooteLit.exists_mul_ne_mul_of_isQuasisimple hJq
  have : IsSimpleGroup ↥J' := FooteLit.isSimpleGroup_of_lieModel_psl_two hJm
  have : IsSimpleGroup ↥L := eJL.symm.isSimpleGroup
  have hLna : ∃ a b : ↥L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hJna
    exact ⟨eJL a, eJL b, fun h => hab (eJL.injective (by rw [map_mul, map_mul, h]))⟩
  have hLZ : center ↥L = ⊥ := FooteLit.center_eq_bot_of_isSimpleGroup hLna
  have hZodd : Odd (Nat.card (center ↥L)) := by
    rw [hLZ, Subgroup.card_bot]
    exact odd_one
  let eLb : ↥L ⧸ center ↥L ≃* ↥J' :=
    (QuotientGroup.quotientMulEquivOfEq hLZ).trans (QuotientGroup.quotientBot.trans eJL.symm)
  have hLm : Blueprint.LieModel (↥L ⧸ center ↥L) .PSL 2 ℓ m :=
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv eLb.symm hJm
  have hsrc : StatedClassicalModel (↥L ⧸ center ↥L) .PSL 2 ℓ m ∨
      Nonempty (↥L ⧸ center ↥L ≃* alternatingGroup (Fin 7)) ∨
      StatedClassicalModel (↥L ⧸ center ↥L) .PSL 3 2 2 :=
    Or.inl (GSThmB.statedClassicalModel_of_lieModel_ne_zero (by norm_num) hLm)
  have hCA : (centralizer {φ}).map ρ = ρ.range ⊓ centralizer {ρ φ} := by
    rw [hρ, Subgroup.map_id, MonoidHom.range_eq_top.2 Function.surjective_id, top_inf_eq]
    rfl
  have hCW : (OuterAutomorphisms.inner (projectiveSL 4 k) ⊓ centralizer {φ}).map ρ =
      OuterAutomorphisms.inner (projectiveSL 4 k) ⊓ centralizer {ρ φ} := by
    rw [hρ, Subgroup.map_id]
    rfl
  have hbig : ∀ {E : Type} [Field E] [Finite E], Nat.card E = Nat.card k ^ 2 →
      Nonempty (↥L ≃* projectiveSL 2 E) → m = 2 * e := by
    intro E _ _ hE ⟨eX⟩
    have hEodd : Odd (Nat.card E) := by rw [hE]; exact hodd.pow
    let eX' : ↥L ≃* GorensteinWalter.PSL2 E :=
      eX.trans (LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 E).symm
    have hLm' : Blueprint.LieModel (↥L ⧸ (⊥ : Subgroup ↥L)) .PSL 2 ℓ m :=
      CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
        ((QuotientGroup.quotientBot.trans eJL.symm).symm) hJm
    have h := GSThmB.Catalog7L4M.eq_card_of_psl2 rfl hℓ hℓ2 hLm' hEodd eX'
    rw [hE, hk, ← pow_mul] at h
    have := Nat.pow_right_injective hℓ.two_le h
    omega
  obtain ⟨-, hform⟩ := automorphism_generation (K := k) (by norm_num : 3 ≤ 4)
  obtain ⟨B, τ, ε, hε, hφB⟩ := hform φ
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · rw [pow_zero, mul_one] at hφB
    by_cases hτ : τ = 1
    · subst hτ
      rw [map_one, mul_one] at hφB
      obtain ⟨μ, hμ, hsq, -⟩ := inner_case_reduction ha le_rfl hℓ hℓ2 he hk hinj hL₁ hφB hℓ2
        hsrc (fun _ => Or.inr hZodd)
      obtain ⟨hrow, E, _, _, hE, hiso⟩ :=
        selectorRowS_of_inner htwo hinj hCA hCW hL₁ hφB hμ hsq
      exact ⟨hbig hE hiso, Or.inl hrow⟩
    · exact (field_case_false ha (by norm_num) hℓ hℓ2 he hk hinj hL₁ hτ hφB hℓ2 hsrc).elim
  · rw [pow_one] at hφB
    by_cases hτ : τ = 1
    · subst hτ
      rw [map_one, mul_one] at hφB
      have hα2 : (conjAut 4 k B * dualAut 4 k) ^ 2 = 1 := by rw [← hφB]; exact hφ2
      rcases transpose_eq_or_eq_neg_of_pureGraph (by norm_num) B hα2 with hB | hB
      · by_cases hsplit : ∃ S : Submodule k (Fin 4 → k), Module.finrank k S = 2 ∧
            ∀ v ∈ S, CatalogueBLinearHigherB.matrixQuadraticForm B⁻¹ v = 0
        · exfalso
          obtain ⟨-, ψ, hψ, hfac⟩ :=
            Catalog7L4E.split_component_factor hℓ hℓ2 he hk hL₁ hφB hB hsplit
          rw [hρ, Subgroup.map_id] at hfac
          exact split_false hk2 hJφ hJ huniq hJna hφB hB hψ hfac
        · obtain ⟨hrow, E, _, _, hE, hiso⟩ :=
            selectorRowO_of_nonsplit hodd hinj hCA hCW hL₁ hφB hB hsplit
          exact ⟨hbig hE hiso, Or.inr hrow⟩
      · exact (symplectic_case_false (by norm_num) hℓ hℓ2 he hk hinj hL₁ hφB hB hℓ2 hsrc).elim
    · exact (graph_field_case_false ha (by norm_num) hℓ hℓ2 he hk hinj hL₁ hτ hφB hℓ2
        hsrc).elim

end CFSG.ComponentClassification.HarrisLit.C3
