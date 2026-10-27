module

public import CFSG.LocalAnalysis.ComponentClassification.FiveCatC5PSLFour
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerUGraph

public section

namespace CFSG.ComponentClassification.SolMax.FiveCat.C5PSU

open CFSG Subgroup Matrix CFSG.Open CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.CatLeafProof.X10Lin
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram idForm idForm_isSymm idForm_separatingLeft
  toLin_mem_sesqUnitaryGroup_iff)

theorem unique_component_lift {P S : Type} [Group P] [Group S] [Finite P] {π : P →* S}
    (hπ : Function.Surjective π) (hK : π.ker ≤ center P) {a : MulAut P} {α : MulAut S}
    (ha : ∀ x, a (a x) = x) (hα : ∀ s, α (α s) = s) (hcomm : ∀ x, π (a x) = α (π x))
    {L : Subgroup (fixedSubgroup α)} (hL : IsComponent L)
    (hu : ∀ L' : Subgroup (fixedSubgroup α), IsComponent L' → L' = L) :
    ∃ Q : Subgroup P, Assembly.IsComponentOf Q (fixedSubgroup a) ∧
      Nonempty (↥Q ⧸ center ↥Q ≃* ↥L ⧸ center ↥L) ∧
      ∀ Q' : Subgroup P, Assembly.IsComponentOf Q' (fixedSubgroup a) → Q' = Q := by
  obtain ⟨-, -, hbij, hlift, -⟩ :=
    full_central_kernel_involution_fixed_component_correspondence hπ hK ha hα hcomm
  have hR : Assembly.IsComponentOf (L.map (fixedSubgroup α).subtype) (fixedSubgroup α) := by
    refine (isComponentOf_iff_isComponent_subgroupOf (map_subtype_le L)).2 ?_
    have hRL : (L.map (fixedSubgroup α).subtype).subgroupOf (fixedSubgroup α) = L :=
      Subgroup.comap_map_eq_self_of_injective (subtype_injective _) L
    rw [hRL]
    exact hL
  obtain ⟨-, hQ, hQR, -, -, -, hQZ⟩ := hlift _ hR
  refine ⟨_, hQ, ?_, fun Q' hQ' => ?_⟩
  · obtain ⟨e⟩ := hQZ
    exact ⟨e.trans (QuotientGroup.congr _ _ (L.equivMapOfInjective (fixedSubgroup α).subtype
      (subtype_injective _)) (Subgroup.map_center_eq _)).symm⟩
  · have h1 := hbij.mapsTo hQ'
    have h2 := (isComponentOf_iff_isComponent_subgroupOf h1.1).1 h1
    have h3 := hu _ h2
    have h4 : Q'.map π = L.map (fixedSubgroup α).subtype := by
      rw [← h3, Subgroup.map_subgroupOf_eq_of_le h1.1]
    exact hbij.injOn hQ' hQ (h4.trans hQR.symm)


section Graph

variable {n : ℕ} {K : Type} [Field K] {p f : ℕ} (h : UnitaryFieldData p f K)

theorem psu_graph_scalar (hn : 3 ≤ n) (A : primeFormUnitary h (idGram K n)) (φ : K ≃+* K)
    (hφ : ∀ x, φ x = h.bar x)
    (hA : orderOf (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩) = 2) :
    ∃ c : Kˣ, (A : GL (Fin n) K) * glAut φ (A : GL (Fin n) K) =
        GeneralLinearGroup.scalar (Fin n) c ∧
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar = (c : K) • 1 := by
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  have hx2 : primeFormPsi h hC (⟨A, φ⟩ * ⟨A, φ⟩) = 1 := by
    rw [map_mul, ← pow_two, ← hA, pow_orderOf_eq_one]
  obtain ⟨-, c, -, hc⟩ := (primeFormPsi_eq_one_iff h hC hn _).mp hx2
  have hmapA : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map φ =
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar := Matrix.ext fun i j => hφ _
  have hAA : (A : GL (Fin n) K) * glAut φ (A : GL (Fin n) K) =
      GeneralLinearGroup.scalar (Fin n) c := hc
  refine ⟨c, hAA, ?_⟩
  have h2 := congrArg Units.val hAA
  rw [Units.val_mul, coe_glAut, GeneralLinearGroup.coe_scalar, hmapA] at h2
  rw [h2, Matrix.smul_one_eq_diagonal]
  rfl

@[expose] noncomputable def psiLift (A : primeFormUnitary h (idGram K n)) (φ : K ≃+* K) :
    MulAut (gramSU h (idGram K n)) :=
  primeFormConjSU h (idGram K n) A *
    primeFormFieldSU h (isPrimeFormGram_one : IsPrimeFormGram (1 : GL (Fin n) K)) φ

theorem psiLift_apply (A : primeFormUnitary h (idGram K n)) (φ : K ≃+* K)
    (g : gramSU h (idGram K n)) :
    ((psiLift h A φ g : gramSU h (idGram K n)) : GL (Fin n) K) =
      (A : GL (Fin n) K) * glAut φ (g : GL (Fin n) K) * (A : GL (Fin n) K)⁻¹ := rfl

theorem psiLift_inv (A : primeFormUnitary h (idGram K n)) (φ : K ≃+* K) :
    (normOneScalars h (gramSU h (idGram K n)) n).map (psiLift h A φ).toMonoidHom =
      normOneScalars h (gramSU h (idGram K n)) n := by
  have e1 : (psiLift h A φ).toMonoidHom = (primeFormConjSU h (idGram K n) A).toMonoidHom.comp
      (primeFormFieldSU h
        (isPrimeFormGram_one : IsPrimeFormGram (1 : GL (Fin n) K)) φ).toMonoidHom :=
    rfl
  rw [e1, ← Subgroup.map_map, map_normOneScalars_field, map_normOneScalars_conj]

theorem psiLift_involutive (A : primeFormUnitary h (idGram K n))
    (φ : K ≃+* K) (hφ : ∀ x, φ x = h.bar x) {c : Kˣ}
    (hAA : (A : GL (Fin n) K) * glAut φ (A : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) c)
    (x : gramSU h (idGram K n)) : psiLift h A φ (psiLift h A φ x) = x := by
  have hφ2 : φ * φ = 1 := RingEquiv.ext fun x => by
    change φ (φ x) = x
    rw [hφ, hφ, h.bar_bar]
  apply Subtype.ext
  rw [psiLift_apply, psiLift_apply]
  have e1 : ∀ g : GL (Fin n) K, glAut φ (glAut φ g) = g := fun g => by
    rw [← MulAut.mul_apply, ← map_mul, hφ2, map_one, MulAut.one_apply]
  rw [map_mul, map_mul, map_inv, e1]
  calc (A : GL (Fin n) K) * (glAut φ (A : GL (Fin n) K) * (x : GL (Fin n) K) *
        (glAut φ (A : GL (Fin n) K))⁻¹) * (A : GL (Fin n) K)⁻¹
      = ((A : GL (Fin n) K) * glAut φ (A : GL (Fin n) K)) * x *
          ((A : GL (Fin n) K) * glAut φ (A : GL (Fin n) K))⁻¹ := by group
    _ = GeneralLinearGroup.scalar (Fin n) c * x * (GeneralLinearGroup.scalar (Fin n) c)⁻¹ := by
        rw [hAA]
    _ = x := by
        rw [GeneralLinearGroup.scalar_commute]
        group

theorem primeFormPsi_eq_onQuotient (A : primeFormUnitary h (idGram K n)) (φ : K ≃+* K) :
    primeFormPsi h (isPrimeFormGram_one : IsPrimeFormGram (1 : GL (Fin n) K)) ⟨A, φ⟩ =
      CatalogueBFixedCentralQuotient.onQuotient (normOneScalars h (gramSU h (idGram K n)) n)
        (psiLift h A φ) (psiLift_inv h A φ) := by
  refine MulEquiv.ext fun y => ?_
  induction y using QuotientGroup.induction_on with
  | H g =>
    rw [show ((g : primeFormP h (idGram K n))) =
        QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n) g from rfl,
      CatalogueBFixedCentralQuotient.onQuotient_mk, primeFormPsi_apply, MulAut.mul_apply]
    change primeFormConjAut h _ A (primeFormFieldAut h _ φ (g : primeFormP h _)) = _
    rw [primeFormFieldAut_mk, primeFormConjAut_mk]
    rfl

theorem psu_graph_lift_unique (hn : 3 ≤ n) (A : primeFormUnitary h (idGram K n)) (φ : K ≃+* K)
    (hφ : ∀ x, φ x = h.bar x)
    (hA : orderOf (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩) = 2)
    {L : Subgroup (fixedSubgroup (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩))}
    (hL : IsComponent L)
    (hu : ∀ L' : Subgroup (fixedSubgroup (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩)),
      IsComponent L' → L' = L) :
    ∃ Q : Subgroup (gramSU h (idGram K n)),
      Assembly.IsComponentOf Q (fixedSubgroup (psiLift h A φ)) ∧
      Nonempty (↥Q ⧸ center ↥Q ≃* ↥L ⧸ center ↥L) ∧
      ∀ Q' : Subgroup (gramSU h (idGram K n)),
        Assembly.IsComponentOf Q' (fixedSubgroup (psiLift h A φ)) → Q' = Q := by
  have : Finite K := h.finite
  obtain ⟨c, hAA, -⟩ := psu_graph_scalar h hn A φ hφ hA
  have hZc : normOneScalars h (gramSU h (idGram K n)) n ≤ center (gramSU h (idGram K n)) := by
    rintro z ⟨c', -, -, hz⟩
    refine Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hz]
    exact (commute_scalar c' _).eq
  refine unique_component_lift (π := QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']; exact hZc)
    (psiLift_involutive h A φ hφ hAA) (fun s => ?_) (fun x => ?_) hL hu
  · rw [← MulAut.mul_apply, ← pow_two, ← hA, pow_orderOf_eq_one, MulAut.one_apply]
  · rw [primeFormPsi_eq_onQuotient h A φ]
    exact CatalogueBFixedCentralQuotient.onQuotient_mk _ _ (psiLift_inv h A φ) _

@[expose] noncomputable def suToLin :
    gramSU h (idGram K n) →* LinearMap.GeneralLinearGroup K (Fin n → K) :=
  (Matrix.GeneralLinearGroup.toLin : GL (Fin n) K ≃*
    LinearMap.GeneralLinearGroup K (Fin n → K)).toMonoidHom.comp (gramSU h (idGram K n)).subtype

theorem suToLin_injective : Function.Injective (suToLin h (n := n)) := fun x y hxy =>
  Subtype.ext (Matrix.GeneralLinearGroup.toLin.injective hxy)

theorem psiLift_fixed_map (A : primeFormUnitary h (idGram K n)) (φ : K ≃+* K)
    (hφ : ∀ x, φ x = h.bar x) :
    (fixedSubgroup (psiLift h A φ)).map (suToLin h) =
      commutingUnitary (idForm h n)
        (semilinearMatrixMap h ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ⊓
        sesqSpecialUnitaryGroup (idForm h n) := by
  set τ₀ := semilinearMatrixMap h ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hτ₀def
  have hfixg : ∀ g : gramSU h (idGram K n), g ∈ fixedSubgroup (psiLift h A φ) ↔
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar := by
    intro g
    change psiLift h A φ g = g ↔ _
    rw [Subtype.ext_iff, psiLift_apply]
    rw [mul_inv_eq_iff_eq_mul, ← Units.val_inj, Units.val_mul, Units.val_mul, coe_glAut]
    have hmap : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map φ =
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar := Matrix.ext fun i j => hφ _
    rw [hmap]
    exact eq_comm
  have htoLin : ∀ (g : GL (Fin n) K) (v : Fin n → K),
      ((Matrix.GeneralLinearGroup.toLin g : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        (Fin n → K) →ₗ[K] (Fin n → K)) v = (g : Matrix (Fin n) (Fin n) K) *ᵥ v := fun g v => by
    rw [Matrix.GeneralLinearGroup.coe_toLin, Matrix.mulVecLin_apply]
  ext y
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hS : suToLin h g ∈ sesqSpecialUnitaryGroup (idForm h n) :=
      (toLin_mem_sesqSpecialUnitaryGroup_iff h (idGram K n) g).mpr g.2
    refine Subgroup.mem_inf.mpr ⟨⟨sesqSpecialUnitaryGroup_le _ hS, fun v => ?_⟩, hS⟩
    change ((Matrix.GeneralLinearGroup.toLin (g : GL (Fin n) K) :
        LinearMap.GeneralLinearGroup K (Fin n → K)) : (Fin n → K) →ₗ[K] (Fin n → K))
          (τ₀ v) = τ₀ (((Matrix.GeneralLinearGroup.toLin (g : GL (Fin n) K) :
            LinearMap.GeneralLinearGroup K (Fin n → K)) : (Fin n → K) →ₗ[K] (Fin n → K)) v)
    rw [htoLin, htoLin]
    exact (OddInner.commute_semilinearMatrixMap_iff h _ _).mpr ((hfixg g).mp hg) v
  · intro hy
    obtain ⟨hyC, hyS⟩ := Subgroup.mem_inf.mp hy
    set g := Matrix.GeneralLinearGroup.toLin.symm y with hgdef
    have hgy : Matrix.GeneralLinearGroup.toLin g = y := MulEquiv.apply_symm_apply _ _
    have hg : g ∈ gramSU h (idGram K n) := by
      rw [← toLin_mem_sesqSpecialUnitaryGroup_iff, hgy]
      exact hyS
    refine ⟨⟨g, hg⟩, (hfixg _).mpr
      ((OddInner.commute_semilinearMatrixMap_iff h _ _).mp fun v => ?_), hgy⟩
    have h1 := hyC.2 v
    rw [← hgy, htoLin, htoLin] at h1
    exact h1

theorem psu_graph_two_components (A : primeFormUnitary h (idGram K n)) (φ : K ≃+* K)
    (hφ : ∀ x, φ x = h.bar x) {G₀ : Type} [Group G₀]
    (e₁ : ↥(commutingUnitary (idForm h n)
      (semilinearMatrixMap h ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) ≃* G₀)
    {F₁ F₂ : Subgroup G₀} (h₁ : IsComponent F₁) (h₂ : IsComponent F₂) (hne : F₁ ≠ F₂)
    (hΩ₁ : F₁ ≤ commutator G₀) (hΩ₂ : F₂ ≤ commutator G₀) :
    ∃ Q₁ Q₂ : Subgroup (gramSU h (idGram K n)),
      Assembly.IsComponentOf Q₁ (fixedSubgroup (psiLift h A φ)) ∧
      Assembly.IsComponentOf Q₂ (fixedSubgroup (psiLift h A φ)) ∧ Q₁ ≠ Q₂ := by
  set τ₀ := semilinearMatrixMap h ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hτ₀def
  set G := commutingUnitary (idForm h n) τ₀ with hGdef
  set B := fixedSubgroup (psiLift h A φ) with hBdef
  have hmap := psiLift_fixed_map h A φ hφ
  have hBG : ∀ b : ↥B, suToLin h b.1 ∈ G := fun b => by
    have : suToLin h b.1 ∈ B.map (suToLin h) := Subgroup.mem_map_of_mem _ b.2
    rw [hmap] at this
    exact (Subgroup.mem_inf.mp this).1
  let ι : ↥B →* ↥G := ((suToLin h).comp B.subtype).codRestrict G hBG
  have hι : Function.Injective ι := fun a b hab =>
    Subtype.ext (suToLin_injective h (congrArg Subtype.val hab))
  let Θ : ↥B →* G₀ := e₁.toMonoidHom.comp ι
  have hΘ : Function.Injective Θ := fun a b hab => hι (e₁.injective hab)
  have hrange : ∀ {F : Subgroup G₀}, F ≤ commutator G₀ → F ≤ Θ.range := by
    intro F hF g hg
    let D : G₀ →* Kˣ := (Units.map (LinearMap.det : ((Fin n → K) →ₗ[K] (Fin n → K)) →* K)).comp
      (G.subtype.comp e₁.symm.toMonoidHom)
    have hdet : D g = 1 := MonoidHom.mem_ker.1 (Abelianization.commutator_subset_ker D (hF hg))
    have hmem : ((e₁.symm g : ↥G) : LinearMap.GeneralLinearGroup K (Fin n → K)) ∈
        G ⊓ sesqSpecialUnitaryGroup (idForm h n) :=
      Subgroup.mem_inf.2 ⟨(e₁.symm g).2, by
        rw [sesqSpecialUnitaryGroup]
        exact Subgroup.mem_inf.2 ⟨(e₁.symm g).2.1, MonoidHom.mem_ker.2 hdet⟩⟩
    rw [← hmap] at hmem
    obtain ⟨b, hb, hbg⟩ := Subgroup.mem_map.mp hmem
    refine ⟨⟨b, hb⟩, ?_⟩
    change e₁ (ι ⟨b, hb⟩) = g
    have : ι ⟨b, hb⟩ = e₁.symm g := Subtype.ext hbg
    rw [this, MulEquiv.apply_symm_apply]
  have hQB : ∀ {F : Subgroup G₀}, IsComponent F → F ≤ commutator G₀ →
      Assembly.IsComponentOf ((F.comap Θ).map B.subtype) B := by
    intro F hF hle
    refine (isComponentOf_iff_isComponent_subgroupOf (map_subtype_le _)).2 ?_
    have hQQ : ((F.comap Θ).map B.subtype).subgroupOf B = F.comap Θ :=
      Subgroup.comap_map_eq_self_of_injective (subtype_injective _) _
    rw [hQQ]
    exact C5PSL.isComponent_comap_of_le Θ hΘ hF (hrange hle)
  refine ⟨_, _, hQB h₁ hΩ₁, hQB h₂ hΩ₂, fun heq => hne ?_⟩
  have hcomap : F₁.comap Θ = F₂.comap Θ := Subgroup.map_injective (subtype_injective B) heq
  calc F₁ = (F₁.comap Θ).map Θ := by rw [Subgroup.map_comap_eq, inf_eq_right.2 (hrange hΩ₁)]
    _ = (F₂.comap Θ).map Θ := by rw [hcomap]
    _ = F₂ := by rw [Subgroup.map_comap_eq, inf_eq_right.2 (hrange hΩ₂)]

end Graph

theorem nonempty_centerQuotient_equiv_of_mulEquiv {A B X : Type} [Group A] [Group B] [Group X]
    (e : A ≃* B) (h : Nonempty (A ⧸ center A ≃* X)) : Nonempty (B ⧸ center B ≃* X) :=
  ⟨(QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).symm.trans h.some⟩

section Embed

variable {n : ℕ} {K : Type} [Field K] {p f : ℕ} (h : UnitaryFieldData p f K)

theorem psu_graph_component_G (A : primeFormUnitary h (idGram K n)) (φ : K ≃+* K)
    (hφ : ∀ x, φ x = h.bar x) {Q : Subgroup (gramSU h (idGram K n))}
    (hQ : Assembly.IsComponentOf Q (fixedSubgroup (psiLift h A φ))) :
    IsComponent ((Q.map (suToLin h)).subgroupOf (commutingUnitary (idForm h n)
      (semilinearMatrixMap h ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))) := by
  have hmap := psiLift_fixed_map h A φ hφ
  have h1 := isComponentOf_map_of_injective hQ (suToLin h) (suToLin_injective h)
  rw [hmap] at h1
  have hnormal : ((commutingUnitary (idForm h n)
      (semilinearMatrixMap h ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ⊓
        sesqSpecialUnitaryGroup (idForm h n)).subgroupOf (commutingUnitary (idForm h n)
      (semilinearMatrixMap h ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))).Normal := by
    constructor
    intro x hx g
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨-, hxS⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨(g * x * g⁻¹).2, ?_⟩
    rw [sesqSpecialUnitaryGroup] at hxS ⊢
    obtain ⟨hxU, hxD⟩ := Subgroup.mem_inf.mp hxS
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
        mul_mem (mul_mem g.2.1 hxU) (inv_mem g.2.1)
    · simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
        (MonoidHom.normal_ker _).conj_mem _ hxD (g : LinearMap.GeneralLinearGroup K (Fin n → K))
  have h2 := OddClassSelector.isComponentOf_of_normal_le h1 inf_le_left hnormal
  exact (isComponentOf_iff_isComponent_subgroupOf h2.1).1 h2

theorem psu_graph_map_le (A : primeFormUnitary h (idGram K n)) (φ : K ≃+* K)
    (hφ : ∀ x, φ x = h.bar x) {Q : Subgroup (gramSU h (idGram K n))}
    (hQ : Assembly.IsComponentOf Q (fixedSubgroup (psiLift h A φ))) :
    Q.map (suToLin h) ≤ commutingUnitary (idForm h n)
      (semilinearMatrixMap h ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  have hmap := psiLift_fixed_map h A φ hφ
  have h1 := isComponentOf_map_of_injective hQ (suToLin h) (suToLin_injective h)
  rw [hmap] at h1
  exact h1.1.trans inf_le_left

end Embed

section Descent

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

theorem psu_graph_descent_four {K : Type} [Field K] {f : ℕ} (h : UnitaryFieldData 5 f K)
    (τ₀ : (Fin 4 → K) →ₛₗ[h.bar] (Fin 4 → K)) (hτ₀ : Function.Bijective τ₀)
    (hτ₀B : ∀ v w, idForm h 4 (τ₀ v) (τ₀ w) = h.bar (idForm h 4 v w)) (c : Kˣ)
    (hμ : ∀ v, τ₀ (τ₀ v) = (c : K) • v) :
    (∃ (W : Type) (_ : AddCommGroup W) (_ : Module h.fixedField W)
        (_ : FiniteDimensional h.fixedField W) (Q₀ : QuadraticForm h.fixedField W),
        Q₀.polarBilin.Nondegenerate ∧ Module.finrank h.fixedField W = 4 ∧
          Nonempty (↥(commutingUnitary (idForm h 4) τ₀) ≃*
            ↥(TauCeti.QuadraticMap.orthogonalGroup Q₀))) ∨
    (∃ (W : Type) (_ : AddCommGroup W) (_ : Module h.fixedField W)
        (_ : FiniteDimensional h.fixedField W) (B' : LinearMap.BilinForm h.fixedField W),
        B'.IsAlt ∧ B'.Nondegenerate ∧ Module.finrank h.fixedField W = 4 ∧
          Nonempty (↥(commutingUnitary (idForm h 4) τ₀) ≃*
            ↥(CatalogueBAlternatingIsometry.isometryGroup B'))) := by
  have : Fact (Nat.Prime 5) := ⟨h.prime⟩
  have : Finite K := h.finite
  have hodd : Odd 5 := by decide
  have hdim : Module.finrank K (Fin 4 → K) = 4 := Module.finrank_fin_fun K
  obtain ⟨hμ1, ⟨b, hb⟩, ⟨t, ht⟩, hall⟩ := odd_unitary_conjugate_semilinear_involution_descent h
    hodd (by omega) (idForm_isSymm h 4) (idForm_separatingLeft h 4) τ₀ hτ₀ hτ₀B c hμ
  obtain ⟨-, hfinW, -, hB1, hB2⟩ := hall b t hb ht
  have : Module.Finite h.fixedField (conjFixed h ((b : K) • τ₀)) := finite_conjFixed
  rw [hdim] at hfinW
  rcases hμ1 with hμ1 | hμ1
  · obtain ⟨B', -, hsym, hnd, Φ, -⟩ := hB1 hμ1
    have h2' : (2 : h.fixedField) ≠ 0 := fun h0 => by
      have h1 := congrArg h.fixedField.subtype h0
      rw [map_ofNat, map_zero] at h1
      exact UnitaryHigher.two_ne_zero_of_odd h (by norm_num) h1
    have hQ₀ : (CatalogueBOrthogonalDescent.originalQuadratic B').polarBilin.Nondegenerate := by
      rw [CatalogueBOrthogonalDescent.originalQuadratic_polarBilin B' hsym h2']
      exact hnd
    exact Or.inl ⟨↥(conjFixed h ((b : K) • τ₀)), inferInstance, inferInstance, inferInstance,
      CatalogueBOrthogonalDescent.originalQuadratic B', hQ₀, hfinW,
      ⟨Φ.trans (MulEquiv.subgroupCongr
        (CatalogueBUnitaryB.isometryGroup_eq_orthogonalGroup B' hsym h2'))⟩⟩
  · obtain ⟨B', -, halt, hnd, -, Φ, -⟩ := hB2 hμ1
    exact Or.inr ⟨↥(conjFixed h ((b : K) • τ₀)), inferInstance, inferInstance, inferInstance, B',
      halt, hnd, hfinW, ⟨Φ⟩⟩

end Descent

theorem a5_psuGraph_four {K : Type} [Field K] {f : ℕ} (h : UnitaryFieldData 5 f K)
    (A : primeFormUnitary h (idGram K 4)) (φ : K ≃+* K) (hφ : ∀ x, φ x = h.bar x)
    (hA : orderOf (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩) = 2)
    {L : Subgroup (fixedSubgroup (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩))}
    (hL : IsComponent L) (hA5 : Nonempty (↥L ⧸ center ↥L ≃* alternatingGroup (Fin 5)))
    (hu : ∀ L' : Subgroup (fixedSubgroup (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩)),
      IsComponent L' → L' = L) : False := by
  have : Fact (Nat.Prime 5) := ⟨h.prime⟩
  have : Finite K := h.finite
  have hf1 : 1 ≤ f := h.one_le
  obtain ⟨Q, hQ, hQZ, huQ⟩ := psu_graph_lift_unique h (by norm_num) A φ hφ hA hL hu
  obtain ⟨c, -, hAc⟩ := psu_graph_scalar h (by norm_num) A φ hφ hA
  have hQA : Nonempty (↥Q ⧸ center ↥Q ≃* alternatingGroup (Fin 5)) := ⟨hQZ.some.trans hA5.some⟩
  have hτ₀ : Function.Bijective
      (semilinearMatrixMap h ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) :=
    OddInner.semilinearMatrixMap_bijective_of h c.ne_zero hAc
  have hτ₀B := OddInner.idForm_semilinearMatrixMap h A.2
  have hμ := OddInner.semilinearMatrixMap_sq_of h hAc
  have h3 := psu_graph_component_G h A φ hφ hQ
  have hkc : Nat.card h.fixedField = 5 ^ f := h.card_fixedField
  have hN1 := nonempty_centerQuotient_equiv_of_mulEquiv
    ((Q.equivMapOfInjective (suToLin h) (suToLin_injective h)).trans
      (Subgroup.subgroupOfEquivOfLe (psu_graph_map_le h A φ hφ hQ)).symm) hQA
  rcases psu_graph_descent_four h _ hτ₀ hτ₀B c hμ with
    ⟨W, _, _, _, Q₀, hQ₀, hdimW, ⟨eG⟩⟩ | ⟨W, _, _, _, B', halt, hnd, hdimW, ⟨Φ⟩⟩
  · by_cases hS : ∃ S : Submodule h.fixedField W, Module.finrank h.fixedField S = 2 ∧
        ∀ x ∈ S, Q₀ x = 0
    ·
      have h5 : 5 ≤ 5 ^ f := le_trans (by norm_num) (Nat.le_self_pow (by omega) 5)
      have hK2 : Nat.card h.fixedField ≠ 2 := by omega
      have hK3 : Nat.card h.fixedField ≠ 3 := by omega
      obtain ⟨ψ', e', -, -, hsup, hq₁, hq₂, hn₁, hn₂, hcomm, -, -⟩ :=
        LocalAnalysis.ComponentInitial.orthogonal_split_four_derived hK2 hK3 Q₀ hQ₀ hdimW hS
      obtain ⟨hc₁, hc₂, hne, hle₁, hle₂⟩ :=
        C5PSL.two_components_of_split hsup hq₁ hq₂ hn₁ hn₂ hcomm
      obtain ⟨Q₁, Q₂, hQ₁, hQ₂, hne'⟩ :=
        psu_graph_two_components h A φ hφ eG hc₁ hc₂ hne hle₁ hle₂
      exact hne' ((huQ Q₁ hQ₁).trans (huQ Q₂ hQ₂).symm)
    ·
      have hN₀ := LocalCores.isComponent_map_mulEquiv eG h3
      have hNA₀ := nonempty_centerQuotient_equiv_of_mulEquiv
        (((Q.map (suToLin h)).subgroupOf (commutingUnitary (idForm h 4)
          (semilinearMatrixMap h ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)))
            ).equivMapOfInjective eG.toMonoidHom eG.injective) hN1
      have hmodel := X10Lin.centralModel_orthogonal_nonsplit_four Nat.prime_five
        (by norm_num : (5 : ℕ) ≠ 2) hf1 hkc Q₀ hQ₀ hdimW hS hN₀
      obtain ⟨-, -, he⟩ := C5PSL.eq_psl_two_one_of_a5 (Or.inl rfl) hmodel.1 hmodel.2 hNA₀
      omega
  ·
    have hN₀ := LocalCores.isComponent_map_mulEquiv Φ h3
    have hNA₀ := nonempty_centerQuotient_equiv_of_mulEquiv
      (((Q.map (suToLin h)).subgroupOf (commutingUnitary (idForm h 4)
        (semilinearMatrixMap h ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)))
          ).equivMapOfInjective Φ.toMonoidHom Φ.injective) hN1
    have hmodel := X10Sp.centralModel_isometryGroup_component (ℓ := 5) (j := f) (m := 2)
      Nat.prime_five (by norm_num : (5 : ℕ) ≠ 2) hf1 hkc B' halt hnd hdimW le_rfl hN₀
    obtain ⟨h1, -⟩ := C5PSL.eq_psl_two_one_of_a5 (Or.inr (Or.inr (Or.inl rfl))) hmodel.1
      hmodel.2 hNA₀
    exact absurd h1 (by decide)

end CFSG.ComponentClassification.SolMax.FiveCat.C5PSU
