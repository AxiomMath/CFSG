module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RootCenterAutomorphismUnitary

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.RootCenter

open CFSG.BenderSuzuki.MatrixGroups CFSG.ShultStronglyClosedTI
open RootCenterAutomorphisms

variable {P F : Type*} [Group P] [Group F]

theorem map_conj_map (ε : P ≃* F) (H : Subgroup P) :
    (H.map ε.toMonoidHom).map MulAut.conj =
      (H.map MulAut.conj).map (MulAut.congr ε).toMonoidHom := by
  ext γ
  constructor
  · rintro ⟨_, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨MulAut.conj r, ⟨r, hr, rfl⟩, congr_conj ε r⟩
  · rintro ⟨_, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨ε r, Subgroup.mem_map_of_mem _ hr, (congr_conj ε r).symm⟩

theorem rootCenterAut_map (ε : P ≃* F) (R U : Subgroup P) :
    rootCenterAut (R.map ε.toMonoidHom) (U.map ε.toMonoidHom) =
      (rootCenterAut R U).map (MulAut.congr ε).toMonoidHom := by
  ext γ'
  obtain ⟨γ, rfl⟩ := (MulAut.congr ε).surjective γ'
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, mem_rootCenterAut, mem_rootCenterAut,
    RootCenterAutomorphisms.map_congr, RootCenterAutomorphisms.forall_congr_apply]
  exact and_congr_left' ⟨fun h' => Subgroup.map_injective ε.injective h', fun h' => by rw [h']⟩

variable {K : Type} [Field K] {J : HermitianForm 3 K} {hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]}
  {q : ℕ}

theorem UnitaryRootCenterAutomorphisms.map (h : UnitaryRootCenterAutomorphisms J hJ q)
    (ε : ProjectiveSpecialUnitaryMatrixGroup J ≃* F) :
    let R := (unitaryCoverRoot J hJ).map ε.toMonoidHom
    let U := (unitaryRootCenter J hJ).map ε.toMonoidHom
    let A := rootCenterAut R U
    (∀ x, x ∈ U ↔ x ∈ R ∧ ∀ y ∈ R, x * y = y * x) ∧
    Set.InjOn MulAut.conj (R : Set F) ∧
    (∃ D : Subgroup (MulAut F), R.map MulAut.conj ⊓ D = ⊥ ∧ R.map MulAut.conj ⊔ D = A ∧
      ((R.map MulAut.conj).subgroupOf A).Normal ∧ Nat.card D = 2 * (q + 1) ∧
      Nonempty (D ≃* DihedralGroup (q + 1))) ∧
    (∀ γ ∈ A, γ ^ 2 ∈ U.map MulAut.conj → γ ∈ R.map MulAut.conj ∨ γ ^ 2 = 1) ∧
    (∀ R₀ : Subgroup F, U ≤ R₀ → R₀ ≤ R → R₀.relIndex R ≤ 2 →
      {γ | γ ∈ A ∧ ∀ x ∈ R₀, γ x = x} = (U.map MulAut.conj : Set (MulAut F))) ∧
    IsElementaryAbelian 2 (U.map MulAut.conj) ∧ Nat.card (U.map MulAut.conj) = q := by
  intro R U A
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Φ := MulAut.congr ε
  have hA : A = (rootCenterAut (unitaryCoverRoot J hJ) (unitaryRootCenter J hJ)).map
      Φ.toMonoidHom := rootCenterAut_map ε _ _
  have hcR : R.map MulAut.conj = ((unitaryCoverRoot J hJ).map MulAut.conj).map Φ.toMonoidHom :=
    map_conj_map ε _
  have hcU : U.map MulAut.conj = ((unitaryRootCenter J hJ).map MulAut.conj).map Φ.toMonoidHom :=
    map_conj_map ε _
  have hΦ : ∀ γ H, Φ γ ∈ (H : Subgroup (MulAut _)).map Φ.toMonoidHom ↔ γ ∈ H := fun γ H =>
    Subgroup.mem_map_iff_mem Φ.injective
  refine ⟨fun x => ?_, ?_, ⟨(diagBar J hJ).map Φ.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_map_equiv, h.center_iff, Subgroup.mem_map_equiv]
    refine and_congr_right fun _ => ⟨fun H y hy => ?_, fun H y hy => ?_⟩
    · apply ε.symm.injective
      rw [map_mul, map_mul]
      exact H _ (Subgroup.mem_map_equiv.1 hy)
    · have := congrArg ε.symm (H (ε y) (Subgroup.mem_map_of_mem _ hy))
      rwa [map_mul, map_mul, MulEquiv.symm_apply_apply] at this
  · rintro _ ⟨r, hr, rfl⟩ _ ⟨s, hs, rfl⟩ hrs
    have h' : MulAut.conj r = MulAut.conj s := Φ.injective (by
      rw [congr_conj, congr_conj]
      exact hrs)
    exact congrArg ε (h.injOn_conj hr hs h')
  · rw [hcR, ← Subgroup.map_inf_eq _ _ _ Φ.injective, h.inf_eq_bot, Subgroup.map_bot]
  · rw [hcR, ← Subgroup.map_sup, h.sup_eq, hA]
  · rw [hcR, hA]
    have hn := h.normal
    have hle : (unitaryCoverRoot J hJ).map MulAut.conj ≤
        rootCenterAut (unitaryCoverRoot J hJ) (unitaryRootCenter J hJ) := by
      rw [← h.sup_eq]
      exact le_sup_left
    rw [Subgroup.normal_subgroupOf_iff hle] at hn
    rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono hle)]
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_inv, ← map_mul]
    exact Subgroup.mem_map_of_mem _ (hn a b ha hb)
  · rw [Subgroup.card_map_of_injective Φ.injective, h.card_diagBar]
  · obtain ⟨e⟩ := h.diagBar_dihedral
    exact ⟨((diagBar J hJ).equivMapOfInjective Φ.toMonoidHom Φ.injective).symm.trans e⟩
  · intro γ' hγ' hsq
    rw [hA] at hγ'
    obtain ⟨γ, hγ, rfl⟩ := hγ'
    rw [hcU, MulEquiv.coe_toMonoidHom, ← map_pow, hΦ] at hsq
    rcases h.sq_mem γ hγ hsq with h1 | h1
    · left
      rw [hcR]
      exact Subgroup.mem_map_of_mem _ h1
    · right
      rw [MulEquiv.coe_toMonoidHom, ← map_pow, h1, map_one]
  · intro R₀' hU hR hidx
    have hR₀ : R₀' = (R₀'.map ε.symm.toMonoidHom).map ε.toMonoidHom := by
      rw [Subgroup.map_map]
      convert (Subgroup.map_id R₀').symm
      ext x
      simp
    rw [hR₀] at hU hR hidx ⊢
    have hU' := (Subgroup.map_le_map_iff_of_injective ε.injective).1 hU
    have hR' := (Subgroup.map_le_map_iff_of_injective ε.injective).1 hR
    rw [Subgroup.relIndex_map_map_of_injective _ _ ε.injective] at hidx
    ext γ'
    obtain ⟨γ, rfl⟩ := Φ.surjective γ'
    rw [Set.mem_ofPred_eq, hA, hΦ, RootCenterAutomorphisms.forall_congr_apply, SetLike.mem_coe,
      hcU, hΦ]
    exact Set.ext_iff.1 (h.fix_eq _ hU' hR' hidx) γ
  · rw [hcU]
    have := h.conj_isElementaryAbelian
    exact IsElementaryAbelian.map _
  · rw [hcU, Subgroup.card_map_of_injective Φ.injective, h.card_conj]

theorem even_unitary_root_center_automorphisms_of_mulEquiv [Finite K] (J : HermitianForm 3 K)
    (f : ℕ) (hf : 2 ≤ f) (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (e : F ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (R : Sylow 2 F) (U : Subgroup F)
    (hU : U = (CFSG.omega₁ (G := (R : Subgroup F)) (p := 2)).map (R : Subgroup F).subtype) :
    (∃ ε : ProjectiveSpecialUnitaryMatrixGroup J ≃* F,
      (unitaryCoverRoot J hJ).map ε.toMonoidHom = R ∧
      (unitaryRootCenter J hJ).map ε.toMonoidHom = U ∧
      rootCenterAut (R : Subgroup F) U =
        (rootCenterAut (unitaryCoverRoot J hJ) (unitaryRootCenter J hJ)).map
          (MulAut.congr ε).toMonoidHom) ∧
    (∀ x, x ∈ U ↔ x ∈ (R : Subgroup F) ∧ ∀ y ∈ (R : Subgroup F), x * y = y * x) ∧
    Set.InjOn MulAut.conj ((R : Subgroup F) : Set F) ∧
    (∃ D : Subgroup (MulAut F), (R : Subgroup F).map MulAut.conj ⊓ D = ⊥ ∧
      (R : Subgroup F).map MulAut.conj ⊔ D = rootCenterAut (R : Subgroup F) U ∧
      (((R : Subgroup F).map MulAut.conj).subgroupOf (rootCenterAut (R : Subgroup F) U)).Normal ∧
      Nat.card D = 2 * (2 ^ f + 1) ∧ Nonempty (D ≃* DihedralGroup (2 ^ f + 1))) ∧
    (∀ γ ∈ rootCenterAut (R : Subgroup F) U, γ ^ 2 ∈ U.map MulAut.conj →
      γ ∈ (R : Subgroup F).map MulAut.conj ∨ γ ^ 2 = 1) ∧
    (∀ R₀ : Subgroup F, U ≤ R₀ → R₀ ≤ (R : Subgroup F) → R₀.relIndex (R : Subgroup F) ≤ 2 →
      {γ | γ ∈ rootCenterAut (R : Subgroup F) U ∧ ∀ x ∈ R₀, γ x = x} =
        (U.map MulAut.conj : Set (MulAut F))) ∧
    IsElementaryAbelian 2 (U.map MulAut.conj) ∧ Nat.card (U.map MulAut.conj) = 2 ^ f := by
  have h := unitaryRootCenterAutomorphisms J f hf hcard hfixed hJ
  have : CharP K 2 := charP_two_of_card f hcard
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective _ Subtype.coe_injective
  obtain ⟨ε, hε⟩ := exists_mulEquiv_map_eq e (unitaryCoverSylow J f hf hcard hfixed hJ) R
  have h' : (unitaryRootCenter J hJ).map ε.toMonoidHom =
      (CFSG.omega₁ (G := (unitaryCoverRoot J hJ).map ε.toMonoidHom) (p := 2)).map
        ((unitaryCoverRoot J hJ).map ε.toMonoidHom).subtype := by
    rw [← h.omega_eq, map_omega₁_map]
  change (unitaryCoverRoot J hJ).map ε.toMonoidHom = R at hε
  rw [hε] at h'
  obtain rfl : U = (unitaryRootCenter J hJ).map ε.toMonoidHom := hU.trans h'.symm
  rw [← hε]
  exact ⟨⟨ε, rfl, rfl, rootCenterAut_map ε _ _⟩, h.map ε⟩

end CFSG.ProperTwoGeneratedCore.RootCenter
