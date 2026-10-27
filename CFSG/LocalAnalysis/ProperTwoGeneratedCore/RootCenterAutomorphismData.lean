module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RootCenterAutomorphismBasic

public section

namespace CFSG.ProperTwoGeneratedCore.RootCenter

variable {F F' : Type*} [Group F] [Group F']

theorem isElementaryAbelian_of_isElemAbelian {p : ℕ} {U : Subgroup F}
    (hU : CFSG.Open.IsElemAbelian p U) : IsElementaryAbelian p U where
  toIsMulCommutative := hU.1
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x =>
    Subtype.ext (by rw [Subgroup.coe_pow]; exact hU.2 x x.2)

theorem map_mul_mulAut (α β : MulAut F) (H : Subgroup F) :
    H.map (α * β).toMonoidHom = (H.map β.toMonoidHom).map α.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

@[expose] def rootCenterAut (R U : Subgroup F) : Subgroup (MulAut F) where
  carrier := {γ | R.map γ.toMonoidHom = R ∧ ∀ u ∈ U, γ u = u}
  mul_mem' := by
    rintro γ₁ γ₂ ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩
    refine ⟨by rw [map_mul_mulAut, h₂, h₁], fun u hu => ?_⟩
    rw [MulAut.mul_apply, h₂' u hu, h₁' u hu]
  one_mem' := ⟨Subgroup.map_id R, fun _ _ => rfl⟩
  inv_mem' := by
    rintro γ ⟨h, h'⟩
    refine ⟨?_, fun u hu => (MulEquiv.symm_apply_eq γ).2 (h' u hu).symm⟩
    conv_lhs => rw [← h]
    rw [← map_mul_mulAut, inv_mul_cancel]
    exact Subgroup.map_id R

theorem mem_rootCenterAut {R U : Subgroup F} {γ : MulAut F} :
    γ ∈ rootCenterAut R U ↔ R.map γ.toMonoidHom = R ∧ ∀ u ∈ U, γ u = u :=
  Iff.rfl

theorem map_conj_of_mem {H : Subgroup F} {r : F} (hr : r ∈ H) :
    H.map (MulAut.conj r).toMonoidHom = H := by
  ext x
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  refine ⟨fun h => ?_, fun h => H.mul_mem (H.mul_mem (H.inv_mem hr) h) hr⟩
  simpa [mul_assoc] using H.mul_mem (H.mul_mem hr h) (H.inv_mem hr)

structure RootCenterAutomorphisms (R U : Subgroup F) (q : ℕ) : Prop where
  mem_iff : ∀ x, x ∈ U ↔ x ∈ R ∧ ∀ y ∈ R, x * y = y * x
  isElementaryAbelian : IsElementaryAbelian 2 U
  card_eq : Nat.card U = q
  sq_mem : ∀ x ∈ R, x ^ 2 ∈ U
  injOn_conj : Set.InjOn MulAut.conj (R : Set F)
  aut_eq : {γ : MulAut F | R.map γ.toMonoidHom = R ∧ ∀ u ∈ U, γ u = u} =
    (R.map MulAut.conj : Set (MulAut F))
  fix_eq : ∀ R₀ : Subgroup F, U ≤ R₀ → R₀ ≤ R → R₀.relIndex R ≤ 2 →
    {γ : MulAut F | (R.map γ.toMonoidHom = R ∧ ∀ u ∈ U, γ u = u) ∧ ∀ x ∈ R₀, γ x = x} =
      (U.map MulAut.conj : Set (MulAut F))
  conj_isElementaryAbelian : IsElementaryAbelian 2 (U.map MulAut.conj)
  card_conj : Nat.card (U.map MulAut.conj) = q

namespace RootCenterAutomorphisms

theorem of_core {R U : Subgroup F} {q : ℕ} (hmem : ∀ x, x ∈ U ↔ x ∈ R ∧ ∀ y ∈ R, x * y = y * x)
    (hU : IsElementaryAbelian 2 U) (hcard : Nat.card U = q) (hsq : ∀ x ∈ R, x ^ 2 ∈ U)
    (hinj : Set.InjOn MulAut.conj (R : Set F))
    (haut : {γ : MulAut F | R.map γ.toMonoidHom = R ∧ ∀ u ∈ U, γ u = u} =
      (R.map MulAut.conj : Set (MulAut F)))
    (hfix : ∀ R₀ : Subgroup F, U ≤ R₀ → R₀ ≤ R → R₀.relIndex R ≤ 2 →
      {γ : MulAut F | (R.map γ.toMonoidHom = R ∧ ∀ u ∈ U, γ u = u) ∧ ∀ x ∈ R₀, γ x = x} =
        (U.map MulAut.conj : Set (MulAut F))) :
    RootCenterAutomorphisms R U q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUR : U ≤ R := fun x hx => ((hmem x).1 hx).1
  refine ⟨hmem, hU, hcard, hsq, hinj, haut, hfix, IsElementaryAbelian.map _, ?_⟩
  rw [← hcard]
  refine (Nat.card_image_of_injOn (hinj.mono hUR)).trans ?_
  rfl

variable {R U : Subgroup F} {q : ℕ}

theorem map_congr (ε : F ≃* F') (γ : MulAut F) (H : Subgroup F) :
    (H.map ε.toMonoidHom).map (MulAut.congr ε γ).toMonoidHom =
      (H.map γ.toMonoidHom).map ε.toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp

theorem forall_congr_apply (ε : F ≃* F') (γ : MulAut F) (H : Subgroup F) :
    (∀ x ∈ H.map ε.toMonoidHom, MulAut.congr ε γ x = x) ↔ ∀ x ∈ H, γ x = x := by
  constructor
  · intro h x hx
    have := h (ε x) (Subgroup.mem_map_of_mem _ hx)
    simpa using this
  · intro h x hx
    rw [Subgroup.mem_map_equiv] at hx
    simp [h _ hx]

theorem congr_mem_map_conj (ε : F ≃* F') (γ : MulAut F) (H : Subgroup F) :
    MulAut.congr ε γ ∈ (H.map ε.toMonoidHom).map MulAut.conj ↔ γ ∈ H.map MulAut.conj := by
  constructor
  · rintro ⟨_, ⟨r, hr, rfl⟩, h⟩
    refine ⟨r, hr, (MulAut.congr ε).injective ?_⟩
    rw [← h]
    exact congr_conj ε r
  · rintro ⟨r, hr, rfl⟩
    exact ⟨ε r, Subgroup.mem_map_of_mem _ hr, (congr_conj ε r).symm⟩

theorem map (h : RootCenterAutomorphisms R U q) (ε : F ≃* F') :
    RootCenterAutomorphisms (R.map ε.toMonoidHom) (U.map ε.toMonoidHom) q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.isElementaryAbelian
  have hA : ∀ γ : MulAut F, ((R.map ε.toMonoidHom).map (MulAut.congr ε γ).toMonoidHom =
      R.map ε.toMonoidHom ∧ ∀ u ∈ U.map ε.toMonoidHom, MulAut.congr ε γ u = u) ↔
        (R.map γ.toMonoidHom = R ∧ ∀ u ∈ U, γ u = u) := fun γ => by
    rw [map_congr, forall_congr_apply]
    exact and_congr_left' ⟨fun h' => Subgroup.map_injective ε.injective h', fun h' => by rw [h']⟩
  have hsurj : ∀ γ' : MulAut F', ∃ γ : MulAut F, MulAut.congr ε γ = γ' :=
    (MulAut.congr ε).surjective
  apply of_core
  · intro x
    rw [Subgroup.mem_map_equiv, h.mem_iff, Subgroup.mem_map_equiv]
    refine and_congr_right fun _ => ⟨fun H y hy => ?_, fun H y hy => ?_⟩
    · apply ε.symm.injective
      rw [map_mul, map_mul]
      exact H _ (Subgroup.mem_map_equiv.1 hy)
    · have := congrArg ε.symm (H (ε y) (Subgroup.mem_map_of_mem _ hy))
      rwa [map_mul, map_mul, MulEquiv.symm_apply_apply] at this
  · exact IsElementaryAbelian.map _
  · rw [Subgroup.card_map_of_injective ε.injective, h.card_eq]
  · intro x hx
    rw [Subgroup.mem_map_equiv, map_pow]
    exact h.sq_mem _ (Subgroup.mem_map_equiv.1 hx)
  · rintro _ ⟨r, hr, rfl⟩ _ ⟨s, hs, rfl⟩ hrs
    have h' : MulAut.conj r = MulAut.conj s := (MulAut.congr ε).injective (by
      rw [congr_conj, congr_conj]
      exact hrs)
    exact congrArg ε (h.injOn_conj hr hs h')
  · ext γ'
    obtain ⟨γ, rfl⟩ := hsurj γ'
    rw [Set.mem_ofPred_eq, hA, SetLike.mem_coe, congr_mem_map_conj]
    exact Set.ext_iff.1 h.aut_eq γ
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
    obtain ⟨γ, rfl⟩ := hsurj γ'
    rw [Set.mem_ofPred_eq, hA, forall_congr_apply, SetLike.mem_coe, congr_mem_map_conj]
    exact Set.ext_iff.1 (h.fix_eq _ hU' hR' hidx) γ

theorem of_sylow {M G : Type*} [Group M] [Group G] [Finite M] (e : G ≃* M) (P : Sylow 2 M)
    (h : RootCenterAutomorphisms (P : Subgroup M)
      ((CFSG.omega₁ (G := (P : Subgroup M)) (p := 2)).map (P : Subgroup M).subtype) q)
    (R : Sylow 2 G) :
    RootCenterAutomorphisms (R : Subgroup G)
      ((CFSG.omega₁ (G := (R : Subgroup G)) (p := 2)).map (R : Subgroup G).subtype) q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ε, hε⟩ := exists_mulEquiv_map_eq e P R
  have h' := h.map ε
  rw [map_omega₁_map, hε] at h'
  exact h'

end RootCenterAutomorphisms

end CFSG.ProperTwoGeneratedCore.RootCenter
