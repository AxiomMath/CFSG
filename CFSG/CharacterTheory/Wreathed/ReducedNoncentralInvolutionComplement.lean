module

public import CFSG.CharacterTheory.Wreathed.ReducedNoncentralInvolutionTorus
public import CFSG.CharacterTheory.Wreathed.CyclicWeakClosure

public noncomputable section

namespace CFSG.Wreathed.ReducedInvolution

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.CentralSL2
open CFSG.Wreathed.CentralSL2Abelianization

theorem oddCore_eq_range_inr {C P Q : Type*} [Group C] [Group P] [Group Q] [Finite C]
    (Θ : P × Q ≃* C) (hP : IsPGroup 2 P) (hQ : Odd (Nat.card Q)) :
    CFSG.oddCore C = (Θ.toMonoidHom.comp (MonoidHom.inr P Q)).range := by
  have hker : (Θ.toMonoidHom.comp (MonoidHom.inr P Q)).range =
      ((MonoidHom.fst P Q).comp Θ.symm.toMonoidHom).ker := by
    ext k
    rw [MonoidHom.mem_ker, MonoidHom.mem_range]
    constructor
    · rintro ⟨x, rfl⟩
      simp
    · intro hk
      refine ⟨(Θ.symm k).2, Θ.symm.injective ?_⟩
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
        MonoidHom.inr_apply]
      exact Prod.ext hk.symm rfl
  have hinj : Function.Injective (Θ.toMonoidHom.comp (MonoidHom.inr P Q)) :=
    Θ.injective.comp (Prod.mk_right_injective 1)
  apply le_antisymm
  · intro k hk
    have hodd : Odd (orderOf k) := Odd.of_dvd_nat (CFSG.Wreathed.weakClosure_oddCore_card C)
      (Subgroup.orderOf_dvd_natCard _ hk)
    rw [hker, MonoidHom.mem_ker]
    obtain ⟨n, hn⟩ := hP (Θ.symm k).1
    refine eq_one_of_pow_two_pow hn (Odd.of_dvd_nat hodd ?_)
    calc orderOf (Θ.symm k).1 ∣ orderOf (Θ.symm k) := orderOf_map_dvd (MonoidHom.fst P Q) _
      _ = orderOf k := MulEquiv.orderOf_eq _ _
  · refine le_sSup ⟨?_, ?_⟩
    · rw [hker]
      infer_instance
    · rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
      exact hQ

section Model

variable {F : Type} [Field F] (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
  {Sigma : Subgroup (F ≃+* F)} (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)
  {W : Subgroup (SpecialLinearGroup (Fin 2) F)} {φ : Sigma →* MulAut W}
  (hφ : ∀ σ w, ((φ σ w : W) : SpecialLinearGroup (Fin 2) F) =
    SpecialLinearGroup.map (σ : F ≃+* F).toRingHom w)

@[expose] def complementHom : W ⋊[φ] Sigma →* SemilinearExtension F b m hm heven Sigma hSigma :=
  SemidirectProduct.map ((specialInclusion F b m hm heven).comp W.subtype) (MonoidHom.id Sigma)
    fun σ => MonoidHom.ext fun w => by
      change specialInclusion F b m hm heven ((φ σ w : W) : SpecialLinearGroup (Fin 2) F) =
        fieldAction F b m hm heven Sigma hSigma σ (specialInclusion F b m hm heven w)
      rw [fieldAction_specialInclusion, hφ]
      rfl

theorem complementHom_apply (x : W ⋊[φ] Sigma) :
    complementHom b m hm heven hSigma hφ x =
      SemidirectProduct.inl (specialInclusion F b m hm heven x.left) *
        SemidirectProduct.inr x.right := by
  rw [← SemidirectProduct.inl_left_mul_inr_right (complementHom b m hm heven hSigma hφ x)]
  rfl

theorem complementHom_injective : Function.Injective (complementHom b m hm heven hSigma hφ) := by
  intro x x' h
  have hl := congrArg SemidirectProduct.left h
  have hr := congrArg SemidirectProduct.right h
  exact SemidirectProduct.ext (Subtype.ext (specialInclusion_injective F b m hm heven hl)) hr

theorem range_complementHom :
    (complementHom b m hm heven hSigma hφ).range =
      W.map ((SemidirectProduct.inl : CentralExtension F b m hm heven →*
          SemilinearExtension F b m hm heven Sigma hSigma).comp (specialInclusion F b m hm heven)) ⊔
        (SemidirectProduct.inr : Sigma →*
          SemilinearExtension F b m hm heven Sigma hSigma).range := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [complementHom_apply]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨x.left, x.left.2, rfl⟩)
      (Subgroup.mem_sup_right ⟨x.right, rfl⟩)
  · refine sup_le ?_ ?_
    · rintro _ ⟨w, hw, rfl⟩
      refine ⟨SemidirectProduct.inl ⟨w, hw⟩, ?_⟩
      rw [complementHom_apply, SemidirectProduct.left_inl, SemidirectProduct.right_inl, map_one,
        mul_one]
      rfl
    · rintro _ ⟨σ, rfl⟩
      refine ⟨SemidirectProduct.inr σ, ?_⟩
      rw [complementHom_apply, SemidirectProduct.left_inr, SemidirectProduct.right_inr]
      simp

include hφ in
theorem exists_complement_equiv :
    ∃ Ψ : W ⋊[φ] Sigma ≃* (W.map ((SemidirectProduct.inl : CentralExtension F b m hm heven →*
          SemilinearExtension F b m hm heven Sigma hSigma).comp (specialInclusion F b m hm heven)) ⊔
        (SemidirectProduct.inr : Sigma →* SemilinearExtension F b m hm heven Sigma hSigma).range :
          Subgroup (SemilinearExtension F b m hm heven Sigma hSigma)),
      ∀ x, (Ψ x : SemilinearExtension F b m hm heven Sigma hSigma) =
        SemidirectProduct.inl (specialInclusion F b m hm heven x.left) *
          SemidirectProduct.inr x.right :=
  ⟨(MonoidHom.ofInjective (complementHom_injective b m hm heven hSigma hφ)).trans
      (MulEquiv.subgroupCongr (range_complementHom b m hm heven hSigma hφ)),
    fun x => complementHom_apply b m hm heven hSigma hφ x⟩

include hφ in
theorem exists_centralizer_equiv [Fintype F] (hb : ¬ IsSquare b)
    (hW : ∀ g, g ∈ W ↔ g ∈ Subgroup.centralizer {weyl F} ∧ Odd (orderOf g))
    (P : Subgroup (Subgroup.centralizer {involutionY F b m hm heven})) (hP2 : IsPGroup 2 P)
    (hPfix : ∀ σ : Sigma, ∀ g ∈ P,
      fieldAction F b m hm heven Sigma hSigma σ (g : CentralExtension F b m hm heven) = g)
    (hcard : Nat.card (Subgroup.centralizer {(SemidirectProduct.inl (involutionY F b m hm heven) :
      SemilinearExtension F b m hm heven Sigma hSigma)}) ≤
        Nat.card P * (Nat.card W * Nat.card Sigma)) :
    ∃ Θ : P × (W ⋊[φ] Sigma) ≃* Subgroup.centralizer
        {(SemidirectProduct.inl (involutionY F b m hm heven) :
          SemilinearExtension F b m hm heven Sigma hSigma)},
      ∀ g x, (Θ (g, x) : SemilinearExtension F b m hm heven Sigma hSigma) =
        SemidirectProduct.inl ((g : Subgroup.centralizer {involutionY F b m hm heven}) :
          CentralExtension F b m hm heven) *
          SemidirectProduct.inl (specialInclusion F b m hm heven x.left) *
          SemidirectProduct.inr x.right := by
  have hy := fieldAction_involutionY (m := m) (hm := hm) (heven := heven) (hSigma := hSigma)
  have hWD : ∀ w : W, specialInclusion F b m hm heven w ∈
      Subgroup.centralizer {involutionY F b m hm heven} := fun w =>
    (specialInclusion_mem_centralizer_iff _).mpr ((hW w).mp w.2).1
  let f : P →* SemilinearExtension F b m hm heven Sigma hSigma :=
    SemidirectProduct.inl.comp ((Subgroup.centralizer {involutionY F b m hm heven}).subtype.comp
      P.subtype)
  have hcomm : ∀ (g : P) (x : W ⋊[φ] Sigma),
      Commute (f g) (complementHom b m hm heven hSigma hφ x) := by
    intro g x
    rw [complementHom_apply]
    apply SemidirectProduct.ext
    · change (SemidirectProduct.inl ((g : Subgroup.centralizer {involutionY F b m hm heven}) :
          CentralExtension F b m hm heven) * _).left = (_ * SemidirectProduct.inl
            ((g : Subgroup.centralizer {involutionY F b m hm heven}) :
              CentralExtension F b m hm heven)).left
      simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl,
        SemidirectProduct.right_inl, SemidirectProduct.left_inr, SemidirectProduct.right_inr,
        SemidirectProduct.mul_right, map_one, MulAut.one_apply, mul_one, one_mul,
        hPfix _ _ g.2]
      exact centralizer_involutionY_comm hb g.1.2 (hWD x.left)
    · change (SemidirectProduct.inl _ * _).right = (_ * SemidirectProduct.inl _).right
      simp only [SemidirectProduct.mul_right, SemidirectProduct.right_inl,
        SemidirectProduct.right_inr, mul_one, one_mul]
  let Θ₀ : P × (W ⋊[φ] Sigma) →* SemilinearExtension F b m hm heven Sigma hSigma :=
    f.noncommCoprod (complementHom b m hm heven hSigma hφ) hcomm
  have hΘ₀ : ∀ g x, Θ₀ (g, x) = SemidirectProduct.inl
      ((g : Subgroup.centralizer {involutionY F b m hm heven}) : CentralExtension F b m hm heven) *
        (SemidirectProduct.inl (specialInclusion F b m hm heven x.left) *
          SemidirectProduct.inr x.right) := by
    intro g x
    rw [MonoidHom.noncommCoprod_apply, complementHom_apply]
    rfl
  have hleft : ∀ g x, (Θ₀ (g, x)).left =
      ((g : Subgroup.centralizer {involutionY F b m hm heven}) : CentralExtension F b m hm heven) *
        specialInclusion F b m hm heven x.left := by
    intro g x
    rw [hΘ₀]
    simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, SemidirectProduct.left_inr, map_one, MulAut.one_apply,
      mul_one]
  have hright : ∀ g x, (Θ₀ (g, x)).right = x.right := by
    intro g x
    rw [hΘ₀]
    simp only [SemidirectProduct.mul_right, SemidirectProduct.right_inl,
      SemidirectProduct.right_inr, one_mul]
  have hmem : ∀ z, Θ₀ z ∈ Subgroup.centralizer
      {(SemidirectProduct.inl (involutionY F b m hm heven) :
        SemilinearExtension F b m hm heven Sigma hSigma)} := by
    rintro ⟨g, x⟩
    rw [mem_centralizer_inl_iff hy, hleft]
    exact Subgroup.mul_mem _ g.1.2 (hWD x.left)
  let Θ₁ := Θ₀.codRestrict _ hmem
  have hinj : Function.Injective Θ₁ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨g, x⟩ h
    have h' : Θ₀ (g, x) = 1 := congrArg Subtype.val h
    have hl : ((g : Subgroup.centralizer {involutionY F b m hm heven}) :
        CentralExtension F b m hm heven) * specialInclusion F b m hm heven x.left = 1 := by
      rw [← hleft, h']
      rfl
    have hr : x.right = 1 := by
      rw [← hright g x, h']
      rfl
    have hgw : ((g : Subgroup.centralizer {involutionY F b m hm heven}) :
        CentralExtension F b m hm heven) =
          specialInclusion F b m hm heven ((x.left⁻¹ : W) : SpecialLinearGroup (Fin 2) F) := by
      rw [Subgroup.coe_inv, map_inv]
      exact eq_inv_of_mul_eq_one_left hl
    have hg1 : ((g : Subgroup.centralizer {involutionY F b m hm heven}) :
        CentralExtension F b m hm heven) = 1 := by
      obtain ⟨k, hk⟩ := hP2 g
      refine eq_one_of_pow_two_pow (s := k) ?_ ?_
      · have := congrArg (fun z : P => ((z : Subgroup.centralizer
          {involutionY F b m hm heven}) : CentralExtension F b m hm heven)) hk
        simpa using this
      · rw [hgw, orderOf_injective _ (specialInclusion_injective F b m hm heven)]
        exact ((hW _).mp (x.left⁻¹).2).2
    have hw1 : x.left = 1 := by
      apply Subtype.ext
      apply specialInclusion_injective F b m hm heven
      rw [← one_mul (specialInclusion F b m hm heven x.left), ← hg1, hl, OneMemClass.coe_one,
        map_one]
    have hg1' : g = 1 := Subtype.ext (Subtype.ext hg1)
    rw [hg1', show x = 1 from SemidirectProduct.ext hw1 hr]
    rfl
  have hbij : Function.Bijective Θ₁ :=
    hinj.bijective_of_nat_card_le (by rw [Nat.card_prod, SemidirectProduct.card]; exact hcard)
  refine ⟨MulEquiv.ofBijective Θ₁ hbij, fun g x => ?_⟩
  change Θ₀ (g, x) = _
  rw [hΘ₀, mul_assoc]

end Model

end CFSG.Wreathed.ReducedInvolution
