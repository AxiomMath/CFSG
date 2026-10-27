module

public import CFSG.ClassicalInvolution.Asc77.AscT7S2RA
public import CFSG.ClassicalInvolution.ModelFacts.Orth15Aut

public section

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.FrameVertex
  CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.LieType.Universal CFSG.Assembly.LowTwoRank

namespace CFSG.ClassicalInvolution.RouteD.TWT4

section Hol

@[expose] noncomputable def restrictAut {X : Type} [Group X] (L : Subgroup X) [Finite L]
    (σ : X ≃* X) (hσ : ∀ l ∈ L, σ l ∈ L) : MulAut ↥L :=
  MulEquiv.ofBijective ((σ.toMonoidHom.comp L.subtype).codRestrict L (fun l => hσ l l.2))
    (by
      have hinj : Function.Injective ((σ.toMonoidHom.comp L.subtype).codRestrict L
          (fun l => hσ l l.2)) := by
        intro a b hab
        apply Subtype.ext
        exact σ.injective (congrArg Subtype.val hab)
      exact ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩)

end Hol

section Vac

open SemidirectProduct in
theorem sq_aut_of_twinOuterVac {t : StatedLieTag} {M : LieUniversal} (hV : TwinOuterVacOn t M)
    {X : Type} [Group X] [Finite X] (ψ : M.K →* X) {R R' : Subgroup M.K} {x x' : M.K}
    (hpair : TwinPairOn t M ψ R R' x x') (σ : X ≃* X) (hσL : ∀ l ∈ ψ.range, σ l ∈ ψ.range)
    (hσR : ∀ r ∈ R, σ (ψ r) = ψ r) (hσR' : ∀ r ∈ R', σ (ψ r) = ψ r)
    (hσ4 : ∀ l ∈ ψ.range, σ (σ (σ (σ l))) = l) :
    (∀ l ∈ ψ.range, σ (σ l) = l) ∨ (∀ l ∈ ψ.range, σ (σ l) = ψ x * l * (ψ x)⁻¹) := by
  classical
  set L : Subgroup X := ψ.range with hL
  set σL : MulAut ↥L := restrictAut L σ hσL with hσLdef
  have hσLc : ∀ l : ↥L, ((σL l : ↥L) : X) = σ l := fun l => rfl
  let H' := ↥L ⋊[MonoidHom.id (MulAut ↥L)] MulAut ↥L
  have : Finite H' := Finite.of_equiv _
    (SemidirectProduct.equivProd (N := ↥L) (G := MulAut ↥L) (φ := MonoidHom.id (MulAut ↥L))).symm
  let ψ' : M.K →* H' := (inl : ↥L →* H').comp ψ.rangeRestrict
  have hψ'inl : ∀ k, ψ' k = inl (ψ.rangeRestrict k) := fun k => rfl
  have hψ'range : ∀ l : ↥L, (inl l : H') ∈ ψ'.range := by
    intro l
    obtain ⟨k, hk⟩ := ψ.rangeRestrict_surjective l
    exact ⟨k, by rw [hψ'inl, hk]⟩
  have hrange_eq : ψ'.range = (inl : ↥L →* H').range := by
    ext y
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨l, rfl⟩
      exact hψ'range l
  have hnorm : ψ'.range.Normal := by
    rw [hrange_eq, SemidirectProduct.range_inl_eq_ker_rightHom]
    infer_instance
  have hn : (inr σL : H') ∈ Subgroup.normalizer (ψ'.range : Set H') := by
    have := hnorm
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top _
  have hconj : ∀ l : ↥L, (inr σL : H') * inl l * (inr σL : H')⁻¹ = inl (σL l) := by
    intro l
    have := SemidirectProduct.inl_aut (φ := MonoidHom.id (MulAut ↥L)) σL l
    rw [map_inv] at this
    exact this.symm
  have hpair' : TwinPairOn t M ψ' R R' x x' := by
    refine ⟨?_, hpair.mem, hpair.mem', hpair.ne, hpair.comm, hpair.hx, hpair.hx2, hpair.hx1,
      hpair.hx', hpair.hx'2, hpair.hx'1, ?_⟩
    · intro k hk
      apply hpair.ker
      rw [MonoidHom.mem_ker] at hk ⊢
      have h1 : (inl (ψ.rangeRestrict k) : H') = inl 1 := by
        rw [← hψ'inl, hk, map_one]
      have h2 := SemidirectProduct.inl_injective h1
      have h3 := congrArg Subtype.val h2
      exact h3
    · rw [hψ'inl, hψ'inl]
      exact congrArg inl (Subtype.ext hpair.same)
  set v : ↥(inducedAutOn ψ'.range) := toInducedAutOn ψ'.range ⟨inr σL, hn⟩ with hv
  have hv_apply : ∀ l : ↥L,
      ((v : MulAut ↥ψ'.range) ⟨inl l, hψ'range l⟩ : H') = inl (σL l) := by
    intro l
    rw [hv, toInducedAutOn_apply_coe]
    exact hconj l
  have hvv_apply : ∀ l : ↥L,
      (((v * v : ↥(inducedAutOn ψ'.range)) : MulAut ↥ψ'.range) ⟨inl l, hψ'range l⟩ : H') =
        inl (σL (σL l)) := by
    intro l
    have h1 : (v : MulAut ↥ψ'.range) ⟨inl l, hψ'range l⟩ = ⟨inl (σL l), hψ'range _⟩ :=
      Subtype.ext (hv_apply l)
    show ((v : MulAut ↥ψ'.range) ((v : MulAut ↥ψ'.range) ⟨inl l, hψ'range l⟩) : H') = _
    rw [h1]
    exact hv_apply (σL l)
  have hcommv : ∀ r : M.K, σ (ψ r) = ψ r → v * innerHom ψ' r = innerHom ψ' r * v := by
    intro r hr
    rw [innerHom_apply, hv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show (inr σL : H') * ψ' r = ψ' r * inr σL
    rw [hψ'inl, ← mul_inv_eq_iff_eq_mul, hconj]
    exact congrArg inl (Subtype.ext hr)
  have hv4 : v * v * (v * v) = 1 := by
    rw [hv, ← map_mul, ← map_mul]
    have : (⟨inr σL, hn⟩ * ⟨inr σL, hn⟩ * (⟨inr σL, hn⟩ * ⟨inr σL, hn⟩) :
        ↥(Subgroup.normalizer (ψ'.range : Set H'))) = 1 := by
      apply Subtype.ext
      show (inr σL : H') * inr σL * (inr σL * inr σL) = 1
      rw [← map_mul, ← map_mul]
      have h4 : σL * σL * (σL * σL) = 1 := by
        ext l
        show σ (σ (σ (σ l))) = l
        exact hσ4 l l.2
      rw [h4, map_one]
    rw [this, map_one]
  rcases hV H' ψ' R R' x x' hpair' v (fun r hr => hcommv r (hσR r hr))
    (fun r hr => hcommv r (hσR' r hr)) hv4 with h | h
  · left
    intro l hl
    have h1 := congrArg (fun w : ↥(inducedAutOn ψ'.range) =>
      ((w : MulAut ↥ψ'.range) ⟨inl ⟨l, hl⟩, hψ'range _⟩ : H')) h
    simp only [hvv_apply] at h1
    have h2 := SemidirectProduct.inl_injective (h1.trans (by rfl))
    exact congrArg Subtype.val h2
  · right
    intro l hl
    have h1 := congrArg (fun w : ↥(inducedAutOn ψ'.range) =>
      ((w : MulAut ↥ψ'.range) ⟨inl ⟨l, hl⟩, hψ'range _⟩ : H')) h
    simp only [hvv_apply] at h1
    rw [innerHom_apply, toInducedAutOn_apply_coe] at h1
    have h3 : (ψ' x : H') * inl ⟨l, hl⟩ * (ψ' x)⁻¹ =
        inl (ψ.rangeRestrict x * ⟨l, hl⟩ * (ψ.rangeRestrict x)⁻¹) := by
      rw [hψ'inl]
      simp only [map_mul, map_inv]
    rw [h3] at h1
    have h2 := SemidirectProduct.inl_injective h1
    exact congrArg Subtype.val h2

end Vac

end CFSG.ClassicalInvolution.RouteD.TWT4
