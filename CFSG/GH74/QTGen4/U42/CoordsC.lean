module

public import CFSG.GH74.QTGen4.U42.Coords

public section

namespace CFSG.GH74.QTGen4.U42

open CFSG.Quasithin.A5Model CFSG.QuasithinUnique CFSG.Quasithin.H13.A5

namespace CoordData

variable {M : Type*} [Group M] (C : CoordData M)

theorem exists_dec {A : Subgroup M} (hA' : C.V ⊔ A = ⊤) (g : M) :
    ∃ v ∈ C.V, ∃ a ∈ A, v * a = g := by
  have := C.hV
  have htop : g ∈ C.V ⊔ A := by
    rw [hA']
    exact Subgroup.mem_top _
  obtain ⟨v, hv, a, ha, h⟩ := Subgroup.mem_sup_of_normal_left.mp htop
  exact ⟨v, hv, a, ha, h⟩

theorem dec_unique {A : Subgroup M} (hA : A ⊓ C.V = ⊥) {v v' a a' : M}
    (hv : v ∈ C.V) (ha : a ∈ A) (hv' : v' ∈ C.V) (ha' : a' ∈ A)
    (h : v * a = v' * a') : v = v' ∧ a = a' := by
  have hx : v'⁻¹ * v = a' * a⁻¹ := by
    calc v'⁻¹ * v = v'⁻¹ * (v * a) * a⁻¹ := by group
      _ = v'⁻¹ * (v' * a') * a⁻¹ := by rw [h]
      _ = a' * a⁻¹ := by group
  have hxA : v'⁻¹ * v ∈ A := by
    rw [hx]
    exact A.mul_mem ha' (A.inv_mem ha)
  have hxV : v'⁻¹ * v ∈ C.V := C.V.mul_mem (C.V.inv_mem hv') hv
  have hxb : v'⁻¹ * v ∈ A ⊓ C.V := ⟨hxA, hxV⟩
  rw [hA, Subgroup.mem_bot] at hxb
  have hvv : v' = v := inv_mul_eq_one.mp hxb
  rw [hvv] at h
  exact ⟨hvv.symm, mul_left_cancel h⟩

end CoordData

theorem CoordData.equiv_of_complement {M : Type*} [Group M] [Finite M] (C : CoordData M)
    (A : Subgroup M) (hA : A ⊓ C.V = ⊥) (hA' : C.V ⊔ A = ⊤) :
    ∃ e : M ≃* Mof C.ρ.range,
      (∀ v : ↥C.V, ((e (v : M) : Mof C.ρ.range) : Mc) = SemidirectProduct.inl (C.ψ v)) ∧
      ∀ m : M, ((e m : Mof C.ρ.range) : Mc).right = C.ρ m := by
  choose vf hvf af haf hprod using C.exists_dec hA'
  have key : ∀ (g v a : M) (hv : v ∈ C.V) (ha : a ∈ A), v * a = g → vf g = v := by
    intro g v a hv ha hva
    exact (C.dec_unique hA (hvf g) (haf g) hv ha ((hprod g).trans hva.symm)).1
  have rho_af : ∀ g : M, C.ρ (af g) = C.ρ g := by
    intro g
    have h := C.ρ.map_mul (vf g) (af g)
    rw [hprod g, C.rho_eq_one_of_mem (hvf g), one_mul] at h
    exact h.symm
  have h_one : (⟨C.ψ ⟨vf 1, hvf 1⟩, C.ρ 1⟩ : Mc) = 1 := by
    have h1 : vf 1 = 1 := key 1 1 1 C.V.one_mem A.one_mem (mul_one 1)
    refine SemidirectProduct.ext ?_ ?_
    · show C.ψ ⟨vf 1, hvf 1⟩ = 1
      rw [show (⟨vf 1, hvf 1⟩ : ↥C.V) = 1 from Subtype.ext h1, map_one]
    · show C.ρ 1 = 1
      exact map_one _
  have h_mul : ∀ g h : M, (⟨C.ψ ⟨vf (g * h), hvf (g * h)⟩, C.ρ (g * h)⟩ : Mc) =
      ⟨C.ψ ⟨vf g, hvf g⟩, C.ρ g⟩ * ⟨C.ψ ⟨vf h, hvf h⟩, C.ρ h⟩ := by
    intro g h
    have hw : af g * vf h * (af g)⁻¹ ∈ C.V := C.hV.conj_mem _ (hvf h) _
    have hc : C.ψ ⟨af g * vf h * (af g)⁻¹, hw⟩ = pact (C.ρ g) (C.ψ ⟨vf h, hvf h⟩) := by
      rw [← rho_af g]
      exact C.conj_ψ (af g) ⟨vf h, hvf h⟩
    have hdec : (vf g * (af g * vf h * (af g)⁻¹)) * (af g * af h) = g * h := by
      calc (vf g * (af g * vf h * (af g)⁻¹)) * (af g * af h)
          = (vf g * af g) * (vf h * af h) := by group
        _ = g * h := by rw [hprod g, hprod h]
    have hk := key (g * h) (vf g * (af g * vf h * (af g)⁻¹)) (af g * af h)
      (C.V.mul_mem (hvf g) hw) (A.mul_mem (haf g) (haf h)) hdec
    have hl : C.ψ ⟨vf (g * h), hvf (g * h)⟩ =
        C.ψ ⟨vf g, hvf g⟩ * pact (C.ρ g) (C.ψ ⟨vf h, hvf h⟩) := by
      rw [← hc, ← map_mul]
      congr 1
      exact Subtype.ext hk
    refine SemidirectProduct.ext ?_ ?_
    · show C.ψ ⟨vf (g * h), hvf (g * h)⟩ = C.ψ ⟨vf g, hvf g⟩ * pact (C.ρ g) (C.ψ ⟨vf h, hvf h⟩)
      exact hl
    · show C.ρ (g * h) = C.ρ g * C.ρ h
      exact map_mul C.ρ g h
  let Φ : M →* Mc :=
    { toFun := fun g => ⟨C.ψ ⟨vf g, hvf g⟩, C.ρ g⟩
      map_one' := h_one
      map_mul' := h_mul }
  have hΦ : ∀ g : M, Φ g = ⟨C.ψ ⟨vf g, hvf g⟩, C.ρ g⟩ := fun g => rfl
  have hR : ∀ g : M, Φ g ∈ Mof C.ρ.range := fun g => mem_Mof.mpr (MonoidHom.mem_range.mpr ⟨g, rfl⟩)
  let Ψ : M →* ↥(Mof C.ρ.range) := Φ.codRestrict (Mof C.ρ.range) hR
  have hinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hΦg : Φ g = 1 := congrArg Subtype.val hg
    have h2 : (Φ g).right = (1 : Mc).right := congrArg SemidirectProduct.right hΦg
    have h3 : (Φ g).left = (1 : Mc).left := congrArg SemidirectProduct.left hΦg
    have hρg : C.ρ g = 1 := h2
    have hl : C.ψ ⟨vf g, hvf g⟩ = 1 := h3
    have hgV : g ∈ C.V := C.mem_of_rho_eq_one hρg
    have hvg : vf g = g := key g g 1 hgV A.one_mem (mul_one g)
    have hpt : (⟨vf g, hvf g⟩ : ↥C.V) = 1 := C.ψ.injective (by rw [hl, map_one])
    have hv1 : vf g = 1 := congrArg Subtype.val hpt
    exact hvg.symm.trans hv1
  have hsurj : Function.Surjective Ψ := by
    rintro ⟨x, hx⟩
    have hxR : x.right ∈ C.ρ.range := mem_Mof.mp hx
    obtain ⟨g', hg'⟩ := MonoidHom.mem_range.mp hxR
    obtain ⟨v, hv⟩ : ∃ v : ↥C.V, C.ψ v = x.left * (C.ψ ⟨vf g', hvf g'⟩)⁻¹ :=
      ⟨C.ψ.symm _, C.ψ.apply_symm_apply _⟩
    refine ⟨(v : M) * g', Subtype.ext ?_⟩
    show Φ ((v : M) * g') = x
    have hk : vf ((v : M) * g') = (v : M) * vf g' :=
      key ((v : M) * g') ((v : M) * vf g') (af g') (C.V.mul_mem v.2 (hvf g')) (haf g')
        (by rw [mul_assoc, hprod g'])
    refine SemidirectProduct.ext ?_ ?_
    · show C.ψ ⟨vf ((v : M) * g'), hvf _⟩ = x.left
      rw [show (⟨vf ((v : M) * g'), hvf _⟩ : ↥C.V) = v * ⟨vf g', hvf g'⟩ from Subtype.ext hk,
        map_mul, hv, inv_mul_cancel_right]
    · show C.ρ ((v : M) * g') = x.right
      rw [map_mul, C.rho_eq_one_of_mem v.2, one_mul, hg']
  refine ⟨MulEquiv.ofBijective Ψ ⟨hinj, hsurj⟩, ?_, ?_⟩
  · intro v
    show Φ (v : M) = SemidirectProduct.inl (C.ψ v)
    refine SemidirectProduct.ext ?_ ?_
    · show C.ψ ⟨vf (v : M), hvf _⟩ = C.ψ v
      rw [show (⟨vf (v : M), hvf _⟩ : ↥C.V) = v from
        Subtype.ext (key (v : M) v 1 v.2 A.one_mem (mul_one _))]
    · show C.ρ (v : M) = 1
      exact C.rho_eq_one_of_mem v.2
  · intro m
    rfl

end CFSG.GH74.QTGen4.U42
