module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OModelT

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open Matrix CFSG.Open CFSG.ClassicalGroups.Orthogonal

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

theorem isElemAbelian_range' {A H : Type*} [CommGroup A] [Group H] (f : A →* H) {p : ℕ}
    (hA : ∀ x : A, x ^ p = 1) : IsElemAbelian p f.range := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a, ha⟩ := x.2
    obtain ⟨b, hb⟩ := y.2
    apply Subtype.ext
    show (x : H) * y = y * x
    rw [← ha, ← hb, ← map_mul, ← map_mul, mul_comm]
  · obtain ⟨a, rfl⟩ := hx
    rw [← map_pow, hA, map_one]

theorem exists_unit_order_p (M : NormModel F b c) {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ Nat.card F + 1) :
    ∃ ζ : M.Eˣ, orderOf ζ = p ∧ ζ ∈ rootsOfUnity (Nat.card F + 1) M.E := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hq : 1 ≤ Nat.card F := Nat.card_pos
  have hdvd : p ∣ Nat.card M.Eˣ := by
    rw [Nat.card_units, M.card_E, CFSG.ClassicalGroups.Unitary.sq_sub_one_eq (Nat.card F) hq]
    exact Dvd.dvd.mul_right hpq _
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := M.Eˣ) p hdvd
  refine ⟨ζ, hζ, ?_⟩
  rw [mem_rootsOfUnity]
  exact orderOf_dvd_iff_pow_eq_one.mp (hζ ▸ hpq)

theorem tau_mulVec_symm (M : NormModel F b c)
    (a : ↥(rootsOfUnity (Nat.card F + 1) M.E) × ↥(rootsOfUnity (Nat.card F + 1) M.E) ×
      ↥(rootsOfUnity (Nat.card F + 1) M.E)) (v : Fin 3 → M.E) :
    ((M.τ a : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
      Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ
        M.T.symm v =
      M.T.symm ![((a.1 : M.Eˣ) : M.E) * v 0, ((a.2.1 : M.Eˣ) : M.E) * v 1,
        ((a.2.2 : M.Eˣ) : M.E) * v 2] := by
  apply M.T.injective
  rw [M.τ_apply, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem exists_Zc (M : NormModel F b c) {p : ℕ} (hp : p.Prime) (hpq : p ∣ Nat.card F + 1) :
    ∃ Z : Subgroup ↥(rootsOfUnity (Nat.card F + 1) M.E), (∀ x ∈ Z, x ^ p = 1) ∧ Nat.card Z = p := by
  obtain ⟨ζ, hζ, hζμ⟩ := exists_unit_order_p M hp hpq
  refine ⟨Subgroup.zpowers (⟨ζ, hζμ⟩ : ↥(rootsOfUnity (Nat.card F + 1) M.E)), fun x hx => ?_, ?_⟩
  · have ho : orderOf (⟨ζ, hζμ⟩ : ↥(rootsOfUnity (Nat.card F + 1) M.E)) = p := by
      rw [← hζ]
      exact Subgroup.orderOf_mk ζ hζμ
    exact orderOf_dvd_iff_pow_eq_one.mp (ho ▸ orderOf_dvd_of_mem_zpowers hx)
  · rw [Nat.card_zpowers]
    rw [← hζ]
    exact Subgroup.orderOf_mk ζ hζμ

abbrev MuG (M : NormModel F b c) : Type := ↥(rootsOfUnity (Nat.card F + 1) M.E)

section Homs

variable (M : NormModel F b c)

@[expose] noncomputable def hom0 (Z : Subgroup (MuG M)) :
    (↥Z × ↥Z) →* GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F where
  toFun x := M.τ (1, (x.1 : MuG M), (x.2 : MuG M))
  map_one' := by
    show M.τ _ = 1
    exact M.τ.map_one
  map_mul' x y := by
    rw [← map_mul]
    congr 1 <;> simp [Prod.ext_iff]

@[expose] noncomputable def hom1 (Z : Subgroup (MuG M)) :
    ↥Z →* GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F where
  toFun z := M.τ (1, 1, (z : MuG M))
  map_one' := by
    show M.τ _ = 1
    exact M.τ.map_one
  map_mul' x y := by
    rw [← map_mul]
    congr 1 <;> simp [Prod.ext_iff]

@[expose] noncomputable def hom2 (Z : Subgroup (MuG M)) :
    (↥Z × ↥Z) →* GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F where
  toFun x := M.τ ((x.1 : MuG M), (x.1 : MuG M), (x.2 : MuG M))
  map_one' := by
    show M.τ _ = 1
    exact M.τ.map_one
  map_mul' x y := by
    rw [← map_mul]
    congr 1 <;> simp [Prod.ext_iff]

theorem hom0_apply (Z : Subgroup (MuG M)) (x : ↥Z × ↥Z) :
    hom0 M Z x = M.τ (1, (x.1 : MuG M), (x.2 : MuG M)) := rfl

theorem hom1_apply (Z : Subgroup (MuG M)) (z : ↥Z) : hom1 M Z z = M.τ (1, 1, (z : MuG M)) := rfl

theorem hom2_apply (Z : Subgroup (MuG M)) (x : ↥Z × ↥Z) :
    hom2 M Z x = M.τ ((x.1 : MuG M), (x.1 : MuG M), (x.2 : MuG M)) := rfl

theorem hom0_injective (Z : Subgroup (MuG M)) : Function.Injective (hom0 M Z) := by
  intro x y h
  rw [hom0_apply, hom0_apply] at h
  have h1 := M.τ_injective h
  have e1 : ((x.1 : MuG M)) = (y.1 : MuG M) := congrArg (fun t => t.2.1) h1
  have e2 : ((x.2 : MuG M)) = (y.2 : MuG M) := congrArg (fun t => t.2.2) h1
  exact Prod.ext (Subtype.ext e1) (Subtype.ext e2)

theorem hom1_injective (Z : Subgroup (MuG M)) : Function.Injective (hom1 M Z) := by
  intro x y h
  rw [hom1_apply, hom1_apply] at h
  have h1 := M.τ_injective h
  exact Subtype.ext (congrArg (fun t => t.2.2) h1)

theorem hom2_injective (Z : Subgroup (MuG M)) : Function.Injective (hom2 M Z) := by
  intro x y h
  rw [hom2_apply, hom2_apply] at h
  have h1 := M.τ_injective h
  have e1 : ((x.1 : MuG M)) = (y.1 : MuG M) := congrArg (fun t => t.1) h1
  have e2 : ((x.2 : MuG M)) = (y.2 : MuG M) := congrArg (fun t => t.2.2) h1
  exact Prod.ext (Subtype.ext e1) (Subtype.ext e2)

end Homs

section Subgroups

variable (M : NormModel F b c) {p : ℕ}

theorem exists_E0 (hp : p.Prime) (hpq : p ∣ Nat.card F + 1) :
    ∃ E : Subgroup (GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F),
      E ≤ StatedOmega (StatedQuadMinus 3 F b c) ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      ∀ g ∈ E, ∀ z : M.E, ((g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
        Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ
          M.T.symm ![z, 0, 0] = M.T.symm ![z, 0, 0] := by
  obtain ⟨Z, hZp, hZc⟩ := exists_Zc M hp hpq
  refine ⟨(hom0 M Z).range, ?_, isElemAbelian_range' (hom0 M Z) ?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact M.τ_mem _
  · intro x
    exact Prod.ext (Subtype.ext (by simpa using hZp _ x.1.2)) (Subtype.ext (by simpa using hZp _ x.2.2))
  · rw [← Nat.card_congr (MonoidHom.ofInjective (hom0_injective M Z)).toEquiv, Nat.card_prod, hZc,
      sq]
  · rintro _ ⟨x, rfl⟩ z
    rw [hom0_apply, tau_mulVec_symm]
    congr 1
    funext i
    fin_cases i <;> simp

theorem exists_E1 (hp : p.Prime) (hpq : p ∣ Nat.card F + 1) :
    ∃ E : Subgroup (GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F),
      E ≤ StatedOmega (StatedQuadMinus 3 F b c) ∧ IsElemAbelian p E ∧ Nat.card E = p ∧
      ∀ g ∈ E, ∀ z z' : M.E, ((g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
        Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ
          M.T.symm ![z, z', 0] = M.T.symm ![z, z', 0] := by
  obtain ⟨Z, hZp, hZc⟩ := exists_Zc M hp hpq
  refine ⟨(hom1 M Z).range, ?_, isElemAbelian_range' (hom1 M Z) ?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact M.τ_mem _
  · intro x
    exact Subtype.ext (by simpa using hZp _ x.2)
  · rw [← Nat.card_congr (MonoidHom.ofInjective (hom1_injective M Z)).toEquiv, hZc]
  · rintro _ ⟨x, rfl⟩ z z'
    rw [hom1_apply, tau_mulVec_symm]
    congr 1
    funext i
    fin_cases i <;> simp

theorem exists_E2 (hp : p.Prime) (hpq : p ∣ Nat.card F + 1) :
    ∃ E : Subgroup (GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F),
      E ≤ StatedOmega (StatedQuadMinus 3 F b c) ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      ∀ g ∈ E, ∀ x : OW F, M.T x 0 = M.T x 1 → M.T x 2 = 0 →
        (M.T (((g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
          Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ x) 0 =
          M.T (((g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
          Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ x) 1 ∧
        M.T (((g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
          Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ x) 2 = 0) := by
  obtain ⟨Z, hZp, hZc⟩ := exists_Zc M hp hpq
  refine ⟨(hom2 M Z).range, ?_, isElemAbelian_range' (hom2 M Z) ?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact M.τ_mem _
  · intro x
    exact Prod.ext (Subtype.ext (by simpa using hZp _ x.1.2)) (Subtype.ext (by simpa using hZp _ x.2.2))
  · rw [← Nat.card_congr (MonoidHom.ofInjective (hom2_injective M Z)).toEquiv, Nat.card_prod, hZc,
      sq]
  · rintro _ ⟨x, rfl⟩ w h0 h2
    rw [hom2_apply, M.τ_apply]
    simp [h0, h2]

end Subgroups

end CFSG.LocalAnalysis.RankThreeUC
