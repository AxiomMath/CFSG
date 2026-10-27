module

public import CFSG.GH74.GLS.SP.Local.SPLSL2ThreeDescent
public import CFSG.GH74.GLS.SP.Local.SPLSL2Input

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG.GH74.GLS.IVK.L2Torus CFSG.Semidihedral.OddFieldSL2
open CFSG.Semidihedral.MatrixCoverData (slConjugation slConjugation_toGL slConjugation_matrix)
open scoped MatrixGroups

namespace SL2Three

section Diag

noncomputable def diagToUnit (F : Type) [Field F] : diagSub F →* Fˣ where
  toFun x := Units.mk0 ((x : SL2m F).1 0 0) (by
    intro h
    have hdet := sl2_det (x : SL2m F)
    rw [h, x.2.1] at hdet
    simp at hdet)
  map_one' := by
    apply Units.ext
    simp
  map_mul' x y := by
    apply Units.ext
    have h := mul_apply' (x : SL2m F) (y : SL2m F) 0 0
    rw [x.2.1] at h
    simpa using h

theorem diagToUnit_bijective (F : Type) [Field F] : Function.Bijective (diagToUnit F) := by
  constructor
  · intro x y hxy
    have h00 : (x : SL2m F).1 0 0 = (y : SL2m F).1 0 0 := by
      simpa [diagToUnit] using congrArg Units.val hxy
    have hx := sl2_det (x : SL2m F)
    have hy := sl2_det (y : SL2m F)
    rw [x.2.1] at hx
    rw [y.2.1] at hy
    have hne : (x : SL2m F).1 0 0 ≠ 0 := by
      intro h
      rw [h] at hx
      simp at hx
    apply Subtype.ext
    apply sl2_ext h00 (by rw [x.2.1, y.2.1]) (by rw [x.2.2, y.2.2])
    apply mul_left_cancel₀ hne
    rw [h00] at hx ⊢
    linear_combination hx - hy
  · intro t
    refine ⟨⟨dg (t : F) (t⁻¹ : Fˣ) t.mul_inv, dg_mem_diagSub _ _ _⟩, ?_⟩
    apply Units.ext
    simp [diagToUnit, dg_apply_00]

theorem isCyclic_diagSub (F : Type) [Field F] [Finite F] : IsCyclic (diagSub F) :=
  isCyclic_of_injective (diagToUnit F) (diagToUnit_bijective F).1

theorem card_diagSub_eq (F : Type) [Field F] [Finite F] :
    Nat.card (diagSub F) = Nat.card F - 1 := by
  rw [Nat.card_congr (Equiv.ofBijective _ (diagToUnit_bijective F)), Nat.card_units]

theorem normalizer_diagSub_eq (F : Type) [Field F] [Finite F] (h3 : 3 < Nat.card F) :
    normalizer (diagSub F : Set (SL2m F)) = diagSub F ⊔ zpowers (w0 F) := by
  obtain ⟨a, ha0, ha⟩ := exists_sq_ne_one h3
  refine normalizer_diagSub (t := dg a a⁻¹ (mul_inv_cancel₀ ha0)) (dg_mem_diagSub _ _ _) ?_
  rw [dg_apply_00, dg_apply_11]
  intro h
  apply ha
  nth_rewrite 2 [h]
  exact mul_inv_cancel₀ ha0

end Diag

section Torus

variable {F : Type} [Field F]

@[expose] def torus (P : GL (Fin 2) F) : Subgroup SL(2, F) :=
  (diagSub F).map (slConjugation F P).toMonoidHom

theorem mem_torus_iff (P : GL (Fin 2) F) (x : SL(2, F)) :
    x ∈ torus P ↔ ∃ d ∈ diagSub F, slConjugation F P d = x := Iff.rfl

theorem torus_isCyclic [Finite F] (P : GL (Fin 2) F) : IsCyclic (torus P) :=
  (Subgroup.equivMapOfInjective (diagSub F) (slConjugation F P).toMonoidHom
    (slConjugation F P).injective).isCyclic.1 (isCyclic_diagSub F)

theorem torus_card [Finite F] (P : GL (Fin 2) F) : Nat.card (torus P) = Nat.card F - 1 := by
  rw [torus, Subgroup.card_map_of_injective (slConjugation F P).injective, card_diagSub_eq]

theorem normalizer_torus [Finite F] (h3 : 3 < Nat.card F) (P : GL (Fin 2) F) :
    normalizer (torus P : Set SL(2, F)) = torus P ⊔ zpowers (slConjugation F P (w0 F)) := by
  rw [torus, ← Subgroup.map_equiv_normalizer_eq, normalizer_diagSub_eq F h3, Subgroup.map_sup,
    MonoidHom.map_zpowers]
  rfl

theorem torus_inv (P : GL (Fin 2) F) {t : SL(2, F)} (ht : t ∈ torus P) :
    slConjugation F P (w0 F) * t * (slConjugation F P (w0 F))⁻¹ = t⁻¹ := by
  obtain ⟨d, hd, rfl⟩ := ht
  have := w0_inv_diag hd
  have h2 := congrArg (slConjugation F P) this
  simpa [map_mul, map_inv] using h2

theorem minusIdentity_mem_torus (P : GL (Fin 2) F) : minusIdentity F ∈ torus P := by
  have hneg : ((minusIdentity F : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = -1 := by
    rw [minusIdentity_matrix]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]
  refine ⟨minusIdentity F, ?_, ?_⟩
  · refine ⟨?_, ?_⟩ <;> simp [hneg]
  · apply Subtype.ext
    change ((slConjugation F P (minusIdentity F) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = _
    rw [slConjugation_matrix, hneg]
    simp

theorem torus_map {φ : MulAut SL(2, F)} {P : GL (Fin 2) F} {σ : F ≃+* F}
    (hC : ∀ X : SL(2, F), φ (slConjugation F P X) =
      slConjugation F P (Matrix.SpecialLinearGroup.map (σ : F →+* F) X)) {t : SL(2, F)} (ht : t ∈ torus P) :
    φ t ∈ torus P := by
  obtain ⟨d, hd, rfl⟩ := ht
  refine ⟨Matrix.SpecialLinearGroup.map (σ : F →+* F) d, ⟨?_, ?_⟩, (hC d).symm⟩
  · simp [hd.1]
  · simp [hd.2]

end Torus

end SL2Three

open SL2Three

theorem sl2OddAutTorusSL2_three : SL2OddAutTorusSL2 3 := by
  intro F _ _ hodd h5 hmod Q Φ hfix hΦodd
  have h3 : 3 < Nat.card F := by omega
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card F hodd
  obtain ⟨α, β, hαQ, hβQ, hαα, hββ, hβα⟩ := CFSG.GH74.GLS.LU.Local.SL2.exists_anticomm_pair hodd Q
  have hfix' : ∀ φ ∈ Φ, φ α = α ∧ φ β = β := fun φ hφ =>
    ⟨hfix φ hφ α hαQ, hfix φ hφ β hβQ⟩
  have hcyc : IsCyclic Φ := SL2Three.isCyclic_of_fix hodd h3 α β hαα hββ hβα Φ hfix'
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  obtain ⟨P, σ, hC, hαP⟩ := SL2Three.exists_descent hodd h3 hmod α β hαα hββ hβα (g : MulAut SL(2, F))
    (hfix' _ g.2).1 (hfix' _ g.2).2 (hΦodd _ g.2)
  obtain ⟨t, ht⟩ := (SL2Three.torus_isCyclic P).exists_generator
  have hTh : zpowers (t : SL(2, F)) = torus P := by
    apply le_antisymm
    · exact zpowers_le.2 t.2
    · intro x hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (ht ⟨x, hx⟩)
      exact Subgroup.mem_zpowers_iff.2 ⟨k, by rw [← Subgroup.coe_zpow, hk]⟩
  have hord : orderOf (t : SL(2, F)) = Nat.card F - 1 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers ht, SL2Three.torus_card]
  refine ⟨t, α, hord, hαQ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hαα]
    exact minusIdentity_mem_center F
  · rw [hαα]
    exact minusIdentity_ne_one F h2
  · intro k hk
    rw [hTh] at hk
    have := SL2Three.torus_inv P hk
    rwa [← hαP] at this
  · rw [hTh, SL2Three.normalizer_torus h3 P, ← hαP]
  · rw [hTh]
    intro hdvd
    have h1 := Subgroup.relIndex_mul_card (H := torus P ⊓ (Q : Subgroup SL(2, F))) (K := torus P)
    rw [inf_eq_left.2 inf_le_left, SL2Three.torus_card] at h1
    have hmem : minusIdentity F ∈ torus P ⊓ (Q : Subgroup SL(2, F)) :=
      ⟨SL2Three.minusIdentity_mem_torus P, hαα ▸ mul_mem hαQ hαQ⟩
    have h2d : 2 ∣ Nat.card ↥(torus P ⊓ (Q : Subgroup SL(2, F))) := by
      have := Subgroup.orderOf_dvd_natCard (torus P ⊓ (Q : Subgroup SL(2, F))) hmem
      rwa [minusIdentity_orderOf F h2] at this
    obtain ⟨a, ha⟩ := hdvd
    obtain ⟨b, hb⟩ := h2d
    have h4 : 4 ∣ Nat.card F - 1 := ⟨a * b, by rw [← h1, ha, hb]; ring⟩
    omega
  · intro φ hφ k hk
    rw [hTh] at hk ⊢
    have hφ0 : IsOfFinOrder (g : MulAut SL(2, F)) := orderOf_pos_iff.1 (hΦodd _ g.2).pos
    have hmem : φ ∈ Subgroup.zpowers (g : MulAut SL(2, F)) := by
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨φ, hφ⟩)
      exact Subgroup.mem_zpowers_iff.2 ⟨m, by simpa using congrArg Subtype.val hm⟩
    have hpow : ∀ n : ℕ, ∀ k ∈ torus P, ((g : MulAut SL(2, F)) ^ n) k ∈ torus P := by
      intro n
      induction n with
      | zero => intro k hk; simpa using hk
      | succ n ih =>
        intro k hk
        rw [pow_succ', MulAut.mul_apply]
        exact SL2Three.torus_map hC (ih k hk)
    obtain ⟨n, hn⟩ := (hφ0.mem_powers_iff_mem_zpowers).2 hmem
    rw [← hn]
    exact hpow n k hk

end CFSG.GH74.GLS.SP.Local
