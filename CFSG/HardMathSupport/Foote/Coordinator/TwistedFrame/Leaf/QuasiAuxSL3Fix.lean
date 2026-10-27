module

public import CFSG.RankThree.Classical.SteinbergBYExchangedSL3

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.QuasiSL3

open Matrix CFSG.RankThree.Classical2
open scoped MatrixGroups commutatorElement

variable {Ω : Type} [Field Ω] {ℓ f : ℕ} {k : Type} [Field k] [Algebra k Ω]

local notation "M₃" => Matrix (Fin 3) (Fin 3) Ω

theorem exchange_fixed_iff_range (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hk : Nat.card k = ℓ ^ f)
    [IsAlgClosure k Ω] (σ : Ω →+* Ω) (hσ : ∀ c, σ c = c ^ ℓ ^ f) (a b : SL(3, Ω)) :
    ∃ F : Subfield Ω, (∀ c : Ω, c ∈ F ↔ c ^ (ℓ ^ f) ^ 2 = c) ∧ Nat.card F = (ℓ ^ f) ^ 2 ∧
      ∃ ρ' : SL(3, F) →* SL(3, Ω) × SL(3, Ω), ∀ s : SL(3, Ω) × SL(3, Ω),
        (a * SpecialLinearGroup.map σ s.2 * a⁻¹, b * SpecialLinearGroup.map σ s.1 * b⁻¹) = s ↔
          s ∈ ρ'.range := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact (pow_pos hℓ.pos f).ne')
  have : Fintype k := Fintype.ofFinite k
  have : CharP k ℓ := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hk])
  have : CharP Ω ℓ := charP_of_injective_algebraMap (algebraMap k Ω).injective ℓ
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  set q := ℓ ^ f with hq
  have hq1 : 1 ≤ q := Nat.one_le_pow _ _ hℓ.pos
  set F : Subfield Ω := (iterateFrobenius Ω ℓ (2 * f)).eqLocusField (RingHom.id Ω) with hFdef
  have hq2 : q ^ 2 = ℓ ^ (2 * f) := by rw [hq, ← pow_mul, mul_comm]
  have hF2 : ∀ c : Ω, c ∈ F ↔ c ^ ℓ ^ (2 * f) = c := fun c => by
    rw [hFdef, RingHom.mem_eqLocusField, iterateFrobenius_def, RingHom.id_apply]
  have hF : ∀ c : Ω, c ∈ F ↔ c ^ q ^ 2 = c := fun c => by
    rw [hq2]
    exact hF2 c
  have hFcard : Nat.card F = q ^ 2 := by
    rw [hq2, ← natCard_setOf_pow_eq_self (Ω := Ω) (ℓ := ℓ) (by omega : 2 * f ≠ 0)]
    exact Nat.card_congr (Equiv.subtypeEquivRight hF2)
  have : Finite F := Nat.finite_of_card_ne_zero (by
    rw [hFcard]
    exact (pow_pos (pow_pos hℓ.pos f) 2).ne')
  have hkq : ∀ c : k, c ^ q = c := fun c => by
    rw [← hk, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hσσ : ∀ c, σ (σ c) = c ^ q ^ 2 := fun c => by rw [hσ, hσ, ← pow_mul, sq]
  set σS : SL(3, Ω) →* SL(3, Ω) := SpecialLinearGroup.map σ with hσS
  have hσS : ∀ X : SL(3, Ω), (σS X : M₃) = (X : M₃).map σ := fun X => rfl
  set ι : SL(3, F) →* SL(3, Ω) := SpecialLinearGroup.map F.subtype with hιdef
  have hι : ∀ A : SL(3, F), (ι A : M₃) = (A : Matrix (Fin 3) (Fin 3) F).map F.subtype :=
    fun A => rfl
  have hιinj : Function.Injective ι := specialLinearGroup_map_injective F.subtype.injective
  have hσσι : ∀ A : SL(3, F), σS (σS (ι A)) = ι A := by
    intro A
    apply Subtype.ext
    ext i j
    rw [hσS, Matrix.map_apply, hσS, Matrix.map_apply, hσσ, hι, Matrix.map_apply]
    exact (hF _).mp (A i j).2
  have hσσfix : ∀ X : SL(3, Ω), σS (σS X) = X → ∃ A : SL(3, F), ι A = X := by
    intro X hX
    refine exists_map_eq_of_forall_mem_range F.subtype.injective X fun i j => ?_
    have h1 := congrArg (fun Z : SL(3, Ω) => (Z : M₃) i j) hX
    simp only [hσS, Matrix.map_apply, hσσ] at h1
    exact ⟨⟨_, (hF _).mpr h1⟩, rfl⟩
  set F' : IntermediateField k Ω := F.toIntermediateField (fun x => by
    rw [hF, ← map_pow, pow_two, pow_mul, hkq, hkq]) with hF'def
  have : IsAlgClosure F' Ω :=
    ⟨IsAlgClosure.isAlgClosed k, Algebra.IsAlgebraic.tower_top (K := k) (A := Ω) F'⟩
  have : CharP F' ℓ := (RingHom.charP_iff_charP (algebraMap F' Ω) ℓ).mpr inferInstance
  have hF'card : Nat.card F' = ℓ ^ (2 * f) := by
    rw [← hq2, ← hFcard]
    rfl
  obtain ⟨-, hlang⟩ := matrix_frobenius_lang (K := F') (f := 2 * f) hℓ (by omega)
    hF'card (n := 3) (by norm_num) (SpecialLinearGroup.toGL (a * σS b))
  obtain ⟨H, hHdet, hH⟩ := hlang (a * σS b).2
  set Hs : SL(3, Ω) := ⟨H, hHdet⟩ with hHsdef
  have hc₀ : a * σS b = Hs⁻¹ * σS (σS Hs) := by
    apply Subtype.ext
    have e1 : ((a * σS b : SL(3, Ω)) : M₃) = (SpecialLinearGroup.toGL (a * σS b) : M₃) := rfl
    have hinv : ((Hs⁻¹ : SL(3, Ω)) : M₃) = ((H⁻¹ : GL (Fin 3) Ω) : M₃) := by
      rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.coe_units_inv, Matrix.inv_def, hHdet,
        Ring.inverse_one, one_smul]
    rw [e1, hH, Matrix.SpecialLinearGroup.coe_mul, hσS, hσS, Matrix.map_map, hinv]
    congr 1
    ext i j
    rw [Matrix.map_apply, Matrix.map_apply, Function.comp_apply, hσσ, hq2]
  set h₁ : SL(3, Ω) := Hs⁻¹ with hh₁
  set h₂ : SL(3, Ω) := b * σS h₁ with hh₂
  have hah : a * σS h₂ = h₁ := by
    rw [hh₂, map_mul, ← mul_assoc, hc₀, mul_assoc, ← map_mul σS, ← map_mul σS, hh₁,
      mul_inv_cancel, map_one, map_one, mul_one]
  refine ⟨F, hF, hFcard, (MonoidHom.prod ((MulAut.conj h₁).toMonoidHom.comp ι)
    ((MulAut.conj h₂).toMonoidHom.comp (σS.comp ι))), fun s => ?_⟩
  obtain ⟨A, B⟩ := s
  constructor
  · intro hs
    have hA : a * σS B * a⁻¹ = A := congrArg Prod.fst hs
    have hB : b * σS A * b⁻¹ = B := congrArg Prod.snd hs
    set X : SL(3, Ω) := h₁⁻¹ * A * h₁ with hXdef
    set Y : SL(3, Ω) := h₂⁻¹ * B * h₂ with hYdef
    have hAX : A = h₁ * X * h₁⁻¹ := by rw [hXdef]; group
    have hBY : B = h₂ * Y * h₂⁻¹ := by rw [hYdef]; group
    have hXY : σS Y = X := by
      have e : a * σS (h₂ * Y * h₂⁻¹) * a⁻¹ = (a * σS h₂) * σS Y * (a * σS h₂)⁻¹ := by
        simp only [map_mul, map_inv]
        group
      rw [hBY, e, hah] at hA
      rw [hXdef, ← hA]
      group
    have hYX : σS X = Y := by
      have e : b * σS (h₁ * X * h₁⁻¹) * b⁻¹ = (b * σS h₁) * σS X * (b * σS h₁)⁻¹ := by
        simp only [map_mul, map_inv]
        group
      rw [hAX, e, ← hh₂] at hB
      rw [hYdef, ← hB]
      group
    have hX : σS (σS X) = X := by rw [hYX, hXY]
    obtain ⟨A', hA'⟩ := hσσfix X hX
    refine ⟨A', ?_⟩
    simp only [MonoidHom.prod_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, hA', hYX]
    rw [← hAX, ← hBY]
  · rintro ⟨A', hA'⟩
    simp only [MonoidHom.prod_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, Prod.mk.injEq] at hA'
    obtain ⟨h1, h2⟩ := hA'
    have e1 : a * σS (h₂ * σS (ι A') * h₂⁻¹) * a⁻¹ =
        (a * σS h₂) * σS (σS (ι A')) * (a * σS h₂)⁻¹ := by
      simp only [map_mul, map_inv]
      group
    have e2 : b * σS (h₁ * ι A' * h₁⁻¹) * b⁻¹ = (b * σS h₁) * σS (ι A') * (b * σS h₁)⁻¹ := by
      simp only [map_mul, map_inv]
      group
    show (a * σS B * a⁻¹, b * σS A * b⁻¹) = (A, B)
    rw [← h1, ← h2, Prod.mk.injEq, e1, e2, hah, ← hh₂, hσσι]
    exact ⟨rfl, rfl⟩

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.QuasiSL3
