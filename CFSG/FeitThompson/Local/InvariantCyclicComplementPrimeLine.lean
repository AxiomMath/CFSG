module

public import CFSG.FeitThompson.Local.InvariantComplementsInvertibleOrder
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.GroupTheory.Complement

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup Pointwise

section Invariant

variable {P : Type*} [Group P] {B : Type*} [Group B]

theorem map_eq_of_invariant (α : B →* MulAut P) {N : Subgroup P}
    (h : ∀ b : B, ∀ x ∈ N, α b x ∈ N) (b : B) : N.map ((α b : P ≃* P) : P →* P) = N := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨y, hy, rfl⟩
    exact h b y hy
  · intro x hx
    refine ⟨α b⁻¹ x, h b⁻¹ x hx, ?_⟩
    rw [map_inv]
    exact (α b).apply_symm_apply x

theorem apply_mem_of_map_eq (α : B →* MulAut P) {N : Subgroup P}
    (h : ∀ b : B, N.map ((α b : P ≃* P) : P →* P) = N) (b : B) {x : P} (hx : x ∈ N) :
    α b x ∈ N := by
  rw [← h b]; exact ⟨x, hx, rfl⟩

def quotientMulAut (α : B →* MulAut P) (N : Subgroup P) [N.Normal]
    (h : ∀ b : B, ∀ x ∈ N, α b x ∈ N) : B →* MulAut (P ⧸ N) where
  toFun b := QuotientGroup.congr N N (α b) (map_eq_of_invariant α h b)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | _ y => simp [QuotientGroup.congr_mk]
  map_mul' b c := by
    ext x
    induction x using QuotientGroup.induction_on with
    | _ y => simp [QuotientGroup.congr_mk]

@[simp]
theorem quotientMulAut_mk (α : B →* MulAut P) (N : Subgroup P) [N.Normal]
    (h : ∀ b : B, ∀ x ∈ N, α b x ∈ N) (b : B) (x : P) :
    quotientMulAut α N h b (QuotientGroup.mk x) = (QuotientGroup.mk (α b x) : P ⧸ N) :=
  QuotientGroup.congr_mk N N (α b) (map_eq_of_invariant α h b) x

end Invariant

theorem exists_invariant_isCompl_of_pow_eq_one {R : Type*} [CommGroup R] {p : ℕ}
    (hp : p.Prime) (hexp : ∀ x : R, x ^ p = 1) {B : Type*} [Group B] [Finite B]
    (β : B →* MulAut R) (hB : ¬ p ∣ Nat.card B) {S : Subgroup R}
    (hS : ∀ b : B, ∀ x ∈ S, β b x ∈ S) :
    ∃ T : Subgroup R, (∀ b : B, ∀ x ∈ T, β b x ∈ T) ∧ IsCompl S T := by
  have : Fact p.Prime := ⟨hp⟩
  have inst : Module (ZMod p) (Additive R) := AddCommGroup.zmodModule (n := p) (by
    intro x
    induction x using Additive.ofMul.surjective.forall.2 with
    | _ y => rw [← ofMul_pow, hexp]; rfl)
  set e : Subgroup R ≃o Submodule (ZMod p) (Additive R) :=
    (Subgroup.toAddSubgroup (G := R)).trans (AddSubgroup.toZModSubmodule p) with he
  have hmem : ∀ (T : Subgroup R) (x : R), Additive.ofMul x ∈ e T ↔ x ∈ T := by
    intro T x; rw [he]; simp
  let ρ : Representation (ZMod p) B (Additive R) :=
    { toFun := fun b => ((MulEquiv.toAdditive (β b)).toAddMonoidHom.toZModLinearMap p)
      map_one' := by ext x; simp
      map_mul' := by intro a b; ext x; simp }
  have hρ : ∀ (b : B) (x : R), ρ b (Additive.ofMul x) = Additive.ofMul (β b x) := fun _ _ => rfl
  have hcard : (Nat.card B : ZMod p) ≠ 0 := by
    simpa [ZMod.natCast_eq_zero_iff] using hB
  obtain ⟨U, hU, hcompl⟩ := exists_invariant_isCompl_of_natCard_ne_zero hcard ρ (e S) (by
    intro b v hv
    induction v using Additive.ofMul.surjective.forall.2 with
    | _ y => rw [hρ]; rw [hmem] at hv ⊢; exact hS b y hv)
  refine ⟨e.symm U, ?_, ?_⟩
  · intro b x hx
    have h1 : Additive.ofMul x ∈ U := by
      have := (hmem (e.symm U) x).2 hx
      rwa [e.apply_symm_apply] at this
    have h2 := hU b _ h1
    rw [hρ] at h2
    rw [← hmem, e.apply_symm_apply]
    exact h2
  · rw [e.isCompl_iff, e.apply_symm_apply]
    exact hcompl

section Main

variable {p : ℕ} {P : Type*} [CommGroup P] {B : Type*} [Group B] [Finite B]

theorem isComplement'_of_mul_coe_eq_univ_of_inf_eq_bot {A H : Subgroup P}
    (hprod : (A : Set P) * (H : Set P) = Set.univ) (hinf : A ⊓ H = ⊥) : H.IsComplement' A := by
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.2 ?_) ?_
  · rw [inf_comm]; exact hinf
  · have h : ((H ⊔ A : Subgroup P) : Set P) = (H : Set P) * (A : Set P) :=
      Subgroup.mul_normal H A
    have h2 : ((A ⊔ H : Subgroup P) : Set P) = (A : Set P) * (H : Set P) :=
      Subgroup.mul_normal A H
    rw [← h, sup_comm, h2, hprod]

theorem exists_invariant_isCyclic_of_natCard_eq_prime (hp : p.Prime) {A₀ Y : Subgroup P}
    (hA₀ : Nat.card A₀ = p) [IsCyclic Y] (hprod : (A₀ : Set P) * (Y : Set P) = Set.univ)
    (hinfY : A₀ ⊓ Y = ⊥) (hB : (Nat.card B).Coprime p) (α : B →* MulAut P)
    (hA₀inv : ∀ b : B, A₀.map ((α b : P ≃* P) : P →* P) = A₀) :
    ∃ P₀ : Subgroup P, (∀ b : B, P₀.map ((α b : P ≃* P) : P →* P) = P₀) ∧ IsCyclic P₀ ∧
      (A₀ : Set P) * (P₀ : Set P) = Set.univ ∧ A₀ ⊓ P₀ = ⊥ ∧ Nat.card P₀ = Nat.card Y := by
  have hBp : ¬ p ∣ Nat.card B := (Nat.Prime.coprime_iff_not_dvd hp).1 hB.symm
  have hA₀pow : ∀ x ∈ A₀, x ^ p = 1 := by
    intro x hx
    have : Finite A₀ := Nat.finite_of_card_ne_zero (by rw [hA₀]; exact hp.ne_zero)
    have h : (⟨x, hx⟩ : A₀) ^ Nat.card A₀ = 1 := pow_card_eq_one'
    rw [hA₀] at h
    have h2 : (((⟨x, hx⟩ : A₀) ^ p : A₀) : P) = ((1 : A₀) : P) := congrArg _ h
    simpa using h2
  set Q : Subgroup P := (powMonoidHom p : P →* P).range with hQdef
  have hQinv : ∀ b : B, ∀ x ∈ Q, α b x ∈ Q := by
    rintro b x ⟨z, rfl⟩
    exact ⟨α b z, by simp [powMonoidHom]⟩
  have hQY : Q ≤ Y := by
    rintro x ⟨z, rfl⟩
    have hz : z ∈ (A₀ : Set P) * (Y : Set P) := by rw [hprod]; trivial
    obtain ⟨a, ha, y, hy, rfl⟩ := hz
    have hcalc : (powMonoidHom p : P →* P) (a * y) = y ^ p := by
      simp [powMonoidHom, mul_pow, hA₀pow a ha]
    rw [hcalc]
    exact Y.pow_mem hy p
  have hAQ : A₀ ⊓ Q = ⊥ := le_bot_iff.1 (hinfY.le.trans' (inf_le_inf_left A₀ hQY))
  have hexp : ∀ x : P ⧸ Q, x ^ p = 1 := by
    intro x
    induction x using QuotientGroup.induction_on with
    | _ y =>
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact ⟨y, rfl⟩
  set β := quotientMulAut α Q hQinv with hβ
  set S : Subgroup (P ⧸ Q) := A₀.map (QuotientGroup.mk' Q) with hSdef
  have hSinv : ∀ b : B, ∀ x ∈ S, β b x ∈ S := by
    rintro b x ⟨a, ha, rfl⟩
    exact ⟨α b a, apply_mem_of_map_eq α hA₀inv b ha, quotientMulAut_mk α Q hQinv b a⟩
  obtain ⟨T, hT, hcompl⟩ := exists_invariant_isCompl_of_pow_eq_one hp hexp β hBp hSinv
  set P₀ : Subgroup P := T.comap (QuotientGroup.mk' Q) with hP₀def
  have hmemP₀ : ∀ x : P, x ∈ P₀ ↔ (QuotientGroup.mk x : P ⧸ Q) ∈ T := fun x => Iff.rfl
  have hQP₀ : Q ≤ P₀ := by
    intro x hx
    rw [hmemP₀, (QuotientGroup.eq_one_iff x).2 hx]
    exact one_mem T
  have hP₀inv : ∀ b : B, P₀.map ((α b : P ≃* P) : P →* P) = P₀ := by
    refine map_eq_of_invariant α ?_
    intro b x hx
    rw [hmemP₀] at hx ⊢
    have := hT b _ hx
    rwa [quotientMulAut_mk α Q hQinv b x] at this
  have hinfP₀ : A₀ ⊓ P₀ = ⊥ := by
    rw [← hAQ]
    refine le_antisymm (le_inf inf_le_left ?_) (inf_le_inf_left A₀ hQP₀)
    intro x hx
    have h1 : (QuotientGroup.mk x : P ⧸ Q) ∈ S := ⟨x, hx.1, rfl⟩
    have h2 : (QuotientGroup.mk x : P ⧸ Q) ∈ T := (hmemP₀ x).1 hx.2
    have h3 : (QuotientGroup.mk x : P ⧸ Q) = 1 := by
      have h4 := hcompl.inf_eq_bot
      rw [eq_bot_iff] at h4
      exact h4 ⟨h1, h2⟩
    exact (QuotientGroup.eq_one_iff x).1 h3
  have hsupP₀ : A₀ ⊔ P₀ = ⊤ := by
    have hsurj : Function.Surjective (QuotientGroup.mk' Q) := QuotientGroup.mk'_surjective Q
    have h1 : Subgroup.comap (QuotientGroup.mk' Q) (S ⊔ T) = A₀ ⊔ Q ⊔ P₀ := by
      rw [← Subgroup.comap_sup_eq _ _ _ hsurj, hSdef, Subgroup.comap_map_eq,
        QuotientGroup.ker_mk']
    rw [hcompl.sup_eq_top, Subgroup.comap_top] at h1
    have h4 : A₀ ⊔ Q ⊔ P₀ = A₀ ⊔ P₀ := by rw [sup_assoc, sup_eq_right.2 hQP₀]
    rw [← h4, ← h1]
  have hprodP₀ : (A₀ : Set P) * (P₀ : Set P) = Set.univ := by
    have h2 : ((A₀ ⊔ P₀ : Subgroup P) : Set P) = (A₀ : Set P) * (P₀ : Set P) :=
      Subgroup.mul_normal A₀ P₀
    rw [← h2, hsupP₀]; rfl
  have hcP₀ : P₀.IsComplement' A₀ :=
    isComplement'_of_mul_coe_eq_univ_of_inf_eq_bot hprodP₀ hinfP₀
  have hcY : Y.IsComplement' A₀ := isComplement'_of_mul_coe_eq_univ_of_inf_eq_bot hprod hinfY
  have hiso : (P₀ : Type _) ≃* (Y : Type _) :=
    hcP₀.QuotientMulEquiv.symm.trans hcY.QuotientMulEquiv
  exact ⟨P₀, hP₀inv, isCyclic_of_injective hiso.toMonoidHom hiso.injective,
    hprodP₀, hinfP₀, Nat.card_eq_of_bijective _ hiso.bijective⟩

end Main

end CFSG.FeitThompson
