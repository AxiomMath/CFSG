module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveOmeCore
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveOmeLevi
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveZetAut

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix
open scoped commutatorElement
open CFSG.LocalAnalysis.ComponentInitial (LinearFlag.unitriangular)

section Generic

variable {F : Type} [Field F]

theorem isColRadical_one : IsColRadical (1 : Matrix (Fin 4) (Fin 4) F) :=
  ⟨fun _ _ => rfl, one_apply_eq _⟩

theorem colRadVec_one : colRadVec (1 : Matrix (Fin 4) (Fin 4) F) = 0 := by
  funext i
  rw [colRadVec, one_apply_ne (Fin.castSucc_lt_last i).ne, Pi.zero_apply]

theorem isColRadical_conj {A B : SpecialLinearGroup (Fin 4) F} (hA : A ∈ leviQ F)
    (hB : IsColRadical (B : Matrix (Fin 4) (Fin 4) F)) :
    IsColRadical ((A * B * A⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
  have hBQ := mem_leviQ_of_isColRadical hB
  have hBb : (B : Matrix (Fin 4) (Fin 4) F).submatrix Fin.castSucc Fin.castSucc = 1 := by
    ext i j
    rw [submatrix_apply, hB.1, one_apply, one_apply]
    simp only [Fin.castSucc_inj]
  refine isColRadical_of_mem_leviQ (mul_mem (mul_mem hA hBQ) (inv_mem hA)) ?_
  rw [leviBlock_mul (inv_mem hA), leviBlock_mul hBQ, hBb, Matrix.mul_one,
    ← leviBlock_mul (inv_mem hA), mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one,
    submatrix_castSucc_one]

theorem mem_leviQ_of_mem_unitriangular {M : SpecialLinearGroup (Fin 4) F}
    (hM : M ∈ LinearFlag.unitriangular 4 F) : M ∈ leviQ F :=
  ⟨fun j => hM.1 _ _ (Fin.castSucc_lt_last j), hM.2 _⟩

theorem transvection_mem_leviQ {i k : Fin 4} (hik : i ≠ k) (hi : i ≠ Fin.last 3) (a : F) :
    SpecialLinearGroup.transvection hik a ∈ leviQ F := by
  refine ⟨fun j => ?_, ?_⟩
  · rw [SpecialLinearGroup.transvection_coe, Matrix.add_apply,
      one_apply_ne (Fin.castSucc_lt_last j).ne', single_apply, ite_eq_right_iff.2
        fun h => absurd h.1 hi, add_zero]
  · rw [SpecialLinearGroup.transvection_coe, Matrix.add_apply, one_apply_eq, single_apply,
      ite_eq_right_iff.2 fun h => absurd h.1 hi, add_zero]

theorem eq_one_of_commutator_eq_self {G : Type*} [Group G] {H : Subgroup G} (hH : ⁅H, H⁆ = H)
    {A : Type*} [CommGroup A] (f : H →* A) (x : H) : f x = 1 := by
  have : Group.IsPerfect H := Subgroup.isPerfect_iff.2 hH
  exact Abelianization.commutator_subset_ker f Group.IsPerfect.mem_commutator

end Generic

section Setting

variable {G : Type*} [Group G] [Finite G] {F : Type} [Field F]
variable {N W₁ W₂ S₀ : Subgroup G} {p : G → SpecialLinearGroup (Fin 4) F} {b : G → Fin 4 → F}

theorem IsFieldModuleData.lastRow_of_conj (h : IsFieldModuleData N W₁ S₀ p b)
    (hF : Nat.card F = 4) (hW₂S₀ : W₂ ≤ S₀) (hS₀W₂ : S₀ ≤ normalizer (W₂ : Set G))
    (hW₂c : Nat.card W₂ = 2 ^ 8) (hZ : Nat.card (W₁ ⊓ W₂ : Subgroup G) ≤ 4) {x : G}
    (hx : x ∈ N) (hxZ : ∀ z ∈ W₁ ⊓ W₂, x * z * x⁻¹ ∈ W₁ ⊓ W₂) (j : Fin 3) :
    (p x : Matrix (Fin 4) (Fin 4) F) (Fin.last 3) j.castSucc = 0 := by
  obtain ⟨-, -, hall⟩ := h.wTwo_count hF hW₂S₀ hS₀W₂ hW₂c hZ
  obtain ⟨z₀, hz₀, hb₀⟩ := hall 1
  have hinv : ∀ k : Fin 3, (((p x)⁻¹ : SpecialLinearGroup (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F) (Fin.last 3) k.castSucc = 0 := by
    intro k
    have h1 := h.apply_castSucc_eq_zero hF hS₀W₂ hZ (hxZ z₀ hz₀) k
    rw [h.act x hx z₀ (mem_inf.1 hz₀).1, hb₀, single_one_vecMul] at h1
    exact h1
  have h2 := lastRow_of_mul_eq_one
    (M := (((p x)⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))
    (N := (p x : Matrix (Fin 4) (Fin 4) F))
    (by rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]) hinv
  exact h2.1 j

theorem IsFieldModuleData.lastRow_of_twist (h : IsFieldModuleData N W₁ S₀ p b)
    (hF : Nat.card F = 4) (hW₂S₀ : W₂ ≤ S₀) (hS₀W₂ : S₀ ≤ normalizer (W₂ : Set G))
    (hW₂c : Nat.card W₂ = 2 ^ 8) (hZ : Nat.card (W₁ ⊓ W₂ : Subgroup G) ≤ 4) {σ : F →+* F}
    {t : G} {c : SpecialLinearGroup (Fin 4) F}
    (hβt : ∀ w ∈ W₁, b (t * w * t⁻¹) =
      (fun k => σ (b w k)) ᵥ* ((c⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))
    (htZ : ∀ z ∈ W₁ ⊓ W₂, t * z * t⁻¹ ∈ W₁ ⊓ W₂) (j : Fin 3) :
    (c : Matrix (Fin 4) (Fin 4) F) (Fin.last 3) j.castSucc = 0 := by
  obtain ⟨-, -, hall⟩ := h.wTwo_count hF hW₂S₀ hS₀W₂ hW₂c hZ
  obtain ⟨z₀, hz₀, hb₀⟩ := hall 1
  have hσ1 : (fun k => σ (b z₀ k)) = (Pi.single (Fin.last 3) (1 : F) : Fin 4 → F) := by
    funext k
    rw [hb₀, Pi.single_apply]
    split_ifs <;> simp
  have hinv : ∀ k : Fin 3, (((c⁻¹ : SpecialLinearGroup (Fin 4) F)) :
      Matrix (Fin 4) (Fin 4) F) (Fin.last 3) k.castSucc = 0 := by
    intro k
    have h1 := h.apply_castSucc_eq_zero hF hS₀W₂ hZ (htZ z₀ hz₀) k
    rw [hβt z₀ (mem_inf.1 hz₀).1, hσ1, single_one_vecMul] at h1
    exact h1
  have h2 := lastRow_of_mul_eq_one
    (M := (((c⁻¹ : SpecialLinearGroup (Fin 4) F)) : Matrix (Fin 4) (Fin 4) F))
    (N := (c : Matrix (Fin 4) (Fin 4) F))
    (by rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]) hinv
  exact h2.1 j

theorem IsFieldModuleData.mem_sup_iff (h : IsFieldModuleData N W₁ S₀ p b) (hF : Nat.card F = 4)
    (hW₂S₀ : W₂ ≤ S₀) (hS₀W₂ : S₀ ≤ normalizer (W₂ : Set G)) (hW₂c : Nat.card W₂ = 2 ^ 8)
    (hZ : Nat.card (W₁ ⊓ W₂ : Subgroup G) ≤ 4) {g : G} (hg : g ∈ N) :
    g ∈ W₁ ⊔ W₂ ↔ IsColRadical (p g : Matrix (Fin 4) (Fin 4) F) := by
  constructor
  · intro hgW
    let K : Subgroup G :=
      { carrier := {x | x ∈ N ∧ IsColRadical (p x : Matrix (Fin 4) (Fin 4) F)}
        mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1, by
          rw [h.map_mul x hx.1 y hy.1, Matrix.SpecialLinearGroup.coe_mul]
          exact (hx.2.mul hy.2).1⟩
        one_mem' := ⟨one_mem N, by
          rw [h.map_one, Matrix.SpecialLinearGroup.coe_one]
          exact isColRadical_one⟩
        inv_mem' := fun {x} hx => ⟨inv_mem hx.1, by
          rw [h.map_inv hx.1]
          exact (IsColRadical.inv hx.2).1⟩ }
    have hW₁K : W₁ ≤ K := fun w hw => ⟨h.wOne_le hw, by
      rw [(h.eq_one_iff w (h.wOne_le hw)).2 hw, Matrix.SpecialLinearGroup.coe_one]
      exact isColRadical_one⟩
    have hW₂K : W₂ ≤ K := fun w hw =>
      ⟨h.sZero_le (hW₂S₀ hw), h.isColRadical hF hW₂S₀ hS₀W₂ hZ hw⟩
    exact (sup_le hW₁K hW₂K hgW).2
  · intro hgc
    obtain ⟨hall, -, -⟩ := h.wTwo_count hF hW₂S₀ hS₀W₂ hW₂c hZ
    obtain ⟨w, hw, hwv⟩ := hall (colRadVec (p g : Matrix (Fin 4) (Fin 4) F))
    have hwN := h.sZero_le (hW₂S₀ hw)
    have hpw : p w = p g := Subtype.ext
      ((h.isColRadical hF hW₂S₀ hS₀W₂ hZ hw).ext hgc hwv)
    have h1 : g * w⁻¹ ∈ W₁ := by
      rw [← h.eq_one_iff _ (mul_mem hg (inv_mem hwN)), h.map_mul _ hg _ (inv_mem hwN),
        h.map_inv hwN, hpw, mul_inv_cancel]
    rw [show g = g * w⁻¹ * w by group]
    exact mul_mem (mem_sup_left h1) (mem_sup_right hw)

@[expose] def IsFieldModuleData.leviPre (h : IsFieldModuleData N W₁ S₀ p b) : Subgroup G where
  carrier := {g | g ∈ N ∧ p g ∈ leviQ F}
  mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1, by
    rw [h.map_mul x hx.1 y hy.1]
    exact mul_mem hx.2 hy.2⟩
  one_mem' := ⟨one_mem N, by
    rw [h.map_one]
    exact one_mem _⟩
  inv_mem' := fun {x} hx => ⟨inv_mem hx.1, by
    rw [h.map_inv hx.1]
    exact inv_mem hx.2⟩

theorem exists_ne_zero_ne_one_of_card_four (hF : Nat.card F = 4) : ∃ ω : F, ω ≠ 0 ∧ ω ≠ 1 := by
  classical
  have : Finite F := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype F := Fintype.ofFinite F
  by_contra hne
  push Not at hne
  have hsub : (Finset.univ : Finset F) ⊆ {0, 1} := by
    intro x _
    by_cases hx : x = 0
    · simp [hx]
    · simp [hne x hx]
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hF] at h1
  have h2 := Finset.card_le_two (a := (0 : F)) (b := 1)
  omega

omit [Finite G] in
theorem IsFieldModuleData.commutator_leviPre (h : IsFieldModuleData N W₁ S₀ p b)
    (hF : Nat.card F = 4) : ⁅h.leviPre, h.leviPre⁆ = h.leviPre := by
  set Y := h.leviPre with hY
  have hW₁Y : W₁ ≤ Y := fun w hw => ⟨h.wOne_le hw, by
    rw [(h.eq_one_iff w (h.wOne_le hw)).2 hw]
    exact one_mem _⟩
  have hCN : ⁅Y, Y⁆ ≤ N := (Subgroup.commutator_le_self Y).trans fun y hy => hy.1
  have hsingle : ∀ (k : Fin 4) (a : F), ∃ g ∈ W₁, g ∈ ⁅Y, Y⁆ ∧ b g = Pi.single k a := by
    intro k a
    obtain ⟨i, hik, hi⟩ : ∃ i : Fin 4, i ≠ k ∧ i ≠ Fin.last 3 := by
      by_cases hk : k = 0
      · exact ⟨1, by rw [hk]; decide, by decide⟩
      · exact ⟨0, fun h0 => hk h0.symm, by decide⟩
    obtain ⟨w, hw, hbw⟩ := h.surjB (Pi.single i 1)
    obtain ⟨y, hyN, hy⟩ := h.surj (SpecialLinearGroup.transvection hik (-a))⁻¹
    have hyY : y ∈ Y := ⟨hyN, by
      rw [hy]
      exact inv_mem (transvection_mem_leviQ hik hi (-a))⟩
    have hconj : y * w⁻¹ * y⁻¹ ∈ W₁ :=
      (mem_normalizer_iff.1 (h.le_normalizer hyN) w⁻¹).1 (inv_mem hw)
    have heq : ⁅w, y⁆ = w * (y * w⁻¹ * y⁻¹) := by
      rw [commutatorElement_def]
      group
    refine ⟨⁅w, y⁆, heq ▸ mul_mem hw hconj,
      Subgroup.commutator_mem_commutator (hW₁Y hw) hyY, ?_⟩
    rw [heq, h.add _ hw _ hconj, h.act _ hyN _ (inv_mem hw), h.b_inv hw, hy, inv_inv, hbw,
      Matrix.neg_vecMul, vecMul_transvection_eq_add_single, Pi.single_eq_same, one_mul,
      Pi.single_neg]
    abel
  have hW₁C : W₁ ≤ ⁅Y, Y⁆ := by
    intro w hw
    choose g hgW hgC hgb using hsingle
    have hw'W : g 0 (b w 0) * g 1 (b w 1) * g 2 (b w 2) * g 3 (b w 3) ∈ W₁ :=
      mul_mem (mul_mem (mul_mem (hgW _ _) (hgW _ _)) (hgW _ _)) (hgW _ _)
    have hbw' : b (g 0 (b w 0) * g 1 (b w 1) * g 2 (b w 2) * g 3 (b w 3)) = b w := by
      rw [h.add _ (mul_mem (mul_mem (hgW _ _) (hgW _ _)) (hgW _ _)) _ (hgW _ _),
        h.add _ (mul_mem (hgW _ _) (hgW _ _)) _ (hgW _ _), h.add _ (hgW _ _) _ (hgW _ _),
        hgb, hgb, hgb, hgb]
      funext m
      fin_cases m <;> simp
    rw [← h.inj _ hw'W w hw hbw']
    exact mul_mem (mul_mem (mul_mem (hgC _ _) (hgC _ _)) (hgC _ _)) (hgC _ _)
  have hlift : ∀ M ∈ ⁅leviQ F, leviQ F⁆, ∃ k ∈ ⁅Y, Y⁆, p k = M := by
    intro M hM
    rw [Subgroup.commutator_def] at hM
    induction hM using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨A, hA, B, hB, rfl⟩ := hx
      obtain ⟨y₁, hy₁N, rfl⟩ := h.surj A
      obtain ⟨y₂, hy₂N, rfl⟩ := h.surj B
      refine ⟨⁅y₁, y₂⁆, Subgroup.commutator_mem_commutator ⟨hy₁N, hA⟩ ⟨hy₂N, hB⟩, ?_⟩
      rw [commutatorElement_def, commutatorElement_def,
        h.map_mul _ (mul_mem (mul_mem hy₁N hy₂N) (inv_mem hy₁N)) _ (inv_mem hy₂N),
        h.map_mul _ (mul_mem hy₁N hy₂N) _ (inv_mem hy₁N), h.map_mul _ hy₁N _ hy₂N,
        h.map_inv hy₁N, h.map_inv hy₂N]
    | one => exact ⟨1, one_mem _, h.map_one⟩
    | mul x y _ _ hx hy =>
      obtain ⟨k₁, hk₁, rfl⟩ := hx
      obtain ⟨k₂, hk₂, rfl⟩ := hy
      exact ⟨k₁ * k₂, mul_mem hk₁ hk₂, h.map_mul _ (hCN hk₁) _ (hCN hk₂)⟩
    | inv x _ hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      exact ⟨k⁻¹, inv_mem hk, h.map_inv (hCN hk)⟩
  obtain ⟨ω, hω0, hω1⟩ := exists_ne_zero_ne_one_of_card_four hF
  have hQ := commutator_leviQ (pow_three_eq_one_of_card_four hF hω0) hω1
  refine le_antisymm (Subgroup.commutator_le_self Y) fun y hy => ?_
  obtain ⟨k, hk, hpk⟩ := hlift (p y) (hQ.symm ▸ hy.2)
  have hyk : y * k⁻¹ ∈ W₁ := by
    rw [← h.eq_one_iff _ (mul_mem hy.1 (inv_mem (hCN hk))), h.map_mul _ hy.1 _ (inv_mem (hCN hk)),
      h.map_inv (hCN hk), hpk, mul_inv_cancel]
  rw [show y = y * k⁻¹ * k by group]
  exact mul_mem (hW₁C hyk) hk

end Setting

end CFSG.SeitzReduction.LinearPilot
