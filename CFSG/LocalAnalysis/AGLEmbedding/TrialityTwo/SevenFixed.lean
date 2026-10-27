module

public import CFSG.LocalAnalysis.AGLEmbedding.TrialityTwo.SevenBasis

public section

namespace CFSG.AGLEmbedding.TrialityTwo.Seven

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {t : Module.End K V}

namespace Frame

variable (F : Frame Q t)

abbrev w₁ : V := F.b (.inl (Fin.last 3))

abbrev w₂ : V := F.b (.inr (Fin.last 3))

theorem polar_w : polar Q F.w₁ F.w₂ = 1 :=
  (F.polar_lr (Fin.last 3) (Fin.last 3)).trans (ite_eq_left rfl)

theorem w₁_ne_zero : F.w₁ ≠ 0 := by
  intro h
  have := F.polar_w
  rw [h, polar_zero_left] at this
  exact zero_ne_one this

theorem w₂_ne_zero : F.w₂ ≠ 0 := by
  intro h
  have := F.polar_w
  rw [h, polar_zero_right] at this
  exact zero_ne_one this

theorem polar_e₀_f₀ : polar Q (F.b (.inl 0)) (F.b (.inr 0)) = 1 :=
  (F.polar_lr 0 0).trans (ite_eq_left rfl)

end Frame

theorem pow_apply_mem {W : Submodule K V} (hW : ∀ x ∈ W, t x ∈ W) (n : ℕ) {x : V} (hx : x ∈ W) :
    (t ^ n) x ∈ W := by
  induction n with
  | zero => simpa using hx
  | succ n ih => rw [pow_succ', Module.End.mul_apply]; exact hW _ ih

theorem projC_apply_mem_of_inv {W : Submodule K V} (hW : ∀ x ∈ W, t x ∈ W) {x : V} (hx : x ∈ W) :
    projC t x ∈ W := by
  simp only [projC, LinearMap.add_apply, Module.End.one_apply]
  have h := fun n => pow_apply_mem hW n hx
  exact add_mem (add_mem (add_mem (add_mem (add_mem (add_mem hx (hW _ hx)) (h 2)) (h 3)) (h 4))
    (h 5)) (h 6)

theorem projU₁_apply_mem_of_inv {W : Submodule K V} (hW : ∀ x ∈ W, t x ∈ W) {x : V}
    (hx : x ∈ W) : projU₁ t x ∈ W := by
  simp only [projU₁, LinearMap.add_apply, Module.End.one_apply]
  exact add_mem (add_mem (add_mem hx (hW _ hx)) (pow_apply_mem hW 2 hx)) (pow_apply_mem hW 4 hx)

theorem projU₂_apply_mem_of_inv {W : Submodule K V} (hW : ∀ x ∈ W, t x ∈ W) {x : V}
    (hx : x ∈ W) : projU₂ t x ∈ W := by
  simp only [projU₂, LinearMap.add_apply, Module.End.one_apply]
  exact add_mem (add_mem (add_mem hx (pow_apply_mem hW 3 hx)) (pow_apply_mem hW 5 hx))
    (pow_apply_mem hW 6 hx)

theorem eq_sup_inf_of_inv (h7 : t ^ 7 = 1) (h2 : (2 : K) = 0) {W : Submodule K V}
    (hW : ∀ x ∈ W, t x ∈ W) : W = W ⊓ fixC t ⊔ W ⊓ spU₁ t ⊔ W ⊓ spU₂ t := by
  apply le_antisymm
  · intro x hx
    rw [← projC_add_projU₁_add_projU₂_apply h7 h2 x]
    exact add_mem (add_mem
      (Submodule.mem_sup_left (Submodule.mem_sup_left
        ⟨projC_apply_mem_of_inv hW hx, projC_apply_mem_fixC h7 h2 x⟩))
      (Submodule.mem_sup_left (Submodule.mem_sup_right
        ⟨projU₁_apply_mem_of_inv hW hx, projU₁_apply_mem x⟩)))
      (Submodule.mem_sup_right ⟨projU₂_apply_mem_of_inv hW hx, projU₂_apply_mem x⟩)
  · exact sup_le (sup_le inf_le_left inf_le_left) inf_le_left

theorem map_spU₁ (h7 : t ^ 7 = 1) : (spU₁ t).map t = spU₁ t := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact apply_mem_spU₁ hx
  · intro x hx
    refine ⟨(t ^ 6) x, pow_apply_mem (fun _ hy => apply_mem_spU₁ hy) 6 hx, ?_⟩
    rw [← Module.End.mul_apply, ← pow_succ', h7, Module.End.one_apply]

theorem map_spU₂ (h7 : t ^ 7 = 1) : (spU₂ t).map t = spU₂ t := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact apply_mem_spU₂ hx
  · intro x hx
    refine ⟨(t ^ 6) x, pow_apply_mem (fun _ hy => apply_mem_spU₂ hy) 6 hx, ?_⟩
    rw [← Module.End.mul_apply, ← pow_succ', h7, Module.End.one_apply]

theorem map_span_of_mem_fixC {w : V} (hw : w ∈ fixC t) :
    (Submodule.span K {w}).map t = Submodule.span K {w} := by
  rw [Submodule.map_span, Set.image_singleton, (mem_fixC_iff).1 hw]

theorem exists_eq_span_of_finrank_eq_one {W : Submodule K V} (h1 : finrank K W = 1) :
    ∃ x ∈ W, x ≠ 0 ∧ W = Submodule.span K {x} := by
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.1 h1
  refine ⟨v, v.2, fun h => hv0 (Subtype.ext h), le_antisymm (fun x hx => ?_) ?_⟩
  · obtain ⟨c, hc⟩ := hv ⟨x, hx⟩
    exact Submodule.mem_span_singleton.2 ⟨c, congrArg Subtype.val hc⟩
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact v.2

section Classification

variable [FiniteDimensional K V] (hK : Nat.card K = 2) (h7 : t ^ 7 = 1) (ht : t ≠ 1)
  (hQt : ∀ v, Q (t v) = Q v) (hB : (polarBilin Q).Nondegenerate) (hV : finrank K V = 8)
  (F : Frame Q t)
include hK h7 ht hQt hB hV

theorem eq_span_of_le_fixC {A : Submodule K V} (hA : A ≤ fixC t) (h1 : finrank K A = 1)
    (hs : ∀ v ∈ A, Q v = 0) :
    A = Submodule.span K {F.w₁} ∨ A = Submodule.span K {F.w₂} := by
  obtain ⟨x, hxA, hx0, rfl⟩ := exists_eq_span_of_finrank_eq_one h1
  rcases eq_or_eq_of_mem_fixC hK h7 ht hQt hB hV F.mem_C₁ F.mem_C₂ (F.Q_b _) (F.Q_b _)
    F.polar_w (hA hxA) (hs x hxA) hx0 with rfl | rfl
  · exact .inl rfl
  · exact .inr rfl

theorem eq_span_of_fixed_point {W : Submodule K V} (h1 : finrank K W = 1)
    (hs : ∀ v ∈ W, Q v = 0) (hW : W.map t = W) :
    W = Submodule.span K {F.w₁} ∨ W = Submodule.span K {F.w₂} := by
  obtain ⟨x, hxW, hx0, hWx⟩ := exists_eq_span_of_finrank_eq_one h1
  have htx : t x ∈ W := hW ▸ Submodule.mem_map_of_mem hxW
  rw [hWx, Submodule.mem_span_singleton] at htx
  obtain ⟨c, hc⟩ := htx
  have hfix : t x = x := by
    rcases eq_zero_or_eq_one_of_card hK c with rfl | rfl
    · exfalso
      apply hx0
      have : (t ^ 7) x = x := by rw [h7, Module.End.one_apply]
      rw [← this, pow_succ, Module.End.mul_apply, ← hc, zero_smul, map_zero]
    · rw [← hc, one_smul]
  refine eq_span_of_le_fixC hK h7 ht hQt hB hV F ?_ h1 hs
  rw [hWx, Submodule.span_le, Set.singleton_subset_iff]
  exact (mem_fixC_iff).2 hfix

theorem eq_of_fixed_solid {W : Submodule K V} (h4 : finrank K W = 4)
    (hs : ∀ v ∈ W, Q v = 0) (hW : W.map t = W) :
    W = spU₁ t ⊔ Submodule.span K {F.w₁} ∨ W = spU₁ t ⊔ Submodule.span K {F.w₂} ∨
      W = spU₂ t ⊔ Submodule.span K {F.w₁} ∨ W = spU₂ t ⊔ Submodule.span K {F.w₂} := by
  have h2 := two_eq_zero_of_card hK
  have hinv : ∀ x ∈ W, t x ∈ W := fun x hx => hW ▸ Submodule.mem_map_of_mem hx
  have hdec := eq_sup_inf_of_inv h7 h2 hinv
  have hdim : 4 ≤ finrank K ↥(W ⊓ fixC t) + finrank K ↥(W ⊓ spU₁ t) +
      finrank K ↥(W ⊓ spU₂ t) := by
    have e1 := Submodule.finrank_add_le_finrank_add_finrank (W ⊓ fixC t ⊔ W ⊓ spU₁ t)
      (W ⊓ spU₂ t)
    have e2 := Submodule.finrank_add_le_finrank_add_finrank (W ⊓ fixC t) (W ⊓ spU₁ t)
    rw [← hdec, h4] at e1
    omega
  have hC : finrank K ↥(W ⊓ fixC t) ≤ 1 := by
    by_contra hcon
    have hle := Submodule.finrank_mono (inf_le_right : W ⊓ fixC t ≤ fixC t)
    rw [finrank_fixC_eq_two hK h7 ht hQt hB hV] at hle
    have heq : W ⊓ fixC t = fixC t := Submodule.eq_of_le_of_finrank_eq inf_le_right
      (by rw [finrank_fixC_eq_two hK h7 ht hQt hB hV]; omega)
    have h₁ : F.w₁ ∈ W ⊓ fixC t := by rw [heq]; exact F.mem_C₁
    have h₂ : F.w₂ ∈ W ⊓ fixC t := by rw [heq]; exact F.mem_C₂
    have := hs _ (add_mem h₁.1 h₂.1)
    rw [map_add_pair_eq_one (F.Q_b _) (F.Q_b _) F.polar_w] at this
    exact one_ne_zero this
  have hinv₁ : ∀ x ∈ W ⊓ spU₁ t, t x ∈ W ⊓ spU₁ t :=
    fun x hx => ⟨hinv x hx.1, apply_mem_spU₁ hx.2⟩
  have hinv₂ : ∀ x ∈ W ⊓ spU₂ t, t x ∈ W ⊓ spU₂ t :=
    fun x hx => ⟨hinv x hx.1, apply_mem_spU₂ hx.2⟩
  have hU₁ := eq_bot_or_eq_of_le_spU₁ hK h7 ht hQt hB hV hinv₁ inf_le_right
  have hU₂ := eq_bot_or_eq_of_le_spU₂ hK h7 ht hQt hB hV hinv₂ inf_le_right
  have hd₁ := finrank_spU₁_eq_three hK h7 ht hQt hB hV
  have hd₂ := finrank_spU₂_eq_three hK h7 ht hQt hB hV
  have hline : finrank K ↥(W ⊓ fixC t) = 1 →
      W ⊓ fixC t = Submodule.span K {F.w₁} ∨ W ⊓ fixC t = Submodule.span K {F.w₂} :=
    fun h1 => eq_span_of_le_fixC hK h7 ht hQt hB hV F inf_le_right h1 fun v hv => hs v hv.1
  rcases hU₁ with h₁ | h₁ <;> rcases hU₂ with h₂ | h₂
  · rw [h₁, h₂, finrank_bot] at hdim
    omega
  · rw [h₁, h₂, finrank_bot, hd₂] at hdim
    rcases hline (by omega) with h | h
    · right; right; left
      rw [hdec, h, h₁, h₂, sup_bot_eq, sup_comm]
    · right; right; right
      rw [hdec, h, h₁, h₂, sup_bot_eq, sup_comm]
  · rw [h₁, h₂, finrank_bot, hd₁] at hdim
    rcases hline (by omega) with h | h
    · left
      rw [hdec, h, h₁, h₂, sup_bot_eq, sup_comm]
    · right; left
      rw [hdec, h, h₁, h₂, sup_bot_eq, sup_comm]
  · exfalso
    have he : F.b (.inl 0) ∈ W ⊓ spU₁ t := by rw [h₁]; exact F.mem_U₁ 0
    have hf : F.b (.inr 0) ∈ W ⊓ spU₂ t := by rw [h₂]; exact F.mem_U₂ 0
    have := hs _ (add_mem he.1 hf.1)
    rw [QuadraticMap.map_add (⇑Q), F.Q_b, F.Q_b, F.polar_e₀_f₀, zero_add, zero_add] at this
    exact one_ne_zero this

end Classification

end CFSG.AGLEmbedding.TrialityTwo.Seven
