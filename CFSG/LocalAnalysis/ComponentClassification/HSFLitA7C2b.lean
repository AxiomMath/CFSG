module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7C2
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7TFacts

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

namespace A7Base

variable {X : Type} [Group X] [Finite X] {S : A7Base X}

theorem z_sq (S : A7Base X) : S.z ^ 2 = 1 := S.sq_of_mem_B (subset_closure (by simp))

namespace Case2

variable (C : S.Case2)

@[expose] noncomputable def word (a b c d : Fin 2) : X :=
  S.t ^ (a : ℕ) * S.z ^ (b : ℕ) * C.f ^ (c : ℕ) * C.u ^ (d : ℕ)

theorem word_mem (a b c d : Fin 2) : C.word a b c d ∈ S.E C.yb :=
  mul_mem (mul_mem (mul_mem (pow_mem C.t_mem_E _) (pow_mem C.z_mem_E _)) (pow_mem C.f_mem_E _))
    (pow_mem C.u_mem _)

theorem word_mul (a b c d a' b' c' d' : Fin 2) :
    C.word a b c d * C.word a' b' c' d' = C.word (a + a') (b + b') (c + c') (d + d') := by
  have hc : ∀ {p q : X}, p ∈ S.E C.yb → q ∈ S.E C.yb → p * q = q * p := fun hp hq =>
    C.comm hp hq
  have ht := C.t_mem_E
  have hz := C.z_mem_E
  have hf := C.f_mem_E
  have hu := C.u_mem
  rw [word, word, word, pow_fin_add S.t_sq, pow_fin_add S.z_sq, pow_fin_add C.f_sq,
    pow_fin_add C.u_sq]
  set A := S.t ^ (a : ℕ)
  set B := S.z ^ (b : ℕ)
  set Cc := C.f ^ (c : ℕ)
  set D := C.u ^ (d : ℕ)
  set A' := S.t ^ (a' : ℕ)
  set B' := S.z ^ (b' : ℕ)
  set C' := C.f ^ (c' : ℕ)
  set D' := C.u ^ (d' : ℕ)
  have hA' : A' ∈ S.E C.yb := pow_mem ht _
  have hB : B ∈ S.E C.yb := pow_mem hz _
  have hB' : B' ∈ S.E C.yb := pow_mem hz _
  have hC : Cc ∈ S.E C.yb := pow_mem hf _
  have hC' : C' ∈ S.E C.yb := pow_mem hf _
  have hD : D ∈ S.E C.yb := pow_mem hu _
  calc A * B * Cc * D * (A' * B' * C' * D')
      = A * (B * Cc * D * A') * (B' * C' * D') := by group
    _ = A * (A' * (B * Cc * D)) * (B' * C' * D') := by
        rw [hc (mul_mem (mul_mem hB hC) hD) hA']
    _ = A * A' * B * (Cc * D * B') * (C' * D') := by group
    _ = A * A' * B * (B' * (Cc * D)) * (C' * D') := by
        rw [hc (mul_mem hC hD) hB']
    _ = A * A' * (B * B') * Cc * (D * C') * D' := by group
    _ = A * A' * (B * B') * Cc * (C' * D) * D' := by rw [hc hD hC']
    _ = A * A' * (B * B') * (Cc * C') * (D * D') := by group

theorem exists_word {e : X} (he : e ∈ S.E C.yb) : ∃ a b c d : Fin 2, e = C.word a b c d := by
  have hcomm : ∀ {p q : X}, p ∈ S.E C.yb → q ∈ S.E C.yb → q * p = p * q := fun hp hq =>
    C.comm hq hp
  have htB : S.t ∈ S.B := subset_closure (by simp)
  have hzB : S.z ∈ S.B := subset_closure (by simp)
  obtain ⟨hV1, hV1m, hV1c⟩ := ElemAbelianTwo.bot.sup_zpowers S.t_sq
    (fun h => S.t_ne_one (mem_bot.mp h)) (fun a ha => by rw [mem_bot.mp ha, one_mul, mul_one])
  have hV1E : (⊥ ⊔ zpowers S.t : Subgroup X) ≤ S.E C.yb :=
    sup_le bot_le (zpowers_le.mpr C.t_mem_E)
  have hzV1 : S.z ∉ (⊥ ⊔ zpowers S.t : Subgroup X) := by
    intro h
    rcases hV1m _ h with h1 | h1
    · exact S.z_ne_one (mem_bot.mp h1)
    · have : S.z = S.t⁻¹ := eq_inv_of_mul_eq_one_left (mem_bot.mp h1)
      rw [inv_eq_of_mul_eq_one_right (by rw [← pow_two, S.t_sq])] at this
      exact S.data.t_not_mem_L (this ▸ S.z_mem.2)
  obtain ⟨hV2, hV2m, hV2c⟩ := hV1.sup_zpowers S.z_sq hzV1
    (fun a ha => hcomm (hV1E ha) C.z_mem_E)
  have hV2E : (⊥ ⊔ zpowers S.t ⊔ zpowers S.z : Subgroup X) ≤ S.E C.yb :=
    sup_le hV1E (zpowers_le.mpr C.z_mem_E)
  have hV2le : (⊥ ⊔ zpowers S.t ⊔ zpowers S.z : Subgroup X) ≤ zpowers S.t ⊔ zpowers S.z :=
    sup_le (sup_le bot_le le_sup_left) le_sup_right
  obtain ⟨hV3, hV3m, hV3c⟩ := hV2.sup_zpowers C.f_sq (fun h => C.f_not_mem (hV2le h))
    (fun a ha => hcomm (hV2E ha) C.f_mem_E)
  have hV3E : (⊥ ⊔ zpowers S.t ⊔ zpowers S.z ⊔ zpowers C.f : Subgroup X) ≤ S.E C.yb :=
    sup_le hV2E (zpowers_le.mpr C.f_mem_E)
  have hV3B : (⊥ ⊔ zpowers S.t ⊔ zpowers S.z ⊔ zpowers C.f : Subgroup X) ≤ S.B :=
    sup_le (sup_le (sup_le bot_le (zpowers_le.mpr htB)) (zpowers_le.mpr hzB))
      (zpowers_le.mpr C.f_mem)
  obtain ⟨-, hV4m, hV4c⟩ := hV3.sup_zpowers C.u_sq (fun h => C.u_not_mem (hV3B h))
    (fun a ha => hcomm (hV3E ha) C.u_mem)
  have hV4E : (⊥ ⊔ zpowers S.t ⊔ zpowers S.z ⊔ zpowers C.f ⊔ zpowers C.u : Subgroup X) =
      S.E C.yb := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hV3E (zpowers_le.mpr C.u_mem)) ?_
    rw [C.card_E, hV4c, hV3c, hV2c, hV1c, Subgroup.card_bot]
  rw [← hV4E] at he
  have hinv : ∀ (g : X), g ^ 2 = 1 → g⁻¹ = g := fun g hg =>
    inv_eq_of_mul_eq_one_right (by rw [← pow_two, hg])
  obtain ⟨d, hd⟩ : ∃ d : Fin 2, e * C.u ^ (d : ℕ) ∈
      (⊥ ⊔ zpowers S.t ⊔ zpowers S.z ⊔ zpowers C.f : Subgroup X) := by
    rcases hV4m e he with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  obtain ⟨c, hc⟩ : ∃ c : Fin 2, e * C.u ^ (d : ℕ) * C.f ^ (c : ℕ) ∈
      (⊥ ⊔ zpowers S.t ⊔ zpowers S.z : Subgroup X) := by
    rcases hV3m _ hd with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin 2, e * C.u ^ (d : ℕ) * C.f ^ (c : ℕ) * S.z ^ (b : ℕ) ∈
      (⊥ ⊔ zpowers S.t : Subgroup X) := by
    rcases hV2m _ hc with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  obtain ⟨a, ha⟩ : ∃ a : Fin 2,
      e * C.u ^ (d : ℕ) * C.f ^ (c : ℕ) * S.z ^ (b : ℕ) * S.t ^ (a : ℕ) = 1 := by
    rcases hV1m _ hb with h | h
    · exact ⟨0, by simpa using mem_bot.mp h⟩
    · exact ⟨1, by simpa using mem_bot.mp h⟩
  refine ⟨a, b, c, d, ?_⟩
  have hpow : ∀ (g : X) (k : Fin 2), g ^ 2 = 1 → (g ^ (k : ℕ))⁻¹ = g ^ (k : ℕ) := by
    intro g k hg
    fin_cases k
    · simp
    · simpa using hinv g hg
  have h1 : e = (S.t ^ (a : ℕ))⁻¹ * (S.z ^ (b : ℕ))⁻¹ * (C.f ^ (c : ℕ))⁻¹ * (C.u ^ (d : ℕ))⁻¹ := by
    calc e = e * C.u ^ (d : ℕ) * C.f ^ (c : ℕ) * S.z ^ (b : ℕ) * S.t ^ (a : ℕ) *
          ((S.t ^ (a : ℕ))⁻¹ * (S.z ^ (b : ℕ))⁻¹ * (C.f ^ (c : ℕ))⁻¹ * (C.u ^ (d : ℕ))⁻¹) := by
          group
      _ = _ := by rw [ha, one_mul]
  rw [h1, hpow _ _ S.t_sq, hpow _ _ S.z_sq, hpow _ _ C.f_sq, hpow _ _ C.u_sq]
  rfl

theorem word_injective {a b c d a' b' c' d' : Fin 2}
    (h : C.word a b c d = C.word a' b' c' d') : a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  classical
  let F : Fin 2 × Fin 2 × Fin 2 × Fin 2 → S.E C.yb :=
    fun v => ⟨C.word v.1 v.2.1 v.2.2.1 v.2.2.2, C.word_mem _ _ _ _⟩
  have hsurj : Function.Surjective F := by
    rintro ⟨e, he⟩
    obtain ⟨a, b, c, d, rfl⟩ := C.exists_word he
    exact ⟨(a, b, c, d), rfl⟩
  have : Fintype (S.E C.yb) := Fintype.ofFinite _
  have hcard : Fintype.card (Fin 2 × Fin 2 × Fin 2 × Fin 2) = Fintype.card (S.E C.yb) := by
    have h1 : Fintype.card (S.E C.yb) = 16 := by
      rw [← Nat.card_eq_fintype_card]
      exact C.card_E
    rw [h1]
    rfl
  have hinj := ((Fintype.bijective_iff_surjective_and_card F).mpr ⟨hsurj, hcard⟩).1
  have := hinj (a₁ := (a, b, c, d)) (a₂ := (a', b', c', d')) (Subtype.ext h)
  simp only [Prod.mk.injEq] at this
  exact this

end Case2

end A7Base

end CFSG.ComponentClassification.HSFLit
