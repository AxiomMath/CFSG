module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R6Abs
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R9CaseA

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1

open Subgroup CFSG.GH74.GLS.Stage1.Thm3.Sec4.M CFSG.GH74.GLS CFSG.GH74
open CFSG.GH74.GLS.Stage1.Thm3.Sec6.B (relIndex_ne_zero' sq_mem_of_relIndex_le_two)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem not_le_sup_cyclic {A B C : Subgroup G} {z : G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hinf : ∀ x ∈ A, x ∈ B → x = 1 ∨ x = z)
    (hz : z ∈ A) (hCnA : C ≤ normalizer (A : Set G)) (hC : IsCyclic ↥C) (hCR : C ≤ A ⊔ B)
    (hBnc : ∃ b ∈ B, ∃ b' ∈ B, b * b' ≠ b' * b) : ¬ (B ≤ A ⊔ C) := by
  intro hBAC
  obtain ⟨c₀, hc₀C, hgen⟩ := exists_gen_of_cyclic hC
  obtain ⟨a₀, ha₀, b₀, hb₀, hc₀⟩ := mem_sup_of_commute hcomm (hCR hc₀C)
  have hzcomm : ∀ b ∈ B, z * b = b * z := fun b hb => hcomm z hz b hb
  have key : ∀ b ∈ B, ∃ e : G, (e = 1 ∨ e = z) ∧ ∃ k : ℤ, b = e * b₀ ^ k := by
    intro b hb
    have hbm : b ∈ C ⊔ A := by rw [sup_comm]; exact hBAC hb
    obtain ⟨c, hc, a, ha, hba⟩ := mem_sup_of_le_normalizer hCnA hbm
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (hgen c hc)
    have hcomm0 : a₀ * b₀ = b₀ * a₀ := hcomm a₀ ha₀ b₀ hb₀
    have hck : c = a₀ ^ k * b₀ ^ k := by
      rw [← hk, hc₀]
      exact (show Commute a₀ b₀ from hcomm0).mul_zpow k
    have heA : a₀ ^ k * a ∈ A := mul_mem (zpow_mem ha₀ k) ha
    have heq : b = (a₀ ^ k * a) * b₀ ^ k := by
      have hab : b₀ ^ k * a = a * b₀ ^ k := (hcomm a ha (b₀ ^ k) (zpow_mem hb₀ k)).symm
      calc b = c * a := hba
        _ = a₀ ^ k * b₀ ^ k * a := by rw [hck]
        _ = a₀ ^ k * (b₀ ^ k * a) := by group
        _ = a₀ ^ k * (a * b₀ ^ k) := by rw [hab]
        _ = (a₀ ^ k * a) * b₀ ^ k := by group
    have heB : a₀ ^ k * a ∈ B := by
      have : a₀ ^ k * a = b * (b₀ ^ k)⁻¹ := by rw [heq]; group
      rw [this]; exact mul_mem hb (inv_mem (zpow_mem hb₀ k))
    exact ⟨a₀ ^ k * a, hinf _ heA heB, k, heq⟩
  obtain ⟨b, hb, b', hb', hne⟩ := hBnc
  obtain ⟨e, he, k, hbk⟩ := key b hb
  obtain ⟨e', he', k', hbk'⟩ := key b' hb'
  apply hne
  have hee : ∀ w : G, (w = 1 ∨ w = z) → ∀ m : ℤ, w * b₀ ^ m = b₀ ^ m * w := by
    intro w hw m
    rcases hw with rfl | rfl
    · simp
    · exact hzcomm _ (zpow_mem hb₀ m)
  have hee' : e * e' = e' * e := by
    rcases he with rfl | rfl <;> rcases he' with rfl | rfl <;> simp
  rw [hbk, hbk']
  calc e * b₀ ^ k * (e' * b₀ ^ k') = e * (b₀ ^ k * e') * b₀ ^ k' := by group
    _ = e * (e' * b₀ ^ k) * b₀ ^ k' := by rw [← hee e' he' k]
    _ = (e * e') * (b₀ ^ k * b₀ ^ k') := by group
    _ = (e' * e) * (b₀ ^ k' * b₀ ^ k) := by rw [hee', ← zpow_add, ← zpow_add, add_comm]
    _ = e' * (e * b₀ ^ k') * b₀ ^ k := by group
    _ = e' * (b₀ ^ k' * e) * b₀ ^ k := by rw [hee e he k']
    _ = e' * b₀ ^ k' * (e * b₀ ^ k) := by group

theorem cyc_bound {A B C : Subgroup G} {z : G} (hz2 : z * z = 1) (hz1 : z ≠ 1) (hzA : z ∈ A)
    (hzB : z ∈ B) (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hinf : ∀ x ∈ A, x ∈ B → x = 1 ∨ x = z) (hCn : ∀ c ∈ C, ∀ a ∈ A, c * a * c⁻¹ ∈ A)
    (hC : IsCyclic ↥C) (hCR : C ≤ A ⊔ B) (hCA : ∀ c ∈ C, c ∈ A → c = 1)
    (hBnc : ∃ b ∈ B, ∃ b' ∈ B, b * b' ≠ b' * b) : 4 * Nat.card ↥C ≤ Nat.card ↥B := by
  have hBnA : B ≤ normalizer (A : Set G) := by
    intro b hb
    refine mem_normalizer_of_both (fun a ha => ?_) (fun a ha => ?_)
    · have := hcomm a ha b hb
      have e : b * a * b⁻¹ = a := by
        calc b * a * b⁻¹ = (a * b) * b⁻¹ := by rw [this]
          _ = a := by group
      rw [e]; exact ha
    · have := hcomm a ha b hb
      have e : b⁻¹ * a * b = a := by
        calc b⁻¹ * a * b = b⁻¹ * (a * b) := by group
          _ = b⁻¹ * (b * a) := by rw [this]
          _ = a := by group
      rw [e]; exact ha
  have hCnA : C ≤ normalizer (A : Set G) := fun c hc =>
    mem_normalizer_of_both (fun a ha => hCn c hc a ha) (fun a ha => by
      have := hCn c⁻¹ (C.inv_mem hc) a ha
      simpa using this)
  have hAB : A ⊓ B = zpowers z := by
    ext x
    constructor
    · intro hx
      exact (mem_zpowers_of_sq hz2).2 (hinf x hx.1 hx.2)
    · intro hx
      rcases (mem_zpowers_of_sq hz2).1 hx with rfl | rfl
      · exact ⟨one_mem _, one_mem _⟩
      · exact ⟨hzA, hzB⟩
  have hcardAB : Nat.card ↥(A ⊓ B) = 2 := by
    rw [hAB, Nat.card_zpowers]
    exact orderOf_two_of_sq_one hz2 hz1
  have hRc := card_sup_mul_card_inf (A := A) (B := B) hBnA
  rw [hcardAB] at hRc
  have hAC : A ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have := hCA x hx.2 hx.1
    rw [this]; exact one_mem _
  have hDc := card_sup_mul_card_inf (A := A) (B := C) hCnA
  rw [hAC, Subgroup.card_bot, mul_one] at hDc
  have hnot := not_le_sup_cyclic hcomm hinf hzA hCnA hC hCR hBnc
  have hDR : A ⊔ C ≤ A ⊔ B := sup_le le_sup_left hCR
  have hne1 : (A ⊔ C).relIndex (A ⊔ B) ≠ 1 := by
    intro h1
    exact hnot (le_sup_right.trans (Subgroup.relIndex_eq_one.1 h1))
  have hm := Subgroup.relIndex_mul_card (H := A ⊔ C) (K := A ⊔ B)
  rw [inf_eq_left.2 hDR] at hm
  have hm0 : (A ⊔ C).relIndex (A ⊔ B) ≠ 0 := relIndex_ne_zero'
  have hm2 : 2 ≤ (A ⊔ C).relIndex (A ⊔ B) := by omega
  have hApos : 0 < Nat.card ↥A := Nat.card_pos
  have h1 : Nat.card ↥A * Nat.card ↥B =
      Nat.card ↥A * ((A ⊔ C).relIndex (A ⊔ B) * Nat.card ↥C * 2) := by
    rw [← hRc, ← hm, hDc]; ring
  have h2 := Nat.eq_of_mul_eq_mul_left hApos h1
  have h3 := Nat.mul_le_mul_right (Nat.card ↥C * 2) hm2
  nlinarith

theorem cyc_bound_sq {A B C S : Subgroup G} {z : G} (hz2 : z * z = 1) (hz1 : z ≠ 1) (hzA : z ∈ A)
    (hzB : z ∈ B) (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hinf : ∀ x ∈ A, x ∈ B → x = 1 ∨ x = z) (hCn : ∀ c ∈ C, ∀ a ∈ A, c * a * c⁻¹ ∈ A)
    (hC : IsCyclic ↥C) (hCS : C ≤ S) (hidx : (A ⊔ B).relIndex S ≤ 2)
    (hCA : ∀ c ∈ C, c ∈ A → c = 1) (hBnc : ∃ b ∈ B, ∃ b' ∈ B, b * b' ≠ b' * b) :
    2 * Nat.card ↥C ≤ Nat.card ↥B := by
  obtain ⟨c₀, hc₀C, hgen⟩ := exists_gen_of_cyclic hC
  have hCeq : C = zpowers c₀ := le_antisymm (fun c hc => hgen c hc) (zpowers_le.2 hc₀C)
  have hC₂C : zpowers (c₀ * c₀) ≤ C := zpowers_le.2 (mul_mem hc₀C hc₀C)
  have hC₂R : zpowers (c₀ * c₀) ≤ A ⊔ B :=
    zpowers_le.2 (sq_mem_of_relIndex_le_two hidx (hCS hc₀C))
  have hb := cyc_bound hz2 hz1 hzA hzB hcomm hinf (fun c hc a ha => hCn c (hC₂C hc) a ha)
    (inferInstance : IsCyclic ↥(zpowers (c₀ * c₀))) hC₂R (fun c hc hcA => hCA c (hC₂C hc) hcA) hBnc
  have hcardC : Nat.card ↥C = orderOf c₀ := by rw [hCeq, Nat.card_zpowers]
  have hcardC₂ : Nat.card ↥(zpowers (c₀ * c₀)) = orderOf (c₀ * c₀) := Nat.card_zpowers _
  have hord : orderOf (c₀ * c₀) = orderOf c₀ / Nat.gcd (orderOf c₀) 2 := by
    rw [← sq]; exact orderOf_pow' c₀ (by norm_num)
  have hg : Nat.gcd (orderOf c₀) 2 ≤ 2 := Nat.gcd_le_right _ (by norm_num)
  have hdiv : orderOf c₀ / Nat.gcd (orderOf c₀) 2 * Nat.gcd (orderOf c₀) 2 = orderOf c₀ :=
    Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
  have hle : orderOf c₀ ≤ 2 * (orderOf c₀ / Nat.gcd (orderOf c₀) 2) := by
    calc orderOf c₀ = orderOf c₀ / Nat.gcd (orderOf c₀) 2 * Nat.gcd (orderOf c₀) 2 := hdiv.symm
      _ ≤ orderOf c₀ / Nat.gcd (orderOf c₀) 2 * 2 := Nat.mul_le_mul_left _ hg
      _ = 2 * (orderOf c₀ / Nat.gcd (orderOf c₀) 2) := by ring
  rw [hcardC₂, hord] at hb
  rw [hcardC]
  omega

omit [Finite G] in
theorem z_mem_zpowers_of_mem {Y : Subgroup G} {z : G} (hY2 : IsPGroup 2 ↥Y)
    (hinv : ∀ p ∈ Y, p * p = 1 → p = 1 ∨ p = z) {c : G} (hc : c ∈ Y) (hc1 : c ≠ 1) :
    z ∈ zpowers c := by
  by_cases hc2 : c * c = 1
  · rcases hinv c hc hc2 with h1 | h1
    · exact absurd h1 hc1
    · rw [← h1]; exact mem_zpowers c
  · obtain ⟨k, hk⟩ := exists_pow_sq_eq hY2 hinv hc hc2
    rw [← hk, ← pow_add]
    exact pow_mem (mem_zpowers c) _

theorem count_AB {S P Q : Subgroup G} {z : G} {FA : G → Prop} (h : Cfg1 G z S P Q Q FA) {nP nQ : ℕ}
    (hnP : IVK.IsQuaternionTwoGroup ↥P nP) (hnQ : IVK.IsQuaternionTwoGroup ↥Q nQ)
    {V₁ V₂ W : Subgroup G} (hV₁P : V₁ ≤ P) (hV₁c : IsCyclic ↥V₁) (hV₁i : V₁.relIndex P = 2)
    (hzV₁ : z ∈ V₁) (hV₂Q : V₂ ≤ Q) (hV₂c : IsCyclic ↥V₂) (hV₂i : V₂.relIndex Q = 2)
    (hzV₂ : z ∈ V₂) (hV₁W : V₁ ≤ W) (hV₂W : V₂ ≤ W) (hWS : W ≤ S) {x : G}
    (hxW : ∀ w ∈ W, x * w * x⁻¹ ∈ W) (hxz : x * z * x⁻¹ ≠ z) :
    Nat.card ↥P = Nat.card ↥Q ∧ (P ⊔ Q).relIndex S = 2 := by
  have hz1 := h.z_ne
  have hz2 := h.z_sq
  have hPinv : ∀ p ∈ P, p * p = 1 → p = 1 ∨ p = z := h.P_inv
  have hQinv : ∀ q ∈ Q, q * q = 1 → q = 1 ∨ q = z := quat_invol_sub hnQ h.z_Q hz2 hz1
  have hPnc : ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := quat_noncomm_group hnP
    exact ⟨a, a.2, b, b.2, fun e => hab (Subtype.ext e)⟩
  have hQnc : ∃ a ∈ Q, ∃ b ∈ Q, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := quat_noncomm_group hnQ
    exact ⟨a, a.2, b, b.2, fun e => hab (Subtype.ext e)⟩
  have hidx : (P ⊔ Q).relIndex S ≤ 2 := h.idx
  have hidx' : (Q ⊔ P).relIndex S ≤ 2 := by rw [sup_comm]; exact h.idx
  set C₁ := V₁.map (MulAut.conj x).toMonoidHom with hC₁
  set C₂ := V₂.map (MulAut.conj x).toMonoidHom with hC₂
  have hC₁S : C₁ ≤ S := by
    intro y hy
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hy
    exact hWS (hxW v (hV₁W hv))
  have hC₂S : C₂ ≤ S := by
    intro y hy
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hy
    exact hWS (hxW v (hV₂W hv))
  have hC₁c : IsCyclic ↥C₁ := by
    have := hV₁c
    exact isCyclic_of_surjective ((MulAut.conj x).toMonoidHom.subgroupMap V₁)
      (MonoidHom.subgroupMap_surjective _ _)
  have hC₂c : IsCyclic ↥C₂ := by
    have := hV₂c
    exact isCyclic_of_surjective ((MulAut.conj x).toMonoidHom.subgroupMap V₂)
      (MonoidHom.subgroupMap_surjective _ _)
  have hcardC₁ : Nat.card ↥C₁ = Nat.card ↥V₁ := Subgroup.card_map_of_injective (MulAut.conj x).injective
  have hcardC₂ : Nat.card ↥C₂ = Nat.card ↥V₂ := Subgroup.card_map_of_injective (MulAut.conj x).injective
  have hcardP : 2 * Nat.card ↥V₁ = Nat.card ↥P := by
    have := Subgroup.relIndex_mul_card (H := V₁) (K := P)
    rw [inf_eq_left.2 hV₁P, hV₁i] at this
    exact this
  have hcardQ : 2 * Nat.card ↥V₂ = Nat.card ↥Q := by
    have := Subgroup.relIndex_mul_card (H := V₂) (K := Q)
    rw [inf_eq_left.2 hV₂Q, hV₂i] at this
    exact this
  have hz'₁ : x * z * x⁻¹ ∈ C₁ := Subgroup.mem_map.2 ⟨z, hzV₁, rfl⟩
  have hz'₂ : x * z * x⁻¹ ∈ C₂ := Subgroup.mem_map.2 ⟨z, hzV₂, rfl⟩
  have hz'2 : (x * z * x⁻¹) * (x * z * x⁻¹) = 1 := by
    calc (x * z * x⁻¹) * (x * z * x⁻¹) = x * (z * z) * x⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  have hz'1 : x * z * x⁻¹ ≠ 1 := by
    intro e
    apply hz1
    calc z = x⁻¹ * (x * z * x⁻¹) * x := by group
      _ = 1 := by rw [e]; group
  have hC₁P : ∀ c ∈ C₁, c ∈ P → c = 1 := by
    intro c hc hcP
    by_contra hc1
    have hzc : z ∈ C₁ := Subgroup.zpowers_le.2 hc (z_mem_zpowers_of_mem (isPGroup_of_quat hnP) hPinv hcP hc1)
    exact hxz (B.cyclic_invol_unique hC₁c hzc hz'₁ hz2 hz'2 hz1 hz'1).symm
  have hC₂Q : ∀ c ∈ C₂, c ∈ Q → c = 1 := by
    intro c hc hcQ
    by_contra hc1
    have hzc : z ∈ C₂ := Subgroup.zpowers_le.2 hc (z_mem_zpowers_of_mem (isPGroup_of_quat hnQ) hQinv hcQ hc1)
    exact hxz (B.cyclic_invol_unique hC₂c hzc hz'₂ hz2 hz'2 hz1 hz'1).symm
  have hcommPQ : ∀ a ∈ P, ∀ b ∈ Q, a * b = b * a := fun a ha b hb => h.PQ_comm a ha b hb
  have hcommQP : ∀ a ∈ Q, ∀ b ∈ P, a * b = b * a := fun a ha b hb => (h.PQ_comm b hb a ha).symm
  have hinfPQ : ∀ y ∈ P, y ∈ Q → y = 1 ∨ y = z := fun y hy hy' => h.PQ_inf y hy hy'
  have hinfQP : ∀ y ∈ Q, y ∈ P → y = 1 ∨ y = z := fun y hy hy' => h.PQ_inf y hy' hy
  have hCn₁ : ∀ c ∈ C₁, ∀ a ∈ P, c * a * c⁻¹ ∈ P := fun c hc a ha => h.P_norm c (hC₁S hc) a ha
  have hCn₂ : ∀ c ∈ C₂, ∀ a ∈ Q, c * a * c⁻¹ ∈ Q := fun c hc a ha => h.Q_norm c (hC₂S hc) a ha
  have hb₁ := cyc_bound_sq hz2 hz1 h.z_P h.z_Q hcommPQ hinfPQ hCn₁ hC₁c hC₁S hidx hC₁P hQnc
  have hb₂ := cyc_bound_sq hz2 hz1 h.z_Q h.z_P hcommQP hinfQP hCn₂ hC₂c hC₂S hidx' hC₂Q hPnc
  have hPQ : Nat.card ↥P = Nat.card ↥Q := by
    apply le_antisymm
    · omega
    · omega
  refine ⟨hPQ, ?_⟩
  have hle2 : (P ⊔ Q).relIndex S ≠ 0 := relIndex_ne_zero'
  by_contra hne2
  have h1 : (P ⊔ Q).relIndex S = 1 := by omega
  have hSR : S ≤ P ⊔ Q := Subgroup.relIndex_eq_one.1 h1
  have hSR' : S ≤ Q ⊔ P := by rw [sup_comm]; exact hSR
  have hbb₁ := cyc_bound hz2 hz1 h.z_P h.z_Q hcommPQ hinfPQ hCn₁ hC₁c (hC₁S.trans hSR) hC₁P hQnc
  have hbb₂ := cyc_bound hz2 hz1 h.z_Q h.z_P hcommQP hinfQP hCn₂ hC₂c (hC₂S.trans hSR') hC₂Q hPnc
  have hPpos : 0 < Nat.card ↥P := Nat.card_pos
  omega

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1
