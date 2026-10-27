module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCorePOuter
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCorePQuatMod

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open QuaternionGroup

theorem quaternionEight_comm_or :
    ∀ x y : QuaternionGroup 2, x * y = y * x ∨ x * y = y * x * a 2 := by
  decide

theorem quaternionSixteen_exists_not_commute :
    ∃ x y : QuaternionGroup 4, x * y * x⁻¹ * y⁻¹ ≠ 1 ∧ x * y * x⁻¹ * y⁻¹ ≠ a 4 :=
  ⟨a 1, xa 0, by decide, by decide⟩

section Transport

variable {G : Type} [Group G] {Q : Subgroup G} (φ : Q ≃* QuaternionGroup 2) {e : G}
  (he : e ∈ Q) (he2 : orderOf e = 2)
include φ he he2

theorem quaternion_comm_or {x y : G} (hx : x ∈ Q) (hy : y ∈ Q) :
    x * y = y * x ∨ x * y = y * x * e := by
  rcases quaternionEight_comm_or (φ ⟨x, hx⟩) (φ ⟨y, hy⟩) with h | h
  · left
    rw [quaternion_eq_iff φ (Q.mul_mem hx hy) (Q.mul_mem hy hx), quaternion_map_mul φ hx hy,
      quaternion_map_mul φ hy hx]
    exact h
  · right
    rw [quaternion_eq_iff φ (Q.mul_mem hx hy) (Q.mul_mem (Q.mul_mem hy hx) he),
      quaternion_map_mul φ hx hy, quaternion_map_mul φ (Q.mul_mem hy hx) he,
      quaternion_map_mul φ hy hx, quaternion_map_eq φ he he2]
    exact h

end Transport

section Central

variable {G : Type} [Group G] {e y a b : G}

theorem conj_mul_mod_central (he : e ∈ Subgroup.center G) (hee : e * e = 1)
    (ha : y * a * y⁻¹ = a ∨ y * a * y⁻¹ = a * e) (hb : y * b * y⁻¹ = b ∨ y * b * y⁻¹ = b * e) :
    y * (a * b) * y⁻¹ = a * b ∨ y * (a * b) * y⁻¹ = a * b * e := by
  have hc : ∀ x : G, x * e = e * x := fun x => (Subgroup.mem_center_iff.mp he x)
  have hsplit : y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
  rw [hsplit]
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb]
  · exact Or.inl rfl
  · exact Or.inr (by group)
  · exact Or.inr (by rw [mul_assoc a e b, ← hc b, ← mul_assoc])
  · left
    rw [mul_assoc a e (b * e), ← mul_assoc e b e, ← hc b, mul_assoc b e e, hee, mul_one]

end Central

namespace PartC

variable {G : Type} [Group G] {T Q P₁ : Subgroup G} {e u y : G}

theorem map_centralElt_sup_zpowers (hc : PartC T Q P₁ e u) (hyT : y ∈ T) (hy : y ∉ Q ⊔ P₁)
    (hyy : y * y ∈ P₁) (ψ : (P₁ ⊔ Subgroup.zpowers y : Subgroup G) ≃* QuaternionGroup 4) :
    ψ ⟨e, Subgroup.mem_sup_left hc.mem_right⟩ = a 4 := by
  have hw : orderOf (ψ.symm (a 4) : (P₁ ⊔ Subgroup.zpowers y : Subgroup G)) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact quaternionGroup_orderOf_a_self (m := 4) (by norm_num)
  have he : ((ψ.symm (a 4) : (P₁ ⊔ Subgroup.zpowers y : Subgroup G)) : G) = e :=
    hc.eq_of_mem_sup_zpowers hyT hy hyy (ψ.symm (a 4)).2 (by rw [Subgroup.orderOf_coe]; exact hw)
  rw [show (⟨e, Subgroup.mem_sup_left hc.mem_right⟩ : (P₁ ⊔ Subgroup.zpowers y : Subgroup G)) =
    ψ.symm (a 4) from Subtype.ext he.symm, MulEquiv.apply_symm_apply]

theorem commutator_mem_right (hc : PartC T Q P₁ e u) (φ : P₁ ≃* QuaternionGroup 2) {p p' : G}
    (hp : p ∈ P₁) (hp' : p' ∈ P₁) : p * p' * p⁻¹ * p'⁻¹ = 1 ∨ p * p' * p⁻¹ * p'⁻¹ = e := by
  rcases quaternion_comm_or φ hc.mem_right hc.order hp hp' with h | h
  · left
    rw [h]
    group
  · right
    rw [h, show p' * p * e * p⁻¹ * p'⁻¹ = p' * p * (e * p⁻¹) * p'⁻¹ by group,
      ← hc.commute_centralElt p⁻¹, show p' * p * (p⁻¹ * e) * p'⁻¹ = p' * e * p'⁻¹ by group,
      hc.conj_centralElt]

theorem exists_moved_right (hc : PartC T Q P₁ e u) (hyT : y ∈ T) (hy : y ∉ Q ⊔ P₁)
    (hyy : y * y ∈ P₁) (φ : P₁ ≃* QuaternionGroup 2)
    (ψ : (P₁ ⊔ Subgroup.zpowers y : Subgroup G) ≃* QuaternionGroup 4) :
    ∃ m ∈ P₁, y * m * y⁻¹ ≠ m ∧ y * m * y⁻¹ ≠ m * e := by
  by_contra hall
  push Not at hall
  have hfix : ∀ p ∈ P₁, y * p * y⁻¹ = p ∨ y * p * y⁻¹ = p * e := fun p hp => by
    by_cases h : y * p * y⁻¹ = p
    · exact Or.inl h
    · exact Or.inr (hall p hp h)
  have hZ : ∀ {c : G}, (c = 1 ∨ c = e) → (c * e = 1 ∨ c * e = e) := by
    rintro c (rfl | rfl)
    · exact Or.inr (one_mul e)
    · exact Or.inl hc.centralElt_mul_self
  have hZinv : ∀ {c : G}, (c = 1 ∨ c = e) → (c⁻¹ = 1 ∨ c⁻¹ = e) := by
    rintro c (rfl | rfl)
    · exact Or.inl inv_one
    · exact Or.inr hc.centralElt_inv
  have hcomm1 : ∀ p ∈ P₁, ∀ p' ∈ P₁, ∀ ε : Bool,
      (p * y ^ (cond ε 1 0 : ℕ)) * p' * (p * y ^ (cond ε 1 0 : ℕ))⁻¹ * p'⁻¹ = 1 ∨
      (p * y ^ (cond ε 1 0 : ℕ)) * p' * (p * y ^ (cond ε 1 0 : ℕ))⁻¹ * p'⁻¹ = e := by
    intro p hp p' hp' ε
    cases ε
    · simpa using hc.commutator_mem_right φ hp hp'
    · simp only [Bool.cond_true, pow_one]
      rcases hfix p' hp' with h | h
      · have h' : p * y * p' * (p * y)⁻¹ * p'⁻¹ = p * (y * p' * y⁻¹) * p⁻¹ * p'⁻¹ := by group
        rw [h', h]
        exact hc.commutator_mem_right φ hp hp'
      · have h' : p * y * p' * (p * y)⁻¹ * p'⁻¹ = p * (y * p' * y⁻¹) * p⁻¹ * p'⁻¹ := by group
        rw [h', h, show p * (p' * e) * p⁻¹ * p'⁻¹ = p * p' * (e * p⁻¹) * p'⁻¹ by group,
          ← hc.commute_centralElt p⁻¹,
          show p * p' * (p⁻¹ * e) * p'⁻¹ = p * p' * p⁻¹ * (e * p'⁻¹) by group,
          ← hc.commute_centralElt p'⁻¹, ← mul_assoc]
        exact hZ (hc.commutator_mem_right φ hp hp')
  have hall' : ∀ g ∈ (P₁ ⊔ Subgroup.zpowers y : Subgroup G),
      ∀ g' ∈ (P₁ ⊔ Subgroup.zpowers y : Subgroup G),
      g * g' * g⁻¹ * g'⁻¹ = 1 ∨ g * g' * g⁻¹ * g'⁻¹ = e := by
    intro g hg g' hg'
    obtain ⟨p, hp, ε, rfl⟩ : ∃ p ∈ P₁, ∃ ε : Bool, p * y ^ (cond ε 1 0 : ℕ) = g := by
      rcases (hc.mem_sup_zpowers_iff hyT hyy).mp hg with h | h
      · exact ⟨g, h, false, by simp⟩
      · exact ⟨g * y⁻¹, h, true, by simp⟩
    rcases (hc.mem_sup_zpowers_iff hyT hyy).mp hg' with h' | h'
    · exact hcomm1 p hp g' h' ε
    ·
      set p' := g' * y⁻¹ with hp'def
      have hg'eq : g' = p' * y := by rw [hp'def]; group
      cases ε
      ·
        have h1 := hcomm1 p' h' p hp true
        simp only [Bool.cond_true, pow_one, Bool.cond_false, pow_zero, mul_one] at h1 ⊢
        have hinv : p * g' * p⁻¹ * g'⁻¹ = (g' * p * g'⁻¹ * p⁻¹)⁻¹ := by group
        rw [hinv, hg'eq]
        exact hZinv h1
      · simp only [Bool.cond_true, pow_one]
        have h2 : p * y * g' * (p * y)⁻¹ * g'⁻¹ =
            p * (y * (p' * p⁻¹) * y⁻¹) * p'⁻¹ := by rw [hg'eq]; group
        rw [h2]
        have hpp : p' * p⁻¹ ∈ P₁ := P₁.mul_mem h' (P₁.inv_mem hp)
        rcases hfix _ hpp with h | h
        · rw [h, show p * (p' * p⁻¹) * p'⁻¹ = p * p' * p⁻¹ * p'⁻¹ by group]
          exact hc.commutator_mem_right φ hp h'
        · rw [h, show p * (p' * p⁻¹ * e) * p'⁻¹ = p * p' * p⁻¹ * (e * p'⁻¹) by group,
            ← hc.commute_centralElt p'⁻¹, ← mul_assoc]
          exact hZ (hc.commutator_mem_right φ hp h')
  obtain ⟨x₁, x₂, h1, h2⟩ := quaternionSixteen_exists_not_commute
  set g₁ := ψ.symm x₁
  set g₂ := ψ.symm x₂
  have hψe := hc.map_centralElt_sup_zpowers hyT hy hyy ψ
  rcases hall' g₁ g₁.2 g₂ g₂.2 with h | h
  · apply h1
    have h' : g₁ * g₂ * g₁⁻¹ * g₂⁻¹ = 1 := Subtype.ext (by simpa using h)
    have := congrArg ψ h'
    simpa [g₁, g₂] using this
  · apply h2
    have h' : g₁ * g₂ * g₁⁻¹ * g₂⁻¹ = ⟨e, Subgroup.mem_sup_left hc.mem_right⟩ :=
      Subtype.ext (by simpa using h)
    have := congrArg ψ h'
    rw [hψe] at this
    simpa [g₁, g₂] using this

theorem exists_mul_self_eq_of_moved (hc : PartC T Q P₁ e u) (φ : P₁ ≃* QuaternionGroup 2)
    (hyT : y ∈ T) (hy : y ∉ Q ⊔ P₁) (hyy : y * y ∈ P₁) {m : G} (hm : m ∈ P₁)
    (hm1 : y * m * y⁻¹ ≠ m) (hm2 : y * m * y⁻¹ ≠ m * e) :
    y * y = e ∨ y * m * (y * m) = e := by
  have hnot1 : ∀ w ∈ T, w ∉ Q ⊔ P₁ → w * w ≠ 1 := by
    intro w hwT hw hww
    have hw1 : w ≠ 1 := fun h => hw (h ▸ (Q ⊔ P₁).one_mem)
    exact hw (hc.involution_mem w hwT (orderOf_eq_prime (by rw [pow_two]; exact hww) hw1))
  have hymQ : y * m ∉ Q ⊔ P₁ := fun h => hy (by
    simpa using (Q ⊔ P₁).mul_mem h ((Q ⊔ P₁).inv_mem (Subgroup.mem_sup_right hm)))
  set p₀ := y * y with hp₀
  have hp₀1 : p₀ ≠ 1 := hnot1 y hyT hy
  by_cases hp₀e : p₀ = e
  · exact Or.inl hp₀e
  right
  have heP := hc.mem_right
  have he2 := hc.order
  have hp₀p₀ : p₀ * p₀ = e := quaternion_mul_self_of_ne φ heP he2 hyy hp₀1 hp₀e
  have hyp₀ : y * p₀ * y⁻¹ = p₀ := by rw [hp₀]; group
  have hinj : ∀ a c : G, y * a * y⁻¹ = y * c * y⁻¹ → a = c := fun a c h =>
    mul_left_cancel (mul_right_cancel h)
  have hm1' : m ≠ 1 := fun h => hm1 (by rw [h, mul_one, mul_inv_cancel])
  have hme : m ≠ e := fun h => hm1 (by rw [h, hc.conj_centralElt])
  have hmm : m * m = e := quaternion_mul_self_of_ne φ heP he2 hm hm1' hme
  have hb : y * m * y⁻¹ ∈ P₁ := hc.normal_right y hyT m hm
  set b := y * m * y⁻¹ with hbdef
  have hb1 : b ≠ 1 := fun h => hm1' (hinj m 1 (by rw [← hbdef, h, mul_one, mul_inv_cancel]))
  have hbe : b ≠ e := fun h => hme (hinj m e (by rw [← hbdef, h, hc.conj_centralElt]))
  have hmp₀ : p₀ ≠ m := fun h => hm1 (by rw [hbdef, ← h, hyp₀])
  have hmp₀e : p₀ ≠ m * e := fun h => hm1 (by
    have hm' : m = p₀ * e := by rw [h, hc.mul_centralElt_mul_centralElt]
    rw [hbdef, hm', hc.conj_mul_centralElt, hyp₀])
  have hbp₀ : b ≠ p₀ := fun h => hmp₀ (hinj m p₀ (by rw [← hbdef, h, hyp₀])).symm
  have hbp₀e : b ≠ p₀ * e := fun h => hmp₀e (by
    have hm' : m = p₀ * e := hinj m (p₀ * e) (by rw [← hbdef, h, hc.conj_mul_centralElt, hyp₀])
    rw [hm', hc.mul_centralElt_mul_centralElt])
  have hsq : y * m * (y * m) = b * p₀ * m := by rw [hbdef, hp₀]; group
  rcases quaternion_enum φ heP he2 hm hyy hb hmm hp₀p₀ hmp₀ hmp₀e with
    h | h | h | h | h | h | h | h
  · exact absurd h hb1
  · exact absurd h hbe
  · exact absurd h hm1
  · exact absurd h hm2
  · exact absurd h hbp₀
  · exact absurd h hbp₀e
  · exfalso
    apply hnot1 (y * m) (T.mul_mem hyT (hc.right_le hm)) hymQ
    rw [hsq, h, show m * p₀ * p₀ * m = m * (p₀ * p₀) * m by group, hp₀p₀,
      hc.commute_centralElt m, mul_assoc, hmm, hc.centralElt_mul_self]
  · rw [hsq, h]
    calc m * p₀ * e * p₀ * m = m * p₀ * (e * p₀) * m := by group
      _ = m * p₀ * (p₀ * e) * m := by rw [hc.commute_centralElt p₀]
      _ = m * (p₀ * p₀) * (e * m) := by group
      _ = m * (e * e) * m := by rw [hp₀p₀]; group
      _ = e := by rw [hc.centralElt_mul_self, mul_one, hmm]

end PartC

structure CaseC3 {G : Type} [Group G] (T Q P₁ : Subgroup G) (e u y : G) : Prop where
  partC : PartC T Q P₁ e u
  le_normalizer : T ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G)
  quaternion_right : Nonempty (P₁ ≃* QuaternionGroup 2)
  mem : y ∈ T
  not_mem : y ∉ Q ⊔ P₁
  mul_self : y * y = e
  moved : ∃ m ∈ P₁, y * m * y⁻¹ ≠ m ∧ y * m * y⁻¹ ≠ m * e

namespace PartC

variable {G : Type} [Group G] {T Q P₁ : Subgroup G} {e u y : G}

theorem exists_caseC3 (hc : PartC T Q P₁ e u)
    (hTu : T ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G)) (hyT : y ∈ T) (hy : y ∉ Q ⊔ P₁)
    (hyy : y * y ∈ P₁) (hφ : Nonempty (P₁ ≃* QuaternionGroup 2))
    (hψ : Nonempty ((P₁ ⊔ Subgroup.zpowers y : Subgroup G) ≃* QuaternionGroup 4)) :
    ∃ y', CaseC3 T Q P₁ e u y' := by
  obtain ⟨φ⟩ := hφ
  obtain ⟨ψ⟩ := hψ
  obtain ⟨m, hm, hm1, hm2⟩ := hc.exists_moved_right hyT hy hyy φ ψ
  rcases hc.exists_mul_self_eq_of_moved φ hyT hy hyy hm hm1 hm2 with h | h
  · exact ⟨y, hc, hTu, ⟨φ⟩, hyT, hy, h, m, hm, hm1, hm2⟩
  · refine ⟨y * m, hc, hTu, ⟨φ⟩, T.mul_mem hyT (hc.right_le hm), fun hmem => hy ?_, h, m, hm, ?_⟩
    · simpa using (Q ⊔ P₁).mul_mem hmem ((Q ⊔ P₁).inv_mem (Subgroup.mem_sup_right hm))
    · rw [show y * m * m * (y * m)⁻¹ = y * m * y⁻¹ by group]
      exact ⟨hm1, hm2⟩

end PartC

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
