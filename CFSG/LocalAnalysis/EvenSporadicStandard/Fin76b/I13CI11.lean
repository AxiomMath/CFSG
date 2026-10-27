module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13CI10

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

theorem mem_klein {G : Type} [Group G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) {g : G} (hg : g ∈ zpowers a ⊔ zpowers b) :
    g = 1 ∨ g = a ∨ g = b ∨ g = a * b := by
  have hN : ∀ n ∈ zpowers a, b * n * b⁻¹ ∈ zpowers a := by
    intro n hn
    rcases mem_zpowers_sq_eq_one ha hn with h | h
    · rw [h]; simp
    · rw [h]
      have : b * a * b⁻¹ = a := by rw [← hab]; group
      rw [this]; exact mem_zpowers a
  obtain ⟨k, hk, h⟩ := mem_sup_zpowers_of_conj hb hN hg
  rcases mem_zpowers_sq_eq_one ha hk with h1 | h1
  · rcases h with h | h
    · exact Or.inl (h.trans h1)
    · exact Or.inr (Or.inr (Or.inl (by rw [h, h1, one_mul])))
  · rcases h with h | h
    · exact Or.inr (Or.inl (h.trans h1))
    · exact Or.inr (Or.inr (Or.inr (by rw [h, h1])))

namespace I13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}
  {Q : Sylow 2 G} {x β : G} {B S : Subgroup G} {α : G}
  (c : I13Ctx L z t T₀ E Q x β B S α)

@[expose] noncomputable def QB1 (b₁ b₂ : G) : Subgroup G := c.Qs ⊔ (zpowers b₁ ⊔ zpowers b₂)

variable {b₁ b₂ : G}

include c

theorem B1_le_N1 (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B) : zpowers b₁ ⊔ zpowers b₂ ≤ c.N1 :=
  sup_le (zpowers_le.2 (c.B_le_N1 hb₁)) (zpowers_le.2 (c.B_le_N1 hb₂))

theorem QB1_le_N1 (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B) : c.QB1 b₁ b₂ ≤ c.N1 :=
  sup_le c.Qs_le_N1 (c.B1_le_N1 hb₁ hb₂)

theorem B_conj_Qs {b : G} (hb : b ∈ B) {q : G} (hq : q ∈ c.Qs) : b * q * b⁻¹ ∈ c.Qs :=
  (c.mem_Nc.1 (c.B_le_Nc hb) q).1 hq

theorem QB1_pgroup (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B) (h11 : b₁ * b₁ = 1) (h22 : b₂ * b₂ = 1)
    (h12 : b₁ * b₂ = b₂ * b₁) : IsPGroup 2 (c.QB1 b₁ b₂) := by
  have hK2 : IsPGroup 2 (zpowers b₁ ⊔ zpowers b₂ : Subgroup G) := by
    intro g
    refine ⟨1, Subtype.ext ?_⟩
    show (g : G) ^ (2 ^ 1) = 1
    rw [pow_one, pow_two]
    rcases mem_klein h11 h22 h12 g.2 with h | h | h | h
    · rw [h]; simp
    · rw [h]; exact h11
    · rw [h]; exact h22
    · rw [h]
      calc b₁ * b₂ * (b₁ * b₂) = b₁ * (b₂ * b₁) * b₂ := by group
        _ = b₁ * (b₁ * b₂) * b₂ := by rw [h12]
        _ = (b₁ * b₁) * (b₂ * b₂) := by group
        _ = 1 := by rw [h11, h22, one_mul]
  have hKN : (zpowers b₁ ⊔ zpowers b₂ : Subgroup G) ≤ normalizer (c.Qs : Set G) :=
    sup_le (zpowers_le.2 (c.B_le_Nc hb₁)) (zpowers_le.2 (c.B_le_Nc hb₂))
  have := hK2.to_sup_of_normal_right' c.Qs_pgroup hKN
  rw [sup_comm] at this
  exact this

theorem mem_QB1 (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B) (h11 : b₁ * b₁ = 1) (h22 : b₂ * b₂ = 1)
    (h12 : b₁ * b₂ = b₂ * b₁) {y : G} (hy : y ∈ c.QB1 b₁ b₂) :
    ∃ q ∈ c.Qs, ∃ b : G, (b = 1 ∨ b = b₁ ∨ b = b₂ ∨ b = b₁ * b₂) ∧ y = q * b := by
  have hS : c.QB1 b₁ b₂ = (c.Qs ⊔ zpowers b₁) ⊔ zpowers b₂ := by rw [QB1, sup_assoc]
  rw [hS] at hy
  have hN2 : ∀ n ∈ c.Qs ⊔ zpowers b₁, b₂ * n * b₂⁻¹ ∈ c.Qs ⊔ zpowers b₁ := by
    intro n hn
    have hle : c.Qs ⊔ zpowers b₁ ≤
        (c.Qs ⊔ zpowers b₁).comap (MulAut.conj b₂).toMonoidHom := by
      refine sup_le (fun q hq => ?_) (fun u hu => ?_)
      · refine Subgroup.mem_comap.2 (mem_sup_left ?_)
        simpa [MulAut.conj_apply] using c.B_conj_Qs hb₂ hq
      · apply Subgroup.mem_comap.2
        rcases mem_zpowers_sq_eq_one h11 hu with h | h
        · rw [h]; simp
        · rw [h]
          have : b₂ * b₁ * b₂⁻¹ = b₁ := by rw [← h12]; group
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          rw [this]
          exact mem_sup_right (mem_zpowers b₁)
    have := hle hn
    simpa [MulAut.conj_apply] using this
  obtain ⟨k, hk, h⟩ := mem_sup_zpowers_of_conj h22 hN2 hy
  obtain ⟨q, hq, h'⟩ := mem_sup_zpowers_of_conj h11 (fun n hn => c.B_conj_Qs hb₁ hn) hk
  rcases h with h | h
  · rcases h' with h' | h'
    · exact ⟨q, hq, 1, Or.inl rfl, by rw [h, h', mul_one]⟩
    · exact ⟨q, hq, b₁, Or.inr (Or.inl rfl), by rw [h, h']⟩
  · rcases h' with h' | h'
    · exact ⟨q, hq, b₂, Or.inr (Or.inr (Or.inl rfl)), by rw [h, h']⟩
    · exact ⟨q, hq, b₁ * b₂, Or.inr (Or.inr (Or.inr rfl)), by rw [h, h', mul_assoc]⟩

theorem card_QB1_ge (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B) (h22 : b₂ * b₂ = 1)
    (h1 : b₁ ≠ 1) (h2 : b₂ ≠ 1) (h3 : b₁ ≠ b₂) :
    4096 ≤ Nat.card (c.QB1 b₁ b₂) := by
  set Bset : Set G := {1, b₁, b₂, b₁ * b₂} with hBset
  have hBB : ∀ b ∈ Bset, b ∈ B := by
    intro b hb
    rcases hb with h | h | h | h
    · rw [h]; exact B.one_mem
    · rw [h]; exact hb₁
    · rw [h]; exact hb₂
    · rw [h]; exact mul_mem hb₁ hb₂
  have hBmem : ∀ b ∈ Bset, b ∈ zpowers b₁ ⊔ zpowers b₂ := by
    intro b hb
    rcases hb with h | h | h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact mem_sup_left (mem_zpowers b₁)
    · rw [h]; exact mem_sup_right (mem_zpowers b₂)
    · rw [h]; exact mul_mem (mem_sup_left (mem_zpowers b₁)) (mem_sup_right (mem_zpowers b₂))
  have hb12 : b₁ * b₂ ≠ 1 := by
    intro h
    apply h3
    have : b₁ = b₂⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this]
    exact (inv_eq_of_mul_eq_one_right h22)
  have n1 : (1 : G) ∉ ({b₁, b₂, b₁ * b₂} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => h1 h.symm, fun h => h2 h.symm, fun h => hb12 h.symm⟩
  have n2 : b₁ ∉ ({b₂, b₁ * b₂} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    refine ⟨h3, fun h => h2 ?_⟩
    have : b₁ * 1 = b₁ * b₂ := by rw [mul_one]; exact h
    exact (mul_left_cancel this).symm
  have n3 : b₂ ≠ b₁ * b₂ := by
    intro h
    apply h1
    have : 1 * b₂ = b₁ * b₂ := by rw [one_mul]; exact h
    exact (mul_right_cancel this).symm
  have hBcard : Bset.ncard = 4 := by
    rw [hBset, Set.ncard_insert_of_notMem n1, Set.ncard_insert_of_notMem n2, Set.ncard_pair n3]
  have hinj : Set.InjOn (fun p : G × G => p.1 * p.2) ((c.Qs : Set G) ×ˢ Bset) := by
    rintro ⟨q, b⟩ ⟨hq, hb⟩ ⟨q', b'⟩ ⟨hq', hb'⟩ hqb
    have hqb' : q * b = q' * b' := hqb
    have e : q'⁻¹ * q = b' * b⁻¹ := by
      calc q'⁻¹ * q = q'⁻¹ * (q * b) * b⁻¹ := by group
        _ = q'⁻¹ * (q' * b') * b⁻¹ := by rw [hqb']
        _ = b' * b⁻¹ := by group
    have hBin : b' * b⁻¹ ∈ B := mul_mem (hBB _ hb') (inv_mem (hBB _ hb))
    have hQin : b' * b⁻¹ ∈ c.Qs := e ▸ mul_mem (inv_mem hq') hq
    have h1' : b' * b⁻¹ = 1 :=
      c.h.B_inf_F c.hα hBin ((c.mem_Qs.1 hQin).1)
    have hbb : b' = b := mul_inv_eq_one.1 h1'
    have hqq : q = q' := by
      rw [hbb] at hqb'
      exact mul_right_cancel hqb'
    show (q, b) = (q', b')
    rw [hqq, hbb]
  have hsub : (fun p : G × G => p.1 * p.2) '' ((c.Qs : Set G) ×ˢ Bset) ⊆ (c.QB1 b₁ b₂ : Set G) := by
    rintro _ ⟨⟨q, b⟩, ⟨hq, hb⟩, rfl⟩
    exact mul_mem (mem_sup_left hq) (mem_sup_right (hBmem b hb))
  have h4 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hQc : Set.ncard (c.Qs : Set G) = 1024 := by
    rw [← Nat.card_coe_set_eq]; exact c.card_Qs
  rw [Set.InjOn.ncard_image hinj, Set.ncard_prod, hBcard, hQc] at h4
  have h5 : Set.ncard ((c.QB1 b₁ b₂ : Subgroup G) : Set G) = Nat.card (c.QB1 b₁ b₂) :=
    (Nat.card_coe_set_eq _).symm
  omega

end I13Ctx

end CFSG.EvenSporadicStandard.Fin76b
