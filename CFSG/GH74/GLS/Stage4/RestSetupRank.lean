module

public import CFSG.Foundations.Basic

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG

theorem isElementaryAbelian_bot' {G : Type*} [Group G] : IsElementaryAbelian 2 ↥(⊥ : Subgroup G) := by
  refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_of_forall_pow_eq_one fun g => ?_
  have : g = 1 := Subsingleton.elim _ _
  rw [this, one_pow]

theorem exists_elementary_succ {G : Type*} [Group G] [Finite G] {E : Subgroup G} {k : ℕ}
    (hE : IsElementaryAbelian 2 ↥E) (hk : Nat.card E = 2 ^ k) {x : G} (hx : x * x = 1)
    (hcent : ∀ e ∈ E, e * x = x * e) (hxE : x ∉ E) :
    ∃ E' : Subgroup G, IsElementaryAbelian 2 ↥E' ∧ Nat.card E' = 2 ^ (k + 1) ∧ E ≤ E' ∧ x ∈ E' ∧
      ∀ g ∈ E', g ∈ E ∨ ∃ e ∈ E, g = e * x := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hx2 : x ^ 2 = 1 := by rw [pow_two]; exact hx
  have := hE
  have hz : IsElementaryAbelian 2 ↥(Subgroup.zpowers x) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one hx2
  have hxc : x ∈ Subgroup.centralizer (E : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact hcent e he
  have hzc : Subgroup.zpowers x ≤ Subgroup.centralizer (E : Set G) :=
    Subgroup.zpowers_le.mpr hxc
  have hel : IsElementaryAbelian 2 ↥(E ⊔ Subgroup.zpowers x : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer hzc
  let S : Subgroup G :=
    { carrier := {g | g ∈ E ∨ ∃ e ∈ E, g = e * x}
      one_mem' := Or.inl E.one_mem
      mul_mem' := by
        rintro a b (ha | ⟨e₁, he₁, rfl⟩) (hb | ⟨e₂, he₂, rfl⟩)
        · exact Or.inl (E.mul_mem ha hb)
        · exact Or.inr ⟨a * e₂, E.mul_mem ha he₂, by group⟩
        · refine Or.inr ⟨e₁ * b, E.mul_mem he₁ hb, ?_⟩
          rw [mul_assoc, ← hcent b hb, ← mul_assoc]
        · refine Or.inl ?_
          have : e₁ * x * (e₂ * x) = e₁ * e₂ := by
            calc e₁ * x * (e₂ * x) = e₁ * (x * e₂) * x := by group
              _ = e₁ * (e₂ * x) * x := by rw [← hcent e₂ he₂]
              _ = e₁ * e₂ * (x * x) := by group
              _ = e₁ * e₂ := by rw [hx, mul_one]
          rw [this]
          exact E.mul_mem he₁ he₂
      inv_mem' := by
        rintro a (ha | ⟨e, he, rfl⟩)
        · exact Or.inl (E.inv_mem ha)
        · refine Or.inr ⟨e⁻¹, E.inv_mem he, ?_⟩
          calc (e * x)⁻¹ = x⁻¹ * e⁻¹ := by group
            _ = x * e⁻¹ := by rw [hxi]
            _ = e⁻¹ * x := by
              have := hcent e⁻¹ (E.inv_mem he)
              exact this.symm }
  have hSeq : E ⊔ Subgroup.zpowers x = S := by
    apply le_antisymm
    · refine sup_le (fun g hg => Or.inl hg) ?_
      refine Subgroup.zpowers_le.mpr ?_
      exact Or.inr ⟨1, E.one_mem, by simp⟩
    · rintro g (hg | ⟨e, he, rfl⟩)
      · exact Subgroup.mem_sup_left hg
      · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left he)
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
  refine ⟨S, ?_, ?_, ?_, ?_, fun g hg => hg⟩
  · rw [← hSeq]; exact hel
  ·
    have hES : E ≤ S := fun g hg => Or.inl hg
    have hxS : x ∈ S := Or.inr ⟨1, E.one_mem, by simp⟩
    have hidx : (E.subgroupOf S).index = 2 := by
      rw [Subgroup.index_eq_two_iff]
      refine ⟨⟨x, hxS⟩, fun b => ?_⟩
      obtain ⟨b, hb⟩ := b
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul]
      rcases hb with hb | ⟨e, he, rfl⟩
      · refine Or.inr ⟨hb, ?_⟩
        intro hbx
        apply hxE
        have := E.mul_mem (E.inv_mem hb) hbx
        simpa using this
      · refine Or.inl ⟨?_, ?_⟩
        · have : e * x * x = e := by rw [mul_assoc, hx, mul_one]
          rw [this]; exact he
        · intro hex
          apply hxE
          have := E.mul_mem (E.inv_mem he) hex
          simpa using this
    have hcardsub : Nat.card (E.subgroupOf S) = Nat.card E :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hES).toEquiv
    rw [← Subgroup.index_mul_card (E.subgroupOf S), hidx, hcardsub, hk]
    simp [pow_succ, mul_comm]
  · exact fun g hg => Or.inl hg
  · exact Or.inr ⟨1, E.one_mem, by simp⟩


theorem le_pRank_of_card' {G : Type*} [Group G] [Finite G] (E : Subgroup G)
    (hE : IsElementaryAbelian 2 ↥E) {k : ℕ} (hk : Nat.card E = 2 ^ k) : k ≤ CFSG.pRank 2 G := by
  refine le_csSup ⟨Nat.card G, ?_⟩ ⟨E, hE, hk⟩
  rintro r ⟨B, -, hB⟩
  calc r ≤ 2 ^ r := (Nat.lt_two_pow_self).le
    _ = Nat.card B := hB.symm
    _ ≤ Nat.card G := Subgroup.card_le_card_group B

theorem four_le_pRank_of_Q8 {G : Type} [Group G] [Finite G] {K₁ K₂ : Subgroup G}
    {a x₁ y₁ x₂ y₂ z : G}
    (hx₁ : x₁ ∈ K₁) (hy₁ : y₁ ∈ K₁) (hx₂ : x₂ ∈ K₂) (hy₂ : y₂ ∈ K₂)
    (ha₁ : a ∈ K₁) (ha₂ : a ∈ K₂) (ha1 : a ≠ 1) (hinter : ∀ g ∈ K₁ ⊓ K₂, g = 1 ∨ g = a)
    (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x)
    (haa : a * a = 1) (hx₁s : x₁ * x₁ = a) (hy₁s : y₁ * y₁ = a) (hx₂s : x₂ * x₂ = a)
    (hy₂s : y₂ * y₂ = a) (hxy₁ : x₁ * y₁ = a * (y₁ * x₁)) (hxy₂ : x₂ * y₂ = a * (y₂ * x₂))
    (hz : z * z = 1) (hzK : ∀ k ∈ K₁ ⊔ K₂, z * k = k * z) (hzn : z ∉ K₁ ⊔ K₂) :
    4 ≤ CFSG.pRank 2 G := by
  have haK₁ : ∀ k ∈ K₁, a * k = k * a := fun k hk => (hcomm k hk a ha₂).symm
  have haK₂ : ∀ k ∈ K₂, a * k = k * a := fun k hk => hcomm a ha₁ k hk
  have hx₁₂ : x₂ * x₁ = x₁ * x₂ := (hcomm x₁ hx₁ x₂ hx₂).symm
  have hy₁₂ : y₂ * y₁ = y₁ * y₂ := (hcomm y₁ hy₁ y₂ hy₂).symm
  have hx₁y₂ : x₁ * y₂ = y₂ * x₁ := hcomm x₁ hx₁ y₂ hy₂
  have hy₁x₂ : y₁ * x₂ = x₂ * y₁ := hcomm y₁ hy₁ x₂ hx₂
  obtain ⟨t₁, ht₁⟩ : ∃ t : G, t = x₁ * x₂ := ⟨_, rfl⟩
  obtain ⟨t₂, ht₂⟩ : ∃ t : G, t = y₁ * y₂ := ⟨_, rfl⟩
  have ht₁s : t₁ * t₁ = 1 := by
    calc t₁ * t₁ = x₁ * (x₂ * x₁) * x₂ := by rw [ht₁]; group
      _ = x₁ * (x₁ * x₂) * x₂ := by rw [hx₁₂]
      _ = (x₁ * x₁) * (x₂ * x₂) := by group
      _ = 1 := by rw [hx₁s, hx₂s, haa]
  have ht₂s : t₂ * t₂ = 1 := by
    calc t₂ * t₂ = y₁ * (y₂ * y₁) * y₂ := by rw [ht₂]; group
      _ = y₁ * (y₁ * y₂) * y₂ := by rw [hy₁₂]
      _ = (y₁ * y₁) * (y₂ * y₂) := by group
      _ = 1 := by rw [hy₁s, hy₂s, haa]
  have hat₁ : a * t₁ = t₁ * a := by
    calc a * t₁ = (a * x₁) * x₂ := by rw [ht₁]; group
      _ = (x₁ * a) * x₂ := by rw [haK₁ x₁ hx₁]
      _ = x₁ * (a * x₂) := by group
      _ = x₁ * (x₂ * a) := by rw [haK₂ x₂ hx₂]
      _ = t₁ * a := by rw [ht₁]; group
  have hat₂ : a * t₂ = t₂ * a := by
    calc a * t₂ = (a * y₁) * y₂ := by rw [ht₂]; group
      _ = (y₁ * a) * y₂ := by rw [haK₁ y₁ hy₁]
      _ = y₁ * (a * y₂) := by group
      _ = y₁ * (y₂ * a) := by rw [haK₂ y₂ hy₂]
      _ = t₂ * a := by rw [ht₂]; group
  have ht₁t₂ : t₁ * t₂ = t₂ * t₁ := by
    have e1 : x₁ * x₂ * (y₁ * y₂) = (x₁ * y₁) * (x₂ * y₂) := by
      calc x₁ * x₂ * (y₁ * y₂) = x₁ * (x₂ * y₁) * y₂ := by group
        _ = x₁ * (y₁ * x₂) * y₂ := by rw [hy₁x₂]
        _ = (x₁ * y₁) * (x₂ * y₂) := by group
    have e2 : y₁ * y₂ * (x₁ * x₂) = (y₁ * x₁) * (y₂ * x₂) := by
      calc y₁ * y₂ * (x₁ * x₂) = y₁ * (y₂ * x₁) * x₂ := by group
        _ = y₁ * (x₁ * y₂) * x₂ := by rw [hx₁y₂]
        _ = (y₁ * x₁) * (y₂ * x₂) := by group
    have hay₁x₁ : a * (y₁ * x₁) = (y₁ * x₁) * a := haK₁ _ (K₁.mul_mem hy₁ hx₁)
    calc t₁ * t₂ = (x₁ * y₁) * (x₂ * y₂) := by rw [ht₁, ht₂]; exact e1
      _ = (a * (y₁ * x₁)) * (a * (y₂ * x₂)) := by rw [hxy₁, hxy₂]
      _ = ((y₁ * x₁) * a) * (a * (y₂ * x₂)) := by rw [hay₁x₁]
      _ = (y₁ * x₁) * (a * a) * (y₂ * x₂) := by group
      _ = (y₁ * x₁) * (y₂ * x₂) := by rw [haa, mul_one]
      _ = t₂ * t₁ := by rw [ht₁, ht₂]; exact e2.symm
  have hcontra : y₁ * x₁ = x₁ * y₁ → False := by
    intro h
    have h1 : x₁ * y₁ = a * (x₁ * y₁) := by
      calc x₁ * y₁ = a * (y₁ * x₁) := hxy₁
        _ = a * (x₁ * y₁) := by rw [h]
    have h2 : (1 : G) * (x₁ * y₁) = a * (x₁ * y₁) := by rw [one_mul]; exact h1
    exact ha1 (mul_right_cancel h2).symm
  have hx₁K₂ : ∀ c ∈ K₂, x₁ * x₂ = c → False := by
    intro c hc he
    have h1 : x₁ = c * x₂⁻¹ := by
      calc x₁ = x₁ * x₂ * x₂⁻¹ := by group
        _ = c * x₂⁻¹ := by rw [he]
    have h2 : x₁ ∈ K₂ := by rw [h1]; exact K₂.mul_mem hc (K₂.inv_mem hx₂)
    rcases hinter x₁ ⟨hx₁, h2⟩ with h3 | h3
    · rw [h3, one_mul] at hx₁s; exact ha1 hx₁s.symm
    · rw [h3, haa] at hx₁s; exact ha1 hx₁s.symm
  have hax₁ : a * x₁ = x₁ * a := haK₁ x₁ hx₁
  have hy₁not : ∀ p : G, p ∈ K₁ → p * x₁ = x₁ * p → ∀ q : G, q ∈ K₂ → y₁ * y₂ = p * q → False := by
    intro p hp hpc q hq he
    have h1 : p⁻¹ * y₁ = q * y₂⁻¹ := by
      calc p⁻¹ * y₁ = p⁻¹ * (y₁ * y₂) * y₂⁻¹ := by group
        _ = p⁻¹ * (p * q) * y₂⁻¹ := by rw [he]
        _ = q * y₂⁻¹ := by group
    have h2 : p⁻¹ * y₁ ∈ K₁ := K₁.mul_mem (K₁.inv_mem hp) hy₁
    have h3 : p⁻¹ * y₁ ∈ K₂ := by rw [h1]; exact K₂.mul_mem hq (K₂.inv_mem hy₂)
    rcases hinter _ ⟨h2, h3⟩ with h4 | h4
    · have h5 : y₁ = p := by
        calc y₁ = p * (p⁻¹ * y₁) := by group
          _ = p := by rw [h4, mul_one]
      apply hcontra
      rw [h5]
      exact hpc
    · have h5 : y₁ = p * a := by
        calc y₁ = p * (p⁻¹ * y₁) := by group
          _ = p * a := by rw [h4]
      apply hcontra
      rw [h5]
      calc p * a * x₁ = p * (a * x₁) := by group
        _ = p * (x₁ * a) := by rw [hax₁]
        _ = (p * x₁) * a := by group
        _ = (x₁ * p) * a := by rw [hpc]
        _ = x₁ * (p * a) := by group
  obtain ⟨E₁, hE₁, hc₁, -, haE₁, hd₁⟩ := exists_elementary_succ (isElementaryAbelian_bot' (G := G))
    (by simp : Nat.card (⊥ : Subgroup G) = 2 ^ 0) haa
    (fun e he => by rw [Subgroup.mem_bot.1 he]; simp) (fun h => ha1 (Subgroup.mem_bot.1 h))
  have hE₁mem : ∀ g ∈ E₁, g = 1 ∨ g = a := by
    intro g hg
    rcases hd₁ g hg with h | ⟨e, he, h⟩
    · exact Or.inl (Subgroup.mem_bot.1 h)
    · exact Or.inr (by rw [h, Subgroup.mem_bot.1 he, one_mul])
  have hK₁K : K₁ ≤ K₁ ⊔ K₂ := le_sup_left
  have hK₂K : K₂ ≤ K₁ ⊔ K₂ := le_sup_right
  have haK : a ∈ K₁ ⊔ K₂ := hK₁K ha₁
  have ht₁K : t₁ ∈ K₁ ⊔ K₂ := by rw [ht₁]; exact Subgroup.mul_mem _ (hK₁K hx₁) (hK₂K hx₂)
  have ht₂K : t₂ ∈ K₁ ⊔ K₂ := by rw [ht₂]; exact Subgroup.mul_mem _ (hK₁K hy₁) (hK₂K hy₂)
  have hE₁K : ∀ g ∈ E₁, g ∈ K₁ ⊔ K₂ := by
    intro g hg
    rcases hE₁mem g hg with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact haK
  have ht₁E₁ : t₁ ∉ E₁ := by
    intro h
    rcases hE₁mem t₁ h with h1 | h1
    · exact hx₁K₂ 1 (Subgroup.one_mem _) (by rw [← ht₁]; exact h1)
    · exact hx₁K₂ a ha₂ (by rw [← ht₁]; exact h1)
  obtain ⟨E₂, hE₂, hc₂, -, ht₁E₂, hd₂⟩ := exists_elementary_succ hE₁ hc₁ ht₁s
    (fun e he => by
      rcases hE₁mem e he with h | h
      · rw [h]; simp
      · rw [h]; exact hat₁) ht₁E₁
  have hE₂K : ∀ g ∈ E₂, g ∈ K₁ ⊔ K₂ := by
    intro g hg
    rcases hd₂ g hg with h | ⟨e, he, h⟩
    · exact hE₁K g h
    · rw [h]; exact Subgroup.mul_mem _ (hE₁K e he) ht₁K
  have hax₁x₁ : a * x₁ * x₁ = x₁ * (a * x₁) := by
    calc a * x₁ * x₁ = (x₁ * a) * x₁ := by rw [hax₁]
      _ = x₁ * (a * x₁) := by group
  have ht₂E₂ : t₂ ∉ E₂ := by
    intro h
    rcases hd₂ t₂ h with h1 | ⟨e, he, h1⟩
    · rcases hE₁mem t₂ h1 with h2 | h2
      · exact hy₁not 1 (Subgroup.one_mem _) (by simp) 1 (Subgroup.one_mem _)
          (by rw [← ht₂, h2]; simp)
      · exact hy₁not a ha₁ hax₁ 1 (Subgroup.one_mem _) (by rw [← ht₂, h2]; simp)
    · rcases hE₁mem e he with h2 | h2
      · exact hy₁not x₁ hx₁ rfl x₂ hx₂ (by rw [← ht₂, h1, ht₁, h2]; simp)
      · exact hy₁not (a * x₁) (K₁.mul_mem ha₁ hx₁) hax₁x₁ x₂ hx₂
          (by rw [← ht₂, h1, ht₁, h2]; group)
  obtain ⟨E₃, hE₃, hc₃, -, ht₂E₃, hd₃⟩ := exists_elementary_succ hE₂ hc₂ ht₂s
    (fun e he => by
      rcases hd₂ e he with h | ⟨e', he', h⟩
      · rcases hE₁mem e h with h' | h'
        · rw [h']; simp
        · rw [h']; exact hat₂
      · rcases hE₁mem e' he' with h' | h'
        · rw [h, h']; simpa using ht₁t₂
        · rw [h, h']
          calc a * t₁ * t₂ = a * (t₁ * t₂) := by group
            _ = a * (t₂ * t₁) := by rw [ht₁t₂]
            _ = (a * t₂) * t₁ := by group
            _ = (t₂ * a) * t₁ := by rw [hat₂]
            _ = t₂ * (a * t₁) := by group) ht₂E₂
  have hE₃K : ∀ g ∈ E₃, g ∈ K₁ ⊔ K₂ := by
    intro g hg
    rcases hd₃ g hg with h | ⟨e, he, h⟩
    · exact hE₂K g h
    · rw [h]; exact Subgroup.mul_mem _ (hE₂K e he) ht₂K
  have hzE₃ : z ∉ E₃ := fun h => hzn (hE₃K z h)
  obtain ⟨E₄, hE₄, hc₄, -⟩ := exists_elementary_succ hE₃ hc₃ hz
    (fun e he => (hzK e (hE₃K e he)).symm) hzE₃
  have := le_pRank_of_card' E₄ hE₄ hc₄
  omega

end CFSG.GH74.GLS.Stage4.Rest
