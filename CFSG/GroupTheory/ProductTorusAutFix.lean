module

public import CFSG.GroupTheory.ProductAutFactors
public import CFSG.GroupTheory.TwoGroupAutFixOfNoInvariant
public import CFSG.GroupTheory.InvertedOddNoTwoSubgroup

public section

namespace CFSG.GroupTheory

open Subgroup

theorem eq_prod_map_fst_snd_of_card_eq_mul {Y₁ Y₂ : Type*} [Group Y₁] [Group Y₂] [Finite Y₁]
    [Finite Y₂] {m c₁ c₂ : ℕ} (hm : 0 < m) (hY₁ : Nat.card Y₁ = m * c₁)
    (hY₂ : Nat.card Y₂ = m * c₂) (hc₁ : m.Coprime c₁) (hc₂ : m.Coprime c₂)
    {A : Subgroup (Y₁ × Y₂)} (hA : Nat.card A = m * m) :
    A = (A.map (MonoidHom.fst Y₁ Y₂)).prod (A.map (MonoidHom.snd Y₁ Y₂)) ∧
      Nat.card (A.map (MonoidHom.fst Y₁ Y₂)) = m ∧
      Nat.card (A.map (MonoidHom.snd Y₁ Y₂)) = m := by
  have hdvd₁ : Nat.card (A.map (MonoidHom.fst Y₁ Y₂)) ∣ m := by
    have h1 : Nat.card (A.map (MonoidHom.fst Y₁ Y₂)) ∣ Nat.gcd (Nat.card A) (Nat.card Y₁) :=
      Nat.dvd_gcd (Subgroup.card_map_dvd A (MonoidHom.fst Y₁ Y₂))
        (Subgroup.card_subgroup_dvd_card _)
    rwa [hA, hY₁, Nat.gcd_mul_left, hc₁, mul_one] at h1
  have hdvd₂ : Nat.card (A.map (MonoidHom.snd Y₁ Y₂)) ∣ m := by
    have h1 : Nat.card (A.map (MonoidHom.snd Y₁ Y₂)) ∣ Nat.gcd (Nat.card A) (Nat.card Y₂) :=
      Nat.dvd_gcd (Subgroup.card_map_dvd A (MonoidHom.snd Y₁ Y₂))
        (Subgroup.card_subgroup_dvd_card _)
    rwa [hA, hY₂, Nat.gcd_mul_left, hc₂, mul_one] at h1
  have hle : A ≤ (A.map (MonoidHom.fst Y₁ Y₂)).prod (A.map (MonoidHom.snd Y₁ Y₂)) :=
    fun x hx => Subgroup.mem_prod.mpr ⟨⟨x, hx, rfl⟩, ⟨x, hx, rfl⟩⟩
  have hcardle : Nat.card A ≤
      Nat.card (A.map (MonoidHom.fst Y₁ Y₂)) * Nat.card (A.map (MonoidHom.snd Y₁ Y₂)) := by
    have h := Subgroup.card_le_of_le hle
    rwa [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod] at h
  have h₁le : Nat.card (A.map (MonoidHom.fst Y₁ Y₂)) ≤ m := Nat.le_of_dvd hm hdvd₁
  have h₂le : Nat.card (A.map (MonoidHom.snd Y₁ Y₂)) ≤ m := Nat.le_of_dvd hm hdvd₂
  have hEq : Nat.card (A.map (MonoidHom.fst Y₁ Y₂)) *
      Nat.card (A.map (MonoidHom.snd Y₁ Y₂)) = m * m := by
    refine le_antisymm (Nat.mul_le_mul h₁le h₂le) ?_
    rw [← hA]
    exact hcardle
  have hcard₁ : Nat.card (A.map (MonoidHom.fst Y₁ Y₂)) = m := by
    rcases lt_or_eq_of_le h₁le with hlt | heq
    · exfalso
      have h3 : Nat.card (A.map (MonoidHom.fst Y₁ Y₂)) *
            Nat.card (A.map (MonoidHom.snd Y₁ Y₂)) <
          m * Nat.card (A.map (MonoidHom.snd Y₁ Y₂)) :=
        Nat.mul_lt_mul_of_pos_right hlt Nat.card_pos
      have h4 : m * Nat.card (A.map (MonoidHom.snd Y₁ Y₂)) ≤ m * m :=
        Nat.mul_le_mul_left m h₂le
      have h5 : Nat.card (A.map (MonoidHom.fst Y₁ Y₂)) *
          Nat.card (A.map (MonoidHom.snd Y₁ Y₂)) < m * m := h3.trans_le h4
      rw [hEq] at h5
      exact absurd h5 (lt_irrefl _)
    · exact heq
  have hcard₂ : Nat.card (A.map (MonoidHom.snd Y₁ Y₂)) = m := by
    have h := hEq
    rw [hcard₁] at h
    exact Nat.mul_left_cancel hm h
  refine ⟨?_, hcard₁, hcard₂⟩
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, hcard₁, hcard₂, hA]

theorem eq_bot_of_isPGroup_of_sup_zpowers {Y₁ Y₂ : Type*} [Group Y₁] [Group Y₂]
    {A : Subgroup (Y₁ × Y₂)} {t : Y₁ × Y₂} {m : ℕ} (hm : 1 < m) (hmodd : Odd m)
    (hcard₁ : Nat.card (A.map (MonoidHom.fst Y₁ Y₂)) = m)
    (hcard₂ : Nat.card (A.map (MonoidHom.snd Y₁ Y₂)) = m)
    (ht : ∃ k : ℕ, orderOf t = 2 ^ k) (hinv : ∀ a ∈ A, t * a * t⁻¹ = a⁻¹)
    (hN₁ : ∀ B : Subgroup Y₁, B ≠ ⊥ → Odd (Nat.card B) → ∀ s : Y₁,
      (∃ k : ℕ, orderOf s = 2 ^ k) → (∀ b ∈ B, s * b * s⁻¹ = b⁻¹) → ∀ R : Subgroup Y₁,
      IsPGroup 2 R → B ≤ normalizer (R : Set Y₁) → s ∈ normalizer (R : Set Y₁) → R = ⊥)
    (hN₂ : ∀ B : Subgroup Y₂, B ≠ ⊥ → Odd (Nat.card B) → ∀ s : Y₂,
      (∃ k : ℕ, orderOf s = 2 ^ k) → (∀ b ∈ B, s * b * s⁻¹ = b⁻¹) → ∀ R : Subgroup Y₂,
      IsPGroup 2 R → B ≤ normalizer (R : Set Y₂) → s ∈ normalizer (R : Set Y₂) → R = ⊥)
    {R : Subgroup (Y₁ × Y₂)} (hR : IsPGroup 2 R)
    (hNR : A ⊔ zpowers t ≤ normalizer (R : Set (Y₁ × Y₂))) : R = ⊥ := by
  have hA₁ne : A.map (MonoidHom.fst Y₁ Y₂) ≠ ⊥ := by
    rw [ne_eq, Subgroup.eq_bot_iff_card, hcard₁]
    omega
  have hA₂ne : A.map (MonoidHom.snd Y₁ Y₂) ≠ ⊥ := by
    rw [ne_eq, Subgroup.eq_bot_iff_card, hcard₂]
    omega
  have hpow₁ : ∃ k : ℕ, orderOf t.1 = 2 ^ k := by
    obtain ⟨k, hk⟩ := ht
    have hdvd : orderOf t.1 ∣ orderOf t := orderOf_fst_dvd_orderOf
    rw [hk] at hdvd
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨j, hj⟩
  have hpow₂ : ∃ k : ℕ, orderOf t.2 = 2 ^ k := by
    obtain ⟨k, hk⟩ := ht
    have hdvd : orderOf t.2 ∣ orderOf t := orderOf_snd_dvd_orderOf
    rw [hk] at hdvd
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨j, hj⟩
  refine eq_bot_of_prod (B := A ⊔ zpowers t) (s := t) ?_ ?_ hR hNR
    (hNR (Subgroup.mem_sup_right (Subgroup.mem_zpowers t)))
  · intro S hSp hBS hsS
    refine hN₁ (A.map (MonoidHom.fst Y₁ Y₂)) hA₁ne (hcard₁ ▸ hmodd) t.1 hpow₁ ?_ S hSp ?_ hsS
    · intro b hb
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hb
      have h := congrArg Prod.fst (hinv a ha)
      simpa using h
    · exact (Subgroup.map_mono le_sup_left).trans hBS
  · intro S hSp hBS hsS
    refine hN₂ (A.map (MonoidHom.snd Y₁ Y₂)) hA₂ne (hcard₂ ▸ hmodd) t.2 hpow₂ ?_ S hSp ?_ hsS
    · intro b hb
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hb
      have h := congrArg Prod.snd (hinv a ha)
      simpa using h
    · exact (Subgroup.map_mono le_sup_left).trans hBS

theorem exists_mulAut_prod_eq_of_mem_of_fixes {Y₁ Y₂ : Type*} [Group Y₁] [Group Y₂] [Finite Y₁]
    [Finite Y₂] [IsSimpleGroup Y₁] [IsSimpleGroup Y₂] {A : Subgroup (Y₁ × Y₂)} {a₁ : Y₁}
    {a₂ : Y₂} (ha₁ : (a₁, 1) ∈ A) (ha₂ : ((1 : Y₁), a₂) ∈ A) (ha₁ne : a₁ ≠ 1)
    (ha₂ne : a₂ ≠ 1) {Q : Subgroup (MulAut (Y₁ × Y₂))} (hQ : IsPGroup 2 Q)
    {α : MulAut (Y₁ × Y₂)} (hα : α ∈ Q) (hfix : ∀ a ∈ A, α a = a) :
    ∃ β₁ : MulAut Y₁, ∃ β₂ : MulAut Y₂, α = mulAutProdHom Y₁ Y₂ (β₁, β₂) ∧
      (∃ k : ℕ, orderOf β₁ = 2 ^ k) ∧ (∃ k : ℕ, orderOf β₂ = 2 ^ k) ∧
      (∀ a ∈ A.map (MonoidHom.fst Y₁ Y₂), β₁ a = a) ∧
      ∀ a ∈ A.map (MonoidHom.snd Y₁ Y₂), β₂ a = a := by
  have h1 : α (a₁, 1) = (a₁, 1) := hfix _ ha₁
  have h2 : α ((1 : Y₁), a₂) = ((1 : Y₁), a₂) := hfix _ ha₂
  obtain ⟨hα1, hα2⟩ := prod_factors_of_apply_eq α ha₁ne ha₂ne h1 h2
  obtain ⟨β₁, β₂, hαβ⟩ := exists_mulAut_prod_eq α hα1 hα2
  obtain ⟨n, hn⟩ := IsPGroup.exists_pow_pow_eq_one hQ ⟨α, hα⟩
  have hαpow : α ^ 2 ^ n = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  have hβ : (β₁, β₂) ^ 2 ^ n = 1 := by
    apply mulAutProdHom_injective Y₁ Y₂
    rw [map_pow, ← hαβ, hαpow, map_one]
  have hβ₁pow : β₁ ^ 2 ^ n = 1 := by
    have := congrArg Prod.fst hβ
    simpa using this
  have hβ₂pow : β₂ ^ 2 ^ n = 1 := by
    have := congrArg Prod.snd hβ
    simpa using this
  refine ⟨β₁, β₂, hαβ, ?_, ?_, ?_, ?_⟩
  · obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (orderOf_dvd_of_pow_eq_one hβ₁pow)
    exact ⟨k, hk⟩
  · obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (orderOf_dvd_of_pow_eq_one hβ₂pow)
    exact ⟨k, hk⟩
  · intro a ha
    rw [Subgroup.mem_map] at ha
    obtain ⟨⟨x, y⟩, ha', rfl⟩ := ha
    have h := congrArg Prod.fst (hfix (x, y) ha')
    simpa [hαβ, mulAutProdHom_apply] using h
  · intro a ha
    rw [Subgroup.mem_map] at ha
    obtain ⟨⟨x, y⟩, ha', rfl⟩ := ha
    have h := congrArg Prod.snd (hfix (x, y) ha')
    simpa [hαβ, mulAutProdHom_apply] using h

theorem prod_aut_fix_of_forall_eq_bot {Y₁ Y₂ : Type*} [Group Y₁] [Group Y₂] [Finite Y₁]
    [Finite Y₂] [IsSimpleGroup Y₁] [IsSimpleGroup Y₂] (hZ₁ : center Y₁ = ⊥)
    (hZ₂ : center Y₂ = ⊥) {m c₁ c₂ : ℕ} (hm : 1 < m) (hmodd : Odd m)
    (hY₁ : Nat.card Y₁ = m * c₁) (hY₂ : Nat.card Y₂ = m * c₂) (hc₁ : m.Coprime c₁)
    (hc₂ : m.Coprime c₂)
    (hN₁ : ∀ B : Subgroup Y₁, B ≠ ⊥ → Odd (Nat.card B) → ∀ s : Y₁,
      (∃ k : ℕ, orderOf s = 2 ^ k) → (∀ b ∈ B, s * b * s⁻¹ = b⁻¹) → ∀ R : Subgroup Y₁,
      IsPGroup 2 R → B ≤ normalizer (R : Set Y₁) → s ∈ normalizer (R : Set Y₁) → R = ⊥)
    (hN₂ : ∀ B : Subgroup Y₂, B ≠ ⊥ → Odd (Nat.card B) → ∀ s : Y₂,
      (∃ k : ℕ, orderOf s = 2 ^ k) → (∀ b ∈ B, s * b * s⁻¹ = b⁻¹) → ∀ R : Subgroup Y₂,
      IsPGroup 2 R → B ≤ normalizer (R : Set Y₂) → s ∈ normalizer (R : Set Y₂) → R = ⊥)
    {A : Subgroup (Y₁ × Y₂)} (hA : Nat.card A = m * m) {t : Y₁ × Y₂}
    (ht : ∃ k : ℕ, orderOf t = 2 ^ k) (hinv : ∀ a ∈ A, t * a * t⁻¹ = a⁻¹)
    {Q : Subgroup (MulAut (Y₁ × Y₂))} (hQ : IsPGroup 2 Q)
    (hQB : ∀ b ∈ A ⊔ zpowers t, MulAut.conj b ∈ normalizer (Q : Set (MulAut (Y₁ × Y₂)))) :
    Nat.card (A.map (MonoidHom.fst Y₁ Y₂)) = m ∧ Nat.card (A.map (MonoidHom.snd Y₁ Y₂)) = m ∧
      (∀ x : Y₁ × Y₂, MulAut.conj x ∈ Q → x = 1) ∧
      ∀ α ∈ Q, ∃ β₁ : MulAut Y₁, ∃ β₂ : MulAut Y₂, α = mulAutProdHom Y₁ Y₂ (β₁, β₂) ∧
        (∃ k : ℕ, orderOf β₁ = 2 ^ k) ∧ (∃ k : ℕ, orderOf β₂ = 2 ^ k) ∧
        (∀ a ∈ A.map (MonoidHom.fst Y₁ Y₂), β₁ a = a) ∧
        ∀ a ∈ A.map (MonoidHom.snd Y₁ Y₂), β₂ a = a := by
  obtain ⟨hAprod, hcard₁, hcard₂⟩ :=
    eq_prod_map_fst_snd_of_card_eq_mul (m := m) (by omega) hY₁ hY₂ hc₁ hc₂ hA
  have hA₁ne : A.map (MonoidHom.fst Y₁ Y₂) ≠ ⊥ := by
    rw [ne_eq, Subgroup.eq_bot_iff_card, hcard₁]
    omega
  have hA₂ne : A.map (MonoidHom.snd Y₁ Y₂) ≠ ⊥ := by
    rw [ne_eq, Subgroup.eq_bot_iff_card, hcard₂]
    omega
  haveI hnt₁ : Nontrivial ↥(A.map (MonoidHom.fst Y₁ Y₂)) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hA₁ne
  haveI hnt₂ : Nontrivial ↥(A.map (MonoidHom.snd Y₁ Y₂)) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hA₂ne
  obtain ⟨a₁, ha₁, ha₁ne⟩ :=
    Subgroup.exists_ne_one_of_nontrivial (A.map (MonoidHom.fst Y₁ Y₂))
  obtain ⟨a₂, ha₂, ha₂ne⟩ :=
    Subgroup.exists_ne_one_of_nontrivial (A.map (MonoidHom.snd Y₁ Y₂))
  have ha₁A : (a₁, 1) ∈ A := by
    have hmem : (a₁, 1) ∈
        (A.map (MonoidHom.fst Y₁ Y₂)).prod (A.map (MonoidHom.snd Y₁ Y₂)) :=
      Subgroup.mem_prod.mpr ⟨ha₁, Subgroup.one_mem _⟩
    rw [← hAprod] at hmem
    exact hmem
  have ha₂A : ((1 : Y₁), a₂) ∈ A := by
    have hmem : ((1 : Y₁), a₂) ∈
        (A.map (MonoidHom.fst Y₁ Y₂)).prod (A.map (MonoidHom.snd Y₁ Y₂)) :=
      Subgroup.mem_prod.mpr ⟨Subgroup.one_mem _, ha₂⟩
    rw [← hAprod] at hmem
    exact hmem
  have hR : ∀ R : Subgroup (Y₁ × Y₂), IsPGroup 2 R →
      A ⊔ zpowers t ≤ normalizer (R : Set (Y₁ × Y₂)) → R = ⊥ :=
    fun R hRp hNR => eq_bot_of_isPGroup_of_sup_zpowers hm hmodd hcard₁ hcard₂ ht hinv
      hN₁ hN₂ hRp hNR
  have hZ : Subgroup.center (Y₁ × Y₂) = ⊥ := by
    rw [Subgroup.center_prod, hZ₁, hZ₂, Subgroup.bot_prod_bot]
  have hQinn : ∀ x : Y₁ × Y₂, MulAut.conj x ∈ Q → x = 1 :=
    fun x hx => eq_one_of_conj_mem_of_forall_isPGroup_eq_bot hZ hQ hQB hR hx
  have hfix : ∀ α ∈ Q, ∀ b ∈ A ⊔ zpowers t, α b = b :=
    apply_eq_of_forall_isPGroup_eq_bot hZ hQ hQB hR
  refine ⟨hcard₁, hcard₂, hQinn, ?_⟩
  intro α hα
  exact exists_mulAut_prod_eq_of_mem_of_fixes ha₁A ha₂A ha₁ne ha₂ne hQ hα
    (fun a ha => hfix α hα a (Subgroup.mem_sup_left ha))

end CFSG.GroupTheory

end
