module

public import CFSG.LocalAnalysis.EvenBN.U4.Prelim.Semilinear

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem even_relIndex_of_isPGroup {H X : Subgroup Γ} {t : Γ} (hXH : X ≤ H)
    (hX : IsPGroup 2 X)
    (hlt : ∀ S : Subgroup Γ, S ≤ H ⊓ centralizer ({t} : Set Γ) → IsPGroup 2 S →
      Nat.card S < Nat.card X) :
    Even ((centralizer ({t} : Set Γ)).relIndex H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hX
  set C := H ⊓ centralizer ({t} : Set Γ) with hC
  have hHC : Nat.card H = (centralizer ({t} : Set Γ)).relIndex H * Nat.card C := by
    rw [← relIndex_mul_card (centralizer ({t} : Set Γ)) H, hC, inf_comm]
  have hdvd : 2 ^ n ∣ Nat.card C := by
    have h1 : 2 ^ n ∣ Nat.card H := hn ▸ card_dvd_of_le hXH
    rw [hHC] at h1
    exact (Nat.Coprime.pow_left n (Nat.coprime_two_left.2 hodd)).dvd_of_dvd_mul_left h1
  obtain ⟨S, hS⟩ := Sylow.exists_subgroup_card_pow_prime 2 (G := C) hdvd
  have hS' : IsPGroup 2 (S.map C.subtype) :=
    (IsPGroup.of_card (n := n) hS).map _
  have := hlt (S.map C.subtype) (map_subtype_le _) hS'
  rw [card_map_of_injective C.subtype_injective, hS, ← hn] at this
  exact lt_irrefl _ this

theorem conj_mem_of_orbit_even {Q A H C : Subgroup Γ} {t : Γ} (hAQ : A ≤ Q) (htQ : t ∈ Q)
    (htA : t ∉ A) (ht2 : t * t = 1) (hQ : ∀ x ∈ Q, x ∈ A ∨ t * x ∈ A)
    (hHQ : H ≤ normalizer (Q : Set Γ)) (hCH : C ≤ H ⊓ centralizer ({t} : Set Γ))
    (htrans : ∀ a ∈ A, a ≠ 1 → ∀ a' ∈ A, a' ≠ 1 → ∃ c ∈ C, c⁻¹ * a * c = a')
    (heven : Even ((centralizer ({t} : Set Γ)).relIndex H)) (hA2 : 2 < Nat.card A) :
    (∀ g ∈ H, t * (g⁻¹ * t * g) ∈ A) ∧ H ≤ normalizer (A : Set Γ) ∧
      (centralizer ({t} : Set Γ)).relIndex H = Nat.card A := by
  classical
  set O : Set Γ := {x | ∃ g ∈ H, x = g⁻¹ * t * g} with hO
  have hcardO : Nat.card O = (centralizer ({t} : Set Γ)).relIndex H :=
    card_conj_set_eq_relIndex H t
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have htO : t ∈ O := ⟨1, one_mem _, by group⟩
  have hOinv : ∀ g ∈ H, ∀ x ∈ O, g⁻¹ * x * g ∈ O := by
    rintro g hg _ ⟨k, hk, rfl⟩
    exact ⟨k * g, mul_mem hk hg, by group⟩
  have hOQ : ∀ x ∈ O, x ∈ Q := by
    rintro _ ⟨g, hg, rfl⟩
    have := (mem_normalizer_iff.1 (hHQ (inv_mem hg)) t).1 htQ
    rwa [inv_inv] at this
  have hO1 : ∀ x ∈ O, x ≠ 1 := by
    rintro _ ⟨g, hg, rfl⟩ e
    apply htA
    have : t = 1 := by
      calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
        _ = 1 := by rw [e]; group
    rw [this]
    exact one_mem _
  have htmul : ∀ a ∈ A, t * (t * a) = a := fun a _ => by rw [← mul_assoc, ht2, one_mul]
  have htrans' : ∀ a ∈ A, a ≠ 1 → t * a ∈ O → ∀ a' ∈ A, a' ≠ 1 → t * a' ∈ O := by
    intro a ha ha1 hta a' ha' ha'1
    obtain ⟨c, hc, e⟩ := htrans a ha ha1 a' ha' ha'1
    have hct : c⁻¹ * t * c = t := by
      have hct' : c * t = t * c := mem_centralizer_singleton_iff.1 (mem_inf.1 (hCH hc)).2
      calc c⁻¹ * t * c = c⁻¹ * (c * t) := by rw [mul_assoc, hct']
        _ = t := by group
    have := hOinv c (mem_inf.1 (hCH hc)).1 _ hta
    rwa [show c⁻¹ * (t * a) * c = (c⁻¹ * t * c) * (c⁻¹ * a * c) by group, hct, e] at this
  have hQset : (Q : Set Γ) = (A : Set Γ) ∪ (fun a => t * a) '' (A : Set Γ) := by
    ext x
    constructor
    · intro hx
      rcases hQ x hx with hxA | hxA
      · exact Or.inl hxA
      · exact Or.inr ⟨t * x, hxA, by show t * (t * x) = x; rw [← mul_assoc, ht2, one_mul]⟩
    · rintro (hx | ⟨a, ha, rfl⟩)
      · exact hAQ hx
      · exact mul_mem htQ (hAQ ha)
  have hdisj : Disjoint (A : Set Γ) ((fun a => t * a) '' (A : Set Γ)) := by
    rw [Set.disjoint_left]
    rintro _ hx ⟨a, ha, rfl⟩
    apply htA
    have := mul_mem hx (inv_mem ha)
    rwa [mul_inv_cancel_right] at this
  have hQcard : Nat.card Q = 2 * Nat.card A := by
    rw [← SetLike.coe_sort_coe Q, Nat.card_coe_set_eq, ← SetLike.coe_sort_coe A,
      Nat.card_coe_set_eq, hQset, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _),
      Set.ncard_image_of_injective _ (mul_right_injective t), two_mul]
  have hOA : ∀ x ∈ O, x ∉ A := by
    intro x₀ hx₀O hx₀A
    have hx₀1 := hO1 x₀ hx₀O
    have hAO : ∀ a ∈ A, a ≠ 1 → a ∈ O := by
      intro a ha ha1
      obtain ⟨c, hc, e⟩ := htrans x₀ hx₀A hx₀1 a ha ha1
      rw [← e]
      exact hOinv c (mem_inf.1 (hCH hc)).1 x₀ hx₀O
    by_cases hB : ∃ a ∈ A, a ≠ 1 ∧ t * a ∈ O
    ·
      obtain ⟨a₀, ha₀, ha₀1, hta₀⟩ := hB
      have hOeq : O = (Q : Set Γ) \ {1} := by
        ext x
        constructor
        · intro hx
          exact ⟨hOQ x hx, hO1 x hx⟩
        · rintro ⟨hxQ, hx1⟩
          rcases hQ x hxQ with hxA | htx
          · exact hAO x hxA hx1
          · by_cases htx1 : t * x = 1
            · have : x = t := by
                calc x = t * (t * x) := by rw [← mul_assoc, ht2, one_mul]
                  _ = t := by rw [htx1, mul_one]
              rw [this]
              exact htO
            · have := htrans' a₀ ha₀ ha₀1 hta₀ (t * x) htx htx1
              rwa [← mul_assoc, ht2, one_mul] at this
      have hodd : Nat.card O = 2 * Nat.card A - 1 := by
        rw [hOeq, Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_of_mem (one_mem Q : (1 : Γ) ∈ Q),
          ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hQcard]
      rw [hcardO] at hodd
      rw [hodd] at heven
      have hpos : 0 < Nat.card A := Nat.card_pos
      obtain ⟨k, hk⟩ := heven
      omega
    ·
      push Not at hB
      obtain ⟨g, hg, hgt⟩ := hx₀O
      set B := A.map (MulAut.conj g).toMonoidHom with hBdef
      have hBmem : ∀ a ∈ A, g * a * g⁻¹ ∈ B := fun a ha =>
        ⟨a, ha, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
      have htB : t ∈ B := by
        have := hBmem x₀ hx₀A
        rwa [hgt, show g * (g⁻¹ * t * g) * g⁻¹ = t by group] at this
      have hBsub : ∀ b ∈ B, b ≠ t → b ∈ A := by
        rintro _ ⟨a, ha, rfl⟩ hbt
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hbt ⊢
        by_cases ha1 : a = 1
        · rw [ha1, mul_one, mul_inv_cancel]
          exact one_mem _
        have hbO : g * a * g⁻¹ ∈ O := by
          have := hOinv g⁻¹ (inv_mem hg) a (hAO a ha ha1)
          rwa [inv_inv] at this
        rcases hQ _ (hOQ _ hbO) with hbA | hbA
        · exact hbA
        · exfalso
          by_cases htb1 : t * (g * a * g⁻¹) = 1
          · apply hbt
            calc g * a * g⁻¹ = t * (t * (g * a * g⁻¹)) := by rw [← mul_assoc, ht2, one_mul]
              _ = t := by rw [htb1, mul_one]
          · exact hB _ hbA htb1 (by rwa [← mul_assoc, ht2, one_mul])
      have hBA : ((B ⊓ A : Subgroup Γ) : Set Γ) = (B : Set Γ) \ {t} := by
        ext b
        constructor
        · intro hb
          exact ⟨(mem_inf.1 hb).1, fun e => htA (e ▸ (mem_inf.1 hb).2)⟩
        · rintro ⟨hbB, hbt⟩
          exact mem_inf.2 ⟨hbB, hBsub b hbB hbt⟩
      have hcardB : Nat.card B = Nat.card A :=
        card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
      have hcardBA : Nat.card (B ⊓ A : Subgroup Γ) + 1 = Nat.card A := by
        rw [← SetLike.coe_sort_coe (B ⊓ A), Nat.card_coe_set_eq, hBA,
          Set.ncard_sdiff_singleton_add_one htB (Set.toFinite _), ← Nat.card_coe_set_eq,
          SetLike.coe_sort_coe, hcardB]
      have hdvd : Nat.card (B ⊓ A : Subgroup Γ) ∣ Nat.card B := card_dvd_of_le inf_le_left
      rw [hcardB] at hdvd
      have h1 : Nat.card (B ⊓ A : Subgroup Γ) ∣ 1 := by
        have h2 : Nat.card (B ⊓ A : Subgroup Γ) ∣ Nat.card (B ⊓ A : Subgroup Γ) + 1 := by
          rw [hcardBA]
          exact hdvd
        exact (Nat.dvd_add_right (dvd_refl _)).1 h2
      have h3 := Nat.le_of_dvd one_pos h1
      omega
  have hex : ∃ x ∈ O, x ≠ t := by
    by_contra hcon
    push Not at hcon
    have hsub : O = {t} := Set.eq_singleton_iff_unique_mem.2 ⟨htO, hcon⟩
    rw [hsub, Nat.card_coe_set_eq, Set.ncard_singleton] at hcardO
    rw [← hcardO] at heven
    exact Nat.not_even_one heven
  obtain ⟨x, hxO, hxt⟩ := hex
  have hx1 : t * x ∈ A := (hQ x (hOQ x hxO)).resolve_left (hOA x hxO)
  have htx1 : t * x ≠ 1 := fun e => hxt (by
    calc x = t * (t * x) := by rw [← mul_assoc, ht2, one_mul]
      _ = t := by rw [e, mul_one])
  have htxO : t * (t * x) ∈ O := by rwa [← mul_assoc, ht2, one_mul]
  have hall : ∀ a ∈ A, t * a ∈ O := by
    intro a ha
    by_cases ha1 : a = 1
    · rw [ha1, mul_one]
      exact htO
    · exact htrans' (t * x) hx1 htx1 htxO a ha ha1
  have hOeq : O = (fun a => t * a) '' (A : Set Γ) := by
    ext y
    constructor
    · intro hy
      have h1 := (hQ y (hOQ y hy)).resolve_left (hOA y hy)
      exact ⟨t * y, h1, by show t * (t * y) = y; rw [← mul_assoc, ht2, one_mul]⟩
    · rintro ⟨a, ha, rfl⟩
      exact hall a ha
  have hconj : ∀ k ∈ H, ∀ a ∈ A, k⁻¹ * a * k ∈ A := by
    intro k hk a ha
    have hkQ : k⁻¹ * a * k ∈ Q := by
      have := (mem_normalizer_iff.1 (hHQ (inv_mem hk)) a).1 (hAQ ha)
      rwa [inv_inv] at this
    rcases hQ _ hkQ with h1 | h1
    · exact h1
    · exfalso
      have hO' : k⁻¹ * a * k ∈ O := by
        have := hall _ h1
        rwa [← mul_assoc, ht2, one_mul] at this
      have := hOinv k⁻¹ (inv_mem hk) _ hO'
      rw [show k⁻¹⁻¹ * (k⁻¹ * a * k) * k⁻¹ = a by group] at this
      exact hOA a this ha
  refine ⟨fun g hg => ?_, fun g hg => ?_, ?_⟩
  · have hx : g⁻¹ * t * g ∈ O := ⟨g, hg, rfl⟩
    rcases hQ _ (hOQ _ hx) with h1 | h1
    · exact absurd h1 (hOA _ hx)
    · exact h1
  · refine mem_normalizer_fintype fun a ha => ?_
    have := hconj g⁻¹ (inv_mem hg) a ha
    rwa [inv_inv] at this
  · rw [← hcardO, hOeq, Nat.card_coe_set_eq, Set.ncard_image_of_injective _ (mul_right_injective t),
      ← Nat.card_coe_set_eq, SetLike.coe_sort_coe]

end CFSG.LocalAnalysis.EvenBN.U4
