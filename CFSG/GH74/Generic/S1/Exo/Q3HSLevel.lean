module

public import CFSG.GH74.Generic.S1.Exo.Q3HLemmas
public import CFSG.GH74.Generic.S1.Exo.Q3HNoQ8Alt
public import CFSG.GH74.Generic.S1.Exo.Q3HNoQ8L2
public import CFSG.GH74.GLS.LU.Local.L3InvAll
public import CFSG.GH74.Generic.S1.Exo.Q3HReduce

public section

namespace CFSG.GH74.Generic.S1.Exo

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Filter.ClassicalOdd CFSG.Assembly CFSG.Assembly.LowTwoRank Subgroup
open scoped commutatorElement

theorem isPGroup_two_of_sq {S : Type} [Group S] (E : Subgroup S) (hE2 : ∀ a ∈ E, a * a = 1) : IsPGroup 2 E := by
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  have := hE2 g g.2
  rw [Subgroup.coe_pow, Subgroup.coe_one, pow_one, pow_two]; exact this

theorem twoRank_eq_two {S : Type} [Group S] [Finite S]
    (hle : ∀ E : Subgroup S, (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → (∀ a ∈ E, a * a = 1) → Nat.card E ≤ 4)
    (hge : 2 ≤ twoRank S) : twoRank S = 2 := by
  classical
  have hbdd : BddAbove {k | ∃ E : Subgroup S, E ≤ ⊤ ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ k} :=
    ⟨Nat.card S, fun k ⟨E, _, _, hk⟩ => (Nat.lt_two_pow_self).le.trans
      (hk ▸ Subgroup.card_le_card_group E)⟩
  refine le_antisymm ?_ hge
  unfold CFSG.Assembly.twoRank CFSG.Assembly.pRank
  have hne : {k | ∃ E : Subgroup S, E ≤ ⊤ ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ k}.Nonempty :=
    ⟨0, ⊥, le_top, ⟨⟨⟨fun a b => Subsingleton.elim _ _⟩⟩, fun x hx => by
      rw [Subgroup.mem_bot.1 hx, one_pow]⟩, by simp⟩
  refine csSup_le hne ?_
  rintro k ⟨E, -, ⟨hc, hE2'⟩, hk⟩
  have hc' : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb => by
    have := hc.1.comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val this
  have hE2 : ∀ a ∈ E, a * a = 1 := fun a ha => by rw [← pow_two]; exact hE2' a ha
  have h4 := hle E hc' hE2
  by_contra hk3
  push Not at hk3
  have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
  omega

theorem exists_four_of_twoRank_eq_two {S : Type} [Group S] [Finite S] (h : twoRank S = 2) :
    ∃ E : Subgroup S, (∀ a ∈ E, a * a = 1) ∧ Nat.card E = 4 := by
  classical
  have hbdd : BddAbove {k | ∃ E : Subgroup S, E ≤ ⊤ ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ k} :=
    ⟨Nat.card S, fun k ⟨E, _, _, hk⟩ => (Nat.lt_two_pow_self).le.trans
      (hk ▸ Subgroup.card_le_card_group E)⟩
  have hne : {k | ∃ E : Subgroup S, E ≤ ⊤ ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ k}.Nonempty :=
    ⟨0, ⊥, le_top, ⟨⟨⟨fun a b => Subsingleton.elim _ _⟩⟩, fun x hx => by
      rw [Subgroup.mem_bot.1 hx, one_pow]⟩, by simp⟩
  have hmem := Nat.sSup_mem hne hbdd
  unfold CFSG.Assembly.twoRank CFSG.Assembly.pRank at h
  rw [h] at hmem
  obtain ⟨E, -, ⟨-, hE2'⟩, hk⟩ := hmem
  exact ⟨E, fun a ha => by rw [← pow_two]; exact hE2' a ha, by rw [hk]; norm_num⟩

theorem false_of_l3Eps_five {S : Type} [Group S] [Finite S] {δ : ℤ} {q : ℕ} (hδ : δ = 1 ∨ δ = -1) (hq : Odd q)
    (h5 : 5 ≤ q) (hS : CFSG.GH74.GLS.IVK.IsLnEps 3 S δ q) {s : S} (hs : s * s = 1) (hs1 : s ≠ 1)
    (E : Subgroup S) (hE2 : ∀ a ∈ E, a * a = 1) (h4 : 4 ≤ Nat.card E)
    (hperf : ∀ M : Subgroup S, ⁅M, M⁆ = M → M ≤ centralizer ({s} : Set S) → M = ⊥) : False := by
  classical
  obtain ⟨b, hb2, hb1, hbs, hbc⟩ := exists_commuting_involution hs hs1 E hE2 h4
  have hso : orderOf s = 2 := orderOf_eq_prime (by rw [pow_two]; exact hs) hs1
  have hbo : orderOf b = 2 := orderOf_eq_prime (by rw [pow_two]; exact hb2) hb1
  have hcard := CFSG.GH74.GLS.LU.Local.l3InvTorus S δ q hδ hq h5 hS s b hso hbo hbs.symm hbc.symm
  have hEz : CFSG.GH74.GLS.IVK.Ez s = ⊥ := by
    apply hperf
    · unfold CFSG.GH74.GLS.IVK.Ez
      rw [← Subgroup.map_commutator, CFSG.LocalCores.layer_perfect]
    · rintro _ ⟨x, -, rfl⟩
      exact x.2
  rw [hEz, inf_bot_eq, Subgroup.card_bot] at hcard
  have : (q : ℤ) - δ ≥ 4 := by rcases hδ with rfl | rfl <;> omega
  omega

@[expose] def RankTwoConcl (G : Type) [Group G] : Prop :=
  (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ StatedClassicalModel G .PSL 2 p f) ∨
  (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ StatedClassicalModel G .PSL 3 p f) ∨
  (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ StatedClassicalModel G .PSU 3 p f) ∨
  StatedClassicalModel G .PSU 3 2 2 ∨
  Nonempty (G ≃* alternatingGroup (Fin 7)) ∨
  Nonempty (G ≃* StatedM11)

@[expose] def RankTwoStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) → twoRank G = 2 → RankTwoConcl G

theorem q3_S_cases (hR : RankTwoStmt) {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hnonab : ∃ a b : S, a * b ≠ b * a)
    (hle : ∀ E : Subgroup S, (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → (∀ a ∈ E, a * a = 1) → Nat.card E ≤ 4)
    (ψ : Q8 →* S) (hψ : Function.Injective ψ)
    (hperf : ∀ M : Subgroup S, ⁅M, M⁆ = M → M ≤ centralizer ({ψ (QuaternionGroup.a 2)} : Set S) → M = ⊥)
    (P : Subgroup S) (hP360 : Nat.card P = 360) : Nonempty (S ≃* StatedM11) := by
  classical
  have hPdvd : 360 ∣ Nat.card S := hP360 ▸ Subgroup.card_subgroup_dvd_card P
  have heven : Even (Nat.card S) := even_iff_two_dvd.2 (dvd_trans (by norm_num) hPdvd)
  have h2 : twoRank S = 2 := twoRank_eq_two hle (CFSG.Walter.two_le_twoRank S hnonab heven)
  obtain ⟨E, hE2, hE4⟩ := exists_four_of_twoRank_eq_two h2
  have hzsq : ψ (QuaternionGroup.a 2) * ψ (QuaternionGroup.a 2) = 1 := by
    rw [← map_mul, q8_z_sq, map_one]
  have hz1 : ψ (QuaternionGroup.a 2) ≠ 1 := by
    intro h
    exact q8_z_ne (hψ (h.trans (map_one ψ).symm))
  rcases hR S hnonab h2 with ⟨p, f, hp, hp2, hf, h⟩ | ⟨p, f, hp, hp2, hf, h⟩ | ⟨p, f, hp, hp2, hf, h⟩ | h | h7 | h
  · exact (no_q8_of_psl2_model hp hp2 h ψ hψ).elim
  ·
    have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    have h3 : 3 ≤ p ^ f := by
      have : 3 ≤ p := by have := hp.two_le; omega
      exact this.trans (Nat.le_self_pow (by omega) p)
    by_cases h5 : 5 ≤ p ^ f
    · exact (false_of_l3Eps_five (Or.inl rfl) hodd h5 (isLnEps_of_model (Or.inl ⟨rfl, h⟩)) hzsq hz1 E hE2
        (by omega) hperf).elim
    · have hq3 : p ^ f = 3 := by
        have := hodd; rw [Nat.odd_iff] at this; omega
      have hcard := card_of_model hp hf (Or.inl ⟨rfl, h⟩)
      rw [hq3] at hcard
      have : l3Card 1 3 = 5616 := by simp [l3Card, pslCard]
      rw [this] at hcard
      rw [hcard] at hPdvd
      omega
  ·
    have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    have h3 : 3 ≤ p ^ f := by
      have : 3 ≤ p := by have := hp.two_le; omega
      exact this.trans (Nat.le_self_pow (by omega) p)
    by_cases h5 : 5 ≤ p ^ f
    · exact (false_of_l3Eps_five (Or.inr rfl) hodd h5 (isLnEps_of_model (Or.inr ⟨rfl, h⟩)) hzsq hz1 E hE2
        (by omega) hperf).elim
    · have hq3 : p ^ f = 3 := by
        have := hodd; rw [Nat.odd_iff] at this; omega
      have hcard := card_of_model hp hf (Or.inr ⟨rfl, h⟩)
      rw [hq3] at hcard
      have : l3Card (-1) 3 = 6048 := by simp [l3Card, psuCard]
      rw [this] at hcard
      rw [hcard] at hPdvd
      omega
  ·
    have hcard := card_of_model Nat.prime_two (by norm_num : 1 ≤ 2) (Or.inr ⟨rfl, h⟩)
    have : l3Card (-1) (2 ^ 2) = 62400 := by simp [l3Card, psuCard]
    rw [this] at hcard
    rw [hcard] at hPdvd
    omega
  · obtain ⟨e⟩ := h7
    exact (no_q8_of_alt7 e ψ hψ).elim
  · exact h

end CFSG.GH74.Generic.S1.Exo
