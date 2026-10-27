module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Basic

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup

@[expose] def IsTwoLocalIn {H : Type} [Group H] (N₀ K₁ : Subgroup H) : Prop :=
  ∃ R : Subgroup H, R ≠ ⊥ ∧ IsPGroup 2 R ∧ R ≤ K₁ ∧ N₀ = normalizer (R : Set H) ⊓ K₁

@[expose] def IsSectionOf (X : Type) [Group X] (Y : Type) [Group Y] : Prop :=
  ∃ (A : Subgroup Y) (f : ↥A →* X), Function.Surjective f

@[expose] def CanLoc {H : Type} [Group H] (K₁ N₀ : Subgroup H) : Prop :=
  (Even (Nat.card ↥(center ↥K₁)) ∧ N₀ = K₁) ∨
    (Odd (Nat.card ↥(center ↥K₁)) ∧ ∃ R : Subgroup H, R ≠ ⊥ ∧ R ≤ K₁ ∧
      Nat.card ↥R = 2 ^ (Nat.card ↥K₁).factorization 2 ∧ N₀ = normalizer (R : Set H) ⊓ K₁)

variable {H : Type} [Group H] {K₁ N₀ : Subgroup H}

theorem CanLoc.le (h : CanLoc K₁ N₀) : N₀ ≤ K₁ := by
  rcases h with ⟨-, rfl⟩ | ⟨-, R, -, -, -, rfl⟩
  · exact le_rfl
  · exact inf_le_right

theorem isPGroup_two_of_card_eq {R : Subgroup H} {k : ℕ} (h : Nat.card ↥R = 2 ^ k) :
    IsPGroup 2 ↥R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsPGroup.of_card h

theorem CanLoc.isTwoLocalIn [Finite H] (h : CanLoc K₁ N₀) : IsTwoLocalIn N₀ K₁ := by
  rcases h with ⟨hev, hN⟩ | ⟨-, R, hR0, hRK, hRc, rfl⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(center ↥K₁)) 2
      (even_iff_two_dvd.1 hev)
    have hz2 : orderOf ((z : ↥K₁) : H) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
      exact hz
    set x : H := ((z : ↥K₁) : H) with hx
    have hxc : ∀ k ∈ K₁, k * x = x * k := fun k hk =>
      congrArg Subtype.val (Subgroup.mem_center_iff.1 z.2 ⟨k, hk⟩)
    refine ⟨zpowers x, ?_, ?_, ?_, ?_⟩
    · rw [Ne, Subgroup.zpowers_eq_bot]
      intro h1
      rw [h1, orderOf_one] at hz2
      omega
    · exact isPGroup_two_of_card_eq (k := 1) (by rw [Nat.card_zpowers, hz2]; norm_num)
    · exact Subgroup.zpowers_le.2 (z : ↥K₁).2
    · rw [hN]
      refine le_antisymm (le_inf ?_ le_rfl) inf_le_right
      intro k hk
      refine Subgroup.centralizer_le_normalizer (zpowers x : Set H) ?_
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
      exact ((Commute.zpow_left (hxc k hk).symm m)).eq
  · exact ⟨R, hR0, isPGroup_two_of_card_eq hRc, hRK, rfl⟩

theorem CanLoc.map {H' : Type} [Group H'] (e : H ≃* H') (h : CanLoc K₁ N₀) :
    CanLoc (K₁.map e.toMonoidHom) (N₀.map e.toMonoidHom) := by
  have hcard : Nat.card ↥(center ↥(K₁.map e.toMonoidHom)) = Nat.card ↥(center ↥K₁) :=
    Nat.card_congr (Subgroup.centerCongr
      (Subgroup.equivMapOfInjective K₁ e.toMonoidHom e.injective)).toEquiv.symm
  have hK : Nat.card ↥(K₁.map e.toMonoidHom) = Nat.card ↥K₁ :=
    Nat.card_congr (Subgroup.equivMapOfInjective K₁ e.toMonoidHom e.injective).toEquiv.symm
  rcases h with ⟨hev, rfl⟩ | ⟨hodd, R, hR0, hRK, hRc, rfl⟩
  · exact Or.inl ⟨hcard ▸ hev, rfl⟩
  · refine Or.inr ⟨hcard ▸ hodd, R.map e.toMonoidHom, ?_, Subgroup.map_mono hRK, ?_, ?_⟩
    · rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ e.injective]
      exact hR0
    · rw [hK, ← hRc]
      exact (Nat.card_congr
        (Subgroup.equivMapOfInjective R e.toMonoidHom e.injective).toEquiv.symm)
    · rw [Subgroup.map_inf _ _ _ e.injective, Subgroup.map_equiv_normalizer_eq]

theorem exists_canLoc [Finite H] (K₁ : Subgroup H) (hev : Even (Nat.card ↥K₁)) :
    ∃ N₀ : Subgroup H, CanLoc K₁ N₀ := by
  rcases Nat.even_or_odd (Nat.card ↥(center ↥K₁)) with hc | hc
  · exact ⟨K₁, Or.inl ⟨hc, rfl⟩⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨P⟩ : Nonempty (Sylow 2 ↥K₁) := inferInstance
    refine ⟨normalizer ((P.map K₁.subtype : Subgroup H) : Set H) ⊓ K₁,
      Or.inr ⟨hc, P.map K₁.subtype, ?_, ?_, ?_, rfl⟩⟩
    · rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ K₁.subtype_injective]
      intro hP
      have h1 : Nat.card ↥(P : Subgroup ↥K₁) = 1 := by rw [hP]; simp
      have h2 := P.card_eq_multiplicity
      have h3 : 2 ∣ Nat.card ↥K₁ := even_iff_two_dvd.1 hev
      have hpos : 0 < Nat.card ↥K₁ := Nat.card_pos
      have h4 : 0 < (Nat.card ↥K₁).factorization 2 :=
        (Nat.Prime.factorization_pos_of_dvd Nat.prime_two hpos.ne' h3)
      rw [h1] at h2
      have : 2 ^ (Nat.card ↥K₁).factorization 2 ≥ 2 := by
        calc 2 ^ (Nat.card ↥K₁).factorization 2 ≥ 2 ^ 1 :=
              Nat.pow_le_pow_right (by norm_num) h4
          _ = 2 := by norm_num
      omega
    · rintro _ ⟨x, -, rfl⟩
      exact x.2
    · rw [Subgroup.card_map_of_injective K₁.subtype_injective]
      exact P.card_eq_multiplicity

end CFSG.EvenSporadicStandard.Induction
