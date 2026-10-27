module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.L2Dim
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.LnLift

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.Quasithin CFSG.SectionRank.OddCover CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

variable {W : Type} [CommGroup W] [Finite W]

theorem two_pow_le_card_of_field_root (hW : ∀ w : W, w * w = 1) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {L : Subgroup (MulAut W)} {S : Type} [Group S] (π : ↥L →* S)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center ↥L)
    (hZ : ¬ p ∣ Nat.card π.ker) {F : Type} [Field F] [Finite F] [CharP F p]
    (u : Multiplicative F →* S) (hu : Function.Injective u) (t : Fˣ →* S)
    (htu : ∀ (b : Fˣ) (a : F), t b * u (Multiplicative.ofAdd a) * (t b)⁻¹ =
      u (Multiplicative.ofAdd ((b : F) ^ 2 * a))) :
    2 ^ (orderOf (2 : ZMod p) * ((Nat.card F - 1) / (2 * (p - 1)))) ≤ Nat.card W := by
  classical
  have hUc : ∀ a ∈ u.range, ∀ b ∈ u.range, a * b = b * a := by
    rintro _ ⟨s, rfl⟩ _ ⟨r, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  have hUp : ∀ a ∈ u.range, a ^ p = 1 := by
    rintro _ ⟨r, rfl⟩
    rw [← map_pow, multiplicative_pow_char_eq_one, map_one]
  have hU1 : u.range ≠ ⊥ := by
    intro h
    have hm : u (Multiplicative.ofAdd (1 : F)) ∈ u.range := ⟨_, rfl⟩
    rw [h, Subgroup.mem_bot, ← map_one u] at hm
    have := hu hm
    simp at this
  have hTN : t.range ≤ Subgroup.normalizer (u.range : Set S) := by
    rintro _ ⟨a, rfl⟩
    rw [Subgroup.mem_set_normalizer_iff]
    intro h
    constructor
    · rintro ⟨s, rfl⟩
      refine ⟨Multiplicative.ofAdd ((a : F) ^ 2 * s.toAdd), ?_⟩
      rw [← htu a s.toAdd, ofAdd_toAdd]
    · rintro ⟨s', hs'⟩
      have e : h = t a⁻¹ * u s' * (t a⁻¹)⁻¹ := by rw [map_inv, hs']; group
      refine ⟨Multiplicative.ofAdd (((a⁻¹ : Fˣ) : F) ^ 2 * s'.toAdd), ?_⟩
      rw [← htu a⁻¹ s'.toAdd, ofAdd_toAdd, ← e]
  have hunits : Nat.card Fˣ = Nat.card F - 1 := by
    have := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_units]
  let P : Fˣ → Prop := fun a => ((a : F) ^ 2) ^ p = (a : F) ^ 2
  have horb : ∀ D : Subgroup S, D ≤ u.range → D.relIndex u.range = p →
      (Nat.card F - 1) / (2 * (p - 1)) ≤
        (t.range ⊓ Subgroup.normalizer (D : Set S)).relIndex t.range := by
    intro D hDU hrel
    obtain ⟨D'', hDD⟩ : ∃ D'' : Subgroup (Multiplicative F), D''.map u = D :=
      ⟨D.comap u, Subgroup.map_comap_eq_self hDU⟩
    have hidx : D''.index = p := by
      rw [← Subgroup.relIndex_top_right, ← Subgroup.relIndex_map_map_of_injective D'' ⊤ hu, hDD,
        ← MonoidHom.range_eq_map]
      exact hrel
    have hD'idx : (addOfMul D'').index = p := (index_addOfMul D'').trans hidx
    let T : Subgroup Fˣ := ((t.range ⊓ Subgroup.normalizer (D : Set S)).subgroupOf
      t.range).comap t.rangeRestrict
    have hTP : ∀ a ∈ T, P a := by
      intro a ha
      refine pow_char_eq_self_of_mul_mem (D := addOfMul D'') hD'idx ?_
      intro x hx
      have hN : t a ∈ Subgroup.normalizer (D : Set S) := (Subgroup.mem_inf.1 ha).2
      have hxD : u (Multiplicative.ofAdd x) ∈ D := by
        rw [← hDD]
        exact ⟨_, hx, rfl⟩
      have h1 := (Subgroup.mem_set_normalizer_iff.1 hN _).1 hxD
      rw [htu, ← hDD] at h1
      obtain ⟨y, hy, hyeq⟩ := h1
      have h2 := hu hyeq
      show Multiplicative.ofAdd ((a : F) ^ 2 * x) ∈ D''
      rw [← h2]
      exact hy
    have hTle : Nat.card T ≤ 2 * (p - 1) :=
      (Nat.card_le_card_of_injective (fun a : T => (⟨a.1, hTP a.1 a.2⟩ : {a : Fˣ // P a}))
        (fun a b h => Subtype.ext (Subtype.mk.inj h))).trans card_sq_pow_char_le
    have hindex : T.index = (t.range ⊓ Subgroup.normalizer (D : Set S)).relIndex t.range := by
      rw [Subgroup.relIndex]
      exact Subgroup.index_comap_of_surjective _ t.rangeRestrict_surjective
    have hcard : Nat.card T * T.index = Nat.card Fˣ := Subgroup.card_mul_index T
    rw [← hindex]
    apply Nat.div_le_of_le_mul
    calc Nat.card F - 1 = Nat.card T * T.index := by rw [hcard, hunits]
      _ ≤ (2 * (p - 1)) * T.index := Nat.mul_le_mul_right _ hTle
  have h := two_pow_le_card_of_lift_orbit hW hp2 π hπ hker hZ hUc hUp hU1 hTN horb
  rwa [mul_comm] at h

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
