module

public import CFSG.LargeExtraspecial.S3Fusion

public section

namespace CFSG.LargeExtraspecial.S11

open Subgroup

variable {H : Type*} [Group H] [Finite H] {X N L : Subgroup H}

omit [Finite H] in
theorem exists_mul_of_mem_sup {P N : Subgroup H}
    (hPN : P ≤ normalizer (N : Set H)) {y : H} (hy : y ∈ P ⊔ N) :
    ∃ a ∈ P, ∃ b ∈ N, a * b = y := by
  have hy' : y ∈ ((P ⊔ N : Subgroup H) : Set H) := hy
  rw [coe_mul_of_left_le_normalizer_right P N hPN] at hy'
  exact Set.mem_mul.mp hy'

theorem mem_sup_of_conj_mem_of_comm (hLX : L ≤ X)
    (hNn : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hL : IsPGroup 2 L)
    (hLc : ∀ a ∈ L, ∀ b ∈ L, a * b = b * a)
    (hw : ∀ x ∈ X, (∀ l ∈ L, ∀ l₂ ∈ L, x * l * x⁻¹ * l₂ * (x * l * x⁻¹)⁻¹ ∈ L ⊔ N) →
      L.map (MulAut.conj x).toMonoidHom = L)
    {x l : H} (hx : x ∈ X) (hl : l ∈ L)
    (hc : ∀ l₂ ∈ L, x * l * x⁻¹ * l₂ * (x * l * x⁻¹)⁻¹ * l₂⁻¹ ∈ N) :
    x * l * x⁻¹ ∈ L ⊔ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : (N.subgroupOf X).Normal := ⟨fun n hn y => by
    rw [mem_subgroupOf] at hn ⊢
    exact hNn y y.2 n hn⟩
  have hLN : L ≤ normalizer (N : Set H) := fun y hy =>
    mem_normalizer_iff.mpr fun n => ⟨fun hn => hNn y (hLX hy) n hn, fun hn => by
      have := hNn y⁻¹ (inv_mem (hLX hy)) _ hn
      rwa [show y⁻¹ * (y * n * y⁻¹) * y⁻¹⁻¹ = n by group] at this⟩
  obtain ⟨π, hπ⟩ : ∃ f : X →* X ⧸ N.subgroupOf X, f = QuotientGroup.mk' (N.subgroupOf X) :=
    ⟨_, rfl⟩
  have hπs : Function.Surjective π := hπ ▸ QuotientGroup.mk'_surjective _
  have hπeq : ∀ a b : X, π a = π b ↔ a⁻¹ * b ∈ N.subgroupOf X := fun a b => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  obtain ⟨T, hT⟩ : ∃ T : Subgroup (X ⧸ N.subgroupOf X), T = (L.subgroupOf X).map π := ⟨_, rfl⟩
  have hTmem : ∀ v : X, π v ∈ T ↔ (v : H) ∈ L ⊔ N := by
    intro v
    rw [hT]
    constructor
    · rintro ⟨w, hw', hwv⟩
      rw [hπeq, mem_subgroupOf] at hwv
      have hw0 : (w : H) ∈ L := hw'
      have e : (v : H) = (w : H) * ((w⁻¹ * v : X) : H) := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
      rw [e]
      exact mul_mem (mem_sup_left hw0) (mem_sup_right hwv)
    · intro hv
      obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup hLN hv
      refine ⟨⟨a, hLX ha⟩, mem_subgroupOf.mpr ha, ?_⟩
      rw [hπeq, mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, ← hab]
      simpa using hb
  have hπT : ∀ w : X, (w : H) ∈ L → π w ∈ T := fun w hw => by
    rw [hT]; exact ⟨w, mem_subgroupOf.mpr hw, rfl⟩
  have hTπ : ∀ t ∈ T, ∃ w : X, (w : H) ∈ L ∧ π w = t := fun t ht => by
    rw [hT] at ht
    obtain ⟨w, hw, rfl⟩ := ht
    exact ⟨w, mem_subgroupOf.mp hw, rfl⟩
  have hT2 : IsPGroup 2 T := hT ▸ (hL.of_equiv (subgroupOfEquivOfLe hLX).symm).map _
  have hTc : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := by
    intro a ha b hb
    obtain ⟨a', ha', rfl⟩ := hTπ a ha
    obtain ⟨b', hb', rfl⟩ := hTπ b hb
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hLc _ ha' _ hb')
  have hTw : IsWeaklyClosedInNormalizer T := by
    intro γ hγ
    obtain ⟨x', rfl⟩ := hπs γ
    have hLx : L.map (MulAut.conj (x' : H)).toMonoidHom = L := by
      refine hw x' x'.2 fun l hl l₂ hl₂ => ?_
      have h1 : π (x' * ⟨l, hLX hl⟩ * x'⁻¹) ∈ normalizer (T : Set (X ⧸ N.subgroupOf X)) := by
        refine hγ ⟨π ⟨l, hLX hl⟩, hπT _ hl, ?_⟩
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_mul, map_inv]
      have h2 := (mem_normalizer_iff.mp h1 (π ⟨l₂, hLX hl₂⟩)).mp (hπT _ hl₂)
      rw [← map_inv, ← map_mul, ← map_mul] at h2
      exact (hTmem _).mp h2
    ext γ'
    constructor
    · rintro ⟨_, ht, rfl⟩
      obtain ⟨w, hw', rfl⟩ := hTπ _ ht
      have hmem : ((x' * w * x'⁻¹ : X) : H) ∈ L.map (MulAut.conj (x' : H)).toMonoidHom :=
        ⟨w, hw', rfl⟩
      rw [hLx] at hmem
      have := hπT _ hmem
      rw [map_mul, map_mul, map_inv] at this
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact this
    · intro ht
      obtain ⟨w, hw', rfl⟩ := hTπ _ ht
      have hw0 : (w : H) ∈ L.map (MulAut.conj (x' : H)).toMonoidHom := by
        rw [hLx]; exact hw'
      have hw1 : ((x'⁻¹ * w * x' : X) : H) ∈ L := by
        obtain ⟨l, hl, hlw⟩ := hw0
        have e : ((x'⁻¹ * w * x' : X) : H) = l := by
          rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hlw]
          simp [mul_assoc]
        rw [e]; exact hl
      refine ⟨π (x'⁻¹ * w * x'), hπT _ hw1, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
      congr 1
      group
  have hsc := lemma_3_12_isStronglyClosedIn hT2 hTc hTw
  have hlX : l ∈ X := hLX hl
  have huX : x * l * x⁻¹ ∈ X := mul_mem (mul_mem hx hlX) (inv_mem hx)
  have ha : π ⟨l, hlX⟩ ∈ T := hπT _ hl
  have e : (π ⟨x⁻¹, inv_mem hx⟩)⁻¹ * π ⟨l, hlX⟩ * π ⟨x⁻¹, inv_mem hx⟩ =
      π ⟨x * l * x⁻¹, huX⟩ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (by simp)
  have hcent : π ⟨x * l * x⁻¹, huX⟩ ∈ centralizer (T : Set (X ⧸ N.subgroupOf X)) := by
    rw [mem_centralizer_iff]
    intro t ht
    obtain ⟨w, hw', rfl⟩ := hTπ t ht
    rw [← map_mul, ← map_mul, hπeq, mem_subgroupOf]
    have h1 := hc w hw'
    have hwX : (w : H) ∈ X := w.2
    have h2 := hNn ((x * l * x⁻¹)⁻¹ * (w : H)⁻¹) (mul_mem (inv_mem huX) (inv_mem hwX)) _ h1
    have e2 : (((w * ⟨x * l * x⁻¹, huX⟩)⁻¹ * (⟨x * l * x⁻¹, huX⟩ * w) : X) : H) =
        (x * l * x⁻¹)⁻¹ * (w : H)⁻¹ * (x * l * x⁻¹ * w * (x * l * x⁻¹)⁻¹ * (w : H)⁻¹) *
          ((x * l * x⁻¹)⁻¹ * (w : H)⁻¹)⁻¹ := by
      push_cast
      group
    rw [e2]
    exact h2
  have hmem := hsc.2 _ ha (π ⟨x⁻¹, inv_mem hx⟩) (by rw [e]; exact hcent)
  rw [e] at hmem
  exact (hTmem _).mp hmem

end CFSG.LargeExtraspecial.S11
