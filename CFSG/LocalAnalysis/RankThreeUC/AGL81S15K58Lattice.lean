module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.GroupTheory.PGroup
public import Mathlib.RepresentationTheory.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K58Proof

open Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem normalizer_eq_self_of_lattice [IsSimpleGroup G] {S A B H : Subgroup G} {n : ℕ}
    (hlat : ∀ K : Subgroup G, S ≤ K → K = S ∨ K = A ∨ K = B ∨ K = ⊤) (hA : A.index = n)
    (hB : B.index = n) (hSidx : n < S.index) (hn : 1 < n) (hSH : S ≤ H) (hH : H.index = n) :
    normalizer (H : Set G) = H := by
  have hHN : H ≤ normalizer (H : Set G) := le_normalizer
  have hidx : ∀ K : Subgroup G, H ≤ K → K.index = n → K = H := fun K hHK hK => by
    have h1 := relIndex_mul_index hHK
    rw [hK, hH] at h1
    have h2 : H.relIndex K = 1 := by
      rcases Nat.lt_or_ge (H.relIndex K) 2 with h | h
      · have h0 : H.relIndex K ≠ 0 := by
          intro h0
          rw [h0, zero_mul] at h1
          omega
        omega
      · nlinarith
    exact le_antisymm (relIndex_eq_one.1 h2) hHK
  rcases hlat _ (hSH.trans hHN) with h | h | h | h
  · have hHS : H = S := le_antisymm (h ▸ hHN) hSH
    rw [hHS] at hH
    omega
  · exact hidx _ hHN (h ▸ hA)
  · exact hidx _ hHN (h ▸ hB)
  · exfalso
    have hnorm : H.Normal := normalizer_eq_top_iff.1 h
    rcases hnorm.eq_bot_or_eq_top with hb | ht
    · have hS : S = ⊥ := le_bot_iff.1 (hb ▸ hSH)
      rw [hb] at hH
      rw [hS] at hSidx
      omega
    · rw [ht, index_top] at hH
      omega

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem fixed_eq_pair_of_lattice (ρ : Representation (ZMod 2) G W) {n : ℕ}
    (hW : Nat.card W = n + 1) (hfix : ∀ w : W, (∀ g, ρ g w = w) → w = 0) {S A B : Subgroup G}
    (hS2 : IsPGroup 2 S) (hSidx : n < S.index)
    (hlat : ∀ H : Subgroup G, S ≤ H → H = S ∨ H = A ∨ H = B ∨ H = ⊤) (hA : A.index = n)
    (hB : B.index = n) (hAn : normalizer (A : Set G) = A) (hBn : normalizer (B : Set G) = B) :
    ∃ w₀ ≠ 0, (∀ w : W, (∀ s ∈ S, ρ s w = w) → w = 0 ∨ w = w₀) ∧
      ((∀ g, ρ g w₀ = w₀ ↔ g ∈ A) ∨ (∀ g, ρ g w₀ = w₀ ↔ g ∈ B)) := by
  classical
  have : Finite W := Nat.finite_of_card_ne_zero (by omega)
  let _ : MulAction G W := MulAction.compHom W ρ
  have hinv : ∀ (g : G) (w : W), ρ g⁻¹ (ρ g w) = w := fun g w => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hne0 : ∀ (g : G) (w : W), w ≠ 0 → ρ g w ≠ 0 := fun g w hw h =>
    hw (by rw [← hinv g w, h, map_zero])
  have hcard1 : {w : W | w ≠ 0}.ncard = n := by
    have h1 : {w : W | w ≠ 0} = Set.univ \ {0} := by
      ext w
      simp
    rw [h1, Set.ncard_sdiff (by simp), Set.ncard_univ, hW, Set.ncard_singleton]
    omega
  have hstab : ∀ v : W, v ≠ 0 → (∀ s ∈ S, ρ s v = v) →
      (MulAction.stabilizer G v = A ∨ MulAction.stabilizer G v = B) ∧
        MulAction.orbit G v = {w : W | w ≠ 0} := by
    intro v hv0 hvS
    have hSle : S ≤ MulAction.stabilizer G v := fun s hs => hvS s hs
    have hsub : MulAction.orbit G v ⊆ {w : W | w ≠ 0} := by
      rintro _ ⟨g, rfl⟩
      exact hne0 g v hv0
    have hle : (MulAction.orbit G v).ncard ≤ n := hcard1 ▸ Set.ncard_le_ncard hsub
    have hidx := MulAction.index_stabilizer G v
    rcases hlat _ hSle with h | h | h | h
    · rw [h] at hidx
      omega
    · refine ⟨Or.inl h, Set.eq_of_subset_of_ncard_le hsub ?_⟩
      rw [hcard1, ← hidx, h, hA]
    · refine ⟨Or.inr h, Set.eq_of_subset_of_ncard_le hsub ?_⟩
      rw [hcard1, ← hidx, h, hB]
    · exfalso
      exact hv0 (hfix v fun g => (show g ∈ MulAction.stabilizer G v from h ▸ mem_top g))
  have hsame : ∀ p q : W, p ≠ 0 → q ≠ 0 → (∀ s ∈ S, ρ s p = p) →
      MulAction.stabilizer G p = MulAction.stabilizer G q → p = q := by
    intro p q hp hq hpS hpq
    obtain ⟨hHp, horb⟩ := hstab p hp hpS
    have hq' : q ∈ MulAction.orbit G p := by rw [horb]; exact hq
    obtain ⟨g, rfl⟩ := hq'
    have h1 := MulAction.stabilizer_smul_eq_stabilizer_map_conj g p
    rw [← hpq] at h1
    have hgN : g ∈ normalizer ((MulAction.stabilizer G p : Subgroup G) : Set G) := by
      rw [mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        rw [h1]
        exact ⟨x, hx, rfl⟩
      · intro hx
        rw [h1] at hx
        obtain ⟨y, hy, hyx⟩ := hx
        have hxy : y = x := by
          have e : g * y * g⁻¹ = g * x * g⁻¹ := hyx
          simpa using e
        exact hxy ▸ hy
    have hg : g ∈ MulAction.stabilizer G p := by
      rcases hHp with h | h
      · rw [h, hAn] at hgN
        rwa [h]
      · rw [h, hBn] at hgN
        rwa [h]
    exact (hg : g • p = p).symm
  have huniq : ∀ v w : W, v ≠ 0 → w ≠ 0 → (∀ s ∈ S, ρ s v = v) → (∀ s ∈ S, ρ s w = w) →
      v = w := by
    intro v w hv0 hw0 hvS hwS
    by_contra hvw
    have huS : ∀ s ∈ S, ρ s (v + w) = v + w := fun s hs => by
      rw [map_add, hvS s hs, hwS s hs]
    have hu0 : v + w ≠ 0 := fun h => hvw (by
      have h2 : (2 : ZMod 2) = 0 := rfl
      have hvv : v + v = 0 := by rw [← two_smul (ZMod 2) v, h2, zero_smul]
      calc v = v + (v + w) := by rw [h, add_zero]
        _ = (v + v) + w := by abel
        _ = w := by rw [hvv, zero_add])
    have huv : v + w ≠ v := fun h => hw0 (by simpa using h)
    have huw : v + w ≠ w := fun h => hv0 (by simpa using h)
    rcases (hstab v hv0 hvS).1 with hv | hv <;> rcases (hstab w hw0 hwS).1 with hw | hw <;>
      rcases (hstab (v + w) hu0 huS).1 with hu | hu
    all_goals first
      | exact hvw (hsame v w hv0 hw0 hvS (hv.trans hw.symm))
      | exact huv (hsame _ _ hu0 hv0 huS (hu.trans hv.symm))
      | exact huw (hsame _ _ hu0 hw0 huS (hu.trans hw.symm))
  have hn0 : n ≠ 0 := by
    rw [← hA]
    exact index_ne_zero_of_finite
  have hW2 : 2 ∣ Nat.card W := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)
    rw [Nat.card_zmod] at hc
    rcases Nat.eq_zero_or_pos (Module.finrank (ZMod 2) W) with h0 | hpos
    · rw [h0, pow_zero, hW] at hc
      omega
    · rw [hc]
      exact dvd_pow_self 2 hpos.ne'
  have hmod : Nat.card W ≡ Nat.card (MulAction.fixedPoints S W) [MOD 2] :=
    hS2.card_modEq_card_fixedPoints W
  have hfp : ∀ v : W, v ∈ MulAction.fixedPoints S W ↔ ∀ s ∈ S, ρ s v = v := fun v =>
    ⟨fun h s hs => h ⟨s, hs⟩, fun h s => h s s.2⟩
  have hcardeq : Nat.card (MulAction.fixedPoints S W) = Nat.card {v : W // ∀ s ∈ S, ρ s v = v} :=
    Nat.card_congr (Equiv.subtypeEquivRight hfp)
  rw [hcardeq] at hmod
  have hpos : 1 ≤ Nat.card {v : W // ∀ s ∈ S, ρ s v = v} :=
    Nat.one_le_iff_ne_zero.2 (Nat.card_ne_zero.2 ⟨⟨⟨0, fun s _ => map_zero _⟩⟩, inferInstance⟩)
  have h2 : 2 ≤ Nat.card {v : W // ∀ s ∈ S, ρ s v = v} := by
    have h3 := Nat.ModEq.symm hmod
    unfold Nat.ModEq at h3
    omega
  obtain ⟨⟨w₀, hw₀S⟩, hw₀ne⟩ :
      ∃ x : {v : W // ∀ s ∈ S, ρ s v = v}, x ≠ ⟨0, fun s _ => map_zero _⟩ := by
    by_contra h
    push Not at h
    have : Nat.card {v : W // ∀ s ∈ S, ρ s v = v} ≤ 1 :=
      Finite.card_le_one_iff_subsingleton.2 ⟨fun a b => (h a).trans (h b).symm⟩
    omega
  have hw₀0 : w₀ ≠ 0 := fun h => hw₀ne (Subtype.ext h)
  refine ⟨w₀, hw₀0, fun w hw => ?_, ?_⟩
  · by_cases h0 : w = 0
    · exact Or.inl h0
    · exact Or.inr (huniq w w₀ h0 hw₀0 hw hw₀S)
  · rcases (hstab w₀ hw₀0 hw₀S).1 with h | h
    · exact Or.inl fun g => by rw [← h]; exact Iff.rfl
    · exact Or.inr fun g => by rw [← h]; exact Iff.rfl

end CFSG.LocalAnalysis.RankThreeUC.S15.K58Proof
