module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.FamilyL3

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

open CFSG.Open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.L3Leaves

theorem overgroupL32Core_of_A0 {G : Type} [Group G] [Finite G] {A₀ : Subgroup G}
    (hA₀ : Nat.card A₀ = 3)
    (h : ∀ W Y : Subgroup G, Subgroup.normalizer (A₀ : Set G) ≤ W → Y ≤ W → A₀ ≤ Y →
      IsLThreeTwo (↥Y ⧸ CFSG.pCore 2 ↥Y) → W = ⊤ ∨ ¬ 2 ∣ W.index) :
    OvergroupL32Core G := by
  intro hcyc A W Y hA hNW hYW hAY hY
  obtain ⟨g, hg⟩ := exists_conj_eq_of_card_eq_three hcyc hA hA₀
  set cg := (MulAut.conj g).toMonoidHom
  have hNW' : Subgroup.normalizer (A₀ : Set G) ≤ W.map cg := by
    rw [hg, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hNW
  have hAY' : A₀ ≤ Y.map cg := hg ▸ Subgroup.map_mono hAY
  have hidx : (W.map cg).index = W.index := Subgroup.index_map_equiv W (MulAut.conj g)
  rcases h (W.map cg) (Y.map cg) hNW' (Subgroup.map_mono hYW) hAY'
      (isLThreeTwo_map_equiv (MulAut.conj g) Y hY) with htop | hodd
  · left
    rw [← Subgroup.index_eq_one, ← hidx, htop, Subgroup.index_top]
  · exact Or.inr (hidx ▸ hodd)

@[expose] def twoCoset {G : Type} [Group G] (T : Subgroup G) (s : G) (hs2 : s * s = 1)
    (hn : ∀ x ∈ T, s * x * s⁻¹ ∈ T) : Subgroup G where
  carrier := {x | x ∈ T ∨ ∃ t ∈ T, x = t * s}
  one_mem' := Or.inl T.one_mem
  mul_mem' := by
    have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
    rintro a b (ha | ⟨t, ht, rfl⟩) (hb | ⟨u, hu, rfl⟩)
    · exact Or.inl (T.mul_mem ha hb)
    · exact Or.inr ⟨a * u, T.mul_mem ha hu, by simp [mul_assoc]⟩
    · refine Or.inr ⟨t * (s * b * s⁻¹), T.mul_mem ht (hn b hb), ?_⟩
      simp [mul_assoc]
    · refine Or.inl ?_
      have : t * s * (u * s) = t * (s * u * s⁻¹) := by
        rw [hsi]; simp only [mul_assoc]
      rw [this]
      exact T.mul_mem ht (hn u hu)
  inv_mem' := by
    have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
    rintro a (ha | ⟨t, ht, rfl⟩)
    · exact Or.inl (T.inv_mem ha)
    · refine Or.inr ⟨s * t⁻¹ * s⁻¹, hn _ (T.inv_mem ht), ?_⟩
      simp [mul_assoc, hsi, hs2]

theorem card_twoCoset {G : Type} [Group G] [Finite G] (T : Subgroup G) (s : G)
    (hs2 : s * s = 1) (hn : ∀ x ∈ T, s * x * s⁻¹ ∈ T) (hsT : s ∉ T) :
    Nat.card (twoCoset T s hs2 hn) = 2 * Nat.card T := by
  have hTH : T ≤ twoCoset T s hs2 hn := fun x hx => Or.inl hx
  have hsH : s ∈ twoCoset T s hs2 hn := Or.inr ⟨1, T.one_mem, by simp⟩
  have hidx : (T.subgroupOf (twoCoset T s hs2 hn)).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨s, hsH⟩, fun b => ?_⟩
    obtain ⟨b, hb⟩ := b
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    rcases hb with hb | ⟨t, ht, rfl⟩
    · refine Or.inr ⟨hb, ?_⟩
      intro h
      exact hsT (by simpa using T.mul_mem (T.inv_mem hb) h)
    · refine Or.inl ⟨?_, ?_⟩
      · rw [mul_assoc, hs2, mul_one]; exact ht
      · intro h
        exact hsT (by simpa using T.mul_mem (T.inv_mem ht) h)
  have hcard : Nat.card (T.subgroupOf (twoCoset T s hs2 hn)) = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH).toEquiv
  rw [← Subgroup.card_mul_index (T.subgroupOf (twoCoset T s hs2 hn)), hidx, hcard, mul_comm]

theorem two_mul_card_dvd_of_involution {G : Type} [Group G] [Finite G] {T W : Subgroup G}
    {s : G} (hs2 : s * s = 1) (hsT : s ∉ T) (hn : ∀ x ∈ T, s * x * s⁻¹ ∈ T) (hTW : T ≤ W)
    (hsW : s ∈ W) : 2 * Nat.card T ∣ Nat.card W := by
  rw [← card_twoCoset T s hs2 hn hsT]
  refine Subgroup.card_dvd_of_le ?_
  rintro x (hx | ⟨t, ht, rfl⟩)
  · exact hTW hx
  · exact W.mul_mem (hTW ht) hsW

theorem not_two_dvd_index_of_dvd_card {G : Type} [Group G] [Finite G] {T W : Subgroup G}
    (h : 2 * Nat.card T ∣ Nat.card W) (h4 : ¬ 4 * Nat.card T ∣ Nat.card G) :
    ¬ 2 ∣ W.index := by
  intro h2
  apply h4
  rw [← Subgroup.card_mul_index W]
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := h2
  exact ⟨a * b, by rw [ha, hb]; ring⟩

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
