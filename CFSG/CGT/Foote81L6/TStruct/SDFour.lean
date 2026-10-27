module

public import CFSG.CGT.Foote81L6.TStruct.Transport

public section

namespace CFSG.CGT.Foote81L6.TStruct

open Subgroup CFSG.Semidihedral CFSG.Open

theorem card_le_of_forall_mem_finset' {X : Type*} [Group X] {E : Subgroup X} (F : Finset X)
    (h : ∀ x ∈ E, x ∈ F) : Nat.card E ≤ F.card := by
  have h1 := Nat.card_le_card_of_injective (fun x : E => (⟨x, h x x.2⟩ : F))
    fun a b hab => Subtype.ext (by simpa using hab)
  rwa [Nat.card_eq_finsetCard] at h1

variable {N : ℕ}

theorem comm_element_refl (h3 : 3 ≤ N) (hN : 4 ≤ N) (p : ZMod (modulus N))
    {y : SemidihedralGroup N} (hy : y * element N h3 p 1 = element N h3 p 1 * y) :
    y = element N h3 0 0 ∨ y = element N h3 (half N) 0 ∨ y = element N h3 p 1 ∨
      y = element N h3 (p + half N) 1 := by
  obtain ⟨⟨i, e⟩, rfl⟩ := (coordinateEquiv N h3).symm.surjective y
  change element N h3 i e * element N h3 p 1 = element N h3 p 1 * element N h3 i e at hy
  change element N h3 i e = _ ∨ element N h3 i e = _ ∨ element N h3 i e = _ ∨
    element N h3 i e = _
  rcases exponent_cases e with rfl | rfl
  · rw [element_rotation_mul, element_reflection_mul, element_eq_iff] at hy
    have hfix : twist N * i = i := by linear_combination -hy.1
    rcases (twist_fixed_iff N hN i).1 hfix with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · rw [element_reflection_mul, element_reflection_mul, element_eq_iff] at hy
    have hfix : twist N * (i - p) = i - p := by linear_combination -hy.1
    rcases (twist_fixed_iff N hN (i - p)).1 hfix with h | h
    · refine Or.inr (Or.inr (Or.inl ?_))
      rw [element_eq_iff]
      exact ⟨by linear_combination h, rfl⟩
    · refine Or.inr (Or.inr (Or.inr ?_))
      rw [element_eq_iff]
      exact ⟨by linear_combination h, rfl⟩

theorem card_normalizer_sd_le (hN : 4 ≤ N) {V : Subgroup (SemidihedralGroup N)}
    (hV2 : ∀ x ∈ V, x * x = 1) (hV4 : Nat.card V = 4) :
    Nat.card (normalizer (V : Set (SemidihedralGroup N))) ≤ 8 := by
  classical
  have h3 : 3 ≤ N := by omega
  haveI : Finite (SemidihedralGroup N) := presentation_finite N h3
  set z := element N h3 (half N) 0 with hz
  have hzc : ∀ g : SemidihedralGroup N, g * z = z * g := fun g =>
    (mem_center_iff.1 (by rw [hz, element_mem_center_iff N hN]; exact ⟨rfl, Or.inr rfl⟩) g)
  have hzz : z * z = 1 := by
    rw [hz, element_rotation_mul, ← two_mul, two_mul_half_residue N h3, element_zero_zero]
  have hrot : ∀ i, element N h3 i 0 ∈ V → element N h3 i 0 = 1 ∨ element N h3 i 0 = z := by
    intro i hi
    have h := hV2 _ hi
    rw [element_rotation_mul, ← element_zero_zero N h3, element_eq_iff, ← two_mul] at h
    rcases (two_mul_eq_zero_iff N h3 i).1 h.1 with rfl | rfl
    · exact Or.inl (element_zero_zero N h3)
    · exact Or.inr rfl
  obtain ⟨p, hp⟩ : ∃ p, element N h3 p 1 ∈ V := by
    by_contra hno
    have hsub : ∀ x ∈ V, x ∈ ({1, z} : Finset (SemidihedralGroup N)) := by
      intro x hx
      obtain ⟨⟨i, e⟩, rfl⟩ := (coordinateEquiv N h3).symm.surjective x
      change element N h3 i e ∈ V at hx
      change element N h3 i e ∈ ({1, z} : Finset _)
      rcases exponent_cases e with rfl | rfl
      · rcases hrot i hx with h | h <;> simp [h]
      · exact absurd ⟨i, hx⟩ hno
    have := card_le_of_forall_mem_finset' _ hsub
    rw [hV4] at this
    have h2 : ({1, z} : Finset (SemidihedralGroup N)).card ≤ 2 := Finset.card_le_two
    omega
  set x := element N h3 p 1 with hx
  set x' := element N h3 (p + half N) 1 with hx'
  have hxz : x * z = x' := by
    rw [hx, hz, hx', element_reflection_mul, (twist_fixed_iff N hN _).2 (Or.inr rfl), add_zero]
  have hx_ne1 : x ≠ 1 := by
    rw [hx, ← element_zero_zero N h3, ne_eq, element_eq_iff]
    exact fun h => absurd h.2 (by decide)
  have hx_nez : x ≠ z := by
    rw [hx, hz, ne_eq, element_eq_iff]
    exact fun h => absurd h.2 (by decide)
  have hVx : ∀ v ∈ V, v ≠ 1 → v ≠ z → v = x ∨ v = x' := by
    intro v hv hv1 hvz
    have hc := comm_of_mul_self hV2 hv hp
    rcases comm_element_refl h3 hN p hc with h | h | h | h
    · exact absurd (h.trans (element_zero_zero N h3)) hv1
    · exact absurd h hvz
    · exact Or.inl h
    · exact Or.inr h
  have hconj : ∀ g ∈ normalizer (V : Set (SemidihedralGroup N)),
      g * x * g⁻¹ = x ∨ g * x * g⁻¹ = x' := by
    intro g hg
    have hmem := (mem_normalizer_iff.1 hg x).1 hp
    refine hVx _ hmem (fun h => hx_ne1 ?_) (fun h => hx_nez ?_)
    · calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    · calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = g⁻¹ * (z * g) := by rw [h, mul_assoc]
        _ = z := by rw [← hzc g]; group
  set K := normalizer (V : Set (SemidihedralGroup N))
  set C := centralizer ({x} : Set (SemidihedralGroup N))
  have hdvd : C.relIndex K ∣ 2 := by
    rw [relIndex_dvd_two_iff]
    by_cases hex : ∃ a ∈ K, a * x * a⁻¹ = x'
    · obtain ⟨a, ha, hax⟩ := hex
      refine ⟨a, ha, fun b hb => ?_⟩
      rcases hconj b hb with h | h
      · right
        rw [mem_centralizer_singleton_iff]
        calc b * x = (b * x * b⁻¹) * b := by group
          _ = x * b := by rw [h]
      · left
        rw [mem_centralizer_singleton_iff]
        have hbx' : b * x' * b⁻¹ = x := by
          rw [← hxz]
          calc b * (x * z) * b⁻¹ = (b * x * b⁻¹) * (b * z * b⁻¹) := by group
            _ = x' * z := by rw [h, hzc b, mul_inv_cancel_right]
            _ = x := by rw [← hxz, mul_assoc, hzz, mul_one]
        calc b * a * x = (b * (a * x * a⁻¹) * b⁻¹) * (b * a) := by group
          _ = x * (b * a) := by rw [hax, hbx']
    · refine ⟨1, one_mem _, fun b hb => Or.inr ?_⟩
      rw [mem_centralizer_singleton_iff]
      rcases hconj b hb with h | h
      · calc b * x = (b * x * b⁻¹) * b := by group
          _ = x * b := by rw [h]
      · exact absurd ⟨b, hb, h⟩ hex
  have hC : Nat.card ↥(C ⊓ K) ≤ 4 := by
    have hsub : ∀ y ∈ C ⊓ K, y ∈ ({element N h3 0 0, element N h3 (half N) 0, x, x'} :
        Finset (SemidihedralGroup N)) := by
      intro y hy
      have hyc := mem_centralizer_singleton_iff.1 hy.1
      rcases comm_element_refl h3 hN p hyc with h | h | h | h <;> simp [h, hx, hx']
    exact (card_le_of_forall_mem_finset' _ hsub).trans Finset.card_le_four
  have hrel : C.relIndex K ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have hmul := relIndex_mul_card (H := C) (K := K)
  calc Nat.card K = C.relIndex K * Nat.card ↥(C ⊓ K) := hmul.symm
    _ ≤ 2 * 4 := Nat.mul_le_mul hrel hC

theorem card_inf_normalizer_le_of_semidihedral {G : Type*} [Group G] {P : Subgroup G}
    (hN : 4 ≤ N) (e : P ≃* SemidihedralGroup N) {V : Subgroup G} (hVP : V ≤ P)
    (hV2 : ∀ x ∈ V, x * x = 1) (hV4 : Nat.card V = 4) :
    Nat.card ↥(P ⊓ normalizer (V : Set G)) ≤ 8 := by
  rw [← liftSub_lowerSub e hVP, inf_normalizer_liftSub, card_liftSub]
  exact card_normalizer_sd_le hN (mul_self_lowerSub e hV2) (by rw [card_lowerSub e hVP, hV4])

end CFSG.CGT.Foote81L6.TStruct
