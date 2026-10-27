module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.NOne

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup

variable {G X : Type} [Group G] [Group X]

theorem map_comap_of_le_range (φ : X →* G) {F : Subgroup G} (hF : F ≤ φ.range) :
    (F.comap φ).map φ = F := Subgroup.map_comap_eq_self hF

theorem mem_map_iff_conj {φ : X →* G} (hφ : Function.Injective φ) {F : Subgroup X} {m : X}
    (hm : ∀ x, x ∈ F ↔ m * x * m⁻¹ ∈ F) :
    ∀ x : G, x ∈ F.map φ ↔ φ m * x * (φ m)⁻¹ ∈ F.map φ := by
  intro x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨m * y * m⁻¹, (hm y).1 hy, by simp⟩
  · intro hx
    by_cases hxr : x ∈ φ.range
    · obtain ⟨y, rfl⟩ := hxr
      refine Subgroup.mem_map_of_mem φ ((hm y).2 ?_)
      rwa [← map_inv, ← map_mul, ← map_mul, Subgroup.mem_map_iff_mem hφ] at hx
    · exfalso
      obtain ⟨z, hz, hzx⟩ := hx
      apply hxr
      have : x = (φ m)⁻¹ * (φ m * x * (φ m)⁻¹) * φ m := by group
      rw [this, ← hzx]
      exact (φ.range).mul_mem ((φ.range).mul_mem ((φ.range).inv_mem ⟨m, rfl⟩) ⟨z, rfl⟩)
        ⟨m, rfl⟩

theorem FusionData.map {φ : X →* G} (hφ : Function.Injective φ) {t m : X} {T1 F1 F2 : Subgroup X}
    (D : FusionData (⊤ : Subgroup X) t T1 F1 F2 m) :
    FusionData φ.range (φ t) (T1.map φ) (F1.map φ) (F2.map φ) (φ m) := by
  have hrange : φ.range = (⊤ : Subgroup X).map φ := MonoidHom.range_eq_map φ
  have hmem : ∀ {S : Subgroup X} {x : X}, φ x ∈ S.map φ ↔ x ∈ S := fun {S x} =>
    Subgroup.mem_map_iff_mem hφ
  refine ⟨Subgroup.map_le_range φ _, D.T1_pgroup.map φ, ?_, Subgroup.mem_map_of_mem φ D.t_mem,
    ?_, ?_, ?_, Subgroup.map_mono D.F1_le, Subgroup.map_mono D.F2_le, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, Subgroup.mem_map_of_mem φ D.t_mem_F1, Subgroup.mem_map_of_mem φ D.t_mem_F2,
    ⟨m, rfl⟩, ?_, ?_, ?_⟩
  · rw [hrange, Subgroup.relIndex_map_map_of_injective _ _ hφ]
    exact D.T1_odd
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, D.t_central x hx]
  · rintro _ ⟨x, hx, rfl⟩ hcomm
    have : ∀ y ∈ T1, x * y = y * x := fun y hy =>
      hφ (by rw [map_mul, map_mul]; exact hcomm _ (Subgroup.mem_map_of_mem φ hy))
    rcases D.T1_center x hx this with rfl | rfl
    · left; simp
    · right; rfl
  · have hset : {a : G | a ∈ T1.map φ ∧ a * a = 1} = φ '' {a : X | a ∈ T1 ∧ a * a = 1} := by
      ext a
      constructor
      · rintro ⟨⟨x, hx, rfl⟩, ha⟩
        exact ⟨x, ⟨hx, hφ (by rw [map_mul, ha, map_one])⟩, rfl⟩
      · rintro ⟨x, ⟨hx, hx2⟩, rfl⟩
        exact ⟨Subgroup.mem_map_of_mem φ hx, by rw [← map_mul, hx2, map_one]⟩
    rw [hset, ← MonoidHom.map_closure, D.T1_gen]
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, D.F1_comm x hx y hy]
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, D.F2_comm x hx y hy]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, D.F1_sq x hx, map_one]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, D.F2_sq x hx, map_one]
  · rw [Subgroup.card_map_of_injective hφ, D.F1_card]
  · rw [Subgroup.card_map_of_injective hφ, D.F2_card]
  · intro h
    exact D.F_ne (Subgroup.map_injective hφ h)
  · intro F hF hc hs hcard
    have hFr : F ≤ φ.range := hF.trans (Subgroup.map_le_range φ _)
    have hF' : F.comap φ ≤ T1 := fun x hx => (hmem (S := T1)).1 (hF hx)
    have hc' : ∀ x ∈ F.comap φ, ∀ y ∈ F.comap φ, x * y = y * x := fun x hx y hy =>
      hφ (by rw [map_mul, map_mul]; exact hc _ hx _ hy)
    have hs' : ∀ x ∈ F.comap φ, x * x = 1 := fun x hx =>
      hφ (by rw [map_mul, map_one]; exact hs _ hx)
    have hcard' : Nat.card (F.comap φ) = 16 := by
      rw [← hcard, ← map_comap_of_le_range φ hFr, Subgroup.card_map_of_injective hφ,
        map_comap_of_le_range φ hFr]
    rcases D.F_only _ hF' hc' hs' hcard' with h | h
    · left
      rw [← map_comap_of_le_range φ hFr, h]
    · right
      rw [← map_comap_of_le_range φ hFr, h]
  · exact mem_map_iff_conj hφ D.m_F1
  · exact mem_map_iff_conj hφ D.m_F2
  · intro h
    apply D.m_t
    apply hφ
    simpa [map_mul, map_inv] using h

theorem NData.map {φ : X →* G} (hφ : Function.Injective φ) {F : Subgroup X}
    (D : NData (⊤ : Subgroup X) F) : NData φ.range (F.map φ) := by
  have hmem : ∀ {S : Subgroup X} {x : X}, φ x ∈ S.map φ ↔ x ∈ S := fun {S x} =>
    Subgroup.mem_map_iff_mem hφ
  refine ⟨Subgroup.map_le_range φ _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, D.F_comm x hx y hy]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, D.F_sq x hx, map_one]
  · rw [Subgroup.card_map_of_injective hφ, D.F_card]
  · rintro _ ⟨x, rfl⟩ hx
    refine Subgroup.mem_map_of_mem φ (D.F_self x trivial fun f hf => hφ ?_)
    rw [map_mul, map_mul]
    exact hx _ (Subgroup.mem_map_of_mem φ hf)
  · have hmap : (Subgroup.normalizer (F : Set X) ⊓ ⊤).map φ =
        Subgroup.normalizer ((F.map φ : Subgroup G) : Set G) ⊓ φ.range := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine Subgroup.mem_inf.2 ⟨Subgroup.mem_normalizer_iff.2 fun g => ?_, ⟨y, rfl⟩⟩
        have hy' := Subgroup.mem_normalizer_iff.1 (Subgroup.mem_inf.1 hy).1
        exact mem_map_iff_conj hφ hy' g
      · rintro ⟨hxn, ⟨y, rfl⟩⟩
        refine ⟨y, Subgroup.mem_inf.2 ⟨Subgroup.mem_normalizer_iff.2 fun g => ?_, trivial⟩, rfl⟩
        have := (Subgroup.mem_normalizer_iff.1 hxn) (φ g)
        rw [← map_mul, ← map_inv, ← map_mul, hmem, hmem] at this
        exact this
    rw [← hmap, Subgroup.card_map_of_injective hφ]
    exact D.N_two
  · rintro _ ⟨x, hx, rfl⟩ hf1 _ ⟨x', hx', rfl⟩ hf'1
    obtain ⟨b, -, hbF, hbf⟩ := D.trans x hx (fun h => hf1 (by rw [h, map_one])) x' hx'
      (fun h => hf'1 (by rw [h, map_one]))
    refine ⟨φ b, ⟨b, rfl⟩, mem_map_iff_conj hφ hbF, ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul, hbf]

end CFSG.EvenSporadicStandard.M23Std
