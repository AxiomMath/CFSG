module

public import CFSG.GH74.Uniqueness.SU.SU5J2Emb2
public import CFSG.GH74.Uniqueness.SU.SU5J2U

public section

namespace CFSG.GH74.Uniqueness.SU.SU5

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups

namespace J2Syl

theorem order4_iff : ∀ m : J2Syl, (m ∈ R ∧ orderOf m = 4) ↔ (orderOf m = 4 ∧ m * m = z0) := by
  intro m
  rw [orderOf_eq_four_iff]
  have h1 : ∀ m : J2Syl, m ∈ R → m * m ≠ 1 → (m * m) * (m * m) = 1 → m * m = z0 :=
    sq_eq_z_of_mem_R
  constructor
  · rintro ⟨hR, h2, h3⟩
    exact ⟨⟨h2, h3⟩, h1 m hR h2 h3⟩
  · rintro ⟨⟨h2, h3⟩, h4⟩
    exact ⟨mem_R_of_sq_eq_z m h4, h2, h3⟩

end J2Syl

section Emb3

variable {G : Type*} [Group G]

namespace J2Emb

variable {S T : Subgroup G} {x : G}

theorem le4_centralizer (h : J2Emb S T x) : ∀ s ∈ S, s ∉ T → s ^ 2 = 1 →
    ∀ E : Subgroup G, E ≤ S ⊓ centralizer {s} → Open.IsElemAbelian 2 E → Nat.card E ≤ 4 := by
  obtain ⟨f, hf, rfl, rfl, rfl⟩ := h
  rintro _ ⟨m, rfl⟩ hmT hm2 E hE hEE
  have h1 : m.right ≠ 1 := fun h0 => hmT (Subgroup.mem_map_of_mem f h0)
  have h2 : m * m = 1 := hf (by rw [map_mul, map_one, ← pow_two]; exact hm2)
  obtain ⟨X, rfl⟩ := exists_eq_map_of_le_range (hE.trans inf_le_left)
  rw [Subgroup.card_map_of_injective hf]
  refine J2Syl.le4_centralizer m h1 h2 X (fun t ht => ?_) ((isElemAbelian_map_iff hf).1 hEE)
  have h3 := Subgroup.mem_centralizer_iff.1 (hE (Subgroup.mem_map_of_mem f ht)).2 (f m) rfl
  exact hf (by rw [map_mul, map_mul]; exact h3.symm)

theorem facts_R (h : J2Emb S T x) {z : G} (hz : IsZGen S z) :
    ∃ R V : Subgroup G, R ≤ S ∧ V ≤ S ∧ (∀ s ∈ S, ∀ r ∈ R, s * r * s⁻¹ ∈ R) ∧ IsQ8D8 R ∧
      (∀ N : Subgroup G, N ≤ S → (∀ s ∈ S, ∀ n ∈ N, s * n * s⁻¹ ∈ N) → IsQ8D8 N → N = R) ∧
      R ⊔ V = S ∧ R ⊓ V = ⊥ ∧ IsE 2 V ∧ Nat.card R = 32 ∧ z ∈ R ∧
      (∀ s ∈ S, (s ∈ R ∧ s ≠ 1 ∧ s ^ 2 = 1) ↔
        ((s ∈ Zc T ∧ s ≠ 1) ∨ (s ∉ T ∧ s ^ 2 = 1))) ∧
      (∀ E : Subgroup G, E ≤ S → IsE 4 E → E ⊓ R = Zc T) ∧
      (∀ s ∈ S, s ^ 2 = z → s ∈ R) ∧
      (∀ s ∈ S, ((s ∈ R ∧ orderOf s = 4) ↔ (orderOf s = 4 ∧ s ^ 2 = z))) := by
  obtain ⟨f, hf, rfl, rfl, rfl⟩ := h
  obtain rfl := hz.unique (isZGen_f hf)
  have hsq : ∀ m : J2Syl, (f m) ^ 2 = 1 ↔ m * m = 1 := fun m => by
    rw [pow_two, ← map_mul, ← map_one f, hf.eq_iff]
  refine ⟨J2Syl.R.map f, J2Syl.V.map f, Subgroup.map_le_range f _, Subgroup.map_le_range f _,
    ?_, (isQ8D8_map_iff hf).2 J2Syl.isQ8D8_R, ?_, ?_, ?_, (isE_map hf).2 J2Syl.isE_V, ?_,
    Subgroup.mem_map_of_mem f J2Syl.z0_mem_R, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨m, rfl⟩ _ ⟨r, hr, rfl⟩
    exact ⟨m * r * m⁻¹, J2Syl.R_normal m r hr, by simp⟩
  · intro N hNS hNn hNQ
    obtain ⟨N₀, rfl⟩ := exists_eq_map_of_le_range hNS
    have hN₀ : N₀.Normal := ⟨fun n hn g => by
      have h1 := hNn (f g) ⟨g, rfl⟩ (f n) (Subgroup.mem_map_of_mem f hn)
      rw [← map_mul, ← map_inv, ← map_mul, Subgroup.mem_map_iff_mem hf] at h1
      exact h1⟩
    exact congrArg (Subgroup.map f) (J2Syl.unique_R N₀ hN₀ ((isQ8D8_map_iff hf).1 hNQ))
  · rw [← Subgroup.map_sup, J2Syl.R_sup_V, ← MonoidHom.range_eq_map]
  · rw [← Subgroup.map_inf_eq _ _ f hf, J2Syl.R_inf_V, Subgroup.map_bot]
  · rw [Subgroup.card_map_of_injective hf, J2Syl.card_R]
  · rintro _ ⟨m, rfl⟩
    have hR : f m ∈ J2Syl.R.map f ↔ m ∈ J2Syl.R := Subgroup.mem_map_iff_mem hf
    have hW : f m ∈ J2Syl.W.map f ↔ m ∈ J2Syl.W := Subgroup.mem_map_iff_mem hf
    have hZ : f m ∈ Zc (J2Syl.W.map f) ↔ m ∈ J2Syl.U := by
      rw [Zc_map hf, J2Syl.Zc_W]; exact Subgroup.mem_map_iff_mem hf
    have h1 : f m ≠ 1 ↔ m ≠ 1 := by
      rw [← map_one f]; exact not_congr hf.eq_iff
    rw [hR, hW, hZ, h1, hsq]
    exact J2Syl.invol_R m
  · intro E hE hEE
    obtain ⟨X, rfl⟩ := exists_eq_map_of_le_range hE
    rw [Zc_map hf, J2Syl.Zc_W]
    rcases J2Syl.isE4_unique X ((isE_map hf).1 hEE) with rfl | rfl
    · rw [← Subgroup.map_inf_eq _ _ f hf, J2Syl.A_inf_R]
    · rw [← Subgroup.map_inf_eq _ _ f hf, J2Syl.B_inf_R]
  · rintro _ ⟨m, rfl⟩ hm
    have h1 : m * m = J2Syl.z0 := hf (by rw [map_mul, ← pow_two]; exact hm)
    exact Subgroup.mem_map_of_mem f (J2Syl.mem_R_of_sq_eq_z m h1)
  · rintro _ ⟨m, rfl⟩
    rw [orderOf_injective f hf m, Subgroup.mem_map_iff_mem hf]
    have h1 : (f m) ^ 2 = f J2Syl.z0 ↔ m * m = J2Syl.z0 := by
      rw [pow_two, ← map_mul, hf.eq_iff]
    rw [h1]
    exact J2Syl.order4_iff m

end J2Emb

end Emb3

end CFSG.GH74.Uniqueness.SU.SU5
