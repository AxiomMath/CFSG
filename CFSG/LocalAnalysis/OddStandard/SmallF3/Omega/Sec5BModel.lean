module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BWeights
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Statements2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

structure Sec5Model58 (t : G) (L : Subgroup G) (z r : G) (A : Subgroup G)
    (φ : (Fin 6 → ZMod 2) → G) : Prop where
  perm : IsPerm6 φ A (L ⊓ normalizer (A : Set G))
  map_one : φ (fun _ => 1) = t
  r_mem : ∃ i : Fin 6, φ (Pi.single i 1) = r
  z_mem : ∃ v, vecWeight v = 4 ∧ φ v = z
  mem_L : ∀ v, φ v ∈ L ↔ IsEvenVec v
  type_one : ∀ v, vecWeight v = 1 ∨ vecWeight v = 5 →
    ∃ α : ℤˣ, InducesTypeSome L (φ v) 6 (-1) 1 α
  type_three : ∀ v, vecWeight v = 3 → ∃ α : ℤˣ, InducesTypeSome L (φ v) 6 (-1) 3 α

theorem sec5b_model58_of (h : Asc82Lemma58d) [Finite G] {t : G} {L S : Subgroup G} {z r : G}
    {B A : Subgroup G} (hR : Sec5RCtx G t L S z r B A) :
    ∃ φ : (Fin 6 → ZMod 2) → G, Sec5Model58 t L z r A φ := by
  obtain ⟨φ, hperm, h1, hi, hv, hL, hodd, hthree⟩ := h G t L S z r B A hR
  exact ⟨φ, hperm, h1, hi, hv, hL, hodd, hthree⟩

variable {t : G} {L : Subgroup G} {z r : G} {A : Subgroup G} {φ : (Fin 6 → ZMod 2) → G}

theorem Sec5Model58.t_mem_wclass (hm : Sec5Model58 t L z r A φ) : t ∈ wclass φ 6 := by
  refine ⟨(1 : Fin 6 → ZMod 2), sec5b6_vecWeight_one, ?_⟩
  simpa only [Pi.one_def] using hm.map_one

theorem Sec5Model58.r_mem_wclass (hm : Sec5Model58 t L z r A φ) : r ∈ wclass φ 1 := by
  obtain ⟨i, hi⟩ := hm.r_mem
  exact ⟨Pi.single i 1, sec5b6_vecWeight_single i, hi⟩

theorem Sec5Model58.z_mem_wclass (hm : Sec5Model58 t L z r A φ) : z ∈ wclass φ 4 := by
  obtain ⟨v, hv, hvz⟩ := hm.z_mem
  exact ⟨v, hv, hvz⟩

theorem Sec5Model58.tz_mem_wclass (hm : Sec5Model58 t L z r A φ) : t * z ∈ wclass φ 2 := by
  have hz : z ∈ wclass φ 4 := hm.z_mem_wclass
  have h := hm.perm.mul_mem_wclass (k := 4) (by norm_num) hz
  have ht : φ (1 : Fin 6 → ZMod 2) = t := by
    rw [Pi.one_def]
    exact hm.map_one
  rw [ht] at h
  have h2 : 6 - 4 = 2 := by norm_num
  rwa [h2] at h

theorem Sec5Model58.mem_L_iff (hm : Sec5Model58 t L z r A φ) {k : ℕ} {x : G}
    (hx : x ∈ wclass φ k) : x ∈ L ↔ Even k := by
  obtain ⟨v, hv, rfl⟩ := hx
  rw [hm.mem_L v, sec5b6_isEvenVec_iff, hv]

theorem Sec5Model58.mem_A (hm : Sec5Model58 t L z r A φ) : t ∈ A ∧ r ∈ A ∧ z ∈ A := by
  refine ⟨?_, ?_, ?_⟩
  · have ht := hm.perm.mem (fun _ => 1)
    rwa [hm.map_one] at ht
  · obtain ⟨i, hi⟩ := hm.r_mem
    rw [← hi]
    exact hm.perm.mem (Pi.single i 1)
  · obtain ⟨v, _, hv⟩ := hm.z_mem
    rw [← hv]
    exact hm.perm.mem v

theorem Sec5Model58.r_not_mem_L (hm : Sec5Model58 t L z r A φ) : r ∉ L := by
  intro hr
  exact absurd ((hm.mem_L_iff hm.r_mem_wclass).mp hr) (by norm_num : ¬ Even 1)

theorem Sec5Model58.not_subset_L (hm : Sec5Model58 t L z r A φ)
    (hirr : ∀ B' : Subgroup G, B' ≤ A → (∀ m ∈ normalizer (A : Set G), ∀ b ∈ B', m * b * m⁻¹ ∈ B') →
      B' = ⊥ ∨ B' = A)
    {T : Set G} (hTA : T ⊆ (A : Set G))
    (hinv : ∀ m ∈ normalizer (A : Set G), ∀ x ∈ T, m * x * m⁻¹ ∈ T) (hne : ∃ x ∈ T, x ≠ 1) :
    ¬ T ⊆ (L : Set G) := by
  intro hTL
  set B' : Subgroup G := Subgroup.closure T with hB'def
  have hB'A : B' ≤ A := by
    rw [hB'def]
    exact (Subgroup.closure_le A).mpr hTA
  have hB'inv : ∀ m ∈ normalizer (A : Set G), ∀ b ∈ B', m * b * m⁻¹ ∈ B' := by
    intro m hmN b hb
    have hmap : Subgroup.map (MulAut.conj m).toMonoidHom B' ≤ B' := by
      rw [hB'def, MonoidHom.map_closure]
      apply Subgroup.closure_mono
      rintro y ⟨x, hx, rfl⟩
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hinv m hmN x hx
    exact hmap ⟨b, hb, rfl⟩
  rcases hirr B' hB'A hB'inv with hbot | htop
  · obtain ⟨x, hxT, hx1⟩ := hne
    have hx : x ∈ B' := by
      rw [hB'def]
      exact Subgroup.subset_closure hxT
    rw [hbot] at hx
    exact hx1 (Subgroup.mem_bot.mp hx)
  · have hB'L : B' ≤ L := by
      rw [hB'def]
      exact (Subgroup.closure_le L).mpr hTL
    have hrB' : r ∈ B' := by
      rw [htop]
      exact hm.mem_A.2.1
    exact hm.r_not_mem_L (hB'L hrB')

end CFSG.OddStandard.SmallF3.Omega
