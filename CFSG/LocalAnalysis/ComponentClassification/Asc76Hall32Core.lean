module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76Hall32Dihedral
public import CFSG.LocalAnalysis.ComponentClassification.Asc76Hall32Main
public import CFSG.Goldschmidt75.CorollaryB3

public section

namespace CFSG.ComponentClassification.Asc76X

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc76

namespace Hall32

theorem exists_mem_ne_ne {G : Type} [Group G] [Finite G] {T : Subgroup G} (hT4 : Nat.card T = 4)
    (a b : G) : ∃ c ∈ T, c ≠ a ∧ c ≠ b := by
  by_contra hcon
  push Not at hcon
  have hsub : (T : Set G) ⊆ {a, b} := by
    intro c hc
    by_cases hca : c = a
    · exact Or.inl hca
    · exact Or.inr (hcon c hc hca)
  have h1 : Nat.card T = (T : Set G).ncard := Nat.card_coe_set_eq _
  have h2 : (T : Set G).ncard ≤ ({a, b} : Set G).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have h3 : ({a, b} : Set G).ncard ≤ 2 :=
    (Set.ncard_insert_le a {b}).trans (by rw [Set.ncard_singleton])
  omega

end Hall32

open Hall32 in
theorem hall32Core :
    Hall32Core := by
  intro G _ _ _ S T hS hTS hT4 hTel hwc hns htop _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 S := IsPGroup.of_card (isSylowOf_iff_card.mp hS).2
  have hTab : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := fun a ha b hb => by
    have h1 : (⟨a, ha⟩ : ↥T) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := hTel.1.is_comm.comm _ _
    simpa using congrArg Subtype.val h1
  have hSN := le_normalizer_of_weaklyClosed hTS hwc
  have hT1 : T ≠ ⊥ := fun e => by
    rw [e] at hT4
    simp at hT4
  obtain ⟨⟨z, hz⟩, hz1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (inf_center_ne_bot' hS2 hTS hSN hT1)
  have hzT : z ∈ T := (mem_inf.mp hz).1
  have hzc : ∀ s ∈ S, s * z = z * s :=
    fun s hs => mem_centralizer_iff.mp (mem_inf.mp (mem_inf.mp hz).2).2 s hs
  have hz1' : z ≠ 1 := fun e => hz1 (Subtype.ext e)
  have hset : Setup S T z := ⟨hS, hTS, hT4, hTel.2, hTab, hwc, hzT, hz1', hzc⟩
  obtain ⟨t, htT, ht1, htz⟩ := exists_mem_ne_ne hT4 1 z
  obtain ⟨n₀, hn₀⟩ := exists_conj_sdiff_centralizer hS hTS hT4 hTel hwc hns hzT hz1' hzc
  obtain ⟨n, ⟨hvS, hvC⟩, hmax⟩ := Set.exists_max_image
    {m : G | m⁻¹ * z * m ∈ S ∧ m⁻¹ * z * m ∉ centralizer (T : Set G)}
    (fun m => Nat.card (S ⊓ centralizer ({m⁻¹ * z * m} : Set G) : Subgroup G))
    (Set.toFinite _) ⟨n₀, hn₀⟩
  obtain ⟨P₁, hs⟩ := hset.exists_split htT ht1 htz hvS hvC fun m h1 h2 => hmax m ⟨h1, h2⟩
  generalize n⁻¹ * z * n = v at hs
  set D := dihedral T v (hSN hs.v_mem) hs.v_mul_v with hDdef
  have hDS : D ≤ S := by
    intro x hx
    rcases mem_dihedral.mp hx with hx | hx
    · exact hTS hx
    · have e : x = x * v * v := by rw [mul_assoc, hs.v_mul_v, mul_one]
      rw [e]
      exact mul_mem (hTS hx) hs.v_mem
  have hTD : (T : Set G) ⊆ D := fun x hx => mem_dihedral.mpr (Or.inl hx)
  obtain ⟨S', hS'⟩ := exists_sylow_eq_of_isSylowOf_top hS
  have hsc : fusionStronglyClosed (D : Set G) S' := by
    intro a ha g hg
    rw [hS'] at hg
    exact mem_dihedral.mpr (hs.conj_mem_dihedral hset (mem_dihedral.mp ha) hg)
  have hN : ∀ m ∈ normalizer (D : Set G), ∃ k : ℕ, m ^ (2 ^ k) ∈ centralizer (D : Set G) := by
    intro m hm
    refine ⟨1, ?_⟩
    rw [pow_one, pow_two]
    refine mem_centralizer_iff.mpr fun y hy => ?_
    have hm' : ∀ y : G, (y ∈ T ∨ y * v ∈ T) ↔ (m * y * m⁻¹ ∈ T ∨ m * y * m⁻¹ * v ∈ T) :=
      fun y => mem_normalizer_iff.mp hm y
    exact hs.sq_comm_of_normalizes hset hm' y (mem_dihedral.mp hy)
  have hB3 := CFSG.Goldschmidt75.corollaryB3 S' (by rw [hS']; exact hDS) hsc hN
  have hnc : normalClosure (D : Set G) = ⊤ :=
    le_antisymm le_top (htop ▸ normalClosure_mono hTD)
  have hSD : S = D := hB3.2.2 S (by rw [hnc]; exact le_top) hS2 hDS
  ext x
  constructor
  · rintro hx
    obtain ⟨hxS, hxC⟩ := mem_inf.mp hx
    rw [hSD] at hxS
    rcases mem_dihedral.mp hxS with hxT | hxv
    · exact hxT
    · refine absurd ?_ hs.v_not_mem
      have e : v = x⁻¹ * (x * v) := by group
      rw [e]
      exact mul_mem (inv_mem hxC)
        (mem_centralizer_iff.mpr fun y hy => hTab y hy _ hxv)
  · intro hx
    exact mem_inf.mpr ⟨hTS hx, mem_centralizer_iff.mpr fun y hy => hTab y hy x hx⟩

theorem hallFusionThm32 :
    HallFusionThm32 :=
  hallFusionThm32_of_core hall32Core

end CFSG.ComponentClassification.Asc76X
