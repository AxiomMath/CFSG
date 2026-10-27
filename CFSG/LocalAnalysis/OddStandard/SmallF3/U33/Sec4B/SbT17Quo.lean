module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Dih
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Basic

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G]

private lemma mk'_eq_mk'_of_inv_mul_mem {ℰ E₀ : Subgroup G} [(E₀.subgroupOf ℰ).Normal]
    {x d : G} (hx : x ∈ ℰ) (hd : d ∈ ℰ) (h : x⁻¹ * d ∈ E₀) :
    QuotientGroup.mk' (E₀.subgroupOf ℰ) ⟨x, hx⟩ =
      QuotientGroup.mk' (E₀.subgroupOf ℰ) ⟨d, hd⟩ := by
  change ((⟨x, hx⟩ : ↥ℰ) : ↥ℰ ⧸ (E₀.subgroupOf ℰ)) =
    ((⟨d, hd⟩ : ↥ℰ) : ↥ℰ ⧸ (E₀.subgroupOf ℰ))
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simpa using h

theorem exists_index_two_of_fusion {ℰ E₀ : Subgroup G} (hℰ : IsPGroup 2 ℰ)
    (hN : NormalIn E₀ ℰ) {t l : G} (ht : t ∈ ℰ) (hl : l ∈ ℰ) (ht2 : t * t = 1)
    (hl2 : l * l = 1) (hexp : ∀ x ∈ ℰ, x ^ 4 ∈ E₀) (ht1 : t ∉ E₀) (hl1 : l ∉ E₀)
    (htl : t * l ∉ E₀) (hcomm : t * l * t⁻¹ * l⁻¹ ∈ E₀)
    (hC : ∀ x ∈ ℰ, x * t * x⁻¹ * t⁻¹ ∈ E₀ →
      x ∈ E₀ ∨ t⁻¹ * x ∈ E₀ ∨ l⁻¹ * x ∈ E₀ ∨ (t * l)⁻¹ * x ∈ E₀)
    (hnc : ∀ x ∈ ℰ, ∀ e ∈ E₀, x * t * x⁻¹ ≠ l * e) :
    ∃ M₁ : Subgroup G, M₁ ≤ ℰ ∧ M₁.relIndex ℰ = 2 ∧ t ∉ M₁ ∧
      ∀ u ∈ M₁, u * u = 1 → u ∈ E₀ ∨ ∃ e ∈ E₀, u = l * e := by
  letI hN₀ : (E₀.subgroupOf ℰ).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using hN.2 g.1 g.2 n.1 hn⟩
  have hB : IsPGroup 2 (↥ℰ ⧸ (E₀.subgroupOf ℰ)) := hℰ.to_quotient (E₀.subgroupOf ℰ)
  have hexpB : ∀ x : ↥ℰ ⧸ (E₀.subgroupOf ℰ), x ^ 4 = 1 := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (E₀.subgroupOf ℰ) x
    rw [← map_pow]
    refine (QuotientGroup.eq_one_iff (N := E₀.subgroupOf ℰ) (y ^ 4)).mpr ?_
    exact Subgroup.mem_subgroupOf.mpr (by simpa using hexp y.1 y.2)
  have haq : (QuotientGroup.mk' (E₀.subgroupOf ℰ) ⟨t, ht⟩) ^ 2 = 1 := by
    rw [pow_two, ← map_mul,
      show (⟨t, ht⟩ * ⟨t, ht⟩ : ↥ℰ) = 1 from Subtype.ext (by simpa using ht2), map_one]
  have hlq : (QuotientGroup.mk' (E₀.subgroupOf ℰ) ⟨l, hl⟩) ^ 2 = 1 := by
    rw [pow_two, ← map_mul,
      show (⟨l, hl⟩ * ⟨l, hl⟩ : ↥ℰ) = 1 from Subtype.ext (by simpa using hl2), map_one]
  have ha1 : QuotientGroup.mk' (E₀.subgroupOf ℰ) ⟨t, ht⟩ ≠ 1 := by
    intro h
    apply ht1
    exact Subgroup.mem_subgroupOf.mp
      ((QuotientGroup.eq_one_iff (N := E₀.subgroupOf ℰ) ⟨t, ht⟩).mp (by simpa using h))
  have hl1q : QuotientGroup.mk' (E₀.subgroupOf ℰ) ⟨l, hl⟩ ≠ 1 := by
    intro h
    apply hl1
    exact Subgroup.mem_subgroupOf.mp
      ((QuotientGroup.eq_one_iff (N := E₀.subgroupOf ℰ) ⟨l, hl⟩).mp (by simpa using h))
  have hal : QuotientGroup.mk' (E₀.subgroupOf ℰ) ⟨t, ht⟩ ≠
      QuotientGroup.mk' (E₀.subgroupOf ℰ) ⟨l, hl⟩ := by
    intro h
    apply htl
    have h1 : QuotientGroup.mk' (E₀.subgroupOf ℰ) (⟨t, ht⟩ * ⟨l, hl⟩) = 1 := by
      rw [map_mul, h]
      simpa [pow_two] using hlq
    have h2 : (⟨t, ht⟩ * ⟨l, hl⟩ : ↥ℰ) ∈ E₀.subgroupOf ℰ :=
      (QuotientGroup.eq_one_iff (N := E₀.subgroupOf ℰ) (⟨t, ht⟩ * ⟨l, hl⟩)).mp
        (by simpa using h1)
    have h3 := Subgroup.mem_subgroupOf.mp h2
    simpa using h3
  have hcommB : QuotientGroup.mk' (E₀.subgroupOf ℰ) ⟨t, ht⟩ *
      QuotientGroup.mk' (E₀.subgroupOf ℰ) ⟨l, hl⟩ =
      QuotientGroup.mk' (E₀.subgroupOf ℰ) ⟨l, hl⟩ *
        QuotientGroup.mk' (E₀.subgroupOf ℰ) ⟨t, ht⟩ := by
    have h1 : QuotientGroup.mk' (E₀.subgroupOf ℰ)
        (⟨t, ht⟩ * ⟨l, hl⟩ * ⟨t, ht⟩⁻¹ * ⟨l, hl⟩⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff (N := E₀.subgroupOf ℰ) _).mpr
        (Subgroup.mem_subgroupOf.mpr (by simpa using hcomm))
    have h2 : QuotientGroup.mk' (E₀.subgroupOf ℰ) ⟨t, ht⟩ *
        QuotientGroup.mk' (E₀.subgroupOf ℰ) ⟨l, hl⟩ *
        (QuotientGroup.mk' (E₀.subgroupOf ℰ) ⟨t, ht⟩)⁻¹ *
        (QuotientGroup.mk' (E₀.subgroupOf ℰ) ⟨l, hl⟩)⁻¹ = 1 := by
      simpa only [map_mul, map_inv] using h1
    have h3 : (QuotientGroup.mk' (E₀.subgroupOf ℰ) ⟨t, ht⟩ *
        QuotientGroup.mk' (E₀.subgroupOf ℰ) ⟨l, hl⟩) /
        (QuotientGroup.mk' (E₀.subgroupOf ℰ) ⟨l, hl⟩ *
          QuotientGroup.mk' (E₀.subgroupOf ℰ) ⟨t, ht⟩) = 1 := by
      simpa only [div_eq_mul_inv, mul_inv_rev, mul_assoc] using h2
    exact div_eq_one.mp h3
  have hCB : ∀ x : ↥ℰ ⧸ (E₀.subgroupOf ℰ),
      x * QuotientGroup.mk' (E₀.subgroupOf ℰ) ⟨t, ht⟩ =
        QuotientGroup.mk' (E₀.subgroupOf ℰ) ⟨t, ht⟩ * x →
      x = 1 ∨ x = QuotientGroup.mk' (E₀.subgroupOf ℰ) ⟨t, ht⟩ ∨
        x = QuotientGroup.mk' (E₀.subgroupOf ℰ) ⟨l, hl⟩ ∨
        x = QuotientGroup.mk' (E₀.subgroupOf ℰ) ⟨t, ht⟩ *
          QuotientGroup.mk' (E₀.subgroupOf ℰ) ⟨l, hl⟩ := by
    intro x hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (E₀.subgroupOf ℰ) x
    have hmem : y.1 * t * y.1⁻¹ * t⁻¹ ∈ E₀ := by
      have htmp : QuotientGroup.mk' (E₀.subgroupOf ℰ)
          (y * ⟨t, ht⟩ * y⁻¹ * ⟨t, ht⟩⁻¹) =
          QuotientGroup.mk' (E₀.subgroupOf ℰ) y *
            QuotientGroup.mk' (E₀.subgroupOf ℰ) ⟨t, ht⟩ *
            (QuotientGroup.mk' (E₀.subgroupOf ℰ) y)⁻¹ *
            (QuotientGroup.mk' (E₀.subgroupOf ℰ) ⟨t, ht⟩)⁻¹ := by
        simp only [map_mul, map_inv]
      have hzero : QuotientGroup.mk' (E₀.subgroupOf ℰ)
          (y * ⟨t, ht⟩ * y⁻¹ * ⟨t, ht⟩⁻¹) = 1 := by
        rw [htmp, hx]
        group
      have hker : y * ⟨t, ht⟩ * y⁻¹ * ⟨t, ht⟩⁻¹ ∈ E₀.subgroupOf ℰ :=
        (QuotientGroup.eq_one_iff (N := E₀.subgroupOf ℰ) _).mp hzero
      simpa using Subgroup.mem_subgroupOf.mp hker
    rcases hC y.1 y.2 hmem with h | h | h | h
    · left
      exact (QuotientGroup.eq_one_iff (N := E₀.subgroupOf ℰ) y).mpr
        (Subgroup.mem_subgroupOf.mpr h)
    · right; left
      exact mk'_eq_mk'_of_inv_mul_mem y.2 ht (by simpa using E₀.inv_mem h)
    · right; right; left
      exact mk'_eq_mk'_of_inv_mul_mem y.2 hl (by simpa using E₀.inv_mem h)
    · right; right; right
      rw [← map_mul]
      exact mk'_eq_mk'_of_inv_mul_mem y.2 (ℰ.mul_mem ht hl) (by simpa using E₀.inv_mem h)
  have hncB : ∀ x : ↥ℰ ⧸ (E₀.subgroupOf ℰ),
      x * QuotientGroup.mk' (E₀.subgroupOf ℰ) ⟨t, ht⟩ * x⁻¹ ≠
        QuotientGroup.mk' (E₀.subgroupOf ℰ) ⟨l, hl⟩ := by
    intro x hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (E₀.subgroupOf ℰ) x
    have heq : QuotientGroup.mk' (E₀.subgroupOf ℰ) (y * ⟨t, ht⟩ * y⁻¹) =
        QuotientGroup.mk' (E₀.subgroupOf ℰ) ⟨l, hl⟩ := by
      simpa only [map_mul, map_inv] using hx
    have hmem : (y * ⟨t, ht⟩ * y⁻¹)⁻¹ * ⟨l, hl⟩ ∈ E₀.subgroupOf ℰ :=
      QuotientGroup.eq.mp heq
    have he : (y.1 * t * y.1⁻¹)⁻¹ * l ∈ E₀ := by
      simpa using (Subgroup.mem_subgroupOf.mp hmem)
    exact absurd (by group : y.1 * t * y.1⁻¹ = l * ((y.1 * t * y.1⁻¹)⁻¹ * l)⁻¹)
      (hnc y.1 y.2 ((y.1 * t * y.1⁻¹)⁻¹ * l)⁻¹ (E₀.inv_mem he))
  obtain ⟨N, hNindex, haN, hNinv⟩ :=
    exists_index_two_of_four_centralizer (B := ↥ℰ ⧸ (E₀.subgroupOf ℰ))
      hB hexpB haq hlq ha1 hl1q hal hcommB hCB hncB
  let M₁ : Subgroup G := (N.comap (QuotientGroup.mk' (E₀.subgroupOf ℰ))).map ℰ.subtype
  have hM₁le : M₁ ≤ ℰ := Subgroup.map_subtype_le _
  have hsub : M₁.subgroupOf ℰ = N.comap (QuotientGroup.mk' (E₀.subgroupOf ℰ)) := by
    ext z
    constructor
    · intro hz
      rw [Subgroup.mem_subgroupOf] at hz
      change (z : G) ∈ (N.comap (QuotientGroup.mk' (E₀.subgroupOf ℰ))).map ℰ.subtype at hz
      rw [Subgroup.mem_map] at hz
      obtain ⟨w, hw, hwz⟩ := hz
      rw [Subgroup.mem_comap] at hw
      rw [Subgroup.mem_comap]
      have hwz' : w = z := Subtype.ext hwz
      simpa [hwz'] using hw
    · intro hz
      rw [Subgroup.mem_subgroupOf]
      change (z : G) ∈ (N.comap (QuotientGroup.mk' (E₀.subgroupOf ℰ))).map ℰ.subtype
      rw [Subgroup.mem_map]
      exact ⟨z, hz, rfl⟩
  refine ⟨M₁, hM₁le, ?_, ?_, ?_⟩
  · change (M₁.subgroupOf ℰ).index = 2
    rw [hsub]
    rw [Subgroup.index_comap_of_surjective N
      (QuotientGroup.mk'_surjective (E₀.subgroupOf ℰ))]
    exact hNindex
  · intro htM
    change t ∈ (N.comap (QuotientGroup.mk' (E₀.subgroupOf ℰ))).map ℰ.subtype at htM
    rw [Subgroup.mem_map] at htM
    obtain ⟨w, hw, hw_eq⟩ := htM
    rw [Subgroup.mem_comap] at hw
    apply haN
    have hw' : w = ⟨t, ht⟩ := Subtype.ext hw_eq
    simpa [hw'] using hw
  · intro u hu hu2
    change u ∈ (N.comap (QuotientGroup.mk' (E₀.subgroupOf ℰ))).map ℰ.subtype at hu
    rw [Subgroup.mem_map] at hu
    obtain ⟨w, hw, hwu⟩ := hu
    rw [Subgroup.mem_comap] at hw
    have hwu' : (w : G) = u := hwu
    have hw2 : w ^ 2 = 1 := by
      apply Subtype.ext
      change (w : G) ^ 2 = 1
      rw [hwu']
      simpa [pow_two] using hu2
    have hw2q : (QuotientGroup.mk' (E₀.subgroupOf ℰ) w) ^ 2 = 1 := by
      rw [← map_pow, hw2, map_one]
    rcases hNinv (QuotientGroup.mk' (E₀.subgroupOf ℰ) w) hw hw2q with hw1 | hwl
    · left
      have hw1' : w ∈ E₀.subgroupOf ℰ :=
        (QuotientGroup.eq_one_iff (N := E₀.subgroupOf ℰ) w).mp hw1
      have hw1'' : (w : G) ∈ E₀ := Subgroup.mem_subgroupOf.mp hw1'
      rwa [← hwu']
    · right
      have hw_eq : (w : ↥ℰ ⧸ (E₀.subgroupOf ℰ)) =
          ((⟨l, hl⟩ : ↥ℰ) : ↥ℰ ⧸ (E₀.subgroupOf ℰ)) := hwl
      have hmem : w⁻¹ * ⟨l, hl⟩ ∈ E₀.subgroupOf ℰ := QuotientGroup.eq.mp hw_eq
      have hmem' : w.1⁻¹ * l ∈ E₀ := by
        have := Subgroup.mem_subgroupOf.mp hmem
        simpa using this
      refine ⟨(w.1⁻¹ * l)⁻¹, E₀.inv_mem hmem', ?_⟩
      rw [← hwu']
      group

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
