module

public import CFSG.GH74.GLS.SP.Local.SPLOrdL2

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup

namespace S2C

theorem mem_of_mul_self_eq_one_of_mem_normalizer {G : Type*} [Group G] {S : Subgroup G}
    (hS : IsPGroup 2 S) (hmax : ∀ P : Subgroup G, IsPGroup 2 P → S ≤ P → P = S) {g : G}
    (hg2 : g * g = 1) (hgn : g ∈ normalizer S) : g ∈ S := by
  have hzp : IsPGroup 2 (zpowers g) := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hg2)
  have hnorm : zpowers g ≤ normalizer S := by
    rw [zpowers_le]
    exact hgn
  have hsup : IsPGroup 2 (zpowers g ⊔ S : Subgroup G) := hzp.to_sup_of_normal_right' hS hnorm
  have heq : zpowers g ⊔ S = S := hmax _ hsup le_sup_right
  exact (le_sup_left.trans heq.le) (mem_zpowers g)

theorem mem_of_centralizes_of_dihedral {n : ℕ} {G : Type*} [Group G] (φ : G ≃* DihedralGroup n)
    {S : Subgroup G} (hS : IsPGroup 2 S) (hmax : ∀ P : Subgroup G, IsPGroup 2 P → S ≤ P → P = S)
    {g : G} (hg : ∀ a ∈ S, g * a = a * g) : g ∈ S := by
  have hcn : g ∈ normalizer S :=
    Subgroup.centralizer_le_normalizer (S : Set G)
      (Subgroup.mem_centralizer_iff.mpr fun h hh => (hg h hh).symm)
  have hrefl : ∃ t ∈ S, ∃ i : ZMod n, φ t = DihedralGroup.sr i := by
    by_contra hno
    push Not at hno
    obtain ⟨s, hs⟩ : ∃ s : G, φ s = DihedralGroup.sr 0 := ⟨φ.symm _, φ.apply_symm_apply _⟩
    have hs2 : s * s = 1 := by
      apply φ.injective
      rw [map_mul, hs, map_one, DihedralGroup.sr_mul_self]
    have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
    have hconj : ∀ y ∈ S, s * y * s⁻¹ ∈ S := by
      intro y hy
      have hyinv : s * y * s⁻¹ = y⁻¹ := by
        apply φ.injective
        rcases hy' : φ y with k | k
        · rw [map_mul, map_mul, map_inv, map_inv, hs, hy', DihedralGroup.inv_sr,
            DihedralGroup.inv_r, DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr]
          congr 1
          ring
        · exact absurd hy' (hno y hy k)
      rw [hyinv]
      exact S.inv_mem hy
    have hsn : s ∈ normalizer S := by
      rw [mem_normalizer_iff]
      intro x
      refine ⟨hconj x, fun hx => ?_⟩
      have h := hconj _ hx
      have hx' : s * (s * x * s⁻¹) * s⁻¹ = x := by
        rw [hsinv]
        calc s * (s * x * s) * s = (s * s) * x * (s * s) := by group
          _ = x := by rw [hs2]; group
      rwa [hx'] at h
    have hsS : s ∈ S := mem_of_mul_self_eq_one_of_mem_normalizer hS hmax hs2 hsn
    exact hno s hsS 0 hs
  obtain ⟨t, htS, i, hti⟩ := hrefl
  have hgg : g * g = 1 := by
    have hct : g * t = t * g := hg t htS
    apply φ.injective
    rw [map_mul, map_one]
    rcases hg' : φ g with j | j
    · have h1 : φ (g * t) = φ (t * g) := by rw [hct]
      rw [map_mul, map_mul, hg', hti, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r] at h1
      have h2 : i - j = i + j := by
        have := DihedralGroup.sr.inj h1
        exact this
      rw [DihedralGroup.r_mul_r, ← DihedralGroup.r_zero]
      congr 1
      have h3 : j + j = 0 := by
        have h4 : (i + j) - (i - j) = 0 := by rw [h2]; exact sub_self _
        have h5 : (i + j) - (i - j) = j + j := by ring
        rw [← h5]; exact h4
      exact h3
    · exact DihedralGroup.sr_mul_self j
  exact mem_of_mul_self_eq_one_of_mem_normalizer hS hmax hgg hcn

end S2C

theorem L2_sylow_self_cent {I : Type} [Group I] [Finite I] {q : ℕ}
    (hI : CFSG.GH74.GLS.IVK.IsL2 I (fun r => r = q)) (hq5 : 5 ≤ q) (hqodd : Odd q)
    (T₁ : Subgroup I) (hT₁ : IsPGroup 2 T₁)
    (hmax : ∀ P : Subgroup I, IsPGroup 2 P → T₁ ≤ P → P = T₁) :
    ∀ g : I, (∀ a ∈ T₁, g * a = a * g) → g ∈ T₁ := by
  obtain ⟨ε, δ, hε1, hε, hδ⟩ : ∃ (ε : ℤ) (δ : ℕ), (ε = 1 ∨ ε = -1) ∧ (q : ℤ) ≡ ε [ZMOD 4] ∧
      ((2 * δ : ℕ) : ℤ) = q - ε := by
    have h4 : q % 4 = 1 ∨ q % 4 = 3 := by
      obtain ⟨k, hk⟩ := hqodd
      omega
    rcases h4 with h4 | h4
    · exact ⟨1, (q - 1) / 2, Or.inl rfl, by unfold Int.ModEq; omega, by omega⟩
    · exact ⟨-1, (q + 1) / 2, Or.inr rfl, by unfold Int.ModEq; omega, by omega⟩
  obtain ⟨hcard, -, hcent⟩ := L2_involution_facts hI hq5 hqodd hε1 hε hδ
  have heven : 2 ∣ Nat.card I := by
    obtain ⟨k, hk⟩ := hqodd
    have h1 : q ^ 2 - 1 = 4 * (k * (k + 1)) := by
      have h2 : q ^ 2 = 4 * (k * (k + 1)) + 1 := by rw [hk]; ring
      omega
    have h3 : 2 * Nat.card I = 4 * (q * (k * (k + 1))) := by
      rw [hcard, h1]
      ring
    exact ⟨q * (k * (k + 1)), by omega⟩
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' 2 heven
  have hT₁ne : Nontrivial T₁ := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    intro hbot
    have hzp : IsPGroup 2 (zpowers v) := by
      refine IsPGroup.of_card_dvd_pow (n := 1) ?_
      rw [Nat.card_zpowers, hv, pow_one]
    have h := hmax _ hzp (by rw [hbot]; exact bot_le)
    have hv1 : v ∈ T₁ := by
      rw [← h]
      exact mem_zpowers v
    rw [hbot, mem_bot] at hv1
    rw [hv1, orderOf_one] at hv
    exact absurd hv (by norm_num)
  have hcenter : Nontrivial (center T₁) := hT₁.center_nontrivial
  have hcP : IsPGroup 2 (center T₁) :=
    hT₁.of_injective (center T₁).subtype (center T₁).subtype_injective
  have hdvd : 2 ∣ Nat.card (center T₁) := by
    rcases hcP.card_eq_or_dvd with h | h
    · exact absurd (Nat.card_eq_one_iff_unique.mp h).1 (not_subsingleton _)
    · exact h
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  obtain ⟨u, huT, hu2, hcommu⟩ : ∃ u : I, u ∈ T₁ ∧ orderOf u = 2 ∧ ∀ a ∈ T₁, a * u = u * a := by
    refine ⟨((z : T₁) : I), (z : T₁).2, ?_, fun a ha => ?_⟩
    · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
      exact hz
    · exact congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨a, ha⟩)
  have hTC : T₁ ≤ centralizer ({u} : Set I) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcommu a ha)
  obtain ⟨φ⟩ := hcent u hu2
  have hS₀ : IsPGroup 2 (T₁.subgroupOf (centralizer ({u} : Set I))) :=
    hT₁.of_equiv (Subgroup.subgroupOfEquivOfLe hTC).symm
  have hmax₀ : ∀ P : Subgroup (centralizer ({u} : Set I)), IsPGroup 2 P →
      T₁.subgroupOf (centralizer ({u} : Set I)) ≤ P →
      P = T₁.subgroupOf (centralizer ({u} : Set I)) := by
    intro P hP hle
    have hPI : IsPGroup 2 (P.map (centralizer ({u} : Set I)).subtype) := hP.map _
    have hT1le : T₁ ≤ P.map (centralizer ({u} : Set I)).subtype := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hTC]
      exact Subgroup.map_mono hle
    have heq := hmax _ hPI hT1le
    refine le_antisymm (fun x hx => ?_) hle
    rw [Subgroup.mem_subgroupOf, ← heq]
    exact ⟨x, hx, rfl⟩
  intro g hg
  have hgC : g ∈ centralizer ({u} : Set I) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hg u huT)
  have key := S2C.mem_of_centralizes_of_dihedral φ hS₀ hmax₀ (g := ⟨g, hgC⟩)
    (fun a ha => Subtype.ext (hg a (Subgroup.mem_subgroupOf.mp ha)))
  exact Subgroup.mem_subgroupOf.mp key

end CFSG.GH74.GLS.SP.Local
