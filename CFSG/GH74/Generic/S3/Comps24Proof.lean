module

public import CFSG.GH74.Generic.S3.Comps24
public import CFSG.GH74.Generic.S3.Rank5Inv

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank Subgroup
open scoped MatrixGroups

theorem exists_sq_mem_pair {G : Type} [Group G] [Finite G] {T : Subgroup G} (hT : IsPGroup 2 ↥T)
    (hcard : 3 ≤ Nat.card ↥T) {v : G} (hv : v * v = 1) :
    ∃ x ∈ T, x ≠ 1 ∧ x ≠ v ∧ (x * x = 1 ∨ x * x = v) := by
  classical
  have hy : ∃ y ∈ T, y ≠ 1 ∧ y ≠ v := by
    by_contra hcon
    have hle : T ≤ zpowers v := by
      intro y hy
      by_cases h1 : y = 1
      · rw [h1]; exact one_mem _
      · have : y = v := by
          by_contra h2
          exact hcon ⟨y, hy, h1, h2⟩
        rw [this]; exact mem_zpowers v
    have h1 := Subgroup.card_le_of_le hle
    have h2 := card_zpowers_le_two hv
    omega
  obtain ⟨y, hyT, hy1, hyv⟩ := hy
  obtain ⟨k, hk⟩ := hT ⟨y, hyT⟩
  have hk' : y ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hex : ∃ j : ℕ, y ^ (2 ^ j) = 1 ∨ y ^ (2 ^ j) = v := ⟨k, Or.inl hk'⟩
  obtain ⟨j, hj, hmin⟩ : ∃ j : ℕ, (y ^ (2 ^ j) = 1 ∨ y ^ (2 ^ j) = v) ∧
      ∀ m : ℕ, m < j → ¬ (y ^ (2 ^ m) = 1 ∨ y ^ (2 ^ m) = v) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  have hj0 : j ≠ 0 := by
    intro h
    rw [h, pow_zero, pow_one] at hj
    rcases hj with h1 | h1
    · exact hy1 h1
    · exact hyv h1
  obtain ⟨j', hj'⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  have hlt : j' < j := by omega
  refine ⟨y ^ (2 ^ j'), Subgroup.pow_mem T hyT _, ?_, ?_, ?_⟩
  · intro h
    exact hmin j' hlt (Or.inl h)
  · intro h
    exact hmin j' hlt (Or.inr h)
  · have h2 : 2 ^ j = 2 ^ j' + 2 ^ j' := by rw [hj', Nat.pow_succ]; omega
    rw [← pow_add, ← h2]
    exact hj

theorem b_S3_comps24_of_cover (hcov : B_L3_cover) : B_S3_comps24 := by
  intro G _ _ hG t p f v w Iv Iw Ivw P V v₁ hcfg F _ _ hF J₀ _ J₂ hP₀ _ hP₂ hJ₀Iv _ hcomm _ J hJ
  have C := hcfg.conf
  obtain ⟨-, -, hcomp⟩ := b_S3_layers_of_cover hcov G hG t p f v w Iv Iw Ivw P V v₁ hcfg F
    inferInstance inferInstance hF
  have hs := hcfg.setup
  have hwv₁ : w * v₁ ∈ Wset V w := by
    show w * (w * v₁) ∈ V
    rw [← mul_assoc, hs.w_sq, one_mul]
    exact hcfg.hv₁.1
  have hv2 : v * v = 1 := hs.V_sq v hcfg.hv.1
  have hv1 : v ≠ 1 := hcfg.hv.2
  have hJ₂c : IsCompC J₂ v := hcomp (w * v₁) hwv₁ v hcfg.hv J₂ hP₂
  have hJ₀c : IsCompC J₀ v := hJ₀Iv ▸ C.comp_v
  by_contra hcon
  obtain ⟨hJ0, hJ2⟩ := not_or.1 hcon
  have hc0 : ∀ a ∈ J, ∀ b ∈ J₀, a * b = b * a :=
    (hJ.eq_or_commute hJ₀c).resolve_left (fun h => hJ0 (h.trans hJ₀Iv))
  have hc2 : ∀ a ∈ J, ∀ b ∈ J₂, a * b = b * a := (hJ.eq_or_commute hJ₂c).resolve_left hJ2
  have hJq : IsQuasisimple ↥J :=
    LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJ.1) hJ.2.1
  obtain ⟨P', hP'2, hP'4⟩ := exists_two_subgroup_card_ge_four hJq
  have hT2 : IsPGroup 2 (P'.map J.subtype) := hP'2.map J.subtype
  have hTcard : Nat.card (P'.map J.subtype) = Nat.card P' :=
    Subgroup.card_map_of_injective J.subtype_injective
  obtain ⟨x, hxT, hx1, hxv, hxsq⟩ := exists_sq_mem_pair hT2 (by omega) hv2
  have hxJ : x ∈ J := by
    obtain ⟨y, -, rfl⟩ := hxT
    exact y.2
  have hx0 : ∀ a ∈ J₀, a * x = x * a := fun a ha => (hc0 x hxJ a ha).symm
  have hx2 : ∀ b ∈ J₂, b * x = x * b := fun b hb => (hc2 x hxJ b hb).symm
  have hz0 : v ∈ J₀ := hP₀.mem
  have hz2 : v ∈ J₂ := hP₂.mem
  have hzc0 : ∀ a ∈ J₀, a * v = v * a := fun a ha => (hP₀.commute a ha).2
  have hzc2 : ∀ a ∈ J₂, a * v = v * a := fun a ha => (hP₂.commute a ha).2
  obtain ⟨e0⟩ := hP₀.iso
  obtain ⟨e2⟩ := hP₂.iso
  have hF2 : ringChar F ≠ 2 := ringChar_ne_two_of_card_pow C.prime.1 C.prime.2.1 hF
  have hind : ∀ a ∈ J₀, ∀ b ∈ J₂, x ≠ a * b := by
    intro a ha b hb hab
    rcases mem_center_pair_of_commute hF2 e0 e2 hcomm hz0 hz2 hv1 hv2 hzc0 hzc2 hx0 hx2 ha hb
      hab with h | h
    · exact hx1 h
    · exact hxv h
  exact not_gen4_of_sl2_pair_sq hF2 e0 e2 hcomm hz0 hz2 hv2 hx0 hx2 hxsq hind hG.gen4

end CFSG.GH74.Generic.S3
