module

public import CFSG.CGT.Timmesfeld75.SimpleCase
public import CFSG.CGT.Timmesfeld75.StdPair
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.Adapters.Involutions
import CFSG.CGT.PushingUpLit.A78Sp4.Util

public section

namespace CFSG.CGT.PushingUpLit.T2KSW

open CFSG CFSG.ABGLocalTools CFSG.CGT.Timmesfeld75 CFSG.Open

theorem exists_sylow_two_of_isSylowOf_top {G : Type*} [Group G] [Finite G] {T : Subgroup G}
    (hT : IsSylowOf 2 T ⊤) : ∃ S : Sylow 2 G, (S : Subgroup G) = T := by
  have h := isSylowOf_iff.1 hT
  exact ⟨h.2.1.toSylow (by simpa [Subgroup.relIndex_top_right] using h.2.2), rfl⟩

theorem four_le_card_of_weaklyClosed {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hna : ∃ a b : G, a * b ≠ b * a) {E T : Subgroup G} (hT : IsSylowOf 2 T ⊤) (hET : E ≤ T)
    (hTE : T ≤ Subgroup.normalizer (E : Set G)) (hE1 : E ≠ ⊥) (hEab : IsElemAbelian 2 E)
    (hwc : ∀ g : G, conjSubgroup g E ≤ T → conjSubgroup g E = E) : 4 ≤ Nat.card E := by
  by_contra hlt
  push Not at hlt
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2E : Nat.card E = 2 := by
    have hEp : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by simpa using hEab.2 x x.2)⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hEp
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hE1 (Subgroup.eq_bot_of_card_eq E (by simpa using hk))
    have hk1 : k < 2 := by
      by_contra h
      push Not at h
      have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h
      omega
    obtain rfl : k = 1 := by omega
    simpa using hk
  obtain ⟨⟨z, hzE⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hE1
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hsq : z * z = 1 := by simpa [pow_two] using hEab.2 z hzE
  have hord : orderOf z = 2 := orderOf_eq_prime (by simpa [pow_two] using hsq) hz1'
  have hEeq : E = Subgroup.zpowers z := by
    symm
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.zpowers_le]
      exact hzE
    · rw [Nat.card_zpowers, hord, h2E]
  have hmemE : ∀ y ∈ E, y = 1 ∨ y = z := by
    intro y hy
    rw [hEeq] at hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hpow : z ^ k = z ^ (k % 2) :=
      zpow_eq_zpow_emod k (by simpa [hord] using pow_orderOf_eq_one z)
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      rw [hpow, h] at hk
      simpa using hk.symm
    · right
      rw [hpow, h] at hk
      simpa using hk.symm
  have hconj1 : ∀ g : G, g⁻¹ * z * g ≠ 1 := fun g h => hz1' (by
    have e : z = g * (g⁻¹ * z * g) * g⁻¹ := by group
    rw [e, h]
    group)
  have hzcent : ∀ t ∈ T, t * z * t⁻¹ = z := by
    intro t ht
    have h1 : t * z * t⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.1 (hTE ht) z).1 hzE
    rcases hmemE _ h1 with h | h
    · exfalso
      exact hconj1 t⁻¹ (by simpa using h)
    · exact h
  obtain ⟨S, hS⟩ := exists_sylow_two_of_isSylowOf_top hT
  have hzS : z ∈ (S : Subgroup G) := hS ▸ hET hzE
  have hzZ : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G) := by
    rw [Subgroup.mem_center_iff]
    intro s
    apply Subtype.ext
    have hsT : (s : G) ∈ T := hS ▸ s.2
    have h := hzcent _ hsT
    show (s : G) * z = z * s
    calc (s : G) * z = (s : G) * z * (s : G)⁻¹ * s := by group
      _ = z * s := by rw [h]
  have hordS : orderOf (⟨z, hzS⟩ : (S : Subgroup G)) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hord
  have hwcS : ∀ g : G, g⁻¹ * z * g ∈ (S : Subgroup G) → g⁻¹ * z * g = z := by
    intro g hg
    have hgT : g⁻¹ * z * g ∈ T := hS ▸ hg
    have hle : conjSubgroup g⁻¹ E ≤ T := by
      intro y hy
      rw [mem_conjSubgroup, inv_inv] at hy
      rcases hmemE _ hy with h | h
      · have : y = 1 := by
          have e : y = g⁻¹ * (g * y * g⁻¹) * g := by group
          rw [e, h]
          group
        rw [this]
        exact T.one_mem
      · have : y = g⁻¹ * z * g := by
          have e : y = g⁻¹ * (g * y * g⁻¹) * g := by group
          rw [e, h]
        rw [this]
        exact hgT
    have hmem : g⁻¹ * z * g ∈ E := by
      have h2 := hwc g⁻¹ hle
      have : g⁻¹ * z * g ∈ conjSubgroup g⁻¹ E := by
        rw [mem_conjSubgroup, inv_inv]
        have e : g * (g⁻¹ * z * g) * g⁻¹ = z := by group
        rw [e]
        exact hzE
      rwa [h2] at this
    rcases hmemE _ hmem with h | h
    · exact absurd h (hconj1 g)
    · exact h
  obtain ⟨-, hcen⟩ := CFSG.Adapters.glauberman_zStar S ⟨z, hzS⟩ hzZ hordS hwcS
  have hodd0 : oddCore G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (oddCore G) with h | h
    · exact h
    · exfalso
      have hz' : z ∈ oddCore G := by
        rw [h]
        exact Subgroup.mem_top z
      exact CFSG.Adapters.not_mem_oddCore_of_orderOf_eq_two hord hz'
  have hzG : z ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h := Subgroup.mem_center_iff.1 hcen (QuotientGroup.mk g)
    have h' : (g * z)⁻¹ * (z * g) ∈ oddCore G := by
      rw [← QuotientGroup.eq, QuotientGroup.mk_mul, QuotientGroup.mk_mul]
      exact h
    rw [hodd0, Subgroup.mem_bot, inv_mul_eq_one] at h'
    exact h'
  have hcenter : Subgroup.center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hna
      apply hab
      have ha : a ∈ Subgroup.center G := by
        rw [h]
        exact Subgroup.mem_top a
      exact ((Subgroup.mem_center_iff.mp ha) b).symm
  rw [hcenter, Subgroup.mem_bot] at hzG
  exact hz1' hzG

theorem conjSubgroup_mul_conjSubgroup {G : Type*} [Group G] (g h : G) (E : Subgroup G) :
    conjSubgroup (g * h) E = conjSubgroup g (conjSubgroup h E) := by
  ext y
  simp only [mem_conjSubgroup]
  rw [show (g * h)⁻¹ * y * (g * h) = h⁻¹ * (g⁻¹ * y * g) * h by group]

theorem conjSubgroup_eq_of_mem_normalizer_self {G : Type*} [Group G] {E : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (E : Set G)) : conjSubgroup g E = E := by
  ext y
  rw [mem_conjSubgroup]
  have := Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (E : Set G)).inv_mem hg) y
  rw [inv_inv] at this
  exact this.symm

theorem isWC_of_weaklyClosed {G : Type} [Group G] [Finite G] {E M T : Subgroup G}
    (hEab : IsElemAbelian 2 E) (hN : Subgroup.normalizer (E : Set G) = M)
    (hTM : IsSylowOf 2 T M) (hTI : ∀ g : G, g ∉ M → E ⊓ conjSubgroup g E = ⊥)
    (hwc : ∀ g : G, conjSubgroup g E ≤ T → conjSubgroup g E = E) : IsWC E := by
  have hEp : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by simpa using hEab.2 x x.2)⟩
  refine isWC_of_corBHyp (corBHyp_of_ti_of_weaklyClosed hEab (fun g => ?_) (fun g hle => ?_))
  · by_cases hg : g⁻¹ ∈ M
    · right
      rw [conjSubgroup_eq_of_mem_normalizer_self (hN ▸ hg), inf_idem]
    · left
      exact hTI g⁻¹ hg
  · have hM : conjSubgroup g⁻¹ E ≤ M := hN ▸ hle
    have hPp : IsPGroup 2 (conjSubgroup g⁻¹ E) := hEp.map _
    obtain ⟨m, hmM, hm⟩ := A78Sp4.exists_mem_conj_le_of_isSylowOf hTM hM hPp
    have hle' : conjSubgroup (m * g⁻¹) E ≤ T := by
      rw [conjSubgroup_mul_conjSubgroup]
      intro y hy
      rw [mem_conjSubgroup] at hy
      have := hm _ hy
      simpa [mul_assoc] using this
    have h1 := hwc _ hle'
    calc conjSubgroup g⁻¹ E = conjSubgroup (m⁻¹ * (m * g⁻¹)) E := by rw [inv_mul_cancel_left]
      _ = conjSubgroup m⁻¹ (conjSubgroup (m * g⁻¹) E) := conjSubgroup_mul_conjSubgroup _ _ _
      _ = conjSubgroup m⁻¹ E := by rw [h1]
      _ = E := conjSubgroup_eq_of_mem_normalizer_self (hN ▸ M.inv_mem hmM)

theorem stdPair_of_weaklyClosed (hSCL : SimpleCaseListStmt) (hList : ListWCIdentification)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hna : ∃ a b : G, a * b ≠ b * a)
    {E M T : Subgroup G} (hET : E ≤ T) (hE1 : E ≠ ⊥) (hEab : IsElemAbelian 2 E)
    (hN : Subgroup.normalizer (E : Set G) = M) (hTM : IsSylowOf 2 T M) (hTG : IsSylowOf 2 T ⊤)
    (hTI : ∀ g : G, g ∉ M → E ⊓ conjSubgroup g E = ⊥)
    (hwc : ∀ g : G, conjSubgroup g E ≤ T → conjSubgroup g E = E) : StdPair G E := by
  have hE4 := four_le_card_of_weaklyClosed hna hTG hET (by rw [hN]; exact hTM.le) hE1 hEab hwc
  have hWC := isWC_of_weaklyClosed hEab hN hTM hTI hwc
  exact hList G (hSCL G hna E hWC hE4) E hWC hE4

end CFSG.CGT.PushingUpLit.T2KSW
