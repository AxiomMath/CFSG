module

public import CFSG.GH74.GLS.Stage1.Main.Bridge
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Basic
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank

public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm3

variable {G : Type} [Group G] [Finite G]

theorem sylow_top_of_central {z : G} {S : Subgroup G} (hz : IsCentralInvolution z)
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (centralizer ({z} : Set G))) :
    CFSG.ABGLocalTools.IsSylowOf 2 S ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨_, S', hzS', hzc⟩ := hz
  have hS'le : (S' : Subgroup G) ≤ centralizer ({z} : Set G) := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzc s hs)
  have hS'G : CFSG.ABGLocalTools.IsSylowOf 2 (S' : Subgroup G) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_top, S'.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact S'.not_dvd_index
  have hS'C := hS'G.of_le hS'le le_top
  have h1 := hS.card_eq
  have h2 := hS'C.card_eq
  have h3 := hS'G.card_eq
  refine CFSG.ABGLocalTools.isSylowOf_of_card le_top ?_
  rw [h1, ← h2, h3]

theorem pRank_eq_of_sylow_top {S : Subgroup G} (hS : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤) :
    pRank 2 ↥S = pRank 2 G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := (CFSG.ABGLocalTools.isSylowOf_iff).1 hS
  have hidx : ¬ 2 ∣ S.index := by
    have := h.2.2
    rwa [Subgroup.relIndex_top_right] at this
  let P : Sylow 2 G := h.2.1.toSylow hidx
  have hP : (P : Subgroup G) = S := IsPGroup.toSylow_coe _ _
  have := (CFSG.SectionRank.pRank_sylow P).2
  rwa [hP] at this

omit [Finite G] in
theorem isCentralInvolution_of_classical {z : G} (hcl : IsStronglyClassicalInvolution G z)
    (hthm2 : ∃ t ∈ centralizer ({z} : Set G), IsConj z t ∧ t ∉ zStar (rigidProduct z)) :
    IsCentralInvolution z := by
  obtain ⟨t, htC, htz, htn⟩ := hthm2
  obtain ⟨S, hS⟩ := (hcl.2 t htC htz htn).2.2.2.1
  have hz := (hS z).2 (Subgroup.mem_zpowers z)
  exact ⟨hcl.1, S, hz.1, hz.2.1⟩

@[expose] def ZCen (z : G) (S : Subgroup G) : Prop :=
  ∀ w ∈ S, (∀ s ∈ S, s * w = w * s) → orderOf w = 2 → w = z

theorem zcen_of_classical {z : G} {S : Subgroup G} (hcl : IsStronglyClassicalInvolution G z)
    (hthm2 : ∃ t ∈ centralizer ({z} : Set G), IsConj z t ∧ t ∉ zStar (rigidProduct z))
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (centralizer ({z} : Set G))) : ZCen z S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, htC, htz, htn⟩ := hthm2
  obtain ⟨S₀, hS₀⟩ := (hcl.2 t htC htz htn).2.2.2.1
  have hz := (hS₀ z).2 (Subgroup.mem_zpowers z)
  have hS₀le : (S₀ : Subgroup G) ≤ centralizer ({z} : Set G) := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hz.2.1 s hs)
  have hS₀C : CFSG.ABGLocalTools.IsSylowOf 2 (S₀ : Subgroup G) (centralizer ({z} : Set G)) := by
    have hS₀G : CFSG.ABGLocalTools.IsSylowOf 2 (S₀ : Subgroup G) ⊤ := by
      rw [CFSG.ABGLocalTools.isSylowOf_iff]
      refine ⟨le_top, S₀.isPGroup', ?_⟩
      rw [Subgroup.relIndex_top_right]
      exact S₀.not_dvd_index
    exact hS₀G.of_le hS₀le le_top
  obtain ⟨c, hcC, hc⟩ := Sec4.M.Syl2In.exists_conj ((CFSG.ABGLocalTools.isSylowOf_iff).1 hS₀C)
    ((CFSG.ABGLocalTools.isSylowOf_iff).1 hS)
  have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hcC
  intro w hwS hwc hw2
  have hcw : c * w * c⁻¹ ∈ (S₀ : Subgroup G) := by
    have : w ∈ Sec4.M.cj (S₀ : Subgroup G) c := hc ▸ hwS
    exact this
  have hcent : ∀ s₀ ∈ (S₀ : Subgroup G), s₀ * (c * w * c⁻¹) = (c * w * c⁻¹) * s₀ := by
    intro s₀ hs₀
    have hs : c⁻¹ * s₀ * c ∈ S := by
      have : c⁻¹ * s₀ * c ∈ Sec4.M.cj (S₀ : Subgroup G) c := by
        show c * (c⁻¹ * s₀ * c) * c⁻¹ ∈ (S₀ : Subgroup G)
        simpa [mul_assoc] using hs₀
      exact hc ▸ this
    have h1 := hwc _ hs
    calc s₀ * (c * w * c⁻¹) = c * ((c⁻¹ * s₀ * c) * w) * c⁻¹ := by group
      _ = c * (w * (c⁻¹ * s₀ * c)) * c⁻¹ := by rw [h1]
      _ = (c * w * c⁻¹) * s₀ := by group
  have hsq : (c * w * c⁻¹) ^ 2 = 1 := by
    have hw1 : w ^ 2 = 1 := by rw [← hw2]; exact pow_orderOf_eq_one w
    rw [conj_pow, hw1]; group
  have hmem := ((hS₀ (c * w * c⁻¹)).1 ⟨hcw, hcent, hsq⟩)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hzo : orderOf z = 2 := hcl.1
  have hk2 : z ^ (k % 2) = c * w * c⁻¹ := by
    rw [← hk]
    have := zpow_mod_orderOf z k
    rwa [hzo, Nat.cast_ofNat] at this
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · rw [h0, zpow_zero] at hk2
    have hw1 : w = 1 := by
      calc w = c⁻¹ * (c * w * c⁻¹) * c := by group
        _ = c⁻¹ * 1 * c := by rw [← hk2]
        _ = 1 := by group
    rw [hw1, orderOf_one] at hw2
    omega
  · rw [h1, zpow_one] at hk2
    calc w = c⁻¹ * (c * w * c⁻¹) * c := by group
      _ = c⁻¹ * z * c := by rw [← hk2]
      _ = z := by rw [mul_assoc, ← hcz]; group

theorem Stage1Base.of_parts {z : G} {S : Subgroup G} (hz : ZCen z S)
    (hr : (RC S z ≠ S → ∃ s ∈ S, s ∉ RC S z ∧ orderOf s = 2) ∧
      (∀ U : Subgroup G, U ≤ S → IVK.IsFourSubgroup U → (∀ s ∈ S, ∀ u ∈ U, s * u * s⁻¹ ∈ U) →
        U ≤ LC z)) : Stage1Base G z S :=
  ⟨hz, hr.1, hr.2⟩

theorem Cen2.of_classical {z : G} {S : Subgroup G} (hStd : Std0 G) (hcl : IsStronglyClassicalInvolution G z)
    (hthm2 : ∃ t ∈ centralizer ({z} : Set G), IsConj z t ∧ t ∉ zStar (rigidProduct z))
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (centralizer ({z} : Set G))) : Cen2 G z S :=
  ⟨hStd, isCentralInvolution_of_classical hcl hthm2, hS⟩

theorem Cen2.pRank_eq {z : G} {S : Subgroup G} (h : Cen2 G z S) : pRank 2 ↥S = pRank 2 G :=
  pRank_eq_of_sylow_top (sylow_top_of_central h.central h.sylow)

end CFSG.GH74.GLS.Stage1.Main
