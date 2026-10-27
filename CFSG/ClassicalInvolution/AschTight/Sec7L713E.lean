module

public import CFSG.ClassicalInvolution.Asc77.AscL62Main
public import CFSG.ClassicalInvolution.AschTight.Sec7Basic

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem exists_mem_USet_le (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) {R : Subgroup G}
    (hR : R ∈ RSet Ω) : ∃ U ∈ USet Ω, U ≤ R := by
  obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR
  obtain ⟨U, hUR, hUc, hcard⟩ := (hΩ.isQuatSub_of_mem_RSet hp hR).exists_cyclic_index_two
  exact ⟨U, mem_USet_of_natCard hJ hRJ hUR hUc hcard, hUR⟩

omit [Finite G] in
theorem le_normalizer_of_commutator_le {V J : Subgroup G} (h : ⁅V, J⁆ ≤ oddCoreOf J) :
    V ≤ Subgroup.normalizer (J : Set G) := by
  have key : ∀ v ∈ V, ∀ j ∈ J, v * j * v⁻¹ ∈ J := by
    intro v hv j hj
    have h1 : v * j * v⁻¹ * j⁻¹ ∈ J :=
      oddCoreOf_le_self J (h (Subgroup.commutator_mem_commutator hv hj))
    have e : v * j * v⁻¹ = (v * j * v⁻¹ * j⁻¹) * j := by group
    rw [e]
    exact J.mul_mem h1 hj
  intro v hv
  rw [Subgroup.mem_normalizer_iff]
  intro j
  refine ⟨key v hv j, fun hj => ?_⟩
  have := key v⁻¹ (V.inv_mem hv) _ hj
  rwa [show v⁻¹ * (v * j * v⁻¹) * v⁻¹⁻¹ = j by group] at this

theorem eq_or_mem_omegaStarNbr_of_fixed (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {J L : Subgroup G} (hJ : J ∈ Ω) (hL : L ∈ Ω) {a : G} (ha : IsUniqueInvolution J a)
    {g : G} (hgL : g ∈ L) (hga : a * g * a⁻¹ = g) (hg4 : orderOf g = 4) :
    L = J ∨ L ∈ omegaStarNbr Ω J := by
  by_cases hLJ : L = J
  · exact Or.inl hLJ
  right
  obtain ⟨zL, hzL⟩ := hΩ.exists_uniqueInvolution hp hq hL
  have hA2 : IsPGroup 2 (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hg4]; norm_num)
  have hA4 : Nat.card (Subgroup.zpowers g) = 4 := by rw [Nat.card_zpowers, hg4]
  have hAL : Subgroup.zpowers g ≤ L := Subgroup.zpowers_le.mpr hgL
  have hAa : Subgroup.zpowers g ≤ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    calc g * a = a * g * a⁻¹ * a := by rw [hga]
      _ = a * g := by group
  have hzA : zL ∈ Subgroup.zpowers g := hzL.mem_of_le hAL hA2 (by omega)
  by_cases htw : L ∈ twinSet Ω J
  · obtain ⟨-, z', hz'J, hz'L⟩ := htw
    have hLN := hΩ.le_normalizer_of_twin hL hJ hLJ hz'L hz'J
    obtain ⟨R, hR⟩ := exists_isSylow2In L
    obtain ⟨U, hU, hUR⟩ := exists_mem_USet_le hp hΩ (mem_RSet_of_isSylow2In hL hR)
    exact ⟨hL, hLJ, U, hU, hUR.trans hR.1, (hUR.trans hR.1).trans hLN⟩
  obtain ⟨V, hV, hAV⟩ := IsSylow2In.exists_ge hA2 (le_inf hAL hAa)
  have hzV : zL ∈ V := hAV hzA
  have hcard : ¬ V = Subgroup.zpowers zL := by
    intro h
    have h1 := Subgroup.card_le_of_le (h ▸ hAV)
    rw [hA4, Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hzL.sq) hzL.ne_one] at h1
    omega
  rcases l6_2 p f hp hq G Ω hΩ J hJ a ha L hL htw zL hzL V hV hzV with
    h | h | ⟨hVU, hVN, -⟩ | ⟨hVR, hVc⟩
  · exact absurd h.1 hcard
  · exact absurd h.1 hcard
  · exact ⟨hL, hLJ, V, hVU, hV.1.trans inf_le_left, hVN⟩
  · obtain ⟨U, hU, hUV⟩ := exists_mem_USet_le hp hΩ hVR
    exact ⟨hL, hLJ, U, hU, hUV.trans (hV.1.trans inf_le_left),
      hUV.trans (le_normalizer_of_commutator_le hVc)⟩

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7
