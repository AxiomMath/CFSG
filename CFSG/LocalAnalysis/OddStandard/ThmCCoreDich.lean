module

public import CFSG.LocalAnalysis.OddStandard.ThmCCoreCase

public section

namespace CFSG.OddStandard.ThmC.Core

open CFSG Subgroup CFSG.OddStandard.ThmC CFSG.OddStandard.ThmC.T CFSG.RankTwoShapes
open CFSG.GH74.GLS.Bg.TwoGroups

section Dichotomy

variable {X : Type} [Group X] [Finite X] {T : Sylow 2 X} {Z A B L : Subgroup X} [L.Normal]

theorem center_le_inf (hTA : TAmbient (T : Subgroup X) Z A B) [Group.IsPerfect L]
    (heven : 2 ∣ Nat.card L) : Z ≤ (T : Subgroup X) ⊓ L := by
  set D : Subgroup X := (T : Subgroup X) ⊓ L with hD
  set S' : Sylow 2 L := sylowInfL T L with hS'
  have hDT : D ≤ (T : Subgroup X) := inf_le_left
  have hDn : ∀ s ∈ (T : Subgroup X), ∀ n ∈ D, s * n * s⁻¹ ∈ D := fun s hs n hn =>
    inf_normal_mem hs hn
  have hcardD : Nat.card D = Nat.card (S' : Subgroup L) := (card_sylowInfL T L).symm
  have h2D : 2 ∣ Nat.card (S' : Subgroup L) := Sylow.dvd_card_of_dvd_card S' heven
  rcases hTA.normal_dich D hDT hDn with hDZ | hZD
  · by_cases hDZeq : D = Z
    · exact hDZeq ▸ le_rfl
    · exfalso
      have hdvd : Nat.card D ∣ 4 := hTA.card_Z ▸ Subgroup.card_dvd_of_le hDZ
      have hne4 : Nat.card D ≠ 4 := fun h =>
        hDZeq (Subgroup.eq_of_le_of_card_ge hDZ (by rw [hTA.card_Z, h]))
      have hpos : 0 < Nat.card D := Nat.card_pos
      have hle : Nat.card D ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
      have h2 : Nat.card (S' : Subgroup L) = 2 := by omega
      have : IsCyclic (S' : Subgroup L) := isCyclic_of_prime_card (p := 2) h2
      obtain ⟨-, -, -, ⟨hKn, -, hKidx, -⟩, -⟩ := CFSG.cyclic_sylow_normal_odd_complement S' this
      have hq : IsPGroup 2 (L ⧸ pPrimeCore 2 L) :=
        IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hKidx.trans h2)
      have hKtop : pPrimeCore 2 L = ⊤ := eq_top_of_pGroup_quotient hq
      rw [hKtop, Subgroup.index_top, h2] at hKidx
      exact absurd hKidx (by norm_num)
  · exact hZD

end Dichotomy

theorem coreDichotomy (hS2 : O2Structure) (hGor : CFSG.OddStandard.ThmC.O2.Gor42)
    {X : Type} [Group X] [Finite X] (T : Sylow 2 X) (hT : IsT (T : Subgroup X))
    (L : Subgroup X) [L.Normal] [Group.IsPerfect L] (heven : 2 ∣ Nat.card L)
    (hO : pPrimeCore 2 L = ⊥) : (T : Subgroup X) ≤ L := by
  obtain ⟨Z, A, B, hTA⟩ := hT.exists_tAmbient
  have hZD : Z ≤ (T : Subgroup X) ⊓ L := center_le_inf hTA heven
  by_cases hA : A ≤ (T : Subgroup X) ⊓ L
  · by_cases hB : B ≤ (T : Subgroup X) ⊓ L
    · intro t ht
      obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_A_B hT hTA t ht
      exact L.mul_mem (hA ha).2 (hB hb).2
    · exfalso
      by_cases hAD : A = (T : Subgroup X) ⊓ L
      · exact not_abel hS2 hGor hT hTA hAD heven hO
      · exact not_u1 hS2 hT hTA hZD hA hB hAD
  · by_cases hB : B ≤ (T : Subgroup X) ⊓ L
    · exfalso
      have hTA' := tAmbient_swap hTA
      by_cases hBD : B = (T : Subgroup X) ⊓ L
      · exact not_abel hS2 hGor hT hTA' hBD heven hO
      · exact not_u1 hS2 hT hTA' hZD hB hA hBD
    · exact (not_frob hS2 hT hTA hZD hA hB heven).elim

theorem coreDichotomy_sub (hS2 : O2Structure) (hGor : CFSG.OddStandard.ThmC.O2.Gor42)
    {X : Type} [Group X] [Finite X] (T : Sylow 2 X) (hT : IsT (T : Subgroup X))
    (Y L : Subgroup X) (hTY : (T : Subgroup X) ≤ Y) (hLY : L ≤ Y)
    (hnorm : ∀ y ∈ Y, ∀ l ∈ L, y * l * y⁻¹ ∈ L) [Group.IsPerfect L] (heven : 2 ∣ Nat.card L)
    (hO : pPrimeCore 2 L = ⊥) : (T : Subgroup X) ≤ L := by
  set L' : Subgroup Y := L.subgroupOf Y with hL'
  have hL'n : L'.Normal := ⟨fun n hn y => by
    rw [hL', Subgroup.mem_subgroupOf] at hn ⊢
    exact hnorm y y.2 n hn⟩
  let e : L' ≃* L := Subgroup.subgroupOfEquivOfLe hLY
  have : Group.IsPerfect L' :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hT' : IsT ((T.subtype hTY : Sylow 2 Y) : Subgroup Y) := by
    obtain ⟨φ⟩ := hT
    have hcoe : ((T.subtype hTY : Sylow 2 Y) : Subgroup Y) = (T : Subgroup X).subgroupOf Y :=
      Sylow.coe_subtype T hTY
    exact ⟨((MulEquiv.subgroupCongr hcoe).trans (Subgroup.subgroupOfEquivOfLe hTY)).trans φ⟩
  have heven' : 2 ∣ Nat.card L' := by
    rw [Nat.card_congr e.toEquiv]
    exact heven
  have hO' : pPrimeCore 2 L' = ⊥ := by
    have h := pPrimeCore_map_iso 2 e.symm
    rw [hO, Subgroup.map_bot] at h
    exact h.symm
  have key := coreDichotomy hS2 hGor (T.subtype hTY : Sylow 2 Y) hT' L' heven' hO'
  intro t ht
  have ht' : (⟨t, hTY ht⟩ : Y) ∈ ((T.subtype hTY : Sylow 2 Y) : Subgroup Y) := by
    rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf]
    exact ht
  exact key ht'

end CFSG.OddStandard.ThmC.Core
