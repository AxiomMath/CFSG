module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P4K7
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5S22Abs

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5

open Subgroup CFSG.Open CFSG.Sporadic.Schreier.Tits CFSG.LocalAnalysis.EvenBN.Tits
open CFSG.LocalAnalysis.EvenBN.Tits.N.P4

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


theorem t_comm_and_not_mem (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀)
    (h17s : Node17s d z₀) {y₁ : G} (hy : IsV1 d z₀ y₁) :
    (∀ u ∈ Us d, star d d.t * u = u * star d d.t) ∧ star d d.t ∉ Us d := by
  obtain ⟨hF, hCe, hinf, hcomm⟩ := C_data h49 hd hz h10 h17s hy
  refine ⟨fun u hu => hcomm u (IsF20.U_le_Pgrp _ _ _ hu), fun hmem => ?_⟩
  have hm : star d d.t ∈ zpowers (star d d.t) ⊓ IsF20.Pgrp (Us d) (star d d.x₅) (star d y₁) :=
    ⟨mem_zpowers _, IsF20.U_le_Pgrp _ _ _ hmem⟩
  rw [hinf] at hm
  exact star_t_ne h49 hd hz (Subgroup.mem_bot.1 hm)

theorem U0s_data (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀)
    (h17s : Node17s d z₀) {y₁ : G} (hy : IsV1 d z₀ y₁) :
    IsElemAbelian 2 (U0s d) ∧ Nat.card ↥(U0s d) = 32 := by
  obtain ⟨hF, hCe, hinf, hcomm⟩ := C_data h49 hd hz h10 h17s hy
  obtain ⟨htU, htnU⟩ := t_comm_and_not_mem h49 hd hz h10 h17s hy
  have htt := star_t_mul_self h49 hd
  refine ⟨?_, card_U0 hF htt htU htnU⟩
  refine IsElemAbelian.sup_of_commute h17s.1 (isElemAbelian_zpowers (by rw [pow_two]; exact htt)) ?_
  rintro a ha b hb
  obtain ⟨n, rfl⟩ := hb
  exact (Commute.zpow_right (show Commute a (star d d.t) from (htU a ha).symm) n).eq

theorem elemAb_le_C (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀)
    (h17s : Node17s d z₀) {y₁ : G} (hy : IsV1 d z₀ y₁) {D : Subgroup (MulAut ↥d.s56V)}
    (hDC : D ≤ img d (CMt d)) (hD : IsElemAbelian 2 D) :
    Nat.card ↥D ≤ 32 ∧ (Nat.card ↥D = 32 → D = U0s d) := by
  obtain ⟨hF, hCe, hinf, hcomm⟩ := C_data h49 hd hz h10 h17s hy
  obtain ⟨htU, htnU⟩ := t_comm_and_not_mem h49 hd hz h10 h17s hy
  have htt := star_t_mul_self h49 hd
  have hZP : ∀ a ∈ zpowers (star d d.t), ∀ p ∈ IsF20.Pgrp (Us d) (star d d.x₅) (star d y₁),
      a * p = p * a := by
    intro a ha p hp
    obtain ⟨n, rfl⟩ := ha
    exact (Commute.zpow_left (show Commute (star d d.t) p from hcomm p hp) n).eq
  have h2 : Nat.card ↥(zpowers (star d d.t)) = 2 := card_zpowers_invol htt htnU
  obtain ⟨hle, heq⟩ := IsF20.card_elemAb_le_sup hF hZP hinf (hCe ▸ hDC)
    (fun a ha b hb => hD.comm ha hb) (fun a ha => hD.mul_self_eq_one ha)
  rw [h2] at hle heq
  refine ⟨hle, fun hc => ?_⟩
  rw [heq hc]
  exact sup_comm _ _

theorem node18_a (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀)
    (h17s : Node17s d z₀) {y₁ : G} (hy : IsV1 d z₀ y₁) :
    ∀ T' : Subgroup (MulAut ↥d.s56V), fusionIsSylowIn 2 T' (img d (CMt d)) →
      maxElemAbelian2 T' = {U0s d} := by
  intro T' hT'
  obtain ⟨hF, hCe, hinf, hcomm⟩ := C_data h49 hd hz h10 h17s hy
  obtain ⟨htU, htnU⟩ := t_comm_and_not_mem h49 hd hz h10 h17s hy
  have htt := star_t_mul_self h49 hd
  obtain ⟨hab, hcard⟩ := U0s_data h49 hd hz h10 h17s hy
  have hU0C : U0s d ≤ img d (CMt d) := by
    rw [hCe]
    exact sup_le ((IsF20.U_le_Pgrp _ _ _).trans le_sup_right) le_sup_left
  have hCN : img d (CMt d) ≤ normalizer ((U0s d : Subgroup (MulAut ↥d.s56V)) : Set _) :=
    (C_le_Ks h49 hd hz h10 h17s hy).trans inf_le_left
  have hU0T : U0s d ≤ T' :=
    le_of_fusionIsSylowIn_of_normalizes hT' (isPGroup_U0 hF htt htU htnU) hU0C (hT'.1.trans hCN)
  refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨hU0T, hab, fun D hD hDab => ?_⟩, fun E hE => ?_⟩
  · have := (elemAb_le_C h49 hd hz h10 h17s hy (hD.trans hT'.1) hDab).1
    rw [hcard]
    exact this
  · obtain ⟨hET, hEab, hEmax⟩ := hE
    have h1 : Nat.card ↥(U0s d) ≤ Nat.card ↥E := hEmax _ hU0T hab
    have h2 := elemAb_le_C h49 hd hz h10 h17s hy (hET.trans hT'.1) hEab
    exact h2.2 (le_antisymm h2.1 (hcard ▸ h1))

theorem node18_b (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀)
    (h17s : Node17s d z₀) (h17 : Node17 d z₀) {y₁ : G} (hy : IsV1 d z₀ y₁) :
    DeltaS d ⊆ (fun u => star d d.t * u) '' (Us d : Set (MulAut ↥d.s56V)) := by
  intro δ hδ
  obtain ⟨hδU0, h, hh, hδh⟩ := hδ
  obtain ⟨htU, htnU⟩ := t_comm_and_not_mem h49 hd hz h10 h17s hy
  have htt := star_t_mul_self h49 hd
  have hnot : δ ∉ Us d := by
    rw [← hδh]
    exact h17.2.2.2.2.2 h hh
  rcases (mem_sup_zpowers_iff_of_comm_invol htt htU).1 hδU0 with h1 | h1
  · exact absurd h1 hnot
  · exact ⟨star d d.t * δ, h1, by
      show star d d.t * (star d d.t * δ) = δ
      rw [← mul_assoc, htt, one_mul]⟩

theorem exists_Ks_conj_t (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀)
    (h17s : Node17s d z₀) {y₁ : G} (hy : IsV1 d z₀ y₁)
    (hCcent : img d (CMt d) = centralizer ({star d d.t} : Set (MulAut ↥d.s56V)) ⊓ Hs d)
    {a : MulAut ↥d.s56V} (ha : a ∈ DeltaS d) : ∃ k ∈ Ks d, k * star d d.t * k⁻¹ = a := by
  obtain ⟨haU, h, hh, hha⟩ := ha
  have htH : d.t ∈ Hg d := t_mem_Hg h49 hd
  have hg : star d h ∈ Hs d := actFun_mem_imgIn hh hh
  have hconj : star d (h * d.t * h⁻¹) = star d h * star d d.t * (star d h)⁻¹ :=
    star_conj_of_mem hh htH
  rw [hconj] at hha
  obtain ⟨hab, hcard⟩ := U0s_data h49 hd hz h10 h17s hy
  have hU0Hs : U0s d ≤ Hs d := U0s_le_Hs h49 hd hz h10
  have key : (U0s d).map (MulAut.conj (star d h)⁻¹).toMonoidHom ≤ img d (CMt d) := by
    rintro _ ⟨u, hu, rfl⟩
    rw [hCcent]
    refine ⟨mem_centralizer_singleton_iff.2 ?_, ?_⟩
    · have hua : u * a = a * u := hab.comm hu haU
      rw [← hha] at hua
      show (star d h)⁻¹ * u * (star d h)⁻¹⁻¹ * star d d.t =
        star d d.t * ((star d h)⁻¹ * u * (star d h)⁻¹⁻¹)
      calc (star d h)⁻¹ * u * (star d h)⁻¹⁻¹ * star d d.t
          = (star d h)⁻¹ * (u * (star d h * star d d.t * (star d h)⁻¹)) * star d h := by group
        _ = (star d h)⁻¹ * ((star d h * star d d.t * (star d h)⁻¹) * u) * star d h := by rw [hua]
        _ = star d d.t * ((star d h)⁻¹ * u * (star d h)⁻¹⁻¹) := by group
    · exact mul_mem (mul_mem (Subgroup.inv_mem _ hg) (hU0Hs hu)) (by simpa using hg)
  have hE : IsElemAbelian 2 ((U0s d).map (MulAut.conj (star d h)⁻¹).toMonoidHom) := hab.map _
  have hcard' : Nat.card ↥((U0s d).map (MulAut.conj (star d h)⁻¹).toMonoidHom) = 32 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj (star d h)⁻¹).injective, hcard]
  have heq := (elemAb_le_C h49 hd hz h10 h17s hy key hE).2 hcard'
  have hnorm : star d h ∈ normalizer ((U0s d : Subgroup (MulAut ↥d.s56V)) : Set (MulAut ↥d.s56V)) := by
    rw [Subgroup.mem_normalizer_iff'']
    intro x
    constructor
    · intro hx
      have h1 : (star d h)⁻¹ * x * star d h ∈
          (U0s d).map (MulAut.conj (star d h)⁻¹).toMonoidHom :=
        ⟨x, hx, by simp [MulAut.conj_apply]⟩
      rw [heq] at h1
      exact h1
    · intro hx
      have h1 : (star d h)⁻¹ * x * star d h ∈
          (U0s d).map (MulAut.conj (star d h)⁻¹).toMonoidHom := by
        rw [heq]; exact hx
      obtain ⟨u, hu, hux⟩ := h1
      have : u = x := by
        have h2 : (star d h)⁻¹ * u * star d h = (star d h)⁻¹ * x * star d h := by
          simpa [MulAut.conj_apply] using hux
        simpa using h2
      rw [← this]
      exact hu
  exact ⟨star d h, ⟨hnorm, hg⟩, hha⟩

theorem node18_c (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀)
    (h17s : Node17s d z₀) (h17 : Node17 d z₀) {y₁ : G} (hy : IsV1 d z₀ y₁) :
    ∀ a ∈ DeltaS d, ∀ b ∈ DeltaS d, ∃ k ∈ Ks d, k * a * k⁻¹ = b := by
  intro a ha b hb
  obtain ⟨ka, hka, hkaa⟩ := exists_Ks_conj_t h49 hd hz h10 h17s hy h17.2.2.2.1 ha
  obtain ⟨kb, hkb, hkbb⟩ := exists_Ks_conj_t h49 hd hz h10 h17s hy h17.2.2.2.1 hb
  refine ⟨kb * ka⁻¹, mul_mem hkb (Subgroup.inv_mem _ hka), ?_⟩
  rw [← hkaa, ← hkbb]
  group

theorem node18_of_surj (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h09 : Node09 d z₀)
    (h10 : Node10 d z₀) (h17s : Node17s d z₀) (h17 : Node17 d z₀)
    (hsurj : ∀ u ∈ Us d, star d d.t * u ∈ DeltaS d) : Node18 d := by
  obtain ⟨y₁, hy⟩ := exists_V1_of_node09 h09
  refine ⟨node18_a h49 hd hz h10 h17s hy, node18_b h49 hd hz h10 h17s h17 hy,
    node18_c h49 hd hz h10 h17s h17 hy, Set.Subset.antisymm (node18_b h49 hd hz h10 h17s h17 hy) ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  exact hsurj u hu

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5
