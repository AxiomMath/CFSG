module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3Base
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3S14Gen

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open Subgroup CFSG.Open CFSG.Sporadic.Schreier.Tits

section S14A

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


theorem card_le_of_le_centralizer_conj (hd : d.Hyp) {g s : G} (hg : g * d.t * g⁻¹ = s) {E : Subgroup G}
    (hE : E ≤ centralizer ({s} : Set G)) (hEa : IsElemAbelian 2 E) : Nat.card E ≤ 2 ^ 6 := by
  have hX : E.map (MulAut.conj g⁻¹).toMonoidHom ≤ centralizer ({d.t} : Set G) := by
    intro y hy
    rw [mem_map_conj_iff', inv_inv] at hy
    have h1 := mem_centralizer_singleton_iff.1 (hE hy)
    rw [mem_centralizer_singleton_iff]
    rw [← hg] at h1
    have h2 : g * (y * d.t * g⁻¹) = g * (d.t * y * g⁻¹) := by
      calc g * (y * d.t * g⁻¹) = (g * y * g⁻¹) * (g * d.t * g⁻¹) := by group
        _ = (g * d.t * g⁻¹) * (g * y * g⁻¹) := h1
        _ = g * (d.t * y * g⁻¹) := by group
    have h3 := mul_left_cancel h2
    exact mul_right_cancel h3
  have := hd.card_le_of_isElemAbelian hX (isElemAbelian_map_conj hEa _)
  rwa [card_map_conj'] at this

theorem sixFive_D (hd : d.Hyp) (h10 : Node10 d z₀) {g s : G} (hg : g * d.t * g⁻¹ = s)
    (hsH : s ∈ Hg d) :
    IsElemAbelian 2 (zpowers s ⊔ (d.s56V ⊓ centralizer ({s} : Set G)) : Subgroup G) ∧
      zpowers s ⊔ (d.s56V ⊓ centralizer ({s} : Set G)) ≤ centralizer ({s} : Set G) ∧
      Nat.card (zpowers s ⊔ (d.s56V ⊓ centralizer ({s} : Set G)) : Subgroup G) = 2 ^ 6 ∧
      d.s56V ≤ normalizer ((zpowers s ⊔ (d.s56V ⊓ centralizer ({s} : Set G)) : Subgroup G) :
        Set G) := by
  have ht2 := hd.t_mul_self
  have hs2 : s * s = 1 := by
    rw [← hg]
    calc g * d.t * g⁻¹ * (g * d.t * g⁻¹) = g * (d.t * d.t) * g⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  have hcomm : ∀ a ∈ d.s56V, ∀ b ∈ d.s56V, a * b = b * a := fun a ha b hb => h10.comm_V ha hb
  have hsq : ∀ a ∈ d.s56V, a * a = 1 := fun a ha => h10.sq_V ha
  set C : Subgroup G := d.s56V ⊓ centralizer ({s} : Set G) with hC
  have hC5 : 2 ^ 5 ≤ Nat.card C :=
    two_pow_five_le_card_inf_centralizer hcomm hsq h10.card_V hsH hs2
  have hCV : C ≤ d.s56V := inf_le_left
  have hCc : ∀ p ∈ C, p * s = s * p := fun p hp => mem_centralizer_singleton_iff.1 hp.2
  have hCcomm : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a := fun a ha b hb => hcomm a (hCV ha) b (hCV hb)
  have hCsq : ∀ a ∈ C, a * a = 1 := fun a ha => hsq a (hCV ha)
  have hsV : s ∉ d.s56V := by
    intro hsV
    have hV_le : d.s56V ≤ centralizer ({s} : Set G) := fun v hv =>
      mem_centralizer_singleton_iff.2 (hcomm v hv s hsV)
    have := card_le_of_le_centralizer_conj hd hg hV_le h10.isElemAbelian_V
    rw [h10.card_V] at this
    norm_num at this
  have hsC : s ∉ C := fun h => hsV (hCV h)
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hg
    apply hd.t_ne_one
    calc d.t = g⁻¹ * (g * d.t * g⁻¹) * g := by group
      _ = 1 := by rw [hg]; group
  have hz2 : Nat.card (zpowers s) = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hs2) hs1]
  have hbot : C ⊓ zpowers s = ⊥ := by
    refine eq_bot_iff.2 fun a ha => ?_
    obtain ⟨haC, haS⟩ := ha
    rcases eq_one_or_of_mem_zpowers hs2 haS with h | h
    · rw [h]; exact one_mem _
    · exact absurd (h ▸ haC) hsC
  have hsCent : s ∈ centralizer (C : Set G) :=
    mem_centralizer_iff.2 fun h hh => hCc h hh
  have hzN : zpowers s ≤ normalizer (C : Set G) :=
    zpowers_le.2 (Subgroup.centralizer_le_normalizer _ hsCent)
  have hcard : Nat.card (C ⊔ zpowers s : Subgroup G) = Nat.card C * 2 := by
    rw [card_sup_of_inf_eq_bot' hzN hbot, hz2]
  have hDeq : (zpowers s ⊔ C : Subgroup G) = C ⊔ zpowers s := sup_comm _ _
  have hDc : zpowers s ⊔ C ≤ centralizer ({s} : Set G) :=
    sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl)) fun p hp => hp.2
  obtain ⟨hDcomm, hDsq⟩ := Data.sup_zpowers_elemAbelian hs2 hCc hCcomm hCsq
  have hDa : IsElemAbelian 2 (zpowers s ⊔ C : Subgroup G) := by
    rw [hDeq]
    exact isElemAbelian_of_comm_sq hDcomm hDsq
  have hle := card_le_of_le_centralizer_conj hd hg hDc hDa
  have hD64 : Nat.card (zpowers s ⊔ C : Subgroup G) = 2 ^ 6 := by
    rw [hDeq] at hle ⊢
    rw [hcard] at hle ⊢
    omega
  exact ⟨hDa, hDc, hD64, le_normalizer_sup_inf_centralizer hcomm hsq hsH hs2⟩

theorem map_conj_inv_le_normalizer {V Y D : Subgroup G} {k : G}
    (hVD : V ≤ normalizer (D : Set G)) (hDY : D = Y.map (MulAut.conj k).toMonoidHom) :
    V.map (MulAut.conj k⁻¹).toMonoidHom ≤ normalizer (Y : Set G) := by
  intro y hy
  rw [mem_map_conj_iff', inv_inv] at hy
  have h := hVD hy
  rw [hDY, mem_normalizer_map_conj_iff] at h
  rwa [show k⁻¹ * (k * y * k⁻¹) * k = y by group] at h

theorem six_five (hd : d.Hyp) (h10 : Node10 d z₀) (h12 : Node12 d z₀) (h13 : Node13 d)
    {s : G} (hs : s ∈ d.tG) (hsH : s ∈ Hg d) :
    (InAH d s ∧ StarConj d s) ∨
      (IsElemAbelian 2 (P1 d) ∧ Nat.card (P1 d) = 2 ^ 10 ∧ ∃ k : G, k * d.t * k⁻¹ = s ∧
        zpowers s ⊔ (d.s56V ⊓ centralizer ({s} : Set G)) = d.B.map (MulAut.conj k).toMonoidHom ∧
        d.s56V = (P1 d).map (MulAut.conj k).toMonoidHom) := by
  obtain ⟨-, -, -, -, -, hMmax⟩ := h12
  obtain ⟨-, hNcases⟩ := h13
  obtain ⟨g, hg⟩ := hs
  obtain ⟨hDa, hDc, hD64, hVD⟩ := sixFive_D hd h10 hg hsH
  set D := zpowers s ⊔ (d.s56V ⊓ centralizer ({s} : Set G)) with hD
  have hX : D.map (MulAut.conj g⁻¹).toMonoidHom ≤ centralizer ({d.t} : Set G) := by
    intro y hy
    rw [mem_map_conj_iff', inv_inv] at hy
    have h1 := mem_centralizer_singleton_iff.1 (hDc hy)
    rw [mem_centralizer_singleton_iff]
    rw [← hg] at h1
    have h2 : g * (y * d.t * g⁻¹) = g * (d.t * y * g⁻¹) := by
      calc g * (y * d.t * g⁻¹) = (g * y * g⁻¹) * (g * d.t * g⁻¹) := by group
        _ = (g * d.t * g⁻¹) * (g * y * g⁻¹) := h1
        _ = g * (d.t * y * g⁻¹) := by group
    exact mul_right_cancel (mul_left_cancel h2)
  have hXa := isElemAbelian_map_conj hDa g⁻¹
  have hX64 : Nat.card (D.map (MulAut.conj g⁻¹).toMonoidHom) = 2 ^ 6 := by
    rw [card_map_conj', hD64]
  obtain ⟨c, hc, hcAB⟩ := hd.exists_map_conj_eq_A_or_B hX hXa hX64
  set k := g * c⁻¹ with hk
  have hct : c * d.t = d.t * c := mem_centralizer_singleton_iff.1 hc
  have hkt' : k * d.t * k⁻¹ = s := by
    have h1 : c⁻¹ * d.t * c = d.t := by
      calc c⁻¹ * d.t * c = c⁻¹ * (d.t * c) := by group
        _ = c⁻¹ * (c * d.t) := by rw [hct]
        _ = d.t := by group
    calc k * d.t * k⁻¹ = g * (c⁻¹ * d.t * c) * g⁻¹ := by rw [hk]; group
      _ = s := by rw [h1, hg]
  have hDk : ∀ Y : Subgroup G, (D.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj c).toMonoidHom = Y →
      D = Y.map (MulAut.conj k).toMonoidHom := by
    intro Y h
    have e : k * c * g⁻¹ = 1 := by rw [hk]; group
    rw [← h, map_conj_map_conj', map_conj_map_conj', e, map_conj_one']
  have hV10 : Nat.card d.s56V = 2 ^ 10 := h10.card_V
  have hV'a : IsElemAbelian 2 (d.s56V.map (MulAut.conj k⁻¹).toMonoidHom) :=
    isElemAbelian_map_conj h10.isElemAbelian_V _
  have hV'card : Nat.card (d.s56V.map (MulAut.conj k⁻¹).toMonoidHom) = 2 ^ 10 := by
    rw [card_map_conj', hV10]
  have hVmax : d.s56V ∈ maxElemAbelian2 d.M := by
    rw [hMmax]; exact Set.mem_singleton _
  have hV'back : ∀ y, y ∈ d.s56V.map (MulAut.conj k⁻¹).toMonoidHom ↔ k * y * k⁻¹ ∈ d.s56V := by
    intro y
    rw [mem_map_conj_iff', inv_inv]
  rcases hcAB with hA | hB
  ·
    have hDA := hDk _ hA
    have hVN := map_conj_inv_le_normalizer hVD hDA
    have hV'M : d.s56V.map (MulAut.conj k⁻¹).toMonoidHom ≤ d.M := hVN
    have hmem := mem_maxElemAbelian2_of_card_eq hVmax hV'M hV'a (by rw [hV'card, hV10])
    rw [hMmax, Set.mem_singleton_iff] at hmem
    have hkH : k ∈ Hg d := by
      rw [mem_Hg_iff, mem_normalizer_iff]
      intro y
      rw [← hV'back, hmem]
    left
    exact ⟨⟨k, hkH, hDA⟩, k, hkH, by rw [hkt']⟩
  ·
    have hDB := hDk _ hB
    have hVN := map_conj_inv_le_normalizer hVD hDB
    have hV'N : d.s56V.map (MulAut.conj k⁻¹).toMonoidHom ≤ d.N := hVN
    have hrank : 10 ≤ CFSG.Open.pRank 2 d.N := le_pRank_of_isElemAbelian hV'N hV'a hV'card
    rcases hNcases with hlt | ⟨hP1a, hP1c, hP1max⟩
    · exact absurd hrank (not_le.2 hlt)
    · have hP1mem : P1 d ∈ maxElemAbelian2 d.N := by
        rw [hP1max]; exact Set.mem_singleton _
      have hmem := mem_maxElemAbelian2_of_card_eq hP1mem hV'N hV'a (by rw [hV'card, hP1c])
      rw [hP1max, Set.mem_singleton_iff] at hmem
      right
      refine ⟨hP1a, hP1c, k, hkt', hDB, ?_⟩
      rw [← hmem, map_conj_map_conj', mul_inv_cancel, map_conj_one']

end S14A

end CFSG.LocalAnalysis.EvenBN.Tits.N
