module

import CFSG.Adapters.Involutions
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerOddAvg
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Open.GoldschmidtStronglyClosedAbelianMilestoneDefs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Commutator.FocalSubgroup

public section

namespace CFSG.Goldschmidt

open CFSG.Open
open scoped commutatorElement

theorem N7 :
    ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G), IsMulCommutative (S : Subgroup G) →
      ∃ H : Subgroup G, H ≤ Subgroup.normalizer ((S : Subgroup G) : Set G) ∧ Odd (Nat.card H) ∧
        (S : Subgroup G) ⊔ H = Subgroup.normalizer ((S : Subgroup G) : Set G) ∧
        (S : Subgroup G) ⊓ commutator G = ⁅(S : Subgroup G), H⁆ ∧
        ((S : Subgroup G) ⊓ Subgroup.centralizer (H : Set G)) ⊓ ⁅(S : Subgroup G), H⁆ = ⊥ ∧
        ((S : Subgroup G) ⊓ Subgroup.centralizer (H : Set G)) ⊔ ⁅(S : Subgroup G), H⁆ = S ∧
        (goldschmidtOddCore G = ⊥ → ∀ c ∈ (S : Subgroup G) ⊓ Subgroup.centralizer (H : Set G),
          c ^ 2 = 1 → c ∈ Subgroup.center G) := by
  intro G _ _ S hSab
  set N := Subgroup.normalizer ((S : Subgroup G) : Set G) with hNdef
  have hSN : (S : Subgroup G) ≤ N := Subgroup.le_normalizer
  set S' : Subgroup N := (S : Subgroup G).subgroupOf N with hS'def
  have hS'n : S'.Normal := Subgroup.normal_in_normalizer
  have hS'card : Nat.card S' = Nat.card (S : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSN).toEquiv
  have hS'idx : ¬ 2 ∣ S'.index := fun h =>
    S.not_dvd_index (h.trans (Subgroup.relIndex_dvd_index_of_le hSN))
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp S.isPGroup'
  have hcop : (Nat.card S').Coprime S'.index := by
    rw [hS'card, hk]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hS'idx)
  obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  set H : Subgroup G := K.map N.subtype with hHdef
  have hHN : H ≤ N := Subgroup.map_subtype_le K
  have hHcard : Nat.card H = S'.index := by
    rw [hHdef, Subgroup.card_map_of_injective N.subtype_injective]
    exact hK.symm.index_eq_card.symm
  have hHodd : Odd (Nat.card H) := by
    rw [hHcard]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hS'idx)
  have hdecomp : ∀ n ∈ N, ∃ s ∈ (S : Subgroup G), ∃ h ∈ H, s * h = n := by
    intro n hn
    obtain ⟨⟨s, h⟩, hsh⟩ := (hK.existsUnique ⟨n, hn⟩).exists
    exact ⟨s, Subgroup.mem_subgroupOf.mp s.2, h, ⟨h, h.2, rfl⟩, congrArg Subtype.val hsh⟩
  have hsup : (S : Subgroup G) ⊔ H = N := by
    refine le_antisymm (sup_le hSN hHN) fun n hn => ?_
    obtain ⟨s, hs, h, hh, rfl⟩ := hdecomp n hn
    exact Subgroup.mul_mem_sup hs hh
  have hfus : ∀ x ∈ (S : Subgroup G), ∀ g : G, g⁻¹ * x * g ∈ (S : Subgroup G) →
      ∃ h ∈ H, g⁻¹ * x * g = h⁻¹ * x * h := by
    intro x hx g hg
    have := hSab
    obtain ⟨n, hn, hgn⟩ := Sylow.conj_eq_normalizer_conj_of_mem S x g hx hg
    obtain ⟨s, hs, h, hh, rfl⟩ := hdecomp n hn
    refine ⟨h, hh, ?_⟩
    have hxs : x * s = s * x := congrArg Subtype.val (hSab.is_comm.comm ⟨x, hx⟩ ⟨s, hs⟩)
    rw [hgn]
    calc (s * h)⁻¹ * x * (s * h) = h⁻¹ * (s⁻¹ * (x * s)) * h := by group
      _ = h⁻¹ * x * h := by rw [hxs, inv_mul_cancel_left]
  have hfocal : (S : Subgroup G) ⊓ commutator G = ⁅(S : Subgroup G), H⁆ := by
    refine le_antisymm ?_ (le_inf (Subgroup.le_normalizer_iff_commutator_le_left.mp hHN) ?_)
    · have h := CFSG.sylow_inf_derivedSubgroup_eq_focalSubgroup 2 S
      rw [CFSG.derivedSubgroup, derivedSeries_one] at h
      rw [h, Subgroup.closure_le]
      rintro z ⟨x, hx, y, hy, hxy, rfl⟩
      obtain ⟨c, hc⟩ := isConj_iff.mp hxy
      have hy' : c⁻¹⁻¹ * x * c⁻¹ = y := by rw [inv_inv]; exact hc
      obtain ⟨h, hh, hxh⟩ := hfus x hx c⁻¹ (by rw [hy']; exact hy)
      rw [← hy', hxh]
      have he : x⁻¹ * (h⁻¹ * x * h) = ⁅x⁻¹, h⁻¹⁆ := by
        rw [commutatorElement_def, inv_inv, inv_inv]
        group
      rw [he]
      exact Subgroup.commutator_mem_commutator ((S : Subgroup G).inv_mem hx) (H.inv_mem hh)
    · rw [_root_.commutator_def]
      exact Subgroup.commutator_mono le_top le_top
  have hSab' : ∀ x y : (S : Subgroup G), x * y = y * x := fun x y => hSab.is_comm.comm x y
  have hcopHS : Nat.Coprime (Nat.card H) (Nat.card (S : Subgroup G)) := by
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hHodd)
  obtain ⟨hdsup, hddisj⟩ :=
    CFSG.QuasithinUnique.Setup.Layer.coprime_abelian_decomp (S : Subgroup G) H hHN hSab' hcopHS
  refine ⟨H, hHN, hHodd, hsup, hfocal, disjoint_iff.mp hddisj, hdsup, ?_⟩
  intro hO c hc hc2
  by_cases hc1 : c = 1
  · rw [hc1]
    exact Subgroup.one_mem _
  have hcS : c ∈ (S : Subgroup G) := hc.1
  have hcH : c ∈ Subgroup.centralizer (H : Set G) := hc.2
  have hcc : c * c = 1 := by rw [← sq]; exact hc2
  have hwc : ∀ g : G, g⁻¹ * c * g ∈ (S : Subgroup G) → g⁻¹ * c * g = c := by
    intro g hg
    obtain ⟨h, hh, hgh⟩ := hfus c hcS g hg
    have hhc : h * c = c * h := Subgroup.mem_centralizer_iff.mp hcH h hh
    rw [hgh, mul_assoc, ← hhc, inv_mul_cancel_left]
  have hcZ : c ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact congrArg Subtype.val (hSab.is_comm.comm ⟨s, hs⟩ ⟨c, hcS⟩)
  let _ : Fintype G := Fintype.ofFinite G
  obtain ⟨Z, hZn, hZodd, hZ⟩ := CFSG.ZStar.glauberman_zStar G c hc1 hcc
    (fun g hcomm => CFSG.Adapters.isolated_of_weakClosure S hcZ hcc hwc g hcomm)
  have hZbot : Z ≤ goldschmidtOddCore G := le_sSup ⟨hZn, hZodd⟩
  rw [hO] at hZbot
  rw [Subgroup.mem_center_iff]
  intro g
  have h1 : g * c * g⁻¹ * c⁻¹ = 1 := (Subgroup.mem_bot).mp (hZbot (hZ g))
  calc g * c = (g * c * g⁻¹ * c⁻¹) * c * g := by group
    _ = c * g := by rw [h1, one_mul]

end CFSG.Goldschmidt
