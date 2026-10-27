module

import CFSG.Goldschmidt.Steps.Sec8LemmaA
import CFSG.Goldschmidt.Steps.Sec8Basic
import CFSG.Goldschmidt.Steps.Sec8Tools
import CFSG.Walter.Bender1970.S4.Rank
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ComponentLayerCentralizesSolvableNormalized
public import CFSG.Goldschmidt.StatementsG2

public section

namespace CFSG.Goldschmidt.Sec8

open CFSG.Open

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A : Subgroup G}

theorem inf_normalizer_eq (hset : GoldSetting G S A) (h4 : Nat.card A = 4) {a : G} (ha : a ∈ A)
    (ha1 : a ≠ 1) {H : Subgroup G} (hHtop : H ≠ ⊤)
    (hCH : Subgroup.centralizer ({a} : Set G) ≤ H) :
    H ⊓ Subgroup.normalizer (A : Set G) = Subgroup.centralizer (A : Set G) := by
  have hCA : Subgroup.centralizer (A : Set G) ≤ H :=
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha)).trans hCH
  refine le_antisymm (fun x hx => ?_) (le_inf hCA (Subgroup.centralizer_le_normalizer _))
  by_contra hxc
  exact false_of_normalizer_le hset h4 hHtop ha ha1 hCH (normalizer_le hset h4 hCA hx.1 hx.2 hxc)

theorem eq_oddCoreOf_sup (hset : GoldSetting G S A) (h4 : Nat.card A = 4) {a : G} (ha : a ∈ A)
    (ha1 : a ≠ 1) {H : Subgroup G} (hH : H ∈ Walter.benderM a) :
    normalClosureIn H A = oddCoreOf (normalClosureIn H A) ⊔ A ∧
      H = oddCoreOf H ⊔ Subgroup.centralizer (A : Set G) := by
  have hHtop := Walter.ne_top_of_mem_benderM hH
  have hCH := Walter.centralizer_le_of_mem_benderM hH
  obtain ⟨hQ, hHQ⟩ := GLemmaA G S A hset h4 H hHtop (le_of_mem_benderM hset h4 ha hH)
    (inf_normalizer_eq hset h4 ha ha1 hHtop hCH)
  refine ⟨hQ, le_antisymm ?_ (sup_le (oddCoreOf_le H) ?_)⟩
  · refine hHQ.le.trans (sup_le_sup_right ?_ _)
    exact le_oddCoreOf ((oddCoreOf_le _).trans (normalClosureIn_le_self H A))
      (le_normalizer_oddCoreOf_of_le_normalizer (le_normalizer_normalClosureIn H A))
      (odd_card_oddCoreOf _)
  · exact (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha)).trans hCH

omit [Finite G] in
theorem mem_centralizer_of_conj_mem {n y : G} (hn : n ∈ Subgroup.normalizer (A : Set G))
    (hy : n⁻¹ * y * n ∈ Subgroup.centralizer (A : Set G)) :
    y ∈ Subgroup.centralizer (A : Set G) := by
  refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
  have hx' : n⁻¹ * x * n ∈ A := by simpa using conj_mem (Subgroup.inv_mem _ hn) hx
  have h := Subgroup.mem_centralizer_iff.mp hy _ hx'
  calc x * y = n * ((n⁻¹ * x * n) * (n⁻¹ * y * n)) * n⁻¹ := by group
    _ = n * ((n⁻¹ * y * n) * (n⁻¹ * x * n)) * n⁻¹ := by rw [h]
    _ = y * x := by group

theorem commutator_ne_bot (hset : GoldSetting G S A) (h4 : Nat.card A = 4) {a : G} (ha : a ∈ A)
    (ha1 : a ≠ 1) {H : Subgroup G} (hH : H ∈ Walter.benderM a) : ⁅A, oddCoreOf H⁆ ≠ ⊥ := by
  intro hcomm
  have hCH := Walter.centralizer_le_of_mem_benderM hH
  have hOC : oddCoreOf H ≤ Subgroup.centralizer (A : Set G) :=
    Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm)
  have hHC : H ≤ Subgroup.centralizer (A : Set G) :=
    (eq_oddCoreOf_sup hset h4 ha ha1 hH).2.le.trans (sup_le hOC le_rfl)
  have hCAH : Subgroup.centralizer (A : Set G) ≤ H :=
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha)).trans hCH
  refine false_of_centralizer_le hset (Walter.ne_top_of_mem_benderM hH) fun b hb hb1 => ?_
  obtain ⟨n, hn, rfl⟩ := exists_conj_eq hset h4 ha hb ha1 hb1
  intro y hy
  have h1 : n⁻¹ * y * n ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    calc n⁻¹ * y * n * a = n⁻¹ * (y * (n * a * n⁻¹)) * n := by group
      _ = n⁻¹ * ((n * a * n⁻¹) * y) * n := by rw [hy]
      _ = a * (n⁻¹ * y * n) := by group
  exact hCAH (mem_centralizer_of_conj_mem hn (hHC (hCH h1)))

theorem mem_qCoreOf_two_and_eq (h64 : S_G64) (hset : GoldSetting G S A) (h4 : Nat.card A = 4)
    {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) {H : Subgroup G} (hH : H ∈ Walter.benderM a) :
    a ∈ GorensteinWalter.qCoreOf H 2 ∧ H = Subgroup.centralizer ({a} : Set G) := by
  obtain ⟨hQ, hHO⟩ := eq_oddCoreOf_sup hset h4 ha ha1 hH
  have hCH := Walter.centralizer_le_of_mem_benderM hH
  have hQsolv := isSolvable_of_eq_oddCoreOf_sup hset.elem.1 hQ
  have hEQ := GorensteinWalter.componentLayerOf_centralizes_solvable_of_le_normalizer H _
    (normalClosureIn_le_self H A) hQsolv
    ((GorensteinWalter.componentLayerOf_isNormalIn H).1.trans (le_normalizer_normalClosureIn H A))
  have haE : a ∈ Subgroup.centralizer (GorensteinWalter.componentLayerOf H : Set G) :=
    Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hEQ)
      (le_normalClosureIn (hset.le.trans (le_of_mem_benderM hset h4 ha hH)) ha)
  have haF : a ∈ CFSG.fittingSubgroupOf H :=
    Walter.generalizedFittingSubgroupOf_inf_centralizer_le H
      ⟨(h64 G S A hset a ha ha1 H hH).1, haE⟩
  have hza : IsPGroup 2 (Subgroup.zpowers a) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, orderOf_eq_prime (hset.elem.2 a ha) ha1, pow_one])
  have ha2 : a ∈ GorensteinWalter.qCoreOf H 2 :=
    Walter.le_qCoreOf_of_le_fittingSubgroupOf Nat.prime_two (Subgroup.zpowers_le.mpr haF) hza
      (Subgroup.mem_zpowers a)
  refine ⟨ha2, le_antisymm (hHO.le.trans (sup_le (fun y hy => ?_)
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha)))) hCH⟩
  have hyH : y ∈ H := oddCoreOf_le H hy
  have hc2 : y * a * y⁻¹ * a⁻¹ ∈ GorensteinWalter.qCoreOf H 2 :=
    Subgroup.mul_mem _ ((GorensteinWalter.qCoreOf_normal_in H 2).2 y hyH a ha2)
      (Subgroup.inv_mem _ ha2)
  have haH : a ∈ H := hCH (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hcO : y * a * y⁻¹ * a⁻¹ ∈ oddCoreOf H := by
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_oddCoreOf H haH) y⁻¹).mp
      (Subgroup.inv_mem _ hy)
    simpa [mul_assoc] using Subgroup.mul_mem _ hy this
  obtain ⟨k, hk⟩ := GorensteinWalter.qCoreOf_isPGroup H 2 ⟨_, hc2⟩
  have h1 := eq_one_of_pow_two_of_odd (odd_card_oddCoreOf H) hcO
    (k := k) (by simpa using congrArg Subtype.val hk)
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc y * a = y * a * y⁻¹ * a⁻¹ * (a * y) := by group
    _ = a * y := by rw [h1, one_mul]

end CFSG.Goldschmidt.Sec8
