module

public import CFSG.GH74.GLS.Stage2.Signalizer.Defs
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Gen2

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L52Two

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

section NoFin

variable {G : Type} [Group G]

theorem exists_mul_pow_eq {N : Subgroup G} {l t : G} (hl : l ∈ N)
    (ht : t ∈ normalizer (N : Set G)) (j : ℕ) : ∃ n ∈ N, (l * t) ^ j = n * t ^ j := by
  induction j with
  | zero => exact ⟨1, N.one_mem, by simp⟩
  | succ j ih =>
    obtain ⟨n, hn, h⟩ := ih
    have htj : t ^ j ∈ normalizer (N : Set G) := Subgroup.pow_mem _ ht j
    have hc : t ^ j * l * (t ^ j)⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.1 htj l).1 hl
    refine ⟨n * (t ^ j * l * (t ^ j)⁻¹), N.mul_mem hn hc, ?_⟩
    rw [pow_succ, h, pow_succ]
    group

theorem mem_of_odd_orderOf_of_pow_mem {N : Subgroup G} {o : G} (hodd : Odd (orderOf o)) {k : ℕ}
    (h : o ^ (2 ^ k) ∈ N) : o ∈ N := by
  have hcop : IsCoprime ((2 ^ k : ℕ) : ℤ) ((orderOf o : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd))
  obtain ⟨a, b, hab⟩ := hcop
  have e : o = (o ^ (2 ^ k)) ^ a := by
    calc o = o ^ (1 : ℤ) := (zpow_one o).symm
      _ = o ^ (a * ((2 ^ k : ℕ) : ℤ) + b * ((orderOf o : ℕ) : ℤ)) := by rw [hab]
      _ = (o ^ (2 ^ k)) ^ a * (o ^ orderOf o) ^ b := by
          rw [zpow_add, mul_comm a, mul_comm b, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
      _ = (o ^ (2 ^ k)) ^ a := by rw [pow_orderOf_eq_one, one_zpow, mul_one]
  rw [e]
  exact N.zpow_mem h a

theorem exists_pow_mem_of_sup {L T : Subgroup G} (hT2 : IsPGroup 2 ↥T)
    (hTN : T ≤ normalizer (L : Set G)) {x : G} (hx : x ∈ L ⊔ T) : ∃ k : ℕ, x ^ (2 ^ k) ∈ L := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left L T hTN] at hx
  obtain ⟨l, hl, t, ht, rfl⟩ := hx
  obtain ⟨k, hk⟩ := hT2 ⟨t, ht⟩
  have hk' : t ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨n, hn, h⟩ := exists_mul_pow_eq hl (hTN ht) (2 ^ k)
  exact ⟨k, by rw [h, hk', mul_one]; exact hn⟩

theorem le_normalizer_pPrimeCoreOf_two (X : Subgroup G) :
    X ≤ normalizer ((pPrimeCoreOf 2 X : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => TwoThin.pPrimeCoreOf_normalized X hg hh, fun hh => ?_⟩
  have := TwoThin.pPrimeCoreOf_normalized X (Subgroup.inv_mem _ hg) hh
  simpa [mul_assoc] using this

theorem le_pPrimeCoreOf_of_odd_normalized {N X : Subgroup G} (hNX : N ≤ X)
    (hnorm : X ≤ normalizer (N : Set G)) (hcop : Nat.Coprime 2 (Nat.card N)) :
    N ≤ pPrimeCoreOf 2 X := by
  have hnormal : (N.subgroupOf X).Normal := by
    refine ⟨fun a ha h => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (hnorm h.2) a).mp ha
  have hcop' : Nat.Coprime 2 (Nat.card (N.subgroupOf X)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNX).toEquiv]
  have hle : N.subgroupOf X ≤ pPrimeCore 2 X := le_sSup ⟨hnormal, hcop'⟩
  rw [← Subgroup.map_subgroupOf_eq_of_le hNX]
  exact Subgroup.map_mono hle

end NoFin

section Fin

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_pLayerOf (X : Subgroup G) :
    X ≤ normalizer ((pLayerOf 2 X : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    have h1 : (MulAut.conj g).toMonoidHom z ∈ (pLayerOf 2 X).map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hz
    simpa [MulAut.conj_apply] using pLayerOf_map_conj_le hg h1
  · intro hz
    have h1 : (MulAut.conj g⁻¹).toMonoidHom (g * z * g⁻¹) ∈
        (pLayerOf 2 X).map (MulAut.conj g⁻¹).toMonoidHom := Subgroup.mem_map_of_mem _ hz
    have h2 := pLayerOf_map_conj_le (Subgroup.inv_mem _ hg) h1
    simpa [MulAut.conj_apply, mul_assoc] using h2

theorem covering_of_normalizes {L₀ T Tstar A : Subgroup G} (hTstar : Tstar = L₀ ⊔ T)
    (hT2 : IsPGroup 2 ↥T) (hTN : T ≤ normalizer (L₀ : Set G))
    (hcov : Covers A Tstar (pPrimeCoreOf 2 Tstar)) :
    L₀ ≤ (A ⊓ L₀) ⊔ pPrimeCoreOf 2 L₀ := by
  have hL₀T : L₀ ≤ Tstar := hTstar ▸ le_sup_left
  have hTstarN : Tstar ≤ normalizer (L₀ : Set G) :=
    hTstar ▸ sup_le Subgroup.le_normalizer hTN
  have hOodd : Odd (Nat.card ↥(pPrimeCoreOf 2 Tstar)) := TwoThin.card_pPrimeCoreOf_odd Tstar
  have hOL₀ : pPrimeCoreOf 2 Tstar ≤ L₀ := by
    intro o ho
    have hoT : o ∈ L₀ ⊔ T := hTstar ▸ TwoThin.pPrimeCoreOf_le Tstar ho
    obtain ⟨k, hk⟩ := exists_pow_mem_of_sup hT2 hTN hoT
    have hodd : Odd (orderOf o) :=
      Odd.of_dvd_nat hOodd (Subgroup.orderOf_dvd_natCard _ ho)
    exact mem_of_odd_orderOf_of_pow_mem hodd hk
  have hOpL₀ : pPrimeCoreOf 2 Tstar ≤ pPrimeCoreOf 2 L₀ :=
    le_pPrimeCoreOf_of_odd_normalized hOL₀
      (hL₀T.trans (le_normalizer_pPrimeCoreOf_two Tstar)) (Nat.coprime_two_left.2 hOodd)
  intro l hl
  have hl' : l ∈ (A ⊓ Tstar) ⊔ pPrimeCoreOf 2 Tstar := hcov (hL₀T hl)
  have hAN : A ⊓ Tstar ≤ normalizer ((pPrimeCoreOf 2 Tstar : Subgroup G) : Set G) :=
    fun a ha => le_normalizer_pPrimeCoreOf_two Tstar ha.2
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hAN] at hl'
  obtain ⟨a, ha, o, ho, rfl⟩ := hl'
  have haL : a ∈ L₀ := by
    have : a = (a * o) * o⁻¹ := by group
    rw [this]
    exact L₀.mul_mem hl (L₀.inv_mem (hOL₀ ho))
  exact Subgroup.mul_mem_sup (Subgroup.mem_inf.2 ⟨ha.1, haL⟩) (hOpL₀ ho)

theorem covering_L0 {U T Tstar H P : Subgroup G}
    (hTstar : Tstar = pLayerOf 2 (centralizer (U : Set G)) ⊔ T)
    (hT2 : IsPGroup 2 ↥T) (hTC : T ≤ centralizer (U : Set G))
    (hcov : Covers (H ⊓ normalizer (P : Set G)) Tstar (pPrimeCoreOf 2 Tstar)) :
    pLayerOf 2 (centralizer (U : Set G)) ≤
      (H ⊓ pLayerOf 2 (centralizer (U : Set G))) ⊔
        pPrimeCoreOf 2 (pLayerOf 2 (centralizer (U : Set G))) :=
  (covering_of_normalizes hTstar hT2 (hTC.trans (le_normalizer_pLayerOf _)) hcov).trans
    (sup_le_sup_right (inf_le_inf_right _ inf_le_left) _)

end Fin

end CFSG.GH74.GLS.Stage2.Signalizer.L52Two
