module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GXDef
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10PkAbs
public import CFSG.Blueprint.OddStandardExact
public import CFSG.Blueprint.RecognitionDefs
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L310Layer

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

@[expose] def L34GC6 (Y : Type) [Group Y] : Prop :=
  ∀ σ : MulAut Y, σ * σ = 1 → ∀ y u : Y, orderOf y = 2 → orderOf u = 3 → y * u = u * y →
    σ y = y → σ u = u → σ = 1 ∨ σ = MulAut.conj y

theorem l34g_exists_order_three_of_sl23Mod {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y}
    (hK : IsSL23Mod ↥K) : ∃ u ∈ K, orderOf u = 3 := by
  obtain ⟨e⟩ := hK
  have h24 : Nat.card (↥K ⧸ oddCore ↥K) = 24 := by
    rw [Nat.card_congr e.toEquiv]
    exact card_sl23
  have hdvd : Nat.card (↥K ⧸ oddCore ↥K) ∣ Nat.card ↥K := Subgroup.card_quotient_dvd_card _
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : 3 ∣ Nat.card ↥K := (show 3 ∣ 24 by norm_num).trans (h24 ▸ hdvd)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 3 h3
  exact ⟨x, x.2, by rw [← hx]; exact Subgroup.orderOf_coe x⟩

theorem l34g_fix_conj {Y : Type} [Group Y] (b : Y) :
    L34GFix (MulAut.conj b) = centralizer ({b} : Set Y) := by
  ext x
  rw [l34g_mem_fix, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
  constructor
  · intro h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  · intro h
    exact mul_inv_eq_iff_eq_mul.mpr h.symm

end CFSG.OddStandard.SmallF3.Omega
