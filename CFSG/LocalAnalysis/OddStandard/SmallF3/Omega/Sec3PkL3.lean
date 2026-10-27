module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3PkAbs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OddCoreL3U3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Pocket
public import CFSG.ClassicalInvolution.Orders.Classical

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.Open CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Proofs2
  CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog

private theorem det_eq_one_of_central_gl2 :
    ∀ w : GL (Fin 2) (ZMod 3), (∀ g : GL (Fin 2) (ZMod 3), g * w = w * g) → w ^ 2 = 1 →
      Matrix.GeneralLinearGroup.det w = 1 := by
  decide +kernel

theorem nonempty_centralizer_equiv_gl2_of_lieModel_psl33 {Y : Type} [Group Y] [Finite Y]
    (h : LieModel Y .PSL 3 3 1) {z : Y} (hz : orderOf z = 2) :
    Nonempty (↥(centralizer ({z} : Set Y)) ≃* GL (Fin 2) (ZMod 3)) := by
  have hclass : StatedClassicalModel Y .PSL 3 3 1 :=
    LieModel.statedClassicalModel_of_ne_zero (by norm_num) h
  obtain ⟨-, F, hFfield, hFfin, hFcard, ⟨e⟩⟩ := hclass
  have hLn : IsLnEps 3 Y 1 (3 ^ 1) := Or.inl ⟨rfl, F, hFfield, hFfin, hFcard, ⟨e⟩⟩
  obtain ⟨F', hF'field, hF'fin, N, hN, hF'card, hNcard, ⟨e'⟩⟩ :=
    ivk_4_1a_L3 Y 3 1 Nat.prime_three (by norm_num) hLn z hz
  have hF3 : Nat.card F' = 3 := by rw [hF'card]; norm_num
  have hNbot : N = ⊥ := le_bot_iff.mp
    ((oddCore_gl2_eq_bot F' hF3) ▸ le_oddCore_of_normal hN (odd_of_card_one_or_three hNcard))
  exact ⟨(e'.trans ((QuotientGroup.quotientMulEquivOfEq hNbot).trans
    QuotientGroup.quotientBot)).trans (glTwoEquivZMod3 F' hF3).symm⟩

theorem isI4PlusIn_top_of_lieModel_psl33 {Y : Type} [Group Y] [Finite Y]
    (h : LieModel Y .PSL 3 3 1) {z : Y} (hz : orderOf z = 2) :
    IsI4PlusIn (⊤ : Subgroup Y) z := by
  obtain ⟨ψ⟩ := nonempty_centralizer_equiv_gl2_of_lieModel_psl33 h hz
  have hz0 : (⟨z, mem_centralizer_self z⟩ : ↥(centralizer ({z} : Set Y))) ^ 2 = 1 :=
    Subtype.ext (by simpa [hz] using pow_orderOf_eq_one z)
  refine isI4PlusIn_top_of_centralizer_equiv hz ψ
    (Matrix.GeneralLinearGroup.det : GL (Fin 2) (ZMod 3) →* (ZMod 3)ˣ).ker ?_ ?_
  · rw [MonoidHom.mem_ker]
    refine det_eq_one_of_central_gl2 _ (fun g => ?_) (by rw [← map_pow, hz0, map_one])
    obtain ⟨c, rfl⟩ := ψ.surjective g
    rw [← map_mul, ← map_mul]
    exact congrArg ψ (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp c.2))
  · exact isSL23Mod_of_mulEquiv Matrix.SpecialLinearGroup.toGLKerEquiv isSL23Mod_sl2f3

theorem exists_involution_of_lieModel_psl33 {Y : Type} [Group Y] [Finite Y]
    (h : LieModel Y .PSL 3 3 1) : ∃ z : Y, orderOf z = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card Y = 5616 := by
    rw [(CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := Y)
      (show (3 : ℕ) ≠ 2 by norm_num) (h.statedClassicalModel_of_ne_zero (by norm_num))).1 rfl]
    decide +kernel
  exact exists_prime_orderOf_dvd_card' 2 (by rw [hcard]; norm_num)

theorem exists_isI4PlusIn_of_lieModel_psl33 {Y : Type} [Group Y] [Finite Y]
    (h : LieModel Y .PSL 3 3 1) : ∃ q : Y, IsI4PlusIn (⊤ : Subgroup Y) q := by
  obtain ⟨z, hz⟩ := exists_involution_of_lieModel_psl33 h
  exact ⟨z, isI4PlusIn_top_of_lieModel_psl33 h hz⟩

end CFSG.OddStandard.SmallF3.Omega
