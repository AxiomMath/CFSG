module

public import CFSG.GroupTheory.SimpleTrivialOnSmallF2Module
public import CFSG.Open.StatedDefs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.Dimension.Finrank

import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
import CFSG.RankThree.GF2n.Tim79a34SpFacts
import CFSG.RankThree.GF2n.Stroth80.Sec3Zsig
import Mathlib.GroupTheory.OrderOfElement
import CFSG.CGT.Timmesfeld75.Forms
import CFSG.RankThree.GF2n.Stroth80.Anisotropic
import CFSG.RankThree.GF2n.Stroth80.FrobClause
import CFSG.RankThree.GF2n.Stroth80.GlobalModel
import CFSG.RankThree.GF2n.Stroth80.Sec36
import CFSG.RankThree.GF2n.SupIndepDecomp
import CFSG.RankThree.GF2n.Tim79CentC
import CFSG.RankThree.GF2n.Tim79CentL
import CFSG.RankThree.GF2n.Tim79Mod

public section

namespace CFSG.ClassicalGroups.Symplectic

open CFSG.Open CFSG.GroupTheory

theorem card_pow_two_mul_sub_one_dvd_card_statedSp (K : Type) [Field K] [Finite K]
    {m : ℕ} (hm : 1 ≤ m) : Nat.card K ^ (2 * m) - 1 ∣ Nat.card (StatedSp m K) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp]
  exact dvd_mul_of_dvd_right
    (Finset.dvd_prod_of_mem (fun j => Nat.card K ^ (2 * j) - 1)
      (Finset.mem_Icc.mpr ⟨hm, le_rfl⟩)) _

theorem three_pow_four_dvd_card_statedSp_three_zmod_two :
    3 ^ 4 ∣ Nat.card (StatedSp 3 (ZMod 2)) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, Nat.card_zmod]
  decide

theorem ker_sup_ker_eq_top_of_statedSp_of_finrank_lt
    {Y : Type*} [Group Y] [Finite Y] {m : ℕ} (hm : 3 ≤ m)
    (π : Y →* StatedSp m (ZMod 2)) (hπ : Function.Surjective π)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Y →* (V ≃ₗ[ZMod 2] V)) (hdim : Module.finrank (ZMod 2) V < 2 * m) :
    ρ.ker ⊔ π.ker = ⊤ := by
  have : IsSimpleGroup (StatedSp m (ZMod 2)) :=
    CFSG.RankThree.GF2n.Tim79a.isSimpleGroup_statedSp_of_card_two hm (Nat.card_zmod 2)
  rcases eq_or_lt_of_le hm with rfl | hm4
  ·
    exact ker_sup_ker_eq_top_of_dvd_card_of_not_dvd π hπ ρ
      three_pow_four_dvd_card_statedSp_three_zmod_two
      (not_three_pow_four_dvd_card_linearEquiv_of_finrank_le_five (by omega))
  ·
    obtain ⟨p, hp, _, hord⟩ :=
      CFSG.RankThree.GF2n.Stroth80.exists_prime_orderOf_two_eq (e := 2 * m) (by omega) (by omega)
    have : Fact p.Prime := ⟨hp⟩
    have hp2m : p ∣ 2 ^ (2 * m) - 1 := by
      have hpow : (2 : ZMod p) ^ (2 * m) = 1 := by
        rw [← hord]
        exact pow_orderOf_eq_one (2 : ZMod p)
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_two_pow)]
      push_cast
      exact sub_eq_zero.mpr hpow
    have hdvd := card_pow_two_mul_sub_one_dvd_card_statedSp (K := ZMod 2) (m := m) (by omega)
    rw [Nat.card_zmod] at hdvd
    exact ker_sup_ker_eq_top_of_dvd_card_of_not_dvd π hπ ρ (hp2m.trans hdvd)
      (not_prime_dvd_card_linearEquiv_of_finrank_lt hp (by rw [hord]; exact hdim))

theorem eq_one_of_statedSp_of_finrank_lt {m : ℕ} (hm : 3 ≤ m)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : StatedSp m (ZMod 2) →* (V ≃ₗ[ZMod 2] V))
    (hdim : Module.finrank (ZMod 2) V < 2 * m) : ρ = 1 := by
  have htop := ker_sup_ker_eq_top_of_statedSp_of_finrank_lt hm (MonoidHom.id _)
    Function.surjective_id ρ hdim
  rw [MonoidHom.ker_id] at htop
  exact (MonoidHom.ker_eq_top_iff (f := ρ)).mp (by simpa using htop)

end CFSG.ClassicalGroups.Symplectic
