module

public import CFSG.FeitThompson.Definitions.UniqueMaximalOvergroup
public import CFSG.FeitThompson.Definitions.RawNormalPrimeSetCore
import CFSG.FeitThompson.Local.PrimeFittingNormalSelfCentralizingAbelian
import CFSG.FeitThompson.Local.PComplementControlSylowNormalizer
import CFSG.FeitThompson.Local.MaximalIntersectionSylowNormalizerControl
import CFSG.FeitThompson.Local.TrivialComplementaryCoreMaximalSylow
public import Mathlib.GroupTheory.Solvable

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {M A : Subgroup G}

private theorem dvd_natCard_of_isPGroup {H : Subgroup G} (hp : p.Prime) (hAp : IsPGroup p ↥A)
    (hAbot : A ≠ ⊥) (hAH : A ≤ H) : p ∣ Nat.card ↥H := by
  have := Fact.mk hp
  obtain ⟨n, hn⟩ := hAp.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hAbot (Subgroup.card_eq_one.1 (by simpa using hn))
  exact dvd_trans (hn ▸ dvd_pow_self p hn0) (Subgroup.card_dvd_of_le hAH)

theorem pComplCore_eq_bot_of_control {H : Subgroup G} (hp : p.Prime) (hAH : A ≤ H)
    (hcontrol : ∀ Y : Subgroup G, p.Coprime (Nat.card ↥Y) → A ≤ normalizer (Y : Set G) → Y = ⊥) :
    pComplCore p ↥H = ⊥ :=
  (pComplCoreIn_eq_bot_iff p H).1
    (hcontrol _ (hp.coprime_iff_not_dvd.2 (not_dvd_natCard_pComplCoreIn hp H))
      (hAH.trans (le_normalizer_pComplCoreIn p H)))

theorem isUniqueMaximalOvergroup_of_control [IsSimpleGroup G]
    (hp : p.Prime) (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable ↥K)
    (hM : IsCoatom M) (hA : ⊥ < A) (hAp : IsPGroup p ↥A) (hAM : A ≤ M)
    (hcontrol : ∀ Y : Subgroup G, p.Coprime (Nat.card ↥Y) → A ≤ normalizer (Y : Set G) → Y = ⊥) :
    IsUniqueMaximalOvergroup A M := by
  refine ⟨hM, hAM, ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨N₀, hN₀, hAN₀, hN₀M⟩ := hcon
  have : Nonempty {H : Subgroup G // IsCoatom H ∧ A ≤ H ∧ H ≠ M} := ⟨⟨N₀, hN₀, hAN₀, hN₀M⟩⟩
  obtain ⟨⟨H, hH, hAH, hHM⟩, hmax⟩ := Finite.exists_max
    (fun x : {H : Subgroup G // IsCoatom H ∧ A ≤ H ∧ H ≠ M} =>
      (Nat.card ((x : Subgroup G) ⊓ M : Subgroup G)).factorization p)
  obtain ⟨R, hAR, hRHM, hRcard⟩ :=
    exists_le_natCard_eq_pow_factorization hp (le_inf hAH hAM) hAp
  obtain ⟨S, hRS, hSM, hScard⟩ := exists_le_natCard_eq_pow_factorization hp
    (hRHM.trans inf_le_right) (IsPGroup.of_card hRcard)
  have hNS : normalizer (S : Set G) ≤ M :=
    normalizer_le_of_control_of_coprime hna hodd hsolv hM hp hSM hScard hA (hAR.trans hRS)
      (fun K hK hAK => by rw [hcontrol K hK hAK]; exact bot_le)
  have hmax' : ∀ D : Subgroup G, IsCoatom D → D ≠ M → A ≤ D →
      p ^ (Nat.card (D ⊓ M : Subgroup G)).factorization p ≤
        p ^ (Nat.card (H ⊓ M : Subgroup G)).factorization p :=
    fun D hD hDM hAD => Nat.pow_le_pow_right hp.one_lt.le (hmax ⟨D, hD, hAD, hDM⟩)
  have hNR : normalizer (R : Set G) ≤ M :=
    normalizer_le_of_maximal_inf hp hM hA hmax' hAR hRcard hRS hSM hScard hNS
  have hRH : Nat.card ↥R = p ^ (Nat.card ↥H).factorization p :=
    natCard_eq_pow_factorization_of_inf_of_normalizer_le (M := M) hp (hRHM.trans inf_le_left)
      hRcard hNR
  have hpH : p ∣ Nat.card ↥H := dvd_natCard_of_isPGroup hp hAp hA.ne' hAH
  have hpM : p ∣ Nat.card ↥M := dvd_natCard_of_isPGroup hp hAp hA.ne' hAM
  have hH' : pComplCore p ↥H = ⊥ := pComplCore_eq_bot_of_control hp hAH hcontrol
  have hM' : pComplCore p ↥M = ⊥ := pComplCore_eq_bot_of_control hp hAM hcontrol
  obtain ⟨-, hRG⟩ := normalizer_le_and_natCard_eq_of_trivial_pComplCore hp hna hodd hsolv
    hH hpH (hRHM.trans inf_le_left) hRH hH'
  have hRM : Nat.card ↥R = p ^ (Nat.card ↥M).factorization p := by
    have h1 : (Nat.card G).factorization p ≤ (Nat.card ↥M).factorization p :=
      (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').1
        (hRG ▸ Subgroup.card_dvd_of_le (hRHM.trans inf_le_right))
    have h2 : (Nat.card ↥M).factorization p ≤ (Nat.card G).factorization p :=
      (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').1
        ((Nat.ordProj_dvd _ p).trans M.card_subgroup_dvd_card)
    rw [hRG, le_antisymm h1 h2]
  have h1 : normalizer (((puigCenter ↥R).map R.subtype : Subgroup G) : Set G) = H :=
    normalizer_eq_of_trivial_pComplCore hp hodd hsolv hH hpH (hRHM.trans inf_le_left) hRH hH'
  have h2 : normalizer (((puigCenter ↥R).map R.subtype : Subgroup G) : Set G) = M :=
    normalizer_eq_of_trivial_pComplCore hp hodd hsolv hM hpM (hRHM.trans inf_le_right) hRM hM'
  exact hHM (h1.symm.trans h2)

theorem isUniqueMaximalOvergroup_of_control_natCard [IsSimpleGroup G]
    (hp : p.Prime) (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable ↥K)
    (hM : IsCoatom M) {n : ℕ} (hn : n ≠ 0) (hAcard : Nat.card ↥A = p ^ n) (hAM : A ≤ M)
    (hcontrol : ∀ Y : Subgroup G, p.Coprime (Nat.card ↥Y) → A ≤ normalizer (Y : Set G) → Y = ⊥) :
    IsUniqueMaximalOvergroup A M := by
  refine isUniqueMaximalOvergroup_of_control hp hna hodd hsolv hM ?_ (IsPGroup.of_card hAcard)
    hAM hcontrol
  refine bot_lt_iff_ne_bot.2 fun h => ?_
  rw [h, Nat.card_eq_one_iff_unique.2 ⟨inferInstance, inferInstance⟩] at hAcard
  exact absurd hAcard.symm (Nat.one_lt_pow hn hp.one_lt).ne'

theorem eq_of_isCoatom_of_control [IsSimpleGroup G]
    (hp : p.Prime) (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable ↥K)
    (hM : IsCoatom M) (hA : ⊥ < A) (hAp : IsPGroup p ↥A) (hAM : A ≤ M)
    (hcontrol : ∀ Y : Subgroup G, p.Coprime (Nat.card ↥Y) → A ≤ normalizer (Y : Set G) → Y = ⊥)
    {N : Subgroup G} (hN : IsCoatom N) (hAN : A ≤ N) : N = M :=
  (isUniqueMaximalOvergroup_of_control hp hna hodd hsolv hM hA hAp hAM hcontrol).eq_of_isCoatom
    hN hAN

end CFSG.FeitThompson

end
