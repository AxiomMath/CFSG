module

public import Mathlib.GroupTheory.PGroup
import CFSG.FeitThompson.Foundations.CentralExtensionNilpotent
import CFSG.FeitThompson.Local.NormalSubgroupCentralPrimeTorsion

open Subgroup QuotientGroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {p a n : ℕ} {P : Type*} [Group P]

theorem exists_normal_le_natCard_eq_pow_succ (hp : p.Prime) (hP : Nat.card P = p ^ a)
    (N : Subgroup P) [N.Normal] (hN : Nat.card N = p ^ n)
    {d : ℕ} (R : Subgroup P) [R.Normal] (hRN : R ≤ N) (hR : Nat.card R = p ^ d) (hdn : d < n) :
    ∃ R' : Subgroup P, R ≤ R' ∧ R' ≤ N ∧ R'.Normal ∧ Nat.card R' = p ^ (d + 1) := by
  have : Fact p.Prime := ⟨hp⟩
  have hfin : Finite P := Nat.finite_of_card_ne_zero (by rw [hP]; exact pow_ne_zero _ hp.pos.ne')
  set f := QuotientGroup.mk' R with hf
  have hfsurj : Function.Surjective f := QuotientGroup.mk'_surjective R
  set L := N.map f with hL
  have : L.Normal := Subgroup.Normal.map (inferInstance : N.Normal) f hfsurj
  obtain ⟨m, hm⟩ := ((IsPGroup.of_card hP).to_quotient R).exists_card_eq
  have hLne : L ≠ ⊥ := by
    intro h
    rw [hL, Subgroup.map_eq_bot_iff, hf, QuotientGroup.ker_mk'] at h
    have hRNeq : R = N := le_antisymm hRN h
    rw [hRNeq, hN] at hR
    exact absurd (Nat.pow_right_injective hp.two_le hR) (by omega)
  obtain ⟨S, hSle, hScard⟩ := exists_le_inf_center_natCard_eq L hp hm hLne
  refine ⟨S.comap f, ?_, ?_, ?_, ?_⟩
  · have h := MonoidHom.ker_le_comap f S
    rwa [hf, QuotientGroup.ker_mk'] at h
  · have h2 : S.comap f ≤ L.comap f := Subgroup.comap_mono (le_trans hSle inf_le_left)
    rwa [hL, Subgroup.comap_map_eq_self (by rw [hf, QuotientGroup.ker_mk']; exact hRN)] at h2
  · exact (normal_of_le_center (le_trans hSle inf_le_right)).comap f
  ·
    have hidx : (S.comap f).index = S.index := Subgroup.index_comap_of_surjective S hfsurj
    have h1 : (S.comap f).index * Nat.card (S.comap f) = Nat.card P := Subgroup.index_mul_card _
    have h2 : S.index * Nat.card S = Nat.card (P ⧸ R) := Subgroup.index_mul_card _
    have h3 : R.index * Nat.card R = Nat.card P := Subgroup.index_mul_card R
    have h4 : R.index = Nat.card (P ⧸ R) := Subgroup.index_eq_card R
    have key : S.index * Nat.card (S.comap f) = S.index * p ^ (d + 1) :=
      calc S.index * Nat.card (S.comap f) = (S.comap f).index * Nat.card (S.comap f) := by
            rw [hidx]
        _ = Nat.card P := h1
        _ = R.index * Nat.card R := h3.symm
        _ = Nat.card (P ⧸ R) * p ^ d := by rw [h4, hR]
        _ = S.index * Nat.card S * p ^ d := by rw [h2]
        _ = S.index * p ^ (d + 1) := by rw [hScard]; ring
    exact Nat.eq_of_mul_eq_mul_left
      (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) key

theorem exists_normal_le_natCard_eq_pow (hp : p.Prime) (hP : Nat.card P = p ^ a)
    (N : Subgroup P) [N.Normal] (hN : Nat.card N = p ^ n) {d : ℕ} (hd : d ≤ n) :
    ∃ R : Subgroup P, R ≤ N ∧ R.Normal ∧ Nat.card R = p ^ d := by
  induction d with
  | zero => exact ⟨⊥, bot_le, inferInstance, by simp⟩
  | succ d ih =>
    obtain ⟨R, hRN, hRnorm, hRcard⟩ := ih (Nat.le_of_succ_le hd)
    have := hRnorm
    obtain ⟨R', -, h1, h2, h3⟩ := exists_normal_le_natCard_eq_pow_succ hp hP N hN R hRN hRcard hd
    exact ⟨R', h1, h2, h3⟩

theorem exists_normal_le_natCard_eq_pow_of_dvd (hp : p.Prime) (hP : Nat.card P = p ^ a)
    (N : Subgroup P) [N.Normal] (hN : Nat.card N = p ^ n) {d : ℕ} (hd : p ^ d ∣ Nat.card N) :
    ∃ R : Subgroup P, R ≤ N ∧ R.Normal ∧ Nat.card R = p ^ d :=
  exists_normal_le_natCard_eq_pow hp hP N hN
    ((Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp (hN ▸ hd))

theorem exists_normal_le_natCard_eq_pow_of_isPGroup [Finite P] (hp : p.Prime)
    (hP : IsPGroup p P) (N : Subgroup P) [N.Normal] {d : ℕ} (hd : p ^ d ∣ Nat.card N) :
    ∃ R : Subgroup P, R ≤ N ∧ R.Normal ∧ Nat.card R = p ^ d := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := hP.exists_card_eq
  obtain ⟨n, hn⟩ := (hP.to_subgroup N).exists_card_eq
  exact exists_normal_le_natCard_eq_pow_of_dvd hp ha N hn hd

theorem exists_normal_le_natCard_eq (hp : p.Prime) (hP : Nat.card P = p ^ a)
    (N : Subgroup P) [N.Normal] (hN : N ≠ ⊥) :
    ∃ R : Subgroup P, R ≤ N ∧ R.Normal ∧ Nat.card R = p := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite P := Nat.finite_of_card_ne_zero (by rw [hP]; exact pow_ne_zero _ hp.pos.ne')
  obtain ⟨n, hn, hcard⟩ :=
    (IsPGroup.nontrivial_iff_card ((IsPGroup.of_card hP).to_subgroup N)).mp
      ((Subgroup.nontrivial_iff_ne_bot N).mpr hN)
  obtain ⟨R, h1, h2, h3⟩ := exists_normal_le_natCard_eq_pow hp hP N hcard (d := 1) hn
  exact ⟨R, h1, h2, by simpa using h3⟩

end

end CFSG.FeitThompson
