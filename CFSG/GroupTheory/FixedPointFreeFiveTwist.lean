module

public import CFSG.Quasithin.Background.D2Basic
public import CFSG.Quasithin.Background.FixVZPowersMem
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3ThCount
public import CFSG.Quasithin.Recognition.Kleidman.F204.W2FFOrder
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin

theorem two_mul_rk_fixV_le_of_not_commute {W : Type*} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {f φ : MulAut W} {q : ℕ} (hq : q.Prime) (hfq : orderOf f = q)
    (hfix : fixV (Subgroup.zpowers f) = ⊥) (hnorm : φ * f * φ⁻¹ ∈ Subgroup.zpowers f)
    (hne : φ * f ≠ f * φ) : 2 * rk ↥(fixV (Subgroup.zpowers φ)) ≤ rk W := by
  set C : Subgroup W := fixV (Subgroup.zpowers φ) with hCdef
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hnorm
  have hfk_ne_f : f ^ k ≠ f := by
    intro h
    apply hne
    have hg : φ * f * φ⁻¹ = f := by rw [← hk, h]
    calc φ * f = (φ * f * φ⁻¹) * φ := by group
      _ = f * φ := by rw [hg]
  have hinf : C ⊓ C.map f.toMonoidHom = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    rw [Subgroup.mem_bot]
    obtain ⟨huC, huMap⟩ := Subgroup.mem_inf.mp hu
    rw [Subgroup.mem_map] at huMap
    obtain ⟨v, hvC, hvu⟩ := huMap
    change f v = u at hvu
    have hφu : φ u = u := (mem_fixV.mp huC) φ (Subgroup.mem_zpowers φ)
    have hφv : φ v = v := (mem_fixV.mp hvC) φ (Subgroup.mem_zpowers φ)
    have hφinv : (φ⁻¹ : MulAut W) v = v := by
      apply φ.injective
      simpa using hφv.symm
    have hfk : (f ^ k) v = f v := by
      rw [hk]
      calc (φ * f * φ⁻¹) v = φ (f ((φ⁻¹) v)) := by simp [MulAut.mul_apply]
        _ = φ (f v) := by rw [hφinv]
        _ = φ u := by rw [hvu]
        _ = u := hφu
        _ = f v := hvu.symm
    have hmul : f * f ^ (k - 1) = f ^ k := by
      rw [mul_self_zpow]
      congr 1
      ring
    have hcancel : f ((f ^ (k - 1)) v) = f v := by
      have h := congrArg (fun g : MulAut W => g v) hmul
      rw [hfk] at h
      simpa [MulAut.mul_apply] using h
    have hstep : (f ^ (k - 1)) v = v := f.injective hcancel
    have hne1 : f ^ (k - 1) ≠ 1 := by
      intro h
      apply hfk_ne_f
      calc f ^ k = f ^ (k - 1 + 1) := by
            congr 1
            ring
        _ = f ^ (k - 1) * f := (mul_zpow_self f (k - 1)).symm
        _ = f := by rw [h, one_mul]
    have hmemgen : f ^ (k - 1) ∈ Subgroup.zpowers f :=
      zpow_mem (Subgroup.mem_zpowers f) (k - 1)
    have hHcard : Nat.card ↥(Subgroup.zpowers f) = q := by
      rw [Nat.card_zpowers, hfq]
    have htop : Subgroup.zpowers (⟨f ^ (k - 1), hmemgen⟩ : ↥(Subgroup.zpowers f)) = ⊤ :=
      zpowers_eq_top_of_prime_card (p := q) (hp := ⟨hq⟩) hHcard (by simpa using hne1)
    have hgen : Subgroup.zpowers (f ^ (k - 1)) = Subgroup.zpowers f := by
      refine le_antisymm (Subgroup.zpowers_le.mpr hmemgen) ?_
      intro x hx
      have hx' : (⟨x, hx⟩ : ↥(Subgroup.zpowers f)) ∈
          Subgroup.zpowers (⟨f ^ (k - 1), hmemgen⟩ : ↥(Subgroup.zpowers f)) := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx'
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, by simpa using congrArg Subtype.val hn⟩
    have hv : v ∈ fixV (Subgroup.zpowers (f ^ (k - 1))) :=
      mem_fixV_zpowers_iff_apply.mpr hstep
    rw [hgen, hfix] at hv
    have hv1 : v = 1 := Subgroup.mem_bot.mp hv
    rw [← hvu, hv1, map_one]
  have hcard := card_sup_mul_card_inf C (C.map f.toMonoidHom)
  rw [hinf, Subgroup.card_bot] at hcard
  have hmap : Nat.card ↥(C.map f.toMonoidHom) = Nat.card C :=
    Subgroup.card_map_of_injective f.injective
  rw [hmap, mul_one] at hcard
  have hle : Nat.card ↥(C ⊔ C.map f.toMonoidHom) ≤ Nat.card W :=
    Nat.card_le_card_of_injective (fun x => (x : W)) Subtype.val_injective
  rw [hcard] at hle
  have hCcard : Nat.card C = 2 ^ rk C := card_eq_two_pow hW C
  have hWcard : Nat.card W = 2 ^ rk W := by
    simpa [rk_top] using card_eq_two_pow hW (⊤ : Subgroup W)
  rw [hCcard, hWcard, ← pow_two, ← pow_mul] at hle
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
  omega

theorem commute_of_rkIdx_fixV_le {W : Type*} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {f φ : MulAut W} {q : ℕ} (hq : q.Prime) (hfq : orderOf f = q)
    (hfix : fixV (Subgroup.zpowers f) = ⊥) (hnorm : φ * f * φ⁻¹ ∈ Subgroup.zpowers f)
    {N : ℕ} (hN : 2 * N < rk W) (hd : rkIdx (fixV (Subgroup.zpowers φ)) ≤ N) :
    φ * f = f * φ := by
  by_contra hne
  have h := two_mul_rk_fixV_le_of_not_commute hW hq hfq hfix hnorm hne
  have hsum := rk_add_rkIdx (fixV (Subgroup.zpowers φ))
  omega

theorem four_dvd_rk_of_invariant {W : Type*} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {f : MulAut W} (hf5 : f ^ 5 = 1) (hfix : fixV (Subgroup.zpowers f) = ⊥) {U : Subgroup W}
    (hU : ∀ u ∈ U, f u ∈ U) : 4 ∣ rk ↥U := by
  have hfpf : ∀ u ∈ U, f u = u → u = 1 := by
    intro u hu hfu
    have hmem : u ∈ fixV (Subgroup.zpowers f) := mem_fixV_zpowers_iff_apply.mpr hfu
    rw [hfix] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hmod := CFSG.LocalAnalysis.EvenBN.Tits.N.card_mod_five_of_fpf f hf5 U hU hfpf
  rw [card_eq_two_pow hW U] at hmod
  exact CFSG.Quasithin.Kleidman.F204.four_dvd_of_two_pow_mod_five (rk ↥U) hmod

end CFSG.GroupTheory
