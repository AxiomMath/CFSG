module

import CFSG.LocalAnalysis.ComponentClassification.AS81QbarAbstract
import CFSG.ClassicalInvolution.RouteD.GapsPerfect
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenCore
import CFSG.RankThree.PartOne.S13K.N135Lin
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Quasithin.Background.B1MoreQuot
public import CFSG.Quasithin.Background.B1Restrict
public import CFSG.Quasithin.Background.D2Coprime

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin

variable {W : Type} [CommGroup W]

private theorem eq_of_card_lt_two_mul_fpl [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {F G : Subgroup W} (hFG : F ≤ G) (h : Nat.card ↥G < 2 * Nat.card ↥F) : G = F := by
  have hF : Nat.card ↥F = 2 ^ rk ↥F := card_eq_two_pow hW F
  have hG : Nat.card ↥G = 2 ^ rk ↥G := card_eq_two_pow hW G
  have hle : rk ↥F ≤ rk ↥G := rk_mono hFG
  have h2 : 2 * 2 ^ rk ↥F = 2 ^ (rk ↥F + 1) := by
    rw [pow_succ, mul_comm]
  rw [hF, hG, h2] at h
  have hlt : rk ↥G < rk ↥F + 1 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp h
  have hrk : rk ↥G = rk ↥F := by omega
  exact (Subgroup.eq_of_le_of_card_ge hFG (by rw [hG, hF, hrk])).symm

private theorem four_le_or_card_eq_two_mul_fpl [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {F X : Subgroup W} (hFX : F ≤ X) (hne : F ≠ X) :
    4 * Nat.card ↥F ≤ Nat.card ↥X ∨ Nat.card ↥X = 2 * Nat.card ↥F := by
  have hF : Nat.card ↥F = 2 ^ rk ↥F := card_eq_two_pow hW F
  have hX : Nat.card ↥X = 2 ^ rk ↥X := card_eq_two_pow hW X
  have hle : rk ↥F ≤ rk ↥X := rk_mono hFX
  have hlt : rk ↥F < rk ↥X := by
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exact absurd (eq_of_le_of_rk_le hW hFX (by omega)) hne
  by_cases h2 : rk ↥F + 2 ≤ rk ↥X
  · left
    rw [hF, hX]
    have hp : 4 * 2 ^ rk ↥F = 2 ^ (rk ↥F + 2) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add, Nat.add_comm]
    rw [hp]
    exact Nat.pow_le_pow_right (by norm_num : 0 < 2) h2
  · right
    push Not at h2
    rw [hF, hX]
    have hr : rk ↥X = rk ↥F + 1 := by omega
    rw [hr, pow_succ]
    ring

private theorem card_sup_le_four_of_card_two_fpl [Finite W]
    {T₁ T₂ : Subgroup W} (h₁ : Nat.card ↥T₁ = 2) (h₂ : Nat.card ↥T₂ = 2) :
    Nat.card ↥(T₁ ⊔ T₂) ≤ 4 := by
  have h := card_sup_mul_card_inf T₁ T₂
  rw [h₁, h₂] at h
  have hpos : 0 < Nat.card ↥(T₁ ⊓ T₂) := Nat.card_pos
  have hle : Nat.card ↥(T₁ ⊔ T₂) * Nat.card ↥(T₁ ⊓ T₂) ≤
      4 * Nat.card ↥(T₁ ⊓ T₂) := by
    rw [h]
    simpa using Nat.mul_le_mul_left 4 hpos
  exact Nat.le_of_mul_le_mul_right hle hpos

private theorem card_map_commHom_eq_two_fpl [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {A : Subgroup (MulAut W)} {X : Subgroup W} {a : MulAut W} (ha : a ∈ A)
    (hX2 : Nat.card ↥X = 2 * Nat.card ↥(X ⊓ fixV A))
    (hne : X ⊓ fixV (Subgroup.zpowers a) ≠ X) :
    Nat.card ↥(X.map (commHom a)) = 2 := by
  have hFle : X ⊓ fixV A ≤ X ⊓ fixV (Subgroup.zpowers a) :=
    inf_le_inf_left X (B1.fixV_le_fixV (Subgroup.zpowers_le.mpr ha))
  have hGX : X ⊓ fixV (Subgroup.zpowers a) ≤ X := inf_le_left
  have hlt : Nat.card ↥(X ⊓ fixV (Subgroup.zpowers a)) < Nat.card ↥X :=
    Subgroup.card_lt_of_lt (lt_of_le_of_ne hGX hne)
  have hGeq : X ⊓ fixV (Subgroup.zpowers a) = X ⊓ fixV A :=
    eq_of_card_lt_two_mul_fpl hW hFle (by rw [← hX2]; exact hlt)
  have hcard := B1More.card_map_mul_card_inf_ker X (commHom a)
  rw [ker_commHom, hGeq] at hcard
  rw [hX2] at hcard
  exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos) hcard

private theorem false_of_commutes_map_commHom_fpl [Finite W]
    {C : Subgroup (MulAut W)} {X : Subgroup W} {a : MulAut W}
    (hCX : C ≤ stabSub X) (haX : a ∈ stabSub X)
    (hcomm : ∀ c ∈ C, a * c = c * a)
    (hT2 : Nat.card ↥(X.map (commHom a)) = 2)
    (hXC : X ⊓ fixV C = ⊥) : False := by
  have hTX : X.map (commHom a) ≤ X := by
    intro t ht
    obtain ⟨x, hx, rfl⟩ := ht
    exact X.mul_mem ((mem_stabSub.mp haX x).2 hx) (X.inv_mem hx)
  have hmap : ∀ c ∈ C, ∀ t ∈ X.map (commHom a), c t ∈ X.map (commHom a) := by
    rintro c hc t ⟨x, hx, rfl⟩
    refine ⟨c x, (mem_stabSub.mp (hCX hc) x).2 hx, ?_⟩
    have hca : c (a x) = a (c x) :=
      (congrArg (fun g : MulAut W => g x) (hcomm c hc)).symm
    rw [commHom_apply, commHom_apply, map_mul, map_inv, hca]
  have hfix : X.map (commHom a) ≤ fixV C := fun t ht => mem_fixV.mpr fun c hc =>
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.s15_Core_map_eq_self_of_card_le_two _ c hT2.le
      (hmap c hc) t ht
  have hbot : X.map (commHom a) ≤ ⊥ := by
    rw [← hXC]
    exact le_inf hTX hfix
  have hTbot : X.map (commHom a) = ⊥ := le_bot_iff.mp hbot
  rw [hTbot, Subgroup.card_bot] at hT2
  omega

private theorem map_commHom_conj_fpl {X : Subgroup W} {c a : MulAut W}
    (hc : c ∈ stabSub X) :
    X.map (commHom (c * a * c⁻¹)) =
      (X.map (commHom a)).map (c : MulAut W).toMonoidHom := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : c⁻¹ x ∈ X := (mem_stabSub.mp (Subgroup.inv_mem _ hc) x).2 hx
    refine ⟨commHom a (c⁻¹ x), ⟨c⁻¹ x, hx', rfl⟩, ?_⟩
    simp [commHom_apply, MulAut.mul_apply]
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨c x, (mem_stabSub.mp hc x).2 hx, ?_⟩
    simp [commHom_apply, MulAut.mul_apply]

private theorem card_map_commHom_conj_fpl {X : Subgroup W} {c a : MulAut W}
    (hc : c ∈ stabSub X) :
    Nat.card ↥(X.map (commHom (c * a * c⁻¹))) = Nat.card ↥(X.map (commHom a)) := by
  rw [map_commHom_conj_fpl hc]
  exact Subgroup.card_map_of_injective (f := (c : MulAut W).toMonoidHom) c.injective

private theorem le_stabSub_map_commHom_of_centralizes_fpl
    {L C : Subgroup (MulAut W)} (hCZ : C ≤ Subgroup.centralizer (L : Set (MulAut W)))
    {X : Subgroup W} (hLX : L ≤ stabSub X) {c' : MulAut W} (hc' : c' ∈ C) :
    L ≤ stabSub (X.map (commHom c')) := by
  refine B1.le_stabSub_of_invariant ?_
  rintro l hl t ⟨x, hx, rfl⟩
  refine ⟨l x, (mem_stabSub.mp (hLX hl) x).2 hx, ?_⟩
  have hlc : l * c' = c' * l := hCZ hc' l hl
  have h1 : l (c' x) = c' (l x) := by
    rw [← MulAut.mul_apply, hlc, MulAut.mul_apply]
  rw [commHom_apply, commHom_apply, map_mul, map_inv, h1]

private theorem le_fixV_of_perfect_of_card_le_four_fpl [Finite W]
    {L : Subgroup (MulAut W)} (hL : Group.IsPerfect ↥L) {T : Subgroup W}
    (hLT : L ≤ stabSub T) (hcard : Nat.card ↥T ≤ 4) : T ≤ fixV L := by
  let φ : ↥L →* MulAut ↥T := (resHom T).comp (Subgroup.inclusion hLT)
  have hperf : Group.IsPerfect ↥L := hL
  have hsolv : Group.IsSolvable (MulAut ↥T) :=
    CFSG.ComponentClassification.AS81.Qbar.isSolvable_mulAut_of_card_le_four hcard
  have hφ : φ = 1 :=
    @CFSG.ClassicalInvolution.RouteD.Gaps.hom_eq_one_of_perfect_of_solvable
      ↥L (MulAut ↥T) _ _ hsolv hperf φ
  intro t ht
  rw [mem_fixV]
  intro l hl
  have h1 : φ ⟨l, hl⟩ ⟨t, ht⟩ = ⟨t, ht⟩ := by rw [hφ]; rfl
  have h2 := congrArg (fun u : ↥T => (u : W)) h1
  simpa [φ, resHom_apply, Subgroup.inclusion] using h2

private theorem false_of_card_map_commHom_le_four_fpl [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {L C : Subgroup (MulAut W)} (hL : Group.IsPerfect ↥L) (hCL : C ≤ L)
    (hCZ : C ≤ Subgroup.centralizer (L : Set (MulAut W))) (hodd : Odd (Nat.card C))
    {X : Subgroup W} (hLX : L ≤ stabSub X) {c' : MulAut W} (hc' : c' ∈ C) (hc'1 : c' ≠ 1)
    (hcard : Nat.card ↥(X.map (commHom c')) ≤ 4)
    (hCX : C ⊓ centSec X ⊥ = ⊥) : False := by
  have hc'X : c' ∈ stabSub X := hLX (hCL hc')
  have hLT : L ≤ stabSub (X.map (commHom c')) :=
    le_stabSub_map_commHom_of_centralizes_fpl hCZ hLX hc'
  have hTfix : X.map (commHom c') ≤ fixV L :=
    le_fixV_of_perfect_of_card_le_four_fpl hL hLT hcard
  have hsq : ∀ x ∈ X, (c' * c') x = x := by
    intro x hx
    have hm : commHom c' x ∈ X.map (commHom c') := ⟨x, hx, rfl⟩
    have hfix := (mem_fixV.mp (hTfix hm)) c' (hCL hc')
    rw [commHom_apply, map_mul, map_inv] at hfix
    have h1 : c' (c' x) = c' x * x⁻¹ * c' x := by
      have := congrArg (fun y => y * c' x) hfix
      simpa [mul_assoc] using this
    have h2 : c' x * x⁻¹ * c' x = x := by
      calc c' x * x⁻¹ * c' x = c' x * (x⁻¹ * c' x) := mul_assoc _ _ _
        _ = c' x * (c' x * x⁻¹) := by rw [mul_comm (x⁻¹) (c' x)]
        _ = (c' x * c' x) * x⁻¹ := (mul_assoc _ _ _).symm
        _ = 1 * x⁻¹ := by
            rw [show c' x * c' x = 1 from by simpa [pow_two] using hW (c' x)]
        _ = x⁻¹ := one_mul _
        _ = x := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hW x)
    rw [MulAut.mul_apply, h1, h2]
  have hodd' : Odd (orderOf c') := hodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard C hc')
  have htriv : ∀ x ∈ X, c' x = x := fun x hx =>
    CFSG.RankThree.PartOne.S13K.N135.apply_eq_of_sq hodd' (hsq x hx)
  have hcent : c' ∈ centSec X ⊥ := by
    rw [mem_centSec]
    refine ⟨hc'X, fun x hx => ?_⟩
    rw [htriv x hx]
    simp
  have hmem : c' ∈ C ⊓ centSec X ⊥ := ⟨hc', hcent⟩
  rw [hCX, Subgroup.mem_bot] at hmem
  exact hc'1 hmem

private theorem false_of_noncommutes_fpl [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {L C A : Subgroup (MulAut W)} (hL : Group.IsPerfect ↥L) (hCL : C ≤ L)
    (hCZ : C ≤ Subgroup.centralizer (L : Set (MulAut W))) (hodd : Odd (Nat.card C))
    (hAC : A ≤ Subgroup.normalizer (C : Set (MulAut W))) (hAe : IsElemAbelian2 A)
    {X : Subgroup W} (hLX : L ≤ stabSub X)
    (hCX : C ⊓ centSec X ⊥ = ⊥)
    {a : MulAut W} (haA : a ∈ A) (haX : a ∈ stabSub X)
    (hT2 : Nat.card ↥(X.map (commHom a)) = 2)
    {c : MulAut W} (hcC : c ∈ C) (hnc : a * c ≠ c * a) : False := by
  have ha2 : a * a = 1 := by simpa [pow_two] using hAe.2 a haA
  have hcX : c ∈ stabSub X := hLX (hCL hcC)
  set b : MulAut W := c * a * c⁻¹ with hb
  set c' : MulAut W := a * b with hc'
  have hbX : b ∈ stabSub X := by
    rw [hb]
    exact (stabSub X).mul_mem ((stabSub X).mul_mem hcX haX) (Subgroup.inv_mem _ hcX)
  have hc'eq : c' = a * c * a⁻¹ * c⁻¹ := by
    rw [hc', hb, show a⁻¹ = a from inv_eq_of_mul_eq_one_right ha2]
    group
  have hc'C : c' ∈ C := by
    rw [hc'eq]
    exact C.mul_mem (((Subgroup.mem_normalizer_iff.mp (hAC haA)) c).mp hcC) (C.inv_mem hcC)
  have hc'1 : c' ≠ 1 := by
    rw [hc'eq]
    intro h
    exact hnc (by
      calc a * c = (a * c * a⁻¹) * a := by group
        _ = c * a := by rw [mul_inv_eq_one.mp h])
  have hTb2 : Nat.card ↥(X.map (commHom b)) = 2 := by
    rw [hb, card_map_commHom_conj_fpl hcX, hT2]
  have hle : X.map (commHom c') ≤ X.map (commHom a) ⊔ X.map (commHom b) := by
    rintro y ⟨x, hx, rfl⟩
    have hident : commHom c' x = commHom a (b x) * commHom b x := by
      rw [hc', commHom_apply, commHom_apply, commHom_apply, MulAut.mul_apply]
      group
    rw [hident]
    exact Subgroup.mul_mem_sup
      (Subgroup.mem_map_of_mem _ ((mem_stabSub.mp hbX x).2 hx))
      (Subgroup.mem_map_of_mem _ hx)
  have hcard : Nat.card ↥(X.map (commHom c')) ≤ 4 :=
    (Subgroup.card_le_of_le hle).trans (card_sup_le_four_of_card_two_fpl hT2 hTb2)
  exact false_of_card_map_commHom_le_four_fpl hW hL hCL hCZ hodd hLX hc'C hc'1 hcard hCX

private theorem false_of_card_eq_two_mul_fixV_fpl [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {L C A : Subgroup (MulAut W)} (hL : Group.IsPerfect ↥L) (hCL : C ≤ L)
    (hCZ : C ≤ Subgroup.centralizer (L : Set (MulAut W))) (hodd : Odd (Nat.card C))
    (hAC : A ≤ Subgroup.normalizer (C : Set (MulAut W))) (hAe : IsElemAbelian2 A)
    {X : Subgroup W} (hLX : L ≤ stabSub X) (hAX : A ≤ stabSub X) (hXC : X ⊓ fixV C = ⊥)
    (hCX : C ⊓ centSec X ⊥ = ⊥) (hXA : ¬ X ≤ fixV A)
    (hX2 : Nat.card ↥X = 2 * Nat.card ↥(X ⊓ fixV A)) : False := by
  obtain ⟨x₀, hx₀X, hx₀A⟩ := SetLike.not_le_iff_exists.mp hXA
  have hx₀A' : ¬ ∀ a ∈ A, a x₀ = x₀ := fun h => hx₀A (mem_fixV.mpr h)
  push Not at hx₀A'
  obtain ⟨a, haA, hax₀⟩ := hx₀A'
  have haX : a ∈ stabSub X := hAX haA
  have hneG : X ⊓ fixV (Subgroup.zpowers a) ≠ X := by
    intro heq
    have hmem : x₀ ∈ X ⊓ fixV (Subgroup.zpowers a) := heq.symm ▸ hx₀X
    have hfix : x₀ ∈ fixV (Subgroup.zpowers a) := (Subgroup.mem_inf.mp hmem).2
    exact hax₀ ((mem_fixV.mp hfix) a (Subgroup.mem_zpowers a))
  have hT2 : Nat.card ↥(X.map (commHom a)) = 2 :=
    card_map_commHom_eq_two_fpl hW haA hX2 hneG
  have hCstab : C ≤ stabSub X := hCL.trans hLX
  by_cases hcomm : ∀ c ∈ C, a * c = c * a
  · exact false_of_commutes_map_commHom_fpl hCstab haX hcomm hT2 hXC
  · push Not at hcomm
    obtain ⟨c, hcC, hnc⟩ := hcomm
    exact false_of_noncommutes_fpl hW hL hCL hCZ hodd hAC hAe hLX hCX haA haX hT2 hcC hnc

theorem four_mul_card_inf_fixV_le [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {L C A : Subgroup (MulAut W)} (hL : Group.IsPerfect ↥L) (hCL : C ≤ L)
    (hCZ : C ≤ Subgroup.centralizer (L : Set (MulAut W))) (hodd : Odd (Nat.card C))
    (hAC : A ≤ Subgroup.normalizer (C : Set (MulAut W))) (hAe : IsElemAbelian2 A)
    {X : Subgroup W} (hLX : L ≤ stabSub X) (hAX : A ≤ stabSub X) (hXC : X ⊓ fixV C = ⊥)
    (hCX : C ⊓ centSec X ⊥ = ⊥) (hXA : ¬ X ≤ fixV A) :
    4 * Nat.card ↥(X ⊓ fixV A) ≤ Nat.card X := by
  classical
  by_cases hbig : 4 * Nat.card ↥(X ⊓ fixV A) ≤ Nat.card X
  · exact hbig
  · exfalso
    have hFX : X ⊓ fixV A ≤ X := inf_le_left
    have hne : X ⊓ fixV A ≠ X := fun h => hXA (h ▸ inf_le_right)
    rcases four_le_or_card_eq_two_mul_fpl hW hFX hne with h4 | h2
    · exact hbig h4
    · exact false_of_card_eq_two_mul_fixV_fpl hW hL hCL hCZ hodd hAC hAe hLX hAX hXC hCX hXA h2

end CFSG.GroupTheory

