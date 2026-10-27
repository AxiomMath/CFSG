module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2FoldDef

public section

open CFSG.GH74.BNPair
open scoped Pointwise

namespace CFSG.GH74.GLS.SP

variable {X : Type*} [Group X]

theorem rest_conjBy_inf_foldFix {φ : X ≃* X} {m : X} (hm : φ m = m) (A : Subgroup X) :
    conjBy m⁻¹ (A ⊓ foldFix φ) = conjBy m⁻¹ A ⊓ foldFix φ := by
  ext x
  rw [Subgroup.mem_inf, mem_conjBy_iff, mem_conjBy_iff, Subgroup.mem_inf, mem_foldFix,
    mem_foldFix]
  refine and_congr_right fun _ => ?_
  simp only [map_mul, map_inv, hm]
  constructor
  · intro h
    exact mul_left_cancel (mul_right_cancel h)
  · intro h
    rw [h]

theorem rest_conjBy_root_of_actsPos {n : ℕ} {root : ℤ → Subgroup X} {m : X} {f : ℤ → ℤ}
    (hm : ActsPos n root m f) (hm' : ActsPos n root m⁻¹ f) (hff : ∀ q, f (f q) = q) (q : ℤ) :
    conjBy m⁻¹ (root (Rt n q)) = root (Rt n (f q)) := by
  ext x
  rw [mem_conjBy_iff]
  constructor
  · intro hx
    have := hm q _ hx
    have e : m * (m⁻¹ * x * m⁻¹⁻¹) * m⁻¹ = x := by group
    rwa [e] at this
  · intro hx
    have := hm' (f q) x hx
    rw [hff] at this
    exact this

theorem rest_conjBy_root {n : ℕ} {root : ℤ → Subgroup X} {m : X} {f : ℤ → ℤ}
    (hm : ActsPos n root m f) (hm' : ActsPos n root m⁻¹ f) (hff : ∀ q, f (f q) = q) {p a b : ℤ}
    (ha : Rt n p = a) (hb : Rt n (f p) = b) : conjBy m⁻¹ (root a) = root b := by
  subst ha hb
  exact rest_conjBy_root_of_actsPos hm hm' hff p

theorem rest_weyl_pow {G : Type*} [Group G] {s t : G} (ht : t * t = 1) (hst : (s * t) ^ 6 = 1) :
    (s * (t * s * t⁻¹)) ^ 3 = 1 := by
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have h : s * (t * s * t⁻¹) = (s * t) ^ 2 := by
    rw [ht', sq]
    group
  rw [h, ← pow_mul]
  exact hst

section Hexagon

variable {H : Subgroup X} {r₁ r₂ : X} {U : Subgroup X} {root : ℤ → Subgroup X}

theorem rest_r₁_mem_N (R : RGD2 6 H r₁ r₂ U root) {r₁' : X} (h1H : r₁⁻¹ * r₁' ∈ H) :
    r₁' ∈ R.N := by
  have := R.N.mul_mem R.r₁_mem_N (R.H_le_N h1H)
  rwa [mul_inv_cancel_left] at this

theorem rest_r₂_mem_N (R : RGD2 6 H r₁ r₂ U root) {r₂' : X}
    (h2H : (r₂ * r₁ * r₂⁻¹)⁻¹ * r₂' ∈ H) : r₂' ∈ R.N := by
  have := R.N.mul_mem R.r_alpha_mem_N (R.H_le_N h2H)
  rwa [mul_inv_cancel_left] at this

theorem rest_sq₁ (R : RGD2 6 H r₁ r₂ U root) {r₁' : X} (h1H : r₁⁻¹ * r₁' ∈ H) :
    r₁' * r₁' ∈ H := by
  have e : r₁' * r₁' = (r₁ * r₁) * (r₁⁻¹ * (r₁⁻¹ * r₁') * r₁) * (r₁⁻¹ * r₁') := by group
  rw [e]
  exact H.mul_mem (H.mul_mem R.sq₁ (R.conj_H₁' h1H)) h1H

theorem rest_sq₂ (R : RGD2 6 H r₁ r₂ U root) {r₂' : X} (h2H : (r₂ * r₁ * r₂⁻¹)⁻¹ * r₂' ∈ H) :
    r₂' * r₂' ∈ H := by
  have hαα : (r₂ * r₁ * r₂⁻¹) * (r₂ * r₁ * r₂⁻¹) ∈ H := by
    have h := R.conj_H₂ (r₁ * r₁) R.sq₁
    have e : r₂ * r₁ * r₂⁻¹ * (r₂ * r₁ * r₂⁻¹) = r₂ * (r₁ * r₁) * r₂⁻¹ := by group
    rwa [e]
  have hc := (R.N_normalizes_H R.r_alpha_mem_N _ h2H).2
  have e : r₂' * r₂' = ((r₂ * r₁ * r₂⁻¹) * (r₂ * r₁ * r₂⁻¹)) *
      ((r₂ * r₁ * r₂⁻¹)⁻¹ * ((r₂ * r₁ * r₂⁻¹)⁻¹ * r₂') * (r₂ * r₁ * r₂⁻¹)) *
        ((r₂ * r₁ * r₂⁻¹)⁻¹ * r₂') := by group
  rw [e]
  exact H.mul_mem (H.mul_mem hαα hc) h2H

theorem rest_pow (R : RGD2 6 H r₁ r₂ U root) {r₁' r₂' : X} (h1H : r₁⁻¹ * r₁' ∈ H)
    (h2H : (r₂ * r₁ * r₂⁻¹)⁻¹ * r₂' ∈ H) : (r₁' * r₂') ^ 3 ∈ H := by
  have hnorm := R.normal_H_subgroupOf
  have h1N := rest_r₁_mem_N R h1H
  have h2N := rest_r₂_mem_N R h2H
  set a₁ : R.N := ⟨r₁, R.r₁_mem_N⟩ with ha₁
  set a₂ : R.N := ⟨r₂, R.r₂_mem_N⟩ with ha₂
  set b₁ : R.N := ⟨r₁', h1N⟩ with hb₁
  set b₂ : R.N := ⟨r₂', h2N⟩ with hb₂
  let q : R.N →* R.N ⧸ H.subgroupOf R.N := QuotientGroup.mk' (H.subgroupOf R.N)
  have hq1 : q b₁ = q a₁ := by
    symm
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    exact h1H
  have hq2 : q b₂ = q (a₂ * a₁ * a₂⁻¹) := by
    symm
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    exact h2H
  have ht : q a₂ * q a₂ = 1 := by
    rw [← map_mul, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact R.sq₂
  have hst : (q a₁ * q a₂) ^ 6 = 1 := by
    rw [← map_mul, ← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
    exact R.pow
  have key : q ((b₁ * b₂) ^ 3) = 1 := by
    rw [map_pow, map_mul, hq1, hq2, map_mul, map_mul, map_inv]
    exact rest_weyl_pow ht hst
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at key
  exact key

theorem rest_actsPos_r₁ (R : RGD2 6 H r₁ r₂ U root) {r₁' : X} (h1H : r₁⁻¹ * r₁' ∈ H) :
    ActsPos 6 root r₁' (fun q => ((6 : ℕ) : ℤ) - q) ∧
      ActsPos 6 root r₁'⁻¹ (fun q => ((6 : ℕ) : ℤ) - q) := by
  constructor
  · have := R.actsPos_mul_H h1H R.actsPos_r₁
    rwa [mul_inv_cancel_left] at this
  · have h := R.actsPos_H_mul (H.inv_mem h1H) (R.actsPos_inv_of_sq R.sq₁ R.actsPos_r₁)
    have e : (r₁⁻¹ * r₁')⁻¹ * r₁⁻¹ = r₁'⁻¹ := by group
    rwa [e] at h

theorem rest_actsPos_r₂ (R : RGD2 6 H r₁ r₂ U root) {r₂' : X}
    (h2H : (r₂ * r₁ * r₂⁻¹)⁻¹ * r₂' ∈ H) :
    ActsPos 6 root r₂' (fun q => ((6 : ℕ) : ℤ) - 4 - q) ∧
      ActsPos 6 root r₂'⁻¹ (fun q => ((6 : ℕ) : ℤ) - 4 - q) := by
  constructor
  · have := R.actsPos_mul_H h2H R.actsPos_alpha
    rwa [mul_inv_cancel_left] at this
  · have h := R.actsPos_H_mul (H.inv_mem h2H) R.actsPos_alpha_inv
    have e : ((r₂ * r₁ * r₂⁻¹)⁻¹ * r₂')⁻¹ * (r₂ * r₁⁻¹ * r₂⁻¹) = r₂'⁻¹ := by group
    rwa [e] at h

theorem rest_act₁ (R : RGD2 6 H r₁ r₂ U root) {φ : X ≃* X} {r₁' : X} (h1 : φ r₁' = r₁')
    (h1H : r₁⁻¹ * r₁' ∈ H) :
    conjBy r₁'⁻¹ (foldRoot φ root 1) = foldRoot φ root (-1) ∧
      conjBy r₁'⁻¹ (foldRoot φ root (-1)) = foldRoot φ root 1 ∧
      ∀ i : ℤ, 2 ≤ i → i ≤ ((3 : ℕ) : ℤ) →
        conjBy r₁'⁻¹ (foldRoot φ root i) = foldRoot φ root (((3 : ℕ) : ℤ) + 2 - i) ∧
          conjBy r₁'⁻¹ (foldRoot φ root (-i)) = foldRoot φ root (-(((3 : ℕ) : ℤ) + 2 - i)) := by
  obtain ⟨hm, hm'⟩ := rest_actsPos_r₁ R h1H
  have hff : ∀ q : ℤ, ((6 : ℕ) : ℤ) - (((6 : ℕ) : ℤ) - q) = q := fun q => by ring
  have key : ∀ {p a b : ℤ}, Rt 6 p = a → Rt 6 (((6 : ℕ) : ℤ) - p) = b →
      conjBy r₁'⁻¹ (root a ⊓ foldFix φ) = root b ⊓ foldFix φ := by
    intro p a b ha hb
    rw [rest_conjBy_inf_foldFix h1, rest_conjBy_root hm hm' hff ha hb]
  refine ⟨?_, ?_, ?_⟩
  · exact key (p := 0) (a := foldIdx 1) (b := foldIdx (-1)) (by decide) (by decide)
  · exact key (p := 6) (a := foldIdx (-1)) (b := foldIdx 1) (by decide) (by decide)
  · intro i hi2 hi3
    have hi3' : i ≤ 3 := by exact_mod_cast hi3
    interval_cases i
    · exact ⟨key (p := 2) (a := foldIdx 2) (b := foldIdx (((3 : ℕ) : ℤ) + 2 - 2)) (by decide)
        (by decide), key (p := 8) (a := foldIdx (-2)) (b := foldIdx (-(((3 : ℕ) : ℤ) + 2 - 2)))
        (by decide) (by decide)⟩
    · exact ⟨key (p := 4) (a := foldIdx 3) (b := foldIdx (((3 : ℕ) : ℤ) + 2 - 3)) (by decide)
        (by decide), key (p := 10) (a := foldIdx (-3)) (b := foldIdx (-(((3 : ℕ) : ℤ) + 2 - 3)))
        (by decide) (by decide)⟩

theorem rest_act₂ (R : RGD2 6 H r₁ r₂ U root) {φ : X ≃* X} {r₂' : X} (h2 : φ r₂' = r₂')
    (h2H : (r₂ * r₁ * r₂⁻¹)⁻¹ * r₂' ∈ H) :
    conjBy r₂'⁻¹ (foldRoot φ root ((3 : ℕ) : ℤ)) = foldRoot φ root (-((3 : ℕ) : ℤ)) ∧
      conjBy r₂'⁻¹ (foldRoot φ root (-((3 : ℕ) : ℤ))) = foldRoot φ root ((3 : ℕ) : ℤ) ∧
      ∀ i : ℤ, 1 ≤ i → i ≤ ((3 : ℕ) : ℤ) - 1 →
        conjBy r₂'⁻¹ (foldRoot φ root i) = foldRoot φ root (((3 : ℕ) : ℤ) - i) ∧
          conjBy r₂'⁻¹ (foldRoot φ root (-i)) = foldRoot φ root (-(((3 : ℕ) : ℤ) - i)) := by
  obtain ⟨hm, hm'⟩ := rest_actsPos_r₂ R h2H
  have hff : ∀ q : ℤ, ((6 : ℕ) : ℤ) - 4 - (((6 : ℕ) : ℤ) - 4 - q) = q := fun q => by ring
  have key : ∀ {p a b : ℤ}, Rt 6 p = a → Rt 6 (((6 : ℕ) : ℤ) - 4 - p) = b →
      conjBy r₂'⁻¹ (root a ⊓ foldFix φ) = root b ⊓ foldFix φ := by
    intro p a b ha hb
    rw [rest_conjBy_inf_foldFix h2, rest_conjBy_root hm hm' hff ha hb]
  refine ⟨?_, ?_, ?_⟩
  · exact key (p := 4) (a := foldIdx ((3 : ℕ) : ℤ)) (b := foldIdx (-((3 : ℕ) : ℤ))) (by decide)
      (by decide)
  · exact key (p := 10) (a := foldIdx (-((3 : ℕ) : ℤ))) (b := foldIdx ((3 : ℕ) : ℤ)) (by decide)
      (by decide)
  · intro i hi1 hi2
    have hi2' : i ≤ 2 := by
      have : i ≤ ((3 : ℕ) : ℤ) - 1 := hi2
      push_cast at this
      omega
    interval_cases i
    · exact ⟨key (p := 0) (a := foldIdx 1) (b := foldIdx (((3 : ℕ) : ℤ) - 1)) (by decide)
        (by decide), key (p := 6) (a := foldIdx (-1)) (b := foldIdx (-(((3 : ℕ) : ℤ) - 1)))
        (by decide) (by decide)⟩
    · exact ⟨key (p := 2) (a := foldIdx 2) (b := foldIdx (((3 : ℕ) : ℤ) - 2)) (by decide)
        (by decide), key (p := 8) (a := foldIdx (-2)) (b := foldIdx (-(((3 : ℕ) : ℤ) - 2)))
        (by decide) (by decide)⟩

theorem rest_nilpotent (R : RGD2 6 H r₁ r₂ U root) (F : Subgroup X) :
    Group.IsNilpotent ↥(U ⊓ F) := by
  have := R.nilpotent
  have hle : U ⊓ F ≤ U := inf_le_left
  exact Group.nilpotent_of_surjective (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hle).surjective

theorem rest_negGen_le (φ : X ≃* X) (root : ℤ → Subgroup X) :
    negGen 3 (foldRoot φ root) ≤ negGen 6 root := by
  unfold negGen
  refine iSup₂_le fun k hk => ?_
  intro y hy
  have hk1 : 1 ≤ k := hk.1
  have hk3 : k ≤ 3 := by exact_mod_cast hk.2
  have hidx : foldIdx (-k) = -(2 * k - 1) := by
    rw [foldIdx_of_neg (by omega)]
    ring
  refine mem_negGen_of_mem (n := 6) (k := 2 * k - 1) (by omega) (by push_cast; omega) ?_
  have h := hy.1
  rwa [hidx] at h

theorem rest_meet_one (R : RGD2 6 H r₁ r₂ U root) (φ : X ≃* X) :
    ∀ x ∈ (H ⊓ foldFix φ) ⊔ (U ⊓ foldFix φ), x ∈ negGen 3 (foldRoot φ root) → x = 1 := by
  intro x hx hxn
  have hle : (H ⊓ foldFix φ) ⊔ (U ⊓ foldFix φ) ≤ H ⊔ U := sup_le_sup inf_le_left inf_le_left
  exact R.meet_one x (hle hx) (rest_negGen_le φ root hxn)

end Hexagon

namespace FoldData

variable {H : Subgroup X} {r₁ r₂ : X} {U : Subgroup X} {root : ℤ → Subgroup X}
  {R : RGD2 6 H r₁ r₂ U root} {φ : X ≃* X}

theorem rgd2_aux (hf : FoldData R φ) {r₁' r₂' : X} (h1 : φ r₁' = r₁') (h1H : r₁⁻¹ * r₁' ∈ H)
    (h2 : φ r₂' = r₂') (h2H : (r₂ * r₁ * r₂⁻¹)⁻¹ * r₂' ∈ H)
    (hcar : ((U ⊓ foldFix φ : Subgroup X) : Set X) =
      chainProd (foldRoot φ root) (intList 1 ((3 : ℕ) : ℤ)))
    (huniq : ∀ f g : ℤ → X, (∀ k ∈ intList 1 ((3 : ℕ) : ℤ), f k ∈ foldRoot φ root k) →
      (∀ k ∈ intList 1 ((3 : ℕ) : ℤ), g k ∈ foldRoot φ root k) →
      ((intList 1 ((3 : ℕ) : ℤ)).map f).prod = ((intList 1 ((3 : ℕ) : ℤ)).map g).prod →
        ∀ k ∈ intList 1 ((3 : ℕ) : ℤ), f k = g k)
    (hrev : ∀ i j : ℤ, 1 ≤ i → i ≤ j → j ≤ ((3 : ℕ) : ℤ) →
      chainProd (foldRoot φ root) (intList i j) =
        chainProd (foldRoot φ root) (intList i j).reverse)
    (hsub : ∀ i j : ℤ, 1 ≤ i → i ≤ j → j ≤ ((3 : ℕ) : ℤ) →
      ∃ V : Subgroup X, (V : Set X) = chainProd (foldRoot φ root) (intList i j) ∧
        V ≤ U ⊓ foldFix φ ∧
        (1 < i → ∀ x ∈ foldRoot φ root (i - 1), ∀ v ∈ V, x * v * x⁻¹ ∈ V) ∧
        (j < ((3 : ℕ) : ℤ) → ∀ x ∈ foldRoot φ root (j + 1), ∀ v ∈ V, x * v * x⁻¹ ∈ V))
    (hrk1 : ∀ y ∈ foldRoot φ root (-1), y ≠ 1 →
      y ∈ (foldRoot φ root 1 : Set X) * ((H ⊓ foldFix φ : Subgroup X) : Set X) * {r₁'} *
        (foldRoot φ root 1 : Set X))
    (hrk2 : ∀ y ∈ foldRoot φ root (-((3 : ℕ) : ℤ)), y ≠ 1 →
      y ∈ (foldRoot φ root ((3 : ℕ) : ℤ) : Set X) * ((H ⊓ foldFix φ : Subgroup X) : Set X) *
        {r₂'} * (foldRoot φ root ((3 : ℕ) : ℤ) : Set X)) :
    RGD2 3 (H ⊓ foldFix φ) r₁' r₂' (U ⊓ foldFix φ) (foldRoot φ root) := by
  have h1N : r₁' ∈ R.N := rest_r₁_mem_N R h1H
  have h2N : r₂' ∈ R.N := rest_r₂_mem_N R h2H
  have h1F : r₁' ∈ foldFix φ := mem_foldFix.2 h1
  have h2F : r₂' ∈ foldFix φ := mem_foldFix.2 h2
  exact
    { three_le := le_refl 3
      comm_H := fun a ha b hb => R.comm_H a ha.1 b hb.1
      nilpotent := rest_nilpotent R (foldFix φ)
      conj_H₁ := fun h hh =>
        ⟨(R.N_normalizes_H h1N h hh.1).1,
          (foldFix φ).mul_mem ((foldFix φ).mul_mem h1F hh.2) ((foldFix φ).inv_mem h1F)⟩
      conj_H₂ := fun h hh =>
        ⟨(R.N_normalizes_H h2N h hh.1).1,
          (foldFix φ).mul_mem ((foldFix φ).mul_mem h2F hh.2) ((foldFix φ).inv_mem h2F)⟩
      sq₁ := ⟨rest_sq₁ R h1H, (foldFix φ).mul_mem h1F h1F⟩
      sq₂ := ⟨rest_sq₂ R h2H, (foldFix φ).mul_mem h2F h2F⟩
      pow := ⟨rest_pow R h1H h2H, (foldFix φ).pow_mem ((foldFix φ).mul_mem h1F h2F) 3⟩
      U_inf_H := by
        refine eq_bot_iff.2 fun x hx => ?_
        have hx' : x ∈ U ⊓ H := ⟨hx.1.1, hx.2.1⟩
        rw [R.U_inf_H] at hx'
        exact hx'
      ne_bot := fun i hi => by
        obtain ⟨x, hx, hx1, hxφ⟩ :=
          hf.odd_fix (foldIdx i) (isRoot_foldIdx hi) (foldIdx_odd hi.1)
        intro hbot
        have hxm : x ∈ foldRoot φ root i := ⟨hx, mem_foldFix.2 hxφ⟩
        rw [hbot] at hxm
        exact hx1 (Subgroup.mem_bot.1 hxm)
      invariant := fun i hi h hh x hx =>
        ⟨R.invariant (foldIdx i) (isRoot_foldIdx hi) h hh.1 x hx.1,
          (foldFix φ).mul_mem ((foldFix φ).mul_mem hh.2 hx.2) ((foldFix φ).inv_mem hh.2)⟩
      carrier_eq := hcar
      unique := huniq
      reverse_eq := hrev
      subgroup := hsub
      act₁ := rest_act₁ R h1 h1H
      act₂ := rest_act₂ R h2 h2H
      meet_one := rest_meet_one R φ
      rank₁ := hrk1
      rank₂ := hrk2 }

end FoldData

end CFSG.GH74.GLS.SP
