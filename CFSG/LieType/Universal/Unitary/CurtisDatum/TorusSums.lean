module

public import CFSG.LieType.Universal.Unitary.CurtisDatum
public import CFSG.LieType.Steinberg.CentralExt.SUThree
public import CFSG.LieType.Universal.Unitary.Extras.Commutator
public import CFSG.LieType.Universal.Unitary.Extras.RankOneLast
public import CFSG.LieType.Steinberg.CurtisDatum.TorusSums
import all CFSG.LieType.Universal.Unitary.Roots
public import Mathlib.RingTheory.IntegralDomain

public section

namespace CFSG.LieType.Universal.Unitary

open Matrix CFSG.LieType.Steinberg CFSG.LieType.RootSystem CFSG.LieType.BorelTits
  CFSG.LieType.Universal.SpecialLinear CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.Quasithin.SmithCurtis
open scoped MatrixGroups Pointwise

variable {F : Type} [Field F] [Finite F] {f : ℕ} [CharP F 2]

@[instance_reducible] private noncomputable def fintypeOfFinite (α : Type*) [Finite α] :
    Fintype α :=
  Fintype.ofFinite α

attribute [local instance] fintypeOfFinite Classical.propDecidable

local notation "σU" => unitaryInvolution F 2 f

theorem curtisDatum_L_lower (hF : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) (hn : 2 ≤ n)
    (ζ : traceZero (unitaryInvolution F 2 f)) (hζ : (ζ : F) ≠ 0)
    {g : SU (unitaryInvolution F 2 f) n}
    (hg : g ∈ (curtisDatum hF n hn ζ hζ).L) :
    (∀ a b : Fin n, a < b → mat (unitaryInvolution F 2 f) n g a b = 0) ∧
      ∀ a, mat (unitaryInvolution F 2 f) n g a a = 1 := by
  have hσ := unitaryInvolution_involutive hF
  have hL : (curtisDatum hF n hn ζ hζ).L = negUnipotent (rootDatum hF n) := by
    unfold curtisDatum curtisDatumOf
    rfl
  rw [hL] at hg
  unfold negUnipotent at hg
  have h := idBelow_of_mem_iSup hσ (-1)
    {γ | γ ∈ roots (isFiniteType_cartan n) (divisible n) ∧ ht γ < 0}
    (fun γ hγ => by have := hγ.2; omega) hg
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · have hab' : (a : ℤ) < (b : ℤ) := by exact_mod_cast hab
    rw [h a b (by simp only [lvl]; omega)]
    exact Matrix.one_apply_ne (ne_of_lt hab)
  · rw [h a a (by simp only [lvl]; omega)]
    exact Matrix.one_apply_eq a

theorem levelWeyl_conj_levelTorus_inv (hF : Nat.card F = (2 ^ f) ^ 2) {n : ℕ}
    {ζ : traceZero (unitaryInvolution F 2 f)} (hζ : (ζ : F) ≠ 0) {s : Fin (n / 2)}
    (hs : s.val + 1 < n / 2 ∨ Even n) {t : SU (unitaryInvolution F 2 f) n}
    (ht : t ∈ levelTorus (unitaryInvolution F 2 f) s) :
    levelWeyl (unitaryInvolution_involutive hF) ζ s * t *
        (levelWeyl (unitaryInvolution_involutive hF) ζ s)⁻¹ = t⁻¹ := by
  have hσ := unitaryInvolution_involutive hF
  obtain ⟨c, hc⟩ := exists_tFun_of_mem_levelTorus ht
  have hW : mat (unitaryInvolution F 2 f) n (levelWeyl hσ ζ s) =
      signedPerm (levelPerm s) (levelSign (unitaryInvolution F 2 f) (ζ : F) s) := by
    rw [mat_apply, coe_levelWeyl hσ hζ]
  have hconj := coe_conj_diagonal (σ := unitaryInvolution F 2 f)
    (W := levelWeyl hσ ζ s) (g := t) (π := levelPerm s)
    (d := levelSign (unitaryInvolution F 2 f) (ζ : F) s)
    (t := tFun (unitaryInvolution F 2 f) s (c : F)) hW hc
  rw [levelPerm_symm] at hconj
  have hpoint : ∀ r, tFun (unitaryInvolution F 2 f) s (c : F) (levelPerm s r) =
      tFun (unitaryInvolution F 2 f) s ((c : F)⁻¹) r := by
    intro r
    unfold tFun
    by_cases hk : s.val + 1 < n / 2
    · rw [dite_eq_left hk, dite_eq_left hk]
      simpa only [Units.val_inv_eq_inv_val] using shortTorusFun_levelPerm_self hk c r
    · rw [dite_eq_right hk, dite_eq_right hk]
      have he : Even n := hs.resolve_left hk
      rw [ite_eq_left he, ite_eq_left he]
      simpa only [Units.val_inv_eq_inv_val] using longTorusFun_levelPerm_self hk c r
  have ht0 : ∀ r, tFun (unitaryInvolution F 2 f) s (c : F) r ≠ 0 :=
    tFun_ne_zero s c.ne_zero
  have hinv := diagonal_inv_eq ht0 hc
  apply mat_injective
  calc mat (unitaryInvolution F 2 f) n
        (levelWeyl hσ ζ s * t * (levelWeyl hσ ζ s)⁻¹)
      = diagonal (fun r => tFun (unitaryInvolution F 2 f) s (c : F) (levelPerm s r)) := hconj
    _ = diagonal (tFun (unitaryInvolution F 2 f) s ((c : F)⁻¹)) := by
          congr 1
          funext r
          exact hpoint r
    _ = diagonal (fun r => (tFun (unitaryInvolution F 2 f) s (c : F) r)⁻¹) := by
          rw [tFun_inv]
    _ = mat (unitaryInvolution F 2 f) n t⁻¹ := hinv.symm

theorem levelWeyl_inv_conj_levelTorus_inv (hF : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (hn : 2 ≤ n)
    {ζ : traceZero (unitaryInvolution F 2 f)} (hζ : (ζ : F) ≠ 0) {s : Fin (n / 2)}
    (hs : s.val + 1 < n / 2 ∨ Even n) {t : SU (unitaryInvolution F 2 f) n}
    (ht : t ∈ levelTorus (unitaryInvolution F 2 f) s) :
    (levelWeyl (unitaryInvolution_involutive hF) ζ s)⁻¹ * t *
        levelWeyl (unitaryInvolution_involutive hF) ζ s = t⁻¹ := by
  have hσ := unitaryInvolution_involutive hF
  have hconj := levelWeyl_conj_levelTorus_inv hF hζ hs ht
  have hn2 : levelWeyl hσ ζ s ^ 2 ∈ levelTorus (unitaryInvolution F 2 f) s :=
    levelWeyl_sq_mem hσ hζ s
  have hn2H : levelWeyl hσ ζ s ^ 2 ∈ ⨆ j, levelTorus (unitaryInvolution F 2 f) (n := n) j :=
    Subgroup.mem_iSup_of_mem s hn2
  have htH : t ∈ ⨆ j, levelTorus (unitaryInvolution F 2 f) (n := n) j :=
    Subgroup.mem_iSup_of_mem s ht
  have hcomm := CFSG.LieType.Steinberg.iSup_H_comm
    (D := rootDatum hF n) (n := levelWeyl hσ ζ)
    (H := levelTorus (unitaryInvolution F 2 f)) (steinbergExtras hF n hn ζ hζ)
    (a := (levelWeyl hσ ζ s ^ 2)⁻¹) (b := t⁻¹)
  have hnnt : levelWeyl hσ ζ s * t * levelWeyl hσ ζ s =
      t⁻¹ * levelWeyl hσ ζ s ^ 2 := by
    calc levelWeyl hσ ζ s * t * levelWeyl hσ ζ s =
        (levelWeyl hσ ζ s * t * (levelWeyl hσ ζ s)⁻¹) * levelWeyl hσ ζ s ^ 2 := by group
      _ = t⁻¹ * levelWeyl hσ ζ s ^ 2 := by rw [hconj]
  calc (levelWeyl hσ ζ s)⁻¹ * t * levelWeyl hσ ζ s =
      (levelWeyl hσ ζ s ^ 2)⁻¹ * (levelWeyl hσ ζ s * t * levelWeyl hσ ζ s) := by group
    _ = (levelWeyl hσ ζ s ^ 2)⁻¹ * (t⁻¹ * levelWeyl hσ ζ s ^ 2) := by rw [hnnt]
    _ = ((levelWeyl hσ ζ s ^ 2)⁻¹ * t⁻¹) * levelWeyl hσ ζ s ^ 2 := by rw [mul_assoc]
    _ = (t⁻¹ * (levelWeyl hσ ζ s ^ 2)⁻¹) * levelWeyl hσ ζ s ^ 2 := by
          rw [hcomm (inv_mem hn2H) (inv_mem htH)]
    _ = t⁻¹ * ((levelWeyl hσ ζ s ^ 2)⁻¹ * levelWeyl hσ ζ s ^ 2) := by rw [mul_assoc]
    _ = t⁻¹ := by rw [inv_mul_cancel, mul_one]

omit [CharP F 2] in
theorem odd_card_sub_one (hF : Nat.card F = (2 ^ f) ^ 2) : Odd (Nat.card F - 1) := by
  have hf : 0 < f := by
    by_contra h
    have hf0 : f = 0 := by omega
    rw [hf0, pow_zero, one_pow] at hF
    have := Finite.one_lt_card (α := F)
    omega
  have h2 : 2 ∣ Nat.card F := by
    rw [hF, pow_two]
    exact dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) _
  obtain ⟨m, hm⟩ := h2
  have hpos : 0 < Nat.card F := Nat.card_pos
  refine ⟨m - 1, by omega⟩

theorem odd_card_normFib (hF : Nat.card F = (2 ^ f) ^ 2) {b : F} :
    Odd ((@Finset.univ F (Fintype.ofFinite F)).filter
      (fun a : F => b + σU b + σU a * a = 0)).card := by
  classical
  have hσ := unitaryInvolution_involutive hF
  set fib : Finset F := (@Finset.univ F (Fintype.ofFinite F)).filter
    (fun a : F => b + σU b + σU a * a = 0) with hfib
  by_cases hc : b + σU b = 0
  · have hfib0 : fib = {0} := by
      ext a
      rw [hfib, Finset.mem_filter, Finset.mem_singleton]
      constructor
      · intro h
        have h' : σU a * a = 0 := by
          have := h.2
          rw [hc, zero_add] at this
          exact this
        rcases mul_eq_zero.mp h' with h'' | h''
        · exact (map_eq_zero σU).mp h''
        · exact h''
      · intro ha
        rw [ha]
        simpa using hc
    rw [hfib0]
    simp
  · let c : F := -(b + σU b)
    have hc0 : c ≠ 0 := neg_ne_zero.mpr hc
    have hc_fix : σU c = c := by
      simp only [c, map_neg, map_add, hσ]
      abel
    obtain ⟨a0, ha0⟩ := exists_norm_eq (p := 2) hF hc_fix
    have ha0ne : a0 ≠ 0 := by
      intro h
      rw [h] at ha0
      simp at ha0
      exact hc0 ha0.symm
    let U : Finset (normOne σU) := Finset.univ
    have hcard : U.card = fib.card := by
      refine Finset.card_bij (fun u (_ : u ∈ U) => a0 * ((u : Fˣ) : F)) ?_ ?_ ?_
      · intro u _
        rw [hfib, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        calc b + σU b + σU (a0 * ((u : Fˣ) : F)) * (a0 * ((u : Fˣ) : F))
            = (b + σU b) + σU a0 * a0 * (σU ((u : Fˣ) : F) * ((u : Fˣ) : F)) := by
              rw [map_mul]; ring
          _ = 0 := by
            rw [ha0, u.2, mul_one]
            change b + σU b + -(b + σU b) = 0
            exact add_neg_cancel (b + σU b)
      · intro u _ v _ huv
        have h : ((u : Fˣ) : F) = ((v : Fˣ) : F) := mul_left_cancel₀ ha0ne huv
        exact Subtype.ext (Units.ext h)
      · intro a ha
        rw [hfib] at ha
        have hrel := (Finset.mem_filter.mp ha).2
        have hnorm : σU a * a = c := by
          change σU a * a = -(b + σU b)
          rw [eq_neg_iff_add_eq_zero, add_comm]
          exact hrel
        have hane : a ≠ 0 := by
          intro h
          rw [h] at hnorm
          simp only [map_zero, zero_mul] at hnorm
          exact hc0 hnorm.symm
        refine ⟨⟨Units.mk0 (a / a0) (div_ne_zero hane ha0ne), ?_⟩, ?_, ?_⟩
        · rw [mem_normOne, Units.val_mk0, map_div₀]
          field_simp [ha0ne]
          linear_combination hnorm - ha0
        · exact Finset.mem_univ _
        · rw [Units.val_mk0]
          exact mul_div_cancel₀ a ha0ne
    have hcard' : fib.card = Nat.card (normOne σU) := by
      rw [← hcard, Nat.card_eq_fintype_card, Finset.card_univ]
    rw [hcard']
    refine Odd.of_dvd_nat ?_ (Subgroup.card_subgroup_dvd_card (normOne σU))
    rw [Nat.card_units]
    exact odd_card_sub_one hF

theorem chi_one_eq_one_of_ne_zero {n : ℕ} {k : Type*} [Field k]
    (χ : SU σU n → k)
    (hχ : ∀ a ∈ ⨆ j, levelTorus σU (n := n) j,
      ∀ b ∈ ⨆ j, levelTorus σU (n := n) j, χ (a * b) = χ a * χ b)
    (h1 : χ 1 ≠ 0) : χ 1 = 1 := by
  have h := hχ 1 (one_mem _) 1 (one_mem _)
  have h' : χ 1 = χ 1 * χ 1 := by simpa using h
  have h2 : χ 1 * (1 - χ 1) = 0 := by
    calc χ 1 * (1 - χ 1) = χ 1 - χ 1 * χ 1 := by ring
      _ = 0 := by rw [← h', sub_self]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 h1
  · exact (sub_eq_zero.mp h3).symm

theorem chi_eq_zero_of_one_eq_zero {n : ℕ} {k : Type*} [Field k]
    (χ : SU σU n → k)
    (hχ : ∀ a ∈ ⨆ j, levelTorus σU (n := n) j,
      ∀ b ∈ ⨆ j, levelTorus σU (n := n) j, χ (a * b) = χ a * χ b)
    (h1 : χ 1 = 0) {h : SU σU n}
    (hh : h ∈ ⨆ j, levelTorus σU (n := n) j) : χ h = 0 := by
  have h := hχ h hh 1 (one_mem _)
  simpa only [mul_one, h1, mul_zero] using h

theorem chi_mul_self_ne_one (hF : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} {k : Type*} [Field k]
    (χ : SU (unitaryInvolution F 2 f) n → k)
    (hχ : ∀ a ∈ ⨆ j, levelTorus (unitaryInvolution F 2 f) (n := n) j,
      ∀ b ∈ ⨆ j, levelTorus (unitaryInvolution F 2 f) (n := n) j, χ (a * b) = χ a * χ b)
    {t : SU (unitaryInvolution F 2 f) n}
    (htH : t ∈ ⨆ j, levelTorus (unitaryInvolution F 2 f) (n := n) j)
    (htN : t ^ (Nat.card F - 1) = 1) (ht : χ t ≠ 1) : χ t * χ t ≠ 1 := by
  by_cases h1 : χ 1 = 0
  · have hzero : χ t = 0 := by
      have h := hχ 1 (one_mem _) t htH
      simpa only [h1, zero_mul, one_mul] using h
    rw [hzero]
    simp
  · have hchi1 : χ 1 = 1 := by
      have h := hχ 1 (one_mem _) 1 (one_mem _)
      have h' : χ 1 = χ 1 * χ 1 := by simpa using h
      have h2 : χ 1 * (1 - χ 1) = 0 := by
        calc χ 1 * (1 - χ 1) = χ 1 - χ 1 * χ 1 := by ring
          _ = 0 := by rw [← h', sub_self]
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact absurd h3 h1
      · exact (sub_eq_zero.mp h3).symm
    have hpow : ∀ m : ℕ, χ (t ^ m) = (χ t) ^ m := by
      intro m
      induction m with
      | zero => simpa using hchi1
      | succ m ih =>
        rw [pow_succ, hχ (t ^ m) (pow_mem htH m) t htH, ih, pow_succ]
    have hodd := odd_card_sub_one hF
    intro hsq
    have hsq' : (χ t) ^ 2 = 1 := by rw [pow_two]; exact hsq
    apply ht
    have hN : (χ t) ^ (Nat.card F - 1) = 1 := by
      rw [← hpow, htN]
      exact hchi1
    obtain ⟨m, hm⟩ := hodd
    have hcalc : (χ t) ^ (Nat.card F - 1) = χ t := by
      rw [hm, pow_succ, pow_mul, hsq', one_pow, one_mul]
    rwa [hcalc] at hN

omit [Finite F] [CharP F 2] in
theorem rootGroup_last_odd_eq_heisenberg {σ : F ≃+* F} {n : ℕ}
    (hσ : ∀ c, σ (σ c) = c) (hn : ¬ Even n)
    {k : Fin (n / 2)} (hk : ¬ k.val + 1 < n / 2) :
    rootGroup σ hσ n (Pi.single k 1) =
      heisenbergSubgroup σ hσ (lowIdx_ne_rev k k) (last_odd_ne hk hn).1
        (rev_midIdx hn) := by
  refine le_antisymm ?_ (heisenberg_le hσ (lowIdx_ne_rev k k) (last_odd_ne hk hn).1
    (rev_midIdx hn) (toStd_last_odd hk hn).symm)
  unfold rootGroup
  refine sup_le (sup_le ?_ ?_) ?_
  · refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => iSup_le fun hi =>
      iSup_le fun hj => iSup_le fun hji => iSup_le fun hw => ?_
    exfalso
    have hw' : weight n i - weight n j = weight n (lowIdx (n := n) k) := by
      rw [hw, toStd_last_odd hk hn]
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ :=
      eq_of_weight_sub_eq_weight (i := lowIdx (n := n) k) (k := midIdx n hn) (lowIdx_ne_rev k k)
        (rev_midIdx hn) hw'
    · exact hj (rev_midIdx hn).symm
    · exact hi (rev_midIdx hn).symm
  · refine iSup_le fun i => iSup_le fun hi => iSup_le fun hw => ?_
    exfalso
    have hw' : 2 • weight n i = weight n (lowIdx (n := n) k) := by
      rw [hw, toStd_last_odd hk hn]
    have h1 : (2 : ℤ) * weight n i k = 1 := by
      have h := congrFun hw' k
      rw [weight_lowIdx, Pi.single_eq_same] at h
      simpa using h
    have h2 := (weight_apply_bounds i k).1
    have h3 := (weight_apply_bounds i k).2
    omega
  · refine iSup_le fun i => iSup_le fun k' => iSup_le fun hi => iSup_le fun hik =>
      iSup_le fun hk' => iSup_le fun hw => ?_
    have hw' : weight n i = weight n (lowIdx (n := n) k) := by
      rw [hw, toStd_last_odd hk hn]
    have hi' : i = lowIdx (n := n) k := weight_injective hw'
    have hk'' : k' = midIdx n hn := middle_unique hk' (rev_midIdx hn)
    subst hi'
    subst hk''
    exact le_rfl

omit [Finite F] [CharP F 2] in
theorem mem_rootGroup_last_odd_iff {σ : F ≃+* F} {n : ℕ}
    (hσ : ∀ c, σ (σ c) = c) (hn : ¬ Even n)
    {k : Fin (n / 2)} (hk : ¬ k.val + 1 < n / 2) {x : SU σ n} :
    x ∈ rootGroup σ hσ n (Pi.single k 1) ↔
      ∃ a b : F, b + σ b + σ a * a = 0 ∧
        mat σ n x = heisenbergMatrix σ (lowIdx (n := n) k) (midIdx n hn) a b := by
  rw [rootGroup_last_odd_eq_heisenberg hσ hn hk]
  rfl

omit [Finite F] [CharP F 2] in
theorem mat_eq_diagonal_heisTorusFun_of_mem_levelTorus_last_odd {σ : F ≃+* F} {n : ℕ}
    (hn : ¬ Even n) {k : Fin (n / 2)} (hk : ¬ k.val + 1 < n / 2) {g : SU σ n}
    (hg : g ∈ levelTorus σ k) :
    mat σ n g = diagonal (heisTorusFun σ (lowIdx (n := n) k)
      (mat σ n g (lowIdx (n := n) k) (lowIdx (n := n) k))) := by
  obtain ⟨c, hc⟩ := exists_tFun_of_mem_levelTorus hg
  have hpp : mat σ n g (lowIdx (n := n) k) (lowIdx (n := n) k) = (c : F) := by
    rw [hc, Matrix.diagonal_apply_eq]
    rw [tFun, dite_eq_right hk, ite_eq_right hn]
    simp [heisTorusFun]
  rw [hpp, hc]
  congr 1
  funext s
  rw [tFun, dite_eq_right hk, ite_eq_right hn]

omit [Finite F] [CharP F 2] in
theorem mat_apply_self_ne_zero_of_mem_levelTorus_last_odd {σ : F ≃+* F} {n : ℕ}
    (hn : ¬ Even n) {k : Fin (n / 2)} (hk : ¬ k.val + 1 < n / 2) {g : SU σ n}
    (hg : g ∈ levelTorus σ k) :
    mat σ n g (lowIdx (n := n) k) (lowIdx (n := n) k) ≠ 0 := by
  obtain ⟨c, hc⟩ := exists_tFun_of_mem_levelTorus hg
  rw [hc, Matrix.diagonal_apply_eq]
  rw [tFun, dite_eq_right hk, ite_eq_right hn]
  simp [heisTorusFun, c.ne_zero]

omit [Finite F] [CharP F 2] in
theorem eq_of_mem_levelTorus_last_odd_of_apply_eq {σ : F ≃+* F} {n : ℕ}
    (hn : ¬ Even n) {k : Fin (n / 2)} (hk : ¬ k.val + 1 < n / 2) {g g' : SU σ n}
    (hg : g ∈ levelTorus σ k) (hg' : g' ∈ levelTorus σ k)
    (h : mat σ n g (lowIdx (n := n) k) (lowIdx (n := n) k) =
      mat σ n g' (lowIdx (n := n) k) (lowIdx (n := n) k)) : g = g' := by
  apply mat_injective
  rw [mat_eq_diagonal_heisTorusFun_of_mem_levelTorus_last_odd hn hk hg,
    mat_eq_diagonal_heisTorusFun_of_mem_levelTorus_last_odd hn hk hg', h]

omit [Finite F] [CharP F 2] in
theorem heisenbergMatrix_apply_self_rev {σ : F ≃+* F} {n : ℕ} {i k : Fin n}
    (hi : i ≠ Fin.rev i) (hik : i ≠ k) (hk : Fin.rev k = k) (a b : F) :
    heisenbergMatrix σ i k a b i (Fin.rev i) = b := by
  have hki : k ≠ i := hik.symm
  have hkrev : k ≠ Fin.rev i := by
    intro h
    exact hik (by rw [← Fin.rev_rev i, ← h, hk])
  simp [heisenbergMatrix, hki, hkrev, hi]

theorem phi_apply_last_odd_eq_diagonal (hF : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (hn : 2 ≤ n)
    (ζ : traceZero (unitaryInvolution F 2 f)) (hζ : (ζ : F) ≠ 0)
    (hodd : ¬ Even n) {s : Fin (n / 2)} (hs : ¬ s.val + 1 < n / 2)
    {x : SU σU n} (hx : x ∈ (curtisDatum hF n hn ζ hζ).X s) (hx1 : x ≠ 1)
    {a b : F}
    (hxmat : mat σU n x = heisenbergMatrix σU (lowIdx (n := n) s) (midIdx n hodd) a b) :
    mat σU n ((curtisDatum hF n hn ζ hζ).phi s x) =
      diagonal (heisTorusFun σU (lowIdx (n := n) s) (b * (-(ζ : F)⁻¹))) := by
  have hσ : ∀ c, σU (σU c) = c := unitaryInvolution_involutive hF
  have hct := isCTGroupDatum hF n hn ζ hζ
  have hext := steinbergExtras hF n hn ζ hζ
  have hBU := CFSG.LieType.Steinberg.CentralExt.SUBruhat.bruhatExtras hF hn ζ hζ
  have hpG : ∀ γ ∈ (rootDatum hF n).roots, IsPGroup 2 ((rootDatum hF n).rootGroup γ) :=
    fun γ hγ => @CFSG.LieType.Steinberg.isPGroup_rootGroup F inferInstance n σU hσ
      ⟨⟨0, by omega⟩⟩ 2 inferInstance inferInstance γ (toStd_ne_zero_of_mem_roots hγ)
  have hxr : x ∈ (rootDatum hF n).rootGroup (Pi.single s 1) := hx
  set p : Fin n := lowIdx (n := n) s with hp
  set mid : Fin n := midIdx n hodd with hmid
  have hvals : p.val + 1 = mid.val ∧ mid.val + 1 = (Fin.rev p).val := by
    rw [hp, hmid]; exact last_odd_vals hs hodd
  have hne : p ≠ mid ∧ Fin.rev p ≠ mid := by
    rw [hp, hmid]; exact last_odd_ne hs hodd
  have hpp : p ≠ Fin.rev p := by rw [hp]; exact lowIdx_ne_rev s s
  have hxmat' : mat σU n x = heisenbergMatrix σU p mid a b := by
    simpa [hp, hmid] using hxmat
  have hphi : (curtisDatum hF n hn ζ hζ).phi s x = rankOnePhi hct hext hBU s x := by
    unfold curtisDatum
    exact curtisDatumOf_phi_apply hct hext hBU 2 hpG s x
  have hφmem : (curtisDatum hF n hn ζ hζ).phi s x ∈ levelTorus σU s := by
    rw [hphi]
    exact rankOnePhi_mem hct hext hBU s hxr hx1
  have hdiag := mat_eq_diagonal_heisTorusFun_of_mem_levelTorus_last_odd hodd hs hφmem
  have hdiag' : mat σU n ((curtisDatum hF n hn ζ hζ).phi s x) =
      diagonal (heisTorusFun σU p
        (mat σU n ((curtisDatum hF n hn ζ hζ).phi s x) p p)) := by
    rw [hp]; exact hdiag
  obtain ⟨l, hl, u, hu, hlu⟩ := rankOnePhi_spec hct hext hBU s hxr hx1
  have hlL : l ∈ (curtisDatum hF n hn ζ hζ).L := hl
  have huU : u ∈ (curtisDatum hF n hn ζ hζ).U := hu
  have hlmat := curtisDatum_L_lower hF n hn ζ hζ (g := l) hlL
  have humat := (mem_curtisDatum_U_iff hF n hn ζ hζ u).mp huU
  have hlu' : x * (curtisDatum hF n hn ζ hζ).n s = l *
      (curtisDatum hF n hn ζ hζ).phi s x * u := by
    rw [hphi]
    exact hlu
  have hdiag_fun : diagonal (fun t => mat σU n ((curtisDatum hF n hn ζ hζ).phi s x) t t) =
      mat σU n ((curtisDatum hF n hn ζ hζ).phi s x) := by
    rw [hdiag']
    congr 1
    funext t
    rw [hdiag', Matrix.diagonal_apply_eq]
  have hprod : mat σU n l * diagonal (fun t => mat σU n ((curtisDatum hF n hn ζ hζ).phi s x) t t) *
      mat σU n u = mat σU n (x * (curtisDatum hF n hn ζ hζ).n s) := by
    rw [hdiag_fun, ← map_mul, ← map_mul, hlu']
  have hxj : ∀ j : Fin n, j < p →
      mat σU n (x * (curtisDatum hF n hn ζ hζ).n s) p j = 0 := by
    intro j hj
    have hjv : j.val < p.val := Fin.lt_def.mp hj
    have hjp : j ≠ p := ne_of_lt hj
    have hjm : j ≠ mid := by
      intro h; rw [h] at hjv; omega
    have hjr : j ≠ Fin.rev p := by
      intro h; rw [h] at hjv; omega
    have hjp' : j ≠ lowIdx (n := n) s := by rw [← hp]; exact hjp
    have hjr' : j ≠ Fin.rev (lowIdx (n := n) s) := by rw [← hp]; exact hjr
    have hπj : levelPerm s j = j := by
      rw [levelPerm, dite_eq_right hs]
      exact Equiv.swap_apply_of_ne_of_ne hjp' hjr'
    have hεj : levelSign σU ((ζ : F)) s j = 1 := by
      rw [levelSign, dite_eq_right hs, longSign]
      rw [if_neg hjp', if_neg hjr']
    have hcol : ∀ r, mat σU n ((curtisDatum hF n hn ζ hζ).n s) r j = if r = j then 1 else 0 := by
      intro r
      rw [show mat σU n ((curtisDatum hF n hn ζ hζ).n s) =
          signedPerm (levelPerm s) (levelSign σU ((ζ : F)) s) from ?_, signedPerm_apply, hπj, hεj]
      rw [mat_apply]
      exact coe_levelWeyl hσ hζ s
    rw [map_mul, Matrix.mul_apply]
    refine (Finset.sum_eq_single j ?_ ?_).trans ?_
    · intro r _ hr
      rw [hcol r, if_neg hr, mul_zero]
    · intro hj'; simp at hj'
    · rw [hcol j, if_pos rfl, mul_one]
      rw [hxmat']
      have h1 : p ≠ j := hjp.symm
      have h2 : mid ≠ p := hne.1.symm
      have h3 : mid ≠ j := hjm.symm
      have h4 : Fin.rev p ≠ j := hjr.symm
      simp [heisenbergMatrix, h1, h2, h3, h4]
  have hxpp : mat σU n x p (Fin.rev p) = b := by
    rw [hxmat']
    exact heisenbergMatrix_apply_self_rev hpp hne.1 (by rw [hmid]; exact rev_midIdx hodd) a b
  have hcolp : ∀ r, mat σU n ((curtisDatum hF n hn ζ hζ).n s) r p =
      if r = Fin.rev p then -(ζ : F)⁻¹ else 0 := by
    intro r
    have h := levelWeyl_col_last (hσ := hσ) (k := s) hs hζ r
    have hnD : (curtisDatum hF n hn ζ hζ).n s = levelWeyl hσ ζ s := rfl
    rw [hnD, hp]
    exact h
  have hxn_pp : mat σU n (x * (curtisDatum hF n hn ζ hζ).n s) p p =
      b * (-(ζ : F)⁻¹) := by
    rw [map_mul, Matrix.mul_apply]
    refine (Finset.sum_eq_single (Fin.rev p) ?_ ?_).trans ?_
    · intro r _ hr
      rw [hcolp r, if_neg hr, mul_zero]
    · intro h; simp at h
    · rw [hxpp, hcolp (Fin.rev p), if_pos rfl]
  have h0 : ∀ j, j < p →
      (mat σU n l * diagonal (fun t => mat σU n ((curtisDatum hF n hn ζ hζ).phi s x) t t) *
        mat σU n u) p j = 0 := by
    intro j hj
    rw [hprod]
    exact hxj j hj
  have hstep := mul_diagonal_mul_apply_self (L := mat σU n l) (U := mat σU n u)
    (fun t => mat σU n ((curtisDatum hF n hn ζ hζ).phi s x) t t)
    humat.1 humat.2 (hlmat.2 p) h0
  have hpphi : mat σU n ((curtisDatum hF n hn ζ hζ).phi s x) p p = b * (-(ζ : F)⁻¹) := by
    rw [← hstep, hprod, hxn_pp]
  rw [hdiag', hpphi]

theorem sum_comp_eq_sum_erase_of_odd_fiber {X E k : Type*} [Fintype E] [DecidableEq E]
    [CommRing k] [CharP k 2] (S : Finset X) (β : X → E) (ψ : E → k) (b₀ : E)
    (hS : ∀ x ∈ S, β x ≠ b₀)
    (hodd : ∀ b, b ≠ b₀ → Odd (S.filter fun x => β x = b).card) :
    ∑ x ∈ S, ψ (β x) = ∑ b ∈ Finset.univ.erase b₀, ψ b := by
  rw [← Finset.sum_fiberwise_of_maps_to' (g := β) (t := Finset.univ.erase b₀)
    (fun x hx => Finset.mem_erase.mpr ⟨hS x hx, Finset.mem_univ _⟩)]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  obtain ⟨m, hm⟩ := hodd b (Finset.mem_erase.mp hb).1
  rw [hm]
  push_cast
  rw [CharTwo.two_eq_zero, zero_mul, zero_add, one_mul]

theorem sum_erase_zero_comp_mul_eq_sum_units {E M : Type*} [Field E] [Fintype E] [DecidableEq E]
    [Fintype Eˣ] [AddCommMonoid M] (g : E → M) {c : E} (hc : c ≠ 0) :
    ∑ b ∈ Finset.univ.erase (0 : E), g (b * c) = ∑ u : Eˣ, g u := by
  refine Finset.sum_bij' (fun b hb => Units.mk0 (b * c) (mul_ne_zero (Finset.mem_erase.mp hb).1 hc))
    (fun u _ => (u : E) * c⁻¹) (fun _ _ => Finset.mem_univ _) (fun u _ => ?_) (fun b _ => ?_)
    (fun u _ => ?_) (fun b _ => rfl)
  · exact Finset.mem_erase.mpr ⟨mul_ne_zero u.ne_zero (inv_ne_zero hc), Finset.mem_univ _⟩
  · simp [mul_assoc, mul_inv_cancel₀ hc]
  · ext
    simp [mul_assoc, inv_mul_cancel₀ hc]

omit [Finite F] [CharP F 2] in
@[expose] noncomputable def heisenbergElt {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) {n : ℕ}
    {i k : Fin n} (hi : i ≠ Fin.rev i) (hik : i ≠ k) (hk : Fin.rev k = k) {a b : F}
    (hab : b + σ b + σ a * a = 0) : SU σ n :=
  ⟨⟨heisenbergMatrix σ i k a b, heisenbergMatrix σ i k (-a) (-b - a * σ a),
      by
        rw [heisenbergMatrix_mul σ hi hik hk, map_neg, add_neg_cancel,
          show b + (-b - a * σ a) - a * -σ a = 0 by ring, heisenbergMatrix_zero],
      by
        rw [heisenbergMatrix_mul σ hi hik hk, neg_add_cancel,
          show -b - a * σ a + b - -a * σ a = 0 by ring, heisenbergMatrix_zero]⟩,
    det_heisenbergMatrix σ hi hik hk a b, heisenbergMatrix_isometry σ hσ hi hik hk hab⟩

omit [Finite F] [CharP F 2] in
theorem mat_heisenbergElt {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) {n : ℕ} {i k : Fin n}
    (hi : i ≠ Fin.rev i) (hik : i ≠ k) (hk : Fin.rev k = k) {a b : F}
    (hab : b + σ b + σ a * a = 0) :
    mat σ n (heisenbergElt hσ hi hik hk hab) = heisenbergMatrix σ i k a b :=
  rfl

omit [Finite F] [CharP F 2] in
theorem heisenbergMatrix_apply_self_mid {σ : F ≃+* F} {n : ℕ} {i k : Fin n}
    (hik : i ≠ k) (hk : Fin.rev k = k) (a b : F) :
    heisenbergMatrix σ i k a b i k = a := by
  have hki : k ≠ i := hik.symm
  have hrk : Fin.rev i ≠ k := fun h => hik (by rw [← Fin.rev_rev i, h, hk])
  simp [heisenbergMatrix, hik, hki, hrk]

theorem mem_curtisDatum_X_last_odd_iff (hF : Nat.card F = (2 ^ f) ^ 2)
    {n : ℕ} (hn : 2 ≤ n) (ζ : traceZero (unitaryInvolution F 2 f)) (hζ : (ζ : F) ≠ 0)
    (hodd : ¬ Even n) {s : Fin (n / 2)} (hs : ¬ s.val + 1 < n / 2) {x : SU σU n} :
    x ∈ (curtisDatum hF n hn ζ hζ).X s ↔
      ∃ a b : F, b + σU b + σU a * a = 0 ∧
        mat σU n x = heisenbergMatrix σU (lowIdx (n := n) s) (midIdx n hodd) a b :=
  mem_rootGroup_last_odd_iff (unitaryInvolution_involutive hF) hodd hs

theorem curtisDatum_dScalar_eq_zero_last_odd (hF : Nat.card F = (2 ^ f) ^ 2) (n : ℕ)
    (hn : 2 ≤ n) (ζ : traceZero (unitaryInvolution F 2 f)) (hζ : (ζ : F) ≠ 0)
    {k : Type*} [Field k] [CharP k 2] (χ : SU (unitaryInvolution F 2 f) n → k)
    {s : Fin (n / 2)} (hs : ¬ s.val + 1 < n / 2) (hodd : ¬ Even n)
    (hχ : ∀ a ∈ (curtisDatum hF n hn ζ hζ).H, ∀ b ∈ (curtisDatum hF n hn ζ hζ).H,
      χ (a * b) = χ a * χ b)
    (hnt : ∃ t ∈ levelTorus (unitaryInvolution F 2 f) s, χ t ≠ 1) :
    (curtisDatum hF n hn ζ hζ).dScalar χ s = 0 := by
  have hσ : ∀ c, σU (σU c) = c := unitaryInvolution_involutive hF
  set p : Fin n := lowIdx (n := n) s with hp
  set mid : Fin n := midIdx n hodd with hmid
  have hpp : p ≠ Fin.rev p := lowIdx_ne_rev s s
  have hpm : p ≠ mid := (last_odd_ne hs hodd).1
  have hmr : Fin.rev mid = mid := rev_midIdx hodd
  have hnorm : ∀ x, σU x = x → ∃ a, σU a * a = x := by
    intro x hx
    rcases eq_or_ne x 0 with rfl | hx0
    · exact ⟨0, by simp⟩
    · exact CFSG.ClassicalGroups.Unitary.exists_norm_eq_of_fixed hF hx hx0
  have hT : ∀ t : Fˣ, ∃ g ∈ levelTorus σU s,
      mat σU n g = diagonal (heisTorusFun σU p (t : F)) := by
    intro t
    obtain ⟨g, -, hg⟩ := exists_heisGen_mem_rankOne hσ hζ hnorm hs hodd t
    exact ⟨g, heisGen_mem_levelTorus hs hodd t hg, by rw [mat_apply]; exact hg⟩
  choose T hTmem hTmat using hT
  have hTpp : ∀ t : Fˣ, mat σU n (T t) p p = t := by
    intro t
    rw [hTmat, Matrix.diagonal_apply_eq, heisTorusFun_self]
  have hTeq : ∀ {g : SU σU n}, g ∈ levelTorus σU s → ∀ t : Fˣ, mat σU n g p p = t →
      g = T t := by
    intro g hg t h
    exact eq_of_mem_levelTorus_last_odd_of_apply_eq hodd hs hg (hTmem t) (by rw [h, hTpp])
  have hTH : ∀ t : Fˣ, T t ∈ (curtisDatum hF n hn ζ hζ).H :=
    fun t => Subgroup.mem_iSup_of_mem s (hTmem t)
  have hsum : ∑ t : Fˣ, χ (T t) = 0 := by
    by_cases h1 : χ 1 = 0
    · exact Finset.sum_eq_zero fun t _ => chi_eq_zero_of_one_eq_zero χ hχ h1 (hTH t)
    · have h1' : χ 1 = 1 := chi_one_eq_one_of_ne_zero χ hχ h1
      have hT1 : T 1 = 1 := (hTeq (one_mem _) 1 (by simp)).symm
      have hTmul : ∀ u v : Fˣ, T (u * v) = T u * T v := by
        intro u v
        refine (hTeq (mul_mem (hTmem u) (hTmem v)) (u * v) ?_).symm
        rw [map_mul, hTmat, hTmat, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq,
          heisTorusFun_self, heisTorusFun_self, Units.val_mul]
      let ψ : Fˣ →* k :=
        { toFun := fun t => χ (T t)
          map_one' := by simp only [hT1, h1']
          map_mul' := fun u v => by simp only [hTmul, hχ _ (hTH u) _ (hTH v)] }
      have hψ : ψ ≠ 1 := by
        obtain ⟨t, ht, hχt⟩ := hnt
        intro hψ1
        have hpp0 : mat σU n t p p ≠ 0 :=
          mat_apply_self_ne_zero_of_mem_levelTorus_last_odd hodd hs ht
        have h := DFunLike.congr_fun hψ1 (Units.mk0 _ hpp0)
        apply hχt
        rw [hTeq ht (Units.mk0 _ hpp0) (by simp)]
        exact h
      exact sum_hom_units_eq_zero ψ hψ
  set c : F := -(ζ : F)⁻¹ with hc
  have hc0 : c ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hζ)
  let T' : F → SU σU n := fun t => if ht : t = 0 then 1 else T (Units.mk0 t ht)
  have hT' : ∀ u : Fˣ, T' u = T u := fun u => by
    simp only [T', dif_neg u.ne_zero, Units.mk0_val]
  let β : (curtisDatum hF n hn ζ hζ).X s → F := fun x => mat σU n x p (Fin.rev p)
  have hX : ∀ x : (curtisDatum hF n hn ζ hζ).X s, ∃ a, β x + σU (β x) + σU a * a = 0 ∧
      mat σU n x = heisenbergMatrix σU p mid a (β x) := by
    intro x
    obtain ⟨a, b, hab, hx⟩ := (mem_curtisDatum_X_last_odd_iff hF hn ζ hζ hodd hs).mp x.2
    have hb : β x = b := by
      change mat σU n x p (Fin.rev p) = b
      rw [hx]
      exact heisenbergMatrix_apply_self_rev hpp hpm hmr a b
    exact ⟨a, by rw [hb]; exact hab, by rw [hb]; exact hx⟩
  have hβ0 : ∀ x : (curtisDatum hF n hn ζ hζ).X s, x ≠ 1 → β x ≠ 0 := by
    intro x hx1 hb
    obtain ⟨a, hab, hx⟩ := hX x
    rw [hb, map_zero, zero_add, zero_add] at hab
    have ha : a = 0 := by
      rcases mul_eq_zero.mp hab with h | h
      · exact (map_eq_zero σU).mp h
      · exact h
    apply hx1
    apply Subtype.ext
    apply mat_injective
    rw [hx, hb, ha, heisenbergMatrix_zero, OneMemClass.coe_one, map_one]
  have hβ1 : β 1 = 0 := by
    change mat σU n ((1 : (curtisDatum hF n hn ζ hζ).X s) : SU σU n) p (Fin.rev p) = 0
    rw [Subgroup.coe_one, map_one, Matrix.one_apply_ne hpp]
  have hphi : ∀ x : (curtisDatum hF n hn ζ hζ).X s, x ≠ 1 →
      χ ((curtisDatum hF n hn ζ hζ).phi s x) = χ (T' (β x * c)) := by
    intro x hx1
    have hx1' : (x : SU σU n) ≠ 1 := fun h => hx1 (Subtype.ext h)
    obtain ⟨a, -, hx⟩ := hX x
    have hdiag := phi_apply_last_odd_eq_diagonal hF hn ζ hζ hodd hs x.2 hx1' hx
    have hbc : β x * c ≠ 0 := mul_ne_zero (hβ0 x hx1) hc0
    have heq : (curtisDatum hF n hn ζ hζ).phi s x = T (Units.mk0 _ hbc) := by
      apply mat_injective
      rw [hdiag, hTmat, Units.val_mk0]
    rw [heq]
    simp only [T', dif_neg hbc]
  have hEltX : ∀ {a b : F} (hab : b + σU b + σU a * a = 0),
      heisenbergElt hσ hpp hpm hmr hab ∈ (curtisDatum hF n hn ζ hζ).X s :=
    fun hab => (mem_curtisDatum_X_last_odd_iff hF hn ζ hζ hodd hs).mpr
      ⟨_, _, hab, mat_heisenbergElt hσ hpp hpm hmr hab⟩
  have hfib : ∀ (S : Finset ((curtisDatum hF n hn ζ hζ).X s)), (∀ x, x ∈ S ↔ x ≠ 1) →
      ∀ b : F, b ≠ 0 → (S.filter fun x => β x = b).card =
        ((@Finset.univ F (Fintype.ofFinite F)).filter
          fun a : F => b + σU b + σU a * a = 0).card := by
    intro S hSmem b hb
    refine Finset.card_bij (fun x _ => mat σU n x p mid) ?_ ?_ ?_
    · intro x hx
      obtain ⟨hxS, hxb⟩ := Finset.mem_filter.mp hx
      obtain ⟨a, hab, hxm⟩ := hX x
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [hxm, heisenbergMatrix_apply_self_mid hpm hmr, ← hxb]
      exact hab
    · intro x₁ hx₁ x₂ hx₂ h
      obtain ⟨a₁, -, hx₁m⟩ := hX x₁
      obtain ⟨a₂, -, hx₂m⟩ := hX x₂
      have hb₁ := (Finset.mem_filter.mp hx₁).2
      have hb₂ := (Finset.mem_filter.mp hx₂).2
      have ha : a₁ = a₂ := by
        have h' := h
        rw [hx₁m, hx₂m, heisenbergMatrix_apply_self_mid hpm hmr,
          heisenbergMatrix_apply_self_mid hpm hmr] at h'
        exact h'
      apply Subtype.ext
      apply mat_injective
      rw [hx₁m, hx₂m, ha, hb₁, hb₂]
    · intro a ha
      have hab := (Finset.mem_filter.mp ha).2
      let x : (curtisDatum hF n hn ζ hζ).X s := ⟨heisenbergElt hσ hpp hpm hmr hab, hEltX hab⟩
      have hxb : β x = b := by
        change mat σU n (heisenbergElt hσ hpp hpm hmr hab) p (Fin.rev p) = b
        rw [mat_heisenbergElt]
        exact heisenbergMatrix_apply_self_rev hpp hpm hmr a b
      have hx1 : x ≠ 1 := by
        intro h
        apply hb
        rw [← hxb, h]
        exact hβ1
      refine ⟨x, Finset.mem_filter.mpr ⟨(hSmem x).mpr hx1, hxb⟩, ?_⟩
      change mat σU n (heisenbergElt hσ hpp hpm hmr hab) p mid = a
      rw [mat_heisenbergElt]
      exact heisenbergMatrix_apply_self_mid hpm hmr a b
  have hS : ∀ (S : Finset ((curtisDatum hF n hn ζ hζ).X s)), (∀ x, x ∈ S ↔ x ≠ 1) →
      ∑ x ∈ S, χ ((curtisDatum hF n hn ζ hζ).phi s x) = 0 := by
    intro S hSmem
    rw [Finset.sum_congr rfl fun x hx => hphi x ((hSmem x).mp hx),
      sum_comp_eq_sum_erase_of_odd_fiber S β (fun b => χ (T' (b * c))) 0
        (fun x hx => hβ0 x ((hSmem x).mp hx))
        (fun b hb => by rw [hfib S hSmem b hb]; exact odd_card_normFib hF),
      sum_erase_zero_comp_mul_eq_sum_units (fun t => χ (T' t)) hc0]
    simp only [hT']
    exact hsum
  rw [CurtisDatum.dScalar]
  exact hS _ fun x => by simp

theorem curtisDatum_dScalar_eq_zero (hF : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) (hn : 2 ≤ n)
    (ζ : traceZero (unitaryInvolution F 2 f)) (hζ : (ζ : F) ≠ 0)
    {k : Type*} [Field k] [CharP k 2]
    (χ : SU (unitaryInvolution F 2 f) n → k)
    (hχ : ∀ a ∈ (curtisDatum hF n hn ζ hζ).H, ∀ b ∈ (curtisDatum hF n hn ζ hζ).H,
      χ (a * b) = χ a * χ b) (s : Fin (n / 2))
    (hs : ∃ t ∈ levelTorus (unitaryInvolution F 2 f) s, χ t ≠ 1) :
    (curtisDatum hF n hn ζ hζ).dScalar χ s = 0 ∧
      (curtisDatum hF n hn ζ hζ).d'Scalar χ s = 0 := by
  have hσ := unitaryInvolution_involutive hF
  have hct := isCTGroupDatum hF n hn ζ hζ
  have hext := steinbergExtras hF n hn ζ hζ
  have hBU := CFSG.LieType.Steinberg.CentralExt.SUBruhat.bruhatExtras hF hn ζ hζ
  have hpG : ∀ γ ∈ (rootDatum hF n).roots, IsPGroup 2 ((rootDatum hF n).rootGroup γ) :=
    fun γ hγ => @CFSG.LieType.Steinberg.isPGroup_rootGroup F inferInstance n
      (unitaryInvolution F 2 f) hσ ⟨⟨0, by omega⟩⟩ 2 inferInstance inferInstance γ
      (toStd_ne_zero_of_mem_roots hγ)
  have hds : (curtisDatum hF n hn ζ hζ).d'Scalar χ s =
      (curtisDatum hF n hn ζ hζ).dScalar χ s := by
    unfold curtisDatum
    exact curtisDatumOf_d'Scalar_eq_dScalar (D := rootDatum hF n)
      (n := levelWeyl hσ ζ) (H := levelTorus (unitaryInvolution F 2 f))
      hct hext hBU 2 hpG χ s
  have hzero : (curtisDatum hF n hn ζ hζ).dScalar χ s = 0 := by
    by_cases hshort : s.val + 1 < n / 2 ∨ Even n
    · obtain ⟨t, ht, hχt⟩ := hs
      have htH : t ∈ ⨆ j, levelTorus (unitaryInvolution F 2 f) (n := n) j :=
        Subgroup.mem_iSup_of_mem s ht
      have htN : t ^ (Nat.card F - 1) = 1 := levelTorus_pow_card_sub_one ht
      have hfac : (levelWeyl hσ ζ s)⁻¹ * t⁻¹ * levelWeyl hσ ζ s = t := by
        have := levelWeyl_inv_conj_levelTorus_inv hF hn hζ hshort (inv_mem ht)
        simpa only [inv_inv] using this
      have hfactor : χ t * χ ((levelWeyl hσ ζ s)⁻¹ * t⁻¹ * levelWeyl hσ ζ s) ≠ 1 := by
        rw [hfac]
        exact chi_mul_self_ne_one hF χ hχ htH htN hχt
      unfold curtisDatum
      exact curtisDatumOf_dScalar_eq_zero_of_conj (D := rootDatum hF n)
        (n := levelWeyl hσ ζ) (H := levelTorus (unitaryInvolution F 2 f))
        hct hext hBU 2 hpG χ hχ s htH hfactor
    · have h1 : ¬ s.val + 1 < n / 2 := fun h => hshort (Or.inl h)
      have h2 : ¬ Even n := fun h => hshort (Or.inr h)
      exact curtisDatum_dScalar_eq_zero_last_odd hF n hn ζ hζ χ h1 h2 hχ hs
  exact ⟨hzero, hds.trans hzero⟩

theorem curtisDatum_dScalar_eq_neg_one (hF : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) (hn : 2 ≤ n)
    (ζ : traceZero (unitaryInvolution F 2 f)) (hζ : (ζ : F) ≠ 0)
    {k : Type*} [Field k] [CharP k 2]
    (χ : SU (unitaryInvolution F 2 f) n → k) (s : Fin (n / 2))
    (hs : ∀ t ∈ levelTorus (unitaryInvolution F 2 f) s, χ t = 1) :
    (curtisDatum hF n hn ζ hζ).dScalar χ s = -1 ∧
      (curtisDatum hF n hn ζ hζ).d'Scalar χ s = -1 := by
  have hσ := unitaryInvolution_involutive hF
  have hct := isCTGroupDatum hF n hn ζ hζ
  have hext := steinbergExtras hF n hn ζ hζ
  have hBU := CFSG.LieType.Steinberg.CentralExt.SUBruhat.bruhatExtras hF hn ζ hζ
  have hpG : ∀ γ ∈ (rootDatum hF n).roots, IsPGroup 2 ((rootDatum hF n).rootGroup γ) :=
    fun γ hγ => @CFSG.LieType.Steinberg.isPGroup_rootGroup F inferInstance n
      (unitaryInvolution F 2 f) hσ ⟨⟨0, by omega⟩⟩ 2 inferInstance inferInstance γ
      (toStd_ne_zero_of_mem_roots hγ)
  have h1 : (curtisDatum hF n hn ζ hζ).dScalar χ s = -1 := by
    unfold curtisDatum
    exact curtisDatumOf_dScalar_eq_neg_one (D := rootDatum hF n)
      (n := levelWeyl hσ ζ) (H := levelTorus (unitaryInvolution F 2 f))
      hct hext hBU 2 hpG χ s hs
  have h2 : (curtisDatum hF n hn ζ hζ).d'Scalar χ s =
      (curtisDatum hF n hn ζ hζ).dScalar χ s := by
    unfold curtisDatum
    exact curtisDatumOf_d'Scalar_eq_dScalar (D := rootDatum hF n)
      (n := levelWeyl hσ ζ) (H := levelTorus (unitaryInvolution F 2 f))
      hct hext hBU 2 hpG χ s
  exact ⟨h1, h2.trans h1⟩

end CFSG.LieType.Universal.Unitary
