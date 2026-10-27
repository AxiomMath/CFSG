module

public import CFSG.RankThree.PartOne.CTP.Su4Geom
public import CFSG.ClassicalGroups.Unitary.Elements
public import CFSG.RankThree.PartOne.CTP.SpGeom

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.RankThree.PartOne.CTP

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ} {W : Submodule K (Fin n → K)}

theorem smul_mem_hermOrth_iff {g : SUid σ n} (hg : ∀ x ∈ W, g • x = x) {v : Fin n → K} :
    g • v ∈ hermOrth σ W ↔ v ∈ hermOrth σ W := by
  refine ⟨fun h w hw => ?_, fun h w hw => ?_⟩
  · calc herm σ w v = herm σ (g • w) (g • v) := (herm_smul_smul σ g w v).symm
      _ = herm σ w (g • v) := by rw [hg w hw]
      _ = 0 := h w hw
  · calc herm σ w (g • v) = herm σ (g • w) (g • v) := by rw [hg w hw]
      _ = herm σ w v := herm_smul_smul σ g w v
      _ = 0 := h w hw

theorem smul_mem_hermOrth {e : SUid σ n} (he : ∀ w ∈ W, e⁻¹ • w ∈ W) {v : Fin n → K}
    (hv : v ∈ hermOrth σ W) : e • v ∈ hermOrth σ W := by
  intro w hw
  calc herm σ w (e • v) = herm σ (e • (e⁻¹ • w)) (e • v) := by rw [smul_inv_smul]
    _ = herm σ (e⁻¹ • w) v := herm_smul_smul σ e _ v
    _ = 0 := hv _ (he w hw)

@[expose] def uRad (σ : K ≃+* K) (W : Submodule K (Fin n → K))
    (hW : ∀ x ∈ W, ∀ y ∈ W, herm σ x y = 0) : Subgroup (SUid σ n) where
  carrier := {g | (∀ x, g • x - x ∈ hermOrth σ W) ∧ (∀ x ∈ hermOrth σ W, g • x - x ∈ W) ∧
    ∀ x ∈ W, g • x = x}
  mul_mem' := by
    rintro g h ⟨hg1, hg2, hg3⟩ ⟨hh1, hh2, hh3⟩
    have hWP : ∀ x ∈ W, x ∈ hermOrth σ W := fun x hx w hw => hW w hw x hx
    refine ⟨fun x => ?_, fun x hx => ?_, fun x hx => ?_⟩
    · rw [mul_smul]
      have := (hermOrth σ W).add_mem (hg1 (h • x)) (hh1 x)
      simpa using this
    · have hhx : h • x ∈ hermOrth σ W := by
        have := (hermOrth σ W).add_mem hx (hWP _ (hh2 x hx))
        simpa using this
      rw [mul_smul]
      have := W.add_mem (hg2 _ hhx) (hh2 x hx)
      simpa using this
    · rw [mul_smul, hh3 x hx, hg3 x hx]
  one_mem' := ⟨fun x => by simp, fun x _ => by simp, fun x _ => by simp⟩
  inv_mem' := by
    rintro g ⟨hg1, hg2, hg3⟩
    have hinv : ∀ x ∈ W, g⁻¹ • x = x := fun x hx => by
      conv_lhs => rw [← hg3 x hx]
      exact inv_smul_smul g x
    refine ⟨fun x => ?_, fun x hx => ?_, hinv⟩
    · have := (hermOrth σ W).neg_mem (hg1 (g⁻¹ • x))
      rw [smul_inv_smul] at this
      simpa using this
    · have hy : g⁻¹ • x ∈ hermOrth σ W := by
        rw [← smul_mem_hermOrth_iff hg3, smul_inv_smul]
        exact hx
      have := W.neg_mem (hg2 _ hy)
      rw [smul_inv_smul] at this
      simpa using this

theorem uRad_conj_mem {hW : ∀ x ∈ W, ∀ y ∈ W, herm σ x y = 0} {e g : SUid σ n}
    (he : ∀ w ∈ W, e • w ∈ W) (he' : ∀ w ∈ W, e⁻¹ • w ∈ W) (hg : g ∈ uRad σ W hW) :
    e * g * e⁻¹ ∈ uRad σ W hW := by
  obtain ⟨hg1, hg2, hg3⟩ := hg
  have hmul : ∀ x : Fin n → K, (e * g * e⁻¹) • x = e • (g • (e⁻¹ • x)) := fun x => by
    rw [mul_smul, mul_smul]
  refine ⟨fun x => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · rw [hmul]
    have h2 := smul_mem_hermOrth he' (hg1 (e⁻¹ • x))
    rw [smul_sub, smul_inv_smul] at h2
    exact h2
  · rw [hmul]
    have hy : e⁻¹ • x ∈ hermOrth σ W :=
      smul_mem_hermOrth (e := e⁻¹) (fun w hw => by rw [inv_inv]; exact he w hw) hx
    have h2 := he _ (hg2 _ hy)
    rw [smul_sub, smul_inv_smul] at h2
    exact h2
  · rw [hmul, hg3 _ (he' x hx), smul_inv_smul]

theorem tv_mem_uRad {hW : ∀ x ∈ W, ∀ y ∈ W, herm σ x y = 0} (hσ : ∀ c, σ (σ c) = c)
    {a : Fin n → K} (ha : a ∈ W) {c : K} (hc : c + σ c = 0) :
    tv hσ (hW a ha a ha) hc ∈ uRad σ W hW := by
  have hWP : a ∈ hermOrth σ W := fun x hx => hW x hx a ha
  have hdiff : ∀ x, tv hσ (hW a ha a ha) hc • x - x = (c * herm σ a x) • a := fun x => by
    rw [tv_smul, add_sub_cancel_left]
  refine ⟨fun x => ?_, fun x _ => ?_, fun x hx => ?_⟩
  · rw [hdiff]
    exact (hermOrth σ W).smul_mem _ hWP
  · rw [hdiff]
    exact W.smul_mem _ ha
  · rw [tv_smul, hW a ha x hx, mul_zero, zero_smul, add_zero]

theorem eichler_mem_uRad {hW : ∀ x ∈ W, ∀ y ∈ W, herm σ x y = 0} (hσ : ∀ c, σ (σ c) = c)
    {e y : Fin n → K} (he : e ∈ W) (hy : y ∈ hermOrth σ W) {c : K}
    (hc : c + σ c = -herm σ y y) :
    eichler hσ (hW e he e he) (hy e he) hc ∈ uRad σ W hW := by
  have heP : e ∈ hermOrth σ W := fun x hx => hW x hx e he
  have hdiff : ∀ x, eichler hσ (hW e he e he) (hy e he) hc • x - x =
      herm σ e x • (y + c • e) - herm σ y x • e := fun x => by
    rw [eichler_smul]
    abel
  refine ⟨fun x => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · rw [hdiff]
    exact (hermOrth σ W).sub_mem ((hermOrth σ W).smul_mem _
      ((hermOrth σ W).add_mem hy ((hermOrth σ W).smul_mem _ heP))) ((hermOrth σ W).smul_mem _ heP)
  · rw [hdiff, hx e he, zero_smul, zero_sub]
    exact W.neg_mem (W.smul_mem _ he)
  · have hyx : herm σ y x = 0 := herm_eq_zero_comm σ hσ (hy x hx)
    rw [eichler_smul, hW e he x hx, hyx, zero_smul, zero_smul, add_zero, sub_zero]

theorem unip_pow_of_cube_eq_zero {R : Type*} [Ring R] [Algebra K R] {N : R}
    (hN : N * N * N = 0) (m : ℕ) :
    (1 + N) ^ m = 1 + (m : K) • N + (m.choose 2 : K) • (N * N) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ih]
    have hc : ((m + 1).choose 2 : K) = (m : K) + (m.choose 2 : K) := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right]; push_cast; ring
    have h3 : (m.choose 2 : K) • (N * N * N) = 0 := by rw [hN, smul_zero]
    simp only [Nat.cast_succ, hc, add_mul, mul_add, one_mul, mul_one, add_smul, one_smul,
      smul_mul_assoc]
    rw [h3, add_zero]
    abel

theorem actU_apply (g : SUid σ n) (x : Fin n → K) : actU σ n g x = g • x := rfl

theorem eq_one_of_pow_eq_one_uRad {hW : ∀ x ∈ W, ∀ y ∈ W, herm σ x y = 0} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0) {g : SUid σ n} (hg : g ∈ uRad σ W hW)
    (hgp : g ^ p = 1) : g = 1 := by
  obtain ⟨hg1, hg2, hg3⟩ := hg
  set N : Module.End K (Fin n → K) := actU σ n g - 1 with hNdef
  have hNx : ∀ x, N x = g • x - x := fun x => by simp [hNdef, actU_apply]
  have hN3 : N * N * N = 0 := by
    refine LinearMap.ext fun x => ?_
    have h1 : N x ∈ hermOrth σ W := by rw [hNx]; exact hg1 x
    have h2 : N (N x) ∈ W := by rw [hNx]; exact hg2 _ h1
    have h3 : N (N (N x)) = 0 := by rw [hNx, hg3 _ h2, sub_self]
    simpa using h3
  have hg1' : actU σ n g = 1 + N := by rw [hNdef]; abel
  have hpow := congrArg (actU σ n) hgp
  rw [map_pow, map_one, hg1', unip_pow_of_cube_eq_zero (K := K) hN3 p] at hpow
  set c : K := (((p - 1) / 2 : ℕ) : K) with hc
  have hchoose : (p.choose 2 : K) = (p : K) * c := by
    rw [Nat.choose_two_right, Nat.mul_div_assoc _ (even_iff_two_dvd.1 (hp.even_sub_one hp2))]
    push_cast
    rfl
  have h1 : (p : K) • (N + c • (N * N)) = 0 := by
    have h0 : (p : K) • N + (p.choose 2 : K) • (N * N) = 0 := by
      have := hpow
      rw [add_assoc] at this
      exact add_eq_left.1 this
    rw [hchoose, mul_smul] at h0
    rw [smul_add]
    exact h0
  have h2 : N + c • (N * N) = 0 := (smul_eq_zero.1 h1).resolve_left hpK
  have h3 : N * N = 0 := by
    have h := congrArg (fun X => N * X) h2
    simp only [mul_add, mul_zero, mul_smul_comm, ← mul_assoc, hN3, smul_zero, add_zero] at h
    exact h
  have h4 : N = 0 := by
    rw [h3, smul_zero, add_zero] at h2
    exact h2
  have h5 : actU σ n g = 1 := by rw [hg1', h4, add_zero]
  refine ext_smul σ fun v => ?_
  rw [one_smul]
  exact LinearMap.congr_fun h5 v

theorem not_dvd_card_uRad [Finite K] {hW : ∀ x ∈ W, ∀ y ∈ W, herm σ x y = 0} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0) : ¬ p ∣ Nat.card (uRad σ W hW) := by
  intro hdvd
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have h1 : (g : SUid σ n) ^ p = 1 := by
    have := pow_orderOf_eq_one g
    rw [hg] at this
    exact congrArg Subtype.val this
  have h2 : (g : SUid σ n) = 1 := eq_one_of_pow_eq_one_uRad hp hp2 hpK g.2 h1
  have h3 : g = 1 := Subtype.ext h2
  rw [h3, orderOf_one] at hg
  exact hp.one_lt.ne hg

end CFSG.LieType.SeitzGeneration
