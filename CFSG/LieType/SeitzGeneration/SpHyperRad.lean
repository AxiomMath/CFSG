module

public import CFSG.RankThree.PartOne.CTP.SeitzSpClosure

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.PartOne.CTP
  CFSG.Assembly.LowTwoRank

variable {r : ℕ} {K : Type} [Field K]

@[expose] def spPerp (W : Submodule K (Fin r ⊕ Fin r → K)) : Submodule K (Fin r ⊕ Fin r → K) where
  carrier := {v | ∀ w ∈ W, spForm r K w v = 0}
  add_mem' := fun {a b} ha hb w hw => by rw [map_add, ha w hw, hb w hw, add_zero]
  zero_mem' := fun w _ => map_zero _
  smul_mem' := fun c v hv w hw => by rw [map_smul, hv w hw, smul_zero]

theorem mem_spPerp {W : Submodule K (Fin r ⊕ Fin r → K)} {v : Fin r ⊕ Fin r → K} :
    v ∈ spPerp W ↔ ∀ w ∈ W, spForm r K w v = 0 := Iff.rfl

theorem spForm_eq_zero_comm {a b : Fin r ⊕ Fin r → K} (h : spForm r K a b = 0) :
    spForm r K b a = 0 := by
  rw [← spForm_isAlt.neg_eq, h, neg_zero]

theorem spForm_perp_comm {W : Submodule K (Fin r ⊕ Fin r → K)} {v w : Fin r ⊕ Fin r → K}
    (hv : v ∈ spPerp W) (hw : w ∈ W) : spForm r K v w = 0 :=
  spForm_eq_zero_comm (hv w hw)

theorem spEnd_mem_spPerp_iff {W : Submodule K (Fin r ⊕ Fin r → K)} {g : StatedSp r K}
    (hg : ∀ x ∈ W, spEnd g x = x) {v : Fin r ⊕ Fin r → K} :
    spEnd g v ∈ spPerp W ↔ v ∈ spPerp W := by
  refine ⟨fun h w hw => ?_, fun h w hw => ?_⟩
  · calc spForm r K w v = spForm r K (spEnd g w) (spEnd g v) := (spEnd_isometry g w v).symm
      _ = spForm r K w (spEnd g v) := by rw [hg w hw]
      _ = 0 := h w hw
  · calc spForm r K w (spEnd g v) = spForm r K (spEnd g w) (spEnd g v) := by rw [hg w hw]
      _ = spForm r K w v := spEnd_isometry g w v
      _ = 0 := h w hw

theorem spEnd_mem_spPerp {W : Submodule K (Fin r ⊕ Fin r → K)} {e : StatedSp r K}
    (he : ∀ w ∈ W, spEnd e⁻¹ w ∈ W) {v : Fin r ⊕ Fin r → K} (hv : v ∈ spPerp W) :
    spEnd e v ∈ spPerp W := by
  intro w hw
  calc spForm r K w (spEnd e v) = spForm r K (spEnd e (spEnd e⁻¹ w)) (spEnd e v) := by
        rw [spEnd_spEnd_inv]
    _ = spForm r K (spEnd e⁻¹ w) v := spEnd_isometry e _ v
    _ = 0 := hv _ (he w hw)

theorem spEnd_inv_spEnd (g : StatedSp r K) (y : Fin r ⊕ Fin r → K) :
    spEnd g⁻¹ (spEnd g y) = y := by
  rw [← Module.End.mul_apply, ← spEnd_mul, inv_mul_cancel, spEnd_one, Module.End.one_apply]

theorem spEnd_pow (g : StatedSp r K) (m : ℕ) : spEnd (g ^ m) = spEnd g ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, spEnd_one]
  | succ m ih => rw [pow_succ, pow_succ, spEnd_mul, ih]

section Radical

variable {W : Submodule K (Fin r ⊕ Fin r → K)}

@[expose] def spRad (W : Submodule K (Fin r ⊕ Fin r → K))
    (hW : ∀ x ∈ W, ∀ y ∈ W, spForm r K x y = 0) : Subgroup (StatedSp r K) where
  carrier := {g | (∀ x, spEnd g x - x ∈ spPerp W) ∧ (∀ x ∈ spPerp W, spEnd g x - x ∈ W) ∧
    ∀ x ∈ W, spEnd g x = x}
  mul_mem' := by
    rintro g h ⟨hg1, hg2, hg3⟩ ⟨hh1, hh2, hh3⟩
    have hWP : ∀ x ∈ W, x ∈ spPerp W := fun x hx w hw => hW w hw x hx
    refine ⟨fun x => ?_, fun x hx => ?_, fun x hx => ?_⟩
    · rw [spEnd_mul, Module.End.mul_apply]
      have := (spPerp W).add_mem (hg1 (spEnd h x)) (hh1 x)
      simpa using this
    · have hhx : spEnd h x ∈ spPerp W := by
        have := (spPerp W).add_mem hx (hWP _ (hh2 x hx))
        simpa using this
      rw [spEnd_mul, Module.End.mul_apply]
      have := W.add_mem (hg2 _ hhx) (hh2 x hx)
      simpa using this
    · rw [spEnd_mul, Module.End.mul_apply, hh3 x hx, hg3 x hx]
  one_mem' := ⟨fun x => by simp [spEnd_one], fun x _ => by simp [spEnd_one],
    fun x _ => by simp [spEnd_one]⟩
  inv_mem' := by
    rintro g ⟨hg1, hg2, hg3⟩
    have hinv : ∀ x ∈ W, spEnd g⁻¹ x = x := fun x hx => by
      conv_lhs => rw [← hg3 x hx]
      exact spEnd_inv_spEnd g x
    refine ⟨fun x => ?_, fun x hx => ?_, hinv⟩
    · have := (spPerp W).neg_mem (hg1 (spEnd g⁻¹ x))
      rw [spEnd_spEnd_inv] at this
      simpa using this
    · have hy : spEnd g⁻¹ x ∈ spPerp W := by
        rw [← spEnd_mem_spPerp_iff hg3, spEnd_spEnd_inv]
        exact hx
      have := W.neg_mem (hg2 _ hy)
      rw [spEnd_spEnd_inv] at this
      simpa using this

theorem mem_spRad {hW : ∀ x ∈ W, ∀ y ∈ W, spForm r K x y = 0} {g : StatedSp r K} :
    g ∈ spRad W hW ↔ (∀ x, spEnd g x - x ∈ spPerp W) ∧ (∀ x ∈ spPerp W, spEnd g x - x ∈ W) ∧
      ∀ x ∈ W, spEnd g x = x := Iff.rfl

theorem spRad_conj_mem {hW : ∀ x ∈ W, ∀ y ∈ W, spForm r K x y = 0} {e g : StatedSp r K}
    (he : ∀ w ∈ W, spEnd e w ∈ W) (he' : ∀ w ∈ W, spEnd e⁻¹ w ∈ W) (hg : g ∈ spRad W hW) :
    e * g * e⁻¹ ∈ spRad W hW := by
  obtain ⟨hg1, hg2, hg3⟩ := hg
  have hmul : ∀ x, spEnd (e * g * e⁻¹) x = spEnd e (spEnd g (spEnd e⁻¹ x)) := fun x => by
    rw [spEnd_mul, spEnd_mul]; rfl
  refine ⟨fun x => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · rw [hmul]
    have h2 := spEnd_mem_spPerp he' (hg1 (spEnd e⁻¹ x))
    rw [map_sub, spEnd_spEnd_inv] at h2
    exact h2
  · rw [hmul]
    have hy : spEnd e⁻¹ x ∈ spPerp W :=
      spEnd_mem_spPerp (e := e⁻¹) (fun w hw => by rw [inv_inv]; exact he w hw) hx
    have h2 := he _ (hg2 _ hy)
    rw [map_sub, spEnd_spEnd_inv] at h2
    exact h2
  · rw [hmul, hg3 _ (he' x hx), spEnd_spEnd_inv]

theorem spTransvection_mem_spRad {hW : ∀ x ∈ W, ∀ y ∈ W, spForm r K x y = 0}
    {w : Fin r ⊕ Fin r → K} (hw : w ∈ W) (t : K) : spTransvection w t ∈ spRad W hW := by
  have hWP : w ∈ spPerp W := fun x hx => hW x hx w hw
  refine ⟨fun x => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · rw [spEnd_spTransvection, add_sub_cancel_left]
    exact (spPerp W).smul_mem _ hWP
  · rw [spEnd_spTransvection, add_sub_cancel_left, spForm_perp_comm hx hw, mul_zero, zero_smul]
    exact W.zero_mem
  · rw [spEnd_spTransvection, hW x hx w hw, mul_zero, zero_smul, add_zero]

@[expose] noncomputable def spSiegel (a c : Fin r ⊕ Fin r → K) (t : K) : StatedSp r K :=
  spTransvection (a + c) t * spTransvection a (-t) * spTransvection c (-t)

theorem spEnd_spSiegel {a c : Fin r ⊕ Fin r → K} (hac : spForm r K a c = 0) (t : K)
    (x : Fin r ⊕ Fin r → K) :
    spEnd (spSiegel a c t) x = x + t • (spForm r K x a • c + spForm r K x c • a) := by
  have hca : spForm r K c a = 0 := spForm_eq_zero_comm hac
  have haa : spForm r K a a = 0 := spForm_isAlt.self_eq_zero a
  have hcc : spForm r K c c = 0 := spForm_isAlt.self_eq_zero c
  simp only [spSiegel, spEnd_mul, Module.End.mul_apply, spEnd_spTransvection, map_add, map_smul,
    hac, hca, haa, hcc, mul_zero, add_zero]
  module

theorem spSiegel_mem_spRad {hW : ∀ x ∈ W, ∀ y ∈ W, spForm r K x y = 0}
    {a c : Fin r ⊕ Fin r → K} (ha : a ∈ W) (hc : c ∈ spPerp W) (t : K) :
    spSiegel a c t ∈ spRad W hW := by
  have hac : spForm r K a c = 0 := hc a ha
  have haP : a ∈ spPerp W := fun x hx => hW x hx a ha
  refine ⟨fun x => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · rw [spEnd_spSiegel hac, add_sub_cancel_left]
    exact (spPerp W).smul_mem _ ((spPerp W).add_mem ((spPerp W).smul_mem _ hc)
      ((spPerp W).smul_mem _ haP))
  · rw [spEnd_spSiegel hac, add_sub_cancel_left, spForm_perp_comm hx ha, zero_smul, zero_add,
      smul_smul]
    exact W.smul_mem _ ha
  · rw [spEnd_spSiegel hac, hW x hx a ha, hc x hx]
    simp

theorem one_add_pow_of_cube_eq_zero {R : Type*} [Ring R] [Algebra K R] {N : R}
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

theorem eq_one_of_pow_eq_one_spRad {hW : ∀ x ∈ W, ∀ y ∈ W, spForm r K x y = 0} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0) {g : StatedSp r K} (hg : g ∈ spRad W hW)
    (hgp : g ^ p = 1) : g = 1 := by
  obtain ⟨hg1, hg2, hg3⟩ := hg
  set N : Module.End K (Fin r ⊕ Fin r → K) := spEnd g - 1 with hNdef
  have hNx : ∀ x, N x = spEnd g x - x := fun x => by simp [hNdef]
  have hN3 : N * N * N = 0 := by
    refine LinearMap.ext fun x => ?_
    have h1 : N x ∈ spPerp W := by rw [hNx]; exact hg1 x
    have h2 : N (N x) ∈ W := by rw [hNx]; exact hg2 _ h1
    have h3 : N (N (N x)) = 0 := by rw [hNx, hg3 _ h2, sub_self]
    simpa using h3
  have hg1' : spEnd g = 1 + N := by rw [hNdef]; abel
  have hpow := congrArg spEnd hgp
  rw [spEnd_pow, spEnd_one, hg1', one_add_pow_of_cube_eq_zero (K := K) hN3 p] at hpow
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
  have h5 : spEnd g = 1 := by rw [hg1', h4, add_zero]
  apply spLin_injective
  rw [map_one]
  exact Units.ext h5

theorem not_dvd_card_spRad [Finite K] {hW : ∀ x ∈ W, ∀ y ∈ W, spForm r K x y = 0} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0) : ¬ p ∣ Nat.card (spRad W hW) := by
  intro hdvd
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have h1 : (g : StatedSp r K) ^ p = 1 := by
    have := pow_orderOf_eq_one g
    rw [hg] at this
    exact congrArg Subtype.val this
  have h2 : (g : StatedSp r K) = 1 := eq_one_of_pow_eq_one_spRad hp hp2 hpK g.2 h1
  have h3 : g = 1 := Subtype.ext h2
  rw [h3, orderOf_one] at hg
  exact hp.one_lt.ne hg

end Radical

end CFSG.LieType.SeitzGeneration
