module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.KGHS3EigBase
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.TotallySplit

public section

namespace CFSG.ComponentClassification.CatFC.KGHS3

open Module Matrix

theorem l11_perp_of_eigen {E V : Type*} [Field E] [AddCommGroup V] [Module E V]
    {u : Module.End E V} {B : V →ₗ[E] V →ₗ[E] E} (huB : ∀ v w, B (u v) (u w) = B v w) {a b : E}
    (hab : a * b ≠ 1) {v w : V} (hv : u v = a • v) (hw : u w = b • w) : B v w = 0 := by
  have h := huB v w
  simp only [hv, hw, map_smul, LinearMap.smul_apply, smul_smul] at h
  have h1 : (a * b - 1) • B v w = 0 := by rw [sub_smul, one_smul, mul_comm a b, h, sub_self]
  rcases smul_eq_zero.mp h1 with h2 | h2
  · exact absurd (sub_eq_zero.mp h2) hab
  · exact h2

theorem l11_not_dvd_of_ne_neg : ∀ k i : Fin 11, i ≠ -k → ¬ 11 ∣ (k : ℕ) + (i : ℕ) := by
  decide

theorem l11_finrank_le_neg {E V : Type*} [Field E] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V] {B : V →ₗ[E] V →ₗ[E] E} (hB : ∀ v, (∀ w, B v w = 0) → v = 0)
    {W : Fin 11 → Submodule E V} (hW : ⨆ i, W i = ⊤)
    (hperp : ∀ k l : Fin 11, ∀ v ∈ W k, ∀ w ∈ W l, ¬ 11 ∣ (k : ℕ) + (l : ℕ) → B v w = 0)
    (k : Fin 11) : finrank E (W k) ≤ finrank E (W (-k)) := by
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : W k →ₗ[E] (W (-k) →ₗ[E] E), ∀ (v : W k) (w : W (-k)),
      Ψ v w = B (v : V) (w : V) := ⟨B.domRestrict₁₂ (W k) (W (-k)), fun _ _ => rfl⟩
  have hinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have hzero : ∀ w ∈ W (-k), B (v : V) w = 0 := by
      intro w hw
      have h := congrArg (fun f => f ⟨w, hw⟩) hv
      simpa [hΨ] using h
    have hall : ∀ x : V, B (v : V) x = 0 := by
      intro x
      have hx : x ∈ ⨆ i, W i := by
        rw [hW]
        exact Submodule.mem_top
      refine Submodule.iSup_induction W (motive := fun y => B (v : V) y = 0) hx ?_ ?_ ?_
      · intro i y hy
        by_cases hi : i = -k
        · subst hi
          exact hzero y hy
        · exact hperp k i (v : V) v.2 y hy (l11_not_dvd_of_ne_neg k i hi)
      · simp
      · intro x y hxv hyv
        have hxv' : B (v : V) x = 0 := hxv
        have hyv' : B (v : V) y = 0 := hyv
        show B (v : V) (x + y) = 0
        rw [map_add, hxv', hyv', add_zero]
    exact Subtype.ext (by simpa using hB (v : V) hall)
  calc finrank E (W k) ≤ finrank E (W (-k) →ₗ[E] E) :=
        LinearMap.finrank_le_finrank_of_injective hinj
    _ = finrank E (W (-k)) := Subspace.dual_finrank_eq

theorem l11_map_eigenspace {E V : Type*} [Field E] [AddCommGroup V] [Module E V]
    {u h : Module.End E V} {η : E} (hη : IsPrimitiveRoot η 11) (hu : u ^ 11 = 1)
    (hhu : h * u = u ^ 3 * h) (i : Fin 11) {v : V} (hv : v ∈ u.eigenspace (η ^ (i : ℕ))) :
    h v ∈ u.eigenspace (η ^ ((4 * i : Fin 11) : ℕ)) := by
  have hpow3 : (u ^ 3) ^ 4 = u := by
    have h12 : (u ^ 3) ^ 4 = u ^ 12 := (pow_mul u 3 4).symm
    have h13 : u ^ 12 = u ^ 11 * u := pow_succ u 11
    rw [h12, h13, hu, one_mul]
  have hpm : ∀ n : ℕ, η ^ (n % 11) = η ^ n := by
    intro n
    calc η ^ (n % 11) = η ^ (n % 11) * (η ^ 11) ^ (n / 11) := by
          rw [hη.pow_eq_one, one_pow, mul_one]
      _ = η ^ (n % 11 + 11 * (n / 11)) := by rw [pow_add, pow_mul]
      _ = η ^ n := by rw [Nat.mod_add_div]
  have hfin : ∀ i : Fin 11, ((4 * i : Fin 11) : ℕ) = ((i : ℕ) * 4) % 11 := by
    decide
  have hval : ∀ i : Fin 11, η ^ ((4 * i : Fin 11) : ℕ) = (η ^ (i : ℕ)) ^ 4 := by
    intro i
    rw [hfin i, hpm, ← pow_mul]
  rw [hval i]
  exact mem_eigenspace_of_pow_eq hpow3 (map_mem_eigenspace_of_mul_eq hhu hv)

theorem l11_dims_const {E V : Type*} [Field E] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V] {g : Module.End E V} (hg : Function.Injective g)
    {W : Fin 11 → Submodule E V} (hmap : ∀ i : Fin 11, ∀ v ∈ W i, g v ∈ W (4 * i))
    (hdual : ∀ k : Fin 11, finrank E (W k) ≤ finrank E (W (-k))) :
    ∀ k : Fin 11, k ≠ 0 → finrank E (W k) = finrank E (W 1) := by
  have hs5 : ∀ i : Fin 11, (fun k : Fin 11 => 4 * k)^[5] i = i := by
    decide
  have hcyc : ∀ (i : Fin 11) (n : ℕ),
      finrank E (W ((fun k : Fin 11 => 4 * k)^[n] i)) = finrank E (W i) :=
    fun i n => finrank_iterate_eq_of_cycle W (fun k : Fin 11 => 4 * k) hg hmap i
      (by norm_num) (hs5 i) n
  have hs2 : (fun k : Fin 11 => 4 * k)^[2] 2 = -1 := by
    decide
  have hkey : ∀ k : Fin 11, k ≠ 0 →
      (∃ n, n < 5 ∧ (fun j : Fin 11 => 4 * j)^[n] 1 = k) ∨
        (∃ n, n < 5 ∧ (fun j : Fin 11 => 4 * j)^[n] 2 = k) := by
    decide
  have hm1 : finrank E (W 1) = finrank E (W (-1)) := by
    refine le_antisymm (hdual 1) ?_
    have h := hdual (-1)
    rwa [neg_neg] at h
  have hd2 : finrank E (W 2) = finrank E (W 1) := by
    have h := hcyc 2 2
    rw [hs2] at h
    omega
  intro k hk
  rcases hkey k hk with ⟨n, -, hn⟩ | ⟨n, -, hn⟩
  · rw [← hn]
    exact hcyc 1 n
  · rw [← hn, hcyc 2 n]
    exact hd2

theorem ten_le_finrank_of_eleven_selfDual {E V : Type*} [Field E] [IsAlgClosed E]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V] (hE : ringChar E ≠ 11)
    (u h : Module.End E V) (hu : u ^ 11 = 1) (hu1 : u ≠ 1) (hh : IsUnit h)
    (hhu : h * u = u ^ 3 * h) (B : V →ₗ[E] V →ₗ[E] E) (hB : ∀ v, (∀ w, B v w = 0) → v = 0)
    (huB : ∀ v w, B (u v) (u w) = B v w) : 10 ≤ finrank E V := by
  have h11 : ((11 : ℕ) : E) ≠ 0 := by
    intro h0
    have hdvd : ringChar E ∣ 11 := (ringChar.spec (R := E) 11).mp h0
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 11)).mp hdvd with h1 | h1
    · exact CharP.ringChar_ne_one h1
    · exact hE h1
  obtain ⟨η, hη⟩ := exists_isPrimitiveRoot_of_isAlgClosed h11
  obtain ⟨W, hWdef⟩ : ∃ W : Fin 11 → Submodule E V, ∀ k, W k = u.eigenspace (η ^ (k : ℕ)) :=
    ⟨fun k => u.eigenspace (η ^ (k : ℕ)), fun _ => rfl⟩
  have hW : ⨆ i, W i = ⊤ := (iSup_congr hWdef).trans (iSup_eigenspace_pow_eq_top hη h11 hu)
  have hsum : ∑ k : Fin 11, finrank E (W k) = finrank E V :=
    (Finset.sum_congr rfl fun k _ =>
      congrArg (fun X : Submodule E V => finrank E X) (hWdef k)).trans
        (sum_finrank_eigenspace_pow hη h11 hu)
  have hperp : ∀ k l : Fin 11, ∀ v ∈ W k, ∀ w ∈ W l, ¬ 11 ∣ (k : ℕ) + (l : ℕ) → B v w = 0 := by
    intro k l v hv w hw hkl
    rw [hWdef, Module.End.mem_eigenspace_iff] at hv
    rw [hWdef, Module.End.mem_eigenspace_iff] at hw
    refine l11_perp_of_eigen huB (a := η ^ (k : ℕ)) (b := η ^ (l : ℕ)) ?_ hv hw
    rw [← pow_add]
    intro h1
    exact hkl ((hη.pow_eq_one_iff_dvd _).mp h1)
  have hdual : ∀ k : Fin 11, finrank E (W k) ≤ finrank E (W (-k)) :=
    fun k => l11_finrank_le_neg hB hW hperp k
  have hinj : Function.Injective h := by
    intro a b hab
    have ha := Module.End.isUnit_inv_apply_apply_of_isUnit hh a
    have hb := Module.End.isUnit_inv_apply_apply_of_isUnit hh b
    rw [hab] at ha
    exact ha.symm.trans hb
  have hmap : ∀ i : Fin 11, ∀ v ∈ W i, h v ∈ W (4 * i) := by
    intro i v hv
    rw [hWdef] at hv
    rw [hWdef]
    exact l11_map_eigenspace hη hu hhu i hv
  have hdone := l11_dims_const hinj hmap hdual
  have hsplit : ∑ k : Fin 11, finrank E (W k) =
      finrank E (W 0) + ∑ k : Fin 10, finrank E (W k.succ) := Fin.sum_univ_succ _
  have hconst : ∑ k : Fin 10, finrank E (W k.succ) = 10 * finrank E (W 1) := by
    calc ∑ k : Fin 10, finrank E (W k.succ) = ∑ _k : Fin 10, finrank E (W 1) :=
          Finset.sum_congr rfl fun k _ => hdone k.succ (Fin.succ_ne_zero k)
      _ = 10 * finrank E (W 1) := by simp
  obtain ⟨k0, hk0, hne0⟩ := exists_eigenspace_ne_bot_of_ne_one hη h11 hu hu1
  have hW0 : W k0 ≠ ⊥ := by
    rw [hWdef]
    exact hne0
  have hk0' : k0 ≠ 0 := by
    rintro rfl
    exact hk0 rfl
  have hpos : finrank E (W 1) ≠ 0 := by
    rw [← hdone k0 hk0']
    exact fun h0 => hW0 (Submodule.finrank_eq_zero.mp h0)
  omega

theorem l11_card_of_alg {F E : Type} [Field F] [Field E] [IsAlgClosed E] (f : F →+* E)
    (hE : ringChar E ≠ 11) {ι : Type} [Fintype ι] [DecidableEq ι] (u h : Matrix ι ι F)
    (hu : u ^ 11 = 1) (hu1 : u ≠ 1) (hh : IsUnit h) (hhu : h * u = u ^ 3 * h)
    (Bm : Matrix ι ι F) (hBm : IsUnit Bm.det) (huB : uᵀ * Bm * u = Bm) :
    10 ≤ Fintype.card ι := by
  let ψ : Matrix ι ι F →+* Matrix ι ι E := RingHom.mapMatrix f
  let T : Matrix ι ι F →+* Module.End E (ι → E) :=
    (Matrix.toLinAlgEquiv' : Matrix ι ι E ≃ₐ[E] (ι → E) →ₗ[E] ι → E).toAlgHom.toRingHom.comp ψ
  have hTapp : ∀ (M : Matrix ι ι F) (v : ι → E), T M v = ψ M *ᵥ v := fun _ _ => rfl
  have hTinj : Function.Injective T := by
    intro a b hab
    have h1 : Matrix.toLinAlgEquiv' (ψ a) = Matrix.toLinAlgEquiv' (ψ b) := hab
    exact Matrix.map_injective f.injective (Matrix.toLinAlgEquiv'.injective h1)
  have hU : T u ^ 11 = 1 := by
    rw [← map_pow T u 11, hu, map_one]
  have hU1 : T u ≠ 1 := by
    intro h1
    apply hu1
    apply hTinj
    rw [h1, map_one]
  have hH : IsUnit (T h) := hh.map T
  have hHU : T h * T u = T u ^ 3 * T h := by
    rw [← map_mul, hhu, map_mul, map_pow]
  have hdet : IsUnit (ψ Bm).det := by
    have h1 := hBm.map f
    rwa [RingHom.map_det] at h1
  have hsurj : Function.Surjective (ψ Bm).mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr hdet)
  let Bf : (ι → E) →ₗ[E] (ι → E) →ₗ[E] E := Matrix.toBilin' (ψ Bm)
  have hBapp : ∀ v w : ι → E, Bf v w = v ⬝ᵥ (ψ Bm *ᵥ w) := fun v w =>
    Matrix.toBilin'_apply' (ψ Bm) v w
  have hB : ∀ v : ι → E, (∀ w, Bf v w = 0) → v = 0 := by
    intro v hv
    funext i
    obtain ⟨w, hw⟩ := hsurj (Pi.single i 1)
    have h1 := hv w
    rw [hBapp, hw, dotProduct_single, mul_one] at h1
    simpa using h1
  have hdot0 : ∀ (A : Matrix ι ι E) (v x : ι → E), (A *ᵥ v) ⬝ᵥ x = v ⬝ᵥ (Aᵀ *ᵥ x) := by
    intro A v x
    rw [dotProduct_comm (A *ᵥ v) x, dotProduct_mulVec, ← mulVec_transpose,
      dotProduct_comm (Aᵀ *ᵥ x) v]
  have hdot : ∀ (A C : Matrix ι ι E) (v w : ι → E),
      (A *ᵥ v) ⬝ᵥ (C *ᵥ (A *ᵥ w)) = v ⬝ᵥ (((Aᵀ * C) * A) *ᵥ w) := by
    intro A C v w
    rw [hdot0, mulVec_mulVec (A *ᵥ w) Aᵀ C, mulVec_mulVec w (Aᵀ * C) A]
  have hB2 : (ψ u)ᵀ * ψ Bm * ψ u = ψ Bm := by
    have h1 := congrArg (RingHom.mapMatrix f) huB
    simpa [ψ, ← Matrix.transpose_map] using h1
  have huB' : ∀ v w : ι → E, Bf (T u v) (T u w) = Bf v w := by
    intro v w
    rw [hTapp, hTapp, hBapp, hBapp, hdot, hB2]
  have key := ten_le_finrank_of_eleven_selfDual hE (T u) (T h) hU hU1 hH hHU Bf hB huB'
  rw [Module.finrank_fintype_fun_eq_card] at key
  exact key

theorem ten_le_card_of_eleven_selfDual {F : Type} [Field F] (hF : ringChar F ≠ 11) {ι : Type}
    [Fintype ι] [DecidableEq ι] (u h : Matrix ι ι F) (hu : u ^ 11 = 1) (hu1 : u ≠ 1)
    (hh : IsUnit h) (hhu : h * u = u ^ 3 * h) (Bm : Matrix ι ι F) (hBm : IsUnit Bm.det)
    (huB : uᵀ * Bm * u = Bm) : 10 ≤ Fintype.card ι := by
  have hchar : ringChar (AlgebraicClosure F) = ringChar F := by
    have : CharP (AlgebraicClosure F) (ringChar F) :=
      charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective (ringChar F)
    exact ringChar.eq (AlgebraicClosure F) (ringChar F)
  exact l11_card_of_alg (algebraMap F (AlgebraicClosure F)) (by rw [hchar]; exact hF) u h hu hu1
    hh hhu Bm hBm huB

end CFSG.ComponentClassification.CatFC.KGHS3
