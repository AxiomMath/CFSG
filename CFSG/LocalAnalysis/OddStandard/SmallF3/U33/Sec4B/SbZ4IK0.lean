module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {H : Type*} [Group H] [Finite H]

theorem z4i_map_eq_of_forall_mem {S : Type*} [Group S] [Finite S] (ρ : MulAut S)
    (N : Subgroup S) (hN : ∀ n ∈ N, ρ n ∈ N) : N.map ρ.toMonoidHom = N := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro x ⟨n, hn, rfl⟩
    exact hN n hn
  · rw [Subgroup.card_map_of_injective ρ.injective]

@[expose] noncomputable def z4i_quotAut {S : Type*} [Group S] (ρ : MulAut S) (N : Subgroup S)
    [N.Normal] (hN : N.map ρ.toMonoidHom = N) : MulAut (S ⧸ N) :=
  QuotientGroup.congr N N ρ hN

lemma z4i_quotAut_mk {S : Type*} [Group S] (ρ : MulAut S) (N : Subgroup S) [N.Normal]
    (hN : N.map ρ.toMonoidHom = N) (g : S) :
    z4i_quotAut ρ N hN (QuotientGroup.mk g) = QuotientGroup.mk (ρ g) := rfl

lemma z4i_quotAut_pow_three {S : Type*} [Group S] [Finite S] (ρ : MulAut S) (hρ : ρ ^ 3 = 1)
    (N : Subgroup S) [N.Normal] (hN : N.map ρ.toMonoidHom = N) :
    z4i_quotAut ρ N hN ^ 3 = 1 := by
  apply MulEquiv.ext
  intro x
  refine QuotientGroup.induction_on x ?_
  intro g
  have hf : ∀ k : ℕ, ∀ g : S, (z4i_quotAut ρ N hN ^ k) (QuotientGroup.mk g) =
      QuotientGroup.mk ((ρ ^ k) g) := by
    intro k
    induction k with
    | zero => intro g; rfl
    | succ k ih =>
      intro g
      rw [pow_succ, pow_succ, MulAut.mul_apply, z4i_quotAut_mk, ih, MulAut.mul_apply]
  rw [hf 3 g, hρ]
  rfl

theorem z4i_card_mod_three_of_fpf {S : Type*} [Group S] [Finite S] (ρ : MulAut S)
    (hρ : ρ ^ 3 = 1) (hfpf : ∀ g : S, ρ g = g → g = 1) (H : Subgroup S)
    (hH : ∀ h ∈ H, ρ h ∈ H) : Nat.card H % 3 = 1 := by
  classical
  haveI : Fintype H := Fintype.ofFinite H
  let f : Function.End H := fun h => ⟨ρ h, hH h h.2⟩
  have hf : ∀ k : ℕ, ∀ h : H, ((f ^ k) h : S) = (ρ ^ k) h := by
    intro k
    induction k with
    | zero => intro h; rfl
    | succ k ih =>
      intro h
      rw [pow_succ, pow_succ]
      show ((f ^ k) (f h) : S) = (ρ ^ k) (ρ h)
      rw [ih]
  have hf3 : f ^ 3 ^ 1 = 1 := by
    funext h
    apply Subtype.ext
    rw [pow_one, hf 3 h, hρ]
    rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 3) (n := 1) hf3
  have hfix : Fintype.card f.fixedPoints = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨1, Subtype.ext (map_one ρ)⟩, ?_⟩
    rintro ⟨y, hy⟩
    exact Subtype.ext (Subtype.ext (hfpf y (congrArg Subtype.val hy)))
  rw [Nat.card_eq_fintype_card]
  have h2 : Fintype.card f.fixedPoints % 3 = 1 := by simp [hfix]
  have h3 : Fintype.card H % 3 = Fintype.card f.fixedPoints % 3 := hmod
  omega


theorem z4i_mul_rho_rho_sq {S : Type*} [Group S] [Finite S] (ρ : MulAut S) (hρ : ρ ^ 3 = 1)
    (hfpf : ∀ g : S, ρ g = g → g = 1) (g : S) : g * ρ g * ρ (ρ g) = 1 := by
  have hρ3 : ∀ x : S, ρ (ρ (ρ x)) = x := by
    intro x
    have h := congrArg (fun f : MulAut S => f x) hρ
    simpa [pow_succ, MulAut.mul_apply] using h
  let c : S → S := fun x => x⁻¹ * ρ x
  have hc_inj : Function.Injective c := by
    intro p q hpq
    simp only [c] at hpq
    have h1 : q * p⁻¹ = ρ (q * p⁻¹) := by
      rw [map_mul, map_inv]
      calc q * p⁻¹ = q * (p⁻¹ * ρ p) * (ρ p)⁻¹ := by group
        _ = q * (q⁻¹ * ρ q) * (ρ p)⁻¹ := by rw [hpq]
        _ = ρ q * (ρ p)⁻¹ := by group
    have h2 := hfpf (q * p⁻¹) h1.symm
    exact (mul_inv_eq_one.mp h2).symm
  have hc_surj : Function.Surjective c := Finite.injective_iff_surjective.mp hc_inj
  have hc3 : ∀ x : S, c x * ρ (c x) * ρ (ρ (c x)) = 1 := by
    intro x
    simp only [c, map_mul, map_inv]
    rw [hρ3 x]
    group
  obtain ⟨w, hw⟩ := hc_surj g
  rw [← hw]
  exact hc3 w

@[expose] noncomputable def z4i_conjAut {S : Type*} [Group S] [Finite S] (ρ : S) (R : Subgroup S)
    (hR : ∀ x ∈ R, ρ * x * ρ⁻¹ ∈ R) : MulAut R :=
  let φ : R →* R :=
    { toFun := fun x => ⟨ρ * (x : S) * ρ⁻¹, hR x x.2⟩
      map_one' := by ext; simp
      map_mul' := by
        intro x y
        ext
        change ρ * ((x : S) * (y : S)) * ρ⁻¹ =
          (ρ * (x : S) * ρ⁻¹) * (ρ * (y : S) * ρ⁻¹)
        group }
  MulEquiv.ofBijective φ
    (Function.Injective.bijective_of_finite (f := φ) fun x y hxy => by
      apply Subtype.ext
      exact mul_left_cancel (mul_right_cancel (congrArg Subtype.val hxy)))

lemma z4i_conjAut_apply {S : Type*} [Group S] [Finite S] (ρ : S) (R : Subgroup S)
    (hR : ∀ x ∈ R, ρ * x * ρ⁻¹ ∈ R) (x : R) :
    ((z4i_conjAut ρ R hR x : R) : S) = ρ * (x : S) * ρ⁻¹ :=
  rfl

lemma z4i_conjAut_fpf {S : Type*} [Group S] [Finite S] (ρ : S) (R : Subgroup S)
    (hR : ∀ x ∈ R, ρ * x * ρ⁻¹ ∈ R) (hfpf : ∀ x ∈ R, ρ * x * ρ⁻¹ = x → x = 1) :
    ∀ x : R, z4i_conjAut ρ R hR x = x → x = 1 := by
  intro x hx
  apply Subtype.ext
  have h : ρ * (x : S) * ρ⁻¹ = (x : S) := by
    rw [← z4i_conjAut_apply ρ R hR x, hx]
  exact hfpf x x.2 h

lemma z4i_conjAut_pow_three {S : Type*} [Group S] [Finite S] (ρ : S) (R : Subgroup S)
    (hR : ∀ x ∈ R, ρ * x * ρ⁻¹ ∈ R) (hρ3 : ρ ^ 3 = 1) :
    z4i_conjAut ρ R hR ^ 3 = 1 := by
  refine MulEquiv.ext fun x => Subtype.ext ?_
  simp only [pow_succ, MulAut.mul_apply, z4i_conjAut_apply]
  calc ρ * (ρ * (ρ * (x : S) * ρ⁻¹) * ρ⁻¹) * ρ⁻¹
      = (ρ * ρ * ρ) * (x : S) * (ρ * ρ * ρ)⁻¹ := by group
    _ = ρ ^ 3 * (x : S) * (ρ ^ 3)⁻¹ := by rw [← pow_three']
    _ = (x : S) := by rw [hρ3]; simp

lemma z4i_card_eq_sixteen_of {n : ℕ} (h16 : 16 ∣ n) (h64 : n ∣ 64) (h3 : n % 3 = 1)
    (hne : n ≠ 64) : n = 16 := by
  obtain ⟨m, rfl⟩ := h16
  have hm4 : m ∣ 4 := by
    have h1 : 16 * m ∣ 16 * 4 := by
      rw [show (16 : ℕ) * 4 = 64 by norm_num]
      exact h64
    exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 16)).mp h1
  have hmle : m ≤ 4 := Nat.le_of_dvd (by norm_num) hm4
  have hmpos : 0 < m := Nat.pos_of_dvd_of_pos hm4 (by norm_num)
  interval_cases m
  · norm_num
  · exfalso; norm_num at h3
  · exact absurd hm4 (by norm_num)
  · exact absurd (by norm_num : 16 * 4 = 64) hne

lemma z4i_cover_of_card_four {T : Type*} [Group T] [Finite T] (hcard : Nat.card T = 4)
    (α : MulAut T) (hα3 : α ^ 3 = 1) (hfpf : ∀ t : T, α t = t → t = 1)
    {t : T} (ht : t ≠ 1) (x : T) : x = 1 ∨ x = t ∨ x = α t ∨ x = α (α t) := by
  classical
  haveI : Fintype T := Fintype.ofFinite T
  have hα3' : ∀ y : T, α (α (α y)) = y := by
    intro y
    have h := congrArg (fun f : MulAut T => f y) hα3
    simpa [pow_succ, MulAut.mul_apply] using h
  have hαt1 : α t ≠ 1 := fun h => ht (α.injective (by rw [h]; exact (map_one α).symm))
  have hα2t1 : α (α t) ≠ 1 := fun h =>
    hαt1 (α.injective (by rw [h]; exact (map_one α).symm))
  have htαt : t ≠ α t := fun h => ht (hfpf t h.symm)
  have htα2t : t ≠ α (α t) := fun h =>
    htαt ((congrArg α h).trans (hα3' t)).symm
  have hαtα2t : α t ≠ α (α t) := fun h => htαt (α.injective h)
  let f : Fin 4 → T := ![1, t, α t, α (α t)]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [f] at hij <;>
      first
      | rfl
      | exact absurd hij ht
      | exact absurd hij.symm ht
      | exact absurd hij hαt1
      | exact absurd hij.symm hαt1
      | exact absurd hij hα2t1
      | exact absurd hij.symm hα2t1
      | exact absurd hij htαt
      | exact absurd hij.symm htαt
      | exact absurd hij htα2t
      | exact absurd hij.symm htα2t
      | exact absurd hij hαtα2t
      | exact absurd hij.symm hαtα2t
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr
      ⟨hf, by rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]; exact hcard.symm⟩
  obtain ⟨i, hi⟩ := hbij.2 x
  fin_cases i
  · left; simpa [f] using hi.symm
  · right; left; simpa [f] using hi.symm
  · right; right; left; simpa [f] using hi.symm
  · right; right; right; simpa [f] using hi.symm

structure ZIKData (Q Y V V' B K : Subgroup H) (ρ : H) : Prop where
  Q_comm : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a
  card_Q : Nat.card Q = 64
  cent_Q : ∀ g : H, (∀ q ∈ Q, g * q = q * g) → g ∈ Q
  Q_le_K : Q ≤ K
  relIndex_K : Q.relIndex K = 4
  Q_eq : Q = B ⊔ V'
  B_le_Q : B ≤ Q
  Y_le_Q : Y ≤ Q
  Y_eq : Y = V ⊔ V'
  V_inf_V' : V ⊓ V' = ⊥
  card_V : Nat.card V = 4
  card_V' : Nat.card V' = 4
  sq_mem_V : ∀ q ∈ Q, q ^ 2 ∈ V
  K_cent_Y : ∀ k ∈ K, ∀ y ∈ Y, k * y = y * k
  comm_KQ : ∀ k ∈ K, ∀ q ∈ Q, k * q * k⁻¹ * q⁻¹ ∈ V
  rho_pow_three : ρ ^ 3 = 1
  rho_norm_Q : ∀ x ∈ Q, ρ * x * ρ⁻¹ ∈ Q
  rho_norm_Y : ∀ x ∈ Y, ρ * x * ρ⁻¹ ∈ Y
  rho_norm_V : ∀ x ∈ V, ρ * x * ρ⁻¹ ∈ V
  rho_norm_V' : ∀ x ∈ V', ρ * x * ρ⁻¹ ∈ V'
  rho_norm_B : ∀ x ∈ B, ρ * x * ρ⁻¹ ∈ B
  rho_norm_K : ∀ x ∈ K, ρ * x * ρ⁻¹ ∈ K
  rho_fpf_Q : ∀ q ∈ Q, ρ * q * ρ⁻¹ = q → q = 1
  rho_fpf_KQ : ∀ k ∈ K, ρ * k * ρ⁻¹ * k⁻¹ ∈ Q → k ∈ Q

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
