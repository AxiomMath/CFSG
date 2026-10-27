module

public import Mathlib.LinearAlgebra.Matrix.Module
public import CFSG.FeitThompson.Representations.PrimeOrderDetOneDistinctEigenlines
public import CFSG.FeitThompson.Representations.TrivialDeterminantKernelAbelianOrder

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Matrix Module Pointwise Polynomial MatrixGroups

variable {n : Type*} [Fintype n] {E : Type*} [Field E]

theorem exists_mem_ne_zero_of_finrank_eq_one {W : Submodule E (n → E)} (hW : finrank E ↥W = 1) :
    ∃ w ∈ W, w ≠ 0 := by
  refine (Submodule.ne_bot_iff W).mp fun h => ?_
  rw [h] at hW; simp at hW

theorem exists_forall_mulVec_eq_smul {M : Matrix n n E} {W : Submodule E (n → E)}
    (hW : finrank E ↥W = 1) (hMW : ∀ v ∈ W, M *ᵥ v ∈ W) :
    ∃ c : E, ∀ v ∈ W, M *ᵥ v = c • v := by
  obtain ⟨w, hw, hw0⟩ := exists_mem_ne_zero_of_finrank_eq_one hW
  have hWs : W = E ∙ w := eq_span_singleton_of_mem_of_finrank_eq_one hW hw hw0
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hWs ▸ hMW w hw)
  exact ⟨c, fun v hv => by
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (hWs ▸ hv)
    rw [← ht, Matrix.mulVec_smul, ← hc, smul_comm]⟩

theorem mem_of_mulVec_eq_smul {X : Matrix n n E} {a b : E} (hab : a ≠ b)
    {W₁ W₂ : Submodule E (n → E)} (hcompl : IsCompl W₁ W₂)
    (h₁ : ∀ v ∈ W₁, X *ᵥ v = a • v) (h₂ : ∀ v ∈ W₂, X *ᵥ v = b • v)
    {w : n → E} (hc : X *ᵥ w = a • w) : w ∈ W₁ := by
  have hmem : w ∈ W₁ ⊔ W₂ := hcompl.sup_eq_top ▸ Submodule.mem_top
  obtain ⟨u₁, hu₁, u₂, hu₂, hsum⟩ := Submodule.mem_sup.mp hmem
  have h : a • u₁ + b • u₂ = a • u₁ + a • u₂ := by
    have h : X *ᵥ (u₁ + u₂) = a • (u₁ + u₂) := by rw [hsum]; exact hc
    rwa [Matrix.mulVec_add, h₁ u₁ hu₁, h₂ u₂ hu₂, smul_add] at h
  have hu2 : u₂ = 0 := by
    rcases smul_eq_zero.mp (show (a - b) • u₂ = 0 by
      rw [sub_smul, sub_eq_zero]; exact (add_left_cancel h).symm) with h | h
    · exact absurd (sub_eq_zero.mp h) hab
    · exact h
  rw [← hsum, hu2, add_zero]; exact hu₁

theorem eq_of_mulVec_eqOn_span {M N : Matrix n n E} {s : Set (n → E)}
    (hs : Submodule.span E s = ⊤) (h : ∀ v ∈ s, M *ᵥ v = N *ᵥ v) : M = N := by
  have hl : M.mulVecLin = N.mulVecLin := LinearMap.ext_on hs h
  classical
  ext i j
  have h2 := congrFun (congrFun (congrArg (fun (f : (n → E) →ₗ[E] (n → E)) v => f v) hl)
    (Pi.single j 1)) i
  simpa [Matrix.mulVec_single] using h2

variable [DecidableEq n]

theorem coe_glMap {k : Type*} [Field k] (φ : k →+* E) (g : GL n k) :
    (Matrix.GeneralLinearGroup.map φ g : Matrix n n E) = (g : Matrix n n k).map φ := rfl

theorem glMap_injective {k : Type*} [Field k] {φ : k →+* E} (hφ : Function.Injective φ) :
    Function.Injective (Matrix.GeneralLinearGroup.map (n := n) φ) := fun g h hgh =>
  Units.ext (Matrix.map_injective hφ
    (show (g : Matrix n n k).map φ = (h : Matrix n n k).map φ by
      rw [← coe_glMap, ← coe_glMap, hgh]))

theorem glSMul_eq_map (M : GL n E) (W : Submodule E (n → E)) :
    M • W = W.map (Matrix.mulVecLin (M : Matrix n n E)) := rfl

theorem mem_glSMul_iff {M : GL n E} {W : Submodule E (n → E)} {v : n → E} :
    v ∈ M • W ↔ ∃ w ∈ W, (M : Matrix n n E) *ᵥ w = v := by
  rw [glSMul_eq_map, Submodule.mem_map]; rfl

theorem mulVec_mem_glSMul {M : GL n E} {W : Submodule E (n → E)} {v : n → E} (hv : v ∈ W) :
    (M : Matrix n n E) *ᵥ v ∈ M • W :=
  mem_glSMul_iff.mpr ⟨v, hv, rfl⟩

theorem mulVec_mem_of_glSMul_eq_self {M : GL n E} {W : Submodule E (n → E)} (h : M • W = W)
    {v : n → E} (hv : v ∈ W) : (M : Matrix n n E) *ᵥ v ∈ W := h ▸ mulVec_mem_glSMul hv

theorem finrank_glSMul (M : GL n E) (W : Submodule E (n → E)) :
    finrank E ↥(M • W) = finrank E ↥W := by
  rw [glSMul_eq_map]
  exact LinearEquiv.finrank_map_eq
    (LinearMap.GeneralLinearGroup.toLinearEquiv (Matrix.GeneralLinearGroup.toLin M)) W

theorem pow_glSMul_eq_self {M : GL n E} {W : Submodule E (n → E)} (h : M • W = W) (j : ℕ) :
    M ^ j • W = W := by
  induction j with
  | zero => rw [pow_zero, one_smul]
  | succ j ih => rw [pow_succ, mul_smul, h, ih]

theorem eq_of_odd_of_glSMul_swap {M : GL n E} {W₁ W₂ : Submodule E (n → E)} {m : ℕ}
    (hm : Odd m) (hM : M ^ m = 1) (h₁ : M • W₁ = W₂) (h₂ : M • W₂ = W₁) : W₁ = W₂ := by
  obtain ⟨t, ht⟩ := hm
  have hsq : (M ^ 2) • W₁ = W₁ := by rw [pow_two, mul_smul, h₁, h₂]
  have key : M • W₁ = W₁ := by
    have hMe : M = (M ^ 2) ^ (t + 1) := by
      rw [← pow_mul, show 2 * (t + 1) = m + 1 by omega, pow_succ, hM, one_mul]
    rw [hMe, pow_glSMul_eq_self hsq]
  rw [← h₁, key]

theorem mulVec_pow_eq_smul_pow {M : Matrix n n E} {v : n → E} {c : E} (h : M *ᵥ v = c • v)
    (m : ℕ) : (M ^ m) *ᵥ v = c ^ m • v := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, h,
      smul_smul, pow_succ', mul_comm]

theorem glSMul_eq_self_of_commute {X M : GL n E} {a b : E} (hab : a ≠ b)
    {W₁ W₂ : Submodule E (n → E)} (hcompl : IsCompl W₁ W₂) (hW₁ : finrank E ↥W₁ = 1)
    (h₁ : ∀ v ∈ W₁, (X : Matrix n n E) *ᵥ v = a • v)
    (h₂ : ∀ v ∈ W₂, (X : Matrix n n E) *ᵥ v = b • v)
    (hcomm : X * M = M * X) : M • W₁ = W₁ := by
  refine Submodule.eq_of_le_of_finrank_eq (fun v hv => ?_) (by rw [finrank_glSMul, hW₁])
  obtain ⟨w, hw, rfl⟩ := mem_glSMul_iff.mp hv
  refine mem_of_mulVec_eq_smul hab hcompl h₁ h₂ ?_
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, hcomm, Units.val_mul,
    ← Matrix.mulVec_mulVec, h₁ w hw, Matrix.mulVec_smul]

theorem mulVec_mul_comm_of_glSMul_eq_self {M N : GL n E} {W : Submodule E (n → E)}
    (hW : finrank E ↥W = 1) (hM : M • W = W) (hN : N • W = W) (v : n → E) (hv : v ∈ W) :
    ((M * N : GL n E) : Matrix n n E) *ᵥ v = ((N * M : GL n E) : Matrix n n E) *ᵥ v := by
  obtain ⟨cM, hcM⟩ := exists_forall_mulVec_eq_smul hW (fun _ => mulVec_mem_of_glSMul_eq_self hM)
  obtain ⟨cN, hcN⟩ := exists_forall_mulVec_eq_smul hW (fun _ => mulVec_mem_of_glSMul_eq_self hN)
  rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    hcM v hv, hcN v hv, Matrix.mulVec_smul, Matrix.mulVec_smul, hcM v hv, hcN v hv,
    smul_smul, smul_smul, mul_comm]

theorem forall_mulVec_eq_self_of_pow_char {p : ℕ} (hp : p.Prime) [CharP E p] {M : GL n E}
    {W : Submodule E (n → E)} (hW : finrank E ↥W = 1) (hM : M • W = W) (hMp : M ^ p = 1)
    (v : n → E) (hv : v ∈ W) : (M : Matrix n n E) *ᵥ v = v := by
  obtain ⟨c, hc⟩ := exists_forall_mulVec_eq_smul hW (fun _ => mulVec_mem_of_glSMul_eq_self hM)
  obtain ⟨w, hw, hw0⟩ := exists_mem_ne_zero_of_finrank_eq_one hW
  have hcp : c ^ p = 1 := by
    have h1 : ((M : Matrix n n E) ^ p) *ᵥ w = c ^ p • w := mulVec_pow_eq_smul_pow (hc w hw) p
    rw [← Units.val_pow_eq_pow_val, hMp, Units.val_one, Matrix.one_mulVec] at h1
    have h2 : (c ^ p - 1) • w = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
    rcases smul_eq_zero.mp h2 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hw0
  have : Fact p.Prime := ⟨hp⟩
  have hc1 : c = 1 := by
    have h3 : (c - 1) ^ p = 0 := by rw [sub_pow_char, hcp, one_pow, sub_self]
    exact sub_eq_zero.mp ((pow_eq_zero_iff hp.ne_zero).mp h3)
  rw [hc v hv, hc1, one_smul]

theorem eq_of_forall_mulVec_eq {M N : GL n E} {W₁ W₂ : Submodule E (n → E)}
    (hsup : W₁ ⊔ W₂ = ⊤)
    (h₁ : ∀ v ∈ W₁, (M : Matrix n n E) *ᵥ v = (N : Matrix n n E) *ᵥ v)
    (h₂ : ∀ v ∈ W₂, (M : Matrix n n E) *ᵥ v = (N : Matrix n n E) *ᵥ v) : M = N :=
  Units.ext <| eq_of_mulVec_eqOn_span
    (s := (W₁ : Set (n → E)) ∪ (W₂ : Set (n → E)))
    (by rw [Submodule.span_union, Submodule.span_eq, Submodule.span_eq, hsup])
    (fun v hv => hv.elim (h₁ v) (h₂ v))

section Main

variable {k : Type u} [Field k] [Finite k] {p r : ℕ}

theorem isMulCommutative_and_not_dvd_of_normal_abelian_prime_action [CharP k p] (hp : p.Prime)
    (hr : r.Prime) (hrodd : Odd r) (hrp : r ≠ p) {G K : Subgroup (GL (Fin 2) k)}
    (hGodd : Odd (Nat.card G)) (hKG : K ≤ G) (hKnorm : (K.subgroupOf G).Normal) (hK1 : K ≠ ⊥)
    (hKab : IsMulCommutative K)
    (hKSL : K ≤ (Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := k)).range)
    (hKr : ∀ y ∈ K, y ≠ 1 → orderOf y = r) :
    IsMulCommutative G ∧ ¬ p ∣ Nat.card G := by
  classical
  obtain ⟨x₀, hx₀ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hK1
  have hx₀K : (x₀ : GL (Fin 2) k) ∈ K := x₀.2
  have hx₀1 : (x₀ : GL (Fin 2) k) ≠ 1 := fun h => hx₀ne (Subtype.ext h)
  obtain ⟨x, hxx₀⟩ := hKSL hx₀K
  have hxord : orderOf x = r := by
    have h := hKr _ hx₀K hx₀1
    rwa [← hxx₀, orderOf_injective _ Matrix.SpecialLinearGroup.toGL_injective] at h
  obtain ⟨E, _, _, _, hinj, _, a, b, hab, _, W₁, W₂, hW12, hW1, hW2, hcompl, hE₁, hE₂,
    hlines⟩ := exists_finiteField_natCard_eq_or_and_two_invariant_lines k hr hrodd hrp x hxord
  have hEp : CharP E p := charP_of_injective_algebraMap hinj p
  set ψ : GL (Fin 2) k →* GL (Fin 2) E := Matrix.GeneralLinearGroup.map (algebraMap k E) with hψ
  have hψcoe : ∀ g : GL (Fin 2) k, (ψ g : Matrix (Fin 2) (Fin 2) E) =
      (g : Matrix (Fin 2) (Fin 2) k).map (algebraMap k E) := fun _ => rfl
  have hψinj : Function.Injective ψ := glMap_injective hinj
  set X : GL (Fin 2) E := ψ (x₀ : GL (Fin 2) k) with hX
  have hXcoe : (X : Matrix (Fin 2) (Fin 2) E) =
      (x : Matrix (Fin 2) (Fin 2) k).map (algebraMap k E) := by
    rw [hX, ← hxx₀, hψcoe, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
  have hX₁ : ∀ v ∈ W₁, (X : Matrix (Fin 2) (Fin 2) E) *ᵥ v = a • v := by
    intro v hv; rw [hXcoe]; exact hE₁ v hv
  have hX₂ : ∀ v ∈ W₂, (X : Matrix (Fin 2) (Fin 2) E) *ᵥ v = b • v := by
    intro v hv; rw [hXcoe]; exact hE₂ v hv
  have hKstab : ∀ y ∈ K, ψ y • W₁ = W₁ ∧ ψ y • W₂ = W₂ := by
    intro y hy
    have hcomm : (x₀ : GL (Fin 2) k) * y = y * (x₀ : GL (Fin 2) k) :=
      congrArg Subtype.val (hKab.is_comm.comm (⟨_, hx₀K⟩ : K) ⟨y, hy⟩)
    have hXcomm : X * ψ y = ψ y * X := by rw [hX, ← map_mul, ← map_mul, hcomm]
    exact ⟨glSMul_eq_self_of_commute hab hcompl hW1 hX₁ hX₂ hXcomm,
      glSMul_eq_self_of_commute hab.symm hcompl.symm hW2 hX₂ hX₁ hXcomm⟩
  have hKinv : ∀ W : Submodule E (Fin 2 → E), finrank E ↥W = 1 →
      (∀ y ∈ K, ψ y • W = W) → W = W₁ ∨ W = W₂ := by
    intro W hW hWK
    refine hlines W hW fun v hv => ?_
    have h := mulVec_mem_of_glSMul_eq_self (hWK _ hx₀K) hv
    rwa [← hX, hXcoe] at h
  have hconjstab : ∀ g ∈ G, ∀ W : Submodule E (Fin 2 → E), (∀ y ∈ K, ψ y • W = W) →
      ∀ y ∈ K, ψ y • (ψ g • W) = ψ g • W := by
    intro g hg W hWK y hy
    have hyK : (⟨y, hKG hy⟩ : G) ∈ K.subgroupOf G := (Subgroup.mem_subgroupOf).mpr hy
    have hconj : g⁻¹ * y * g ∈ K := by
      have := hKnorm.conj_mem _ hyK (⟨g, hg⟩ : G)⁻¹
      simpa [Subgroup.mem_subgroupOf] using this
    calc ψ y • (ψ g • W) = (ψ y * ψ g) • W := (mul_smul _ _ _).symm
      _ = (ψ g * ψ (g⁻¹ * y * g)) • W := by rw [← map_mul, ← map_mul]; group
      _ = ψ g • (ψ (g⁻¹ * y * g) • W) := mul_smul _ _ _
      _ = ψ g • W := by rw [hWK _ hconj]
  have hGperm₁ : ∀ g ∈ G, ψ g • W₁ = W₁ ∨ ψ g • W₁ = W₂ := fun g hg =>
    hKinv _ (by rw [finrank_glSMul, hW1]) (hconjstab g hg W₁ fun y hy => (hKstab y hy).1)
  have hGperm₂ : ∀ g ∈ G, ψ g • W₂ = W₁ ∨ ψ g • W₂ = W₂ := fun g hg =>
    hKinv _ (by rw [finrank_glSMul, hW2]) (hconjstab g hg W₂ fun y hy => (hKstab y hy).2)
  have hGstab : ∀ g ∈ G, ψ g • W₁ = W₁ ∧ ψ g • W₂ = W₂ := by
    intro g hg
    have hpow : ψ g ^ Nat.card G = 1 := by
      have h : (⟨g, hg⟩ : G) ^ Nat.card G = 1 := pow_card_eq_one'
      have h2 : g ^ Nat.card G = 1 := congrArg (Subtype.val : G → GL (Fin 2) k) h
      rw [← map_pow, h2, map_one]
    rcases hGperm₁ g hg with h₁ | h₁
    · refine ⟨h₁, ?_⟩
      rcases hGperm₂ g hg with h₂ | h₂
      · exact absurd (smul_left_cancel (ψ g) (h₂.trans h₁.symm)) (Ne.symm hW12)
      · exact h₂
    · exfalso
      have h₂ : ψ g • W₂ = W₁ := by
        rcases hGperm₂ g hg with h₂ | h₂
        · exact h₂
        · exact absurd (smul_left_cancel (ψ g) (h₁.trans h₂.symm)) hW12
      exact hW12 (eq_of_odd_of_glSMul_swap hGodd hpow h₁ h₂)
  have hGab : IsMulCommutative G := by
    refine .of_comm fun u v => Subtype.ext (hψinj ?_)
    change ψ ((u : GL (Fin 2) k) * (v : GL (Fin 2) k)) = ψ ((v : GL (Fin 2) k) * u)
    rw [map_mul, map_mul]
    exact eq_of_forall_mulVec_eq hcompl.sup_eq_top
      (mulVec_mul_comm_of_glSMul_eq_self hW1 (hGstab _ u.2).1 (hGstab _ v.2).1)
      (mulVec_mul_comm_of_glSMul_eq_self hW2 (hGstab _ u.2).2 (hGstab _ v.2).2)
  refine ⟨hGab, fun hdvd => ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hgord⟩ := exists_prime_orderOf_dvd_card' (G := G) p hdvd
  have hgp : (g : GL (Fin 2) k) ^ p = 1 := by
    have h : g ^ p = 1 := by rw [← hgord]; exact pow_orderOf_eq_one g
    exact congrArg (Subtype.val : G → GL (Fin 2) k) h
  have hψgp : ψ (g : GL (Fin 2) k) ^ p = 1 := by rw [← map_pow, hgp, map_one]
  have hone : ψ (g : GL (Fin 2) k) = 1 := by
    refine eq_of_forall_mulVec_eq hcompl.sup_eq_top (fun v hv => ?_) (fun v hv => ?_)
    · rw [Units.val_one, Matrix.one_mulVec]
      exact forall_mulVec_eq_self_of_pow_char hp hW1 (hGstab _ g.2).1 hψgp v hv
    · rw [Units.val_one, Matrix.one_mulVec]
      exact forall_mulVec_eq_self_of_pow_char hp hW2 (hGstab _ g.2).2 hψgp v hv
  have hg1 : g = 1 := Subtype.ext (hψinj (by rw [hone]; exact (map_one ψ).symm))
  rw [hg1, orderOf_one] at hgord
  exact hp.one_lt.ne hgord

theorem isMulCommutative_and_not_dvd_of_normal_abelian_prime_action_card {f q : ℕ}
    (hp : p.Prime) (_hf : 1 ≤ f) (hq : q = p ^ f) (hcard : Nat.card k = q)
    (hr : r.Prime) (hrodd : Odd r) (hrp : r ≠ p) {G K : Subgroup (GL (Fin 2) k)}
    (hGodd : Odd (Nat.card G)) (hKG : K ≤ G) (hKnorm : (K.subgroupOf G).Normal) (hK1 : K ≠ ⊥)
    (hKab : IsMulCommutative K)
    (hKSL : K ≤ (Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := k)).range)
    (hKr : ∀ y ∈ K, y ≠ 1 → orderOf y = r) :
    IsMulCommutative G ∧ ¬ p ∣ Nat.card G :=
  have : CharP k p := charP_of_natCard_eq_prime_pow hp (by rw [hcard, hq])
  isMulCommutative_and_not_dvd_of_normal_abelian_prime_action hp hr hrodd hrp hGodd hKG hKnorm
    hK1 hKab hKSL hKr

end Main

end CFSG.FeitThompson
