module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchBits
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchCode
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.EvenSmallLie.OmegaEight.SpBranch

structure KCoord where
  n : ℕ
  lin : ℕ → ℕ
  co : ℕ → ℕ

@[expose] def KCoord.In (K : KCoord) (c : ℕ) : Prop := K.co c < 2 ^ K.n ∧ K.lin (K.co c) = c

structure KFacts (N : ℕ) (mul : ℕ → ℕ → ℕ) (K : KCoord) : Prop where
  lin_lt : ∀ v, v < 2 ^ K.n → K.lin v < N
  co_lin : ∀ v, v < 2 ^ K.n → K.co (K.lin v) = v
  lin_xor : ∀ v w, v < 2 ^ K.n → w < 2 ^ K.n → K.lin (v ^^^ w) = mul (K.lin v) (K.lin w)
  self_cent : ∀ c, c < N → (∀ j, j < K.n → mul c (K.lin (2 ^ j)) = mul (K.lin (2 ^ j)) c) →
    K.In c

namespace KFacts

variable {H : Type*} [Group H] {N : ℕ} {mul : ℕ → ℕ → ℕ} {K : KCoord}
  (hK : KFacts N mul K) (Φ : CodeIso H N mul)

include hK in
theorem in_lin {v : ℕ} (hv : v < 2 ^ K.n) : K.In (K.lin v) := by
  refine ⟨?_, ?_⟩ <;> rw [hK.co_lin v hv]
  exact hv

@[expose] noncomputable def el (K : KCoord) (v : ℕ) : H := Φ.g (K.lin v)

include hK in
theorem f_el {v : ℕ} (hv : v < 2 ^ K.n) : Φ.f (el Φ K v) = K.lin v :=
  Φ.f_g (hK.lin_lt v hv)

include hK in
theorem el_xor {v w : ℕ} (hv : v < 2 ^ K.n) (hw : w < 2 ^ K.n) :
    el Φ K (v ^^^ w) = el Φ K v * el Φ K w := by
  apply Φ.inj
  rw [Φ.map_mul, hK.f_el Φ hv, hK.f_el Φ hw, hK.f_el Φ (Nat.xor_lt_two_pow hv hw),
    hK.lin_xor v w hv hw]

include hK in
theorem el_comm {v w : ℕ} (hv : v < 2 ^ K.n) (hw : w < 2 ^ K.n) :
    el Φ K v * el Φ K w = el Φ K w * el Φ K v := by
  rw [← hK.el_xor Φ hv hw, ← hK.el_xor Φ hw hv, Nat.xor_comm]

@[expose] def Mem (K : KCoord) (x : H) : Prop := K.In (Φ.f x)

include hK in
theorem mem_iff {x : H} : Mem Φ K x ↔ ∃ v, v < 2 ^ K.n ∧ x = el Φ K v := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨K.co (Φ.f x), h1, Φ.inj (by rw [hK.f_el Φ h1, h2])⟩
  · rintro ⟨v, hv, rfl⟩
    unfold Mem
    rw [hK.f_el Φ hv]
    exact hK.in_lin hv

include hK in
theorem mem_comm {x y : H} (hx : Mem Φ K x) (hy : Mem Φ K y) : x * y = y * x := by
  obtain ⟨v, hv, rfl⟩ := (hK.mem_iff Φ).1 hx
  obtain ⟨w, hw, rfl⟩ := (hK.mem_iff Φ).1 hy
  exact hK.el_comm Φ hv hw

include hK in
theorem mem_of_comm {x : H} (hx : ∀ j, j < K.n → x * el Φ K (2 ^ j) = el Φ K (2 ^ j) * x) :
    Mem Φ K x := by
  refine hK.self_cent _ (Φ.lt x) fun j hj => ?_
  have h2 : 2 ^ j < 2 ^ K.n := Nat.pow_lt_pow_right Nat.one_lt_two hj
  rw [← hK.f_el Φ h2, ← Φ.map_mul, ← Φ.map_mul, hx j hj]

omit hK in
theorem char_of_Y {Y : List ℕ} (hYlt : ∀ y ∈ Y, y < N)
    (hY : ∀ γ : H ≃* H, ∀ y ∈ Y, Φ.f (γ (Φ.g y)) ∈ Y)
    (hC : ∀ c, c < N → ((∀ y ∈ Y, mul c y = mul y c) ↔ K.In c))
    (γ : H ≃* H) {x : H} (hx : Mem Φ K x) : Mem Φ K (γ x) := by
  have hxY : ∀ y ∈ Y, x * Φ.g y = Φ.g y * x := by
    intro y hy
    apply Φ.inj
    rw [Φ.map_mul, Φ.map_mul, Φ.f_g (hYlt y hy)]
    exact (hC _ (Φ.lt x)).2 hx y hy
  refine (hC _ (Φ.lt _)).1 fun y hy => ?_
  have hy' : Φ.f (γ.symm (Φ.g y)) ∈ Y := hY γ.symm y hy
  have hcomm := hxY _ hy'
  rw [Φ.g_f] at hcomm
  have := congrArg γ hcomm
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at this
  rw [← Φ.f_g (hYlt y hy), ← Φ.map_mul, ← Φ.map_mul, this]

variable (hchar : ∀ γ : H ≃* H, ∀ x : H, Mem Φ K x → Mem Φ K (γ x))

@[expose] noncomputable def psi (K : KCoord) (γ : H ≃* H) (v : ℕ) : ℕ := K.co (Φ.f (γ (el Φ K v)))

include hK hchar in
theorem psi_lt (γ : H ≃* H) {v : ℕ} (hv : v < 2 ^ K.n) : psi Φ K γ v < 2 ^ K.n :=
  (hchar γ _ ((hK.mem_iff Φ).2 ⟨v, hv, rfl⟩)).1

include hK hchar in
theorem el_psi (γ : H ≃* H) {v : ℕ} (hv : v < 2 ^ K.n) : el Φ K (psi Φ K γ v) = γ (el Φ K v) := by
  apply Φ.inj
  rw [hK.f_el Φ (hK.psi_lt Φ hchar γ hv)]
  exact (hchar γ _ ((hK.mem_iff Φ).2 ⟨v, hv, rfl⟩)).2

include hK hchar in
theorem psi_xor (γ : H ≃* H) {v w : ℕ} (hv : v < 2 ^ K.n) (hw : w < 2 ^ K.n) :
    psi Φ K γ (v ^^^ w) = psi Φ K γ v ^^^ psi Φ K γ w := by
  have hvw := Nat.xor_lt_two_pow hv hw
  have hp := Nat.xor_lt_two_pow (hK.psi_lt Φ hchar γ hv) (hK.psi_lt Φ hchar γ hw)
  have h1 := hK.el_psi Φ hchar γ hvw
  rw [hK.el_xor Φ hv hw, map_mul, ← hK.el_psi Φ hchar γ hv, ← hK.el_psi Φ hchar γ hw,
    ← hK.el_xor Φ (hK.psi_lt Φ hchar γ hv) (hK.psi_lt Φ hchar γ hw)] at h1
  have := congrArg Φ.f h1
  rw [hK.f_el Φ (hK.psi_lt Φ hchar γ hvw), hK.f_el Φ hp] at this
  have h2 := congrArg K.co this
  rwa [hK.co_lin _ (hK.psi_lt Φ hchar γ hvw), hK.co_lin _ hp] at h2

include hK hchar in
theorem psi_eq_xorBits (γ : H ≃* H) {v : ℕ} (hv : v < 2 ^ K.n) :
    psi Φ K γ v = xorBits K.n (fun j => psi Φ K γ (2 ^ j)) v :=
  eq_xorBits (fun _ _ ha hb => hK.psi_xor Φ hchar γ ha hb) hv

end KFacts

end CFSG.EvenSmallLie.OmegaEight.SpBranch
