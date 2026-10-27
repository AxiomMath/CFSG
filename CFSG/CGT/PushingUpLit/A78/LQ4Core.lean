module

public import CFSG.CGT.PushingUpLit.A78.LQ4Space
public import CFSG.CGT.PushingUpLit.A78.LQ4Count
public import CFSG.LocalAnalysis.OddStandard.Harada75Rank
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.CGT.PushingUpLit.A78.LQ4

open CFSG.CGT.PushingUpLit.A78.LQ4Fin
open scoped commutatorElement

variable {S : Type*} [Group S] {J : Subgroup S} [J.Normal]

namespace Coords

variable (c : Coords ↥J)

theorem ker_conj (s : S) {j : ↥J} (hj : c.ε j = 1) : c.ε (MulAut.conjNormal s j) = 1 := by
  have hj' : j ∈ Subgroup.center ↥J := by rw [← c.ker_eq]; exact hj
  have : MulAut.conjNormal s j ∈ Subgroup.center ↥J := by
    rw [Subgroup.mem_center_iff] at hj' ⊢
    intro g
    have h := hj' ((MulAut.conjNormal s).symm g)
    calc g * (MulAut.conjNormal s) j
        = (MulAut.conjNormal s) ((MulAut.conjNormal s).symm g * j) := by simp
      _ = (MulAut.conjNormal s) (j * (MulAut.conjNormal s).symm g) := by rw [h]
      _ = (MulAut.conjNormal s) j * g := by simp
  rw [← c.ker_eq] at this
  exact this

@[expose] noncomputable def rho (s : S) : Bits 4 →* Bits 4 :=
  (MonoidHom.liftOfSurjective c.ε c.surj)
    ⟨c.ε.comp (MulAut.conjNormal s).toMonoidHom, fun j hj => by
      have hj' : c.ε j = 1 := hj
      show c.ε (MulAut.conjNormal s j) = 1
      exact c.ker_conj s hj'⟩

theorem rho_apply (s : S) (j : ↥J) : c.rho s (c.ε j) = c.ε (MulAut.conjNormal s j) := by
  simp [rho]

theorem rho_mul (s t : S) : c.rho (s * t) = (c.rho s).comp (c.rho t) := by
  ext v
  obtain ⟨j, rfl⟩ := c.surj v
  simp [rho_apply, map_mul]

theorem rho_one : c.rho 1 = MonoidHom.id _ := by
  ext v
  obtain ⟨j, rfl⟩ := c.surj v
  simp [rho_apply]

omit [J.Normal] in
theorem sq_mem (j : ↥J) : j ^ 2 ∈ c.ε.ker := by
  rw [MonoidHom.mem_ker, map_pow]; exact Bits.sq_eq_one _

omit [J.Normal] in
theorem qB_eq (j : ↥J) : qB (c.ε j) = c.η ⟨j ^ 2, c.sq_mem j⟩ :=
  Subtype.ext (c.sq j (c.sq_mem j)).symm

@[expose] noncomputable def Rend : S →* Monoid.End (Bits 4) where
  toFun s := c.rho s
  map_one' := c.rho_one
  map_mul' s t := c.rho_mul s t

@[expose] noncomputable def Rg : S →* (Monoid.End (Bits 4))ˣ := c.Rend.toHomUnits

theorem rho_trivial_of_mem {s : S} (hs : s ∈ J) : c.rho s = MonoidHom.id _ := by
  ext v
  obtain ⟨j, rfl⟩ := c.surj v
  rw [c.rho_apply]
  have : (MulAut.conjNormal s) j = ⟨s, hs⟩ * j * ⟨s, hs⟩⁻¹ :=
    Subtype.ext (by simp [MulAut.conjNormal_apply])
  rw [this, map_mul, map_mul, map_inv, mul_comm (c.ε ⟨s, hs⟩), mul_inv_cancel_right]
  rfl

theorem ker_Rg (hF4 : ∀ s : S, (∀ j : ↥J, c.ε (MulAut.conjNormal s j) = c.ε j) → s ∈ J) :
    c.Rg.ker = J := by
  ext s
  constructor
  · intro hs
    have h1 : c.Rg s = 1 := hs
    have h2 : c.rho s = MonoidHom.id _ := by
      have := congrArg Units.val h1
      exact this
    refine hF4 s fun j => ?_
    have := DFunLike.congr_fun h2 (c.ε j)
    rw [c.rho_apply] at this
    exact this
  · intro hs
    show c.Rg s = 1
    refine Units.ext ?_
    exact c.rho_trivial_of_mem hs

@[expose] noncomputable def Ax (s : S) : List ℕ := colsOf (c.rho s)

theorem Ax_mul (s t : S) : c.Ax (s * t) = mul (c.Ax s) (c.Ax t) := by
  simp only [Ax, rho_mul, colsOf_comp]

theorem rho_injective (s : S) : Function.Injective (c.rho s) := by
  have h : (c.rho s⁻¹).comp (c.rho s) = MonoidHom.id _ := by
    rw [← c.rho_mul, inv_mul_cancel, c.rho_one]
  intro a b hab
  have := congrArg (c.rho s⁻¹) hab
  have e : ∀ x, c.rho s⁻¹ (c.rho s x) = x := fun x => DFunLike.congr_fun h x
  rwa [e, e] at this

@[expose] noncomputable def tau (s : S) : c.ε.ker →* c.ε.ker :=
  ((MulAut.conjNormal s).toMonoidHom.comp c.ε.ker.subtype).codRestrict c.ε.ker
    (fun z => c.ker_conj s (MonoidHom.mem_ker.1 z.2))

theorem tau_val (s : S) (z : c.ε.ker) : ((c.tau s z : c.ε.ker) : ↥J) = MulAut.conjNormal s z :=
  rfl

theorem tau_injective (s : S) : Function.Injective (c.tau s) := by
  intro a b h
  have h1 := congrArg Subtype.val h
  rw [tau_val, tau_val] at h1
  exact Subtype.ext ((MulAut.conjNormal s).injective h1)

@[expose] noncomputable def gamma (s : S) : Bits 2 →* Bits 2 :=
  c.η.toMonoidHom.comp ((c.tau s).comp c.η.symm.toMonoidHom)

theorem gamma_injective (s : S) : Function.Injective (c.gamma s) := by
  intro a b h
  have h1 : c.η (c.tau s (c.η.symm a)) = c.η (c.tau s (c.η.symm b)) := h
  have h2 := c.tau_injective s (c.η.injective h1)
  exact c.η.symm.injective h2

theorem gamma_qB (s : S) (v : Bits 4) : c.gamma s (qB v) = qB (c.rho s v) := by
  obtain ⟨j, rfl⟩ := c.surj v
  rw [c.rho_apply, c.qB_eq, c.qB_eq]
  have : c.tau s ⟨j ^ 2, c.sq_mem j⟩ = ⟨(MulAut.conjNormal s j) ^ 2, c.sq_mem _⟩ :=
    Subtype.ext (by rw [tau_val]; simp)
  show c.η (c.tau s (c.η.symm (c.η ⟨j ^ 2, c.sq_mem j⟩))) = _
  rw [MulEquiv.symm_apply_apply, this]

theorem Ax_mem_A0 (s : S) : c.Ax s ∈ A0 :=
  colsOf_mem_A0 (c.rho s) (c.rho_injective s) (c.gamma s) (c.gamma_injective s) (c.gamma_qB s)

theorem Rend_pow_six (x : S) : c.Rend x ^ 6 = 1 := by
  refine Monoid.End.ext (M := Bits 4) fun v => ?_
  have hA := A0_pow6 (c.Ax x) (c.Ax_mem_A0 x) v.1 v.lt16
  have e : ∀ w : Bits 4, mulVec (c.Ax x) w.1 = (c.rho x w).1 := fun w => mulVec_colsOf (c.rho x) w
  simp only [iter6, e] at hA
  show (⇑(c.Rend x))^[6] v = v
  exact Subtype.ext hA

theorem Rend_sq (hS : IsPGroup 2 S) (x : S) : c.Rend x ^ 2 = 1 := by
  obtain ⟨k, hk⟩ := hS x
  have h6 := c.Rend_pow_six x
  have h2k : c.Rend x ^ (2 ^ k) = 1 := by rw [← map_pow, hk, map_one]
  have hg : c.Rend x ^ Nat.gcd 6 (2 ^ k) = 1 := pow_gcd_eq_one.2 ⟨h6, h2k⟩
  have hd : Nat.gcd 6 (2 ^ k) ∣ 2 := by
    have hc : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
    have : Nat.gcd (2 ^ k) (2 * 3) = Nat.gcd (2 ^ k) 2 * Nat.gcd (2 ^ k) 3 :=
      Nat.Coprime.gcd_mul _ (by norm_num)
    rw [Nat.gcd_comm, show (6 : ℕ) = 2 * 3 from rfl, this, hc]
    simpa using Nat.gcd_dvd_right (2 ^ k) 2
  obtain ⟨d, hd'⟩ := hd
  rw [hd', pow_mul, hg, one_pow]

theorem Rend_comm (hS : IsPGroup 2 S) (x y : S) : c.Rend x * c.Rend y = c.Rend y * c.Rend x := by
  have hx := c.Rend_sq hS x
  have hy := c.Rend_sq hS y
  have hxy := c.Rend_sq hS (x * y)
  rw [map_mul] at hxy
  set a := c.Rend x
  set b := c.Rend y
  have h1 : a * b * (a * b) = 1 := by rw [← pow_two]; exact hxy
  have h2 : a * a = 1 := by rw [← pow_two]; exact hx
  have h3 : b * b = 1 := by rw [← pow_two]; exact hy
  calc a * b = a * (a * b * (a * b)) * b := by rw [h1, mul_one]
    _ = (a * a) * b * a * (b * b) := by simp only [mul_assoc]
    _ = b * a := by rw [h2, h3]; simp

theorem Ax_involution (hS : IsPGroup 2 S) (x : S) : mul (c.Ax x) (c.Ax x) = idM := by
  rw [← c.Ax_mul]
  have h : c.rho (x * x) = MonoidHom.id (Bits 4) := by
    have := c.Rend_sq hS x
    rw [pow_two, ← map_mul] at this
    exact this
  rw [Ax, h, colsOf_id]

theorem Ax_comm (hS : IsPGroup 2 S) (x y : S) :
    mul (c.Ax x) (c.Ax y) = mul (c.Ax y) (c.Ax x) := by
  rw [← c.Ax_mul, ← c.Ax_mul]
  have : c.Rend (x * y) = c.Rend (y * x) := by
    rw [map_mul, map_mul]; exact c.Rend_comm hS x y
  exact congrArg colsOf this

theorem Ax_mem_invs (hS : IsPGroup 2 S) (x : S) : c.Ax x ∈ invs :=
  mem_invs.2 ⟨c.Ax_mem_A0 x, c.Ax_involution hS x⟩

theorem exists_two_gens (hS : IsPGroup 2 S) (X : Subgroup S) : ∃ x₁ ∈ X, ∃ x₂ ∈ X, ∀ x ∈ X,
    c.Ax x = idM ∨ c.Ax x = c.Ax x₁ ∨ c.Ax x = c.Ax x₂ ∨
      c.Ax x = mul (c.Ax x₁) (c.Ax x₂) := by
  by_cases h1 : ∀ x ∈ X, c.Ax x = idM
  · exact ⟨1, X.one_mem, 1, X.one_mem, fun x hx => Or.inl (h1 x hx)⟩
  push Not at h1
  obtain ⟨x₁, hx₁, hne₁⟩ := h1
  by_cases h2 : ∀ x ∈ X, c.Ax x = idM ∨ c.Ax x = c.Ax x₁
  · refine ⟨x₁, hx₁, 1, X.one_mem, fun x hx => ?_⟩
    rcases h2 x hx with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  push Not at h2
  obtain ⟨x₂, hx₂, hne₂, hne₂'⟩ := h2
  refine ⟨x₁, hx₁, x₂, hx₂, fun x hx => ?_⟩
  have := rank2 (c.Ax x₁) (c.Ax_mem_invs hS x₁) hne₁ (c.Ax x₂) (c.Ax_mem_invs hS x₂) hne₂ hne₂'
    (c.Ax_comm hS x₁ x₂) (c.Ax x) (c.Ax_mem_invs hS x) (c.Ax_comm hS x₁ x) (c.Ax_comm hS x₂ x)
  exact this

theorem relIndex_le (hF4 : ∀ s : S, (∀ j : ↥J, c.ε (MulAut.conjNormal s j) = c.ε j) → s ∈ J)
    (X : Subgroup S) (x₁ x₂ : S)
    (h : ∀ x ∈ X, c.Ax x = idM ∨ c.Ax x = c.Ax x₁ ∨ c.Ax x = c.Ax x₂ ∨
      c.Ax x = mul (c.Ax x₁) (c.Ax x₂)) : J.relIndex X ≤ pOf (c.Ax x₁) (c.Ax x₂) := by
  classical
  have e : J.relIndex X = Nat.card (X.map c.Rg) := by
    have := Subgroup.relIndex_ker (f := c.Rg) (K := X)
    rwa [c.ker_Rg hF4] at this
  rw [e]
  set L : List (List ℕ) := [idM, c.Ax x₁, c.Ax x₂, mul (c.Ax x₁) (c.Ax x₂)] with hL
  have hmem : ∀ u : ↥(X.map c.Rg), colsOf ((u.1 : (Monoid.End (Bits 4))ˣ) : Monoid.End (Bits 4)) ∈
      L.toFinset := by
    intro u
    obtain ⟨x, hx, hxu⟩ := Subgroup.mem_map.1 u.2
    rw [List.mem_toFinset, hL, ← hxu]
    have e1 : colsOf ((c.Rg x : (Monoid.End (Bits 4))ˣ) : Monoid.End (Bits 4)) = c.Ax x := rfl
    rw [e1]
    simpa [List.mem_cons] using h x hx
  let φ : ↥(X.map c.Rg) → ↥L.toFinset := fun u => ⟨_, hmem u⟩
  have hφ : Function.Injective φ := by
    intro u v huv
    have h1 : colsOf ((u.1 : (Monoid.End (Bits 4))ˣ) : Monoid.End (Bits 4)) =
        colsOf ((v.1 : (Monoid.End (Bits 4))ˣ) : Monoid.End (Bits 4)) := congrArg Subtype.val huv
    exact Subtype.ext (Units.ext (colsOf_injective h1))
  calc Nat.card ↥(X.map c.Rg) ≤ Nat.card ↥L.toFinset := Nat.card_le_card_of_injective φ hφ
    _ = L.toFinset.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ pOf (c.Ax x₁) (c.Ax x₂) := by
      have e : L.toFinset = L.eraseDups.toFinset := by
        ext a; simp [List.mem_eraseDups]
      rw [e]
      exact List.toFinset_card_le _

theorem comm_val (x : S) (n : ↥J) :
    ((n * (MulAut.conjNormal x n)⁻¹ : ↥J) : S) = ⁅(n : S), x⁆ := by
  simp [commutatorElement_def]
  group

theorem eps_comm (x : S) (n : ↥J) :
    c.ε (n * (MulAut.conjNormal x n)⁻¹) = c.ε n * c.rho x (c.ε n) := by
  rw [map_mul, map_inv, ← c.rho_apply]
  rfl

theorem rho_val (x : S) (v : Bits 4) : (c.rho x v).1 = mulVec (c.Ax x) v.1 :=
  (mulVec_colsOf (c.rho x) v).symm

theorem mem_commList {A₁ A₂ : List ℕ} {m w : ℕ} : w ∈ commList A₁ A₂ m ↔
    ∃ v ∈ members m, w = mulVec A₁ v ^^^ v ∨ w = mulVec A₂ v ^^^ v := by
  simp [commList, List.mem_flatMap]

theorem card_C (X : Subgroup S) (x₁ x₂ : S) {m : ℕ}
    (hmbit : ∀ w, w < 16 → (m.testBit w = true ↔
      dec4 w ∈ Subgroup.map c.ε ((X ⊓ J).subgroupOf J))) :
    Nat.card (Subgroup.map c.ε (Subgroup.closure
      {j : ↥J | ∃ n ∈ (X ⊓ J).subgroupOf J, ∃ x ∈ [x₁, x₂], (j : S) = ⁅(n : S), x⁆})) =
      popc (spanMask (commList (c.Ax x₁) (c.Ax x₂) m)) := by
  classical
  rw [MonoidHom.map_closure]
  have hv : ∀ v, v ∈ members m ↔ v < 16 ∧ ∃ n ∈ (X ⊓ J).subgroupOf J, c.ε n = dec4 v := by
    intro v
    rw [mem_members]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, Subgroup.mem_map.1 ((hmbit v h1).1 h2)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (hmbit v h1).2 (Subgroup.mem_map.2 h2)⟩
  have hA : ∀ x ∈ [x₁, x₂], c.Ax x ∈ A0 := fun x _ => c.Ax_mem_A0 x
  refine card_closure (l := commList (c.Ax x₁) (c.Ax x₂) m) ?_ ?_
  · intro y hy
    obtain ⟨v, hvm, h | h⟩ := mem_commList.1 hy
    · have hv16 := ((hv v).1 hvm).1
      rw [h]; exact xor_lt16 (mulVec_lt (c.Ax_mem_A0 x₁) v hv16) hv16
    · have hv16 := ((hv v).1 hvm).1
      rw [h]; exact xor_lt16 (mulVec_lt (c.Ax_mem_A0 x₂) v hv16) hv16
  · intro w
    constructor
    · rintro ⟨j, ⟨n, hn, x, hx, hjn⟩, rfl⟩
      have hj : j = n * (MulAut.conjNormal x n)⁻¹ := Subtype.ext (by rw [hjn, comm_val])
      rw [hj, c.eps_comm, Bits.val_mul, c.rho_val]
      have hvm : (c.ε n).1 ∈ members m :=
        (hv _).2 ⟨(c.ε n).lt16, n, hn, by rw [dec4_val']⟩
      refine mem_commList.2 ⟨(c.ε n).1, hvm, ?_⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact Or.inl (Nat.xor_comm _ _)
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact Or.inr (Nat.xor_comm _ _)
        · simp at hx
    · intro hw
      obtain ⟨v, hvm, h⟩ := mem_commList.1 hw
      obtain ⟨hv16, n, hn, hnv⟩ := (hv v).1 hvm
      have real : ∀ x ∈ [x₁, x₂], w.1 = mulVec (c.Ax x) v ^^^ v → w ∈ c.ε '' {j : ↥J | ∃ n ∈
          (X ⊓ J).subgroupOf J, ∃ x ∈ [x₁, x₂], (j : S) = ⁅(n : S), x⁆} := by
        intro x hx hwx
        refine ⟨n * (MulAut.conjNormal x n)⁻¹, ⟨n, hn, x, hx, comm_val x n⟩, ?_⟩
        apply Subtype.ext
        rw [c.eps_comm, Bits.val_mul, c.rho_val, hwx, hnv, dec4_val hv16, Nat.xor_comm]
      rcases h with h | h
      · exact real x₁ (by simp) h
      · exact real x₂ (by simp) h

omit [J.Normal] in
theorem members_iff (X : Subgroup S) {m : ℕ}
    (hmbit : ∀ w, w < 16 → (m.testBit w = true ↔
      dec4 w ∈ Subgroup.map c.ε ((X ⊓ J).subgroupOf J))) (v : ℕ) :
    v ∈ members m ↔ v < 16 ∧ ∃ n ∈ (X ⊓ J).subgroupOf J, c.ε n = dec4 v := by
  rw [mem_members]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, Subgroup.mem_map.1 ((hmbit v h1).1 h2)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (hmbit v h1).2 (Subgroup.mem_map.2 h2)⟩

omit [J.Normal] in
theorem card_Q (X : Subgroup S) {m : ℕ}
    (hmbit : ∀ w, w < 16 → (m.testBit w = true ↔
      dec4 w ∈ Subgroup.map c.ε ((X ⊓ J).subgroupOf J))) :
    Nat.card (Subgroup.closure {j : ↥J | ∃ n ∈ (X ⊓ J).subgroupOf J, j = n ^ 2}) =
      popc (spanMask (qList m)) := by
  classical
  set N := (X ⊓ J).subgroupOf J with hN
  set K := c.ε.ker with hK
  let ψ : ↥K →* Bits 4 := incl.comp c.η.toMonoidHom
  have hψ : Function.Injective ψ := fun a b h => c.η.injective (incl_injective h)
  let Q0set : Set ↥K := {z | ∃ n ∈ N, (z : ↥J) = n ^ 2}
  have h1 : Subgroup.closure {j : ↥J | ∃ n ∈ N, j = n ^ 2} =
      (Subgroup.closure Q0set).map K.subtype := by
    rw [MonoidHom.map_closure]
    congr 1
    ext j
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨n ^ 2, c.sq_mem n⟩, ⟨n, hn, rfl⟩, rfl⟩
    · rintro ⟨z, ⟨n, hn, hz⟩, rfl⟩
      exact ⟨n, hn, hz⟩
  have h2 : Nat.card (Subgroup.closure {j : ↥J | ∃ n ∈ N, j = n ^ 2}) =
      Nat.card (Subgroup.closure (ψ '' Q0set)) := by
    rw [h1, Subgroup.card_map_of_injective K.subtype_injective, ← MonoidHom.map_closure,
      Subgroup.card_map_of_injective hψ]
  rw [h2]
  refine card_closure (l := qList m) ?_ ?_
  · intro y hy
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hy
    have := qv_lt v (mem_members.1 hv).1
    omega
  · intro w
    constructor
    · rintro ⟨z, ⟨n, hn, hz⟩, rfl⟩
      have hz' : z = ⟨n ^ 2, c.sq_mem n⟩ := Subtype.ext hz
      have hvm : (c.ε n).1 ∈ members m :=
        (c.members_iff X hmbit _).2 ⟨(c.ε n).lt16, n, hn, by rw [dec4_val']⟩
      refine List.mem_map.2 ⟨(c.ε n).1, hvm, ?_⟩
      show qv (c.ε n).1 = (incl (c.η z)).1
      rw [incl_val, hz', c.sq]
    · intro hw
      obtain ⟨v, hv, hvw⟩ := List.mem_map.1 hw
      obtain ⟨hv16, n, hn, hnv⟩ := (c.members_iff X hmbit v).1 hv
      refine ⟨⟨n ^ 2, c.sq_mem n⟩, ⟨n, hn, rfl⟩, ?_⟩
      apply Subtype.ext
      show (incl (c.η ⟨n ^ 2, c.sq_mem n⟩)).1 = w.1
      rw [incl_val, c.sq, hnv, dec4_val hv16, hvw]

omit [J.Normal] in
theorem card_ker : Nat.card c.ε.ker = 4 := by
  rw [Nat.card_congr c.η.toEquiv, Bits.card_eq]
  norm_num

theorem card_le_sixteen [Finite S] (hS : IsPGroup 2 S)
    (hF4 : ∀ s : S, (∀ j : ↥J, c.ε (MulAut.conjNormal s j) = c.ε j) → s ∈ J)
    (X Y : Subgroup S) (hYX : Y ≤ X) (hsq : ∀ x ∈ X, x ^ 2 ∈ Y)
    (hcomm : ∀ x ∈ X, ∀ y ∈ X, ⁅x, y⁆ ∈ Y) : Nat.card X ≤ 16 * Nat.card Y := by
  classical
  obtain ⟨x₁, hx₁, x₂, hx₂, hgen⟩ := c.exists_two_gens hS X
  obtain ⟨m, hm, hmbit⟩ := exists_mask (Subgroup.map c.ε ((X ⊓ J).subgroupOf J))
  have hNbar : Nat.card (Subgroup.map c.ε ((X ⊓ J).subgroupOf J)) = popc m :=
    card_eq_popc _ hmbit
  have hinv : ∀ x ∈ X, invariantB (c.Ax x) m = true := by
    intro x hx
    rw [invariantB_iff]
    intro v hv hbit
    obtain ⟨n, hn, hnv⟩ := Subgroup.mem_map.1 ((hmbit v hv).1 hbit)
    have e : mulVec (c.Ax x) v = (c.rho x (dec4 v)).1 := by rw [c.rho_val, dec4_val hv]
    have hw16 : mulVec (c.Ax x) v < 16 := by rw [e]; exact (c.rho x (dec4 v)).lt16
    refine (hmbit _ hw16).2 ?_
    rw [e, dec4_val', ← hnv, c.rho_apply]
    refine Subgroup.mem_map.2 ⟨MulAut.conjNormal x n, ?_, rfl⟩
    have hnX : (n : S) ∈ X := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hn)).1
    rw [Subgroup.mem_subgroupOf, MulAut.conjNormal_apply]
    exact Subgroup.mem_inf.2
      ⟨X.mul_mem (X.mul_mem hx hnX) (X.inv_mem hx), (MulAut.conjNormal x n).2⟩
  have hb := main_bound m hm (c.Ax x₁) (c.Ax_mem_invs hS x₁) (hinv x₁ hx₁) (c.Ax x₂)
    (c.Ax_mem_invs hS x₂) (hinv x₂ hx₂) (c.Ax_comm hS x₁ x₂)
  have hb' : pOf (c.Ax x₁) (c.Ax x₂) * popc m * 4 ≤
      16 * popc (spanMask (commList (c.Ax x₁) (c.Ax x₂) m)) * popc (spanMask (qList m)) :=
    of_decide_eq_true hb
  have hcount := card_mul_le_of_elementarySection J c.ε (fun k => Bits.sq_eq_one k) X Y hYX hsq
    hcomm [x₁, x₂] (by simp [hx₁, hx₂])
  rw [c.card_C X x₁ x₂ hmbit, c.card_Q X hmbit, hNbar, c.card_ker] at hcount
  have hidx := c.relIndex_le hF4 X x₁ x₂ hgen
  have hCpos : 0 < popc (spanMask (commList (c.Ax x₁) (c.Ax x₂) m)) := by
    rw [← c.card_C X x₁ x₂ hmbit]; exact Nat.card_pos
  have hQpos : 0 < popc (spanMask (qList m)) := by
    rw [← c.card_Q X hmbit]; exact Nat.card_pos
  set C := popc (spanMask (commList (c.Ax x₁) (c.Ax x₂) m))
  set Q := popc (spanMask (qList m))
  have h1 : Nat.card X * (C * Q) ≤ (16 * Nat.card Y) * (C * Q) := by
    calc Nat.card X * (C * Q) = Nat.card X * C * Q := by ring
      _ ≤ Nat.card Y * J.relIndex X * popc m * 4 := hcount
      _ ≤ Nat.card Y * pOf (c.Ax x₁) (c.Ax x₂) * popc m * 4 := by gcongr
      _ = Nat.card Y * (pOf (c.Ax x₁) (c.Ax x₂) * popc m * 4) := by ring
      _ ≤ Nat.card Y * (16 * C * Q) := by gcongr
      _ = (16 * Nat.card Y) * (C * Q) := by ring
  exact Nat.le_of_mul_le_mul_right h1 (Nat.mul_pos hCpos hQpos)

end Coords

theorem noE32_of_coords [Finite S] (hS : IsPGroup 2 S) (c : Coords ↥J)
    (hF4 : ∀ s : S, (∀ j : ↥J, c.ε (MulAut.conjNormal s j) = c.ε j) → s ∈ J) :
    CFSG.OddStandard.Harada75.NoE32 S := by
  intro X Y hXY
  obtain ⟨hYX, hsq, hcomm, hcard⟩ := hXY
  have h := c.card_le_sixteen hS hF4 X Y hYX hsq hcomm
  have hpos : 0 < Nat.card Y := Nat.card_pos
  omega

end CFSG.CGT.PushingUpLit.A78.LQ4
