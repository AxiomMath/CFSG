module

public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.LinearAlgebra.Matrix.Notation

public section

namespace CFSG.CGT.PushingUpLit.T2KR.Model613

open DihedralGroup
open scoped commutatorElement

abbrev N0 := Fin 5 → Multiplicative (ZMod 2)

def Mu : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1,0,0,1,1; 0,1,1,1,0; 0,0,1,0,0; 0,0,0,1,0; 0,0,0,0,1]
def Mb : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1,1,0,0,0; 0,1,0,0,0; 0,0,1,1,0; 0,0,0,1,0; 0,0,0,0,1]

def Md : DihedralGroup 4 → Matrix (Fin 5) (Fin 5) (ZMod 2)
  | r i => (Mu * Mb) ^ i.val
  | sr i => Mu * (Mu * Mb) ^ i.val

theorem Md_mul : ∀ a b : DihedralGroup 4, Md (a * b) = Md a * Md b := by decide +kernel

theorem Md_one : Md 1 = 1 := by decide +kernel

def actv (A : Matrix (Fin 5) (Fin 5) (ZMod 2)) (q : N0) : N0 :=
  fun i => Multiplicative.ofAdd ((A.mulVec (fun j => (q j).toAdd)) i)

theorem actv_actv (A B : Matrix (Fin 5) (Fin 5) (ZMod 2)) (q : N0) :
    actv A (actv B q) = actv (A * B) q := by
  funext i
  simp only [actv, toAdd_ofAdd, Matrix.mulVec_mulVec]

theorem actv_one (q : N0) : actv 1 q = q := by
  funext i
  simp [actv]

theorem actv_mul (A : Matrix (Fin 5) (Fin 5) (ZMod 2)) (q q' : N0) :
    actv A (q * q') = actv A q * actv A q' := by
  funext i
  have h : (fun j => Multiplicative.toAdd (q j * q' j)) =
      (fun j => Multiplicative.toAdd (q j)) + fun j => Multiplicative.toAdd (q' j) := by
    funext j; exact toAdd_mul _ _
  simp only [actv, Pi.mul_apply, h, Matrix.mulVec_add, Pi.add_apply, ofAdd_add]

def autd (d : DihedralGroup 4) : MulAut N0 where
  toFun := actv (Md d)
  invFun := actv (Md d⁻¹)
  left_inv q := by
    rw [actv_actv, ← Md_mul, inv_mul_cancel, Md_one, actv_one]
  right_inv q := by
    rw [actv_actv, ← Md_mul, mul_inv_cancel, Md_one, actv_one]
  map_mul' := actv_mul _

@[expose] def phi0 : DihedralGroup 4 →* MulAut N0 where
  toFun := autd
  map_one' := by
    ext q : 1
    show actv (Md 1) q = q
    rw [Md_one, actv_one]
  map_mul' a b := by
    ext q : 1
    show actv (Md (a * b)) q = actv (Md a) (actv (Md b) q)
    rw [Md_mul, actv_actv]

abbrev T0 := N0 ⋊[phi0] DihedralGroup 4

instance decEqT0 : DecidableEq T0 := fun a b =>
  decidable_of_iff (a.left = b.left ∧ a.right = b.right)
    ⟨fun h => SemidirectProduct.ext h.1 h.2, fun h => ⟨h ▸ rfl, h ▸ rfl⟩⟩

instance : Fintype T0 := Fintype.ofEquiv (N0 × DihedralGroup 4) SemidirectProduct.equivProd.symm

@[expose] def e (i : Fin 5) : T0 :=
  SemidirectProduct.inl (Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod 2)))
@[expose] def dd (d : DihedralGroup 4) : T0 := SemidirectProduct.inr d

theorem card_N0 : Nat.card N0 = 32 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_T0 : Nat.card T0 = 256 := by
  rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod, card_N0, DihedralGroup.nat_card]

@[expose] def sg (i : Fin 5) : N0 := Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod 2))

theorem phi_u0 : phi0 (sr 0) (sg 0) = sg 0 := by decide +kernel
theorem phi_u1 : phi0 (sr 0) (sg 1) = sg 1 := by decide +kernel
theorem phi_u2 : phi0 (sr 0) (sg 2) = sg 1 * sg 2 := by decide +kernel
theorem phi_u3 : phi0 (sr 0) (sg 3) = sg 0 * sg 1 * sg 3 := by decide +kernel
theorem phi_u4 : phi0 (sr 0) (sg 4) = sg 0 * sg 4 := by decide +kernel
theorem phi_b0 : phi0 (sr 1) (sg 0) = sg 0 := by decide +kernel
theorem phi_b1 : phi0 (sr 1) (sg 1) = sg 0 * sg 1 := by decide +kernel
theorem phi_b2 : phi0 (sr 1) (sg 2) = sg 2 := by decide +kernel
theorem phi_b3 : phi0 (sr 1) (sg 3) = sg 2 * sg 3 := by decide +kernel
theorem phi_b4 : phi0 (sr 1) (sg 4) = sg 4 := by decide +kernel

def actTbl : Nat :=
  2 ^ 1024 * 0xc677aef3dfbda9594e304256a6b1cf3988510c20e77dfdeb38ad2f694e116b1e +
  2 ^ 768 * 0xe52d09214c718820d6f38f7fbcb5eb494e3052d2873dac31ca410c20ffbbcce3 +
  2 ^ 512 * 0x7aa56d794e1173d8d4254b290e618820d6f38ef3dfa56f69ca115a909635ee29 +
  2 ^ 256 * 0x0c710c20e77dfce37ab5e959ca30635cf4a16a31c8518820c677af7fbcad2d79 +
  0xca114a14b7b98d214e610c20ffbbcdeb38bdab49ca307b9ac5a928398a418820

def mulDTbl : Nat := 0xd1d6721ab3e4439f5688fac9f5443b3e21ad670d1fac688

def invDTbl : Nat := 0xfac298

def actQ (d q : Nat) : Nat := (actTbl >>> (5 * (32 * d + q))) &&& 31
def mulD (d d' : Nat) : Nat := (mulDTbl >>> (3 * (8 * d + d'))) &&& 7
def invD (d : Nat) : Nat := (invDTbl >>> (3 * d)) &&& 7

def mulT (c c' : Nat) : Nat :=
  ((c % 32) ^^^ actQ (c / 32) (c' % 32)) + 32 * mulD (c / 32) (c' / 32)

def invT (c : Nat) : Nat := actQ (invD (c / 32)) (c % 32) + 32 * invD (c / 32)

def commT (a b : Nat) : Nat := mulT (mulT (mulT a b) (invT a)) (invT b)

def qc (q : N0) : Nat :=
  (List.finRange 5).foldl (fun acc j => acc + (q j).toAdd.val * 2 ^ (j : Nat)) 0

def dc : DihedralGroup 4 → Nat
  | r i => i.val
  | sr i => 4 + i.val

def code (t : T0) : Nat := qc t.left + 32 * dc t.right

theorem qc_lt : ∀ q : N0, qc q < 32 := by decide +kernel
theorem dc_lt : ∀ d : DihedralGroup 4, dc d < 8 := by decide +kernel
theorem qc_mul : ∀ q q' : N0, qc (q * q') = qc q ^^^ qc q' := by decide +kernel
theorem qc_act : ∀ (d : DihedralGroup 4) (q : N0), qc (phi0 d q) = actQ (dc d) (qc q) := by
  decide +kernel
theorem dc_mul : ∀ d d' : DihedralGroup 4, dc (d * d') = mulD (dc d) (dc d') := by decide +kernel
theorem dc_inv : ∀ d : DihedralGroup 4, dc d⁻¹ = invD (dc d) := by decide +kernel
theorem qc_inv : ∀ q : N0, qc q⁻¹ = qc q := by decide +kernel
theorem qc_one : qc (1 : N0) = 0 := by decide +kernel
theorem qc_inj : ∀ q q' : N0, qc q = qc q' → q = q' := by decide +kernel
theorem dc_inj : ∀ d d' : DihedralGroup 4, dc d = dc d' → d = d' := by decide +kernel

theorem code_lt (t : T0) : code t < 256 := by
  unfold code
  have := qc_lt t.left
  have := dc_lt t.right
  omega

theorem code_mod (t : T0) : code t % 32 = qc t.left := by
  unfold code
  have := qc_lt t.left
  omega

theorem code_div (t : T0) : code t / 32 = dc t.right := by
  unfold code
  have := qc_lt t.left
  omega

theorem code_mul (a b : T0) : code (a * b) = mulT (code a) (code b) := by
  have h1 : code (a * b) = qc (a.left * phi0 a.right b.left) + 32 * dc (a.right * b.right) := rfl
  rw [h1, qc_mul, qc_act, dc_mul, mulT, code_mod, code_div, code_mod, code_div]

theorem code_inv (a : T0) : code a⁻¹ = invT (code a) := by
  have h1 : code a⁻¹ = qc (phi0 a.right⁻¹ a.left⁻¹) + 32 * dc a.right⁻¹ := rfl
  rw [h1, qc_act, qc_inv, dc_inv, invT, code_mod, code_div]

theorem code_one : code (1 : T0) = 0 := by
  have h1 : code (1 : T0) = qc (1 : N0) + 32 * dc (1 : DihedralGroup 4) := rfl
  rw [h1, qc_one]
  rfl

theorem code_inj {a b : T0} (h : code a = code b) : a = b := by
  have h1 : qc a.left = qc b.left := by rw [← code_mod a, h, code_mod]
  have h2 : dc a.right = dc b.right := by rw [← code_div a, h, code_div]
  exact SemidirectProduct.ext (qc_inj _ _ h1) (dc_inj _ _ h2)

theorem code_comm (a b : T0) : code ⁅a, b⁆ = commT (code a) (code b) := by
  rw [commutatorElement_def, code_mul, code_mul, code_mul, code_inv, code_inv, commT]

def allLt : Nat → (Nat → Bool) → Bool
  | 0, _ => true
  | n + 1, p => p n && allLt n p

theorem allLt_iff {n : Nat} {p : Nat → Bool} : allLt n p = true ↔ ∀ i < n, p i = true := by
  induction n with
  | zero => simp [allLt]
  | succ n ih =>
    simp only [allLt, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
      · exact h2 i h
      · exact h ▸ h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

def predSubgroup (p : Nat → Bool) (h1 : p 0 = true)
    (hmul : ∀ i < 256, ∀ j < 256, p i = true → p j = true → p (mulT i j) = true)
    (hinv : ∀ i < 256, p i = true → p (invT i) = true) : Subgroup T0 where
  carrier := {t | p (code t) = true}
  mul_mem' := fun {a b} ha hb => by
    show p (code (a * b)) = true
    rw [code_mul]
    exact hmul _ (code_lt a) _ (code_lt b) ha hb
  one_mem' := by
    show p (code 1) = true
    rw [code_one]
    exact h1
  inv_mem' := fun {a} ha => by
    show p (code a⁻¹) = true
    rw [code_inv]
    exact hinv _ (code_lt a) ha

theorem mem_predSubgroup {p h1 hmul hinv} {t : T0} :
    t ∈ predSubgroup p h1 hmul hinv ↔ p (code t) = true := Iff.rfl

def pN0 (c : Nat) : Bool :=
  !((c % 32).testBit 4) && (c / 32 == 0 || c / 32 == 2 || c / 32 == 4 || c / 32 == 6)

def pTh (c : Nat) : Bool :=
  !((c % 32).testBit 3) && !((c % 32).testBit 4) && (c / 32 == 0 || c / 32 == 2)

def chkSub (p : Nat → Bool) : Bool :=
  p 0 && (allLt 256 fun i => !p i || allLt 256 fun j => !p j || p (mulT i j)) &&
    allLt 256 fun i => !p i || p (invT i)

set_option maxHeartbeats 0 in
theorem chkSub_N0 : chkSub pN0 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem chkSub_Th : chkSub pTh = true := by decide +kernel

theorem chkSub_sound {p : Nat → Bool} (h : chkSub p = true) :
    p 0 = true ∧ (∀ i < 256, ∀ j < 256, p i = true → p j = true → p (mulT i j) = true) ∧
      ∀ i < 256, p i = true → p (invT i) = true := by
  simp only [chkSub, Bool.and_eq_true, allLt_iff] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  refine ⟨h0, fun i hi j hj hpi hpj => ?_, fun i hi hpi => ?_⟩
  · have := h1 i hi
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at this
    rcases this with h | h
    · simp [h] at hpi
    · have := (allLt_iff.1 (by simpa using h)) j hj
      simpa [hpj] using this
  · have := h2 i hi
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at this
    rcases this with h | h
    · simp [h] at hpi
    · exact h

def N00 : Subgroup T0 :=
  predSubgroup pN0 (chkSub_sound chkSub_N0).1 (chkSub_sound chkSub_N0).2.1
    (chkSub_sound chkSub_N0).2.2

def Th : Subgroup T0 :=
  predSubgroup pTh (chkSub_sound chkSub_Th).1 (chkSub_sound chkSub_Th).2.1
    (chkSub_sound chkSub_Th).2.2

theorem pN0_iff : ∀ (q : N0) (d : DihedralGroup 4),
    pN0 (qc q + 32 * dc d) = true ↔
      (q 4 = 1 ∧ (d = r 0 ∨ d = r 2 ∨ d = sr 0 ∨ d = sr 2)) := by decide +kernel

theorem mem_N00 {t : T0} : t ∈ N00 ↔
    t.left 4 = 1 ∧ (t.right = r 0 ∨ t.right = r 2 ∨ t.right = sr 0 ∨ t.right = sr 2) :=
  pN0_iff t.left t.right

set_option maxHeartbeats 0 in
theorem chk_Th_le_N0 : (allLt 256 fun i => !pTh i || pN0 i) = true := by decide +kernel

theorem Th_le_N00 : Th ≤ N00 := by
  intro t ht
  have := allLt_iff.1 chk_Th_le_N0 (code t) (code_lt t)
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at this
  rcases this with h | h
  · exact absurd ht (by simp [Th, mem_predSubgroup, h])
  · exact h

set_option maxHeartbeats 0 in
theorem chk_Th_normal : (allLt 256 fun n => !pTh n ||
    allLt 256 fun g => pTh (mulT (mulT g n) (invT g))) = true := by decide +kernel

instance Th_normal : Th.Normal where
  conj_mem n hn g := by
    have h1 := allLt_iff.1 chk_Th_normal (code n) (code_lt n)
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at h1
    rcases h1 with h | h
    · exact absurd hn (by simp [Th, mem_predSubgroup, h])
    · have := allLt_iff.1 (by simpa using h) (code g) (code_lt g)
      show pTh (code (g * n * g⁻¹)) = true
      rw [code_mul, code_mul, code_inv]
      exact this

def genX : Set T0 := {e 0, e 1, e 2, e 3, e 4, dd (sr 0), dd (sr 1)}

theorem inl_mem_closure (q : N0) : SemidirectProduct.inl q ∈ Subgroup.closure genX := by
  have hq : q = ∏ i, Pi.mulSingle i (q i) := (Finset.univ_prod_mulSingle q).symm
  have key : q ∈ (Subgroup.closure genX).comap (SemidirectProduct.inl : N0 →* T0) := by
    rw [hq]
    refine Subgroup.prod_mem _ fun i _ => ?_
    have h2 : q i = 1 ∨ q i = Multiplicative.ofAdd (1 : ZMod 2) := by
      generalize q i = a
      revert a
      decide
    rcases h2 with h | h
    · rw [h]; simp
    · rw [h, Subgroup.mem_comap]
      fin_cases i <;> exact Subgroup.subset_closure (by simp [genX, e])
  exact key

theorem inr_mem_closure (d : DihedralGroup 4) :
    SemidirectProduct.inr d ∈ Subgroup.closure genX := by
  have hs0 : dd (sr 0) ∈ Subgroup.closure genX := Subgroup.subset_closure (by simp [genX])
  have hs1 : dd (sr 1) ∈ Subgroup.closure genX := Subgroup.subset_closure (by simp [genX])
  have hr1 : dd (r 1) ∈ Subgroup.closure genX := by
    have : dd (r 1) = dd (sr 0) * dd (sr 1) := by decide
    rw [this]; exact Subgroup.mul_mem _ hs0 hs1
  have hr2 : dd (r 2) ∈ Subgroup.closure genX := by
    have : dd (r 2) = dd (r 1) * dd (r 1) := by decide
    rw [this]; exact Subgroup.mul_mem _ hr1 hr1
  have hr3 : dd (r 3) ∈ Subgroup.closure genX := by
    have : dd (r 3) = dd (r 2) * dd (r 1) := by decide
    rw [this]; exact Subgroup.mul_mem _ hr2 hr1
  have hs2 : dd (sr 2) ∈ Subgroup.closure genX := by
    have : dd (sr 2) = dd (sr 1) * dd (r 1) := by decide
    rw [this]; exact Subgroup.mul_mem _ hs1 hr1
  have hs3 : dd (sr 3) ∈ Subgroup.closure genX := by
    have : dd (sr 3) = dd (sr 1) * dd (r 2) := by decide
    rw [this]; exact Subgroup.mul_mem _ hs1 hr2
  have h0 : dd (r 0) ∈ Subgroup.closure genX := by
    have : dd (r 0) = 1 := by decide
    rw [this]; exact Subgroup.one_mem _
  rcases d with i | i
  · fin_cases i
    · exact h0
    · exact hr1
    · exact hr2
    · exact hr3
  · fin_cases i
    · exact hs0
    · exact hs1
    · exact hs2
    · exact hs3

theorem closure_genX : Subgroup.closure genX = ⊤ := by
  rw [eq_top_iff]
  intro t _
  have : t = SemidirectProduct.inl t.left * SemidirectProduct.inr t.right :=
    SemidirectProduct.mk_eq_inl_mul_inr t.right t.left
  rw [this]
  exact Subgroup.mul_mem _ (inl_mem_closure _) (inr_mem_closure _)

theorem commutator_top_le_of_gen {G : Type*} [Group G] (K : Subgroup G) [K.Normal] (X : Set G)
    (hX : Subgroup.closure X = ⊤) (h : ∀ a : G, ∀ y ∈ X, ⁅a, y⁆ ∈ K) :
    ⁅(⊤ : Subgroup G), ⊤⁆ ≤ K := by
  rw [Subgroup.commutator_le]
  intro a _ b _
  let B : Subgroup G :=
    { carrier := {b | ⁅a, b⁆ ∈ K}
      one_mem' := by simp
      mul_mem' := fun {b c} hb hc => by
        have e : ⁅a, b * c⁆ = ⁅a, b⁆ * (b * ⁅a, c⁆ * b⁻¹) := by
          simp only [commutatorElement_def]; group
        show ⁅a, b * c⁆ ∈ K
        rw [e]
        exact K.mul_mem hb (Subgroup.Normal.conj_mem inferInstance _ hc b)
      inv_mem' := fun {b} hb => by
        have e : ⁅a, b⁻¹⁆ = b⁻¹ * ⁅a, b⁆⁻¹ * b⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        show ⁅a, b⁻¹⁆ ∈ K
        rw [e]
        exact Subgroup.Normal.conj_mem inferInstance _ (K.inv_mem hb) b⁻¹ }
  have hB : Subgroup.closure X ≤ B := (Subgroup.closure_le B).2 fun y hy => h a y hy
  rw [hX] at hB
  exact hB (Subgroup.mem_top b)

theorem code_e0 : code (e 0) = 1 := by decide +kernel
theorem code_e1 : code (e 1) = 2 := by decide +kernel
theorem code_e2 : code (e 2) = 4 := by decide +kernel
theorem code_e3 : code (e 3) = 8 := by decide +kernel
theorem code_e4 : code (e 4) = 16 := by decide +kernel
theorem code_s0 : code (dd (sr 0)) = 128 := by decide +kernel
theorem code_s1 : code (dd (sr 1)) = 160 := by decide +kernel

theorem e0_central : ∀ g : T0, g * e 0 = e 0 * g := by decide +kernel
theorem e0_ne_one : e 0 ≠ 1 := by decide +kernel

set_option maxHeartbeats 0 in
theorem chk_gen : (allLt 256 fun a => [1, 2, 4, 8, 16, 128, 160].all fun y =>
    pTh (commT a y)) = true := by decide +kernel

theorem comm_top_le_Th : ⁅(⊤ : Subgroup T0), ⊤⁆ ≤ Th := by
  refine commutator_top_le_of_gen Th genX closure_genX fun a y hy => ?_
  have hy' : code y ∈ [1, 2, 4, 8, 16, 128, 160] := by
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp [code_e0]
    · simp [code_e1]
    · simp [code_e2]
    · simp [code_e3]
    · simp [code_e4]
    · simp [code_s0]
    · simp [code_s1]
  have := allLt_iff.1 chk_gen (code a) (code_lt a)
  rw [List.all_eq_true] at this
  have h2 := this _ hy'
  show pTh (code ⁅a, y⁆) = true
  rw [code_comm]
  exact h2

theorem comm_top_le_N00 : ⁅(⊤ : Subgroup T0), ⊤⁆ ≤ N00 := comm_top_le_Th.trans Th_le_N00

def inK (i c : Nat) : Bool := c == 0 || c == i || c == 1 || c == mulT i 1

def chkK (i : Nat) : Bool :=
  let L := [0, i, 1, mulT i 1]
  inK i 0 && (L.all fun c => L.all fun d => inK i (mulT c d)) && (L.all fun c => inK i (invT c))

def critP (i : Nat) : Bool := pTh i && mulT i i == 0 && i != 0 && i != 1

theorem chkK_all : (allLt 256 fun i => !critP i || chkK i) = true := by decide +kernel

theorem chkK_sound {i : Nat} (h : chkK i = true) :
    inK i 0 = true ∧ (∀ c < 256, ∀ d < 256, inK i c = true → inK i d = true →
      inK i (mulT c d) = true) ∧ ∀ c < 256, inK i c = true → inK i (invT c) = true := by
  simp only [chkK, Bool.and_eq_true, List.all_eq_true, List.mem_cons, List.not_mem_nil,
    or_false] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  have hL : ∀ c, inK i c = true → c = 0 ∨ c = i ∨ c = 1 ∨ c = mulT i 1 := by
    intro c hc
    simpa [inK, Bool.or_eq_true, beq_iff_eq, or_assoc] using hc
  refine ⟨h0, fun c _ d _ hc hd => ?_, fun c _ hc => ?_⟩
  · exact h1 c (hL c hc) d (hL d hd)
  · exact h2 c (hL c hc)

def actQf (d q : Nat) : Nat :=
  Nat.land (Nat.shiftRight actTbl (Nat.mul 5 (Nat.add (Nat.mul 32 d) q))) 31
def mulDf (d d' : Nat) : Nat :=
  Nat.land (Nat.shiftRight mulDTbl (Nat.mul 3 (Nat.add (Nat.mul 8 d) d'))) 7
def invDf (d : Nat) : Nat := Nat.land (Nat.shiftRight invDTbl (Nat.mul 3 d)) 7
def mulTf (c c' : Nat) : Nat :=
  Nat.add (Nat.xor (Nat.mod c 32) (actQf (Nat.div c 32) (Nat.mod c' 32)))
    (Nat.mul 32 (mulDf (Nat.div c 32) (Nat.div c' 32)))
def invTf (c : Nat) : Nat :=
  Nat.add (actQf (invDf (Nat.div c 32)) (Nat.mod c 32)) (Nat.mul 32 (invDf (Nat.div c 32)))
def commTf (a b : Nat) : Nat := mulTf (mulTf (mulTf a b) (invTf a)) (invTf b)

private theorem mulTf_eq : mulTf = mulT := rfl
private theorem commTf_eq : commTf = commT := rfl

def pairsAll (C : List Nat) (f : Nat → Nat → Bool) : Bool :=
  C.all fun j => C.all fun k => f j k

def centf (i : Nat) : List Nat := (List.range 256).filter fun j => mulTf i j == mulTf j i
def chkAf : Bool :=
  allLt 256 fun i => !critP i || pairsAll (centf i) fun j k => inK i (commTf j k)

set_option maxHeartbeats 0 in
theorem chkAf_true : chkAf = true := by decide +kernel

theorem chkAf_sound {i : Nat} (hi : i < 256) (hc : critP i = true) :
    ∀ j < 256, mulT i j = mulT j i → ∀ k < 256, mulT i k = mulT k i →
      inK i (commT j k) = true := by
  have h := allLt_iff.1 chkAf_true i hi
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at h
  rcases h with h | h
  · rw [hc] at h; exact absurd h (by simp)
  · intro j hj hij k hk hik
    unfold pairsAll at h
    rw [List.all_eq_true] at h
    have hj' : j ∈ centf i := by
      simp only [centf, List.mem_filter, List.mem_range, beq_iff_eq, mulTf_eq]
      exact ⟨hj, hij⟩
    have hk' : k ∈ centf i := by
      simp only [centf, List.mem_filter, List.mem_range, beq_iff_eq, mulTf_eq]
      exact ⟨hk, hik⟩
    have := (List.all_eq_true.1 (h j hj')) k hk'
    rw [commTf_eq] at this
    exact this

theorem T0_A (t : T0) (ht2 : t * t = 1) (ht1 : t ≠ 1) (htz : t ≠ e 0)
    (hC : t ∈ ⁅Subgroup.centralizer ({t} : Set T0), Subgroup.centralizer ({t} : Set T0)⁆) :
    ∀ w ∈ ⁅Subgroup.centralizer ({t} : Set T0), Subgroup.centralizer ({t} : Set T0)⁆,
      w = 1 ∨ w = t ∨ w = e 0 ∨ w = t * e 0 := by
  have hCle : ⁅Subgroup.centralizer ({t} : Set T0), Subgroup.centralizer ({t} : Set T0)⁆ ≤ Th :=
    (Subgroup.commutator_mono le_top le_top).trans comm_top_le_Th
  have htTh : pTh (code t) = true := hCle hC
  have h2 : mulT (code t) (code t) = 0 := by rw [← code_mul, ht2, code_one]
  have h3 : code t ≠ 0 := fun h => ht1 (code_inj (h.trans code_one.symm))
  have h4 : code t ≠ 1 := fun h => htz (code_inj (h.trans code_e0.symm))
  have hcrit : critP (code t) = true := by simp [critP, htTh, h2, h3, h4]
  have hK := chkK_sound (by
    have := allLt_iff.1 chkK_all (code t) (code_lt t)
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at this
    rcases this with h | h
    · rw [hcrit] at h; exact absurd h (by simp)
    · exact h)
  let K : Subgroup T0 := predSubgroup (inK (code t)) hK.1 hK.2.1 hK.2.2
  have hcK : ∀ a ∈ Subgroup.centralizer ({t} : Set T0), ∀ b ∈ Subgroup.centralizer ({t} : Set T0),
      ⁅a, b⁆ ∈ K := by
    intro a ha b hb
    have ha' := Subgroup.mem_centralizer_singleton_iff.1 ha
    have hb' := Subgroup.mem_centralizer_singleton_iff.1 hb
    have hca : mulT (code t) (code a) = mulT (code a) (code t) := by
      rw [← code_mul, ← code_mul, ha']
    have hcb : mulT (code t) (code b) = mulT (code b) (code t) := by
      rw [← code_mul, ← code_mul, hb']
    show inK (code t) (code ⁅a, b⁆) = true
    rw [code_comm]
    exact chkAf_sound (code_lt t) hcrit _ (code_lt a) hca _ (code_lt b) hcb
  intro w hw
  have hwK : w ∈ K := (Subgroup.commutator_le.2 hcK) hw
  have hw' : inK (code t) (code w) = true := hwK
  simp only [inK, Bool.or_eq_true, beq_iff_eq] at hw'
  rcases hw' with ((h | h) | h) | h
  · left; exact code_inj (h.trans code_one.symm)
  · right; left; exact code_inj h
  · right; right; left; exact code_inj (h.trans code_e0.symm)
  · right; right; right
    apply code_inj
    rw [h, code_mul, code_e0]

theorem T0_B :
    e 0 ∈ ⁅Subgroup.centralizer ({e 4 * dd (r 2)} : Set T0),
      Subgroup.centralizer ({e 4 * dd (r 2)} : Set T0)⁆ ∧
    ∃ w ∈ ⁅Subgroup.centralizer ({e 4 * dd (r 2)} : Set T0),
      Subgroup.centralizer ({e 4 * dd (r 2)} : Set T0)⁆, w ≠ 1 ∧ w ≠ e 0 := by
  have h1 : e 1 ∈ Subgroup.centralizer ({e 4 * dd (r 2)} : Set T0) :=
    Subgroup.mem_centralizer_singleton_iff.2 (by decide +kernel)
  have h2 : e 2 * dd (r 1) ∈ Subgroup.centralizer ({e 4 * dd (r 2)} : Set T0) :=
    Subgroup.mem_centralizer_singleton_iff.2 (by decide +kernel)
  have h3 : e 2 * dd (sr 0) ∈ Subgroup.centralizer ({e 4 * dd (r 2)} : Set T0) :=
    Subgroup.mem_centralizer_singleton_iff.2 (by decide +kernel)
  refine ⟨?_, dd (r 2), ?_, by decide +kernel, by decide +kernel⟩
  · have e1 : ⁅e 1, e 2 * dd (r 1)⁆ = e 0 := by decide +kernel
    have h := Subgroup.commutator_mem_commutator h1 h2
    rw [e1] at h
    exact h
  · have e2 : ⁅e 2 * dd (r 1), e 2 * dd (sr 0)⁆ = dd (r 2) := by decide +kernel
    have h := Subgroup.commutator_mem_commutator h2 h3
    rw [e2] at h
    exact h

theorem code_surj (i : Nat) (hi : i < 256) : ∃ g : T0, code g = i := by
  let f : T0 → Fin 256 := fun t => ⟨code t, code_lt t⟩
  have hf : Function.Injective f := fun a b h =>
    code_inj (by simpa [f] using congrArg Fin.val h)
  have hcard : Fintype.card T0 = Fintype.card (Fin 256) := by
    rw [← Nat.card_eq_fintype_card, card_T0, Fintype.card_fin]
  obtain ⟨g, hg⟩ := ((Fintype.bijective_iff_injective_and_card f).2 ⟨hf, hcard⟩).2 ⟨i, hi⟩
  exact ⟨g, by simpa [f] using congrArg Fin.val hg⟩

theorem chk_center : (allLt 256 fun i => i == 0 || i == 1 ||
    !(allLt 256 fun j => mulTf i j == mulTf j i)) = true := by decide +kernel

theorem center_T0 (z : T0) (hz : ∀ g : T0, z * g = g * z) : z = 1 ∨ z = e 0 := by
  have h := allLt_iff.1 chk_center (code z) (code_lt z)
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  rcases h with (h | h) | h
  · left; exact code_inj (h.trans code_one.symm)
  · right; exact code_inj (h.trans code_e0.symm)
  · exfalso
    have h2 : ∀ j < 256, mulTf (code z) j = mulTf j (code z) := by
      intro j hj
      obtain ⟨g, rfl⟩ := code_surj j hj
      rw [mulTf_eq, ← code_mul, ← code_mul, hz g]
    have h3 := (allLt_iff.2 (fun j hj => by simpa using h2 j hj) : (allLt 256 fun j =>
      mulTf (code z) j == mulTf j (code z)) = true)
    rw [h3] at h
    exact absurd h (by simp)

end CFSG.CGT.PushingUpLit.T2KR.Model613
