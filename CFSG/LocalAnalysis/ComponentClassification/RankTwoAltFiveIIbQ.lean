module

public import CFSG.Certificates.ExtraspecialNormalForm
public import CFSG.Sporadic.Recognition.LyonsAS44Quat

public section

namespace CFSG.ComponentClassification.RankTwoAltFive

open Subgroup

namespace IIbM12

open CFSG.Certificates.ExtraspecialNF

@[expose] def cMat : Fin 4 → Fin 4 → ZMod 2 :=
  ![![0, 1, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 1, 0]]

theorem cMat_nondegenerate : Nondegenerate cMat := by decide

theorem cMat_symm : ∀ i j, cMat i j = cMat j i := by decide

theorem cMat_diag : ∀ i, cMat i i = 0 := by decide

@[expose] def inW₁ (w : Fin 4 → ZMod 2) : Prop :=
  w = 0 ∨ w = ![1, 1, 0, 0] ∨ w = ![1, 0, 1, 1] ∨ w = ![0, 1, 1, 1]

@[expose] def inW₂ (w : Fin 4 → ZMod 2) : Prop :=
  w = 0 ∨ w = ![1, 1, 1, 0] ∨ w = ![1, 1, 0, 1] ∨ w = ![0, 0, 1, 1]

@[expose] def inWE (w : Fin 4 → ZMod 2) : Prop := w 1 = 0 ∧ w 2 = 0

instance : DecidablePred inW₁ := fun w => by unfold inW₁; infer_instance
instance : DecidablePred inW₂ := fun w => by unfold inW₂; infer_instance
instance : DecidablePred inWE := fun w => by unfold inWE; infer_instance

theorem inW₁_zero : inW₁ 0 := Or.inl rfl

theorem inW₂_zero : inW₂ 0 := Or.inl rfl

theorem inWE_zero : inWE 0 := ⟨rfl, rfl⟩

theorem inW₁_add : ∀ w w', inW₁ w → inW₁ w' → inW₁ (w + w') := by decide
theorem inW₂_add : ∀ w w', inW₂ w → inW₂ w' → inW₂ (w + w') := by decide
theorem inWE_add : ∀ w w', inWE w → inWE w' → inWE (w + w') := by decide

theorem classify : ∀ w w' : Fin 4 → ZMod 2, qf cMat w = 1 → qf cMat w' = 1 →
    bil cMat w w' = 1 → (inW₁ w ∧ inW₁ w') ∨ (inW₂ w ∧ inW₂ w') := by decide

theorem qf_of_inWE : ∀ w : Fin 4 → ZMod 2, inWE w → qf cMat w = 0 := by decide

theorem bil_of_inWE : ∀ w w' : Fin 4 → ZMod 2, inWE w → inWE w' → bil cMat w w' = 0 := by
  decide

theorem card_W₁ : Nat.card {w : Fin 4 → ZMod 2 // inW₁ w} = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem card_W₂ : Nat.card {w : Fin 4 → ZMod 2 // inW₂ w} = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem not_sq_a_one : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.a 1 ≠ 1 := by
  decide

theorem not_sq_xa_zero : (QuaternionGroup.xa 0 : QuaternionGroup 2) * QuaternionGroup.xa 0 ≠ 1 := by
  decide

theorem not_comm_a_xa : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 ≠
    QuaternionGroup.xa 0 * QuaternionGroup.a 1 := by
  decide

theorem inWE_cases : ∀ w : Fin 4 → ZMod 2, inWE w →
    w = 0 ∨ w = ![1, 0, 0, 0] ∨ w = ![0, 0, 0, 1] ∨ w = ![1, 0, 0, 1] := by decide

section NF

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type*} [Group G] {n : ℕ} {z : G} {q : Fin n → G} {c : Fin n → Fin n → ZMod 2}

theorem bil_sub_left (c : Fin n → Fin n → ZMod 2) (v w u : Fin n → ZMod 2) :
    bil c (v - w) u = bil c v u - bil c w u := by
  simp only [bil, Pi.sub_apply, sub_mul]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_sub_distrib _ _

theorem zpow_val_inj (hz : z ≠ 1) {a b : ZMod 2} (h : z ^ a.val = z ^ b.val) : a = b := by
  rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases b with rfl | rfl
  · rfl
  · exact absurd (by simpa [val_one_two] using h.symm) hz
  · exact absurd (by simpa [val_one_two] using h) hz
  · rfl

theorem nf_injective (h : Rel z q c) (hz : z ≠ 1) (hnd : Nondegenerate c) :
    Function.Injective (Function.uncurry (nf z q)) := by
  have hsymm := h.symm_of_ne_one hz
  have hdiag := h.diag_eq_zero hz
  rintro ⟨s, v⟩ ⟨s', w⟩ hst
  change nf z q s v = nf z q s' w at hst
  have hbil : ∀ u, bil c v u = bil c w u := by
    intro u
    have h1 := nf_mul_comm h hsymm hdiag s 0 v u
    have h2 := nf_mul_comm h hsymm hdiag s' 0 w u
    rw [← hst] at h2
    rw [h1] at h2
    exact zpow_val_inj hz (mul_left_cancel h2)
  have hvw : v = w := by
    by_contra hne
    obtain ⟨u, hu⟩ := hnd (v - w) (sub_ne_zero.2 hne)
    rw [bil_sub_left, hbil u, sub_self] at hu
    exact hu rfl
  subst hvw
  have hs : z ^ s.val = z ^ s'.val := mul_right_cancel hst
  rw [zpow_val_inj hz hs]

theorem nf_eq_zpow_mul (z : G) (q : Fin n → G) (s : ZMod 2) (w : Fin n → ZMod 2) :
    nf z q s w = z ^ s.val * nf z q 0 w := by
  simp [nf]

end NF

variable {G : Type*} [Group G]

structure D8D8 (z₀ v t a c₁ : G) : Prop where
  z_ne_one : z₀ ≠ 1
  z_sq : z₀ * z₀ = 1
  v_sq : v * v = 1
  t_sq : t * t = 1
  a_sq : a * a = 1
  c_sq : c₁ * c₁ = 1
  z_v : z₀ * v = v * z₀
  z_t : z₀ * t = t * z₀
  z_a : z₀ * a = a * z₀
  z_c : z₀ * c₁ = c₁ * z₀
  v_t : v * t = t * v * z₀
  a_c : a * c₁ = c₁ * a * z₀
  v_a : v * a = a * v
  v_c : v * c₁ = c₁ * v
  t_a : t * a = a * t
  t_c : t * c₁ = c₁ * t

abbrev Qd (z₀ v t a c₁ : G) : Subgroup G := closure (insert z₀ (Set.range ![v, t, a, c₁]))

abbrev E₁d (z₀ v c₁ : G) : Subgroup G := closure ({z₀, v, c₁} : Set G)

namespace D8D8

variable {z₀ v t a c₁ : G}

theorem swap_of_mul_z {x y z : G} (hz : z * z = 1) (h : x * y = y * x * z) :
    y * x = x * y * z := by
  calc y * x = y * x * z * z := by rw [mul_assoc (y * x), hz, mul_one]
    _ = x * y * z := by rw [← h]

theorem rel (h : D8D8 z₀ v t a c₁) : Rel z₀ ![v, t, a, c₁] cMat where
  z_sq := h.z_sq
  z_comm i := by
    fin_cases i
    · exact h.z_v
    · exact h.z_t
    · exact h.z_a
    · exact h.z_c
  q_sq i := by
    fin_cases i
    · exact h.v_sq
    · exact h.t_sq
    · exact h.a_sq
    · exact h.c_sq
  comm i j := by
    have tv := swap_of_mul_z h.z_sq h.v_t
    have ca := swap_of_mul_z h.z_sq h.a_c
    fin_cases i <;> fin_cases j <;> simp [cMat, val_one_two]
    all_goals first
      | exact h.v_t
      | exact tv
      | exact h.a_c
      | exact ca
      | exact h.v_a
      | exact h.v_a.symm
      | exact h.v_c
      | exact h.v_c.symm
      | exact h.t_a
      | exact h.t_a.symm
      | exact h.t_c
      | exact h.t_c.symm

theorem z_mem_Q : z₀ ∈ Qd z₀ v t a c₁ := z_mem_closure _ _

theorem v_mem_Q : v ∈ Qd z₀ v t a c₁ := q_mem_closure z₀ ![v, t, a, c₁] 0

theorem t_mem_Q : t ∈ Qd z₀ v t a c₁ := q_mem_closure z₀ ![v, t, a, c₁] 1

theorem a_mem_Q : a ∈ Qd z₀ v t a c₁ := q_mem_closure z₀ ![v, t, a, c₁] 2

theorem c_mem_Q : c₁ ∈ Qd z₀ v t a c₁ := q_mem_closure z₀ ![v, t, a, c₁] 3

theorem v_eq_nf : v = nf z₀ ![v, t, a, c₁] 0 ![1, 0, 0, 0] := by
  rw [show (![1, 0, 0, 0] : Fin 4 → ZMod 2) = Pi.single 0 1 by decide, nf_single]
  rfl

theorem t_eq_nf : t = nf z₀ ![v, t, a, c₁] 0 ![0, 1, 0, 0] := by
  rw [show (![0, 1, 0, 0] : Fin 4 → ZMod 2) = Pi.single 1 1 by decide, nf_single]
  rfl

theorem a_eq_nf : a = nf z₀ ![v, t, a, c₁] 0 ![0, 0, 1, 0] := by
  rw [show (![0, 0, 1, 0] : Fin 4 → ZMod 2) = Pi.single 2 1 by decide, nf_single]
  rfl

theorem c_eq_nf : c₁ = nf z₀ ![v, t, a, c₁] 0 ![0, 0, 0, 1] := by
  rw [show (![0, 0, 0, 1] : Fin 4 → ZMod 2) = Pi.single 3 1 by decide, nf_single]
  rfl

variable (h : D8D8 z₀ v t a c₁)
include h

theorem injective : Function.Injective (Function.uncurry (nf z₀ ![v, t, a, c₁])) :=
  nf_injective h.rel h.z_ne_one cMat_nondegenerate

theorem nf_inj {s s' : ZMod 2} {w w' : Fin 4 → ZMod 2}
    (e : nf z₀ ![v, t, a, c₁] s w = nf z₀ ![v, t, a, c₁] s' w') : s = s' ∧ w = w' :=
  eq_of_nf_eq h.injective e

theorem mem_Q_iff {x : G} : x ∈ Qd z₀ v t a c₁ ↔ ∃ s w, nf z₀ ![v, t, a, c₁] s w = x :=
  mem_closure_iff h.rel

theorem card_Q : Nat.card (Qd z₀ v t a c₁) = 32 :=
  (card_closure h.rel h.injective).trans (by norm_num)

theorem isExtraspecial_Q : IsExtraspecial 2 ↥(Qd z₀ v t a c₁) where
  center_order_p := card_center h.rel h.injective cMat_nondegenerate
  quotient_elementary_abelian :=
    isElementaryAbelian_quotient_center h.rel h.injective cMat_nondegenerate
  quotient_nontrivial :=
    nontrivial_quotient_center h.rel h.injective cMat_nondegenerate (by norm_num)

theorem sq_nf (s : ZMod 2) (w : Fin 4 → ZMod 2) :
    nf z₀ ![v, t, a, c₁] s w * nf z₀ ![v, t, a, c₁] s w = z₀ ^ (qf cMat w).val := by
  rw [← sq]
  exact nf_sq h.rel cMat_symm s w

theorem comm_nf (s s' : ZMod 2) (w w' : Fin 4 → ZMod 2) :
    nf z₀ ![v, t, a, c₁] s w * nf z₀ ![v, t, a, c₁] s' w' =
      nf z₀ ![v, t, a, c₁] s' w' * nf z₀ ![v, t, a, c₁] s w * z₀ ^ (bil cMat w w').val :=
  nf_mul_comm h.rel cMat_symm cMat_diag s s' w w'

theorem mul_nf (s s' : ZMod 2) (w w' : Fin 4 → ZMod 2) :
    nf z₀ ![v, t, a, c₁] s w * nf z₀ ![v, t, a, c₁] s' w' =
      nf z₀ ![v, t, a, c₁] (s + s' + collect cMat w w') (w + w') :=
  nf_mul_nf h.rel s s' w w'

theorem commutator_mem {x y : G} (hx : x ∈ Qd z₀ v t a c₁) (hy : y ∈ Qd z₀ v t a c₁) :
    x * y * x⁻¹ * y⁻¹ ∈ zpowers z₀ := by
  obtain ⟨s, w, rfl⟩ := h.mem_Q_iff.mp hx
  obtain ⟨s', w', rfl⟩ := h.mem_Q_iff.mp hy
  have e := commutator_eq_zpow h.rel cMat_symm cMat_diag s s' w w'
  rw [commutatorElement_def] at e
  rw [e]
  exact pow_mem (mem_zpowers z₀) _

theorem z_comm_Q {x : G} (hx : x ∈ Qd z₀ v t a c₁) : z₀ * x = x * z₀ :=
  (commute_of_mem_closure h.rel hx).eq

theorem vc_eq_nf : v * c₁ = nf z₀ ![v, t, a, c₁] 0 ![1, 0, 0, 1] := by
  have e := h.mul_nf 0 0 ![1, 0, 0, 0] ![0, 0, 0, 1]
  rw [← v_eq_nf, ← c_eq_nf] at e
  rw [e]
  congr 1
  all_goals decide

def nfSub (P : (Fin 4 → ZMod 2) → Prop) (h0 : P 0)
    (hadd : ∀ w w', P w → P w' → P (w + w')) : Subgroup G where
  carrier := {x | ∃ s w, P w ∧ nf z₀ ![v, t, a, c₁] s w = x}
  one_mem' := ⟨0, 0, h0, nf_zero_zero _ _⟩
  mul_mem' := by
    rintro _ _ ⟨s, w, hw, rfl⟩ ⟨s', w', hw', rfl⟩
    exact ⟨_, _, hadd w w' hw hw', (h.mul_nf s s' w w').symm⟩
  inv_mem' := by
    rintro _ ⟨s, w, hw, rfl⟩
    refine ⟨s + collect cMat w w, w, hw, ?_⟩
    refine (inv_eq_of_mul_eq_one_right ?_).symm
    rw [h.mul_nf]
    have e1 : s + (s + collect cMat w w) + collect cMat w w = 0 := by
      generalize collect cMat w w = b
      revert s b
      decide
    have e2 : w + w = 0 := by
      funext i
      have : ∀ x : ZMod 2, x + x = 0 := by decide
      exact this _
    rw [e1, e2, nf_zero_zero]

theorem nf_mem_zpowers_iff (s : ZMod 2) (w : Fin 4 → ZMod 2) :
    nf z₀ ![v, t, a, c₁] s w ∈ zpowers z₀ ↔ w = 0 := by
  constructor
  · intro hx
    obtain ⟨b, hb⟩ := (mem_zpowers_iff_exists h.rel).mp hx
    rw [← nf_zero_vec z₀ ![v, t, a, c₁] b] at hb
    exact (h.nf_inj hb).2.symm
  · rintro rfl
    rw [nf_zero_vec]
    exact pow_mem (mem_zpowers z₀) _

theorem E₁_le_nfSub : E₁d z₀ v c₁ ≤ h.nfSub inWE inWE_zero inWE_add := by
  rw [closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact ⟨1, 0, inWE_zero, nf_one_zero _ _⟩
  · exact ⟨0, ![1, 0, 0, 0], by decide, v_eq_nf.symm⟩
  · exact ⟨0, ![0, 0, 0, 1], by decide, c_eq_nf.symm⟩

omit h in
theorem z_mem_E₁ : z₀ ∈ E₁d z₀ v c₁ := subset_closure (by simp)

omit h in
theorem v_mem_E₁ : v ∈ E₁d z₀ v c₁ := subset_closure (by simp)

omit h in
theorem c_mem_E₁ : c₁ ∈ E₁d z₀ v c₁ := subset_closure (by simp)

theorem nf_mem_E₁ {s : ZMod 2} {w : Fin 4 → ZMod 2} (hw : inWE w) :
    nf z₀ ![v, t, a, c₁] s w ∈ E₁d z₀ v c₁ := by
  rw [nf_eq_zpow_mul]
  refine mul_mem (pow_mem z_mem_E₁ _) ?_
  rcases inWE_cases w hw with rfl | rfl | rfl | rfl
  · rw [nf_zero_zero]
    exact one_mem _
  · rw [← v_eq_nf]
    exact v_mem_E₁
  · rw [← c_eq_nf]
    exact c_mem_E₁
  · rw [← h.vc_eq_nf]
    exact mul_mem v_mem_E₁ c_mem_E₁

theorem mem_E₁_iff {x : G} :
    x ∈ E₁d z₀ v c₁ ↔ ∃ s w, inWE w ∧ nf z₀ ![v, t, a, c₁] s w = x :=
  ⟨fun hx => h.E₁_le_nfSub hx, fun ⟨_, _, hw, hx⟩ => hx ▸ h.nf_mem_E₁ hw⟩

theorem E₁_le_Q : E₁d z₀ v c₁ ≤ Qd z₀ v t a c₁ := by
  rw [closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  exacts [z_mem_Q, v_mem_Q, c_mem_Q]

theorem mul_self_of_mem_E₁ {x : G} (hx : x ∈ E₁d z₀ v c₁) : x * x = 1 := by
  obtain ⟨s, w, hw, rfl⟩ := h.mem_E₁_iff.mp hx
  rw [h.sq_nf, qf_of_inWE w hw]
  simp

theorem comm_of_mem_E₁ {x y : G} (hx : x ∈ E₁d z₀ v c₁) (hy : y ∈ E₁d z₀ v c₁) :
    x * y = y * x := by
  obtain ⟨s, w, hw, rfl⟩ := h.mem_E₁_iff.mp hx
  obtain ⟨s', w', hw', rfl⟩ := h.mem_E₁_iff.mp hy
  rw [h.comm_nf, bil_of_inWE w w' hw hw']
  simp

@[expose] def HasVec (z₀ v t a c₁ : G) (x : G) (w : Fin 4 → ZMod 2) : Prop :=
  ∃ s, nf z₀ ![v, t, a, c₁] s w = x

omit h in
theorem hasVec_z : HasVec z₀ v t a c₁ z₀ 0 := ⟨1, nf_one_zero _ _⟩

omit h in
theorem hasVec_v : HasVec z₀ v t a c₁ v ![1, 0, 0, 0] := ⟨0, v_eq_nf.symm⟩

omit h in
theorem hasVec_t : HasVec z₀ v t a c₁ t ![0, 1, 0, 0] := ⟨0, t_eq_nf.symm⟩

omit h in
theorem hasVec_a : HasVec z₀ v t a c₁ a ![0, 0, 1, 0] := ⟨0, a_eq_nf.symm⟩

omit h in
theorem hasVec_c : HasVec z₀ v t a c₁ c₁ ![0, 0, 0, 1] := ⟨0, c_eq_nf.symm⟩

theorem hasVec_mul {x y : G} {w w' : Fin 4 → ZMod 2} (hx : HasVec z₀ v t a c₁ x w)
    (hy : HasVec z₀ v t a c₁ y w') : HasVec z₀ v t a c₁ (x * y) (w + w') := by
  obtain ⟨s, rfl⟩ := hx
  obtain ⟨s', rfl⟩ := hy
  exact ⟨_, (h.mul_nf s s' w w').symm⟩

omit h in
theorem HasVec.congr {x : G} {w w' : Fin 4 → ZMod 2} (hx : HasVec z₀ v t a c₁ x w)
    (e : w = w') : HasVec z₀ v t a c₁ x w' := e ▸ hx

omit h in
theorem HasVec.mem_Q {x : G} {w : Fin 4 → ZMod 2} (hx : HasVec z₀ v t a c₁ x w) :
    x ∈ Qd z₀ v t a c₁ := by
  obtain ⟨s, rfl⟩ := hx
  exact nf_mem_closure _ _ s w

theorem hasVec_of_mem_Q {x : G} (hx : x ∈ Qd z₀ v t a c₁) : ∃ w, HasVec z₀ v t a c₁ x w := by
  obtain ⟨s, w, rfl⟩ := h.mem_Q_iff.mp hx
  exact ⟨w, s, rfl⟩

theorem hasVec_unique {x : G} {w w' : Fin 4 → ZMod 2} (hx : HasVec z₀ v t a c₁ x w)
    (hx' : HasVec z₀ v t a c₁ x w') : w = w' := by
  obtain ⟨s, rfl⟩ := hx
  obtain ⟨s', e⟩ := hx'
  exact (h.nf_inj e.symm).2

theorem hasVec_mem_zpowers_iff {x : G} {w : Fin 4 → ZMod 2} (hx : HasVec z₀ v t a c₁ x w) :
    x ∈ zpowers z₀ ↔ w = 0 := by
  obtain ⟨s, rfl⟩ := hx
  exact h.nf_mem_zpowers_iff s w

theorem hasVec_sq {x : G} {w : Fin 4 → ZMod 2} (hx : HasVec z₀ v t a c₁ x w) :
    x * x = z₀ ^ (qf cMat w).val := by
  obtain ⟨s, rfl⟩ := hx
  exact h.sq_nf s w

theorem hasVec_comm {x y : G} {w w' : Fin 4 → ZMod 2} (hx : HasVec z₀ v t a c₁ x w)
    (hy : HasVec z₀ v t a c₁ y w') : x * y = y * x * z₀ ^ (bil cMat w w').val := by
  obtain ⟨s, rfl⟩ := hx
  obtain ⟨s', rfl⟩ := hy
  exact h.comm_nf s s' w w'

def K₁ : Subgroup G := h.nfSub inW₁ inW₁_zero inW₁_add

def K₂ : Subgroup G := h.nfSub inW₂ inW₂_zero inW₂_add

theorem mem_K₁_iff {x : G} : x ∈ h.K₁ ↔ ∃ w, inW₁ w ∧ HasVec z₀ v t a c₁ x w :=
  ⟨fun ⟨s, w, hw, hx⟩ => ⟨w, hw, s, hx⟩, fun ⟨w, hw, s, hx⟩ => ⟨s, w, hw, hx⟩⟩

theorem mem_K₂_iff {x : G} : x ∈ h.K₂ ↔ ∃ w, inW₂ w ∧ HasVec z₀ v t a c₁ x w :=
  ⟨fun ⟨s, w, hw, hx⟩ => ⟨w, hw, s, hx⟩, fun ⟨w, hw, s, hx⟩ => ⟨s, w, hw, hx⟩⟩

theorem K₁_le_Q : h.K₁ ≤ Qd z₀ v t a c₁ := by
  rintro x hx
  obtain ⟨w, -, hxw⟩ := h.mem_K₁_iff.mp hx
  exact hxw.mem_Q

theorem K₂_le_Q : h.K₂ ≤ Qd z₀ v t a c₁ := by
  rintro x hx
  obtain ⟨w, -, hxw⟩ := h.mem_K₂_iff.mp hx
  exact hxw.mem_Q

theorem card_nfSub (P : (Fin 4 → ZMod 2) → Prop) [DecidablePred P] (h0 : P 0)
    (hadd : ∀ w w', P w → P w' → P (w + w')) :
    Nat.card (h.nfSub P h0 hadd) = 2 * Nat.card {w : Fin 4 → ZMod 2 // P w} := by
  let f : ZMod 2 × {w : Fin 4 → ZMod 2 // P w} → h.nfSub P h0 hadd :=
    fun p => ⟨nf z₀ ![v, t, a, c₁] p.1 p.2.1, p.1, p.2.1, p.2.2, rfl⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨s, w, hw⟩ ⟨s', w', hw'⟩ e
      obtain ⟨rfl, rfl⟩ := h.nf_inj (congrArg Subtype.val e)
      rfl
    · rintro ⟨x, s, w, hw, rfl⟩
      exact ⟨(s, ⟨w, hw⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, Nat.card_zmod]

theorem card_K₁ : Nat.card h.K₁ = 8 := by
  rw [K₁, h.card_nfSub, card_W₁]

theorem card_K₂ : Nat.card h.K₂ = 8 := by
  rw [K₂, h.card_nfSub, card_W₂]

theorem vt_mem_K₁ : v * t ∈ h.K₁ :=
  h.mem_K₁_iff.mpr ⟨_, by decide, h.hasVec_mul hasVec_v hasVec_t⟩

theorem vac_mem_K₁ : v * a * c₁ ∈ h.K₁ :=
  h.mem_K₁_iff.mpr ⟨_, by decide, h.hasVec_mul (h.hasVec_mul hasVec_v hasVec_a) hasVec_c⟩

theorem vt_not_mem_K₂ : v * t ∉ h.K₂ := by
  intro hx
  obtain ⟨w, hw, hxw⟩ := h.mem_K₂_iff.mp hx
  rw [← h.hasVec_unique (h.hasVec_mul hasVec_v hasVec_t) hxw] at hw
  revert hw
  decide

theorem K₁_ne_K₂ : h.K₁ ≠ h.K₂ := fun e => h.vt_not_mem_K₂ (e ▸ h.vt_mem_K₁)

theorem quaternion_of_hasVec {K : Subgroup G} (hK8 : Nat.card K = 8) {x y : G}
    {w w' : Fin 4 → ZMod 2}
    (hxK : x ∈ K) (hyK : y ∈ K) (hx : HasVec z₀ v t a c₁ x w) (hy : HasVec z₀ v t a c₁ y w')
    (hqx : qf cMat w = 1) (hqy : qf cMat w' = 1) (hb : bil cMat w' w = 1) :
    Nonempty (K ≃* QuaternionGroup 2) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK8]; norm_num)
  have hx2 : x * x = z₀ := by rw [h.hasVec_sq hx, hqx, val_one_two, pow_one]
  have hy2 : y * y = z₀ := by rw [h.hasVec_sq hy, hqy, val_one_two, pow_one]
  have hyx : y * x = x * y * z₀ := by rw [h.hasVec_comm hy hx, hb, val_one_two, pow_one]
  have hzx : z₀ * x = x * z₀ := h.z_comm_Q hx.mem_Q
  have hzy : z₀ * y = y * z₀ := h.z_comm_Q hy.mem_Q
  have hxinv : x⁻¹ = x * z₀ := by
    rw [inv_eq_iff_mul_eq_one, ← mul_assoc, hx2, h.z_sq]
  refine CFSG.Sporadic.Recognition.LyonsSims.nonempty_mulEquiv_quaternionGroup_two hK8 ⟨x, hxK⟩
    ⟨y, hyK⟩ ?_ ?_ ?_ ?_
  · apply Subtype.ext
    show x ^ 4 = 1
    have e : x ^ 2 = z₀ := by rw [sq, hx2]
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, e, sq, h.z_sq]
  · intro e
    apply h.z_ne_one
    have e' : x ^ 2 = 1 := congrArg Subtype.val e
    rwa [sq, hx2] at e'
  · apply Subtype.ext
    show y * x * y⁻¹ = x⁻¹
    have hzy' : z₀ * y⁻¹ = y⁻¹ * z₀ := (Commute.inv_right (show Commute z₀ y from hzy)).eq
    rw [hyx, hxinv, mul_assoc, mul_assoc, hzy', ← mul_assoc y, mul_inv_cancel, one_mul]
  · apply Subtype.ext
    show y ^ 2 = x ^ 2
    rw [sq, sq, hx2, hy2]

theorem K₁_quaternion : Nonempty (h.K₁ ≃* QuaternionGroup 2) :=
  h.quaternion_of_hasVec h.card_K₁ h.vt_mem_K₁ h.vac_mem_K₁ (h.hasVec_mul hasVec_v hasVec_t)
    (h.hasVec_mul (h.hasVec_mul hasVec_v hasVec_a) hasVec_c) (by decide) (by decide) (by decide)

theorem eq_K₁_or_K₂ {K : Subgroup G} (hKQ : K ≤ Qd z₀ v t a c₁)
    (hK : Nonempty (K ≃* QuaternionGroup 2)) : K = h.K₁ ∨ K = h.K₂ := by
  obtain ⟨φ⟩ := hK
  set i : G := (φ.symm (QuaternionGroup.a 1) : G) with hi
  set j : G := (φ.symm (QuaternionGroup.xa 0) : G) with hj
  have hiK : i ∈ K := (φ.symm _).2
  have hjK : j ∈ K := (φ.symm _).2
  obtain ⟨wi, hwi⟩ := h.hasVec_of_mem_Q (hKQ hiK)
  obtain ⟨wj, hwj⟩ := h.hasVec_of_mem_Q (hKQ hjK)
  have hφi : ∀ g g' : QuaternionGroup 2,
      (φ.symm g : G) * (φ.symm g' : G) = (φ.symm (g * g') : G) := fun g g' => by
    rw [map_mul]; rfl
  have hqi : qf cMat wi = 1 := by
    rcases zmod_two_cases (qf cMat wi) with h0 | h1
    · refine absurd ?_ not_sq_a_one
      have e := h.hasVec_sq hwi
      rw [h0] at e
      simp only [ZMod.val_zero, pow_zero] at e
      rw [hi, hφi] at e
      exact φ.symm.injective (Subtype.ext (by simpa using e))
    · exact h1
  have hqj : qf cMat wj = 1 := by
    rcases zmod_two_cases (qf cMat wj) with h0 | h1
    · refine absurd ?_ not_sq_xa_zero
      have e := h.hasVec_sq hwj
      rw [h0] at e
      simp only [ZMod.val_zero, pow_zero] at e
      rw [hj, hφi] at e
      exact φ.symm.injective (Subtype.ext (by simpa using e))
    · exact h1
  have hb : bil cMat wi wj = 1 := by
    rcases zmod_two_cases (bil cMat wi wj) with h0 | h1
    · refine absurd ?_ not_comm_a_xa
      have e := h.hasVec_comm hwi hwj
      rw [h0] at e
      simp only [ZMod.val_zero, pow_zero, mul_one] at e
      rw [hi, hj, hφi, hφi] at e
      exact φ.symm.injective (Subtype.ext e)
    · exact h1
  have hK8 : Nat.card K = 8 := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hword : ∀ (M : Subgroup G), i ∈ M → j ∈ M → K ≤ M := by
    intro M hiM hjM x hx
    have e : x = (φ.symm (φ ⟨x, hx⟩) : G) := by simp
    rw [e]
    generalize φ ⟨x, hx⟩ = g
    cases g with
    | a m =>
      have : (QuaternionGroup.a m : QuaternionGroup 2) = QuaternionGroup.a 1 ^ m.val := by
        rw [QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val]
      rw [this, map_pow]
      exact pow_mem hiM _
    | xa m =>
      have : (QuaternionGroup.xa m : QuaternionGroup 2) =
          QuaternionGroup.xa 0 * QuaternionGroup.a 1 ^ m.val := by
        rw [QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val, QuaternionGroup.xa_mul_a,
          zero_add]
      rw [this, map_mul, map_pow]
      exact mul_mem hjM (pow_mem hiM _)
  rcases classify wi wj hqi hqj hb with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    have hle := hword h.K₁ (h.mem_K₁_iff.mpr ⟨wi, h1, hwi⟩) (h.mem_K₁_iff.mpr ⟨wj, h2, hwj⟩)
    have : Finite h.K₁ := Nat.finite_of_card_ne_zero (by rw [h.card_K₁]; norm_num)
    exact eq_of_le_of_card_ge hle (by rw [h.card_K₁, hK8])
  · right
    have hle := hword h.K₂ (h.mem_K₂_iff.mpr ⟨wi, h1, hwi⟩) (h.mem_K₂_iff.mpr ⟨wj, h2, hwj⟩)
    have : Finite h.K₂ := Nat.finite_of_card_ne_zero (by rw [h.card_K₂]; norm_num)
    exact eq_of_le_of_card_ge hle (by rw [h.card_K₂, hK8])

theorem map_conj_K₁_of_pow_three {x : G} (hxQ : x ∈ normalizer (Qd z₀ v t a c₁ : Set G))
    (hx3 : x ^ 3 = 1) : h.K₁.map (MulAut.conj x).toMonoidHom = h.K₁ := by
  have hmapQ : ∀ K : Subgroup G, K ≤ Qd z₀ v t a c₁ →
      K.map (MulAut.conj x).toMonoidHom ≤ Qd z₀ v t a c₁ := by
    rintro K hK _ ⟨k, hk, rfl⟩
    exact (mem_normalizer_iff.mp hxQ k).mp (hK hk)
  have hq : ∀ K : Subgroup G, Nonempty (K ≃* QuaternionGroup 2) →
      Nonempty (K.map (MulAut.conj x).toMonoidHom ≃* QuaternionGroup 2) := by
    rintro K ⟨e⟩
    exact ⟨(K.equivMapOfInjective _ (MulAut.conj x).injective).symm.trans e⟩
  have hK₂q : Nonempty (h.K₂ ≃* QuaternionGroup 2) :=
    h.quaternion_of_hasVec h.card_K₂
      (h.mem_K₂_iff.mpr ⟨_, by decide, h.hasVec_mul (h.hasVec_mul hasVec_v hasVec_t) hasVec_a⟩)
      (h.mem_K₂_iff.mpr ⟨_, by decide, h.hasVec_mul (h.hasVec_mul hasVec_v hasVec_t) hasVec_c⟩)
      (h.hasVec_mul (h.hasVec_mul hasVec_v hasVec_t) hasVec_a)
      (h.hasVec_mul (h.hasVec_mul hasVec_v hasVec_t) hasVec_c) (by decide) (by decide) (by decide)
  set f : Subgroup G → Subgroup G := fun K => K.map (MulAut.conj x).toMonoidHom with hf
  have hf1 := h.eq_K₁_or_K₂ (hmapQ _ h.K₁_le_Q) (hq _ h.K₁_quaternion)
  have hf2 := h.eq_K₁_or_K₂ (hmapQ _ h.K₂_le_Q) (hq _ hK₂q)
  have hinj : ∀ K K' : Subgroup G, f K = f K' → K = K' := fun K K' e =>
    map_injective (MulAut.conj x).injective e
  have hf3 : f (f (f h.K₁)) = h.K₁ := by
    have e : ∀ K : Subgroup G, f (f (f K)) = K.map (MulAut.conj (x * (x * x))).toMonoidHom := by
      intro K
      ext y
      simp only [hf, mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      constructor
      · rintro ⟨_, ⟨_, ⟨k, hk, rfl⟩, rfl⟩, rfl⟩
        exact ⟨k, hk, by group⟩
      · rintro ⟨k, hk, rfl⟩
        exact ⟨_, ⟨_, ⟨k, hk, rfl⟩, rfl⟩, by group⟩
    have e1 : x * (x * x) = 1 := by rw [← pow_two, ← pow_succ', hx3]
    rw [e, e1]
    ext y
    simp
  rcases hf1 with e1 | e1
  · exact e1
  · exfalso
    rcases hf2 with e2 | e2
    · have : f (f (f h.K₁)) = h.K₂ := by
        show f (f (h.K₁.map (MulAut.conj x).toMonoidHom)) = h.K₂
        rw [e1]
        show f (h.K₂.map (MulAut.conj x).toMonoidHom) = h.K₂
        rw [e2]
        exact e1
      exact h.K₁_ne_K₂ (hf3.symm.trans this)
    · exact h.K₁_ne_K₂ (hinj _ _ (e1.trans e2.symm))

end D8D8

end IIbM12

end CFSG.ComponentClassification.RankTwoAltFive
