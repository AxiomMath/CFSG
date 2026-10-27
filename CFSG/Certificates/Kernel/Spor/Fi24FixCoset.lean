module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.KC.Fi24FixC

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [CommRing K]

@[expose] def act (g : GL n K) (W : Submodule K (n → K)) : Submodule K (n → K) :=
  W.map (Matrix.mulVecLin (g : Matrix n n K))

theorem act_mul (g h : GL n K) (W : Submodule K (n → K)) : act (g * h) W = act g (act h W) := by
  unfold act
  rw [Units.val_mul, Matrix.mulVecLin_mul, Submodule.map_comp]

theorem act_one (W : Submodule K (n → K)) : act (1 : GL n K) W = W := by
  unfold act
  rw [Units.val_one, Matrix.mulVecLin_one, Submodule.map_id]

theorem act_inv_act (g : GL n K) (W : Submodule K (n → K)) : act g⁻¹ (act g W) = W := by
  rw [← act_mul, inv_mul_cancel, act_one]

theorem act_act_inv (g : GL n K) (W : Submodule K (n → K)) : act g (act g⁻¹ W) = W := by
  rw [← act_mul, mul_inv_cancel, act_one]

theorem act_inv_eq_of_act_eq {g : GL n K} {W : Submodule K (n → K)} (h : act g W = W) :
    act g⁻¹ W = W := by
  conv_lhs => rw [← h]
  exact act_inv_act g W

@[expose] def stab (W : Submodule K (n → K)) : Subgroup (GL n K) where
  carrier := {g | act g W = W}
  mul_mem' {g h} hg hh := by
    change act (g * h) W = W
    rw [act_mul]
    change act h W = W at hh
    change act g W = W at hg
    rw [hh, hg]
  one_mem' := act_one W
  inv_mem' {g} hg := act_inv_eq_of_act_eq hg

theorem mem_stab {W : Submodule K (n → K)} {g : GL n K} : g ∈ stab W ↔ act g W = W := Iff.rfl

variable {G : Type*} [Group G]

@[expose] noncomputable def ev (E : Subgroup G) (a q : G) : G := by
  classical exact if q ∈ E then q else a * q

theorem ev_mem {E : Subgroup G} {a : G} (hE : ∀ q, q ∈ E ∨ a * q ∈ E) (q : G) : ev E a q ∈ E := by
  classical
  unfold ev
  split_ifs with h
  · exact h
  · exact (hE q).resolve_left h

@[expose] noncomputable def subOf (E : Subgroup G) (a : G) (hE : ∀ q, q ∈ E ∨ a * q ∈ E)
    (σ : E →* GL n K) (V : Submodule K (n → K)) (q : G) : Submodule K (n → K) :=
  act (σ ⟨ev E a q, ev_mem hE q⟩)⁻¹ V

variable {H E : Subgroup G} {a : G} {hE : ∀ q, q ∈ E ∨ a * q ∈ E} {σ : E →* GL n K}
  {V : Submodule K (n → K)}

theorem subOf_eq_of_mem (q : G) (hq : q ∈ E) : subOf E a hE σ V q = act (σ ⟨q, hq⟩)⁻¹ V := by
  classical
  have h : ev E a q = q := by
    unfold ev
    rw [if_pos hq]
  have e : (⟨ev E a q, ev_mem hE q⟩ : E) = ⟨q, hq⟩ := Subtype.ext h
  unfold subOf
  rw [e]

theorem ev_rel (haH : a ∈ H) (q : G) : ev E a q * q⁻¹ ∈ H := by
  classical
  unfold ev
  split_ifs
  · rw [mul_inv_cancel]
    exact H.one_mem
  · rw [mul_inv_cancel_right]
    exact haH

theorem subOf_eq_of_rel (haH : a ∈ H) (hst : ∀ (h : G) (hh : h ∈ E), h ∈ H → σ ⟨h, hh⟩ ∈ stab V)
    {u v : G} (huv : u * v⁻¹ ∈ H) : subOf E a hE σ V u = subOf E a hE σ V v := by
  unfold subOf
  set u' : E := ⟨ev E a u, ev_mem hE u⟩
  set v' : E := ⟨ev E a v, ev_mem hE v⟩
  have hw : (u' * v'⁻¹ : E).val ∈ H := by
    change ev E a u * (ev E a v)⁻¹ ∈ H
    have e : ev E a u * (ev E a v)⁻¹ = (ev E a u * u⁻¹) * (u * v⁻¹) * (ev E a v * v⁻¹)⁻¹ := by
      group
    rw [e]
    exact H.mul_mem (H.mul_mem (ev_rel haH u) huv) (H.inv_mem (ev_rel haH v))
  have hs : σ (u' * v'⁻¹) ∈ stab V := hst _ (u' * v'⁻¹).2 hw
  have e : σ u' = σ (u' * v'⁻¹) * σ v' := by
    rw [← map_mul, inv_mul_cancel_right]
  change act (σ u')⁻¹ V = act (σ v')⁻¹ V
  rw [e, _root_.mul_inv_rev, act_mul, act_inv_eq_of_act_eq hs]

theorem ev_mul {e q : G} (he : e ∈ E) : ev E a (q * e) = ev E a q * e := by
  classical
  unfold ev
  by_cases hq : q ∈ E
  · rw [if_pos (E.mul_mem hq he), if_pos hq]
  · have : q * e ∉ E := fun h => hq (by simpa using E.mul_mem h (E.inv_mem he))
    rw [if_neg this, if_neg hq, mul_assoc]

theorem subOf_mul (q : G) (e : E) :
    subOf E a hE σ V (q * e) = act (σ e)⁻¹ (subOf E a hE σ V q) := by
  unfold subOf
  have h1 : (⟨ev E a (q * e), ev_mem hE (q * e)⟩ : E) = ⟨ev E a q, ev_mem hE q⟩ * e :=
    Subtype.ext (ev_mul e.2)
  rw [h1, map_mul, _root_.mul_inv_rev, act_mul]

theorem rel_of_eq {X : Type*} {N : ℕ} (R : ℕ → G) (hcov : ∀ q, ∃ i < N, q * (R i)⁻¹ ∈ H)
    (F : G → X) (hF : ∀ u v, u * v⁻¹ ∈ H → F u = F v) (P : Fin N → X)
    (hP : Function.Injective P) (hPF : ∀ k, ∃ q, P k = F q) :
    (Function.Injective fun i : Fin N => F (R i)) ∧ (∀ u v, F u = F v → u * v⁻¹ ∈ H) ∧
      ∀ i : Fin N, ∃ k, P k = F (R i) := by
  have hPR : ∀ k, ∃ i : Fin N, P k = F (R i) := by
    intro k
    obtain ⟨q, hq⟩ := hPF k
    obtain ⟨i, hi, hr⟩ := hcov q
    exact ⟨⟨i, hi⟩, hq.trans (hF _ _ hr)⟩
  choose c hc using hPR
  have hcinj : Function.Injective c := by
    intro k k' h
    apply hP
    rw [hc k, hc k', h]
  have hcsurj : Function.Surjective c := Finite.injective_iff_surjective.1 hcinj
  have hinj : Function.Injective fun i : Fin N => F (R i) := by
    intro i j h
    obtain ⟨k, rfl⟩ := hcsurj i
    obtain ⟨k', rfl⟩ := hcsurj j
    have : P k = P k' := by
      rw [hc k, hc k']
      exact h
    rw [hP this]
  refine ⟨hinj, fun u v huv => ?_, fun i => ?_⟩
  swap
  · obtain ⟨k, rfl⟩ := hcsurj i
    exact ⟨k, hc k⟩
  obtain ⟨i, hi, hu⟩ := hcov u
  obtain ⟨j, hj, hv⟩ := hcov v
  have hij : (⟨i, hi⟩ : Fin N) = ⟨j, hj⟩ := by
    apply hinj
    change F (R i) = F (R j)
    rw [← hF _ _ hu, ← hF _ _ hv, huv]
  have e : i = j := congrArg Fin.val hij
  subst e
  have : u * v⁻¹ = (u * (R i)⁻¹) * (v * (R i)⁻¹)⁻¹ := by group
  rw [this]
  exact H.mul_mem hu (H.inv_mem hv)

end CFSG.KC.Fi24FixC

end
