module

public import Certificates.Data.Kernel.PtEnum
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBase

public section

namespace CFSG.KC.PtEnum

open CFSG.QuasithinUnique.K1.SporadicPerm

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)]

theorem mem_submonoid_of_finite [Finite Γ] {S : Set Γ} {x : Γ} (hx : x ∈ Subgroup.closure S) :
    x ∈ Submonoid.closure S := by
  let H : Subgroup Γ :=
    { Submonoid.closure S with
      inv_mem' := fun {y} hy => by
        have hc : 0 < Nat.card Γ := Nat.card_pos
        have e : y⁻¹ = y ^ (Nat.card Γ - 1) := by
          refine (eq_inv_of_mul_eq_one_left ?_).symm
          rw [← pow_succ, Nat.sub_add_cancel hc, pow_card_eq_one']
        rw [e]
        exact Submonoid.pow_mem _ hy _ }
  have hle : Subgroup.closure S ≤ H := (Subgroup.closure_le H).2 Submonoid.subset_closure
  exact hle hx

structure RowsFacts (n : ℕ) (P : List ℕ) (G : List (ℕ → ℕ)) (Ts : Array (List ℕ))
    (par lab cl : Array ℕ) : Prop where
  pos : 0 < Ts.size
  first : Ts[0]! = P
  lt : ∀ i < Ts.size, ∀ p ∈ Ts[i]!, p < n
  nodup : Ts.toList.Nodup
  clos : ∀ i < Ts.size, ∀ j < G.length, cl[i * G.length + j]! < Ts.size ∧
    Ts[cl[i * G.length + j]!]! = (Ts[i]!).map (getF G j)
  reach : ∀ i < Ts.size, 0 < i →
    par[i]! < i ∧ lab[i]! < G.length ∧ cl[par[i]! * G.length + lab[i]!]! = i

theorem rows_facts {P : List ℕ} {G : List (ℕ → ℕ)} {Ts : Array (List ℕ)} {par lab cl : Array ℕ}
    (h : rowsOKF n P G Ts par lab cl = true) : RowsFacts n P G Ts par lab cl := by
  unfold rowsOKF at h
  simp only [Bool.and_eq_true, Nat.blt_eq, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h0, h1⟩, hlt⟩, hnd⟩, hcl⟩, hpar⟩ := h
  refine ⟨h0, h1, fun i hi p hp => ?_, hnd, hcl, fun i hi hpos => ?_⟩
  · rw [getElem!_pos Ts i hi] at hp
    simpa using hlt _ (Array.getElem_mem_toList hi) p hp
  · obtain ⟨⟨h1, h2⟩, h3⟩ := (hpar i hi).resolve_left (by omega)
    exact ⟨h1, h2, h3⟩

section Sound

variable {P : List ℕ} {gens : List Γ} {G : List (ℕ → ℕ)} {Ts : Array (List ℕ)}
  {par lab cl : Array ℕ}

theorem row_mul (hG : ∀ j < gens.length, ∀ p < n, getF G j p = act n (gens.getD j 1) p)
    {T : List ℕ} (hT : ∀ p ∈ T, p < n) {x : Γ} (hx : rt n P x = T) {j : ℕ}
    (hj : j < gens.length) (hPx : ∀ p ∈ P, p < n) :
    rt n P (gens.getD j 1 * x) = T.map (getF G j) := by
  rw [← hx]
  unfold rt
  rw [List.map_map]
  refine List.map_congr_left fun p hp => ?_
  rw [Function.comp_apply, act_mul _ _ (hPx p hp), hG j hj _ (act_lt x (hPx p hp))]

theorem rows_reach (hlen : G.length = gens.length)
    (hG : ∀ j < gens.length, ∀ p < n, getF G j p = act n (gens.getD j 1) p)
    (h : RowsFacts n P G Ts par lab cl) :
    ∀ i < Ts.size, ∃ x ∈ Subgroup.closure {x | x ∈ gens}, rt n P x = Ts[i]! := by
  have hP : ∀ p ∈ P, p < n := fun p hp => h.lt 0 h.pos p (by rw [h.first]; exact hp)
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact ⟨1, one_mem _, by rw [rt_one hP, h.first]⟩
    · obtain ⟨hp1, hp2, hp3⟩ := h.reach i hi hpos
      obtain ⟨y, hy, hty⟩ := ih _ hp1 (by omega)
      have hj : lab[i]! < gens.length := by rw [← hlen]; exact hp2
      refine ⟨gens.getD (lab[i]!) 1 * y,
        mul_mem (Subgroup.subset_closure (by
          rw [Set.mem_setOf_eq, List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj)) hy, ?_⟩
      rw [row_mul hG (h.lt _ (by omega)) hty hj hP]
      have := (h.clos (par[i]!) (by omega) _ hp2).2
      rw [hp3] at this
      exact this.symm

theorem rows_closed [Finite Γ] (hlen : G.length = gens.length)
    (hG : ∀ j < gens.length, ∀ p < n, getF G j p = act n (gens.getD j 1) p)
    (h : RowsFacts n P G Ts par lab cl) :
    ∀ x ∈ Subgroup.closure {x | x ∈ gens}, rt n P x ∈ Ts.toList := by
  have hP : ∀ p ∈ P, p < n := fun p hp => h.lt 0 h.pos p (by rw [h.first]; exact hp)
  intro x hx
  have hm := mem_submonoid_of_finite hx
  clear hx
  induction hm using Submonoid.closure_induction_left with
  | one =>
    rw [rt_one hP, ← h.first, getElem!_pos Ts 0 h.pos]
    exact Array.getElem_mem_toList h.pos
  | mul_left s hs y _ ih =>
    obtain ⟨i, hi, hiy⟩ := List.getElem_of_mem ih
    have hi' : i < Ts.size := by simpa using hi
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem (show s ∈ gens from hs)
    have hTi : Ts[i]! = rt n P y := by rw [getElem!_pos Ts i hi']; simpa using hiy
    have hr := row_mul hG (h.lt i hi') hTi.symm hj hP
    rw [List.getD_eq_getElem _ _ hj] at hr
    have hc := h.clos i hi' j (by rw [hlen]; exact hj)
    rw [hr, ← hc.2, getElem!_pos Ts _ hc.1]
    exact Array.getElem_mem_toList _

theorem rt_inj [Finite Γ] (hbase : ∀ g : Γ, (∀ b ∈ P, act n g b = b) → g = 1)
    (hP : ∀ p ∈ P, p < n) {x y : Γ} (e : rt n P x = rt n P y) : x = y :=
  rt_injective hP (fun _ hb => hb) hbase e

theorem card_of_rowsOKF [Finite Γ] (hbase : ∀ g : Γ, (∀ b ∈ P, act n g b = b) → g = 1)
    (hlen : G.length = gens.length)
    (hG : ∀ j < gens.length, ∀ p < n, getF G j p = act n (gens.getD j 1) p)
    (h : rowsOKF n P G Ts par lab cl = true) :
    Nat.card (Subgroup.closure {x | x ∈ gens}) = Ts.size := by
  have hf := rows_facts h
  have hP : ∀ p ∈ P, p < n := fun p hp => hf.lt 0 hf.pos p (by rw [hf.first]; exact hp)
  have himg : rt n P '' (Subgroup.closure {x | x ∈ gens} : Set Γ) = {T | T ∈ Ts.toList} := by
    ext T
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact rows_closed hlen hG hf x hx
    · intro hT
      obtain ⟨i, hi, hiT⟩ := List.getElem_of_mem hT
      have hi' : i < Ts.size := by simpa using hi
      obtain ⟨x, hx, hxT⟩ := rows_reach hlen hG hf i hi'
      refine ⟨x, hx, ?_⟩
      rw [hxT, getElem!_pos Ts i hi']
      simpa using hiT
  have h1 : Nat.card ↥(Subgroup.closure {x | x ∈ gens}) =
      (rt n P '' (Subgroup.closure {x | x ∈ gens} : Set Γ)).ncard := by
    rw [Set.ncard_image_of_injective _ fun x y e => rt_inj hbase hP e]
    exact Nat.card_coe_set_eq _
  rw [h1, himg]
  have : {T | T ∈ Ts.toList} = ((Ts.toList.toFinset : Finset (List ℕ)) : Set (List ℕ)) := by
    ext T; simp
  rw [this, Set.ncard_coe_finset, List.toFinset_card_of_nodup hf.nodup]
  simp

theorem mem_of_rowsOKF [Finite Γ] (hbase : ∀ g : Γ, (∀ b ∈ P, act n g b = b) → g = 1)
    (hlen : G.length = gens.length)
    (hG : ∀ j < gens.length, ∀ p < n, getF G j p = act n (gens.getD j 1) p)
    (h : rowsOKF n P G Ts par lab cl = true) {x : Γ} (hx : rt n P x ∈ Ts.toList) :
    x ∈ Subgroup.closure {x | x ∈ gens} := by
  have hf := rows_facts h
  have hP : ∀ p ∈ P, p < n := fun p hp => hf.lt 0 hf.pos p (by rw [hf.first]; exact hp)
  obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hx
  have hi' : i < Ts.size := by simpa using hi
  obtain ⟨y, hy, hyT⟩ := rows_reach hlen hG hf i hi'
  have e : rt n P y = rt n P x := by
    rw [hyT, getElem!_pos Ts i hi', ← hix]
    simp
  rw [← rt_inj hbase hP e]
  exact hy

end Sound

end CFSG.KC.PtEnum

end
