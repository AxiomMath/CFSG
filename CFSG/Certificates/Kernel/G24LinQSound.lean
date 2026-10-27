module

public import CFSG.Certificates.Kernel.G24LinSound
public import Certificates.Data.Kernel.G24LinQ

public section

namespace CFSG.KC.G24Lin

open CFSG.KD.G24Lin CFSG.Quasithin.St84.G24LE Matrix

theorem bz_eq_zB (x i : ℕ) : bz x i = zB (bitK x i) := rfl

theorem monoVal_bz {n : ℕ} (w : ℕ) (ν : Mono n) : monoVal (fun i => bz w i) ν = zB (monoB w ν) := by
  cases ν with
  | inl i => rfl
  | inr p =>
    simp only [monoVal, monoB, zB, bz]
    by_cases h1 : bitK w p.1.1.val = true <;> by_cases h2 : bitK w p.1.2.val = true <;>
      simp [h1, h2]

theorem quadM_entry {n d : ℕ} (R : Fin 3 → Matrix (Fin n) (Fin n) (ZMod 2))
    (S : Fin 3 → Matrix (Fin d) (Fin d) (ZMod 2)) (RC SR TB : ℕ)
    (hR : ∀ g i j, R g i j = bz (laneK RC (g.val * n + j.val)) i.val)
    (hS : ∀ g t s, S g t s = bz (laneK SR (g.val * d + t.val)) s.val)
    (hT : ∀ (μ : Mono n) (i : Fin n), testVec μ i = bz (laneK TB (monoKey μ)) i.val)
    (r : Fin 3 × Mono n × Fin d) (u : Mono n × Fin d) :
    quadM R S r u = zB (entryB RC SR TB r u) := by
  obtain ⟨g, μ, t⟩ := r
  obtain ⟨ν, s⟩ := u
  have hv : testVec μ = fun i => bz (laneK TB (monoKey μ)) i.val := funext (hT μ)
  have hw : R g *ᵥ testVec μ = fun i => bz (wvK RC n g.val (laneK TB (monoKey μ))) i.val := by
    funext i
    rw [hv]
    exact mulVec_bz (R g) (fun j => laneK RC (g.val * n + j)) (fun i => i.val)
      (fun i j => hR g i j) _ i
  simp only [quadM, Matrix.of_apply]
  rw [hw, hv, monoVal_bz, monoVal_bz, hS]
  simp only [entryB, Nat.add_eq, Nat.mul_eq, bz_eq_zB]
  generalize monoB (wvK RC n g.val (laneK TB (monoKey μ))) ν = a
  generalize monoB (laneK TB (monoKey μ)) ν = c
  generalize bitK (laneK SR (g.val * d + t.val)) s.val = b
  by_cases h : t = s <;> cases a <;> cases b <;> cases c <;> simp [h, zB] <;> decide

theorem pinM_spec {R C : Type*} {rows : List R} {cols : List C} {M : R → C → ZMod 2}
    {kr : R → ℕ} {kc : C → ℕ} {o : ℕ} {D : ℕ → ℕ} (h : pinM rows cols M kr kc o D = true) :
    ∀ r ∈ rows, ∀ u ∈ cols, M r u = bz (D (o + kr r)) (kc u) := by
  intro r hr u hu
  unfold pinM at h
  rw [List.all_eq_true] at h
  have h2 := h r hr
  rw [List.all_eq_true] at h2
  exact beq_iff_eq.1 (h2 u hu)

theorem rowsK_cons (D : ℕ → ℕ) (o : ℕ) (l : List Char) (L : List (List Char)) :
    rowsK D o (l :: L) = (Nat.beq (D o) (packC l) && rowsK D (o + 1) L) := rfl

theorem rowsK_spec (D : ℕ → ℕ) : ∀ (L : List (List Char)) (o : ℕ), rowsK D o L = true →
    ∀ i < L.length, D (o + i) = packC (L.getD i [])
  | [], _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | l :: L, o, h, i, hi => by
    rw [rowsK_cons, Bool.and_eq_true] at h
    cases i with
    | zero =>
      rw [Nat.add_zero, List.getD_cons_zero]
      exact Nat.eq_of_beq_eq_true h.1
    | succ i =>
      have e : o + (i + 1) = o + 1 + i := by omega
      rw [e, List.getD_cons_succ]
      exact rowsK_spec D L (o + 1) h.2 i (by simpa using hi)

theorem bits_ofList_getD (l : List Char) (j : ℕ) :
    (bits (String.ofList l)).getD j 0 = bz (packC l) j := by
  rw [bz_eq_zB, bitK_packC]
  unfold bits zB
  rw [String.toList_ofList, getD_toList]
  simp only [Array.toList_map, List.toList_toArray]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases l[j]? with
  | none => simp
  | some c =>
    simp only [Option.map_some, Option.getD_some]
    by_cases h : c = '1'
    · simp [h]
    · simp [h]

theorem ent_ofBits {R C : Type*} (L : List (List Char)) (kr : R → ℕ) (kc : C → ℕ)
    (hr : ∀ r, kr r < L.length) (r : R) (u : C) :
    ent (ofBits (L.map String.ofList)) kr kc r u = bz (packC (L.getD (kr r) [])) (kc u) := by
  have e : ((L.map String.ofList).map bits).toArray.getD (kr r) #[] =
      bits (String.ofList (L.getD (kr r) [])) := by
    rw [getD_toList, List.toList_toArray, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_map, List.getElem?_eq_getElem (hr r), Option.map_some, Option.map_some,
      Option.getD_some, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hr r),
      Option.getD_some]
  unfold ent ofBits
  rw [Matrix.of_apply, e, bits_ofList_getD]

theorem mem_of_keys {α : Type*} {L : List α} {key : α → ℕ} (h : ∀ x, L[key x]? = some x) (x : α) :
    x ∈ L :=
  List.mem_of_getElem? (h x)

theorem lt_of_keys {α : Type*} {L : List α} {key : α → ℕ} (h : ∀ x, L[key x]? = some x) (x : α) :
    key x < L.length :=
  (List.getElem?_eq_some_iff.1 (h x)).1

theorem spanOK_glue {R C K : Type*} [Fintype R] [DecidableEq R] [Fintype C] [DecidableEq C]
    [Fintype K] [DecidableEq K] (rowsL : List R) (colsL : List C) (ksL : List K) (kr : R → ℕ)
    (kc : C → ℕ) (kk : K → ℕ) (hR : ∀ x, rowsL[kr x]? = some x) (hC : ∀ x, colsL[kc x]? = some x)
    (hK : ∀ x, ksL[kk x]? = some x) (hcR : Fintype.card R = rowsL.length)
    (hcC : Fintype.card C = colsL.length) (hcK : Fintype.card K = ksL.length)
    (m M' : Matrix R C (ZMod 2)) (hmM : ∀ r u, m r u = M' r u) (k : Matrix C K (ZMod 2))
    (pch ych : List (List Char)) (D : ℕ → ℕ) (hpl : pch.length = ksL.length)
    (hyl : ych.length = colsL.length)
    (hm : pinM rowsL colsL M' kr kc (ksL.length + (colsL.length + colsL.length)) D = true)
    (hk : pinM colsL ksL k kc kk ksL.length D = true)
    (hp : rowsK D 0 pch = true) (hy : rowsK D (ksL.length + colsL.length) ych = true)
    (hs : spanK D ksL.length colsL.length rowsL.length = true) :
    spanOK m (ent (tab rowsL colsL fun r u => m r u) kr kc) k
      (ent (ofBits (pch.map String.ofList)) kk kc) (ent (ofBits (ych.map String.ofList)) kc kr) =
        true := by
  have hpk : ∀ x, kk x < pch.length := fun x => by
    rw [hpl]
    exact lt_of_keys hK x
  have hyc : ∀ x, kc x < ych.length := fun x => by
    rw [hyl]
    exact lt_of_keys hC x
  refine spanOK_of (eqvOf rowsL kr hR hcR) (eqvOf colsL kc hC hcC) (eqvOf ksL kk hK hcK) D
    (ent_tab rowsL colsL _ kr kc hR hC) ?_ ?_ ?_ ?_ hs
  · intro r u
    rw [hmM]
    exact pinM_spec hm r (mem_of_keys hR r) u (mem_of_keys hC u)
  · intro c κ
    exact pinM_spec hk c (mem_of_keys hC c) κ (mem_of_keys hK κ)
  · intro κ c
    rw [ent_ofBits pch kk kc hpk]
    have e := rowsK_spec D pch 0 hp (kk κ) (hpk κ)
    rw [Nat.zero_add] at e
    rw [← e]
    rfl
  · intro c r
    rw [ent_ofBits ych kc kr hyc, ← rowsK_spec D ych _ hy (kc c) (hyc c)]
    rfl

end CFSG.KC.G24Lin

end
