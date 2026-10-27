module

public import Certificates.Data.Kernel.PermCent.KGrpC
public import CFSG.Certificates.Kernel.PermCent.CVSound

public section

namespace CFSG.Certificates.Kernel.PkCV.KGrp

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.GH74.KGroups

variable {n : Nat} [Small n]

theorem eq_one_ev (g : CV n) : decide (ev g = 1) = decide (g = 1) := by
  rw [one_eq_ev, decide_ev_eq]

theorem powOneC_eq' (g : CV n) (k : Nat) : decide (g ^ k = 1) = powOneC g k :=
  (powOneC_eq g k).symm

theorem evalW_ev (a b : CV n) (w : List Bool) : evalW (ev a) (ev b) w = ev (evalW a b w) :=
  (map_evalW (evHom n) a b w).symm

theorem mem3_ev (y x : CV n) :
    decide (ev y ∈ ([1, ev x, ev (x ^ 2)] : List (Equiv.Perm (Fin n)))) =
      decide (y ∈ ([1, x, x ^ 2] : List (CV n))) := by
  rw [one_eq_ev]
  exact decide_mem_map_ev [1, x, x ^ 2] y

theorem mem_pow3_ev (z x y : CV n) :
    decide (ev z ∈ pow3list (ev x) (ev y)) = decide (z ∈ pow3list x y) := by
  have h : pow3list (ev x) (ev y) = (pow3list x y).map ev := (pow3list_map (evHom n) x y).symm
  rw [h]
  exact decide_mem_map_ev _ z

theorem map_cOf_ev (L : List (Equiv.Perm (Fin n))) : (L.map cOf).map ev = L := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id L]
  exact List.map_congr_left fun σ _ => ev_cOf σ

theorem prod_map {α β γ δ : Type*} (f : α → γ) (g : β → δ) (A : List α) (B : List β) :
    (A.map f) ×ˢ (B.map g) = (A ×ˢ B).map (Prod.map f g) := by
  induction A with
  | nil => rfl
  | cons a A ih =>
    rw [List.map_cons, List.product_cons, List.product_cons, ih, List.map_append, List.map_map,
      List.map_map]
    rfl

theorem orderIs_C (g : CV n) (m : Nat) : orderIs (ev g) m = orderIsC g m := by
  unfold orderIs orderIsC
  simp only [ev_pow', eq_one_ev, powOneC_eq']

theorem pairInvB_C (ws : List (List Bool × ℕ)) (a b : CV n) :
    pairInvB ws (ev a) (ev b) = pairInvC ws a b := by
  unfold pairInvB pairInvC
  simp only [evalW_ev, orderIs_C]

theorem centTriv_C (L : List (CV n)) (a b : CV n) :
    centTrivCheck (L.map ev) (ev a) (ev b) = centTrivC L a b := by
  unfold centTrivCheck centTrivC
  simp only [List.all_map, Function.comp_def, ev_mul', decide_ev_eq, comm_fast, eq_one_ev]

theorem norm_C (QP : RawSchreierDatum n) (G : List (CV n)) (a b : CV n) :
    normCheck QP (G.map ev) (ev a) (ev b) = normC QP G a b := by
  unfold normCheck normC
  simp only [List.all_map, Function.comp_def, ev_mul', ev_inv', sift_ev]

theorem pairCount_C (QP : RawSchreierDatum n) (oa ob : ℕ) (ws : List (List Bool × ℕ)) :
    pairCountB QP oa ob ws = pairCountC (elemsC QP) oa ob ws := by
  unfold pairCountB pairCountC
  rw [elemsT_eq_elemsC, List.filter_map, List.filter_map, prod_map, List.filter_map,
    List.length_map]
  simp only [Function.comp_def, Prod.map_fst, Prod.map_snd, orderIs_C, pairInvB_C]

theorem inner3_C (LA : List (CV n)) (QP : RawSchreierDatum n) :
    inner3check (LA.map ev) QP = inner3C LA QP := by
  unfold inner3check inner3C
  simp only [List.all_map, Function.comp_def, ev_pow', eq_one_ev, powOneC_eq', sift_ev]

theorem cent_C (L : List (CV n)) (τ : CV n) :
    (L.map ev).filter (fun g => decide (g * ev τ = ev τ * g)) = (centL L τ).map ev := by
  rw [List.filter_map]
  unfold centL
  simp only [Function.comp_def, ev_mul', decide_ev_eq, comm_fast]

theorem e9at_C (C : List (CV n)) : e9at (C.map ev) = e9atC C := by
  unfold e9at e9atC
  simp only [List.all_map, Function.comp_def, ne_eq, decide_not, ev_mul', ev_pow', eq_one_ev,
    decide_ev_eq, powOneC_eq', comm_fast]

theorem e9free_C (L : List (CV n)) : e9free (L.map ev) = e9freeC L := by
  unfold e9free e9freeC
  simp only [List.all_map, Function.comp_def, ne_eq, decide_not, ev_pow', eq_one_ev, powOneC_eq',
    cent_C, e9at_C]

theorem e9all_C (L : List (CV n)) : e9all (L.map ev) = e9allC L := by
  unfold e9all e9allC
  simp only [List.filter_map, List.all_map, Function.comp_def, ne_eq, Bool.decide_and, decide_not,
    ev_mul', ev_pow', eq_one_ev, decide_ev_eq, powOneC_eq', comm_fast]

theorem e27at_C (X : CV n) (C : List (CV n)) : e27at (ev X) (C.map ev) = e27atC X C := by
  unfold e27at e27atC
  simp only [List.all_map, Function.comp_def, ne_eq, decide_not, ev_mul', ev_pow', decide_ev_eq,
    comm_fast, mem3_ev, mem_pow3_ev]

theorem e27free_C (L : List (CV n)) : e27free (L.map ev) = e27freeC L := by
  unfold e27free e27freeC
  simp only [List.all_map, List.filter_map, Function.comp_def, ne_eq, Bool.decide_and, decide_not,
    ev_mul', ev_pow', eq_one_ev, decide_ev_eq, powOneC_eq', comm_fast, e27at_C]

theorem e27freeF_eq (L : List (CV n)) : e27freeC L = e27freeF L := by
  unfold e27freeC e27freeF e27at3
  congr 1
  funext X
  rw [List.filter_filter]
  simp only [Bool.and_comm]

theorem length_filter_product {α β : Type*} (A : List α) (B : List β) (p : α → β → Bool) :
    ((A ×ˢ B).filter fun q => p q.1 q.2).length = (A.map fun a => (B.filter (p a)).length).sum := by
  induction A with
  | nil => rfl
  | cons a A ih =>
    rw [List.product_cons, List.filter_append, List.length_append, ih, List.filter_map,
      List.length_map, List.map_cons, List.sum_cons]
    rfl

theorem pairAll_count (Lx Ly : List (CV n)) (ws : List (List Bool × ℕ)) (c : ℕ)
    (h : pairAll Lx Ly ws c = true) :
    ((Lx ×ˢ Ly).filter fun q => pairInvC ws q.1 q.2).length = Lx.length * c := by
  rw [length_filter_product]
  unfold pairAll at h
  induction Lx with
  | nil => simp
  | cons a A ih =>
    rw [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    rw [List.map_cons, List.sum_cons, h.1, ih h.2, List.length_cons, Nat.succ_mul, Nat.add_comm]

theorem evalW_conj {G : Type*} [Group G] (g a b : G) (w : List Bool) :
    evalW (g * a * g⁻¹) (g * b * g⁻¹) w = g * evalW a b w * g⁻¹ := by
  induction w with
  | nil => simp [evalW]
  | cons c w ih =>
    cases c
    · rw [evalW, evalW, ih]
      group
    · rw [evalW, evalW, ih]
      group

theorem orderIsC_conj (g x : CV n) (m : Nat) : orderIsC (g * x * g⁻¹) m = orderIsC x m := by
  have h : ∀ y : CV n, g * y * g⁻¹ = 1 ↔ y = 1 := fun y =>
    ⟨fun h => by simpa [mul_assoc] using congrArg (fun z => g⁻¹ * z * g) h, fun h => by simp [h]⟩
  unfold orderIsC
  simp only [← powOneC_eq', conj_pow, h]

theorem pairInvC_conj (ws : List (List Bool × ℕ)) (g a b : CV n) :
    pairInvC ws (g * a * g⁻¹) (g * b * g⁻¹) = pairInvC ws a b := by
  unfold pairInvC
  simp only [evalW_conj, orderIsC_conj]

theorem mem_elemsC (Q : RawSchreierDatum n) (hQ : ValidSchreier Q) (c : CV n) :
    c ∈ elemsC Q ↔ ev c ∈ Q.originalSubgroup := by
  rw [← mem_elemsT Q hQ, elemsT_eq_elemsC, mem_map_ev]

theorem nodup_elemsC (Q : RawSchreierDatum n) (hQ : ValidSchreier Q) : (elemsC Q).Nodup := by
  have h := nodup_elemsT Q hQ
  rwa [elemsT_eq_elemsC, nodup_map_ev] at h

theorem conj_mem_elemsC (Q : RawSchreierDatum n) (hQ : ValidSchreier Q) {g y : CV n}
    (hg : g ∈ elemsC Q) (hy : y ∈ elemsC Q) : g * y * g⁻¹ ∈ elemsC Q := by
  rw [mem_elemsC Q hQ] at hg hy ⊢
  rw [← ev_mul', ← ev_mul', ← ev_inv']
  exact Q.originalSubgroup.mul_mem (Q.originalSubgroup.mul_mem hg hy)
    (Q.originalSubgroup.inv_mem hg)

theorem partners_conj (Q : RawSchreierDatum n) (hQ : ValidSchreier Q) (ob : ℕ)
    (ws : List (List Bool × ℕ)) (x0 g : CV n) (hg : g ∈ elemsC Q) :
    (((elemsC Q).filter fun y => orderIsC y ob).filter fun y =>
        pairInvC ws (g * x0 * g⁻¹) y).length =
      (((elemsC Q).filter fun y => orderIsC y ob).filter fun y => pairInvC ws x0 y).length := by
  set Ly := (elemsC Q).filter fun y => orderIsC y ob with hLy
  have hg' : g⁻¹ ∈ elemsC Q := by
    rw [mem_elemsC Q hQ] at hg ⊢
    rw [← ev_inv']
    exact Q.originalSubgroup.inv_mem hg
  have hφ : ∀ y, pairInvC ws (g * x0 * g⁻¹) y = pairInvC ws x0 (g⁻¹ * y * g⁻¹⁻¹) := by
    intro y
    rw [← pairInvC_conj ws g⁻¹ (g * x0 * g⁻¹) y]
    congr 1
    group
  have hmem : ∀ y, y ∈ Ly ↔ y ∈ Ly.map fun z => g⁻¹ * z * g⁻¹⁻¹ := by
    intro y
    rw [List.mem_map, hLy, List.mem_filter]
    constructor
    · rintro ⟨hy, ho⟩
      refine ⟨g * y * g⁻¹, List.mem_filter.2 ⟨conj_mem_elemsC Q hQ hg hy, ?_⟩, by group⟩
      rw [orderIsC_conj]
      exact ho
    · rintro ⟨z, hz, rfl⟩
      rw [List.mem_filter] at hz
      exact ⟨conj_mem_elemsC Q hQ hg' hz.1, by rw [orderIsC_conj]; exact hz.2⟩
  have hnd : Ly.Nodup := (nodup_elemsC Q hQ).filter _
  have hnd' : (Ly.map fun z => g⁻¹ * z * g⁻¹⁻¹).Nodup :=
    hnd.map fun a b h => by simpa using h
  have hp : (Ly.map fun z => g⁻¹ * z * g⁻¹⁻¹).Perm Ly :=
    (List.perm_ext_iff_of_nodup hnd' hnd).2 fun y => (hmem y).symm
  simp only [hφ]
  rw [← (hp.filter (pairInvC ws x0)).length_eq, List.filter_map, List.length_map]
  rfl

theorem pairCount_conj (Q : RawSchreierDatum n) (hQ : ValidSchreier Q) (oa ob : ℕ)
    (ws : List (List Bool × ℕ)) (x0 : CV n) (c : ℕ)
    (hcl : ((elemsC Q).filter fun x => orderIsC x oa).all
      (fun x => (elemsC Q).any fun g => eq22C g x0 x g) = true)
    (hc : (((elemsC Q).filter fun y => orderIsC y ob).filter fun y =>
      pairInvC ws x0 y).length = c) :
    pairCountC (elemsC Q) oa ob ws = ((elemsC Q).filter fun x => orderIsC x oa).length * c := by
  unfold pairCountC
  refine pairAll_count _ _ ws c ?_
  unfold pairAll
  rw [List.all_eq_true] at hcl ⊢
  intro x hx
  obtain ⟨g, hg, hgx⟩ := List.any_eq_true.1 (hcl x hx)
  rw [eq22C_eq, decide_eq_true_iff] at hgx
  have hx' : x = g * x0 * g⁻¹ := by rw [hgx, mul_inv_cancel_right]
  rw [beq_iff_eq, hx', partners_conj Q hQ ob ws x0 g hg, hc]

theorem cent3at_C (x : CV n) (C : List (CV n)) : cent3at (ev x) (C.map ev) = cent3atC x C := by
  unfold cent3at cent3atC
  simp only [List.all_map, Function.comp_def, ev_mul', ev_pow', eq_one_ev, decide_ev_eq,
    powOneC_eq', comm_fast, mem3_ev, mem_pow3_ev]

theorem cent3_C (L : List (CV n)) : cent3check (L.map ev) = cent3C L := by
  unfold cent3check cent3C
  simp only [List.all_map, Function.comp_def, ne_eq, decide_not, ev_pow', eq_one_ev, powOneC_eq',
    cent_C, cent3at_C]

theorem pf_le_two (p q a b : ℕ) (hp : p.Prime) (hq : q.Prime) :
    (p ^ a * q ^ b).primeFactors.card ≤ 2 := by
  have h : (p ^ a * q ^ b).primeFactors ⊆ {p, q} := by
    intro r hr
    rw [Nat.mem_primeFactors] at hr
    obtain ⟨hr, hd, -⟩ := hr
    rcases (Nat.Prime.dvd_mul hr).1 hd with h | h
    · rw [(Nat.prime_dvd_prime_iff_eq hr hp).1 (hr.dvd_of_dvd_pow h)]
      exact Finset.mem_insert_self p {q}
    · rw [(Nat.prime_dvd_prime_iff_eq hr hq).1 (hr.dvd_of_dvd_pow h)]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self q)
  exact (Finset.card_le_card h).trans Finset.card_le_two

theorem solv_C (LA LP : List (CV n)) (goods : List ℕ) (h : solvC LA LP goods = true)
    (hg : ∀ c ∈ goods, c.primeFactors.card ≤ 2) : solvCheck (LA.map ev) (LP.map ev) = true := by
  unfold solvCheck
  unfold solvC at h
  simp only [List.all_map, Function.comp_def, ne_eq, decide_not, ev_pow', eq_one_ev, powOneC_eq',
    cent_C, List.length_map]
  rw [List.all_eq_true] at h ⊢
  intro τ hτ
  have h1 := h τ hτ
  cases hc : (powOneC τ 2 && !decide (τ = 1))
  · rfl
  · rw [hc] at h1
    rw [cond_true] at h1 ⊢
    exact decide_eq_true (hg _ (of_decide_eq_true h1))

end CFSG.Certificates.Kernel.PkCV.KGrp

end
