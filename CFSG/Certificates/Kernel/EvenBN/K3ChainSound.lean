module

public import Certificates.Data.Kernel.EvenBN.K3Chain
public import CFSG.Certificates.Kernel.EvenBN.YamadaKSound
public import CFSG.Certificates.Kernel.Common.ChainBound
import all CFSG.Fischer.F4

public section

namespace CFSG.KC.K3Chain

open CFSG.KC.Enum CFSG.KC.F4Mat CFSG.KC.YamadaK CFSG.KC.StabChain CFSG.Fischer
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo Certificates.U52Yamada Subgroup Matrix

@[expose] def act (g : SU52) (v : Fin 5 → F4) : Fin 5 → F4 := mat g *ᵥ v

theorem act_mul (g h : SU52) (v : Fin 5 → F4) : act (g * h) v = act g (act h v) := by
  simp only [act, mat_mul, Matrix.mulVec_mulVec]

theorem act_one (v : Fin 5 → F4) : act 1 v = v := by
  simp only [act, mat_one, Matrix.one_mulVec]

@[expose] noncomputable def colV (P j : Nat) : Fin 5 → F4 := fun i => f4 (ent P (5 * i.val + j))

@[expose] noncomputable def bv (j : Nat) : Fin 5 → F4 := colV baseK j

@[expose] def vkey (v : Fin 5 → F4) : Nat :=
  code (v 0) + 4 * (code (v 1) + 4 * (code (v 2) + 4 * (code (v 3) + 4 * code (v 4))))

theorem mulVec_colV (A B : Nat) {j : Nat} (hj : j < 5) :
    decM A *ᵥ colV B j = colV (mulK A B) j := by
  funext i
  have h := congrFun (congrFun (decM_mulK A B) i) ⟨j, hj⟩
  rw [Matrix.mul_apply] at h
  exact h.symm

theorem code_f4 (c : Nat) : code (f4 c) = c % 4 := rfl

theorem ent_mod (N k : Nat) : ent N k % 4 = ent N k := Nat.mod_mod _ _

theorem colKey_eq (P j : Nat) : colKey P j = vkey (colV P j) := by
  simp only [colKey, vkey, colV, code_f4, ent_mod, Fin.val_zero, Fin.val_one,
    Fin.val_two, Nat.add_eq, Nat.mul_eq]
  norm_num [Nat.add_comm]

theorem colV_of_colEq {P B j : Nat} (h : colEq P B j = true) : colV P j = colV B j := by
  simp only [colEq, Bool.and_eq_true, Nat.beq_eq, Nat.add_eq] at h
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := h
  simp only [Nat.add_comm] at h1 h2 h3 h4
  funext i
  fin_cases i <;> simp [colV, h0, h1, h2, h3, h4, Nat.add_comm]

@[expose] def kgen (i : Fin 10) : SU52 :=
  ![uSU, vSU, 1, 1, x₂SU 1, x₂SU F4.ω, x₁SU 0 1 (by decide), 1, x₃SU 1, 1] i

@[expose] def wSU (w : List (Fin 10)) : SU52 := (w.map kgen).prod

theorem kgen_mem (i : Fin 10) : kgen i ∈ K₃sub := by
  have hz : x₁SU 0 1 (by decide) ∈ K₃sub := by
    unfold K₃sub
    exact mem_sup_left (mem_sup_left (mem_sup_left (mem_sup_left (mem_sup_left
      ((mem_x₁Sub (P := (· = 0)) (hP0 := rfl) (hPadd := zero_add_zero)).2 ⟨0, 1, rfl, rfl⟩)))))
  have h2 : ∀ a, x₂SU a ∈ K₃sub := fun a => by
    unfold K₃sub
    exact mem_sup_left (mem_sup_left (mem_sup_left (mem_sup_left (mem_sup_right (x₂SU_mem a)))))
  have h3 : x₃SU 1 ∈ K₃sub := by
    unfold K₃sub
    exact mem_sup_left (mem_sup_left (mem_sup_left (mem_sup_right (x₃SU_mem 1))))
  have hu : uSU ∈ K₃sub := by
    unfold K₃sub
    exact mem_sup_left (mem_sup_right (mem_zpowers uSU))
  have hv : vSU ∈ K₃sub := by
    unfold K₃sub
    exact mem_sup_right (mem_zpowers vSU)
  fin_cases i
  · exact hu
  · exact hv
  · exact K₃sub.one_mem
  · exact K₃sub.one_mem
  · exact h2 1
  · exact h2 F4.ω
  · exact hz
  · exact K₃sub.one_mem
  · exact h3
  · exact K₃sub.one_mem

theorem mat_kgen : ∀ i : Fin 10, okL i = true → mat (kgen i) = genMat i := by
  intro i h
  fin_cases i <;> first | rfl | exact absurd h (by decide)

theorem wSU_mem (w : List (Fin 10)) : wSU w ∈ K₃sub :=
  list_prod_mem fun x hx => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact kgen_mem i

theorem mat_wSU : ∀ w : List (Fin 10), (∀ i ∈ w, okL i = true) → mat (wSU w) = wordMat w
  | [], _ => rfl
  | i :: w, h => by
    rw [wSU, List.map_cons, List.prod_cons, mat_mul, ← wSU,
      mat_kgen i (h i List.mem_cons_self), mat_wSU w (fun k hk => h k (List.mem_cons_of_mem _ hk)),
      wordMat, wordMat, List.map_cons, List.prod_cons]

theorem act_wSU {w : List (Fin 10)} (hw : ∀ i ∈ w, okL i = true) {j : Nat} (hj : j < 5) :
    act (wSU w) (bv j) = colV (mulK (wordK w) baseK) j := by
  rw [act, mat_wSU w hw, ← wordK_eq, bv, mulVec_colV _ _ hj]

theorem fixK_spec {P : Nat} : ∀ j, fixK j P = true → ∀ k < j, colEq P baseK k = true
  | 0, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | j + 1, h, k, hk => by
    have h' : (fixK j P && colEq P baseK j) = true := h
    rw [Bool.and_eq_true] at h'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact fixK_spec j h'.1 k hk
    · exact h'.2

theorem wordOK_spec {j : Nat} {w : List (Fin 10)} (h : wordOK j w = true) :
    (∀ i ∈ w, okL i = true) ∧ ∀ k < j, colV (mulK (wordK w) baseK) k = bv k := by
  rw [wordOK, Bool.and_eq_true, List.all_eq_true, strictB_app] at h
  exact ⟨h.1, fun k hk => colV_of_colEq (fixK_spec j h.2 k hk)⟩

theorem imgKey_eq (j : Nat) (w : List (Fin 10)) :
    imgKey j w = vkey (colV (mulK (wordK w) baseK) j) := by
  rw [imgKey, strictN_app, colKey_eq]

theorem incrFrom_spec : ∀ (l : List Nat) (p : Nat), incrFrom l p = true →
    (∀ x ∈ l, p < x) ∧ l.Nodup
  | [], _, _ => ⟨fun _ hx => absurd hx List.not_mem_nil, List.nodup_nil⟩
  | a :: l, p, h => by
    have h' : (Nat.blt p a && incrFrom l a) = true := h
    rw [Bool.and_eq_true, Nat.blt_eq] at h'
    obtain ⟨hl, hnd⟩ := incrFrom_spec l a h'.2
    refine ⟨fun x hx => ?_, List.nodup_cons.2 ⟨fun ha => lt_irrefl a (hl a ha), hnd⟩⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h'.1
    · exact h'.1.trans (hl x hx)

@[expose] noncomputable def toL :Nat → List (List (List (Fin 10))) → List ((Fin 5 → F4) × List SU52)
  | _, [] => []
  | j, T :: Ts => (bv j, T.map wSU) :: toL (j + 1) Ts

theorem toL_lengths : ∀ (j : Nat) (Ts : List (List (List (Fin 10)))),
    (toL j Ts).map (fun l => l.2.length) = Ts.map List.length
  | _, [] => rfl
  | j, T :: Ts => by
    rw [toL, List.map_cons, List.map_cons, toL_lengths (j + 1) Ts, List.length_map]

theorem chain_of_levelsOK : ∀ (Ts : List (List (List (Fin 10)))) (j : Nat), levelsOK Ts j = true →
    ChainOK act K₃sub (toL j Ts) ∧ ∀ l ∈ toL j Ts, ∀ t ∈ l.2, ∀ k < j, act t (bv k) = bv k
  | [], _, _ => ⟨trivial, fun _ hl => absurd hl List.not_mem_nil⟩
  | T :: Ts, j, h => by
    have h' : (Nat.blt j 5 && levelOK j T && levelsOK Ts (j + 1)) = true := h
    rw [Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq] at h'
    obtain ⟨⟨hj5, hlev⟩, hrest⟩ := h'
    obtain ⟨hC, hF⟩ := chain_of_levelsOK Ts (j + 1) hrest
    rw [levelOK, Bool.and_eq_true, List.all_eq_true] at hlev
    obtain ⟨hw, hinc⟩ := hlev
    have hfix : ∀ w ∈ T, ∀ k < j, act (wSU w) (bv k) = bv k := fun w hwT k hk => by
      obtain ⟨hok, hcol⟩ := wordOK_spec (hw w hwT)
      rw [act_wSU hok (hk.trans hj5), hcol k hk]
    have himg : (T.map wSU).map (fun t => act t (bv j)) =
        T.map (fun w => colV (mulK (wordK w) baseK) j) := by
      rw [List.map_map]
      exact List.map_congr_left fun w hwT => act_wSU (wordOK_spec (hw w hwT)).1 hj5
    have hkeys : (T.map fun w => colV (mulK (wordK w) baseK) j).map vkey = T.map (imgKey j) := by
      rw [List.map_map]
      exact List.map_congr_left fun w _ => (imgKey_eq j w).symm
    refine ⟨⟨fun t ht => ?_, ?_, fun l hl t ht => hF l hl t ht j (Nat.lt_succ_self j), hC⟩, ?_⟩
    · obtain ⟨w, -, rfl⟩ := List.mem_map.1 ht
      exact wSU_mem w
    · rw [himg]
      exact List.Nodup.of_map vkey (hkeys ▸ (incrFrom_spec _ 0 hinc).2)
    · intro l hl t ht k hk
      rcases List.mem_cons.1 hl with rfl | hl
      · obtain ⟨w, hwT, rfl⟩ := List.mem_map.1 ht
        exact hfix w hwT k hk
      · exact hF l hl t ht k (hk.trans (Nat.lt_succ_self j))

theorem card_ge_of_chainK (Ts : List (List (List (Fin 10)))) (h : chainK Ts = true) :
    (Ts.map List.length).prod ≤ Nat.card K₃sub := by
  have := prod_le_card_of_chainOK act act_mul act_one K₃sub (toL 0 Ts)
    (chain_of_levelsOK Ts 0 h).1
  rwa [toL_lengths] at this

end CFSG.KC.K3Chain
