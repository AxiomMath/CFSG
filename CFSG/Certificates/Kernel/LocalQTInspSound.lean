module

public import Certificates.Data.Kernel.LocalQT.Insp
public import CFSG.Certificates.Kernel.LocalQTWordSound
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspM23CheckInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspM22Orb

import CFSG.Certificates.Kernel.LocalQTTab2KSound
import CFSG.Certificates.Kernel.LocalQTSylProved

public section

namespace CFSG.KC.LQT.Insp

open CFSG.QuasithinUnique.Vol2Native.L239 CFSG.QuasithinUnique.Vol2Native.L239.M23Insp
  CFSG.KC.LQT.W CFSG.Blueprint

section Helpers

open Equiv CFSG.KC.LQT.P CFSG.KC.Ord CFSG.KC.LQT.T2

private theorem actT_eq (g c : ℕ) : actT 23 5 g c = img g (c % 23) + 23 * img g (c / 23 % 23) + 529 * img g (c / 23 / 23 % 23) + 12167 * img g (c / 23 / 23 / 23 % 23) + 279841 * img g (c / 23 / 23 / 23 / 23 % 23) := by
  have : actT 23 5 g c = 0 + 1 * img g (c % 23) + 23 * img g (c / 23 % 23) + 529 * img g (c / 23 / 23 % 23) + 12167 * img g (c / 23 / 23 / 23 % 23) + 279841 * img g (c / 23 / 23 / 23 / 23 % 23) := rfl
  omega

private theorem tup_actT (σ : Perm (Fin 23)) (c : ℕ) :
    tup (actT 23 5 (codeP σ) c) = fun i => σ (tup c i) := by
  have t0 : ((tup c 0 : Fin 23) : ℕ) = c % 23 := by simp [tup]
  have t1 : ((tup c 1 : Fin 23) : ℕ) = c / 23 % 23 := by simp [tup]
  have t2 : ((tup c 2 : Fin 23) : ℕ) = c / 23 / 23 % 23 := by
    simp [tup]; omega
  have t3 : ((tup c 3 : Fin 23) : ℕ) = c / 23 / 23 / 23 % 23 := by
    simp [tup]; omega
  have t4 : ((tup c 4 : Fin 23) : ℕ) = c / 23 / 23 / 23 / 23 % 23 := by
    simp [tup]; omega
  have k0 : img (codeP σ) (c % 23) = σ (tup c 0) := by
    rw [← t0]; exact img_code (by norm_num) σ (tup c 0)
  have k1 : img (codeP σ) (c / 23 % 23) = σ (tup c 1) := by
    rw [← t1]; exact img_code (by norm_num) σ (tup c 1)
  have k2 : img (codeP σ) (c / 23 / 23 % 23) = σ (tup c 2) := by
    rw [← t2]; exact img_code (by norm_num) σ (tup c 2)
  have k3 : img (codeP σ) (c / 23 / 23 / 23 % 23) = σ (tup c 3) := by
    rw [← t3]; exact img_code (by norm_num) σ (tup c 3)
  have k4 : img (codeP σ) (c / 23 / 23 / 23 / 23 % 23) = σ (tup c 4) := by
    rw [← t4]; exact img_code (by norm_num) σ (tup c 4)
  have hA := actT_eq (codeP σ) c
  rw [k0, k1, k2, k3, k4] at hA
  have b0 := (σ (tup c 0)).isLt
  have b1 := (σ (tup c 1)).isLt
  have b2 := (σ (tup c 2)).isLt
  have b3 := (σ (tup c 3)).isLt
  have b4 := (σ (tup c 4)).isLt
  funext i
  apply Fin.ext
  have tI : ∀ x, ((tup x i : Fin 23) : ℕ) = x / 23 ^ (i : ℕ) % 23 := fun _ => rfl
  rw [tI, hA]
  fin_cases i <;> simp <;> omega

private theorem enc_tup {c : ℕ} (h : c < 6436343) : enc (tup c) = c := by
  unfold enc; simp [tup]; omega

open CFSG.KC.Ord CFSG.KC.LQT.T2 CFSG.QuasithinUnique.Vol2Native.L239 CFSG.Blueprint

private theorem monoA_spec : ∀ (par : List (ℕ × ℕ)) (i c : ℕ), monoA par i c = true →
    ∀ j (hj : j < par.length), (par[j]).1 ≤ i + j
  | [], _, _, _ => fun j hj => absurd hj (by simp)
  | pk :: par, i, c, h => by
    have hm' : andB (Nat.ble c pk.1) (andB (Nat.ble pk.1 i) (monoA par (i + 1) pk.1)) = true := by
      rw [← CFSG.KC.LQT.P.letB_eq i (fun i' => andB (Nat.ble c pk.1) (andB (Nat.ble pk.1 i')
        (monoA par (i' + 1) pk.1)))]
      exact h
    rw [CFSG.KC.LQT.P.andB_iff, CFSG.KC.LQT.P.andB_iff, Nat.ble_eq, Nat.ble_eq] at hm'
    obtain ⟨h1, h2, h3⟩ := hm'
    intro j hj
    cases j with
    | zero => simpa using h2
    | succ j =>
      have := monoA_spec par (i + 1) pk.1 h3 j (by simpa using hj)
      simp only [List.getElem_cons_succ]
      omega

private theorem foldl_spec {op : ℕ → ℕ → ℕ} {d : ℕ} {gens : List ℕ} {start : ℕ} :
    ∀ (par : List (ℕ × ℕ)) (acc : List ℕ), (∀ j (hj : j < par.length), (par[j]).1 < acc.length + j) →
    ∀ L, L = par.foldl (fun acc pk => acc ++ [op (acc.getD pk.1 start) (gens.getD pk.2 d)]) acc →
    L.length = acc.length + par.length ∧ (∀ i < acc.length, L.getD i start = acc.getD i start) ∧
    ∀ j (hj : j < par.length),
      L.getD (acc.length + j) start = op (L.getD (par[j]).1 start) (gens.getD (par[j]).2 d)
  | [], acc, _, L, hL => by
    subst hL
    simp
  | pk :: par, acc, hb, L, hL => by
    have hp : pk.1 < acc.length := by
      have := hb 0 (by simp)
      simpa only [List.getElem_cons_zero, Nat.add_zero] using this
    have hL' := hL
    rw [List.foldl_cons] at hL'
    obtain ⟨h1, h2, h3⟩ := foldl_spec (op := op) (d := d) (gens := gens) (start := start) par
      (acc ++ [op (acc.getD pk.1 start) (gens.getD pk.2 d)])
      (fun j hj => by
        have := hb (j + 1) (by simp; omega)
        simp only [List.getElem_cons_succ] at this
        simp only [List.length_append, List.length_singleton]
        omega) L hL'
    simp only [List.length_append, List.length_singleton] at h1 h2 h3
    refine ⟨by simp; omega, fun i hi => ?_, fun j hj => ?_⟩
    · rw [h2 i (by omega), List.getD_append _ _ _ _ hi]
    · cases j with
      | zero =>
        have e1 := h2 acc.length (by omega)
        have e2 := h2 pk.1 (by omega)
        simp only [Nat.add_zero, List.getElem_cons_zero]
        rw [e1, e2, List.getD_append _ _ _ _ hp]
        simp
      | succ j =>
        have := h3 j (by simpa using hj)
        simp only [List.getElem_cons_succ]
        rw [show acc.length + (j + 1) = acc.length + 1 + j by omega]
        exact this

private theorem getD_G (ks : List ↥CFSG.Blueprint.NativeSporadic.M23) (i : ℕ) :
    (ks.map (fun x : ↥CFSG.Blueprint.NativeSporadic.M23 => codeP (x : Equiv.Perm (Fin 23)))).getD i (one 23) =
      codeP ((ks.getD i 1 : ↥CFSG.Blueprint.NativeSporadic.M23) : Equiv.Perm (Fin 23)) := by
  rw [show one 23 = codeP (((1 : ↥CFSG.Blueprint.NativeSporadic.M23)) : Equiv.Perm (Fin 23)) from code_one]
  exact List.getD_map ks 1 (fun x : ↥CFSG.Blueprint.NativeSporadic.M23 => codeP (x : Equiv.Perm (Fin 23)))


end Helpers

theorem reach23_sound (ks : List ↥NativeSporadic.M23) {G : List ℕ}
    (hG : ks.map (fun x => codeP (x : Equiv.Perm (Fin 23))) = G) (codes tp tl : List ℕ) (c₀ : ℕ)
    (h : reachTK 23 5 G codes tp tl c₀ = true) :
    Reach ks (tup c₀) (codes.map tup) tp tl := by
  have hG' : G = ks.map (fun x : ↥NativeSporadic.M23 => codeP (x : Equiv.Perm (Fin 23))) := by
    rw [← hG]
    simp
  subst hG'
  unfold reachTK at h
  simp only [CFSG.KC.LQT.S.allBs_cons, CFSG.KC.LQT.S.allBs_nil, CFSG.KC.LQT.P.andB_iff] at h
  obtain ⟨h1, h2, h3, h4, -⟩ := h
  rw [CFSG.KC.LQT.P.beq_iff, CFSG.KC.LQT.S.lenL_eq, CFSG.KC.LQT.S.lenL_eq] at h1 h2
  have hmono := monoA_spec _ 0 0 h3
  have hc := (CFSG.KC.LQT.Syl.Pf.eqL_iff _ _).1 h4
  rw [CFSG.KC.LQT.T2.bfsQ_eq _ _ _ _ _ h3] at hc
  obtain ⟨l1, l2, l3⟩ := foldl_spec (op := fun x g => actT 23 5 g x) (d := CFSG.KC.LQT.P.one 23) (gens := _)
    (start := c₀) (List.zip tp.tail tl.tail) [c₀]
    (fun j hj => by have := hmono j hj; simp only [List.length_singleton]; omega) codes hc
  have hlen : codes.length = 1 + (List.zip tp.tail tl.tail).length := by simpa using l1
  have hpl : (List.zip tp.tail tl.tail).length = codes.length - 1 := by
    simp only [List.length_zip, List.length_tail]; omega
  refine ⟨by simp; omega, ?_, ?_⟩
  · rw [List.getD_map codes c₀ tup]
    congr 1
    simpa using l2 0 (by simp)
  · intro k hk hk0
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hj : j < (List.zip tp.tail tl.tail).length := by simp at hk; omega
    have hpj1 : (List.zip tp.tail tl.tail)[j].1 = tp.getD (j + 1) 0 := by
      simp only [List.getElem_zip, List.getElem_tail]
      rw [List.getD_eq_getElem]
    have hpj2 : (List.zip tp.tail tl.tail)[j].2 = tl.getD (j + 1) 0 := by
      simp only [List.getElem_zip, List.getElem_tail]
      rw [List.getD_eq_getElem]
    have e3 := l3 j hj
    simp only [List.length_singleton, Nat.add_comm 1 j, hpj1, hpj2] at e3
    have hm := hmono j hj
    rw [hpj1] at hm
    refine ⟨by omega, ?_⟩
    rw [List.getD_map codes c₀ tup, List.getD_map codes c₀ tup, e3, getD_G, tup_actT]
    rfl

theorem codes23_sound (codes : List ℕ) (h : codesTK 23 5 codes = true) :
    ((codes.map tup).map enc).Nodup := by
  unfold codesTK at h
  rw [CFSG.KC.LQT.P.andB_iff] at h
  obtain ⟨h1, h2⟩ := h
  have hlt : ∀ c ∈ codes, c < 6436343 := fun c hc =>
    CFSG.KC.LQT.P.blt_iff.1 ((CFSG.KC.LQT.P.allL_iff _ _).1 h1 c hc)
  have e : codes.map (enc ∘ tup) = codes := by
    conv_rhs => rw [← List.map_id codes]
    exact List.map_congr_left fun c hc => enc_tup (hlt c hc)
  rw [List.map_map, e]
  exact CFSG.KC.LQT.T2.nodup_of_distinctS h2

end CFSG.KC.LQT.Insp

end
