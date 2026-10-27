module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf5TtRes
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf5Count
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf5TtRowsAll

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.TtK

open CFSG.Monster.B.Co2 PkG CovK CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Sp6Cover
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Sp6CoverData Chain

set_option linter.unusedSectionVars false

@[expose] noncomputable def xw (w : List ℕ) : ↥ySub := ⟨permW CG w, permW_mem CG CG_mem w⟩

theorem xw_val (w : List ℕ) : (xw w : Equiv.Perm (Fin 240)) = permW CG w := rfl

@[expose] noncomputable def tT : Subgroup ↥ySub := Subgroup.centralizer ({Sp6Cover.tY} : Set ↥ySub)

theorem permW_comm_t : ∀ w : List ℕ, permW CG w * Sp6Cover.tP = Sp6Cover.tP * permW CG w
  | [] => by simp [permW_nil]
  | l :: w => by
    rw [permW_cons]
    have h1 := CG_comm_t l
    have h2 := permW_comm_t w
    calc CG l * permW CG w * Sp6Cover.tP = CG l * (permW CG w * Sp6Cover.tP) := by group
      _ = CG l * (Sp6Cover.tP * permW CG w) := by rw [h2]
      _ = (CG l * Sp6Cover.tP) * permW CG w := by group
      _ = Sp6Cover.tP * CG l * permW CG w := by rw [h1]
      _ = Sp6Cover.tP * (CG l * permW CG w) := by group

theorem xw_mem (w : List ℕ) : xw w ∈ tT := by
  rw [tT, Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  exact (permW_comm_t w).symm.symm

@[expose] noncomputable def elt (r : List ℕ) : ↥ySub := xw (rowW r)

theorem res_elt (r : List ℕ) : ResRep (rowVal r) (elt r : Equiv.Perm (Fin 240)) := resW (rowW r)

theorem rows_sound : (∀ r ∈ rowsT, rowOk r = true) ∧ (rowsT.map rowVal).Pairwise (· < ·) :=
  let h := chainChk_sound rowVal rowOk rowsT 0 rowsT_chk
  ⟨h.1, h.2.1⟩

theorem rowVal_nodup : (rowsT.map rowVal).Nodup := rows_sound.2.imp fun h => ne_of_lt h

theorem rowVal_inj {r r' : List ℕ} (hr : r ∈ rowsT) (hr' : r' ∈ rowsT) (h : rowVal r = rowVal r') :
    r = r' :=
  List.inj_on_of_nodup_map rowVal_nodup hr hr' h

theorem elt_inj {r r' : List ℕ} (hr : r ∈ rowsT) (hr' : r' ∈ rowsT) (h : elt r = elt r') : r = r' := by
  apply rowVal_inj hr hr'
  have h1 := res_elt r
  have h2 := res_elt r'
  rw [← h] at h2
  exact h1.digits_unique h2

theorem nodup_elts : (rowsT.map elt).Nodup := by
  rw [List.Nodup, List.pairwise_map]
  have h := rows_sound.2
  rw [List.pairwise_map] at h
  refine h.imp ?_
  intro a b hab heq
  have h1 := res_elt a
  have h2 := res_elt b
  have h3 : (elt a : Equiv.Perm (Fin 240)) = elt b := congrArg Subtype.val heq
  rw [h3] at h1
  exact absurd (h1.digits_unique h2) (ne_of_lt hab)

theorem exists_row {x : ↥ySub} (hx : x ∈ tT) : ∃ r ∈ rowsT, elt r = x := by
  have hm := mem_of_nodup_card tT (rowsT.map elt) nodup_elts
    (fun y hy => by
      obtain ⟨r, -, rfl⟩ := List.mem_map.1 hy
      exact xw_mem _)
    (by rw [List.length_map, rowsT_length]; exact card_centralizer_tY.symm) hx
  obtain ⟨r, hr, hrx⟩ := List.mem_map.1 hm
  exact ⟨r, hr, hrx⟩

theorem res_inj {x y : ↥ySub} (hx : x ∈ tT) (hy : y ∈ tT) {p : ℕ}
    (hpx : ResRep p (x : Equiv.Perm (Fin 240))) (hpy : ResRep p (y : Equiv.Perm (Fin 240))) :
    x = y := by
  obtain ⟨r, hr, rfl⟩ := exists_row hx
  obtain ⟨r', hr', rfl⟩ := exists_row hy
  have h1 := (res_elt r).digits_unique hpx
  have h2 := (res_elt r').digits_unique hpy
  rw [elt_inj hr hr' (by rw [rowVal_inj hr hr' (h1.trans h2.symm)])]

theorem spW_len : spW.length = 11 := by decide +kernel

theorem lwO_sp_parts :
    lwO.getD 12 [] = (spW.getD 0 []).map (· + 6) ∧ lwO.getD 13 [] = (spW.getD 1 []).map (· + 6) ∧
    lwO.getD 14 [] = (spW.getD 2 []).map (· + 6) ∧ lwO.getD 15 [] = (spW.getD 3 []).map (· + 6) ∧
    lwO.getD 16 [] = (spW.getD 4 []).map (· + 6) ∧ lwO.getD 17 [] = (spW.getD 5 []).map (· + 6) ∧
    lwO.getD 18 [] = (spW.getD 6 []).map (· + 6) ∧ lwO.getD 19 [] = (spW.getD 7 []).map (· + 6) ∧
    lwO.getD 20 [] = (spW.getD 8 []).map (· + 6) ∧ lwO.getD 22 [] = (spW.getD 10 []).map (· + 6) := by
  have h := lwO_sp
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
  exact h

theorem sp_lt (k : ℕ) (hk : k < 11) : ∀ l ∈ spW.getD k [], l < 6 :=
  spW_lt' (spW_get_mem (by rw [spW_len]; exact hk))

theorem permW_sp0 : permW CG (spW.getD 0 []) = Sp6Cover.tP := by
  rw [← LGO_cw (sp_lt 0 (by norm_num)) lwO_sp_parts.1, LGO_12]

theorem permW_sp1 : permW CG (spW.getD 1 []) = Sp6Cover.iP := by
  rw [← LGO_cw (sp_lt 1 (by norm_num)) lwO_sp_parts.2.1, LGO_13]

theorem permW_sp3 : permW CG (spW.getD 3 []) = Sp6Cover.jP := by
  rw [← LGO_cw (sp_lt 3 (by norm_num)) lwO_sp_parts.2.2.2.1, LGO_15]

theorem permW_sp5 : permW CG (spW.getD 5 []) = eP * Sp6Cover.iP * eP⁻¹ := by
  rw [← LGO_cw (sp_lt 5 (by norm_num)) lwO_sp_parts.2.2.2.2.2.1, LGO_17, LGO_13]

theorem permW_sp7 : permW CG (spW.getD 7 []) = eP * Sp6Cover.jP * eP⁻¹ := by
  rw [← LGO_cw (sp_lt 7 (by norm_num)) lwO_sp_parts.2.2.2.2.2.2.2.1, LGO_19, LGO_15]

theorem permW_sp10 : permW CG (spW.getD 10 []) = Sp6Cover.tP * LGl 12 := by
  rw [← LGO_cw (sp_lt 10 (by norm_num)) lwO_sp_parts.2.2.2.2.2.2.2.2.2, LGO_22, LGO_12, LGO_21]

theorem res_sp (k : ℕ) : ResRep (SP48.getD k (one 64 48)) (permW CG (spW.getD k [])) := by
  have h := resW (spW.getD k [])
  have e : SP48.getD k (one 64 48) = evalW 64 48 base48 (spW.getD k []) := by
    rw [← SP48_eq]
    exact getD_map' (evalW 64 48 base48) spW k []
  rw [e]
  exact h

theorem res_t : ResRep tP (Sp6Cover.tP : Equiv.Perm (Fin 240)) := by
  have := res_sp 0
  rwa [permW_sp0] at this

theorem res_i : ResRep (SP48.getD 1 (one 64 48)) (Sp6Cover.iP : Equiv.Perm (Fin 240)) := by
  have := res_sp 1
  rwa [permW_sp1] at this

theorem res_j : ResRep (SP48.getD 3 (one 64 48)) (Sp6Cover.jP : Equiv.Perm (Fin 240)) := by
  have := res_sp 3
  rwa [permW_sp3] at this

theorem res_i' : ResRep (SP48.getD 5 (one 64 48)) (eP * Sp6Cover.iP * eP⁻¹) := by
  have := res_sp 5
  rwa [permW_sp5] at this

theorem res_j' : ResRep (SP48.getD 7 (one 64 48)) (eP * Sp6Cover.jP * eP⁻¹) := by
  have := res_sp 7
  rwa [permW_sp7] at this

theorem res_comm {a b : ℕ} {x y : Equiv.Perm (Fin 240)} (ha : ResRep a x) (hb : ResRep b y)
    (h : x * y = y * x) : commP a b = true := by
  unfold commP
  rw [beq_iff_eq]
  have h1 := ha.comp hb
  have h2 := hb.comp ha
  rw [h] at h1
  exact h1.digits_unique h2

theorem res_sq_t {x : Equiv.Perm (Fin 240)} {a : ℕ} (hx : ResRep a x) (h : x * x = Sp6Cover.tP) :
    comp 64 48 a a = tP := by
  have h1 := hx.comp hx
  rw [h] at h1
  exact h1.digits_unique res_t

theorem row_unpack {r : List ℕ} (hr : r ∈ rowsT) :
    ((comp 64 48 (rowVal r) (rowVal r) == tP) == (r.getD 0 0 == 1)) = true ∧
      ccOk (r.getD 1 0) (rowVal r) = true := by
  have h := rows_sound.1 r hr
  simp only [rowOk, Bool.and_eq_true] at h
  exact ⟨h.1.1.2, h.1.2⟩

theorem sq_flag {r : List ℕ} (hr : r ∈ rowsT) (h : elt r * elt r = Sp6Cover.tY) : r.getD 0 0 = 1 := by
  have hs : comp 64 48 (rowVal r) (rowVal r) = tP := by
    apply res_sq_t (res_elt r)
    exact congrArg Subtype.val h
  have := (row_unpack hr).1
  rw [hs] at this
  simpa using this

@[expose] def ccOk' (cc x i j i' j' : ℕ) : Bool :=
  (cc == 0 && !commP x i) || (cc == 1 && commP x i && !commP x j) ||
    (cc == 2 && commP x i && commP x j && !commP x i') ||
    (cc == 3 && commP x i && commP x j && commP x i' && !commP x j') ||
    (cc == 4 && commP x i && commP x j && commP x i' && commP x j')

theorem ccOk_eq (cc x : ℕ) : ccOk cc x = ccOk' cc x (SP48.getD 1 (one 64 48))
    (SP48.getD 3 (one 64 48)) (SP48.getD 5 (one 64 48)) (SP48.getD 7 (one 64 48)) := rfl

theorem ccOk'_ge2 {cc x i j i' j' : ℕ} (h : ccOk' cc x i j i' j' = true) (hi : commP x i = true)
    (hj : commP x j = true) : 2 ≤ cc := by
  unfold ccOk' at h
  by_contra hlt
  have : cc = 0 ∨ cc = 1 := by omega
  rcases this with rfl | rfl <;> simp [hi, hj] at h

theorem ccOk'_eq4 {cc x i j i' j' : ℕ} (h : ccOk' cc x i j i' j' = true) (hi : commP x i = true)
    (hj : commP x j = true) (hi' : commP x i' = true) (hj' : commP x j' = true) : cc = 4 := by
  unfold ccOk' at h
  by_contra hne
  have : cc = 0 ∨ cc = 1 ∨ cc = 2 ∨ cc = 3 ∨ 5 ≤ cc := by omega
  rcases this with rfl | rfl | rfl | rfl | h5
  · simp [hi] at h
  · simp [hi, hj] at h
  · simp [hi, hj, hi'] at h
  · simp [hi, hj, hi', hj'] at h
  · have h0 : (cc == 0) = false := by simp; omega
    have h1 : (cc == 1) = false := by simp; omega
    have h2 : (cc == 2) = false := by simp; omega
    have h3 : (cc == 3) = false := by simp; omega
    have h4 : (cc == 4) = false := by simp; omega
    simp [h0, h1, h2, h3, h4] at h

theorem cc_flag {r : List ℕ} (hr : r ∈ rowsT)
    (hi : (elt r : Equiv.Perm (Fin 240)) * Sp6Cover.iP = Sp6Cover.iP * elt r)
    (hj : (elt r : Equiv.Perm (Fin 240)) * Sp6Cover.jP = Sp6Cover.jP * elt r) :
    2 ≤ r.getD 1 0 := by
  have h := (row_unpack hr).2
  rw [ccOk_eq] at h
  exact ccOk'_ge2 h (res_comm (res_elt r) res_i hi) (res_comm (res_elt r) res_j hj)

theorem cc_flag4 {r : List ℕ} (hr : r ∈ rowsT)
    (hi : (elt r : Equiv.Perm (Fin 240)) * Sp6Cover.iP = Sp6Cover.iP * elt r)
    (hj : (elt r : Equiv.Perm (Fin 240)) * Sp6Cover.jP = Sp6Cover.jP * elt r)
    (hi' : (elt r : Equiv.Perm (Fin 240)) * (eP * Sp6Cover.iP * eP⁻¹) =
      (eP * Sp6Cover.iP * eP⁻¹) * elt r)
    (hj' : (elt r : Equiv.Perm (Fin 240)) * (eP * Sp6Cover.jP * eP⁻¹) =
      (eP * Sp6Cover.jP * eP⁻¹) * elt r) : r.getD 1 0 = 4 := by
  have h := (row_unpack hr).2
  rw [ccOk_eq] at h
  exact ccOk'_eq4 h (res_comm (res_elt r) res_i hi) (res_comm (res_elt r) res_j hj)
    (res_comm (res_elt r) res_i' hi') (res_comm (res_elt r) res_j' hj')

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.TtK
