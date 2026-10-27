module

public import CFSG.LocalAnalysis.AGL81I.Section3.Sp43.CodeSound
public import Certificates.Data.Sp43.Check

public section

namespace CFSG.Sp43

open CFSG.Sp43.Native

abbrev G := Matrix.symplecticGroup (Fin 2) (ZMod 3)

@[expose] def Symp (c : ℕ) : Prop := toM c ∈ Matrix.symplecticGroup (Fin 2) (ZMod 3)

noncomputable def ofCode (c : ℕ) : G := by
  classical exact if h : Symp c then ⟨toM c, h⟩ else 1

private theorem digs_getElem (a : ℕ) {n : ℕ} (hn : n < 16) : (digs a)[n]! = dig a n := by
  simp [digs, dig, hn]

private theorem digs_ent (a : ℕ) {i j : ℕ} (hi : i < 4) (hj : j < 4) :
    (digs a)[4 * i + j]! = ent a i j := digs_getElem a (by omega)

theorem mulF_eq_mulC (a b : ℕ) : mulF a b = mulC a b := by
  dsimp only [mulF, mulC]
  congr 1
  refine List.map_congr_left fun k hk => ?_
  have hk16 : k < 16 := List.mem_range.1 hk
  have hi : k / 4 < 4 := by omega
  have hj : k % 4 < 4 := by omega
  have x0 : (digs a)[4 * (k / 4)]! = ent a (k / 4) 0 :=
    digs_ent a (i := k / 4) (j := 0) hi (by omega)
  have x1 : (digs a)[4 * (k / 4) + 1]! = ent a (k / 4) 1 :=
    digs_ent a (i := k / 4) (j := 1) hi (by omega)
  have x2 : (digs a)[4 * (k / 4) + 2]! = ent a (k / 4) 2 :=
    digs_ent a (i := k / 4) (j := 2) hi (by omega)
  have x3 : (digs a)[4 * (k / 4) + 3]! = ent a (k / 4) 3 :=
    digs_ent a (i := k / 4) (j := 3) hi (by omega)
  have y0 : (digs b)[k % 4]! = ent b 0 (k % 4) := by
    simpa using digs_ent b (i := 0) (j := k % 4) (by omega) hj
  have y1 : (digs b)[4 + k % 4]! = ent b 1 (k % 4) := by
    simpa using digs_ent b (i := 1) (j := k % 4) (by omega) hj
  have y2 : (digs b)[8 + k % 4]! = ent b 2 (k % 4) := by
    simpa using digs_ent b (i := 2) (j := k % 4) (by omega) hj
  have y3 : (digs b)[12 + k % 4]! = ent b 3 (k % 4) := by
    simpa using digs_ent b (i := 3) (j := k % 4) (by omega) hj
  rw [x0, x1, x2, x3, y0, y1, y2, y3]

theorem symp_oneC : Symp oneC := by
  unfold Symp
  rw [toM_oneC]
  exact Submonoid.one_mem _

theorem symp_mulF {a b : ℕ} (ha : Symp a) (hb : Symp b) : Symp (mulF a b) := by
  unfold Symp at *
  rw [mulF_eq_mulC, toM_mulC]
  exact Submonoid.mul_mem _ ha hb

theorem coe_ofCode {c : ℕ} (hc : Symp c) :
    ((ofCode c : G) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3)) = toM c := by
  unfold ofCode
  rw [dif_pos hc]

theorem ofCode_oneC : ofCode oneC = 1 := by
  apply Subtype.ext
  rw [coe_ofCode symp_oneC, toM_oneC]
  rfl

theorem ofCode_mulF {a b : ℕ} (ha : Symp a) (hb : Symp b) :
    ofCode (mulF a b) = ofCode a * ofCode b := by
  apply Subtype.ext
  rw [coe_ofCode (symp_mulF ha hb), mulF_eq_mulC, toM_mulC]
  rw [Submonoid.coe_mul, coe_ofCode ha, coe_ofCode hb]

theorem symp_powC {a : ℕ} (ha : Symp a) (e : ℕ) : Symp (powC a e) := by
  induction e with
  | zero => exact symp_oneC
  | succ e ih =>
    rw [powC, ← mulF_eq_mulC]
    exact symp_mulF ih ha

theorem ofCode_powC {a : ℕ} (ha : Symp a) (e : ℕ) : ofCode (powC a e) = ofCode a ^ e := by
  induction e with
  | zero => rw [powC, ofCode_oneC, pow_zero]
  | succ e ih => rw [powC, ← mulF_eq_mulC, ofCode_mulF (symp_powC ha e) ha, ih, pow_succ]

theorem symp_of_mem_spCodes {c : ℕ} (h : c ∈ spCodes ()) : Symp c :=
  ((mem_spCodes_iff c).1 h).2

theorem encode_mem_spCodes (g : G) :
    encode (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3)) ∈ spCodes () :=
  (mem_spCodes_iff _).2 ⟨encode_lt _, by rw [toM_encode]; exact g.2⟩

theorem ofCode_encode (g : G) :
    ofCode (encode (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3))) = g := by
  apply Subtype.ext
  rw [coe_ofCode (symp_of_mem_spCodes (encode_mem_spCodes g)), toM_encode]

theorem ofCode_injOn {a b : ℕ} (ha : a ∈ spCodes ()) (hb : b ∈ spCodes ())
    (h : ofCode a = ofCode b) : a = b := by
  have ha' := (mem_spCodes_iff a).1 ha
  have hb' := (mem_spCodes_iff b).1 hb
  refine eq_of_toM_eq ha'.1 hb'.1 ?_
  rw [← coe_ofCode ha'.2, ← coe_ofCode hb'.2, h]

private theorem memS_go_spec (L : Array ℕ) (c : ℕ) :
    ∀ f lo hi : ℕ, hi ≤ L.size → memS.go L c lo hi f = true → ∃ i < L.size, L[i]! = c := by
  intro f
  induction f with
  | zero => intro lo hi _ h; simp [memS.go] at h
  | succ f ih =>
    intro lo hi hhi h
    simp only [memS.go] at h
    split_ifs at h with h1 h2 h3
    · exact ⟨(lo + hi) / 2, by omega, by simpa using h2⟩
    · exact ih _ _ hhi h
    · exact ih _ _ (by omega) h

theorem memS_spec {L : Array ℕ} {c : ℕ} (h : memS L c = true) : ∃ i < L.size, L[i]! = c :=
  memS_go_spec L c _ 0 L.size le_rfl h

theorem incOK_inj {L : Array ℕ} (h : incOK L = true) {i j : ℕ} (hi : i < L.size)
    (hj : j < L.size) (hij : L[i]! = L[j]!) : i = j := by
  have hstep : ∀ k, k + 1 < L.size → L[k]! < L[k + 1]! := by
    intro k hk
    simp only [incOK, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
    exact h k (by omega)
  have hlt : ∀ j, ∀ i, i < j → j < L.size → L[i]! < L[j]! := by
    intro j
    induction j with
    | zero => intro i hij; omega
    | succ j ih =>
      intro i hij hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with hlt | rfl
      · exact (ih i hlt (by omega)).trans (hstep j hj)
      · exact hstep i hj
  rcases lt_trichotomy i j with h1 | h1 | h1
  · exact absurd hij (hlt j i h1 hj).ne
  · exact h1
  · exact absurd hij.symm (hlt i j h1 hi).ne

private theorem size_spArr : (spArr ()).size = (spCodes ()).length := by
  simp [spArr]

private theorem spArr_getElem {i : ℕ} (hi : i < (spCodes ()).length) :
    (spArr ())[i]! = (spCodes ())[i] := by
  have h : i < (spArr ()).size := by rw [size_spArr]; exact hi
  rw [getElem!_pos (spArr ()) i h]
  simp [spArr]

private theorem spArr_getElem_mem {i : ℕ} (hi : i < (spArr ()).size) :
    (spArr ())[i]! ∈ spCodes () := by
  rw [size_spArr] at hi
  rw [spArr_getElem hi]
  exact List.getElem_mem hi

theorem exists_spArr (g : G) : ∃ i < (spArr ()).size, ofCode (spArr ())[i]! = g := by
  obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.1 (encode_mem_spCodes g)
  refine ⟨i, by rw [size_spArr]; exact hi, ?_⟩
  rw [spArr_getElem hi, hix, ofCode_encode]

theorem symp_spArr {i : ℕ} (hi : i < (spArr ()).size) : Symp (spArr ())[i]! :=
  symp_of_mem_spCodes (spArr_getElem_mem hi)

theorem card_G (h1 : (spArr ()).size = 51840) (h2 : incOK (spArr ()) = true) :
    Nat.card G = 51840 := by
  have hbij : Function.Bijective (fun i : Fin 51840 => ofCode (spArr ())[(i : ℕ)]!) := by
    constructor
    · intro i j hij
      exact Fin.ext (incOK_inj h2 (by omega) (by omega)
        (ofCode_injOn (spArr_getElem_mem (by omega)) (spArr_getElem_mem (by omega)) hij))
    · intro g
      obtain ⟨i, hi, hg⟩ := exists_spArr g
      exact ⟨⟨i, by omega⟩, hg⟩
  exact (Nat.card_eq_of_bijective _ hbij).symm.trans (Nat.card_fin 51840)

@[expose] noncomputable def sub2 (a b : ℕ) : Subgroup G := Subgroup.closure {ofCode a, ofCode b}

private theorem gen_spec {a b : ℕ} (ha : Symp a) (hb : Symp b) {k : ℕ} (hk : k < 2) :
    Symp #[a, b][k]! ∧ ofCode #[a, b][k]! ∈ sub2 a b := by
  interval_cases k
  · exact ⟨ha, Subgroup.subset_closure (by simp)⟩
  · exact ⟨hb, Subgroup.subset_closure (by simp)⟩

theorem treeOK_spec {L par lab dep : Array ℕ} {a b : ℕ} (ha : Symp a) (hb : Symp b)
    (h : treeOK L #[a, b] par lab dep = true) :
    ∀ i < L.size, Symp L[i]! ∧ ofCode L[i]! ∈ sub2 a b := by
  simp only [treeOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨-, hall⟩ := h
  suffices H : ∀ n i, i < L.size → dep[i]! = n → Symp L[i]! ∧ ofCode L[i]! ∈ sub2 a b from
    fun i hi => H _ i hi rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i hi hdep
    rcases hall i hi with ⟨_, h1⟩ | ⟨⟨⟨hpar, hlab⟩, hlt⟩, heq⟩
    · rw [h1]
      exact ⟨symp_oneC, by rw [ofCode_oneC]; exact Subgroup.one_mem _⟩
    · obtain ⟨hs, hm⟩ := ih _ (by omega) par[i]! hpar rfl
      obtain ⟨hgs, hgm⟩ := gen_spec ha hb (by simpa using hlab)
      rw [heq]
      exact ⟨symp_mulF hs hgs, by rw [ofCode_mulF hs hgs]; exact Subgroup.mul_mem _ hm hgm⟩

private theorem pow_mem_of_mul_mem (S : Set G) (x : G) (hx : ∀ y ∈ S, y * x ∈ S) (k : ℕ) :
    ∀ y ∈ S, y * x ^ k ∈ S := by
  induction k with
  | zero => intro y hy; simpa using hy
  | succ k ih => intro y hy; rw [pow_succ, ← mul_assoc]; exact hx _ (ih y hy)

private theorem inv_mem_of_mul_mem (S : Set G) (x : G) (hx : ∀ y ∈ S, y * x ∈ S) :
    ∀ y ∈ S, y * x⁻¹ ∈ S := by
  have hpos : 0 < Nat.card G := Nat.card_pos
  have h1 : x * x ^ (Nat.card G - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel hpos, pow_card_eq_one']
  rw [inv_eq_of_mul_eq_one_right h1]
  exact pow_mem_of_mul_mem S x hx _

theorem closedOK_spec {L : Array ℕ} {a b : ℕ} (ha : Symp a) (hb : Symp b)
    (hL : ∀ i < L.size, Symp L[i]!) (h : closedOK L #[a, b] = true) :
    ∀ x ∈ sub2 a b, ∃ i < L.size, ofCode L[i]! = x := by
  simp only [closedOK, Bool.and_eq_true, Array.all_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  set S : Set G := {x | ∃ i < L.size, ofCode L[i]! = x}
  have hone : (1 : G) ∈ S := by
    obtain ⟨i, hi, hic⟩ := memS_spec h1
    exact ⟨i, hi, by rw [hic, ofCode_oneC]⟩
  have hgen : ∀ k < 2, ∀ y ∈ S, y * ofCode #[a, b][k]! ∈ S := by
    rintro k hk _ ⟨i, hi, rfl⟩
    have hk' : k < #[a, b].size := by simpa using hk
    have h3 := h2 i hi k hk'
    rw [← getElem!_pos L i hi, ← getElem!_pos #[a, b] k hk'] at h3
    obtain ⟨j, hj, hjc⟩ := memS_spec h3
    exact ⟨j, hj, by rw [hjc, ofCode_mulF (hL i hi) (gen_spec ha hb hk).1]⟩
  have key : ∀ x ∈ sub2 a b, ∀ y ∈ S, y * x ∈ S := by
    intro x hx
    have hx' : x ∈ Subgroup.closure {ofCode a, ofCode b} := hx
    clear hx
    induction hx' using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact hgen 0 (by norm_num)
      · exact hgen 1 (by norm_num)
    | one => intro y hy; simpa using hy
    | mul x y _ _ hx hy => intro z hz; rw [← mul_assoc]; exact hy _ (hx z hz)
    | inv x _ hx => exact inv_mem_of_mul_mem S x hx
  intro x hx
  obtain ⟨i, hi, hix⟩ := key x hx 1 hone
  exact ⟨i, hi, by rw [hix, one_mul]⟩

private theorem treeOK_lt {L gens par lab dep : Array ℕ}
    (h : treeOK L gens par lab dep = true) : ∀ i < L.size, L[i]! < 3 ^ 16 := by
  simp only [treeOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, decide_eq_true_eq] at h
  intro i hi
  rcases h.2 i hi with ⟨_, h1⟩ | ⟨_, heq⟩
  · rw [h1]
    decide
  · rw [heq, mulF_eq_mulC]
    exact mulC_lt _ _

theorem subOK_spec {a b n : ℕ} {r : Array ℕ × Array ℕ × Array ℕ × Array ℕ} (ha : Symp a)
    (hb : Symp b) (h : subOK #[a, b] n r = true) :
    r.1.size = n ∧ (∀ i < n, Symp r.1[i]!) ∧ (∀ x, x ∈ sub2 a b ↔ ∃ i < n, ofCode r.1[i]! = x) ∧
      Nat.card (sub2 a b) = n := by
  simp only [subOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hsize, hinc⟩, htree⟩, hclosed⟩ := h
  have hsym := treeOK_spec ha hb htree
  have hlt := treeOK_lt htree
  have hmem := closedOK_spec ha hb (fun i hi => (hsym i hi).1) hclosed
  have hiff : ∀ x, x ∈ sub2 a b ↔ ∃ i < n, ofCode r.1[i]! = x := by
    intro x
    constructor
    · intro hx
      obtain ⟨i, hi, hix⟩ := hmem x hx
      exact ⟨i, by omega, hix⟩
    · rintro ⟨i, hi, rfl⟩
      exact (hsym i (by omega)).2
  have hspc : ∀ i < n, r.1[i]! ∈ spCodes () := fun i hi =>
    (mem_spCodes_iff _).2 ⟨hlt i (by omega), (hsym i (by omega)).1⟩
  refine ⟨hsize, fun i hi => (hsym i (by omega)).1, hiff, ?_⟩
  have hbij : Function.Bijective (fun i : Fin n =>
      (⟨ofCode r.1[(i : ℕ)]!, (hsym i (by omega)).2⟩ : sub2 a b)) := by
    constructor
    · intro i j hij
      exact Fin.ext (incOK_inj hinc (by omega) (by omega)
        (ofCode_injOn (hspc i i.2) (hspc j j.2) (congrArg Subtype.val hij)))
    · rintro ⟨x, hx⟩
      obtain ⟨i, hi, hix⟩ := (hiff x).1 hx
      exact ⟨⟨i, hi⟩, Subtype.ext hix⟩
  exact (Nat.card_eq_of_bijective _ hbij).symm.trans (Nat.card_fin n)

theorem mem_sub2_of_memS {a b n : ℕ} {r : Array ℕ × Array ℕ × Array ℕ × Array ℕ} (ha : Symp a)
    (hb : Symp b) (hr : subOK #[a, b] n r = true) {c : ℕ} (h : memS r.1 c = true) :
    Symp c ∧ ofCode c ∈ sub2 a b := by
  obtain ⟨i, hi, hic⟩ := memS_spec h
  obtain ⟨hsize, hsym, hiff, -⟩ := subOK_spec ha hb hr
  subst hic
  exact ⟨hsym i (by omega), (hiff _).2 ⟨i, by omega, rfl⟩⟩

end CFSG.Sp43

end
