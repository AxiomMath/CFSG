module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28OmAlg
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28LocalLower
public import Certificates.Certificate9558

set_option linter.unusedSectionVars false

public section

namespace CFSG.AGLEmbedding.KFactProofs.G28

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.RankThree.PartTwo.Sec4.Item434G28 CFSG.PreuniquenessRankFour.Helpers

attribute [local irreducible] txL tU tZ tO tzc gW

theorem quadOK_tzc_of (h : ∀ t < 36, (mulCode tzc tzc)[t]! ^^^ tzc[t]! ^^^ idCode[t]! = 0) :
    quadOK tzc = true := by
  simp only [quadOK, List.all_eq_true, List.mem_range, beq_iff_eq]
  exact h

theorem epsOK_gW_of (h : ∀ j < 4, mulCode (mulCode (wordCode gW[j]!) tzc)
    (wordCode (gW[j]!).reverse) = if j % 2 = 1 then mulCode tzc tzc else tzc) :
    epsOK tzc gW = true := by
  simp only [epsOK, List.all_eq_true, List.mem_range, beq_iff_eq]
  exact h

@[expose] def omIdx (n : ℕ) : ℕ :=
  if n < 1 then 0 else if n < 32320 then 1 else if n < 65152 then 2 else if n < 97984 then 3 else 4

theorem omIdx_spec {n : ℕ} (hn : n < 130816) :
    omIdx n < 5 ∧ omLo (omIdx n) ≤ n ∧ n < omLo (omIdx n + 1) := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := omLo_vals
  unfold omIdx
  split_ifs <;> simp only [h0, h1, h2, h3, h4, h5, Nat.reduceAdd] <;> omega

theorem omIdx_eq {k n : ℕ} (hk : k < 5) (h1 : omLo k ≤ n) (h2 : n < omLo (k + 1)) :
    omIdx n = k := by
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := omLo_vals
  unfold omIdx
  interval_cases k <;> simp only [e0, e1, e2, e3, e4, e5, Nat.reduceAdd] at h1 h2 <;>
    split_ifs <;> omega

theorem omLo_le {k : ℕ} (hk : k < 5) : omLo (k + 1) ≤ 130816 := by
  interval_cases k <;> decide

section Omega


variable {K : Type} [Field K] [Finite K] [CharP K 2] (M : G28Model K)

theorem wordElt_reverse_eq_inv {w : List ℕ}
    (h : mulCode (wordCode w) (wordCode w.reverse) = idCode) :
    M.wordElt w.reverse = (M.wordElt w)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  show M.wordElt w * M.wordElt w.reverse = 1
  exact (M.eq_one_iff_code (valid_mulCode (valid_wordCode _) (valid_wordCode _))
    (M.rho_mul_code (valid_wordCode _) (valid_wordCode _) (M.rho_wordElt w)
      (M.rho_wordElt w.reverse))).2 h

theorem wordElt_append (u v : List ℕ) : M.wordElt (u ++ v) = M.wordElt u * M.wordElt v := by
  simp [G28Model.wordElt, List.map_append, List.prod_append]

@[expose] noncomputable def Bsub (x : adjointGroup .G2 K) : Subgroup (adjointGroup .G2 K) :=
  conjSub x (Subgroup.zpowers (zE M))

theorem Bsub_mul (x y : adjointGroup .G2 K) : Bsub M (x * y) = conjSub x (Bsub M y) :=
  conjSub_mul x y _

theorem Bsub_eq (x : adjointGroup .G2 K) : Bsub M x = Subgroup.zpowers (x * zE M * x⁻¹) := by
  unfold Bsub conjSub
  rw [MonoidHom.map_zpowers]
  simp [MulAut.conj_apply]

theorem conj_zinv (x : adjointGroup .G2 K) : x * (zE M)⁻¹ * x⁻¹ = (x * zE M * x⁻¹)⁻¹ := by
  group

theorem mem_zpowers_cases {G : Type*} [Group G] {w a : G} (h : w ^ 3 = 1)
    (ha : a ∈ Subgroup.zpowers w) : a = 1 ∨ a = w ∨ a = w⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  have e : w ^ k = w ^ (k % 3) := by
    conv_lhs => rw [← Int.mul_ediv_add_emod k 3, zpow_add, zpow_mul]
    have : w ^ (3 : ℤ) = 1 := by exact_mod_cast h
    rw [this, one_zpow, one_mul]
  have hk : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rw [e]
  rcases hk with hk | hk | hk <;> rw [hk]
  · exact Or.inl (zpow_zero w)
  · exact Or.inr (Or.inl (zpow_one w))
  · refine Or.inr (Or.inr ?_)
    rw [zpow_two]
    exact eq_inv_of_mul_eq_one_left ((pow_three' w).symm.trans h)

theorem zpowers_eq_of_inv {G : Type*} [Group G] {a b : G} (h : a = b ∨ a⁻¹ = b) :
    Subgroup.zpowers a = Subgroup.zpowers b := by
  rcases h with rfl | rfl
  · rfl
  · exact (Subgroup.zpowers_inv).symm

theorem isCC_Bsub_eq {u : Array ℕ} {x y : adjointGroup .G2 K} (hx : IsCC M u x)
    (hy : IsCC M u y) : Bsub M x = Bsub M y := by
  rw [Bsub_eq, Bsub_eq]
  unfold IsCC at hx hy
  rw [conj_zinv] at hx hy
  apply zpowers_eq_of_inv
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact Or.inl (M.rho_injective (hx.trans hy.symm))
  · right
    rw [M.rho_injective (hx.trans hy.symm), inv_inv]
  · exact Or.inr (M.rho_injective (hx.trans hy.symm))
  · left
    exact inv_injective (M.rho_injective (hx.trans hy.symm))

theorem isCC_code_eq (hq : quadOK tzc = true) {u u' : Array ℕ} {x y : adjointGroup .G2 K}
    (hu : Valid u) (hu' : Valid u') (he : u[0]! % 2 = 0) (he' : u'[0]! % 2 = 0)
    (hx : IsCC M u x) (hy : IsCC M u' y) (hB : Bsub M x = Bsub M y) : u = u' := by
  have hwx3 : (x * zE M * x⁻¹) ^ 3 = 1 := by
    rw [conj_pow, zE_pow_three]
    group
  have hwy : y * zE M * y⁻¹ ∈ Subgroup.zpowers (x * zE M * x⁻¹) := by
    rw [← Bsub_eq, hB, Bsub_eq]
    exact Subgroup.mem_zpowers _
  have hwy1 : y * zE M * y⁻¹ ≠ 1 := by
    intro h
    apply zE_ne_one M
    have e : zE M = y⁻¹ * (y * zE M * y⁻¹) * y := by group
    rw [e, h]
    simp
  have hAA : ∀ {u₀ : Array ℕ}, IsCC M u₀ y →
      M.rho (x * zE M * x⁻¹) = decode u₀ ∨ M.rho (x * zE M * x⁻¹) + 1 = decode u₀ := by
    intro u₀ hy₀
    have hrx := rho_conj_zinv M hq x
    have hry := rho_conj_zinv M hq y
    rcases mem_zpowers_cases hwx3 hwy with h | h | h
    · exact absurd h hwy1
    · rw [IsCC, hry, h] at hy₀
      exact hy₀
    · have h1 : M.rho (y * zE M * y⁻¹) = M.rho (x * zE M * x⁻¹) + 1 := by
        rw [h, ← conj_zinv, hrx]
      rw [IsCC, hry, h1] at hy₀
      rcases hy₀ with hy₀ | hy₀
      · exact Or.inr hy₀
      · left
        rw [add_assoc, add_self_mat, add_zero] at hy₀
        exact hy₀
  have hxx : M.rho (x * zE M * x⁻¹) = decode u ∨ M.rho (x * zE M * x⁻¹) + 1 = decode u := by
    have hrx := rho_conj_zinv M hq x
    unfold IsCC at hx
    rw [hrx] at hx
    exact hx
  have hpar : ∀ (v : Array ℕ), Valid v → decode u' = decode (invDiag v) → v[0]! % 2 = 0 →
      False := by
    intro v hv hdec he0
    have h1 := eq_of_decode_eq hu' (valid_invDiag hv) hdec
    rw [h1, getElem!_invDiag_zero] at he'
    have hx := xor_one_mod_two ⟨v[0]!, hv.2 0 (by norm_num)⟩
    simp only at hx
    omega
  rcases hxx with h1 | h1 <;> rcases hAA hy with h2 | h2
  · exact eq_of_decode_eq hu hu' (h1.symm.trans h2)
  · exfalso
    exact hpar u hu (by rw [decode_invDiag hu, ← h1, h2]) he
  · exfalso
    exact hpar u hu (by rw [decode_invDiag hu, ← h1, ← h2, add_assoc, add_self_mat, add_zero]) he
  · exact eq_of_decode_eq hu hu' (h1.symm.trans h2)

@[expose] noncomputable def rootElt (D : OmCodes) (k : ℕ) : adjointGroup .G2 K :=
  if k = 0 then 1 else M.wordElt D.seedW[k - 1]!

@[expose] noncomputable def PX : Subgroup (adjointGroup .G2 K) :=
  Subgroup.closure {x | ∃ j < 4, x = gElt M j}

@[expose] noncomputable def symElt (s : ℕ) : adjointGroup .G2 K :=
  if s < 4 then gElt M s else (gElt M (s - 4))⁻¹

@[expose] noncomputable def schElt (w : List ℕ) : adjointGroup .G2 K := (w.map (symElt M)).prod

theorem gElt_mem_PX {j : ℕ} (hj : j < 4) : gElt M j ∈ PX M := Subgroup.subset_closure ⟨j, hj, rfl⟩

theorem symElt_mem_PX {s : ℕ} (hs : s < 8) : symElt M s ∈ PX M := by
  unfold symElt
  split_ifs with h
  · exact gElt_mem_PX M h
  · exact Subgroup.inv_mem _ (gElt_mem_PX M (by omega))

theorem schElt_mem_PX {w : List ℕ} (hw : ∀ s ∈ w, s < 8) : schElt M w ∈ PX M := by
  unfold schElt
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
  exact symElt_mem_PX M (hw s hs)

section Forest

variable (D : OmCodes)

theorem forest_root (hD : D.OK) (hq : quadOK tzc = true) {k : ℕ} (hk : k < 5) :
    Valid (D.pt (omLo k)) ∧ (D.pt (omLo k))[0]! % 2 = 0 ∧
      IsCC M (D.pt (omLo k)) (rootElt M D k) := by
  have h0 : IsCC M tzc 1 := Or.inl (by simp [rho_zE])
  by_cases hk0 : k = 0
  · subst hk0
    rw [omLo_vals.1, hD.root0, rootElt, if_pos rfl]
    exact ⟨valid_canonCode valid_tzc, canon_even valid_tzc, isCC_canon M valid_tzc hq h0⟩
  · rw [hD.roots k (by omega) hk, rootElt, if_neg hk0]
    have hmem : D.seedW[k - 1]! ∈ D.seedW := by
      rw [getElem!_pos D.seedW (k - 1) (by rw [hD.seed_len]; omega)]
      exact List.getElem_mem _
    obtain ⟨hr1, hr2⟩ := hD.seed_rev _ hmem
    have hinv := wordElt_reverse_eq_inv M hr1
    have hstep := isCC_step M valid_tzc (valid_wordCode D.seedW[k - 1]!)
      (valid_wordCode (D.seedW[k - 1]!).reverse) (M.rho_wordElt _)
      (by rw [← hinv]; exact M.rho_wordElt _) h0
    rw [mul_one] at hstep
    have hv := valid_mulCode (valid_mulCode (valid_wordCode D.seedW[k - 1]!) valid_tzc)
      (valid_wordCode (D.seedW[k - 1]!).reverse)
    exact ⟨valid_canonCode hv, canon_even hv, isCC_canon M hv hq hstep⟩

theorem forest_sem (hD : D.OK) (hq : quadOK tzc = true) :
    ∀ n < 130816, Valid (D.pt n) ∧ (D.pt n)[0]! % 2 = 0 ∧ ∃ p ∈ PX M,
      IsCC M (D.pt n) (p * rootElt M D (omIdx n)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    obtain ⟨hk5, hlo, hhi⟩ := omIdx_spec hn
    rcases Nat.eq_or_lt_of_le hlo with hr | hr
    · obtain ⟨a, b, c⟩ := forest_root M D hD hq hk5
      rw [hr] at a b c
      exact ⟨a, b, 1, Subgroup.one_mem _, by rw [one_mul]; exact c⟩
    · obtain ⟨hp1, hp2, hs, he⟩ := hD.step (omIdx n) hk5 n hr hhi
      have hidx : omIdx (D.par n) = omIdx n := omIdx_eq hk5 hp1 (lt_trans hp2 hhi)
      obtain ⟨hv, -, p, hpmem, hc⟩ := ih (D.par n) hp2 (lt_trans hp2 hn)
      rw [hidx] at hc
      have hgi : M.rho (gElt M (D.sym n))⁻¹ = decode (wordCode (gW[D.sym n]!).reverse) := by
        rw [← gInv_eq M hs]
        exact rho_gInv M (D.sym n)
      have hvv := valid_mulCode (valid_mulCode (valid_wordCode gW[D.sym n]!) hv)
        (valid_wordCode (gW[D.sym n]!).reverse)
      have hst := isCC_step M hv (valid_wordCode _) (valid_wordCode _) (rho_gElt M (D.sym n)) hgi hc
      rw [← mul_assoc] at hst
      rw [he]
      exact ⟨valid_canonCode hvv, canon_even hvv, gElt M (D.sym n) * p,
        Subgroup.mul_mem _ (gElt_mem_PX M hs) hpmem, isCC_canon M hvv hq hst⟩

end Forest

section HTree

theorem sym_rho {s : ℕ} (hs : s < 8) :
    Valid omSc[s]! ∧ Valid omSic[s]! ∧ M.rho (symElt M s) = decode omSc[s]! ∧
      M.rho (symElt M s)⁻¹ = decode omSic[s]! := by
  rw [omSc_getElem hs, omSic_getElem hs]
  simp only [symElt]
  by_cases h : s < 4
  · simp only [h, ite_true]
    refine ⟨valid_wordCode _, valid_wordCode _, rho_gElt M s, ?_⟩
    rw [← gInv_eq M h]
    exact rho_gInv M s
  · have h4 : s - 4 < 4 := by omega
    simp only [h, ite_false]
    refine ⟨valid_wordCode _, valid_wordCode _, ?_, ?_⟩
    · rw [← gInv_eq M h4]
      exact rho_gInv M (s - 4)
    · rw [inv_inv]
      exact rho_gElt M (s - 4)

theorem foldl_rho {f : ℕ → adjointGroup .G2 K} {cs : Array (Array ℕ)} (w : List ℕ)
    (hw : ∀ s ∈ w, Valid cs[s]! ∧ M.rho (f s) = decode cs[s]!) :
    ∀ (x : adjointGroup .G2 K) (A : Array ℕ), Valid A → M.rho x = decode A →
      Valid (w.foldl (fun A s => mulCode A cs[s]!) A) ∧
      M.rho (x * (w.map f).prod) = decode (w.foldl (fun A s => mulCode A cs[s]!) A) := by
  induction w with
  | nil =>
    intro x A hA hx
    exact ⟨hA, by simpa using hx⟩
  | cons s w ih =>
    intro x A hA hx
    obtain ⟨hs1, hs2⟩ := hw s (by simp)
    have := ih (fun s' hs' => hw s' (List.mem_cons_of_mem _ hs')) (x * f s)
      (mulCode A cs[s]!) (valid_mulCode hA hs1)
      (by rw [map_mul, hx, hs2, decode_mulCode hA hs1])
    simpa [List.foldl_cons, List.map_cons, List.prod_cons, mul_assoc] using this

theorem sch_rho (w : List ℕ) (hw : ∀ s ∈ w, s < 8) :
    Valid (schCode omSc w) ∧ M.rho (schElt M w) = decode (schCode omSc w) ∧
    Valid (schInv omSic w) ∧ M.rho (schElt M w)⁻¹ = decode (schInv omSic w) := by
  have h1 := foldl_rho M (f := symElt M) (cs := omSc) w
    (fun s hs => ⟨(sym_rho M (hw s hs)).1, (sym_rho M (hw s hs)).2.2.1⟩) 1 idCode
    valid_idCode (by rw [map_one, decode_idCode])
  have h2 := foldl_rho M (f := fun s => (symElt M s)⁻¹) (cs := omSic) w.reverse
    (fun s hs => ⟨(sym_rho M (hw s (List.mem_reverse.mp hs))).2.1,
      (sym_rho M (hw s (List.mem_reverse.mp hs))).2.2.2⟩) 1 idCode
    valid_idCode (by rw [map_one, decode_idCode])
  have e : (schElt M w)⁻¹ = (w.reverse.map fun s => (symElt M s)⁻¹).prod := by
    simp [schElt, List.prod_inv_reverse, List.map_reverse, Function.comp_def]
  refine ⟨h1.1, by simpa [schElt, schCode] using h1.2, h2.1, ?_⟩
  rw [e, schInv]
  simpa using h2.2

variable (D : OmCodes)

theorem htree_sem (hD : D.OK) (hq : quadOK tzc = true) (xc : adjointGroup .G2 K)
    (hxc : IsCC M (D.hpt 0) xc) (hv : Valid (D.hpt 0)) (hev : (D.hpt 0)[0]! % 2 = 0) :
    ∀ n < 1024, Valid (D.hpt n) ∧ (D.hpt n)[0]! % 2 = 0 ∧
      ∃ q ∈ Subgroup.closure {x | ∃ t < 8, x = schElt M D.schW[t]!},
        IsCC M (D.hpt n) (q * xc) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exact ⟨hv, hev, 1, Subgroup.one_mem _, by rw [one_mul]; exact hxc⟩
    · obtain ⟨hp, ht, he⟩ := hD.hstep n hpos hn
      obtain ⟨hv', -, q, hqmem, hc⟩ := ih (D.hpar n) hp (lt_trans hp hn)
      have hmem : D.schW[D.hsym n]! ∈ D.schW := by
        rw [getElem!_pos D.schW _ (by rw [hD.sch_len]; exact ht)]
        exact List.getElem_mem _
      obtain ⟨h1, h2, h3, h4⟩ := sch_rho M _ (hD.sch_sym _ hmem)
      have hvv := valid_mulCode (valid_mulCode h1 hv') h3
      have hst := isCC_step M hv' h1 h3 h2 h4 hc
      rw [← mul_assoc] at hst
      rw [he]
      exact ⟨valid_canonCode hvv, canon_even hvv, schElt M D.schW[D.hsym n]! * q,
        Subgroup.mul_mem _ (Subgroup.subset_closure ⟨D.hsym n, ht, rfl⟩) hqmem,
        isCC_canon M hvv hq hst⟩

end HTree

@[expose] noncomputable def SX : Subgroup (adjointGroup .G2 K) :=
  Subgroup.normalizer (Subgroup.zpowers (zE M) : Set (adjointGroup .G2 K))

theorem PX_le_SX : PX M ≤ SX M := by
  unfold PX SX
  rw [Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  apply mem_normalizer_of_conj_le
  intro x hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have e : gElt M j * zE M ^ k * (gElt M j)⁻¹ = (gElt M j * zE M * (gElt M j)⁻¹) ^ k := by
    rw [conj_zpow]
  rw [e]
  apply Subgroup.zpow_mem
  rcases gElt_conj_z M hj with h | h
  · rw [h]
    exact Subgroup.mem_zpowers _
  · rw [h]
    exact Subgroup.mul_mem _ (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _)

theorem filter_omIdx {k : ℕ} (hk : k < 5) :
    ((Finset.range 130816).filter fun n => omIdx n = k) = Finset.Ico (omLo k) (omLo (k + 1)) := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  constructor
  · rintro ⟨hn, rfl⟩
    exact ⟨(omIdx_spec hn).2.1, (omIdx_spec hn).2.2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨lt_of_lt_of_le h2 (omLo_le hk), omIdx_eq hk h1 h2⟩

theorem omega_main (D : OmCodes) (hK : Nat.card K = 8) (hD : D.OK) :
    PX M = SX M ∧ Nat.card (SX M) = 33094656 ∧
      ∀ H : Subgroup (adjointGroup .G2 K), SX M ≤ H → H = SX M ∨ H = ⊤ := by
  classical
  have hq : quadOK tzc = true := quadOK_tzc_of hD.quad
  have hfs := forest_sem M D hD hq
  choose! px hpx using fun n (hn : n < 130816) => (hfs n hn).2.2
  let xe : ℕ → adjointGroup .G2 K := fun n => px n * rootElt M D (omIdx n)
  let B : ℕ → Subgroup (adjointGroup .G2 K) := fun n => Bsub M (xe n)
  have hBinj : ∀ i < 130816, ∀ j < 130816, B i = B j → i = j := by
    intro i hi j hj hB
    exact hD.inj i hi j hj (isCC_code_eq M hq (hfs i hi).1 (hfs j hj).1 (hfs i hi).2.1
      (hfs j hj).2.1 (hpx i hi).2 (hpx j hj).2 hB)
  have hBconj : ∀ n < 130816, ∃ x, B n = conjSub x (Subgroup.zpowers (zE M)) := fun n _ =>
    ⟨xe n, rfl⟩
  have hBn : ∀ n < 130816, B n = conjSub (px n) (Bsub M (rootElt M D (omIdx n))) := fun n _ =>
    Bsub_mul M _ _
  have hroot1 := forest_root M D hD hq (k := 1) (by norm_num)
  rw [omLo_vals.2.1] at hroot1
  have hmemt : ∀ t < 8, D.schW[t]! ∈ D.schW := fun t ht => by
    rw [getElem!_pos D.schW t (by rw [hD.sch_len]; exact ht)]
    exact List.getElem_mem _
  have hfixA : ∀ w ∈ D.schW,
      conjSub (schElt M w) (Bsub M (rootElt M D 1)) = Bsub M (rootElt M D 1) := by
    intro w hw
    obtain ⟨h1, h2, h3, h4⟩ := sch_rho M w (hD.sch_sym w hw)
    have hstep := isCC_step M hroot1.1 h1 h3 h2 h4 hroot1.2.2
    have hcan : IsCC M (canonCode (conjCode (schCode omSc w) (schInv omSic w) (D.pt 1)))
        (schElt M w * rootElt M D 1) :=
      isCC_canon M (valid_mulCode (valid_mulCode h1 hroot1.1) h3) hq hstep
    rw [hD.fix w hw] at hcan
    rw [← Bsub_mul]
    exact isCC_Bsub_eq M hcan hroot1.2.2
  let Q : Subgroup (adjointGroup .G2 K) :=
    Subgroup.closure {x | ∃ t < 8, x = schElt M D.schW[t]!}
  have hQP : Q ≤ PX M := by
    rw [Subgroup.closure_le]
    rintro _ ⟨t, ht, rfl⟩
    exact schElt_mem_PX M (hD.sch_sym _ (hmemt t ht))
  have hQA : Q ≤ Subgroup.normalizer (Bsub M (rootElt M D 1) : Set (adjointGroup .G2 K)) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨t, ht, rfl⟩
    exact conjSub_eq_self_iff.mp (hfixA _ (hmemt t ht))
  have hxc : IsCC M (D.hpt 0) (xe D.c) := by
    rw [hD.hroot]
    exact (hpx D.c hD.c_lt).2
  have hts := htree_sem M D hD hq (xe D.c) hxc (by rw [hD.hroot]; exact (hfs _ hD.c_lt).1)
    (by rw [hD.hroot]; exact (hfs _ hD.c_lt).2.1)
  choose! qq hqq using fun n (hn : n < 1024) => (hts n hn).2.2
  have hm : 32319 * 1024 ≤ Nat.card (PX M) := by
    have hcard1 : 32319 ≤ ((Finset.range 130816).filter fun n => omIdx n = 1).card := by
      rw [filter_omIdx (by norm_num), Nat.card_Ico]
      decide
    have hchain := card_ge_chain (A := Bsub M (rootElt M D 1)) (C := Bsub M (xe D.c))
      ((Finset.range 130816).filter fun n => omIdx n = 1) (Finset.range 1024) hQP hQA px
      (fun i hi => by
        rw [Finset.mem_filter, Finset.mem_range] at hi
        exact (hpx i hi.1).1)
      (fun i hi j hj hij => by
        rw [Finset.mem_filter, Finset.mem_range] at hi hj
        refine hBinj i hi.1 j hj.1 ?_
        rw [hBn i hi.1, hBn j hj.1, hi.2, hj.2]
        exact hij)
      qq (fun i hi => (hqq i (Finset.mem_range.mp hi)).1)
      (fun i hi j hj hij => by
        have hi' := Finset.mem_range.mp hi
        have hj' := Finset.mem_range.mp hj
        rw [← Bsub_mul, ← Bsub_mul] at hij
        exact hD.hinj i hi' j hj' (isCC_code_eq M hq (hts i hi').1 (hts j hj').1
          (hts i hi').2.1 (hts j hj').2.1 (hqq i hi').2 (hqq j hj').2 hij))
    rw [Finset.card_range] at hchain
    exact le_trans (Nat.mul_le_mul hcard1 le_rfl) hchain
  have hG : Nat.card (adjointGroup .G2 K) = 130816 * (32319 * 1024) := by
    rw [card_X' hK]
    norm_num
  obtain ⟨hPS, hSm, hsurj⟩ := counting_conj (A := Subgroup.zpowers (zE M)) (P := PX M)
    (PX_le_SX M) hG hm B hBconj hBinj
  have hrt : ∀ n < 130816, omIdx n < 5 := fun n hn => (omIdx_spec hn).1
  have hrt0 : omIdx 0 = 0 := rfl
  have hSX : ∀ n < 130816, px n ∈ Subgroup.normalizer (Subgroup.zpowers (zE M) :
      Set (adjointGroup .G2 K)) := fun n hn => PX_le_SX M (hpx n hn).1
  have hB0 : B 0 = Subgroup.zpowers (zE M) := by
    show Bsub M (px 0 * rootElt M D (omIdx 0)) = _
    rw [hrt0, rootElt, if_pos rfl, mul_one, Bsub, conjSub_eq_self_iff]
    exact hSX 0 (by norm_num)
  have hmax := maximal_of_trees (A := Subgroup.zpowers (zE M)) hG hSm (by norm_num) B omIdx px
    (fun k => Bsub M (rootElt M D k)) (fun k => omLo (k + 1) - omLo k) hsurj hBinj
    (fun n hn => ⟨hSX n hn, hBn n hn⟩) hrt (by norm_num) hrt0 hB0
    (fun k hk => by rw [filter_omIdx hk, Nat.card_Ico]) (by decide)
    (subsetOK_spec (N := 130816) (sz := fun k => omLo (k + 1) - omLo k) (by decide))
  refine ⟨hPS, ?_, hmax⟩
  show Nat.card (Subgroup.normalizer (Subgroup.zpowers (zE M) : Set (adjointGroup .G2 K))) = _
  rw [hSm]

end Omega

section Final


variable {K : Type} [Field K] [Finite K] [CharP K 2] (M : G28Model K)

theorem omega_facts (hK : Nat.card K = 8) :
    PX M = SX M ∧ Nat.card (SX M) = 33094656 ∧
      ∀ H : Subgroup (adjointGroup .G2 K), SX M ≤ H → H = SX M ∨ H = ⊤ := by
  obtain ⟨D, hD⟩ := Certificates.certificate9558
  exact omega_main M D hK hD

end Final

end CFSG.AGLEmbedding.KFactProofs.G28
