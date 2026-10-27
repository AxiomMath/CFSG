module

public import CFSG.GF2Type.SmithTypeE.E7.TrClass
public import CFSG.GF2Type.SmithTypeE.DMod.RhoTD6
public import Certificates.Certificate38791
public import Certificates.Certificate38792
public import Certificates.Certificate38793
public import Certificates.Certificate38794

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E7

open CFSG.SmithD6 CFSG.GF2Type.SmithTypeE.DMod CFSG.RankThree.OrthogonalInvolutions Module

section Elt


@[expose] noncomputable def tvElt (k : ℕ) : TD6 :=
  if h : k < 365211 then ⟨tvP ⟨k, h⟩, tvP_mem _⟩ else 1

theorem tvElt_coe {k : ℕ} (hk : k < 365211) :
    ((tvElt k : TD6) : Equiv.Perm (Fin 365211)) = tvP ⟨k, hk⟩ := by
  simp [tvElt, hk]

@[expose] noncomputable def repElt (j : ℕ) : TD6 := ((tr7RepIdx j).map tvElt).prod

theorem prod_tvElt_apply_val :
    ∀ (L : List ℕ), (∀ k ∈ L, k < 365211) → ∀ a : Fin 365211,
      ((((L.map tvElt).prod : TD6) : Equiv.Perm (Fin 365211)) a : ℕ) =
        L.foldr (fun r acc => tvImg r acc) a.val
  | [], _, a => by simp
  | r :: L, h, a => by
    have hr : r < 365211 := h r (List.mem_cons_self ..)
    rw [List.map_cons, List.prod_cons, List.foldr_cons, Subgroup.coe_mul, Equiv.Perm.coe_mul,
      Function.comp_apply, tvElt_coe hr, tvP_apply,
      prod_tvElt_apply_val L (fun k hk => h k (List.mem_cons_of_mem _ hk)) a]

theorem siegelEquiv_eq_siegelK_of_codes {u w : ℕ} (hu : u < 4096) (hw : w < 4096) (hu0 : u ≠ 0)
    (hw0 : w ≠ 0) (hqu : qf u = false) (hqw : qf w = false) (huw : u ≠ w)
    (hb : bf u w = false) :
    lineOf u w < 365211 ∧ siegelEquiv (dec12 u) (dec12 w) = siegelK (lineOf u w) := by
  obtain ⟨hlt, hset⟩ := lineSet_lineIdx3 hu hw hu0 hw0 hqu hqw huw hb
  have hlt' : lineOf u w < 365211 := hlt
  refine ⟨hlt', ?_⟩
  unfold siegelK
  have hk := lineSet_eq (lineOf u w)
  obtain ⟨hp1, hp2, hp3⟩ := linePair_ne hlt'
  exact siegelEquiv_eq_of_lineOfPair_eq (tsPair_dec12 hqu hqw hb) (tsPair_linePair hlt')
    (dec12_ne_zero hu hu0) (dec12_ne_zero hw hw0)
    (fun h => huw (eq_of_dec12_eq hu hw h)) hp1 hp2 hp3 hset.symm

end Elt

section Link

variable
  {j : ℕ}

theorem rep_idx_lt (hj : j < 7) : ∀ k ∈ tr7RepIdx j, k < 365211 := by
  intro k hk
  unfold tr7RepIdx at hk
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hk
  obtain ⟨h0, h1, h2, h3, hn, hq1, hq2, hb⟩ := rep_lines_ok hj p hp
  exact (siegelEquiv_eq_siegelK_of_codes h1 h3 (by omega) (by omega) hq1 hq2 hn hb).1

def ValidLine (p : ℕ × ℕ) : Prop :=
  0 < p.1 ∧ p.1 < 4096 ∧ 0 < p.2 ∧ p.2 < 4096 ∧ p.1 ≠ p.2 ∧ qf p.1 = false ∧ qf p.2 = false ∧
    bf p.1 p.2 = false

theorem siegel_mem_omega_of_valid {p : ℕ × ℕ} (h : ValidLine p) :
    siegelEquiv (dec12 p.1) (dec12 p.2) ∈ CFSG.Open.timmesfeldOmegaPlus 6 := by
  obtain ⟨h0, h1, h2, h3, hn, hq1, hq2, hb⟩ := h
  obtain ⟨hlt, hk⟩ := siegelEquiv_eq_siegelK_of_codes h1 h3 (by omega) (by omega) hq1 hq2 hn hb
  rw [hk]
  exact siegelK_mem_omega hlt

@[expose] noncomputable def sigL (L : List (ℕ × ℕ)) : V12 ≃ₗ[ZMod 2] V12 :=
  (L.map fun p => siegelEquiv (dec12 p.1) (dec12 p.2)).prod

theorem sigL_nil : sigL [] = 1 := rfl

theorem sigL_cons (p : ℕ × ℕ) (L : List (ℕ × ℕ)) :
    sigL (p :: L) = siegelEquiv (dec12 p.1) (dec12 p.2) * sigL L := rfl

theorem prod_siegel_mem :
    ∀ (L : List (ℕ × ℕ)), (∀ p ∈ L, ValidLine p) → sigL L ∈ CFSG.Open.timmesfeldOmegaPlus 6
  | [], _ => by
    rw [sigL_nil]
    exact one_mem _
  | p :: L, h => by
    rw [sigL_cons]
    exact mul_mem (siegel_mem_omega_of_valid (h p (List.mem_cons_self ..)))
      (prod_siegel_mem L (fun q hq => h q (List.mem_cons_of_mem _ hq)))

@[expose] noncomputable def sigProd (L : List (ℕ × ℕ)) (h : ∀ p ∈ L, ValidLine p) :
    ↥(CFSG.Open.timmesfeldOmegaPlus 6) :=
  ⟨sigL L, prod_siegel_mem L h⟩

theorem sigProd_nil (h : ∀ p ∈ ([] : List (ℕ × ℕ)), ValidLine p) : sigProd [] h = 1 :=
  Subtype.ext sigL_nil

theorem sigProd_cons (p : ℕ × ℕ) (L : List (ℕ × ℕ)) (h : ∀ q ∈ p :: L, ValidLine q) :
    sigProd (p :: L) h = ⟨siegelEquiv (dec12 p.1) (dec12 p.2),
      siegel_mem_omega_of_valid (h p (List.mem_cons_self ..))⟩ *
        sigProd L (fun q hq => h q (List.mem_cons_of_mem _ hq)) :=
  Subtype.ext (sigL_cons p L)

theorem omegaTD6_prod_aux :
    ∀ (L : List (ℕ × ℕ)) (h : ∀ p ∈ L, ValidLine p),
      omegaTD6 (sigProd L h) = ((L.map fun p => lineOf p.1 p.2).map tvElt).prod
  | [], h => by
    rw [sigProd_nil, map_one]
    rfl
  | p :: L, h => by
    have hp := h p (List.mem_cons_self ..)
    obtain ⟨h0, h1, h2, h3, hn, hq1, hq2, hb⟩ := hp
    obtain ⟨hlt, hk⟩ := siegelEquiv_eq_siegelK_of_codes h1 h3 (by omega) (by omega) hq1 hq2 hn hb
    have hL := omegaTD6_prod_aux L (fun q hq => h q (List.mem_cons_of_mem _ hq))
    have hsk := siegel_mem_omega_of_valid (h p (List.mem_cons_self ..))
    rw [sigProd_cons, map_mul, hL]
    have e2 : (⟨siegelEquiv (dec12 p.1) (dec12 p.2), hsk⟩ : ↥(CFSG.Open.timmesfeldOmegaPlus 6)) =
        ⟨siegelK (lineOf p.1 p.2), siegelK_mem_omega hlt⟩ := Subtype.ext hk
    have e3 : omegaTD6 ⟨siegelK (lineOf p.1 p.2), siegelK_mem_omega hlt⟩ =
        tvElt (lineOf p.1 p.2) := by
      apply Subtype.ext
      rw [tvElt_coe hlt]
      exact omegaTD6_siegelK ⟨lineOf p.1 p.2, hlt⟩
    rw [e2, e3]
    rfl

include j in
theorem repElt_eq_omega (hj : j < 7)
    (hm : repV12 j ∈ CFSG.Open.timmesfeldOmegaPlus 6) : omegaTD6 ⟨repV12 j, hm⟩ = repElt j := by
  have h := omegaTD6_prod_aux (tr7RepLines j) (fun p hp => rep_lines_ok hj p hp)
  exact h

end Link

attribute [local irreducible] colsLin

section Spin

variable
  {j : ℕ}

theorem repElt_apply_val (hj : j < 7) (a : Fin 365211) :
    (((repElt j : TD6) : Equiv.Perm (Fin 365211)) a : ℕ) = tr7RepImg j a.val := by
  unfold repElt tr7RepImg
  exact prod_tvElt_apply_val (tr7RepIdx j) (rep_idx_lt hj) a

theorem commute_tvElt_repElt (hj : j < 7) {k : ℕ} (hk : k < 365211) (hfix : tr7RepImg j k = k) :
    (tvElt k : TD6) * repElt j = repElt j * tvElt k := by
  have hfix' : ((repElt j : TD6) : Equiv.Perm (Fin 365211)) ⟨k, hk⟩ = ⟨k, hk⟩ := by
    apply Fin.ext
    rw [repElt_apply_val hj]
    exact hfix
  have h := mul_tvP_mul_inv (repElt j).2 ⟨k, hk⟩
  rw [hfix'] at h
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, tvElt_coe hk]
  calc tvP ⟨k, hk⟩ * ((repElt j : TD6) : Equiv.Perm (Fin 365211)) =
        (((repElt j : TD6) : Equiv.Perm (Fin 365211)) * tvP ⟨k, hk⟩ *
          ((repElt j : TD6) : Equiv.Perm (Fin 365211))⁻¹) *
          ((repElt j : TD6) : Equiv.Perm (Fin 365211)) := by rw [h]
    _ = ((repElt j : TD6) : Equiv.Perm (Fin 365211)) * tvP ⟨k, hk⟩ := by group

theorem size_tr7Comp (A B : Array ℕ) : (tr7Comp A B).size = 32 := by simp [tr7Comp]

theorem size_tr7IdCols : tr7IdCols.size = 32 := by simp [tr7IdCols]

theorem size_foldr_cols (L : List ℕ) :
    (L.foldr (fun k acc => tr7Comp (tvCols k) acc) tr7IdCols).size = 32 := by
  induction L with
  | nil => exact size_tr7IdCols
  | cons k L ih => exact size_tr7Comp _ _

theorem size_tr7RepCols (j : ℕ) : (tr7RepCols j).size = 32 := size_foldr_cols _

theorem tr7Comp_getElem (A B : Array ℕ) (m : Fin 32) :
    (tr7Comp A B)[m.val]! = applyCols A B[m.val]! := by
  unfold tr7Comp
  rw [getElem!_pos _ m.val (by simp), Array.getElem_ofFn]
  rfl

theorem tr7IdCols_getElem (m : Fin 32) : tr7IdCols[m.val]! = 2 ^ m.val := by
  unfold tr7IdCols
  rw [getElem!_pos _ m.val (by simp), Array.getElem_ofFn]

theorem colsLin_tr7Comp (A B : Array ℕ) (hA : A.size = 32) :
    colsLin (tr7Comp A B) = colsLin A ∘ₗ colsLin B := by
  refine linearMap_ext_single fun m => ?_
  rw [colsLin_single, LinearMap.comp_apply, colsLin_single, ← decode32_applyCols hA,
    tr7Comp_getElem]

theorem colsLin_tr7IdCols : colsLin tr7IdCols = LinearMap.id := by
  refine linearMap_ext_single fun m => ?_
  rw [colsLin_single, LinearMap.id_apply, tr7IdCols_getElem, decode32_two_pow]

theorem decode32_applyCols_comp (A B : Array ℕ) (hA : A.size = 32) (hB : B.size = 32) (x : ℕ) :
    decode32 (applyCols (tr7Comp A B) x) = decode32 (applyCols A (applyCols B x)) := by
  rw [decode32_applyCols (size_tr7Comp A B), colsLin_tr7Comp A B hA, LinearMap.comp_apply,
    decode32_applyCols hA, decode32_applyCols hB]

theorem prod_tvEquiv_decode :
    ∀ (L : List ℕ), (∀ k ∈ L, k < 365211) → ∀ x : ℕ,
      ((L.map tvEquiv).prod) (decode32 x) =
        decode32 (applyCols (L.foldr (fun k acc => tr7Comp (tvCols k) acc) tr7IdCols) x)
  | [], _, x => by
    simp only [List.map_nil, List.prod_nil, List.foldr_nil, LinearEquiv.coe_one, id_eq]
    rw [decode32_applyCols size_tr7IdCols, colsLin_tr7IdCols]
    rfl
  | k :: L, h, x => by
    have hk : k < 365211 := h k (List.mem_cons_self ..)
    simp only [List.map_cons, List.prod_cons, List.foldr_cons, LinearEquiv.mul_apply]
    rw [prod_tvEquiv_decode L (fun k' hk' => h k' (List.mem_cons_of_mem _ hk')) x,
      tvEquiv_decode hk, decode32_applyCols_comp _ _ (size_tvCols k) (size_foldr_cols L)]

theorem rhoMod_repElt_decode (hj : j < 7) (x : ℕ) :
    rhoMod (repElt j) (decode32 x) = decode32 (applyCols (tr7RepCols j) x) := by
  have e : rhoMod (repElt j) = ((tr7RepIdx j).map tvEquiv).prod := by
    unfold repElt
    rw [map_list_prod, List.map_map]
    congr 1
    refine List.map_congr_left fun k hk => ?_
    have hk' := rep_idx_lt hj k hk
    simp only [Function.comp_apply]
    unfold tvElt
    rw [dif_pos hk']
    exact rhoMod_tvP ⟨k, hk'⟩
  rw [e]
  exact prod_tvEquiv_decode _ (rep_idx_lt hj) x

theorem sub_eq_add_V32 (a b : V) : a - b = a + b := by
  funext i
  simp only [Pi.sub_apply, Pi.add_apply]
  generalize a i = x
  generalize b i = y
  revert x y
  decide

theorem rho_col (hj : j < 7) (c : Fin 32) :
    rhoMod (repElt j) (Pi.single c 1) - Pi.single c 1 =
      decode32 ((tr7RepCols j)[c.val]! ^^^ 2 ^ c.val) := by
  have h1 : rhoMod (repElt j) (Pi.single c 1) = decode32 (tr7RepCols j)[c.val]! := by
    rw [← decode32_two_pow c, rhoMod_repElt_decode hj, decode32_applyCols (size_tr7RepCols j),
      decode32_two_pow, colsLin_single]
  rw [h1, decode32_xor, decode32_two_pow, sub_eq_add_V32]

theorem cols32_mem (hj : j < 7) : ∀ v ∈ tr7Cols32 j,
    decode32 v ∈ commSpace (rhoMod (repElt j)) := by
  intro v hv
  unfold tr7Cols32 at hv
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hv
  have hc' : c < 32 := List.mem_range.1 hc
  rw [← rho_col hj ⟨c, hc'⟩]
  exact sub_mem_commSpace _ _

theorem bs32_mem (hj : j < 7) : ∀ b ∈ tr7Bs32 j, decode32 b ∈ commSpace (rhoMod (repElt j)) := by
  intro b hb
  unfold tr7Bs32 tr7Bs at hb
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hb
  exact dec_ech_mem decode32_xor (U := commSpace (rhoMod (repElt j))) (tr7Cols32 j)
    (cols32_mem hj) e he

theorem commSpace_le_span32 (hj : j < 7)
    (hred : ∀ v ∈ tr7Cols32 j, tr7Red (tr7Ech (tr7Cols32 j)) v = 0) :
    commSpace (rhoMod (repElt j)) ≤
      Submodule.span (ZMod 2) {u | ∃ b ∈ tr7Bs32 j, u = decode32 b} := by
  have hspan : Submodule.span (ZMod 2) (Set.range fun m : Fin 32 => (Pi.single m (1 : ZMod 2) : V))
      = ⊤ := by
    have h1 := (Pi.basisFun (ZMod 2) (Fin 32)).span_eq
    have h2 : (Set.range fun m : Fin 32 => (Pi.single m (1 : ZMod 2) : V)) =
        Set.range ⇑(Pi.basisFun (ZMod 2) (Fin 32)) := by
      congr 1
      funext m
      rw [Pi.basisFun_apply]
    rw [h2]
    exact h1
  have hmap : commSpace (rhoMod (repElt j)) =
      (Submodule.span (ZMod 2) (Set.range fun m : Fin 32 => (Pi.single m (1 : ZMod 2) : V))).map
        ((rhoMod (repElt j) : V →ₗ[ZMod 2] V) - 1) := by
    rw [hspan, Submodule.map_top]
  rw [hmap, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
  have e : ((rhoMod (repElt j) : V →ₗ[ZMod 2] V) - 1) (Pi.single m 1) =
      decode32 ((tr7RepCols j)[m.val]! ^^^ 2 ^ m.val) := by
    have e0 : ((rhoMod (repElt j) : V →ₗ[ZMod 2] V) - 1) (Pi.single m 1) =
        rhoMod (repElt j) (Pi.single m 1) - Pi.single m 1 := rfl
    rw [e0]
    exact rho_col hj m
  show ((rhoMod (repElt j) : V →ₗ[ZMod 2] V) - 1) (Pi.single m 1) ∈ _
  rw [e]
  refine dec_red_mem decode32_xor (tr7Ech (tr7Cols32 j)) _ (fun e he => ?_) ?_
  · exact Submodule.subset_span ⟨e.2, List.mem_map.2 ⟨e, he, rfl⟩, rfl⟩
  · have hv : (tr7RepCols j)[m.val]! ^^^ 2 ^ m.val ∈ tr7Cols32 j :=
      List.mem_map.2 ⟨m.val, List.mem_range.2 m.2, rfl⟩
    rw [hred _ hv, decode32_zero]
    exact Submodule.zero_mem _

end Spin

section Dim

variable
  {j : ℕ}

theorem tr7ChkDims_holds : tr7ChkDims = true := Certificates.certificate38791

theorem tr7ChkDim_of_lt (hj : j < 7) : tr7ChkDim j = true :=
  List.all_eq_true.1 tr7ChkDims_holds j (List.mem_range.2 hj)

theorem eight_le_finrank_commSpace (hj : j < 7) :
    8 ≤ finrank (ZMod 2) (commSpace (rhoMod (repElt j))) := by
  have h := tr7ChkDim_of_lt hj
  unfold tr7ChkDim at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hind, hlt⟩, hlen⟩, -⟩ := h
  have hle := le_finrank_of_indep decode32_xor decode32_inj (U := commSpace (rhoMod (repElt j)))
    (bs := (tr7Bs32 j).take 8) (fun b hb => by
      have := List.all_eq_true.1 hlt b hb
      simpa using this) (fun b hb => bs32_mem hj b (List.mem_of_mem_take hb)) hind
  rw [List.length_take, min_eq_left hlen] at hle
  exact hle

theorem not_totallySingular (hj : j = 2 ∨ j = 6) {q : QuadraticForm (ZMod 2) V}
    (hpol : ∀ u v, QuadraticMap.polar q u v = fModel u v) (hwt : ∀ i < 75735, q (wtV i) = 0) :
    ∃ v ∈ commSpace (rhoMod (repElt j)), q v ≠ 0 := by
  have hj7 : j < 7 := by rcases hj with rfl | rfl <;> norm_num
  have h := tr7ChkDim_of_lt hj7
  unfold tr7ChkDim at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨-, hany⟩ := h
  have hjc : (j == 2 || j == 6) = true := by rcases hj with rfl | rfl <;> decide
  rw [if_pos hjc] at hany
  obtain ⟨i, hi, hfi⟩ := List.any_eq_true.1 hany
  have hi' : i < 75735 := List.mem_range.1 hi
  let ii : Fin 75735 := ⟨i, hi'⟩
  have hAw : rhoMod (repElt j) (wtV i) = decode32 (applyCols (tr7RepCols j) (wt i)) :=
    rhoMod_repElt_decode hj7 _
  have hAw2 : rhoMod (repElt j) (wtV i) = wtV ((repElt j • ii : Fin 75735)).val :=
    rhoMod_wtV (repElt j) ii
  refine ⟨rhoMod (repElt j) (wtV i) - wtV i, sub_mem_commSpace _ _, ?_⟩
  have hq2 : q (rhoMod (repElt j) (wtV i)) = 0 := by
    rw [hAw2]
    exact hwt _ (repElt j • ii).2
  rw [sub_eq_add_V32, add_comm, QuadraticMap.map_add (⇑q), hpol, hq2, hwt i hi', hAw]
  show 0 + 0 + fModel (decode32 (wt i)) (decode32 (applyCols (tr7RepCols j) (wt i))) ≠ 0
  rw [fModel_decode, hfi]
  decide

end Dim

section M1

variable
  {j : ℕ}

@[expose] def M1Facts (j : ℕ) : Prop :=
  (∀ k ∈ tr7Gens j, k < 365211 ∧ tr7RepImg j k = k) ∧ wtIdx (tr7Target j) < 75735 ∧
    (∀ v ∈ tr7Cols32 j, tr7Red (tr7Ech (tr7Cols32 j)) v = 0) ∧
    ∀ m < 2 ^ (tr7Bs32 j).length, tr7XorSel (tr7Bs32 j) m = 0 ∨
      ∀ U : Submodule (ZMod 2) V, (∀ k ∈ tr7Gens j, ∀ c, decode32 c ∈ U →
        decode32 (applyCols (tvCols k) c) ∈ U) →
        decode32 (tr7XorSel (tr7Bs32 j) m) ∈ U → decode32 (tr7Target j) ∈ U

theorem tr7ChkM1a_holds : ∀ j, j = 0 ∨ j = 1 ∨ j = 3 → M1Facts j :=
  Certificates.certificate38792

theorem tr7ChkM1b_holds : M1Facts 4 := Certificates.certificate38793

theorem tr7ChkM1c_holds : M1Facts 5 := Certificates.certificate38794

theorem m1Facts_of_mem (hj : j = 0 ∨ j = 1 ∨ j = 3 ∨ j = 4 ∨ j = 5) : M1Facts j := by
  rcases hj with rfl | rfl | rfl | rfl | rfl
  · exact tr7ChkM1a_holds 0 (Or.inl rfl)
  · exact tr7ChkM1a_holds 1 (Or.inr (Or.inl rfl))
  · exact tr7ChkM1a_holds 3 (Or.inr (Or.inr rfl))
  · exact tr7ChkM1b_holds
  · exact tr7ChkM1c_holds

theorem gens_ok (hj : j = 0 ∨ j = 1 ∨ j = 3 ∨ j = 4 ∨ j = 5) :
    ∀ k ∈ tr7Gens j, k < 365211 ∧ tr7RepImg j k = k :=
  (m1Facts_of_mem hj).1

theorem m1_rep (hj : j = 0 ∨ j = 1 ∨ j = 3 ∨ j = 4 ∨ j = 5) {N : Submodule (ZMod 2) V}
    (hN : N ≠ ⊥) (hle : N ≤ commSpace (rhoMod (repElt j)))
    (hinv : ∀ k ∈ tr7Gens j, ∀ n ∈ N, tvEquiv k n ∈ N) : ∃ i < 75735, wtV i ∈ N := by
  have hj7 : j < 7 := by omega
  obtain ⟨hgens, htarget, hred, hall⟩ := m1Facts_of_mem hj
  obtain ⟨n₀, hn₀N, hn₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN
  obtain ⟨m, hm, hmn⟩ := exists_xorSel_of_mem_span decode32_xor (tr7Bs32 j)
    (commSpace_le_span32 hj7 hred (hle hn₀N))
  rcases hall m hm with h0 | hcont
  · exfalso
    apply hn₀0
    rw [hmn, h0, decode32_zero]
  · have hU : ∀ k ∈ tr7Gens j, ∀ c, decode32 c ∈ N → decode32 (applyCols (tvCols k) c) ∈ N := by
      intro k hk c hc
      rw [← tvEquiv_decode (hgens k hk).1]
      exact hinv k hk _ hc
    have hdec := hcont N hU (by rw [← hmn]; exact hn₀N)
    refine ⟨wtIdx (tr7Target j), htarget, ?_⟩
    have hspec : wt (wtIdx (tr7Target j)) = tr7Target j := wtIdx_spec htarget
    unfold wtV
    rw [hspec]
    exact hdec

end M1

end CFSG.GF2Type.SmithTypeE.E7
