module

public import Certificates.Data.Kernel.KGC31PB
public import CFSG.Certificates.Kernel.KGC31PSound
public import CFSG.Certificates.Kernel.SporSch.ChainKElem
public import CFSG.Quasithin.Vol2.KGFactC31CosetCheck

public section

namespace CFSG.KC.KGC31P

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KC.HeGlueK
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Quasithin.KGC31.Native
open CFSG.KC.Child3 (tabP ap_tabP tabP_size)

variable {n w : Nat}

theorem foldl_congr' {α β : Type} {F G : β → α → β} :
    ∀ {l : List α} (b : β), (∀ a ∈ l, ∀ c, F c a = G c a) → l.foldl F b = l.foldl G b
  | [], _, _ => rfl
  | a :: l, b, h => by
    rw [List.foldl_cons, List.foldl_cons, h a List.mem_cons_self b]
    exact foldl_congr' _ fun x hx c => h x (List.mem_cons_of_mem _ hx) c

theorem ap_tabP' {X i : Nat} (hX : PP n w X) (hi : i < n) : ap (tabP n w X) i = pg w (mask w) X i := by
  obtain ⟨-, -, -, hr⟩ := PF.canon_facts hX.1
  exact ap_tabP hi (by have := hr i hi; have := hX.lt32; omega)

theorem ap_compT {P Q : Table} {i : Nat} (hi : i < n) : ap (compT n P Q) i = ap P (ap Q i) := by
  unfold ap compT
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem commAll_tabP {gs : List Nat} (hg : ∀ g ∈ gs, PP n w g) {e : Nat} (he : PP n w e) :
    commAll n (gs.map (tabP n w)) (tabP n w e) = pcommAll n w gs e := by
  rw [commAll, pcommAll]
  exact all_map_congr fun g hgg => commT_tabP he (hg g hgg)

theorem masksOK_tabP (hsz : szOK n w = true) {bs : List Nat} (hb : ∀ b ∈ bs, PP n w b) {g : Nat}
    (hg : PP n w g) (masks : List Nat) :
    masksOK n (bs.map (tabP n w)) (tabP n w g) masks = pmasksOK n w bs g masks := by
  rw [masksOK, pmasksOK, List.length_map, List.zip_map_left, List.all_map]
  congr 1
  refine all_congr' fun p hp => ?_
  have hp1 : PP n w p.1 := hb p.1 (List.of_mem_zip hp).1
  have hm := PP_pmask hsz bs hb p.2
  simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id]
  rw [maskProd_tabP hsz bs hb, compT_tabP' hg hp1, compT_tabP' hm hg,
    tblEq_tabP (hg.pc hp1) (hm.pc hg)]

theorem blocksOK_tabP {bl : List (List Nat)} (hbl : ∀ B ∈ bl, ∀ p ∈ B, p < n) {g : Nat}
    (hg : PP n w g) : blocksOK bl (tabP n w g) = pblocksOK w bl g := by
  rw [blocksOK, pblocksOK]
  refine all_congr' fun B hB => any_congr' fun B' _ => all_congr' fun p hp => ?_
  rw [ap_tabP' hg (hbl B hB p hp)]

theorem fixesBlocks_tabP {bl : List (List Nat)} (hbl : ∀ B ∈ bl, ∀ p ∈ B, p < n) {g : Nat}
    (hg : PP n w g) : fixesBlocks bl (tabP n w g) = pfixesBlocks w bl g := by
  rw [fixesBlocks, pfixesBlocks]
  refine all_congr' fun B hB => all_congr' fun p hp => ?_
  rw [ap_tabP' hg (hbl B hB p hp)]

theorem compEq_eq (T b u : Table) : compEq n T b u = tblEq n (compT n T b) (compT n u T) := by
  rw [compEq, tblEq, Bool.eq_iff_iff, allIn_eq_true, allIn_eq_true]
  refine forall_congr' fun i => forall_congr' fun _ => forall_congr' fun hi => ?_
  rw [ap_compT hi, ap_compT hi]

theorem beq_comm_conj {T b u : Nat} (hT : PP n w T) (hb : PP n w b) (hu : PP n w u) :
    Nat.beq (pc n w T b) (pc n w u T) = Nat.beq (pcj n w T (pinv n w T) b) u := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, Nat.beq_eq, PP_eq_iff (hT.pc hb) (hu.pc hT),
    PP_eq_iff (PP_pcj hT hT.pinv hb) hu]
  simp only [pcj, pc, pinv]
  rw [sg_pcomp (hT.mul hb) hT.inv, sg_pcomp hT hb, sg_pcomp hu hT, sg_pinv hT]
  exact mul_inv_eq_iff_eq_mul.symm

theorem normAll_tabP (hsz : szOK n w = true) {bs : List Nat} (hb : ∀ b ∈ bs, PP n w b) {T : Nat}
    (hT : PP n w T) : normAll n (bs.map (tabP n w)) (tabP n w T) = pnormAll n w bs T (pinv n w T) := by
  rw [normAll, pnormAll]
  simp only
  rw [spanTabs_tabP hsz hb]
  refine all_map_congr fun b hbb => any_map_congr fun u hu => ?_
  have hu' := PP_pspan hsz hb u hu
  rw [compEq_eq, compT_tabP' hT (hb b hbb), compT_tabP' hu' hT,
    tblEq_tabP (hT.pc (hb b hbb)) (hu'.pc hT), beq_comm_conj hT (hb b hbb) hu']

theorem getD_map_tabP (hsz : szOK n w = true) (rs : List Nat) (m : Nat) :
    (rs.map (tabP n w)).getD m (idT n) = tabP n w (rs.getD m (pidn n w)) := by
  rw [idT_tabP hsz, List.getD_map]

theorem PP_getD (hsz : szOK n w = true) {rs : List Nat} (hr : ∀ r ∈ rs, PP n w r) (m : Nat) :
    PP n w (rs.getD m (pidn n w)) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : rs[m]? with
  | none => exact PP.id hsz
  | some r => exact hr r (List.mem_of_getElem? h)

theorem cosetOK_tabP (hsz : szOK n w = true) {b : Nat} (hb : PP n w b) {bs rs : List Nat}
    (hbs : ∀ c ∈ bs, PP n w c) (hrs : ∀ r ∈ rs, PP n w r) :
    cosetOK n (tabP n w b) (bs.map (tabP n w)) (rs.map (tabP n w)) = pcosetOK n w b bs rs := by
  rw [cosetOK, pcosetOK, List.length_map, List.length_map]
  congr 1
  refine all_congr' fun m _ => ?_
  have hr := PP_getD hsz hrs m
  rw [getD_map_tabP hsz, invOK_tabP hr, Bool.true_and, invT_tabP hr, conjTab_tabP hr hr.pinv hb,
    maskProd_tabP hsz bs hbs, tblEq_tabP (PP_pcj hr hr.pinv hb) (PP_pmask hsz bs hbs _)]

theorem countProducts_tabP {f : Table → Bool} {fk : Nat → Bool}
    (hf : ∀ X, PP n w X → f (tabP n w X) = fk X) :
    ∀ (Ls : List (List Nat)), (∀ L ∈ Ls, ∀ t ∈ L, PP n w t) → ∀ g, PP n w g →
      countProducts n f (Ls.map (List.map (tabP n w))) (tabP n w g) = pcountProducts n w fk Ls g
  | [], _, g, hg => by rw [List.map_nil, countProducts, pcountProducts, hf g hg]
  | L :: Ls, h, g, hg => by
    have hLs : ∀ L ∈ Ls, ∀ t ∈ L, PP n w t := fun L' hL' => h L' (List.mem_cons_of_mem _ hL')
    rw [List.map_cons, countProducts, pcountProducts, List.foldl_map]
    refine foldl_congr' 0 fun t ht c => ?_
    have htp := h L List.mem_cons_self t ht
    rw [compT_tabP' hg htp, countProducts_tabP hf Ls hLs _ (hg.pc htp)]

theorem PP_pfilterProducts (hsz : szOK n w = true) {fk : Nat → Bool} :
    ∀ (Ls : List (List Nat)), (∀ L ∈ Ls, ∀ t ∈ L, PP n w t) → ∀ g acc, PP n w g →
      (∀ x ∈ acc, PP n w x) → ∀ x ∈ pfilterProducts n w fk Ls g acc, PP n w x
  | [], _, g, acc, hg, hacc, x, hx => by
    unfold pfilterProducts at hx
    split at hx
    · rcases List.mem_cons.1 hx with rfl | h
      · exact hg
      · exact hacc x h
    · exact hacc x hx
  | L :: Ls, h, g, acc, hg, hacc, x, hx => by
    have hLs : ∀ L ∈ Ls, ∀ t ∈ L, PP n w t := fun L' hL' => h L' (List.mem_cons_of_mem _ hL')
    unfold pfilterProducts at hx
    suffices ∀ (l : List Nat), (∀ t ∈ l, PP n w t) → ∀ a, (∀ y ∈ a, PP n w y) →
        ∀ y ∈ l.foldl (fun acc t => pfilterProducts n w fk Ls (pc n w g t) acc) a, PP n w y from
      this L (h L List.mem_cons_self) acc hacc x hx
    intro l
    induction l with
    | nil => intro _ a ha y hy; exact ha y hy
    | cons t l ih =>
      intro hl a ha y hy
      rw [List.foldl_cons] at hy
      exact ih (fun s hs => hl s (List.mem_cons_of_mem _ hs)) _
        (PP_pfilterProducts hsz Ls hLs _ a (hg.pc (hl t List.mem_cons_self)) ha) y hy

theorem filterProducts_tabP {f : Table → Bool} {fk : Nat → Bool}
    (hf : ∀ X, PP n w X → f (tabP n w X) = fk X) :
    ∀ (Ls : List (List Nat)), (∀ L ∈ Ls, ∀ t ∈ L, PP n w t) → ∀ g acc, PP n w g →
      filterProducts n f (Ls.map (List.map (tabP n w))) (tabP n w g) (acc.map (tabP n w)) =
        (pfilterProducts n w fk Ls g acc).map (tabP n w)
  | [], _, g, acc, hg => by
    rw [List.map_nil, filterProducts, pfilterProducts, hf g hg]
    split <;> rfl
  | L :: Ls, h, g, acc, hg => by
    have hLs : ∀ L ∈ Ls, ∀ t ∈ L, PP n w t := fun L' hL' => h L' (List.mem_cons_of_mem _ hL')
    rw [List.map_cons, filterProducts, pfilterProducts, List.foldl_map]
    suffices ∀ (l : List Nat), (∀ t ∈ l, PP n w t) → ∀ a,
        l.foldl (fun acc t => filterProducts n f (Ls.map (List.map (tabP n w)))
          (compT n (tabP n w g) (tabP n w t)) acc) (a.map (tabP n w)) =
        (l.foldl (fun acc t => pfilterProducts n w fk Ls (pc n w g t) acc) a).map (tabP n w) from
      this L (h L List.mem_cons_self) acc
    intro l
    induction l with
    | nil => intro _ a; rfl
    | cons t l ih =>
      intro hl a
      have htp := hl t List.mem_cons_self
      rw [List.foldl_cons, List.foldl_cons, compT_tabP' hg htp,
        filterProducts_tabP hf Ls hLs _ a (hg.pc htp)]
      exact ih (fun s hs => hl s (List.mem_cons_of_mem _ hs)) _

section Chain

open CFSG.KS.SporSch.MOC CFSG.Certificates

variable {gens : List (Equiv.Perm (Fin n))} {words : List (List Int)} {k : Nat}
  {bv : Vector (Fin n) k} {PS PSI LR TR TRI : Nat → Nat} {kS BP NS CH : Nat}

theorem levelTables_eq (hQ : ChainK n w gens words bv PS PSI LR TR TRI kS BP NS CH) (hn : 1 ≤ n)
    (hbs : bv.toList.Nodup) :
    levelTables (certificate hn gens words bv hbs) = (trPL n w LR TR k).map (List.map (tabP n w)) := by
  rw [levelTables, trPL, List.map_map, List.map_map]
  apply List.ext_getElem (by simp [certificate])
  intro i h1 h2
  have hi : i < k := by simpa using h2
  simp only [List.getElem_map, List.getElem_finRange, List.getElem_range, Function.comp_apply]
  erw [levelTransversals_eq hQ hn hbs hi]
  rw [List.map_map, List.map_map]
  refine List.map_congr_left fun a ha => ?_
  simp only [Function.comp_apply]
  exact CFSG.KS.SporSch.CodesImg.toTable_eq_arrTable_of_img
    (imageList_of_prep ((chainK_agree hQ hi).2 a (List.mem_range.1 ha)).1)

end Chain

end CFSG.KC.KGC31P

end
