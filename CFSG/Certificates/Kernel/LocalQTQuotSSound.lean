module

public import Certificates.Data.Kernel.LocalQT.QuotS
public import CFSG.Certificates.Kernel.LocalQTBaseSProved
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatQuot
import Std.Data.HashMap.Lemmas
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoKernel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Alt
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Native
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKCover
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKQuot
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Five
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.Quasithin.Background.A1cModuleCoprime
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.Background.OrderingMax
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Sporadic.Schreier.J4SSylow
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.Walter.Defs
public import Certificates.Certificate8026Base

public section

namespace CFSG.KC.LQT.QS

open CFSG.KC.Ord CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.PW CFSG.KC.LQT.BC
open CFSG.KC.LQT.PP CFSG.KC.LQT.BW CFSG.KC.LQT.BT CFSG.KC.LQT.BS
open CFSG.KC.LQT.BW.Pf CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.KC.LQT.RW.Pf CFSG.KC.LQT.RB.Pf CFSG.KC.LQT.BS.Pf
open CFSG.KC.LQT.P (letB impB allL anyL orB_iff andB_iff notB_iff impB_iff beq_iff blt_iff letB_eq)

theorem getK_getD {α : Type} : ∀ (l : List α) (i : Nat) (d : α),
    CFSG.KC.LQT.Syl.getK l i d = l.getD i d
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | _ :: t, i + 1, d => getK_getD t i d

theorem img_wordTabA {tabs : Array (Array Nat)} {n : Nat} {v : List Nat} {i : Nat} (hi : i < n) :
    img (wordTabA tabs n v) i = CFSG.QuasithinUnique.Ch1.SporLat.wordImg tabs v i := by
  simp [img, wordTabA, Array.getD_eq_getD_getElem?, hi]

theorem rep_wordTabA {n w : Nat} (hw : n ≤ 2 ^ w) (tabs : Array (Array Nat)) (TC : List Nat)
    (v : List Nat) (hv : ∀ l ∈ v, l < tabs.size ∧ Rep n w (TC.getD l 0) tabs[l]!) :
    Rep n w (wordC n w TC v) (wordTabA tabs n v) := by
  have key : ∀ i < n, CFSG.QuasithinUnique.Ch1.SporLat.wordImg tabs v i < n ∧
      imgW w (wordC n w TC v) i = CFSG.QuasithinUnique.Ch1.SporLat.wordImg tabs v i := by
    induction v with
    | nil =>
      intro i hi
      refine ⟨hi, ?_⟩
      change imgW w (oneW n w) i = i
      rw [oneW, imgW_ofFnW (fun j hj => by omega) hi]
    | cons a v ih =>
      intro i hi
      obtain ⟨ha, hra⟩ := hv a List.mem_cons_self
      obtain ⟨h1, h2⟩ := ih (fun l hl => hv l (List.mem_cons_of_mem _ hl)) i hi
      have e1 : CFSG.QuasithinUnique.Ch1.SporLat.wordImg tabs (a :: v) i =
          img tabs[a]! (CFSG.QuasithinUnique.Ch1.SporLat.wordImg tabs v i) := by
        simp only [CFSG.QuasithinUnique.Ch1.SporLat.wordImg, List.foldr_cons, img,
          Array.getD_eq_getD_getElem?, getElem!_pos tabs a ha, Array.getElem?_eq_getElem ha,
          Option.getD_some]
      have e2 : wordC n w TC (a :: v) = mulW n w (TC.getD a 0) (wordC n w TC v) := by
        change CFSG.KC.LQT.Syl.letN (wordC n w TC v)
          (fun c => mulW n w (CFSG.KC.LQT.Syl.getK TC a 0) c) = _
        rw [CFSG.KC.LQT.BS.Pf.letN_eq, getK_getD]
      rw [e1, e2, mulW, imgW_ofFnW (fun j _ => imgW_lt _ _ _) hi, h2]
      exact ⟨(hra.2 _ h1).1, (hra.2 _ h1).2⟩
  refine ⟨by simp [wordTabA], fun i hi => ?_⟩
  rw [img_wordTabA hi]
  exact key i hi

theorem genL_eq (n w : Nat) (LC : List Nat) : ∀ xs : List (List Nat × Nat × Nat),
    genL n w LC xs = xs.map (genC n w LC)
  | [] => rfl
  | x :: xs => by
    change letLs (genC n w LC x) (fun c => List.cons c (genL n w LC xs)) = _
    rw [letLs_eq, genL_eq n w LC xs, List.map_cons]

private noncomputable def gcQ (n w : Nat) (LC : List Nat) (x : QuotGen) : Nat :=
  genC n w LC (x.w, x.k, x.m)

theorem rep_oneW {n w : Nat} (hw : n ≤ 2 ^ w) : Rep n w (oneW n w) (idTab n) := by
  refine ⟨by simp [idTab], fun i hi => ?_⟩
  have e : img (idTab n) i = i := by
    simp [img, idTab, Array.getD_eq_getD_getElem?, hi]
  rw [e, oneW, imgW_ofFnW (fun j hj => by omega) hi]
  exact ⟨hi, rfl⟩

theorem rep_powC {n w c : Nat} {t : Array Nat} (hw : n ≤ 2 ^ w) (hc : Rep n w c t) :
    ∀ k, Rep n w (powC n w c k) (powTab n t k)
  | 0 => rep_oneW hw
  | k + 1 => by
    have e : powC n w c (k + 1) = mulW n w c (powC n w c k) := by
      change CFSG.KC.LQT.Syl.letN (powC n w c k) _ = _
      rw [letN_eq]
    rw [e]
    exact rep_mul hc (rep_powC hw hc k)

theorem itW_eq {n w g : Nat} {t : Array Nat} (hw : n ≤ 2 ^ w) (hg : Rep n w g t) {b : Nat}
    (hb : b < n) : ∀ m, itW w g m b = img (powTab n t m) b ∧ img (powTab n t m) b < n
  | 0 => by
    have e : img (idTab n) b = b := by
      simp [img, idTab, Array.getD_eq_getD_getElem?, hb]
    exact ⟨e.symm, by rw [powTab, e]; exact hb⟩
  | m + 1 => by
    obtain ⟨h1, h2⟩ := itW_eq hw hg hb m
    obtain ⟨-, hr⟩ := rep_powC hw hg m
    have hrp := rep_powC hw hg m
    have e : img (powTab n t (m + 1)) b = img t (img (powTab n t m) b) :=
      img_compArr hg.1 hrp.1 (fun i hi => (hrp.2 i hi).1) hb
    have e2 : itW w g (m + 1) b = imgW w g (itW w g m b) := rfl
    rw [e2, e, h1, (hg.2 _ h2).2]
    exact ⟨rfl, (hg.2 _ h2).1⟩

theorem applyTab_comp {n w c d : Nat} {s t : Array Nat} (hc : Rep n w c s) (hd : Rep n w d t)
    {T : List Nat} (hT : ∀ x ∈ T, x < n) :
    applyTab (compArr s t) T = applyTab s (applyTab t T) := by
  rw [applyTab, applyTab, applyTab, List.map_map]
  exact List.map_congr_left fun x hx =>
    img_compArr hc.1 hd.1 (fun i hi => (hd.2 i hi).1) (hT x hx)

theorem applyTab_idTab {n : Nat} {T : List Nat} (hT : ∀ x ∈ T, x < n) : applyTab (idTab n) T = T := by
  rw [applyTab]
  conv_rhs => rw [← List.map_id T]
  exact List.map_congr_left fun x hx => by
    simp [img, idTab, Array.getD_eq_getD_getElem?, hT x hx]

theorem zip_map_same {α β γ : Type} (f : α → β) (g : α → γ) :
    ∀ xs : List α, (xs.map f).zip (xs.map g) = xs.map fun x => (f x, g x)
  | [] => rfl
  | x :: xs => by simp [zip_map_same f g xs]

theorem entQ_spec {w nb r M lg g : Nat} {app : Nat → List Nat → List Nat} {E PG : Nat → Nat}
    {oC j : Nat} (h : entQ w nb r M lg g app E PG oC j = true) :
    (j + 1 < M → keyC w nb (E j) < keyC w nb (E (j + 1))) ∧
    (∀ t < g, memS w nb M lg E (codeK w (app t (decW w r (E j)))) = true) ∧
    (E j = oC ∨ (Nat.land (PG j) 131071 < M ∧ Nat.land (Nat.shiftRight (PG j) 17) 7 < g ∧
      Nat.shiftRight (PG (Nat.land (PG j) 131071)) 20 < Nat.shiftRight (PG j) 20 ∧
      E j = codeK w (app (Nat.land (Nat.shiftRight (PG j) 17) 7)
        (decW w r (E (Nat.land (PG j) 131071)))))) := by
  rw [entQ] at h
  dsimp only at h
  simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h4⟩ := h
  refine ⟨fun hj => P.blt_iff.1 (impB_true h1 (P.blt_iff.2 hj)), fun t ht => ?_, ?_⟩
  · rw [rangeK_eq', allL_eq, List.all_eq_true] at h2
    exact h2 t (List.mem_range.2 ht)
  · rw [orB_eq, Bool.or_eq_true, P.beq_iff, letB_eq, letB_eq] at h4
    rcases h4 with h4 | h4
    · exact Or.inl h4
    · simp only [Bool.and_eq_true, P.blt_iff, P.beq_iff] at h4
      exact Or.inr h4

theorem quotS_sound {n w : Nat} (hw : n ≤ 2 ^ w) (B : List Nat) (L : List (Array Nat))
    (LC : List Nat) (hLC : LC.length = L.length)
    (hL : ∀ i < L.length, Rep n w (LC.getD i 0) L[i]!)
    (xs : List QuotGen) (RS : Nat) (RT : Nat → Nat) (M lg fuel : Nat) (E PG : Nat → Nat)
    (K2 L2 r : Nat) (hr : 0 < r)
    (h : quotSK n w B LC (xs.map fun x => (x.w, x.k, x.m)) RS RT M lg fuel E PG K2 L2 r = true)
    (hs : ∀ c < K2, setQ w B xs.length RS RT M lg E PG (c * L2) L2 = true) :
    QuotOK n B L xs
      (bfsEnumB n B (xs.map (quotGt n L)) (xs.map (quotGi n L)) fuel).1
      (bfsEnumB n B (xs.map (quotGt n L)) (xs.map (quotGi n L)) fuel).2.1
      (bfsEnumB n B (xs.map (quotGt n L)) (xs.map (quotGi n L)) fuel).2.2 r := by
  rw [quotSK] at h
  dsimp only at h
  simp only [allBs_cons, allBs_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨hB, hxs, hitw, hRS, hrows, hMr, hMlg, hMf, hK2, hmo⟩ := h
  have hGcE : genL n w LC (xs.map fun x => (x.w, x.k, x.m)) = xs.map (gcQ n w LC) := by
    rw [genL_eq, List.map_map]
    rfl
  rw [hGcE] at hitw hrows hmo
  have hMr' : M = r := P.beq_iff.1 hMr
  have hM : 0 < M := by omega
  rw [allL_eq, List.all_eq_true] at hB
  have hB' : ∀ b ∈ B, b < n := fun b hb => P.blt_iff.1 (hB b hb)
  rw [List.all_eq_true] at hxs
  have hxs2 : ∀ x ∈ xs, (∀ l ∈ x.w, l < L.length) ∧ x.m % 2 = 1 := by
    intro x hx
    have := hxs (x.w, x.k, x.m) (List.mem_map.2 ⟨x, hx, rfl⟩)
    rw [andB_eq, Bool.and_eq_true, allL_eq, List.all_eq_true, P.beq_iff] at this
    refine ⟨fun l hl => ?_, this.2⟩
    have := P.blt_iff.1 (this.1 l hl)
    rwa [lenA_eq, hLC] at this
  have hgen : ∀ x ∈ xs, Rep n w (gcQ n w LC x) (quotGt n L x) := by
    intro x hx
    have hv : ∀ l ∈ x.w, l < L.toArray.size ∧ Rep n w (LC.getD l 0) L.toArray[l]! := by
      intro l hl
      have hl' := (hxs2 x hx).1 l hl
      exact ⟨by simpa using hl', by simpa using hL l hl'⟩
    have := rep_powC hw (rep_wordTabA hw L.toArray LC x.w hv) x.k
    change Rep n w (CFSG.KC.LQT.Syl.letN (wordC n w LC x.w) fun c => powC n w c x.k) _
    rw [letN_eq]
    exact this
  set G := xs.map (quotGt n L) with hGdef
  set Gi := xs.map (quotGi n L) with hGidef
  have hGl : G.length = xs.length := by rw [hGdef, List.length_map]
  have hGil : Gi.length = xs.length := by rw [hGidef, List.length_map]
  have hGj : ∀ j (hj : j < xs.length), G[j]! = quotGt n L xs[j] := by
    intro j hj
    rw [getElem!_pos G j (by omega)]
    simp only [hGdef, List.getElem_map]
  have hGij : ∀ j (hj : j < xs.length), Gi[j]! = powTab n G[j]! (xs[j].m - 1) := by
    intro j hj
    rw [getElem!_pos Gi j (by omega), hGj j hj]
    simp only [hGidef, List.getElem_map]
    rfl
  have hgenG : ∀ j (hj : j < xs.length), Rep n w (gcQ n w LC xs[j]) G[j]! := by
    intro j hj
    rw [hGj j hj]
    exact hgen _ (List.getElem_mem hj)
  have hGlt : ∀ t < xs.length, ∀ l : List Nat, (∀ y ∈ l, y < n) →
      ∀ x ∈ applyTab G[t]! l, x < n := fun t ht l hl => applyTab_lt (hgenG t ht) hl
  have hitw' : ∀ x ∈ xs, ∀ b ∈ B, itW w (gcQ n w LC x) x.m b = b := by
    intro x hx b hb
    rw [List.all_eq_true] at hitw
    have hmem : (gcQ n w LC x, x.m) ∈ List.zip (xs.map (gcQ n w LC))
        (List.map (fun y => y.2.2) (xs.map fun x => (x.w, x.k, x.m))) := by
      rw [List.map_map, zip_map_same]
      exact List.mem_map.2 ⟨x, hx, rfl⟩
    have := hitw _ hmem
    rw [allL_eq, List.all_eq_true] at this
    exact P.beq_iff.1 (this b hb)
  have hpow : ∀ i < xs.length, ∀ b ∈ B, img (powTab n G[i]! xs[i]!.m) b = b := by
    intro i hi b hb
    rw [hGj i hi, getElem!_pos xs i hi]
    have h1 := hitw' xs[i] (List.getElem_mem hi) b hb
    rw [(itW_eq hw (hgen _ (List.getElem_mem hi)) (hB' b hb) _).1] at h1
    exact h1
  have hRS' : n ≤ 64 * RS := Nat.le_of_ble_eq_true hRS
  have hrowsT : ∀ t (ht : t < xs.length), ∀ k' < RS,
      RT (t * RS + k') = rowW w (gcQ n w LC xs[t]) k' := by
    intro t ht k' hk'
    have := rowsT_go (xs.map (gcQ n w LC)) 0 hrows t (by rw [List.length_map]; exact ht) k' hk'
    rwa [Nat.zero_add, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem ht, Option.map_some, Option.getD_some] at this
  have happ : ∀ t < xs.length, ∀ l : List Nat, (∀ y ∈ l, y < n) →
      imgsR w RS RT t l = applyTab G[t]! l := by
    intro t ht l hl
    exact imgsR_rep hRS' (hrowsT t ht) (hgenG t ht) hl
  have hpts : ptsR w RS RT B xs.length = ptsOf B G := by
    rw [ptsR, appK_eq, flatK_eq, rangeK_eq', ptsOf, List.flatMap_def]
    congr 2
    apply List.ext_getElem (by simp [hGl])
    intro t h1 h2
    simp only [List.getElem_map, List.getElem_range]
    have ht : t < xs.length := by simpa using h1
    rw [happ t ht B hB', getElem!_pos G t (by omega)]
    rfl
  simp only [lenA_eq, List.length_map] at hmo
  rw [hpts] at hmo
  have hent : ∀ j < M, entQ w B.length (ptsOf B G).length M lg xs.length (imgsR w RS RT) E PG
      (codeK w (ptsOf B G)) j = true := by
    intro j hj
    have hK2' := Nat.le_of_ble_eq_true hK2
    rw [Nat.mul_eq] at hK2'
    have hL0 : 0 < L2 := by
      rcases Nat.eq_zero_or_pos L2 with h0 | h0
      · rw [h0, Nat.mul_zero] at hK2'
        omega
      · exact h0
    have hc : j / L2 < K2 := by
      rw [Nat.div_lt_iff_lt_mul hL0]
      omega
    have := hs _ hc
    rw [setQ] at this
    dsimp only at this
    rw [hpts] at this
    have := allR_true this (j % L2) (Nat.mod_lt _ hL0)
    rw [Nat.div_add_mod'] at this
    have := impB_true this (P.blt_iff.2 hj)
    simpa only [lenA_eq] using this
  have hov : Val n (ptsOf B G).length (ptsOf B G) := by
    refine ⟨rfl, fun x hx => ?_⟩
    rw [ptsOf, List.mem_append, List.mem_flatMap] at hx
    rcases hx with hx | ⟨s, hs, hx⟩
    · exact hB' x hx
    · obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hs
      have ht' : t < xs.length := by rw [← hGl]; exact ht
      have e := getElem!_pos G t ht
      rw [← e] at hx
      exact hGlt t ht' B hB' x hx
  have hlt2 : ∀ {l : List Nat}, (∀ x ∈ l, x < n) → ∀ x ∈ l, x < 2 ^ w :=
    fun hl x hx => Nat.lt_of_lt_of_le (hl x hx) hw
  have hval : ∀ d, ∀ j < M, Nat.shiftRight (PG j) 20 = d →
      Val n (ptsOf B G).length (decW w (ptsOf B G).length (E j)) ∧
        E j = codeK w (decW w (ptsOf B G).length (E j)) := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro j hj hd
      rcases (entQ_spec (hent j hj)).2.2 with h4 | ⟨hp, ht, hdep, he⟩
      · rw [h4, decW_codeK' (hlt2 hov.2) rfl]
        exact ⟨hov, rfl⟩
      · obtain ⟨hv, -⟩ := ih _ (hd ▸ hdep) _ hp rfl
        rw [he, happ _ ht _ hv.2]
        have hV : Val n (ptsOf B G).length (applyTab G[Nat.land (Nat.shiftRight (PG j) 17) 7]!
            (decW w (ptsOf B G).length (E (Nat.land (PG j) 131071)))) :=
          ⟨by rw [applyTab, List.length_map]; exact hv.1, hGlt _ ht _ hv.2⟩
        rw [decW_codeK' (hlt2 hV.2) hV.1]
        exact ⟨hV, rfl⟩
  have hU : ∀ j < M, Val n (ptsOf B G).length (decW w (ptsOf B G).length (E j)) ∧
      E j = codeK w (decW w (ptsOf B G).length (E j)) := fun j hj => hval _ j hj rfl
  have hstrict : ∀ a b, a < b → b < M → keyC w B.length (E a) < keyC w B.length (E b) := by
    intro a b hab hb
    induction b with
    | zero => omega
    | succ b ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h | rfl
      · exact Nat.lt_trans (ih h (by omega)) ((entQ_spec (hent b (by omega))).1 hb)
      · exact (entQ_spec (hent a (by omega))).1 hb
  have hkeyU : ∀ a < M, ∀ b < M, keyNat n B.length (decW w (ptsOf B G).length (E a)) =
      keyNat n B.length (decW w (ptsOf B G).length (E b)) → a = b := by
    intro a ha b hb e
    rw [keyNat_eq_iff (hU a ha).1 (hU b hb).1] at e
    have e2 : keyC w B.length (E a) = keyC w B.length (E b) := by
      rw [(hU a ha).2, (hU b hb).2, keyC_codeK (hlt2 (hU a ha).1.2),
        keyC_codeK (hlt2 (hU b hb).1.2), e]
    rcases Nat.lt_trichotomy a b with h | h | h
    · exact absurd e2 (Nat.ne_of_lt (hstrict a b h hb))
    · exact h
    · exact absurd e2.symm (Nat.ne_of_lt (hstrict b a h ha))
  set Ul := (List.range M).map fun j => decW w (ptsOf B G).length (E j) with hUldef
  have hUl : ∀ {T'}, T' ∈ Ul ↔ ∃ j < M, decW w (ptsOf B G).length (E j) = T' := by
    intro T'
    rw [hUldef, List.mem_map]
    simp only [List.mem_range]
  have hUlv : ∀ T' ∈ Ul, Val n (ptsOf B G).length T' := by
    intro T' hT'
    obtain ⟨j, hj, rfl⟩ := hUl.1 hT'
    exact (hU j hj).1
  have hkey : ∀ T' ∈ Ul, ∀ V ∈ Ul, keyNat n B.length T' = keyNat n B.length V → T' = V := by
    intro T' hT' V hV e
    obtain ⟨a, ha, rfl⟩ := hUl.1 hT'
    obtain ⟨b, hb, rfl⟩ := hUl.1 hV
    rw [hkeyU a ha b hb e]
  have hUlnd : Ul.Nodup :=
    List.Nodup.map_on (fun a ha b hb e => hkeyU a (List.mem_range.1 ha) b (List.mem_range.1 hb)
      (by rw [e])) List.nodup_range
  have hUllen : Ul.length = M := by rw [hUldef, List.length_map, List.length_range]
  have hprod : ∀ j < M, ∀ t < xs.length,
      applyTab G[t]! (decW w (ptsOf B G).length (E j)) ∈ Ul := by
    intro j hj t ht
    obtain ⟨j', hj', e⟩ := memS_spec hM ((entQ_spec (hent j hj)).2.1 t ht)
    rw [happ t ht _ (hU j hj).1.2] at e
    have hV : Val n (ptsOf B G).length (applyTab G[t]! (decW w (ptsOf B G).length (E j))) :=
      ⟨by rw [applyTab, List.length_map]; exact (hU j hj).1.1, hGlt t ht _ (hU j hj).1.2⟩
    refine hUl.2 ⟨j', hj', ?_⟩
    rw [e, decW_codeK' (hlt2 hV.2) hV.1]
  have hclo : ∀ T' ∈ Ul, ∀ s ∈ G, applyTab s T' ∈ Ul := by
    intro T' hT' s hs
    obtain ⟨j, hj, rfl⟩ := hUl.1 hT'
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hs
    have ht' : t < xs.length := by omega
    rw [← getElem!_pos G t ht]
    exact hprod j hj t ht'
  have hoU : ptsOf B G ∈ Ul := by
    obtain ⟨j, hj, e⟩ := memS_spec hM hmo
    refine hUl.2 ⟨j, hj, ?_⟩
    rw [e, decW_codeK' (hlt2 hov.2) rfl]
  have hS0 : BInv n B.length G Ul (ptsOf B G) (#[ptsOf B G], #[0],
      (∅ : Std.HashMap Nat Nat).insert (keyNat n B.length (ptsOf B G)) 0) := by
    have hget : ∀ i < 1, (#[ptsOf B G] : Array (List Nat))[i]! = ptsOf B G := by
      intro i hi
      have hi0 : i = 0 := by omega
      subst hi0
      rfl
    refine ⟨rfl, by simp, rfl, fun T' hT' => ?_, fun y => ?_, fun i hi => ?_, fun i hi hi0 => ?_⟩
    · simp only [List.mem_singleton] at hT'
      rw [hT']
      exact hoU
    · simp only [Std.HashMap.contains_insert, Std.HashMap.contains_empty, Bool.or_false,
        beq_iff_eq]
      constructor
      · rintro rfl
        exact ⟨0, by simp, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        have hi0 : i = 0 := by simpa using hi
        subst hi0
        rfl
    · have hi' : i < 1 := by simpa using hi
      rw [hget i hi']
      simp only [Std.HashMap.getD_insert, beq_self_eq_true, ite_true]
      omega
    · have hi' : i < 1 := by simpa using hi
      omega
  have hMf' := Nat.le_of_ble_eq_true hMf
  obtain ⟨hcf, hdone⟩ := loop_done hclo fuel 0 _ hS0 (Nat.zero_le _)
    (fun _ h => absurd h (Nat.not_lt_zero _)) (by rw [hUllen]; omega)
  generalize hSf : bfsLoopB n B.length G fuel 0 (#[ptsOf B G], #[0],
    (∅ : Std.HashMap Nat Nat).insert (keyNat n B.length (ptsOf B G)) 0) = S at hcf hdone
  have hbe : bfsEnumB n B G Gi fuel = (S.1, S.2.1, (List.range S.1.size).foldl (fun acc i =>
      (G ++ Gi).foldl (fun acc' s =>
        acc'.push (S.2.2.getD (keyNat n B.length (applyTab s S.1[i]!)) 0)) acc) #[]) := by
    simp only [bfsEnumB, hSf]
  obtain ⟨hps, hpos, h0, hSU, hmc, hmgS, hpar⟩ := hcf
  have hv : ∀ T' ∈ S.1.toList, Val n (ptsOf B G).length T' := fun T' hT' => hUlv T' (hSU T' hT')
  have hfind : ∀ i < S.1.size, ∀ t < xs.length, ∃ k' < S.1.size,
      S.1[k']! = applyTab G[t]! S.1[i]! := by
    intro i hi t ht
    have hs : G[t]! ∈ G := by rw [getElem!_pos G t (by omega)]; exact List.getElem_mem _
    obtain ⟨k', hk', e⟩ := (hmc _).1 (hdone i hi _ hs)
    refine ⟨k', hk', hkey _ (hSU _ (get_mem hk')) _ (hclo _ (hSU _ (get_mem hi)) _ hs) e⟩
  have hreach : ∀ d, ∀ j < M, Nat.shiftRight (PG j) 20 = d →
      decW w (ptsOf B G).length (E j) ∈ S.1.toList := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro j hj hd
      rcases (entQ_spec (hent j hj)).2.2 with h4 | ⟨hp, ht, hdep, he⟩
      · rw [h4, decW_codeK' (hlt2 hov.2) rfl, ← h0]
        exact get_mem hpos
      · obtain ⟨i', hi', e⟩ := mem_idx (ih _ (hd ▸ hdep) _ hp rfl)
        obtain ⟨k', hk', e'⟩ := hfind i' hi' _ ht
        have hpU := hU _ hp
        rw [he, happ _ ht _ hpU.1.2, ← e]
        have hV : Val n (ptsOf B G).length (applyTab G[Nat.land (Nat.shiftRight (PG j) 17) 7]!
            S.1[i']!) := by
          rw [e]
          exact ⟨by rw [applyTab, List.length_map]; exact hpU.1.1, hGlt _ ht _ hpU.1.2⟩
        rw [decW_codeK' (hlt2 hV.2) hV.1, ← e']
        exact get_mem hk'
  have hsize : S.1.size = M := by
    apply Nat.le_antisymm
    · have := ((toList_nodup ⟨hps, hpos, h0, hSU, hmc, hmgS, hpar⟩).subperm hSU).length_le
      simp only [Array.length_toList] at this
      omega
    · have := (hUlnd.subperm fun T' hT' => by
        obtain ⟨j, hj, rfl⟩ := hUl.1 hT'
        exact hreach _ j hj rfl).length_le
      simp only [Array.length_toList] at this
      omega
  rw [hbe]
  dsimp only
  have hclget : ∀ i < S.1.size, ∀ j < (G ++ Gi).length,
      ((List.range S.1.size).foldl (fun acc i => (G ++ Gi).foldl (fun acc' s =>
        acc'.push (S.2.2.getD (keyNat n B.length (applyTab s S.1[i]!)) 0)) acc)
        (#[] : Array Nat))[i * (G.length + Gi.length) + j]! =
      S.2.2.getD (keyNat n B.length (applyTab (G ++ Gi)[j]! S.1[i]!)) 0 := by
    intro i hi j hj
    rw [arr_getN, cl_fold, ← List.length_append]
    exact (flatMap_getD (G ++ Gi) _ S.1.size).2 i hi j hj
  have hidx : ∀ i < S.1.size, ∀ {s : Array Nat} {k' : Nat}, k' < S.1.size →
      S.1[k']! = applyTab s S.1[i]! →
      S.2.2.getD (keyNat n B.length (applyTab s S.1[i]!)) 0 = k' := by
    intro i _ s k' hk' e
    rw [← e]
    exact hmgS k' hk'
  have hiter : ∀ j (hj : j < xs.length), ∀ k, ∀ i < S.1.size, ∃ k' < S.1.size,
      S.1[k']! = applyTab (powTab n G[j]! k) S.1[i]! := by
    intro j hj k
    induction k with
    | zero =>
      intro i hi
      exact ⟨i, hi, (applyTab_idTab (hv _ (get_mem hi)).2).symm⟩
    | succ k ih =>
      intro i hi
      obtain ⟨k', hk', e⟩ := ih i hi
      obtain ⟨k'', hk'', e'⟩ := hfind k' hk' j hj
      refine ⟨k'', hk'', ?_⟩
      rw [e', e]
      exact (applyTab_comp (hgenG j hj) (rep_powC hw (hgenG j hj) k)
        (hv _ (get_mem hi)).2).symm
  unfold QuotOK QuotOK'
  refine ⟨hxs2, hpow, ?_, by rw [hsize]; exact hMr'⟩
  unfold BaseEnumOK
  refine ⟨hpos, h0, hps, hpar, keys_nodupB ⟨hps, hpos, h0, hSU, hmc, hmgS, hpar⟩,
    fun i hi j hj => ?_, fun i hi j hj => ?_⟩
  · have hjq : j < xs.length := hGl ▸ hj
    obtain ⟨k', hk', e⟩ := hfind i hi j hjq
    rw [hclget i hi j (by simp; omega), getBang_append_left hj, hidx i hi hk' e]
    exact ⟨hk', e⟩
  · have hjq : j < xs.length := hGil ▸ hj
    obtain ⟨k', hk', e⟩ := hiter j hjq (xs[j].m - 1) i hi
    rw [← hGij j hjq] at e
    rw [Nat.add_assoc, hclget i hi _ (by simp; omega), getBang_append_right hj,
      hidx i hi hk' e]
    exact ⟨hk', e⟩

end CFSG.KC.LQT.QS

end
