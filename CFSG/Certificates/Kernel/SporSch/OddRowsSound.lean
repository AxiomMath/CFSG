module

public import Certificates.Data.Kernel.SporSch.OddRows
public import CFSG.Certificates.Kernel.SporSch.ChainKClassEq
public import CFSG.Certificates.Kernel.SporSch.CodesImg
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.SporSch.ChainKOdd

public section

namespace CFSG.KS.SporSch.OddRows

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.MEnum
open CFSG.KS.SporSch.MOC CFSG.KS.SporSch.MBT CFSG.KS.SporSch.CodesImg
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th
open CFSG.Sporadic.Th.Native CFSG.Monster.B.Mathieu CFSG.KS.SporSch.ClsSpec
open CFSG.Sporadic.SmallOddCore CFSG.OddStandard

variable {n w : Nat}

theorem reps_of_classesG (hn : n < 2 ^ 32) {gens gensInv : Array Table}
    {gg : ℕ → Equiv.Perm (Fin n)}
    (hg : ∀ l < gens.size, Rep n gens[l]! (gg l) ∧ Rep n gensInv[l]! (gg l)⁻¹) {cap : Nat}
    {reps : List (Equiv.Perm (Fin n))} {sz : Nat → Nat}
    (hcls : ∀ j (hj : j < reps.length),
      (CFSG.Sporadic.SmallOddCore.conjClass (genK gens gg) reps[j]).ncard = sz j ∧ sz j ≤ cap)
    (hdisj : ∀ i j (hi : i < reps.length) (hj : j < reps.length), i < j →
      reps[j] ∉ CFSG.Sporadic.SmallOddCore.conjClass (genK gens gg) reps[i])
    {X : List Table} (hX : X.length = ((List.range reps.length).map sz).sum) :
    repsOK n gens gensInv X (reps.map toTable) cap = true ∧
      repSizes n gens gensInv (reps.map toTable) cap = (List.range reps.length).map sz := by
  have hcap : ∀ j (hj : j < reps.length), (CFSG.Sporadic.SmallOddCore.conjClass (genK gens gg) reps[j]).ncard ≤ cap := by
    intro j hj
    rw [(hcls j hj).1]
    exact (hcls j hj).2
  have hspec := fun j (hj : j < reps.length) =>
    conjClosure_spec hg (rep_toTable hn reps[j]) (hcap j hj)
  have hsizes : (reps.map toTable).map (fun r => (conjClosure n gens gensInv r cap).1.size) =
      (List.range reps.length).map sz := by
    apply List.ext_getElem (by simp)
    intro j h1 h2
    have hj : j < reps.length := by simpa using h1
    simp only [List.getElem_map, List.getElem_range]
    rw [conjClosure_size hg (rep_toTable hn reps[j]) (hcap j hj), (hcls j hj).1]
  have hidx : ∀ r ∈ reps, ∃ j, ∃ hj : j < reps.length, reps[j] = r := fun r hr =>
    List.mem_iff_getElem.1 hr
  refine ⟨?_, hsizes⟩
  unfold repsOK
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro c hc
    simp only [List.map_map, List.mem_map, Function.comp_apply] at hc
    obtain ⟨r, hr, rfl⟩ := hc
    obtain ⟨j, hj, rfl⟩ := hidx r hr
    exact (hspec j hj).1
  · apply keysDistinct_of
    rw [List.map_flatMap, List.flatMap_map, List.flatMap_map, List.nodup_flatMap]
    refine ⟨fun r hr => ?_, List.pairwise_iff_getElem.2 fun i j hi hj hij => ?_⟩
    · obtain ⟨j, hj, rfl⟩ := hidx r hr
      exact (hspec j hj).2.1
    · intro a ha hb
      simp only [List.mem_map] at ha hb
      obtain ⟨t, ht, rfl⟩ := ha
      obtain ⟨t', ht', e⟩ := hb
      obtain ⟨z, hz, pz⟩ := (hspec i hi).2.2.1 t ht
      obtain ⟨z', hz', pz'⟩ := (hspec j hj).2.2.1 t' ht'
      have ezz := eq_of_key pz' pz e
      rw [ezz] at hz'
      exact hdisj i j hi hj hij (conjClass_trans (conjClass_symm hz') hz)
  · rw [hX, ← hsizes, List.map_map]
    rfl

variable {cg : List (Equiv.Perm (Fin n))} {words : List (List Int)} {k : Nat}
  {bv : Vector (Fin n) k} {PS PSI LR TR TRI : Nat → Nat} {kS BP NS CH : Nat}

theorem strictB_id (y : Nat) (f : Nat → Bool) : strictB y f = f y := by
  cases y <;> rfl

theorem specK_facts {g cap : Nat} {sp : WordRowSpec}
    (h : specK n w PS PSI LR TR TRI BP k g cap sp = true) :
    lettersK g sp.repWord = true ∧ lettersK g sp.conjWord = true ∧ 0 < sp.prime ∧
      0 < sp.productOrder ∧ sp.classSize ≤ cap ∧
      sp.classSize * btK n w (mask w) (n * w) BP k LR TR TRI (wv n w PS PSI sp.repWord)
        (wv n w PS PSI sp.repWord) = ordK LR k ∧
      ordC n w (mask w) (wv n w PS PSI sp.repWord) = sp.prime ∧
      ordC n w (mask w) (pcomp n w (mask w) (wv n w PS PSI sp.repWord) (pcomp n w (mask w)
        (pcomp n w (mask w) (wv n w PS PSI sp.conjWord) (wv n w PS PSI sp.repWord))
        (pinvS n w (mask w) (wv n w PS PSI sp.conjWord)))) = sp.productOrder := by
  unfold specK at h
  rw [strictB_id, strictB_id] at h
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, Nat.eq_of_beq_eq_true h6, Nat.eq_of_beq_eq_true h7,
    Nat.eq_of_beq_eq_true h8⟩

variable (hQ : ChainK n w cg words bv PS PSI LR TR TRI kS BP NS CH) (hn : 1 ≤ n)
  (hbs : bv.toList.Nodup) (hk64 : k ≤ 64)
include hQ hn hbs hk64

theorem oddRowsCheck_of_rowsK {ps : List Nat} {specs : List WordRowSpec} {cap : Nat}
    (h : rowsK n w PS PSI LR TR TRI BP k cg.length ps specs cap = true) :
    oddRowsCheck n (certificate hn cg words bv hbs) cg ps specs cap = true := by
  set Q := certificate hn cg words bv hbs
  have hsz := chainK_szOK hQ
  have hf := szOK_facts hsz
  have hn32 : n < 2 ^ 32 := by omega
  have hwn : n < 2 ^ w := by omega
  have hw0 : 0 < w := PF.w_pos hf.2
  have hV : ValidSchreier Q := chainK_valid hQ hn hbs
  unfold rowsK at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hidK, hperm⟩, hps⟩, hspecs⟩, hdist⟩, hcnt⟩ := h
  have hidl : imageList (1 : Equiv.Perm (Fin n)) = (unpack n w (pidn n w)).toList := by
    rw [idK_sound hidK]
    apply List.ext_getElem <;> simp [imageList, CFSG.Monster.B.Co2.Native.idA]
  have hpm : ∀ j < cg.length, permOK n w (mask w) (n * w) (PS j) (PSI j) = true :=
    fun j hj => allN_spec hperm j hj
  have himg : ∀ {wd : List Int}, lettersK cg.length wd = true →
      PRep n w (wv n w PS PSI wd) (evalCodes cg wd) := fun hl =>
    prep_of_imageList (evalCodes_img hsz hQ.2.2.2.1 hpm hidl hl)
  have hK : Q.originalSubgroup = Subgroup.closure {g | g ∈ cg} :=
    certificate_originalSubgroup hn cg words bv hbs
  have hcgK : ∀ g ∈ cg, g ∈ Q.originalSubgroup := fun g hg => by
    rw [hK]
    exact Subgroup.subset_closure hg
  have hgen : genK (generatorTables cg) (fun l => cg.getD l 1) = Q.originalSubgroup := by
    rw [hK]
    unfold genK
    congr 1
    ext g
    simp only [generatorTables, List.size_toArray, List.length_map, Set.mem_setOf_eq]
    constructor
    · rintro ⟨l, hl, rfl⟩
      rw [List.getD_eq_getElem _ _ hl]
      exact List.getElem_mem hl
    · intro hg
      obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hg
      exact ⟨l, hl, List.getD_eq_getElem _ _ hl⟩
  have hgT := generatorTables_spec hn32 hcgK
  have hcard : Nat.card Q.originalSubgroup = ordK LR k := card_group hQ hn hbs
  set reps := specs.map fun sp => evalCodes cg sp.repWord
  have hlen : reps.length = specs.length := by simp [reps]
  have hrj : ∀ j (hj : j < reps.length), reps[j] =
      evalCodes cg (specs[j]'(hlen ▸ hj)).repWord := fun j hj => by simp [reps]
  have hspec : ∀ j (hj : j < specs.length), specK n w PS PSI LR TR TRI BP k cg.length cap
      specs[j] = true := fun j hj => hspecs _ (List.getElem_mem hj)
  have pR : ∀ j (hj : j < reps.length),
      PRep n w (wv n w PS PSI (specs[j]'(hlen ▸ hj)).repWord) reps[j] := fun j hj => by
    rw [hrj]
    exact himg (specK_facts (hspec j _)).1
  have hrepK : ∀ j (hj : j < reps.length), reps[j] ∈ Q.originalSubgroup := fun j hj => by
    rw [hrj]
    exact evalCodes_mem _ hcgK _
  have hbt : ∀ j (hj : j < reps.length), Nat.card ↥(Q.originalSubgroup ⊓
      Subgroup.centralizer ({reps[j]} : Set (Equiv.Perm (Fin n)))) =
        btK n w (mask w) (n * w) BP k LR TR TRI (wv n w PS PSI (specs[j]'(hlen ▸ hj)).repWord)
          (wv n w PS PSI (specs[j]'(hlen ▸ hj)).repWord) := fun j hj =>
    card_centralizer_eq hQ hn hbs hk64 (pR j hj)
  have hncard : ∀ j (hj : j < reps.length),
      (CFSG.Sporadic.SmallOddCore.conjClass Q.originalSubgroup reps[j]).ncard = (specs[j]'(hlen ▸ hj)).classSize := by
    intro j hj
    have h1 := CFSG.Sporadic.SmallOddCore.ncard_conjClass_mul_card Q.originalSubgroup reps[j]
    have h2 := (specK_facts (hspec j (hlen ▸ hj))).2.2.2.2.2.1
    rw [hbt j hj, hcard, ← h2] at h1
    have hpos : 0 < btK n w (mask w) (n * w) BP k LR TR TRI
        (wv n w PS PSI (specs[j]'(hlen ▸ hj)).repWord)
        (wv n w PS PSI (specs[j]'(hlen ▸ hj)).repWord) := by
      rw [← hbt j hj]
      exact Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos h1
  have hsz' : (List.range reps.length).map (fun j => (specs.getD j ⟨0, [], 0, [], 0⟩).classSize) =
      specs.map (·.classSize) := by
    apply List.ext_getElem (by simp [hlen])
    intro j h1 h2
    have hj : j < specs.length := by simpa using h2
    rw [List.getElem_map, List.getElem_map, List.getElem_range, List.getD_eq_getElem _ _ hj]
  have hdisj : ∀ i j (hi : i < reps.length) (hj : j < reps.length), i < j →
      reps[j] ∉ CFSG.Sporadic.SmallOddCore.conjClass (genK (generatorTables cg) (fun l => cg.getD l 1)) reps[i] := by
    intro i j hi hj hij hc
    rw [hgen] at hc
    obtain ⟨c, hc, hce⟩ := hc
    have h0 := Nat.eq_of_beq_eq_true (allN_spec (allN_spec hdist j (hlen ▸ hj)) i hij)
    rw [List.getD_eq_getElem _ _ (hlen ▸ hi), List.getD_eq_getElem _ _ (hlen ▸ hj),
      btK_eq hQ hn hbs hk64 (pR i hi) (pR j hj), List.countP_eq_zero] at h0
    refine h0 c ((mem_enumeration_iff Q hV c).2 hc) ?_
    rw [decide_eq_true_eq, hce]
    group
  have hcnt' : (orderInTables Q ps).length = (specs.map (·.classSize)).sum := by
    rw [Nat.eq_of_beq_eq_true hcnt, (forall₂_orderInTables hn32 Q fun p hp =>
      Nat.blt_eq.mp (hps p hp)).length_eq, List.length_reverse, ← List.countP_eq_length_filter,
      ← card_subtype_eq_countP Q.originalSubgroup (enumeration Q) (enumeration_nodup Q hV)
        (mem_enumeration_iff Q hV), card_subtype_eq_countP Q.originalSubgroup _
        (elemP_nodup hQ hn hbs) (mem_elemP_iff hQ hn hbs)
        (fun g => ∃ p ∈ ps, orderOf g = p), List.countP_map, cntIn]
    apply List.countP_congr
    intro j _
    rw [strictB_id, Function.comp_apply, ← orderOf_of_ordC (prep_elemK hQ j)]
    simp only [List.any_eq_true, Nat.beq_eq_true_eq, decide_eq_true_eq]
    constructor
    · rintro ⟨p, hp, e⟩
      exact ⟨p, hp, by rw [e]; exact Nat.beq_refl p⟩
    · rintro ⟨p, hp, e⟩
      exact ⟨p, hp, Nat.eq_of_beq_eq_true e⟩
  obtain ⟨hreps, hsizes⟩ := reps_of_classesG hn32 (gensInv := generatorTablesInv cg)
    (fun l hl => ⟨(hgT l hl).1, (hgT l hl).2.1⟩)
    (sz := fun j => (specs.getD j ⟨0, [], 0, [], 0⟩).classSize) (cap := cap) (reps := reps)
    (fun j hj => by
      rw [hgen, hncard j hj, List.getD_eq_getElem _ _ (hlen ▸ hj)]
      exact ⟨rfl, (specK_facts (hspec j (hlen ▸ hj))).2.2.2.2.1⟩)
    hdisj (X := orderInTables Q ps) (by rw [hcnt', hlen, ← hlen, hsz'])
  unfold oddRowsCheck
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨hreps, by rw [hsizes, hsz']⟩, fun sp hsp => ?_⟩, fun sp hsp => ?_⟩, fun sp hsp => ?_⟩
  · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hsp
    have hj' : j < reps.length := hlen ▸ hj
    rw [← card_centralizerIn_eq_commCountT hn32 Q hV, ← (hrj j hj'), centralizerIn,
      hbt j hj', (chainK_check hn hbs hQ).2]
    exact (specK_facts (hspec j hj)).2.2.2.2.2.1
  · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hsp
    have hj' : j < reps.length := hlen ▸ hj
    obtain ⟨-, -, hp, -, -, -, ho, -⟩ := specK_facts (hspec j hj)
    rw [ordTest_iff perm_faithful (rep_toTable hn32 _) hp, ← (hrj j hj'),
      orderOf_of_ordC (pR j hj'), ho]
  · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hsp
    obtain ⟨-, hlc, -, hq, -, -, -, hpo⟩ := specK_facts (hspec j hj)
    have pC := himg hlc
    have pRj := himg (specK_facts (hspec j hj)).1
    have pP := prep_pcomp hn32 pRj (prep_pcomp hn32 (prep_pcomp hn32 pC pRj)
      (prep_pinvS hwn pC).1)
    rw [ordTest_iff perm_faithful (rep_toTable hn32 _) hq, orderOf_of_ordC pP, hpo]

end CFSG.KS.SporSch.OddRows

end
