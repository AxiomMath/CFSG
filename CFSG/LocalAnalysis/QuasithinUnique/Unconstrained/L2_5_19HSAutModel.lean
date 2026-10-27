module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19HSAutNodesCheck

public section

namespace CFSG.QuasithinUnique.Id2519.HSAut

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.RankThreeCoreUniqueness.Helpers CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier
open scoped commutatorElement

theorem nodes_parts
    : chkSizes = true ∧ chkEnum = true ∧ chkConj = true ∧ chkScan = true ∧
    chkR1 = true := by
  have h := nodesCheck_eq
  simpa only [nodesCheck, Bool.and_eq_true, and_assoc] using h

theorem letter_size : ∀ l < 3, (UHS.letterArr l).size = 3850 := by
  have h := nodes_parts.1
  simp only [chkSizes, Bool.and_eq_true, beq_iff_eq, allBelow_eq_true, and_assoc] at h
  exact h.1

theorem tabRep_letter
    {l : ℕ} (hl : l < 3) : TabRep (UHS.letterArr l) (UHS.letterPerm l) :=
  ⟨letter_size l hl, (UHS.rep_letter l).1⟩

theorem tabRep_wordTab :
    ∀ {ls : List ℕ}, (∀ l ∈ ls, l < 3) →
    TabRep (wordTab ls) (UHS.wElt ls)
  | [], _ => by
    simpa [wordTab, UHS.wElt] using
      (TabRep.idTab : TabRep (idTab 3850) (1 : Equiv.Perm (Fin 3850)))
  | l :: ls, h => by
    have h1 := tabRep_letter (h l List.mem_cons_self)
    have h2 := tabRep_wordTab (fun l' hl' => h l' (List.mem_cons_of_mem l hl'))
    simpa [wordTab, UHS.wElt] using h1.comp h2

@[expose] noncomputable def y₁ : Equiv.Perm (Fin 3850) := UHS.wElt UHS.y1Letters

@[expose] noncomputable def y₂ : Equiv.Perm (Fin 3850) := UHS.wElt UHS.y2Letters

theorem y1Letters_lt : ∀ l ∈ UHS.y1Letters, l < 3 := by decide

theorem y2Letters_lt : ∀ l ∈ UHS.y2Letters, l < 3 := by decide

theorem cLetters_lt : ∀ l ∈ UHS.cLetters, l < 3 := by decide

theorem gLetters_lt : ∀ l ∈ gLetters, l < 3 := by decide

theorem tabRep_y1 :
    TabRep y1Tab y₁ := tabRep_wordTab y1Letters_lt

theorem tabRep_y2 :
    TabRep y2Tab y₂ := tabRep_wordTab y2Letters_lt

theorem tabRep_c :
    TabRep cTab UHS.hsC := by
  have := tabRep_wordTab cLetters_lt
  rwa [UHS.wElt_cLetters] at this

theorem tabRep_a0 :
    TabRep a0Tab (hsGen 0) := by
  have := tabRep_letter (l := 0) (by norm_num)
  simpa [a0Tab, UHS.letterPerm] using this

@[expose] noncomputable def gPerm : Equiv.Perm (Fin 3850) := UHS.wElt gLetters

@[expose] noncomputable def ePerm : Equiv.Perm (Fin 3850) := y₁ * y₁ * y₂ * y₁ * y₁ * y₂

theorem tabRep_e :
    TabRep eTab ePerm := by
  have h1 := tabRep_y1
  have h2 := tabRep_y2
  have := h1.comp (h1.comp (h2.comp (h1.comp (h1.comp (h2.comp (TabRep.idTab :
    TabRep (idTab 3850) (1 : Equiv.Perm (Fin 3850))))))))
  simpa [eTab, eLetters, ePerm, mul_assoc] using this

theorem tabRep_g :
    TabRep gTab gPerm := tabRep_wordTab gLetters_lt

theorem gPerm_mem : gPerm ∈ hsP := by
  rw [hsP_eq_original]
  exact UHS.wElt_mem _

theorem exists_a0Row :
    ∃ r ∈ hsRows, r.rep = hsCentTbl 5 ∧ r.centGens = [hsCentTbl 6, hsCentTbl 7] := by
  refine ⟨hsRows[0]'(by decide), List.getElem_mem _, ?_, ?_⟩ <;>
    simp only [hsRows, List.getElem_cons_zero]

@[expose] noncomputable def a0Row : ClassRow := Classical.choose exists_a0Row

theorem a0Row_mem : a0Row ∈ hsRows := (Classical.choose_spec exists_a0Row).1

theorem a0Row_rep : a0Row.rep = hsCentTbl 5 := (Classical.choose_spec exists_a0Row).2.1

theorem a0Row_centGens : a0Row.centGens = [hsCentTbl 6, hsCentTbl 7] :=
  (Classical.choose_spec exists_a0Row).2.2

theorem a0Row_C
    : CFSG.Sporadic.SmallOddCore.hsC a0Row =
    hsP ⊓ Subgroup.centralizer ({hsGen 0} : Set (Equiv.Perm (Fin 3850))) := by
  have h := (hs_involution_centralizers.2.2.2.1 a0Row a0Row_mem).2.2.2.1
  rw [h, a0Row_rep, hs_tp_rep_a]

theorem sizes_parts : (∀ l < 3, (UHS.letterArr l).size = 3850) ∧
    (∀ l < 2, (hsCentTbl (6 + l)).size = 3850 ∧
      CFSG.Sporadic.SmallOddCore.permOK 3850 (hsCentTbl (6 + l)) = true) ∧
    CFSG.Sporadic.SmallOddCore.permOK 3850 hsOuterTbl = true ∧
    CFSG.Sporadic.SmallOddCore.permOK 3850 r1T = true ∧ r1T.size = 3850 := by
  have h := nodes_parts.1
  simp only [chkSizes, Bool.and_eq_true, beq_iff_eq, allBelow_eq_true, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, fun l hl => ?_, h3, h4, h5⟩
  have := h2 l hl
  exact ⟨this.2, this.1⟩

theorem enumerates_A0 :
    Enumerates (CFSG.Sporadic.SmallOddCore.hsC a0Row) enumA0.tabs.toList := by
  have hs := sizes_parts.2.1
  have hs0 : (hsCentTbl 6).size = 3850 ∧
      CFSG.Sporadic.SmallOddCore.permOK 3850 (hsCentTbl 6) = true :=
    hs 0 (by norm_num)
  have hs1 : (hsCentTbl 7).size = 3850 ∧
      CFSG.Sporadic.SmallOddCore.permOK 3850 (hsCentTbl 7) = true :=
    hs 1 (by norm_num)
  have hgen0 : TabRep (CFSG.Sporadic.SmallOddCore.Native.natArr (hsCentTbl 6))
      (tp 3850 (hsCentTbl 6)) := tabRep_natArr hs0.1 hs0.2
  have hgen1 : TabRep (CFSG.Sporadic.SmallOddCore.Native.natArr (hsCentTbl 7))
      (tp 3850 (hsCentTbl 7)) := tabRep_natArr hs1.1 hs1.2
  have hg0 : gensA0[0]! = CFSG.Sporadic.SmallOddCore.Native.natArr (hsCentTbl 6) := by
    simp [gensA0]
  have hg1 : gensA0[1]! = CFSG.Sporadic.SmallOddCore.Native.natArr (hsCentTbl 7) := by
    simp [gensA0]
  have hsize : gensA0.size = 2 := by simp [gensA0]
  have hEnum : enumOK 3850 gensA0 enumA0 = true := by
    have h := nodes_parts.2.1
    simp only [chkEnum, Bool.and_eq_true] at h
    exact h.1
  show Enumerates (Subgroup.closure (tp 3850 '' {x | x ∈ a0Row.centGens.toArray})) _
  refine enumerates_closure (gens := gensA0) ?_ ?_ hEnum
  · rintro a ⟨T, hT, rfl⟩
    have hT1 : T ∈ a0Row.centGens.toArray := hT
    have hT2 : T ∈ a0Row.centGens := List.mem_toArray.1 hT1
    rw [a0Row_centGens] at hT2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hT2
    rcases hT2 with h | h
    · rw [h]
      exact ⟨0, by rw [hsize]; norm_num, hg0 ▸ hgen0⟩
    · rw [h]
      exact ⟨1, by rw [hsize]; norm_num, hg1 ▸ hgen1⟩
  · intro j hj
    have hj' : j < 2 := by rw [hsize] at hj; exact hj
    interval_cases j
    · refine ⟨tp 3850 (hsCentTbl 6), ⟨hsCentTbl 6, ?_, rfl⟩, hg0 ▸ hgen0⟩
      show hsCentTbl 6 ∈ a0Row.centGens.toArray
      rw [List.mem_toArray, a0Row_centGens]
      simp
    · refine ⟨tp 3850 (hsCentTbl 7), ⟨hsCentTbl 7, ?_, rfl⟩, hg1 ▸ hgen1⟩
      show hsCentTbl 7 ∈ a0Row.centGens.toArray
      rw [List.mem_toArray, a0Row_centGens]
      simp

theorem centralizer_nodes
    {x : Equiv.Perm (Fin 3850)} (hx : x ∈ hsP) (h1 : x * y₁ = y₁ * x)
    (h2 : x * y₂ = y₂ * x) : x = 1 ∨ x = UHS.hsC := by
  have hconj := nodes_parts.2.2.1
  have hscan := nodes_parts.2.2.2.1
  simp only [chkConj, Bool.and_eq_true, beq_iff_eq, and_assoc] at hconj
  obtain ⟨hga, hgisz, hgi⟩ := hconj
  have hg := tabRep_g
  have hgi' : TabRep giTab gPerm⁻¹ := hg.inv hgisz hgi
  have he := tabRep_e
  have hga' : gPerm * hsGen 0 = ePerm * gPerm :=
    ((hg.comp tabRep_a0).eq_iff (he.comp hg)).1 hga
  have hxe : x * ePerm = ePerm * x := by
    have c1 : Commute x y₁ := h1
    have c2 : Commute x y₂ := h2
    exact (((((c1.mul_right c1).mul_right c2).mul_right c1).mul_right c1).mul_right c2).eq
  have he' : ePerm = gPerm * hsGen 0 * gPerm⁻¹ := by rw [hga']; group
  set x' := gPerm⁻¹ * x * gPerm with hx'
  have hx'P : x' ∈ hsP := hsP.mul_mem (hsP.mul_mem (hsP.inv_mem gPerm_mem) hx) gPerm_mem
  have hx'a : x' * hsGen 0 = hsGen 0 * x' := by
    have h3 : x * (gPerm * hsGen 0 * gPerm⁻¹) = (gPerm * hsGen 0 * gPerm⁻¹) * x := by
      rw [← he']; exact hxe
    calc x' * hsGen 0 = gPerm⁻¹ * (x * (gPerm * hsGen 0 * gPerm⁻¹)) * gPerm := by
          simp only [hx']; group
      _ = gPerm⁻¹ * ((gPerm * hsGen 0 * gPerm⁻¹) * x) * gPerm := by rw [h3]
      _ = hsGen 0 * x' := by simp only [hx']; group
  have hmem : x' ∈ CFSG.Sporadic.SmallOddCore.hsC a0Row := by
    rw [a0Row_C]
    exact ⟨hx'P, Subgroup.mem_centralizer_singleton_iff.2 hx'a⟩
  obtain ⟨k, hk, hkrep⟩ := enumerates_A0.exists_pos hmem
  have hrow : scanRow k = true := (allBelow_eq_true.1 hscan) k hk
  have hxk : TabRep (scanTab k) x := by
    have := hg.conjTab hkrep hgi'
    have e : gPerm * x' * gPerm⁻¹ = x := by simp only [hx']; group
    rw [e] at this
    exact this
  have hA : (comp 3850 (scanTab k) y1Tab == comp 3850 y1Tab (scanTab k)) = true :=
    ((hxk.comp tabRep_y1).beq_iff (tabRep_y1.comp hxk)).2 h1
  have hB : (comp 3850 (scanTab k) y2Tab == comp 3850 y2Tab (scanTab k)) = true :=
    ((hxk.comp tabRep_y2).beq_iff (tabRep_y2.comp hxk)).2 h2
  unfold scanRow at hrow
  rw [hA, hB] at hrow
  simp only [Bool.and_self, Bool.not_true, Bool.false_or, Bool.or_eq_true] at hrow
  rcases hrow with hC | hD
  · exact Or.inl ((hxk.beq_iff TabRep.idTab).1 hC)
  · exact Or.inr ((hxk.beq_iff tabRep_c).1 hD)

theorem exists_outer_r1
    : ∃ r ∈ hsR, r ∉ hsP ∧ r * r = 1 ∧ r * y₁ = y₁ * r ∧ r * y₂ = y₂ * r := by
  obtain ⟨-, -, hperm, hr1perm, hr1sz⟩ := sizes_parts
  have hR1 := nodes_parts.2.2.2.2
  simp only [chkR1, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', and_assoc] at hR1
  obtain ⟨hsq, hc1, hc2, hns, hs⟩ := hR1
  have hrep : CFSG.Sporadic.Th.Rep 3850 r1T (tp 3850 r1T) := rep_tp hr1perm
  have hr : TabRep r1Tab (tp 3850 r1T) := tabRep_natArr hr1sz hr1perm
  refine ⟨tp 3850 r1T, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨hU2, -, -, hmap, -⟩ := hs_normalizing_model
    have hUn : ∀ p ∈ hsP, hsU * p * hsU⁻¹ ∈ hsP := fun p hp => by
      rw [← hmap]
      exact ⟨p, hp, rfl⟩
    have huRep : CFSG.Sporadic.Th.Rep 3850 hsOuterTbl hsU := rep_tp hperm
    exact mem_R_of_sift hs_groupData hU2 hUn huRep hrep (by rw [hs]; simp)
  · intro hrP
    have := (hs_groupData.sift r1T _ hrep).2 hrP
    rw [hns] at this
    exact Bool.noConfusion this
  · exact ((hr.comp hr).eq_iff TabRep.idTab).1 hsq
  · exact ((hr.comp tabRep_y1).eq_iff (tabRep_y1.comp hr)).1 hc1
  · exact ((hr.comp tabRep_y2).eq_iff (tabRep_y2.comp hr)).1 hc2

open CFSG.QuasithinUnique.Id2519.UHS in
theorem kb_eq_nodes
    (K : Subgroup PP) (hK : Nat.card K = 360) (hKc : ∀ k ∈ K, k * sC = sC * k)
    (hnorm : ∀ c : PP, c * sC = sC * c → ∀ k ∈ K, c * k * c⁻¹ ∈ K) :
    yElt0 ∈ K ∧ yElt1 ∈ K ∧
      ∀ x : PP, x ∈ K ↔ ∃ k < 360, (x : Equiv.Perm (Fin 3850)) = nodeElt k := by
  obtain ⟨ho1, ho2, hc1, hc2, hinj, hconj⟩ := a6_facts
  set Cs : Subgroup PP := Subgroup.centralizer ({sC} : Set PP) with hCsdef
  have hCs : Nat.card Cs = 2880 := card_centralizer_c
  have hKle : K ≤ Cs := fun k hk => Subgroup.mem_centralizer_singleton_iff.2 (hKc k hk)
  have hCle : Cs ≤ Subgroup.normalizer (K : Set PP) := fun c hc => by
    have hcc : c * sC = sC * c := Subgroup.mem_centralizer_singleton_iff.1 hc
    have hcc' : c⁻¹ * sC = sC * c⁻¹ := by
      calc c⁻¹ * sC = c⁻¹ * (sC * c) * c⁻¹ := by group
        _ = c⁻¹ * (c * sC) * c⁻¹ := by rw [hcc]
        _ = sC * c⁻¹ := by group
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hnorm c hcc h hh, fun hh => ?_⟩
    have := hnorm c⁻¹ hcc' _ hh
    simpa [mul_assoc] using this
  have hN : (K.subgroupOf Cs).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKle]
    exact hCle
  have hidx : (K.subgroupOf Cs).index = 8 := by
    have h1 := Subgroup.card_mul_index (K.subgroupOf Cs)
    have h2 : Nat.card (K.subgroupOf Cs) = Nat.card K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKle).toEquiv
    rw [h2, hK, hCs] at h1
    omega
  have hpow : ∀ g ∈ Cs, g ^ 8 ∈ K := fun g hg => by
    have := Subgroup.pow_index_mem (K.subgroupOf Cs) (⟨g, hg⟩ : Cs)
    rw [hidx, Subgroup.mem_subgroupOf] at this
    simpa using this
  have hy : ∀ y : PP, y * sC = sC * y → y ^ 16 = y → y ∈ K := by
    intro y hcomm h16
    have hmem : y ∈ Cs := Subgroup.mem_centralizer_singleton_iff.2 hcomm
    rw [← h16]
    have : y ^ 16 = (y ^ 8) ^ 2 := by rw [← pow_mul]
    rw [this]
    exact K.pow_mem (hpow _ hmem) 2
  have hy0 : yElt0 ∈ K := by
    refine hy _ (Subtype.ext hc1) ?_
    refine Subtype.ext ?_
    have h3 : wElt y1Letters ^ 3 = 1 := by
      have := pow_orderOf_eq_one (wElt y1Letters)
      rwa [ho1] at this
    simp only [yElt0, Subgroup.coe_pow]
    calc wElt y1Letters ^ 16 = (wElt y1Letters ^ 3) ^ 5 * wElt y1Letters := by
          rw [← pow_mul, ← pow_succ]
      _ = wElt y1Letters := by rw [h3]; simp
  have hy1 : yElt1 ∈ K := by
    refine hy _ (Subtype.ext hc2) ?_
    refine Subtype.ext ?_
    have h5 : wElt y2Letters ^ 5 = 1 := by
      have := pow_orderOf_eq_one (wElt y2Letters)
      rwa [ho2] at this
    simp only [yElt1, Subgroup.coe_pow]
    calc wElt y2Letters ^ 16 = (wElt y2Letters ^ 5) ^ 3 * wElt y2Letters := by
          rw [← pow_mul, ← pow_succ]
      _ = wElt y2Letters := by rw [h5]; simp
  set f : Fin 360 → PP := fun k => ⟨nodeElt k, wElt_mem _⟩ with hf
  have hfinj : Function.Injective f := by
    intro k k' h
    exact Fin.ext (hinj k k.2 k' k'.2 (congrArg Subtype.val h))
  have hfK : ∀ k, f k ∈ K := fun k => nodeElt_mem hy0 hy1 360 k
  have hSsub : Set.range f ⊆ (K : Set PP) := by
    rintro _ ⟨k, rfl⟩
    exact hfK k
  have hSncard : (Set.range f).ncard = 360 := by
    rw [← Nat.card_coe_set_eq, Nat.card_range_of_injective hfinj, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have hKncard : (K : Set PP).ncard = 360 := by
    rw [← Nat.card_coe_set_eq]
    exact hK
  have hSeq : Set.range f = (K : Set PP) :=
    Set.eq_of_subset_of_ncard_le hSsub (by rw [hSncard, hKncard])
  refine ⟨hy0, hy1, fun x => ?_⟩
  rw [← SetLike.mem_coe, ← hSeq]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, k.2, by rw [← hk]⟩
  · rintro ⟨k, hk, hx⟩
    exact ⟨⟨k, hk⟩, Subtype.ext hx.symm⟩

theorem commute_nodes
    {r : Equiv.Perm (Fin 3850)} (h1 : r * y₁ = y₁ * r) (h2 : r * y₂ = y₂ * r)
    (i : ℕ) : r * UHS.nodeElt i = UHS.nodeElt i * r := by
  let Kc : Subgroup UHS.PP := (Subgroup.centralizer ({r} : Set (Equiv.Perm (Fin 3850)))).subgroupOf
    UHS.PP
  have hy0 : UHS.yElt0 ∈ Kc :=
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_centralizer_singleton_iff.2 h1.symm)
  have hy1 : UHS.yElt1 ∈ Kc :=
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_centralizer_singleton_iff.2 h2.symm)
  have := UHS.nodeElt_mem hy0 hy1 360 i
  have h3 := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_subgroupOf.1 this)
  exact h3.symm

theorem normalize
    {Kb : Subgroup (Equiv.Perm (Fin 3850))} (hKP : Kb ≤ hsP)
    (hKcard : Nat.card Kb = 360) {h : Equiv.Perm (Fin 3850)} (hhP : h ∈ hsP) (hh2 : h * h = 1)
    (hh1 : h ≠ 1) (hKc : ∀ k ∈ Kb, k * h = h * k)
    (hKn : ∀ c ∈ hsP, c * h = h * c → ∀ k ∈ Kb, c * k * c⁻¹ ∈ Kb) :
    ∃ g ∈ hsP, h = g * UHS.hsC * g⁻¹ ∧ g * y₁ * g⁻¹ ∈ Kb ∧ g * y₂ * g⁻¹ ∈ Kb ∧
      ∀ k : Equiv.Perm (Fin 3850), k ∈ Kb ↔ ∃ i < 360, k = g * UHS.nodeElt i * g⁻¹ := by
  have hPP : ∀ x : Equiv.Perm (Fin 3850), x ∈ hsP ↔ x ∈ UHS.PP := fun x => by
    rw [hsP_eq_original]
  have hKPP : Kb ≤ UHS.PP := fun k hk => (hPP k).1 (hKP hk)
  set Kb' : Subgroup UHS.PP := Kb.subgroupOf UHS.PP with hKb'
  have hmemKb' : ∀ k : UHS.PP, k ∈ Kb' ↔ (k : Equiv.Perm (Fin 3850)) ∈ Kb := fun k =>
    Subgroup.mem_subgroupOf
  have hKb'card : Nat.card Kb' = 360 := by
    rw [← hKcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKPP).toEquiv
  have hhPP : h ∈ UHS.PP := (hPP h).1 hhP
  set s : UHS.PP := ⟨h, hhPP⟩ with hs
  have hord : orderOf h = 2 := orderOf_eq_prime (by rw [sq]; exact hh2) hh1
  have hKb'c : ∀ k ∈ Kb', k * s = s * k := fun k hk => Subtype.ext (hKc k ((hmemKb' k).1 hk))
  have hKb'n : ∀ c : UHS.PP, c * s = s * c → ∀ k ∈ Kb', c * k * c⁻¹ ∈ Kb' := by
    intro c hc k hk
    have hc' : (c : Equiv.Perm (Fin 3850)) * h = h * c := congrArg Subtype.val hc
    have := hKn c ((hPP c).2 c.2) hc' k ((hmemKb' k).1 hk)
    exact (hmemKb' _).2 (by simpa using this)
  have hconjc : ∃ d ∈ UHS.PP, h = d * UHS.hsC * d⁻¹ := by
    rcases UHS.hs_invol_cover hhPP hord with h' | h'
    · exfalso
      obtain ⟨c, hc, hce⟩ := UHS.hsE1_conj _ h'
      have hconj : IsConj (⟨hsGen 0, hsGen_mem 0 (by norm_num)⟩ : UHS.PP) s :=
        isConj_iff.2 ⟨⟨c, hc⟩, Subtype.ext hce.symm⟩
      have h1 := UHS.card_centralizer_of_isConj hconj
      rw [UHS.card_centralizer_a0] at h1
      have hKle : Kb' ≤ Subgroup.centralizer ({s} : Set UHS.PP) := fun k hk =>
        Subgroup.mem_centralizer_singleton_iff.2 (hKb'c k hk)
      have h2 := Subgroup.card_dvd_of_le hKle
      rw [hKb'card, ← h1] at h2
      norm_num at h2
    · exact UHS.hsE2_conj _ h'
  obtain ⟨g, hgPP, hgc⟩ := hconjc
  set c' : UHS.PP := ⟨g, hgPP⟩ with hc'
  have hs_eq : s = c' * UHS.sC * c'⁻¹ := Subtype.ext hgc
  let K' : Subgroup UHS.PP := Kb'.map (MulAut.conj c'⁻¹).toMonoidHom
  have hK' : Nat.card K' = 360 := by
    rw [← hKb'card]
    exact Subgroup.card_map_of_injective (MulAut.conj c'⁻¹).injective
  have hmemK' : ∀ k, k ∈ K' ↔ c' * k * c'⁻¹ ∈ Kb' := by
    intro k
    constructor
    · rintro ⟨k₀, hk₀, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hk₀
    · intro hk
      exact ⟨c' * k * c'⁻¹, hk, by simp [mul_assoc]⟩
  have hKc' : ∀ k ∈ K', k * UHS.sC = UHS.sC * k := by
    intro k hk
    have h1 := hKb'c _ ((hmemK' k).1 hk)
    rw [hs_eq] at h1
    calc k * UHS.sC = c'⁻¹ * ((c' * k * c'⁻¹) * (c' * UHS.sC * c'⁻¹)) * c' := by group
      _ = c'⁻¹ * ((c' * UHS.sC * c'⁻¹) * (c' * k * c'⁻¹)) * c' := by rw [h1]
      _ = UHS.sC * k := by group
  have hnorm' : ∀ x : UHS.PP, x * UHS.sC = UHS.sC * x → ∀ k ∈ K', x * k * x⁻¹ ∈ K' := by
    intro x hx k hk
    rw [hmemK']
    have hy : (c' * x * c'⁻¹) * s = s * (c' * x * c'⁻¹) := by
      rw [hs_eq]
      calc c' * x * c'⁻¹ * (c' * UHS.sC * c'⁻¹) = c' * (x * UHS.sC) * c'⁻¹ := by group
        _ = c' * (UHS.sC * x) * c'⁻¹ := by rw [hx]
        _ = c' * UHS.sC * c'⁻¹ * (c' * x * c'⁻¹) := by group
    have := hKb'n _ hy _ ((hmemK' k).1 hk)
    have e : c' * (x * k * x⁻¹) * c'⁻¹ =
        c' * x * c'⁻¹ * (c' * k * c'⁻¹) * (c' * x * c'⁻¹)⁻¹ := by group
    rw [e]
    exact this
  obtain ⟨hy0, hy1, hnodes⟩ := kb_eq_nodes K' hK' hKc' hnorm'
  refine ⟨g, (hPP g).2 hgPP, hgc, ?_, ?_, ?_⟩
  · exact (hmemKb' _).1 ((hmemK' _).1 hy0)
  · exact (hmemKb' _).1 ((hmemK' _).1 hy1)
  · intro k
    constructor
    · intro hk
      have hkPP : k ∈ UHS.PP := hKPP hk
      have hkK' : c'⁻¹ * ⟨k, hkPP⟩ * c' ∈ K' := by
        rw [hmemK']
        have : c' * (c'⁻¹ * ⟨k, hkPP⟩ * c') * c'⁻¹ = ⟨k, hkPP⟩ := by group
        rw [this]
        exact (hmemKb' _).2 hk
      obtain ⟨i, hi, hik⟩ := (hnodes _).1 hkK'
      refine ⟨i, hi, ?_⟩
      have h3 : g⁻¹ * k * g = UHS.nodeElt i := by simpa using hik
      calc k = g * (g⁻¹ * k * g) * g⁻¹ := by group
        _ = g * UHS.nodeElt i * g⁻¹ := by rw [h3]
    · rintro ⟨i, hi, rfl⟩
      have hnode : (⟨UHS.nodeElt i, UHS.wElt_mem _⟩ : UHS.PP) ∈ K' := (hnodes _).2 ⟨i, hi, rfl⟩
      exact (hmemKb' _).1 ((hmemK' _).1 hnode)

theorem hs_outer_simple
    {Kb : Subgroup (Equiv.Perm (Fin 3850))} (hKP : Kb ≤ hsP)
    (hKcard : Nat.card Kb = 360) {r : Equiv.Perm (Fin 3850)} (hrR : r ∈ hsR) (hrP : r ∉ hsP)
    (hr2 : r * r = 1) (hKr : ∀ k ∈ Kb, r * k = k * r) :
    IsSimpleGroup ↥(perfectResidualOf
        (hsP ⊓ Subgroup.centralizer ({r} : Set (Equiv.Perm (Fin 3850))))) ∧
      Nat.card ↥(perfectResidualOf
        (hsP ⊓ Subgroup.centralizer ({r} : Set (Equiv.Perm (Fin 3850))))) = 20160 := by
  have hr1 : r ≠ 1 := fun h => hrP (h ▸ hsP.one_mem)
  have hord : orderOf r = 2 := orderOf_eq_prime (by rw [sq]; exact hr2) hr1
  obtain ⟨-, -, -, hrows, hcover, -, -, -⟩ := hs_involution_centralizers
  obtain ⟨row, hrow, g, hg, hrg⟩ := hcover r hrR hord
  obtain ⟨-, -, hout, -, hcent, -⟩ := hrows row hrow
  have hrepP : tp 3850 row.rep ∉ hsP := by
    intro hP
    apply hrP
    rw [hrg]
    exact hsP.mul_mem (hsP.mul_mem hg hP) (hsP.inv_mem hg)
  have houter : row.outer = true := hout.2 hrepP
  have hcard : Nat.card ↥(hsP ⊓ Subgroup.centralizer ({r} : Set (Equiv.Perm (Fin 3850)))) =
      row.centOrder := by
    rw [hrg, inf_centralizer_conj hsP hg, Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hcent
  have hdvd : 360 ∣ row.centOrder := by
    rw [← hcard, ← hKcard]
    apply Subgroup.card_dvd_of_le
    intro k hk
    exact ⟨hKP hk, Subgroup.mem_centralizer_singleton_iff.2 (hKr k hk).symm⟩
  have hrow2 : row.rep = hsCentTbl 21 := by
    simp only [hsRows, List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with rfl | rfl | rfl | rfl
    · exact absurd houter (by decide)
    · exact absurd houter (by decide)
    · dsimp only
    · exact absurd hdvd (by decide)
  have hrg' : r = g * outerU * g⁻¹ := by
    rw [hrg, hrow2]
    rfl
  have hC : hsP ⊓ Subgroup.centralizer ({r} : Set (Equiv.Perm (Fin 3850))) =
      outerC.map (MulAut.conj g).toMonoidHom := by
    rw [hrg', inf_centralizer_conj hsP hg]
    rfl
  rw [hC, perfectResidualOf_map_equiv (MulAut.conj g), perfectResidualOf_outerC]
  have e : ↥outerE ≃* ↥(outerE.map (MulAut.conj g).toMonoidHom) :=
    Subgroup.equivMapOfInjective _ _ (MulAut.conj g).injective
  exact ⟨(MulEquiv.isSimpleGroup_congr e).1 outerE_simple, by
    rw [← Nat.card_congr e.toEquiv]
    exact card_outerE⟩

theorem hs_model
    {Kb : Subgroup (Equiv.Perm (Fin 3850))} (hKP : Kb ≤ hsP)
    (hKcard : Nat.card Kb = 360) {h : Equiv.Perm (Fin 3850)} (hhP : h ∈ hsP) (hh2 : h * h = 1)
    (hh1 : h ≠ 1) (hKc : ∀ k ∈ Kb, k * h = h * k)
    (hKn : ∀ c ∈ hsP, c * h = h * c → ∀ k ∈ Kb, c * k * c⁻¹ ∈ Kb) :
    (∀ x ∈ hsP, (∀ k ∈ Kb, x * k = k * x) → x = 1 ∨ x = h) ∧
      ∃ r ∈ hsR, r ∉ hsP ∧ r * r = 1 ∧ ∀ k ∈ Kb, r * k = k * r := by
  obtain ⟨g, hgP, hhg, hy1, hy2, hnodes⟩ := normalize hKP hKcard hhP hh2 hh1 hKc hKn
  constructor
  · intro x hx hxK
    have hx' : g⁻¹ * x * g ∈ hsP := hsP.mul_mem (hsP.mul_mem (hsP.inv_mem hgP) hx) hgP
    have h1 : (g⁻¹ * x * g) * y₁ = y₁ * (g⁻¹ * x * g) := by
      have h3 := hxK _ hy1
      calc g⁻¹ * x * g * y₁ = g⁻¹ * (x * (g * y₁ * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * y₁ * g⁻¹) * x) * g := by rw [h3]
        _ = y₁ * (g⁻¹ * x * g) := by group
    have h2 : (g⁻¹ * x * g) * y₂ = y₂ * (g⁻¹ * x * g) := by
      have h3 := hxK _ hy2
      calc g⁻¹ * x * g * y₂ = g⁻¹ * (x * (g * y₂ * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * y₂ * g⁻¹) * x) * g := by rw [h3]
        _ = y₂ * (g⁻¹ * x * g) := by group
    rcases centralizer_nodes hx' h1 h2 with h' | h'
    · left
      calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        _ = 1 := by rw [h']; group
    · right
      calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        _ = h := by rw [h', hhg]
  · obtain ⟨r, hrR, hrP, hr2, hr1, hr2'⟩ := exists_outer_r1
    have hgR : g ∈ hsR := le_sup_left (a := hsP) (b := Subgroup.zpowers hsU) hgP
    refine ⟨g * r * g⁻¹, hsR.mul_mem (hsR.mul_mem hgR hrR) (hsR.inv_mem hgR), ?_, ?_, ?_⟩
    · intro hP
      apply hrP
      have := hsP.mul_mem (hsP.mul_mem (hsP.inv_mem hgP) hP) hgP
      simpa [mul_assoc] using this
    · calc g * r * g⁻¹ * (g * r * g⁻¹) = g * (r * r) * g⁻¹ := by group
        _ = 1 := by rw [hr2]; group
    · intro k hk
      obtain ⟨i, hi, rfl⟩ := (hnodes k).1 hk
      have hcn := commute_nodes hr1 hr2' i
      calc g * r * g⁻¹ * (g * UHS.nodeElt i * g⁻¹) = g * (r * UHS.nodeElt i) * g⁻¹ := by group
        _ = g * (UHS.nodeElt i * r) * g⁻¹ := by rw [hcn]
        _ = g * UHS.nodeElt i * g⁻¹ * (g * r * g⁻¹) := by group

end CFSG.QuasithinUnique.Id2519.HSAut
