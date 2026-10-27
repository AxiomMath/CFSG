module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HNSideFacts.F4Inputs

public section

namespace CFSG.EvenSporadicStandard.HNRecog.SideF4

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native

private lemma class_parts (h : sideF4ClassOK = true) :
    (∀ m < 256, labTab[m]! < 4 ∧ plettersOK 10 toWords[m]! = true ∧
      plettersOK 10 fromWords[m]! = true ∧
      pathEval colPerms (pinvs 256 colPerms) toWords[m]! m = repTab[labTab[m]!]! ∧
      pathEval colPerms (pinvs 256 colPerms) fromWords[m]! repTab[labTab[m]!]! = m) ∧
    (∀ b < 16, (decide (256 % ((List.range 256).filter fun m => b.testBit labTab[m]!).length ≠ 0)
      || ((List.range 256).filter fun m => b.testBit labTab[m]!).length == 1
      || ((List.range 256).filter fun m => b.testBit labTab[m]!).length == 256) = true) := by
  unfold sideF4ClassOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, h6⟩, h7⟩ := h
  refine ⟨fun m hm => ?_, fun b hb => by simpa using allBelowN_spec h7 hb⟩
  have hm6 := allBelowN_spec h6 hm
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hm6
  exact ⟨hm6.1.1.1.1, hm6.1.1.1.2, hm6.1.1.2, hm6.1.2, hm6.2⟩

private lemma pathEval_mem (T : Finset ℕ)
    (hcl : ∀ l : ℤ, plettersOK 10 [l] = true → ∀ m ∈ T,
      (pletter colPerms (pinvs 256 colPerms) l)[m]! ∈ T) :
    ∀ w : List ℤ, plettersOK 10 w = true → ∀ m ∈ T,
      pathEval colPerms (pinvs 256 colPerms) w m ∈ T := by
  intro w
  induction w with
  | nil => intro _ m hm; simpa [pathEval] using hm
  | cons l w ih =>
      intro hw m hm
      simp only [plettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
        decide_eq_true_eq] at hw
      obtain ⟨⟨hl0, hlj⟩, hw'⟩ := hw
      have hwt : plettersOK 10 w = true := by
        simpa [plettersOK, List.all_eq_true] using hw'
      have hl : plettersOK 10 [l] = true := by
        have hp : (fun l : ℤ => l != 0 && decide (l.natAbs ≤ 10)) l = true := by
          rw [Bool.and_eq_true]
          exact ⟨by simpa using hl0, by simpa using hlj⟩
        simpa [plettersOK] using hp
      have hstep : pathEval colPerms (pinvs 256 colPerms) (l :: w) m =
          pathEval colPerms (pinvs 256 colPerms) w
            ((pletter colPerms (pinvs 256 colPerms) l)[m]!) := by
        simp [pathEval]
      rw [hstep]
      exact ih hwt _ (hcl l hl m hm)

private lemma exists_bitmask (L : Finset ℕ) (hL : ∀ l ∈ L, l < 4) :
    ∃ b < 16, ∀ l < 4, b.testBit l = true ↔ l ∈ L := by
  have key : ∀ S : Finset (Fin 4), ∃ b : Fin 16, ∀ i : Fin 4,
      (b : ℕ).testBit (i : ℕ) = true ↔ i ∈ S := by decide
  set S : Finset (Fin 4) := Finset.univ.filter (fun i : Fin 4 => (i : ℕ) ∈ L) with hS
  obtain ⟨b, hb⟩ := key S
  refine ⟨(b : ℕ), b.2, fun l hl => ?_⟩
  have hmem : (⟨l, hl⟩ : Fin 4) ∈ S ↔ l ∈ L := by
    rw [hS]
    simp
  have := hb ⟨l, hl⟩
  rw [hmem] at this
  simpa using this

theorem class_trichotomy (h : sideF4ClassOK = true) (T : Finset ℕ)
    (hT : ∀ m ∈ T, m < 256) (h0 : 0 ∈ T)
    (hcl : ∀ l : ℤ, plettersOK 10 [l] = true → ∀ m ∈ T,
      (pletter colPerms (pinvs 256 colPerms) l)[m]! ∈ T)
    (hdvd : T.card ∣ 256) : T = {0} ∨ T = Finset.range 256 := by
  obtain ⟨hfacts, hcheck⟩ := class_parts h
  have hclosed := pathEval_mem T hcl
  set L : Finset ℕ := T.image (fun m => labTab[m]!) with hLdef
  have hLlt : ∀ l ∈ L, l < 4 := by
    intro l hl
    rw [hLdef, Finset.mem_image] at hl
    obtain ⟨m, hmT, hm⟩ := hl
    rw [← hm]
    exact (hfacts m (hT m hmT)).1
  obtain ⟨b, hb16, hbit⟩ := exists_bitmask L hLlt
  have hcnt : ((List.range 256).filter fun m => b.testBit labTab[m]!).length = T.card := by
    have hnodup : ((List.range 256).filter fun m => b.testBit labTab[m]!).Nodup :=
      List.nodup_range.filter _
    have hset : ((List.range 256).filter fun m => b.testBit labTab[m]!).toFinset = T := by
      ext m
      rw [List.mem_toFinset, List.mem_filter, List.mem_range]
      constructor
      · rintro ⟨hm256, hbm⟩
        obtain ⟨hlt, hto, hfrom, htoPath, hfromPath⟩ := hfacts m hm256
        have hmL : labTab[m]! ∈ L := (hbit (labTab[m]!) hlt).1 hbm
        rw [hLdef, Finset.mem_image] at hmL
        obtain ⟨m', hm'T, hm'eq⟩ := hmL
        obtain ⟨-, hto', -, htoPath', -⟩ := hfacts m' (hT m' hm'T)
        have hrepT : repTab[labTab[m]!]! ∈ T := by
          have h1 : repTab[labTab[m']!]! ∈ T := by
            rw [← htoPath']
            exact hclosed (toWords[m']!) hto' m' hm'T
          rwa [hm'eq] at h1
        have h2 := hclosed (fromWords[m]!) hfrom (repTab[labTab[m]!]!) hrepT
        rwa [hfromPath] at h2
      · intro hm
        have hm256 : m < 256 := hT m hm
        refine ⟨hm256, ?_⟩
        have hmL : labTab[m]! ∈ L := by
          rw [hLdef, Finset.mem_image]
          exact ⟨m, hm, rfl⟩
        exact (hbit (labTab[m]!) (hfacts m hm256).1).2 hmL
    rw [← List.toFinset_card_of_nodup hnodup, hset]
  have hchk := hcheck b hb16
  simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hchk
  rw [hcnt] at hchk
  have hmod : 256 % T.card = 0 := Nat.mod_eq_zero_of_dvd hdvd
  rcases hchk with (h1 | h1) | h1
  · exact absurd hmod h1
  · refine Or.inl ?_
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
    have ha0 : a = 0 := by
      have h0' : (0 : ℕ) ∈ ({a} : Finset ℕ) := by rw [← ha]; exact h0
      exact (Finset.mem_singleton.mp h0').symm
    rw [ha, ha0]
  · refine Or.inr ?_
    apply Finset.eq_of_subset_of_card_le
    · intro m hm
      rw [Finset.mem_range]
      exact hT m hm
    · simp [Finset.card_range, h1]

end CFSG.EvenSporadicStandard.HNRecog.SideF4
