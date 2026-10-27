module

public import Certificates.Data.Kernel.Misc.Sp8Syl3
public import Certificates.Data.RudvalisFF81Sp8Torus
public import CFSG.Certificates.Kernel.Misc.BfsKSound
public import CFSG.Certificates.Kernel.Mat8PSound

public section

namespace CFSG.KC.Sp8Syl3

open CFSG.KD.Sp8Syl3 CFSG.KD.BfsK CFSG.KC.BfsK CFSG.KC.Mat8P CFSG.Quasithin.H13.Mat8Cert
  CFSG.Quasithin.G2U CFSG.RankThree.PartTwo.Sec21.FF81.Sp8

abbrev EncS (x : List ℕ) (N : ℕ) : Prop := Enc validS code64 x N

theorem code_inj (a b : List ℕ) (ha : validS a = true) (hb : validS b = true)
    (h : code64 a = code64 b) : a = b := by
  rw [← unpackS_code64 a ha, ← unpackS_code64 b hb, h]

theorem length_of_validS {B : List ℕ} (h : validS B = true) : B.length = 8 := by
  simp only [validS, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

theorem mulS_eq (A B : List ℕ) (hB : validS B = true) : mulS A B = mul8 A B := by
  match B, length_of_validS hB with
  | [_, _, _, _, _, _, _, _], _ => rfl

theorem encS_unpackM (X : ℕ) (hX : X < 2 ^ 64) : EncS (unpackM X) X :=
  ⟨validB_unpackM X, by rw [unpackM_eq, code64_unpackS, Nat.mod_eq_of_lt hX]⟩

theorem mulE {a b : List ℕ} {A B : ℕ} (ha : EncS a A) (hb : EncS b B) :
    EncS (mulS a b) (mulP A B) := by
  have e : mulS a b = unpackM (mulP A B) := by
    rw [mulS_eq a b hb.1, ← mul8_unpackM, ← ha.2, ← hb.2, ← code64R_eq,
      unpackM_code64R a ha.1, unpackM_code64R b hb.1]
  rw [e]
  exact encS_unpackM _ (mulP_lt A B)

theorem beqE {a b : List ℕ} {A B : ℕ} (ha : EncS a A) (hb : EncS b B) :
    (a == b) = Nat.beq A B := by
  apply Bool.eq_iff_iff.2
  rw [beq_iff_eq, Nat.beq_eq, ← ha.2, ← hb.2]
  exact ⟨fun h => h ▸ rfl, code_inj a b ha.1 hb.1⟩

theorem commS_eq {x g : List ℕ} {X G : ℕ} (hx : EncS x X) (hg : EncS g G) :
    commS x g = commN X G :=
  beqE (mulE hx hg) (mulE hg hx)

theorem one_enc : EncS one8 oneP := ⟨by decide, by decide⟩

variable {R : ℕ → ℕ}

theorem gen_enc (hz : ∀ s < 5, EncS (pGens.getD s []) (R s)) {s : ℕ} (hs : s < 5) (d : List ℕ) :
    EncS (pGens.getD s d) (R s) := by
  have hl : pGens.length = 5 := rfl
  rw [CFSG.KC.G2Three.listGetD_irrel (by rw [hl]; exact hs) d []]
  exact hz s hs

theorem e0_getD {s : ℕ} (hs : s < 4) (d : List ℕ) : e0Gens.getD s d = pGens.getD s d := by
  interval_cases s <;> rfl

theorem tabE_facts (hz : ∀ s < 5, EncS (pGens.getD s []) (R s)) (h : tabEK R 81 = true) :
    (tabS e0Gens 81).size = 81 ∧ closedCheck mulS e0Gens (tabS e0Gens 81) = true ∧
      distinctCheck (tabS e0Gens 81) = true ∧
      ∀ t < 81, EncS ((tabS e0Gens 81).getD t []) (recX R 11 t) := by
  unfold tabEK at h
  rw [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨h0, h⟩ := h
  obtain ⟨-, hsz, hcl, hdi, hrec⟩ := tableKk_ok (ok := validS) (num := code64) code_inj
    (start := one8) (mul := mulS) (gens := e0Gens) (fuel := 81) (k := 4) rfl (by norm_num) (by norm_num)
    le_rfl (fun x N hx s hs d => by rw [e0_getD hs]; exact mulE hx (gen_enc hz (by omega) d))
    (by rw [h0]; exact one_enc) h (by norm_num) (by norm_num) (by norm_num)
  exact ⟨hsz, hcl, hdi, hrec⟩

theorem tabP_facts (hz : ∀ s < 5, EncS (pGens.getD s []) (R s)) (h : tabPK R 243 = true) :
    (tabS pGens 243).size = 243 ∧ closedCheck mulS pGens (tabS pGens 243) = true ∧
      distinctCheck (tabS pGens 243) = true ∧
      ∀ t < 243, EncS ((tabS pGens 243).getD t []) (recX R 93 t) := by
  unfold tabPK at h
  rw [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨h0, h⟩ := h
  obtain ⟨-, hsz, hcl, hdi, hrec⟩ := tableKk_ok (ok := validS) (num := code64) code_inj
    (start := one8) (mul := mulS) (gens := pGens) (fuel := 243) (k := 5) rfl (by norm_num) (by norm_num)
    le_rfl (fun x N hx s hs d => mulE hx (gen_enc hz hs d))
    (by rw [h0]; exact one_enc) h (by norm_num) (by norm_num) (by norm_num)
  exact ⟨hsz, hcl, hdi, hrec⟩

theorem e0Chk_of (hz : ∀ s < 5, EncS (pGens.getD s []) (R s)) (hsp : e0Gens.all spS = true)
    (hE : tabEK R 81 = true) (h : e0K R = true) : e0Chk899103 = true := by
  obtain ⟨hsz, hcl, hdi, hrec⟩ := tabE_facts hz hE
  have hall := CFSG.KC.G2Three.allBelow_g2 h (by norm_num)
  have g0 : EncS z0S (R 0) := hz 0 (by norm_num)
  have g1 : EncS z1S (R 1) := hz 1 (by norm_num)
  have g2 : EncS z2S (R 2) := hz 2 (by norm_num)
  have g3 : EncS z3S (R 3) := hz 3 (by norm_num)
  unfold e0Chk899103 tabOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨hsz, hcl⟩, hdi⟩, CFSG.KC.G2Three.allCheck_of fun t ht => ?_⟩, hsp⟩,
    CFSG.KC.G2Three.allCheck_of fun t ht => ?_⟩, CFSG.KC.G2Three.allCheck_of fun t ht => ?_⟩
  · rw [hsz] at ht
    exact (hrec t ht).1
  · rw [hsz] at ht
    have hx := hrec t ht
    have e := hall t ht
    simp only [Bool.and_eq_true] at e
    obtain ⟨⟨⟨⟨c0, c1⟩, c2⟩, c3⟩, -⟩ := e
    generalize (tabS e0Gens 81).getD t [] = x at hx ⊢
    simp only [e0Gens, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    rw [commS_eq hx g0, commS_eq hx g1, commS_eq hx g2, commS_eq hx g3]
    exact ⟨c0, c1, c2, c3⟩
  · rw [hsz] at ht
    have hx := hrec t ht
    have e := hall t ht
    simp only [Bool.and_eq_true] at e
    rw [beqE (mulE hx (mulE hx hx)) one_enc]
    exact e.2

theorem pChk_of (hz : ∀ s < 5, EncS (pGens.getD s []) (R s)) (hsp : pGens.all spS = true)
    (h : tabPK R 243 = true) : pChk899103 = true := by
  obtain ⟨hsz, hcl, hdi, hrec⟩ := tabP_facts hz h
  unfold pChk899103 tabOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨hsz, hcl⟩, hdi⟩, CFSG.KC.G2Three.allCheck_of fun t ht => ?_⟩, hsp⟩
  rw [hsz] at ht
  exact (hrec t ht).1

theorem found_of (hz : ∀ s < 5, EncS (pGens.getD s []) (R s)) (hE : tabEK R 81 = true)
    {p : List ℕ} {P w : ℕ} (hp : EncS p P) (h : inE R w P = true) :
    found (tabS e0Gens 81) (indexMap (tabS e0Gens 81)) p = true := by
  obtain ⟨hsz, -, -, hrec⟩ := tabE_facts hz hE
  unfold inE at h
  rw [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  rw [CFSG.KC.G2Three.found_indexMap]
  exact ⟨w, by rw [hsz]; exact h.1,
    code_inj _ _ (hrec w h.1).1 hp.1 (by rw [(hrec w h.1).2, h.2, hp.2])⟩

theorem cpChk_of (hz : ∀ s < 5, EncS (pGens.getD s []) (R s)) (hE : tabEK R 81 = true)
    (hP : tabPK R 243 = true) (h : cpK R 81 = true) : cpChk899103 = true := by
  obtain ⟨hPsz, -, -, hPrec⟩ := tabP_facts hz hP
  have hall := CFSG.KC.G2Three.allBelow_g2 h (by norm_num)
  unfold cpChk899103
  dsimp only
  refine CFSG.KC.G2Three.allCheck_of fun t ht => ?_
  rw [hPsz] at ht
  have hp := hPrec t ht
  have e := hall t ht
  rw [Bool.or_eq_true] at e ⊢
  rcases e with e | e
  · exact Or.inl (found_of hz hE hp e)
  · refine Or.inr ?_
    rw [decide_eq_true_eq, hPsz]
    have hc : ((List.range 243).filter fun s =>
        commS ((tabS pGens 243).getD t []) ((tabS pGens 243).getD s [])) =
        (List.range 243).filter fun s => commN (recX R 93 t) (recX R 93 s) := by
      apply List.filter_congr
      intro s hs
      rw [commS_eq hp (hPrec s (List.mem_range.1 hs))]
    rw [hc]
    unfold cntP at e
    rwa [Nat.blt_eq] at e

theorem conjChk_of (hz : ∀ s < 5, EncS (pGens.getD s []) (R s))
    (hc : ∀ c < 3, EncS (conjL.getD c []) (R (Nat.add 5 c)) ∧
      EncS (invS (conjL.getD c [])) (R (Nat.add 8 c)))
    (hE : tabEK R 81 = true) (hP : tabPK R 243 = true) (h : conjK R = true) :
    conjChk899103 = true := by
  obtain ⟨hEsz, -, -, hErec⟩ := tabE_facts hz hE
  obtain ⟨hPsz, -, -, hPrec⟩ := tabP_facts hz hP
  have hall := CFSG.KC.G2Three.allBelow_g2 h (by norm_num)
  unfold conjChk899103
  dsimp only
  refine CFSG.KC.G2Three.allCheck_of fun t ht => ?_
  rw [hPsz] at ht
  have hp := hPrec t ht
  have e := hall t ht
  rw [beqE (mulE hp (mulE hp hp)) one_enc, beqE hp one_enc]
  simp only [Bool.or_eq_true] at e ⊢
  rcases e with ((e | e) | e) | e
  · exact Or.inl (Or.inl (Or.inl e))
  · exact Or.inl (Or.inl (Or.inr e))
  · exact Or.inl (Or.inr (found_of hz hE hp e))
  · refine Or.inr ?_
    unfold conjAt at e
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at e
    obtain ⟨-, ⟨hc3, he⟩, hcm⟩ := e
    generalize Nat.div (Nat.sub (recF R 93 14 t) 81) 81 = c at hc3 he hcm
    have hel : Nat.mod (Nat.sub (recF R 93 14 t) 81) 81 < 81 := Nat.mod_lt _ (by norm_num)
    generalize Nat.mod (Nat.sub (recF R 93 14 t) 81) 81 = j at hel he hcm
    obtain ⟨hcc, hci⟩ := hc c hc3
    have hconj : EncS (conjS (conjL.getD c []) ((tabS pGens 243).getD t [])) (recX R 11 j) := by
      rw [he]
      exact mulE (mulE hcc hp) hci
    rw [List.any_eq_true]
    refine ⟨conjL.getD c [], ?_, ?_⟩
    · have hl : conjL.length = 3 := rfl
      rw [List.getD_eq_getElem _ _ (by rw [hl]; exact hc3)]
      exact List.getElem_mem _
    · rw [Bool.and_eq_true]
      refine ⟨?_, ?_⟩
      · rw [CFSG.KC.G2Three.found_indexMap]
        exact ⟨j, by rw [hEsz]; exact hel,
          code_inj _ _ (hErec j hel).1 hconj.1 (by rw [(hErec j hel).2, hconj.2])⟩
      · rw [beqE (mulE hcc hp) (mulE hconj hcc), Nat.beq_eq]
        exact hcm

end CFSG.KC.Sp8Syl3

end
