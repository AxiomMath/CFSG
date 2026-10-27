module

public import Certificates.Data.Kernel.Misc.Sp8Cz
public import CFSG.Certificates.Kernel.Misc.Sp8Syl3Sound
public import CFSG.Certificates.Kernel.Sp8.PlanesSound
public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81Sp8Codes

public section

namespace CFSG.KC.Sp8Cz

open CFSG.KD.Sp8Cz CFSG.KD.BfsK CFSG.KC.BfsK CFSG.KC.Mat8P CFSG.KC.Sp8Syl3
  CFSG.Quasithin.H13.Mat8Cert CFSG.Quasithin.G2U CFSG.RankThree.PartTwo.Sec21.FF81.Sp8
open CFSG.RankThree.PartTwo.Sec4.RonanK432 (H8 sm8)

theorem spS_mulS {a b : List ℕ} (ha : spS a = true) (hb : spS b = true) :
    spS (mulS a b) = true := by
  have h := spS_codeS (mkS a ha * mkS b hb)
  rwa [codeS_mul, codeS_mkS, codeS_mkS] at h

theorem mkS_mulS {a b : List ℕ} (ha : spS a = true) (hb : spS b = true) :
    mkS (mulS a b) (spS_mulS ha hb) = mkS a ha * mkS b hb :=
  codeS_injective (by rw [codeS_mul, codeS_mkS, codeS_mkS, codeS_mkS])

theorem commS_iff {a b : List ℕ} (ha : spS a = true) (hb : spS b = true) :
    commS a b = true ↔ mkS a ha * mkS b hb = mkS b hb * mkS a ha := by
  rw [commS, beq_iff_eq, commute_iff_codeS, codeS_mkS, codeS_mkS]

abbrev CzP (x : List ℕ) : Prop := spS x = true ∧ commS x zzS = true

theorem czP_mulS {x g : List ℕ} (hx : CzP x) (hg : CzP g) : CzP (mulS x g) := by
  have hz : spS zzS = true := by decide +kernel
  refine ⟨spS_mulS hx.1 hg.1, ?_⟩
  rw [commS_iff (spS_mulS hx.1 hg.1) hz, mkS_mulS hx.1 hg.1]
  have h1 := (commS_iff hx.1 hz).1 hx.2
  have h2 := (commS_iff hg.1 hz).1 hg.2
  rw [mul_assoc, h2, ← mul_assoc, h1, mul_assoc]

theorem czGens_czP : ∀ s < 8, CzP (czGens.getD s one8) := by decide +kernel

theorem cz_mem : ∀ x ∈ tabS czGens 12960, CzP x := by
  refine build_mem one8 mulS czGens (czGens_czP 7 (by norm_num)) (fun x hx s => ?_) _
  refine czP_mulS hx ?_
  by_cases hs : s < 7
  · exact czGens_czP s (by omega)
  · have hl : czGens.length = 7 := rfl
    have e : czGens.getD s one8 = czGens.getD 7 one8 := by
      rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
    rw [e]
    exact czGens_czP 7 (by norm_num)

theorem getD_mem {es : Array (List ℕ)} {t : ℕ} (ht : t < es.size) : es.getD t [] ∈ es := by
  rw [Array.getD, dif_pos ht]
  exact Array.getElem_mem ht

theorem sm8_eq (M : Matrix (Fin 8) (Fin 8) (ZMod 2)) :
    sm8 M = Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) finSumFinEquiv.symm M := by
  simp [sm8, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply]

theorem zE_eq_prod' (a : Fin 4 → ZMod 3) :
    CFSG.KC.Sp8Planes.zE a = CFSG.KC.Sp8Planes.zE ![1, 0, 0, 0] ^ (a 0).val *
      CFSG.KC.Sp8Planes.zE ![0, 1, 0, 0] ^ (a 1).val * CFSG.KC.Sp8Planes.zE ![0, 0, 1, 0] ^ (a 2).val *
      CFSG.KC.Sp8Planes.zE ![0, 0, 0, 1] ^ (a 3).val := by
  have ha : a = (a 0).val • ![1, 0, 0, 0] + (a 1).val • ![0, 1, 0, 0] + (a 2).val • ![0, 0, 1, 0] +
      (a 3).val • ![0, 0, 0, 1] := by
    funext p
    fin_cases p <;>
      simp [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_zmod_val, -ZMod.natCast_val]
  conv_lhs => rw [ha]
  rw [CFSG.KC.Sp8Planes.zE_add, CFSG.KC.Sp8Planes.zE_add, CFSG.KC.Sp8Planes.zE_add,
    CFSG.KC.Sp8Planes.zE_nsmul, CFSG.KC.Sp8Planes.zE_nsmul, CFSG.KC.Sp8Planes.zE_nsmul,
    CFSG.KC.Sp8Planes.zE_nsmul]

theorem e0_spS : spS z0S = true ∧ spS z1S = true ∧ spS z2S = true ∧ spS z3S = true := by
  decide +kernel

theorem e0_mem {z : List ℕ} (hz : z ∈ e0Gens) (h : spS z = true) : mkS z h ∈ subS e0Gens := by
  refine mem_subS_of_codeS ?_
  rw [codeS_mkS]
  exact hz

theorem found_E_of_zE (htab : tabOK e0Gens (tabS e0Gens 81) 81 = true) {x : List ℕ}
    (hx : spS x = true) {a : Fin 4 → ZMod 3} (ha : dec8 x = CFSG.KC.Sp8Planes.zE a) :
    found (tabS e0Gens 81) (indexMap (tabS e0Gens 81)) x = true := by
  rw [CFSG.KC.G2Three.found_indexMap]
  obtain ⟨s0, s1, s2, s3⟩ := e0_spS
  have hm : mkS x hx = mkS z0S s0 ^ (a 0).val * mkS z1S s1 ^ (a 1).val *
      mkS z2S s2 ^ (a 2).val * mkS z3S s3 ^ (a 3).val := by
    refine matS_injective ?_
    simp only [map_mul, map_pow, matS_mkS, decS, sm8_eq]
    rw [ha, zE_eq_prod', ← CFSG.KC.Sp8Planes.dec8_z0,
      ← CFSG.KC.Sp8Planes.dec8_z1, ← CFSG.KC.Sp8Planes.dec8_z2, ← CFSG.KC.Sp8Planes.dec8_z3]
    simp only [map_mul, map_pow]
  have hg : mkS x hx ∈ subS e0Gens := by
    rw [hm]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.pow_mem _ (e0_mem (by simp [e0Gens]) s0) _)
      (Subgroup.pow_mem _ (e0_mem (by simp [e0Gens]) s1) _))
      (Subgroup.pow_mem _ (e0_mem (by simp [e0Gens]) s2) _))
      (Subgroup.pow_mem _ (e0_mem (by simp [e0Gens]) s3) _)
  obtain ⟨t, ht, e⟩ := (mem_subS_iff htab _).mp hg
  exact ⟨t, ht, by rw [e, codeS_mkS]⟩

theorem tab_e0_of (h : e0Chk899103 = true) : tabOK e0Gens (tabS e0Gens 81) 81 = true := by
  unfold e0Chk899103 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1

theorem e0cChk_of (htab : tabOK e0Gens (tabS e0Gens 81) 81 = true) : e0cChk899105 = true := by
  unfold e0cChk899105
  dsimp only
  refine CFSG.KC.G2Three.allCheck_of fun t ht => ?_
  have hx := (cz_mem _ (getD_mem ht)).1
  generalize (tabS czGens 12960).getD t [] = x at hx ⊢
  cases hc : e0Gens.all (commS x)
  · rfl
  · obtain ⟨a, ha⟩ := CFSG.KC.Sp8Planes.e0c_planes hx hc
    rw [Bool.not_true, Bool.false_or]
    exact found_E_of_zE htab hx ha

theorem hypChk_of (htab : tabOK e0Gens (tabS e0Gens 81) 81 = true) : hypChk899105 = true := by
  unfold hypChk899105
  dsimp only
  refine CFSG.KC.G2Three.allCheck_of fun t ht => ?_
  have hx := cz_mem _ (getD_mem ht)
  generalize (tabS czGens 12960).getD t [] = x at hx ⊢
  rw [List.all_eq_true]
  intro a ha
  rw [List.all_eq_true]
  intro b hb
  cases hc : (commS x a && commS x b)
  · rfl
  · rw [Bool.and_eq_true] at hc
    obtain ⟨e, he⟩ := CFSG.KC.Sp8Planes.hyp_planes hx.1 hx.2 ha hb hc.1 hc.2
    rw [Bool.not_true, Bool.false_or]
    exact found_E_of_zE htab hx.1 he

variable {R : ℕ → ℕ}

theorem czgen_enc (hz : ∀ s < 7, EncS (czGens.getD s []) (R s)) {s : ℕ} (hs : s < 7)
    (d : List ℕ) : EncS (czGens.getD s d) (R s) := by
  have hl : czGens.length = 7 := rfl
  rw [CFSG.KC.G2Three.listGetD_irrel (by rw [hl]; exact hs) d []]
  exact hz s hs

theorem czTab_facts (hz : ∀ s < 7, EncS (czGens.getD s []) (R s)) (h : czTabK R 12960 = true) :
    (tabS czGens 12960).size = 12960 ∧ closedCheck mulS czGens (tabS czGens 12960) = true ∧
      distinctCheck (tabS czGens 12960) = true ∧
      ∀ t < 12960, EncS ((tabS czGens 12960).getD t []) (recX R 8 t) := by
  unfold czTabK at h
  rw [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨h0, h⟩ := h
  obtain ⟨-, hsz, hcl, hdi, hrec⟩ := tableKk_ok (ok := validS) (num := code64) code_inj
    (start := one8) (mul := mulS) (gens := czGens) (fuel := 12960) (k := 7) rfl (by norm_num)
    (by norm_num) le_rfl (fun x N hx s hs d => mulE hx (czgen_enc hz hs d))
    (by rw [h0]; exact one_enc) h (by norm_num) (by norm_num) (by norm_num)
  exact ⟨hsz, hcl, hdi, hrec⟩

theorem czChk_of (hz : ∀ s < 7, EncS (czGens.getD s []) (R s)) (hsp : czGens.all spS = true)
    (hcm : czGens.all (commS zzS) = true) (h : czTabK R 12960 = true) : czChk899105 = true := by
  obtain ⟨hsz, hcl, hdi, hrec⟩ := czTab_facts hz h
  unfold czChk899105 tabOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨hsz, hcl⟩, hdi⟩, CFSG.KC.G2Three.allCheck_of fun t ht => ?_⟩, hsp⟩, hcm⟩
  rw [hsz] at ht
  exact (hrec t ht).1

theorem contains_eq {L : List (List ℕ)} {LN : List ℕ} (h : List.Forall₂ EncS L LN) {x : List ℕ}
    {X : ℕ} (hx : EncS x X) : L.contains x = memN X LN := by
  induction h with
  | nil => rfl
  | cons hab _ ih =>
    rw [List.contains_cons, memN, List.any_cons, ← memN, ← ih, beqE hx hab]

theorem w2_enc {i j : ℕ} {A A' B B' : ℕ} (hA : EncS (l1S.getD (2 * i) []) A)
    (hA' : EncS (l1S.getD (2 * i + 1) []) A') (hB : EncS (l1S.getD (2 * j) []) B)
    (hB' : EncS (l1S.getD (2 * j + 1) []) B') :
    List.Forall₂ EncS (w2S i j) [mulP A B, mulP A B', mulP A' B, mulP A' B'] :=
  .cons (mulE hA hB) (.cons (mulE hA hB') (.cons (mulE hA' hB) (.cons (mulE hA' hB') .nil)))

theorem e9_of {i j a b o : ℕ} (hi : EncS (e0Gens.getD i []) (R a))
    (hj : EncS (e0Gens.getD j []) (R b)) (hl1 : List.Forall₂ EncS l1S (l1N R))
    (hw : List.Forall₂ EncS (w2S i j) (w2N R a b))
    (hsp : [e0Gens.getD i [], e0Gens.getD j []].all spS = true)
    (hT : e9TabK R o a b 9 = true) (hM : e9MemK R o a b = true) :
    (tabOK [e0Gens.getD i [], e0Gens.getD j []] (tabS [e0Gens.getD i [], e0Gens.getD j []] 9) 9 &&
      allCheck (fun x => x == one8 || l1S.contains x || (w2S i j).contains x)
        (tabS [e0Gens.getD i [], e0Gens.getD j []] 9)) = true := by
  unfold e9TabK at hT
  rw [Bool.and_eq_true, Nat.beq_eq] at hT
  obtain ⟨h0, hT⟩ := hT
  obtain ⟨-, hsz, hcl, hdi, hrec⟩ := tableKk_ok (ok := validS) (num := code64) code_inj
    (start := one8) (mul := mulS) (gens := [e0Gens.getD i [], e0Gens.getD j []]) (fuel := 9)
    (k := 2) rfl (by norm_num) (by norm_num) le_rfl
    (fun x N hx s hs d => by
      interval_cases s
      · exact mulE hx hi
      · exact mulE hx hj)
    (by rw [h0]; exact one_enc) hT (by norm_num) (by norm_num) (by norm_num)
  have hall := CFSG.KC.G2Three.allBelow_g2 hM (by norm_num)
  unfold tabOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨hsz, hcl⟩, hdi⟩, CFSG.KC.G2Three.allCheck_of fun t ht => ?_⟩, hsp⟩,
    CFSG.KC.G2Three.allCheck_of fun t ht => ?_⟩
  · have ht' : t < 9 := by
      rw [← hsz]
      exact ht
    exact (hrec t ht').1
  · have ht' : t < 9 := by
      rw [← hsz]
      exact ht
    have hx : EncS ((tabS [e0Gens.getD i [], e0Gens.getD j []] 9).getD t []) (recX R o t) :=
      hrec t ht'
    rw [beqE hx one_enc, contains_eq hl1 hx, contains_eq hw hx]
    exact hall t ht'

theorem card_cWS : cWS.card = cntW := by
  unfold cWS cntW
  apply congrArg Finset.card
  ext ⟨a, b⟩
  simp only [Finset.mem_filter, Finset.mem_product, condW, qW, crossW, Bool.and_eq_true]
  tauto

theorem card_cW'S : cW'S.card = cntW' := by
  unfold cW'S cntW'
  simp only [Finset.card_filter, Finset.sum_product, Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases h1 : b4N p r = true
  · rw [if_pos h1]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases h2 : (!b4N p q && !b4N r q) = true
    · rw [if_pos h2]
      refine Finset.sum_congr rfl fun s _ => ?_
      refine if_congr ?_ rfl rfl
      simp only [condW', Bool.and_eq_true] at h2 ⊢
      tauto
    · rw [if_neg h2]
      refine Finset.sum_eq_zero fun s _ => if_neg fun hc => h2 ?_
      simp only [condW', Bool.and_eq_true] at hc ⊢
      tauto
  · rw [if_neg h1]
    refine Finset.sum_eq_zero fun q _ => Finset.sum_eq_zero fun s _ => if_neg fun hc => h1 ?_
    simp only [condW', Bool.and_eq_true] at hc
    tauto

theorem colChk_of (h1 : cntW = 18) (h2 : cntW' = 720) : colChk899105 = true := by
  unfold colChk899105
  simp only [card_cWS, card_cW'S, h1, h2, beq_self_eq_true, Bool.and_self]

end CFSG.KC.Sp8Cz

end
