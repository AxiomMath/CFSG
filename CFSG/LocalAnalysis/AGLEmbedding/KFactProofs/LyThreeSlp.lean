module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.LyThreeDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.LyGenCrit
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsFp
public import CFSG.RankThree.PartOne.CTP.FusionSound
import all CFSG.Sporadic.Ly.Setup

public section

namespace CFSG.AGLEmbedding.R3

open CFSG.RankThree.Asc83Table CFSG.RankThree.Asc83Table.Native CFSG.SectionRank
  CFSG.SectionRank.Native CFSG.Blueprint CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier
  CFSG.SectionRank.LocalWitness CFSG.Sporadic.He.Native CFSG.Sporadic.Ly.Native
  CFSG.Sporadic.LySchreier.Native

private theorem lyEquivJ_val_aux (u : NativeSporadic.Ly) :
    (((lyEquivJ u : J) : GL (Fin 111) (ZMod 5)) : Matrix (Fin 111) (Fin 111) (ZMod 5)) =
      u.val.val :=
  NativeSporadic.matrixSeedEquiv_val 5 111 (by norm_num) mA mB _ _ u

theorem lyEquivJ_val (u : NativeSporadic.Ly) :
    (((lyEquivJ u : J) : GL (Fin 111) (ZMod 5)) : Matrix (Fin 111) (Fin 111) (ZMod 5)) =
      u.val.val := lyEquivJ_val_aux u

theorem ly_closure_eq_top
    {S : Set NativeSporadic.Ly} {z c0 c1 l t : NativeSporadic.Ly} (hz : lyEquivJ z = lyz)
    (h0 : lyEquivJ c0 = cSeed 0) (h1 : lyEquivJ c1 = cSeed 1)
    (hc0 : c0 ∈ Subgroup.closure S) (hc1 : c1 ∈ Subgroup.closure S)
    (hl : l ∈ Subgroup.closure S) (hlt : l * z * l⁻¹ = t) (ht2 : t * t = 1) (htz : t ≠ z)
    (hcomm : t * z = z * t) : Subgroup.closure S = ⊤ := by
  have hz1 : z ≠ 1 := by
    intro h
    have h' : lyz = 1 := by rw [← hz, h, map_one]
    have : orderOf lyz = 2 := orderOf_a
    rw [h', orderOf_one] at this
    exact absurd this (by norm_num)
  have ht1 : t ≠ 1 := by
    intro h
    apply hz1
    calc z = l⁻¹ * (l * z * l⁻¹) * l := by group
      _ = l⁻¹ * 1 * l := by rw [hlt, h]
      _ = 1 := by group
  set L : Subgroup J := (Subgroup.closure S).map (lyEquivJ : NativeSporadic.Ly →* J) with hL
  have hCL : lyC ≤ L := by
    rw [lyC, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨c0, hc0, h0⟩
    · exact ⟨c1, hc1, h1⟩
  have htC : lyEquivJ t ∈ lyC := by
    rw [lyC_eq_centralizer, Subgroup.mem_centralizer_singleton_iff, ← hz]
    rw [← map_mul, ← map_mul, hcomm]
  have ht2' : orderOf (lyEquivJ t) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [sq, ← map_mul, ht2, map_one]
    · intro h
      exact ht1 (lyEquivJ.injective (by rw [h, map_one]))
  have hne' : lyEquivJ t ≠ lyz := by
    rw [← hz]
    exact fun h => htz (lyEquivJ.injective h)
  have hlz : lyEquivJ l * lyz * (lyEquivJ l)⁻¹ = lyEquivJ t := by
    rw [← hz, ← map_inv, ← map_mul, ← map_mul, hlt]
  have htop := eq_top_of_conj_invol hCL (l := lyEquivJ l) (t := lyEquivJ t)
    ⟨l, hl, rfl⟩ htC ht2' hne' hlz
  have : Subgroup.comap (lyEquivJ : NativeSporadic.Ly →* J) L = Subgroup.closure S :=
    Subgroup.comap_map_eq_self_of_injective lyEquivJ.injective _
  rw [← this, htop, Subgroup.comap_top]

section Ident

variable {C : MCert}
  (hC : mcertCheck (opsP 5 111) NativeSporadic.LySeed1 NativeSporadic.LySeed2 C = true)

theorem ly_ident_of_rep {r e : ℕ} (hf : MFact.ord r e ∈ C.facts)
    {X : Array (Array ℕ)} {g : J} (hX : toMat 5 111 X = mat g)
    (hr : (opsP 5 111).eq (certRegs (opsP 5 111) NativeSporadic.LySeed1
      NativeSporadic.LySeed2 C)[r]! X = true) :
    lyEquivJ (regUnit (specP 5 111) hC r) = g := by
  have hreg := (reg_pow (specP 5 111) hC hf).1
  have h2 : valHom (certMonoid 5 111 NativeSporadic.LySeed1 NativeSporadic.LySeed2)
      (regUnit (specP 5 111) hC r) = (specP 5 111).toMat
        (certRegs (opsP 5 111) NativeSporadic.LySeed1 NativeSporadic.LySeed2 C)[r]! :=
    val_regUnit (specP 5 111) hC hf
  have h3 : (specP 5 111).toMat (certRegs (opsP 5 111) NativeSporadic.LySeed1
      NativeSporadic.LySeed2 C)[r]! = toMat 5 111 X :=
    (specP 5 111).toMat_eq trivial trivial hr
  apply Subtype.ext
  apply Units.ext
  exact (lyEquivJ_val _).trans (h2.trans (h3.trans hX))

theorem ly_ident_seeds (h0 : MFact.ord 0 2 ∈ C.facts)
    (h1 : MFact.ord 1 5 ∈ C.facts)
    (hA : (opsP 5 111).eq (certRegs (opsP 5 111) NativeSporadic.LySeed1
      NativeSporadic.LySeed2 C)[0]! ((opsP 5 111).decode NativeSporadic.LySeed1) = true)
    (hB : (opsP 5 111).eq (certRegs (opsP 5 111) NativeSporadic.LySeed1
      NativeSporadic.LySeed2 C)[1]! ((opsP 5 111).decode NativeSporadic.LySeed2) = true) :
    lyEquivJ (regUnit (specP 5 111) hC 0) = lyz ∧ lyEquivJ (regUnit (specP 5 111) hC 1) = b :=
  ⟨ly_ident_of_rep hC h0 ((specP 5 111).toMat_decode _) hA,
   ly_ident_of_rep hC h1 ((specP 5 111).toMat_decode _) hB⟩

theorem ly_ident_c {r e : ℕ} (hf : MFact.ord r e ∈ C.facts)
    (j : ℕ)
    (hr : (opsP 5 111).eq (certRegs (opsP 5 111) NativeSporadic.LySeed1
      NativeSporadic.LySeed2 C)[r]!
      (evalWordM seedM (seedMInv (powM 5 111 matB 4)) (seedWord j)) = true) :
    lyEquivJ (regUnit (specP 5 111) hC r) = cSeed j :=
  ly_ident_of_rep hC hf (repM_cSeed j) hr

end Ident

section Gen

variable {C : MCert}
  (hC : mcertCheck (opsP 5 111) NativeSporadic.LySeed1 NativeSporadic.LySeed2 C = true)

theorem ly_gen_top
    (G : LGen) (hG : ∀ f ∈ G.facts, f ∈ C.facts)
    (hA : (opsP 5 111).eq (certRegs (opsP 5 111) NativeSporadic.LySeed1
      NativeSporadic.LySeed2 C)[0]! ((opsP 5 111).decode NativeSporadic.LySeed1) = true)
    (hB : (opsP 5 111).eq (certRegs (opsP 5 111) NativeSporadic.LySeed1
      NativeSporadic.LySeed2 C)[1]! ((opsP 5 111).decode NativeSporadic.LySeed2) = true)
    (hc0 : (opsP 5 111).eq (certRegs (opsP 5 111) NativeSporadic.LySeed1
      NativeSporadic.LySeed2 C)[G.rc0]!
      (evalWordM seedM (seedMInv (powM 5 111 matB 4)) (seedWord 0)) = true)
    (hc1 : (opsP 5 111).eq (certRegs (opsP 5 111) NativeSporadic.LySeed1
      NativeSporadic.LySeed2 C)[G.rc1]!
      (evalWordM seedM (seedMInv (powM 5 111 matB 4)) (seedWord 1)) = true)
    {S : Set NativeSporadic.Ly}
    (hw : ∀ q ∈ G.words, regUnit (specP 5 111) hC q.1 ∈ Subgroup.closure S ∧
      ∃ o, MFact.ord q.1 o ∈ C.facts) : Subgroup.closure S = ⊤ := by
  set Sp := specP 5 111 with hSp
  have f0 : MFact.ord 0 2 ∈ C.facts := hG _ (by simp [LGen.facts])
  have f1 : MFact.ord 1 5 ∈ C.facts := hG _ (by simp [LGen.facts])
  have fc0 : MFact.ord G.rc0 14 ∈ C.facts := hG _ (by simp [LGen.facts])
  have fc1 : MFact.ord G.rc1 6 ∈ C.facts := hG _ (by simp [LGen.facts])
  have fw0 : MFact.eq [(G.rc0, 1)] G.wc0 ∈ C.facts := hG _ (by simp [LGen.facts])
  have fw1 : MFact.eq [(G.rc1, 1)] G.wc1 ∈ C.facts := hG _ (by simp [LGen.facts])
  have fl : MFact.ord G.rl G.ol ∈ C.facts := hG _ (by simp [LGen.facts])
  have ft : MFact.ord G.rt 2 ∈ C.facts := hG _ (by simp [LGen.facts])
  have fconj : MFact.conj G.rl [(0, 1)] [(G.rt, 1)] ∈ C.facts := hG _ (by simp [LGen.facts])
  have fcomm : MFact.eq [(G.rt, 1), (0, 1)] [(0, 1), (G.rt, 1)] ∈ C.facts :=
    hG _ (by simp [LGen.facts])
  have fne : MFact.ne [(0, 1)] [(G.rt, 1)] G.tne ∈ C.facts := hG _ (by simp [LGen.facts])
  obtain ⟨e0, -⟩ := ly_ident_seeds hC f0 f1 hA hB
  have ec0 := ly_ident_c hC fc0 0 hc0
  have ec1 := ly_ident_c hC fc1 1 hc1
  have hO : ∀ w : Word, (∀ q ∈ w, q ∈ G.words) → HasOrd C w := fun w hw' q hq => (hw q (hw' q hq)).2
  have hmem : ∀ w : Word, (∀ q ∈ w, q ∈ G.words) → wordUnit Sp hC w ∈ Subgroup.closure S :=
    fun w hw' => CFSG.RankThree.PartOne.CTP.Fus.wordUnit_mem_subgroup Sp hC _ w fun q hq =>
      (hw q (hw' q hq)).1
  have hO0 : HasOrd C [(0, 1)] := fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact ⟨2, f0⟩
  have hOt : HasOrd C [(G.rt, 1)] := fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact ⟨2, ft⟩
  have hOc0 : HasOrd C [(G.rc0, 1)] := fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact ⟨14, fc0⟩
  have hOc1 : HasOrd C [(G.rc1, 1)] := fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact ⟨6, fc1⟩
  have hw0 : regUnit Sp hC G.rc0 = wordUnit Sp hC G.wc0 := by
    have := regUnit_eq Sp hC fw0 hOc0 (hO G.wc0 fun q hq => by simp [LGen.words, hq])
    simpa [wordUnit] using this
  have hw1 : regUnit Sp hC G.rc1 = wordUnit Sp hC G.wc1 := by
    have := regUnit_eq Sp hC fw1 hOc1 (hO G.wc1 fun q hq => by simp [LGen.words, hq])
    simpa [wordUnit] using this
  have hlt : regUnit Sp hC G.rl * regUnit Sp hC 0 * (regUnit Sp hC G.rl)⁻¹ =
      regUnit Sp hC G.rt := by
    have := regUnit_conj Sp hC fconj fl hO0 hOt
    simpa [wordUnit] using this
  have ht2 : regUnit Sp hC G.rt * regUnit Sp hC G.rt = 1 := by
    rw [← sq]; exact regUnit_pow Sp hC ft
  have htz : regUnit Sp hC G.rt ≠ regUnit Sp hC 0 := by
    have := regUnit_ne Sp hC fne hO0 hOt
    simpa [wordUnit] using this.symm
  have hcomm : regUnit Sp hC G.rt * regUnit Sp hC 0 = regUnit Sp hC 0 * regUnit Sp hC G.rt := by
    have := regUnit_eq Sp hC fcomm (by
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact ⟨2, ft⟩
      · exact ⟨2, f0⟩) (by
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact ⟨2, f0⟩
      · exact ⟨2, ft⟩)
    simpa [wordUnit] using this
  refine ly_closure_eq_top (z := regUnit Sp hC 0) (c0 := regUnit Sp hC G.rc0)
    (c1 := regUnit Sp hC G.rc1) (l := regUnit Sp hC G.rl) (t := regUnit Sp hC G.rt) e0 ec0 ec1
    ?_ ?_ ?_ hlt ht2 htz hcomm
  · rw [hw0]; exact hmem _ fun q hq => by simp [LGen.words, hq]
  · rw [hw1]; exact hmem _ fun q hq => by simp [LGen.words, hq]
  · exact (hw (G.rl, 1) (by simp [LGen.words])).1

end Gen


end CFSG.AGLEmbedding.R3
