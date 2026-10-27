module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SKUniComp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SDAut
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryInnerExport
public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.GroupTheory.PLayer.PIndex
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Aux.Descent
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Split
public import CFSG.LieType.Multipliers.U62Sylow
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterD42Spec
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreEven
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreL34
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreRes
public import CFSG.LocalAnalysis.GL83PartI.I713.Basic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2Res
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDescN
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142MThree
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Cfg
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DSGen
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263GSz
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SDLift
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Alt
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieReduce
public import CFSG.Quasithin.Recognition.CertTrialityCheckInputs
public import CFSG.RankThree.PartOne.K159.AutCore
public import CFSG.RankThree.PartOne.K159.AutSzIso
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVDefs
public import CFSG.RankThree.ThinCatalog.EvenLinearTwoLocal

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.SK

open Polynomial Module Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCPrimary CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp

theorem famSel_unitary {n d : ℕ} {K : Type} [Field K] [Finite K] (h : UnitaryFieldData 2 n K)
    (hd : 3 ≤ d) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : p = 3 → 4 ≤ 2 ^ n) :
    SD.FamSel p (primeFormP h (idGram K d)) (fun φ => φ ∈ primeFormD h (idGram K d)) := by
  classical
  intro u hinn hup hu1 𝔹 h𝔹 Y hYfix hY2 hYinv hcomm
  obtain ⟨A, rfl⟩ := hinn
  have hd0 : 0 < d := by omega
  have hq : 2 ≤ 2 ^ n :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h.one_le
  haveI : CharP K 2 := h.charP
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have H := primaryData_of_conj_pow h hd A hp hp2 hup
  have hY2' : ∀ w ∈ Y, ∃ k : ℕ, w ^ (2 ^ k) = 1 := fun w hw => by
    obtain ⟨k, hk⟩ := hY2 ⟨w, hw⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have lift2 : ∀ w ∈ Y, ∃ g : ↥(gramSU h (idGram K d)), (g : primeFormP h (idGram K d)) = w ∧
      (∃ k : ℕ, g ^ (2 ^ k) = 1) ∧
      toLinSU h d g ∈ unitaryCentralizer (idForm h d) (Matrix.GeneralLinearGroup.toLin (A : GL (Fin d) K)) := by
    intro w hw
    obtain ⟨k, hk⟩ := hY2' w hw
    obtain ⟨g, hg, hgk⟩ := exists_lift_two_pow h hd0 hk
    exact ⟨g, hg, ⟨k, hgk⟩, lift_mem_unitaryCentralizer h hd0 A (hYfix hw) hg hgk⟩
  have hcommY : ∀ b ∈ 𝔹, ∀ y ∈ Y, b y * y⁻¹ ∈ Y := by
    intro b hb y hy
    have h1 : b.toMonoidHom y ∈ Y.map b.toMonoidHom := Subgroup.mem_map_of_mem _ hy
    rw [hYinv b hb] at h1
    exact Y.mul_mem h1 (Y.inv_mem hy)
  obtain ⟨b, hb, y, hy, hz⟩ : ∃ b ∈ 𝔹, ∃ y ∈ Y, b y * y⁻¹ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hcomm
    rw [SD.autComm, eq_bot_iff, Subgroup.closure_le]
    rintro z ⟨b, hb, y, hy, rfl⟩
    exact Subgroup.mem_bot.2 (hcon b hb y hy)
  obtain ⟨⟨B, rfl⟩, hbp, hbu⟩ := h𝔹 b hb
  have hzY : primeFormConjHom h (idGram K d) B y * y⁻¹ ∈ Y := hcommY _ hb y hy
  obtain ⟨g, hgy, -, hgcU⟩ := lift2 y hy
  obtain ⟨zt, hzt, ⟨k₂, hzt2⟩, hztc⟩ := lift2 _ hzY
  have hzt1 : zt ≠ 1 := by
    intro h1
    apply hz
    rw [← hzt, h1, QuotientGroup.mk_one]
  have hrel : ((primeFormConjSU h (idGram K d) B g * g⁻¹ : ↥(gramSU h (idGram K d))) :
      primeFormP h (idGram K d)) = (zt : primeFormP h (idGram K d)) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, mk_primeFormConjSU h B g, hgy, hzt]
  have hs : (primeFormConjSU h (idGram K d) B g * g⁻¹)⁻¹ * zt ∈
      normOneScalars h (gramSU h (idGram K d)) d := QuotientGroup.eq.1 hrel
  have hzt_gl : toLinSU h d zt ≠ 1 := fun h1 => hzt1 (toLinSU_injective (by rw [h1, map_one]))
  have hzt_pow : (toLinSU h d zt) ^ (2 ^ k₂) = 1 := by rw [← map_pow, hzt2, map_one]
  have hgc : toLinSU h d g ∈ gl_centralizer (Matrix.GeneralLinearGroup.toLin (A : GL (Fin d) K)) := hgcU.2
  obtain ⟨a, ha, v, hv, hne⟩ := exists_good_block_uni h2 h H.squarefree hztc.2 hzt_pow hzt_gl
    (fun b' hng hm2 => bad_block_trivial_uni h hd hp hp2 hK H hup hbu hbp hgc hs hzt2 b' hng hm2)
  refine ⟨KD264Lie.unitaryBlockComponent h (x := Matrix.GeneralLinearGroup.toLin (A : GL (Fin d) K)) (a : K[X]),
    isComponentOf_unitaryBlockComponent h H hq a ha, ?_, ?_, ?_⟩
  ·
    refine dvd_card_centerQuot_unitaryBlockComponent h H hq a ha hp ?_
    by_cases hpq : p ∣ Nat.card (AdjoinRoot (a : K[X])) - 1
    · exact dvd_card_specialBlock_of_dvd H a ha.1 hp hpq
    · exact dvd_card_specialBlock_of_not_dvd h hd hp H hup hbu hbp hgc hs hzt2 a hpq hv hne
  ·
    intro hbot
    obtain ⟨f, hfF, hnc⟩ := exists_noncomm_uni h hd0 H hq a ha hztc hzt2 hv hne
    have hzmem : primeFormConjHom h (idGram K d) B y * y⁻¹ ∈ SD.autComm 𝔹 Y :=
      Subgroup.subset_closure ⟨_, hb, y, hy, rfl⟩
    have hjmem : QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K d)) d) f ∈
        KD264Lie.unitaryBlockComponent h (x := Matrix.GeneralLinearGroup.toLin (A : GL (Fin d) K)) (a : K[X]) :=
      Subgroup.mem_map_of_mem _ hfF
    have hcc := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hbot hzmem
    have hc1 := Subgroup.mem_centralizer_iff.1 hcc _ hjmem
    apply hnc
    rw [hzt]
    exact hc1.symm
  ·
    rw [SD.autComm, Subgroup.closure_le]
    rintro _ ⟨b', hb', y', hy', rfl⟩
    obtain ⟨zt', hzt', ⟨k, hk⟩, hztc'⟩ := lift2 _ (hcommY b' hb' y' hy')
    obtain ⟨w₁, hw₁, w₂, hw₂c, hw₂comm, hdec⟩ := exists_decomp_uni h H hq a ha hztc' hk
    rw [SetLike.mem_coe, ← hzt', hdec]
    show QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K d)) d) (w₂ * w₁) ∈ _
    rw [map_mul]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨?_, ?_⟩))
      (Subgroup.mem_sup_left (Subgroup.mem_map_of_mem _ hw₁))
    · exact mk_mem_fix_of_mem_fix h ((mem_fixSubgroup_primeFormConjSU_iff A rfl w₂).mpr hw₂c.2)
    · refine Subgroup.mem_centralizer_iff.2 ?_
      rintro _ ⟨f, hf, rfl⟩
      rw [← map_mul, ← map_mul, hw₂comm f hf]

end CFSG.LocalAnalysis.GLTheoremA.T263.SK

end
