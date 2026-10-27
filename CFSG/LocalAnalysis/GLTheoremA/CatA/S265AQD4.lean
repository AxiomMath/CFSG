module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265QCfg
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YCDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRResTwF4
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265AQD4Core
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265AQD4Out

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10


theorem QUCfg.false_of_d4eight_outer (hcore : D4Y.D4BigCoreAt)
    {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x b : Ω}
    (cfg : QUCfg 3 S B T x b) (hF : FieldOn 3 b S)
    (hS8 : StatedClassicalModel (PSimple 3 S) .POmegaPlus 4 2 3)
    (hout : ¬ ∀ e ∈ B, ∀ he : e ∈ Subgroup.normalizer (Ipart 3 S b : Set Ω),
      chevAut 3 (Ipart 3 S b) ⟨e, he⟩ ∈ D4T.innerAut (PSimple 3 (Ipart 3 S b))) : False := by
  push Not at hout
  obtain ⟨e, he, heJ, hoe⟩ := hout
  have hNS : ∀ g : Ω, g ∈ Subgroup.normalizer (S : Set Ω) := fun g =>
    (Subgroup.normalizer_eq_top_iff.2 cfg.normal).symm ▸ Subgroup.mem_top g
  have hbo : ∀ a : ↥S, MulAut.conj a ≠ D4T.conjAut S b hF.1 := by
    intro a ha
    have ha' : MulAut.conj a⁻¹ = D4T.conjHom S ⟨b⁻¹, Subgroup.inv_mem _ hF.1⟩ := by
      rw [map_inv, ha]
      exact (map_inv (D4T.conjHom S) ⟨b, hF.1⟩).symm
    refine (FR.Res.fieldOn_outer Nat.prime_three (by norm_num) hF).2
      ⟨chevQuotHom 3 S a⁻¹, ?_⟩
    ext y
    obtain ⟨k, rfl⟩ := chevQuotHom_surjective 3 S y
    rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, MI.indAut, chevAut_chevQuotHom]
    congr 1
    exact congrArg (fun φ : MulAut ↥S => φ k) ha'
  exact QUCfg.not_notCentralOut hcore cfg hS8 he (hNS e)
    (QUCfg.notCentralOut_of_outer cfg hS8 hF.1
      (QUCfg.not_notCentralOut hcore cfg hS8 cfg.hb hF.1) hbo he (hNS e) heJ hoe)

end CFSG.LocalAnalysis.GLTheoremA.S265

end
