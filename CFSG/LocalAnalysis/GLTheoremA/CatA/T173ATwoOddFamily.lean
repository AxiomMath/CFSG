module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ATwoOddInnerLe
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ATwoOddInnerGe
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ATwoOddType
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ATwoWeightOneLayer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ATwoDich
import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NBase

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S172A.GL (fixSp comSp)
open CFSG.LocalAnalysis.GLTheoremA.T173X
  (stdLayer innerClosure stdFamily IsStdElt StdVanishes StdTyped StdExtends)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem lin_two_oddFull_stdFamily (hb : CatDistinct.OrderBridge)
    (hV : 6 ≤ Module.finrank (ZMod 2) V) {A : Subgroup (V ≃ₗ[ZMod 2] V)}
    {g : V ≃ₗ[ZMod 2] V} (hA : GLAIsBmax 3 A) (hg : IsStdElt 3 A g)
    (hfix : Module.finrank (ZMod 2) (fixSp g) = 1) :
    stdFamily 3 A g ≤ innerClosure A g := by
  have hgA : g ∈ A := hg.1
  have hg3 : g ^ 3 = 1 := hg.2.2.1
  obtain ⟨x, P, V0, hF⟩ := lin_two_std_form_of_bmax (by omega) hA
  have hsumg := S172A.GL.finrank_fixSp hg3
  obtain ⟨m, hm⟩ := S172A.GL.even_finrank_comSp hg3
  have hd : Module.finrank (ZMod 2) V = 2 * m + 1 := by omega
  have hodd : Odd (Module.finrank (ZMod 2) V) := ⟨m, hd⟩
  have hV7 : 7 ≤ Module.finrank (ZMod 2) V := by omega
  obtain ⟨hfixg, hcomg⟩ := lin_two_frame_full_support hF hodd hgA hg3 hfix
  have hinner : innerClosure A g = linTwoOddBlock g :=
    le_antisymm (lin_two_oddFull_innerClosure_le hV hA hg hfix)
      (lin_two_oddFull_oddBlock_le hV hA hg hfix)
  unfold stdFamily
  refine iSup_le fun e => iSup_le fun he => ?_
  have heStd : IsStdElt 3 A e := he.1
  obtain ⟨eiso⟩ := he.2
  have heA : e ∈ A := heStd.1
  have he3 : e ^ 3 = 1 := heStd.2.2.1
  rcases lin_two_std_dichotomy hV hA heStd with h2 | hfixle
  ·
    exfalso
    have hecat := lin_two_weightOne_layerType hV7 he3 h2
    have hgcat : catalogIs (PSimple 3 (stdLayer g))
        (isLnA (Module.finrank (ZMod 2) V - 2) 2) := by
      obtain ⟨i, hi, ⟨f⟩⟩ := hecat
      exact ⟨i, hi, ⟨eiso.symm.trans f⟩⟩
    have hgcat4 := lin_two_oddFull_layerType hV7 hg3 hfix
    have hgm1 : Module.finrank (ZMod 2) V - 2 = 2 * m - 1 := by omega
    have hfullm : (Module.finrank (ZMod 2) V - 1) / 2 = m := by omega
    exact S172A.not_both_types (r := m) hb (by omega)
      (by simpa [hfullm] using hgcat4) (by simpa [hgm1] using hgcat)
  ·
    have hsum_e := S172A.GL.finrank_fixSp he3
    obtain ⟨m', hm'⟩ := S172A.GL.even_finrank_comSp he3
    have hefix : Module.finrank (ZMod 2) (fixSp e) = 1 := by omega
    obtain ⟨hfixe, hcome⟩ := lin_two_frame_full_support hF hodd heA he3 hefix
    have hfixeq : fixSp e = fixSp g := hfixe.trans hfixg.symm
    have hcomeq : comSp e = comSp g := hcome.trans hcomg.symm
    have hblock : linTwoOddBlock e ≤ linTwoOddBlock g := by
      intro h hh
      change (∀ v ∈ fixSp e, h v = v) ∧ (∀ w, w ∈ comSp e ↔ h w ∈ comSp e) at hh
      obtain ⟨hh1, hh2⟩ := hh
      change (∀ v ∈ fixSp g, h v = v) ∧ (∀ w, w ∈ comSp g ↔ h w ∈ comSp g)
      refine ⟨fun v hv => ?_, fun w => ?_⟩
      · rw [← hfixeq] at hv
        exact hh1 v hv
      · rw [← hcomeq]
        exact hh2 w
    calc stdLayer e ≤ Subgroup.centralizer ({e} : Set (V ≃ₗ[ZMod 2] V)) :=
          CFSG.LocalAnalysis.GLTheoremA.I142N.GLALayer_le _
      _ ≤ linTwoOddBlock e := by
          intro h hh
          have hcomm : h * e = e * h := Subgroup.mem_centralizer_singleton_iff.1 hh
          change (∀ v ∈ fixSp e, h v = v) ∧ (∀ w, w ∈ comSp e ↔ h w ∈ comSp e)
          refine ⟨fun v hv => S172A.GL.fix_of_finrank_one hefix
            (fun u hu => S172A.GL.cent_fix hcomm hu) v hv, fun w => ?_⟩
          constructor
          · intro hw
            exact S172A.GL.cent_com hcomm hw
          · intro hw
            have hcomm' : h⁻¹ * e = e * h⁻¹ :=
              Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.inv_mem _ hh)
            have hw' := S172A.GL.cent_com hcomm' hw
            simpa using hw'
      _ ≤ linTwoOddBlock g := hblock
      _ = innerClosure A g := hinner.symm

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
