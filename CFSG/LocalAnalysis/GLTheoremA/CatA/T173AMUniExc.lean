module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMUniOdd
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMExcB
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMExcBase
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMExcComm
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMExcCyc
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMExcHc
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMExcLift
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMExcMark
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMExcStd

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.T173


theorem uni_exceptional {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B N D K : Subgroup Ω}
    {x : Ω} {F : Type} [Field F] [Finite F]
    (θ : ↥S ⧸ Subgroup.center ↥S ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) F (2 ^ 1)))
    (hcfg : Cfg173 p S B N D K x) (hmark : UniMarking p S B 1 6 F θ) (hpd : p ∣ 6)
    (_hZ : ¬ Odd (Nat.card (Subgroup.center ↥S))) : T173Concl p S B K N := by
  have hp : p.Prime := hcfg.prime
  have hp2 : p ≠ 2 := hcfg.odd
  have hS : S.Normal := hcfg.normal
  have hq : CFSG.Open.IsQuasisimple ↥S := hcfg.qs
  set Z : Subgroup Ω := (CFSG.pCore 2 ↥S).map S.subtype with hZdef
  haveI hZn : Z.Normal := uexc_twoCore_normal hS
  have hZ2 : IsPGroup 2 Z := uexc_twoCore_isPGroup S
  have hZS : Z ≤ S := uexc_twoCore_le S
  have hZc : Z ≤ Subgroup.centralizer (S : Set Ω) := uexc_twoCore_le_centralizer hq
  let π : Ω →* Ω ⧸ Z := QuotientGroup.mk' Z
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hker : π.ker = Z := QuotientGroup.ker_mk' Z
  have hk2 : IsPGroup 2 π.ker := by
    rw [hker]
    exact hZ2
  have hkc : π.ker ≤ Subgroup.centralizer (S : Set Ω) := by
    rw [hker]
    exact hZc
  have hkS : π.ker ≤ S := by
    rw [hker]
    exact hZS
  have hN : ¬ p ∣ Nat.card π.ker := uexc_not_dvd_card_ker hp hp2 π hk2
  have hNZ : ¬ p ∣ Nat.card Z := by
    rw [hker] at hN
    exact hN
  have hSperf : ⁅S, S⁆ = S := uexc_commutator_self hq.1
  have hKS : K ≤ S := (mcfg_of_cfg173 hcfg).K_le
  have hKq : CFSG.Open.IsQuasisimple ↥K := hcfg.std.2.2.2.2.2.1.2.2
  have hKperf : ⁅K, K⁆ = K := uexc_commutator_self hKq.1
  obtain ⟨hBel, hBcard, hxmem, hxne⟩ :=
    uexc_B_facts hp hp2 π hk2 hcfg.elem hcfg.mem hcfg.ne_one
  obtain ⟨θ', hmark'⟩ := uexc_uniMarking_map π hq.1 hkc hmark
  have hMcfg : MCfg p (S.map π) (B.map π) (N.map π) (D.map π) (K.map π) (π x) :=
    { prime := hp
      odd := hp2
      normal := Subgroup.Normal.map hS π hπ
      qs := uexc_isQuasisimple_map π hq hkc
      elem := hBel
      four := by rw [hBcard]; exact hcfg.four
      mem := hxmem
      ne_one := hxne
      cent := uexc_cent_field π hSperf hkc hcfg.mem hcfg.cent
      cyc := uexc_cycModSylow_map hp hS Z hNZ hcfg.cyc
      split := uexc_splitInnerDiagMarking16_map π hkc hcfg.split
      std := uexc_std_map hp π hN hS hkc hcfg.std
      hc := uexc_hc_map π hS hkc hKS hKperf hcfg.hc }
  have hodd : Odd (Nat.card (Subgroup.center ↥(S.map π))) := uexc_odd_center_map π hq hker
  have h4 : p ^ (6 - 2) ≤ Nat.card (B.map π) := by
    rw [hBcard]
    exact hcfg.four
  exact Or.inr (uexc_lift hp hp2 π hπ hk2 hS hkS hkc hKS hKperf hcfg.elem
    (uni_odd_case θ' hMcfg hmark' hpd hodd (Or.inr h4)))

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
