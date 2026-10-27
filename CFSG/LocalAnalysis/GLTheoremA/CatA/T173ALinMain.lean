module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ALinCentre
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ALinBStruct
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ALinFrame
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ALinRank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ALinComp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ALinGen
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ALinClosure
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AUniCompQuot

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.T173
open scoped MatrixGroups


theorem t173ALinBig_holds : T173ALinBig := by
  intro p Ω _ _ S B N D K x n d F _ _ θ hcfg _hcat hmark hn hd
  exfalso
  have hp : p.Prime := hcfg.prime
  have hn1 : p ∣ 2 ^ n - 1 := by
    rcases hmark.2.2.2.2.1 with h1 | ⟨h1, -⟩
    · exact h1
    · omega
  have harith : LinArith p n d F :=
    ⟨hp, hcfg.odd, hn1, hd, hmark.1, hn, hmark.2.2.1⟩
  have hZ : ¬ p ∣ Nat.card (Subgroup.center ↥S) := lin_center_coprime hp hcfg.qs hmark hn hd
  obtain ⟨hBx, hBe, hBcard⟩ := lin_B_structure hcfg hmark hn hd hZ
  have hxC : x ∈ Subgroup.centralizer (S : Set Ω) :=
    (hcfg.cent x hcfg.mem).2 (Subgroup.mem_zpowers x)
  obtain ⟨y, hyB, hy1, hK⟩ := comp_quot hp hZ hcfg.elem hBx hcfg.mem hcfg.ne_one hxC hcfg.std
  obtain ⟨ψ, A, hfr⟩ := lin_exists_frame harith θ hBe
  have hrank : p ^ d ≤ Nat.card B := lin_rank_lower harith hcfg θ hZ
  have hd2 : 2 ≤ d := harith.2.2.2.2.2.2
  have hfull : p ^ (d - 1) ≤ Nat.card (modCentreImage S B) := by
    have h1 : p * p ^ (d - 1) ≤ p * Nat.card (modCentreImage S B) := by
      rw [← pow_succ', Nat.sub_add_cancel (by omega), ← hBcard]
      exact hrank
    exact Nat.le_of_mul_le_mul_left h1 hp.pos
  have hBimg := lin_frame_eq harith hfr hfull
  have hyQ : (QuotientGroup.mk y : ↥S ⧸ Subgroup.center ↥S) ∈ modCentreImage S B := by
    unfold modCentreImage
    exact Subgroup.mem_map.2 ⟨y, Subgroup.mem_subgroupOf.2 hyB, rfl⟩
  obtain ⟨I, hI2, hKI⟩ := lin_component_support harith hfr hyQ hy1 hK
  have htop := lin_quot_gen harith hBimg hI2 hKI
  have hcomp : CFSG.Open.IsComponentOf K (S ⊓ Subgroup.centralizer (D : Set Ω)) :=
    hcfg.std.2.2.2.2.2.1
  have hKS : K ≤ S := hcomp.1.trans inf_le_left
  have hcl : closureIn K N = S :=
    closureIn_eq_of_quot hp hcfg.normal hcfg.qs hZ hcfg.elem hBx hxC hcfg.hN hKS htop
  exact lin_hc_false hcfg.qs hcl hcfg.hc

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
