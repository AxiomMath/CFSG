module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48X1
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48X4
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U48.X5

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.CatB
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.CatB.U48
open CFSG.LocalAnalysis.GLTheoremA.CatB.U48.X1
open CFSG.LocalAnalysis.GLTheoremA.CatB.U48.X3
open CFSG.LocalAnalysis.GLTheoremA.CatB.U48.X4


variable {G : Type} [Group G] [Finite G]

theorem primeCoreOf_eq_bot_of_three_group {G : Type} [Group G] [Finite G] {Q : Subgroup G}
    (hQ : IsPGroup 3 Q) : GLAPPrimeCoreOf 3 Q = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hQ
  have h1 : GLAPPrimeCore 3 ↥Q = ⊥ := by
    show CFSG.pPrimeCore 3 ↥Q = ⊥
    rw [CFSG.pPrimeCore_eq_bot_iff]
    intro K _ hKc
    have hd : Nat.card K ∣ 3 ^ n := hn ▸ Subgroup.card_subgroup_dvd_card K
    have h1' : Nat.card K = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right n hKc.symm) hd
    exact Subgroup.eq_bot_of_card_eq K h1'
  show (GLAPPrimeCore 3 ↥Q).map Q.subtype = ⊥
  rw [h1, Subgroup.map_bot]

theorem su32InterAt_holds (G : Type) [Group G] [Finite G] : Su32InterAt G := by
  intro X X' L J b d y hL hJ hcatL hcatJ hFOb hFOd hb3 hd3 hIeq hyI hy3 hy1 hyc hyL hyJ
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hlayle : ∀ Y : Subgroup G, GLAPLayer 3 Y ≤ Y := fun Y => sSup_le fun K hK => hK.1
  obtain ⟨γ, hγ3, hff, hcardF, ψ, hψs, hψk, hIL⟩ :=
    ipart_fix_model X L b hL hcatL hFOb hb3 (Ipart 3 L b) rfl
  obtain ⟨Q, hQ3, hQle, hnc⟩ :=
    derived_three_in_ipart hγ3 hff hcardF ψ hψs hψk hyI hy3 hyc
  have hIJ : Ipart 3 L b ≤ J := by
    have h1 : Ipart 3 J d ≤ J := (hlayle _).trans inf_le_left
    rw [← hIeq] at h1
    exact h1
  have hQL : Q ≤ ⁅L ⊓ Subgroup.centralizer ({y} : Set G), L ⊓ Subgroup.centralizer ({y} : Set G)⁆ :=
    hQle.trans (Subgroup.commutator_mono (inf_le_inf hIL le_rfl) (inf_le_inf hIL le_rfl))
  have hQJ : Q ≤ ⁅J ⊓ Subgroup.centralizer ({y} : Set G), J ⊓ Subgroup.centralizer ({y} : Set G)⁆ :=
    hQle.trans (Subgroup.commutator_mono (inf_le_inf hIJ le_rfl) (inf_le_inf hIJ le_rfl))
  have hQ1 := layer_criterion hL hcatL hy3 hy1 hyL hQ3 hQL
  have hQ2 := layer_criterion hJ hcatJ hy3 hy1 hyJ hQ3 hQJ
  exact ⟨Q, le_inf hQ1 hQ2, hnc, primeCoreOf_eq_bot_of_three_group hQ3⟩

end CFSG.LocalAnalysis.GLTheoremA.CatB.U48.X5
