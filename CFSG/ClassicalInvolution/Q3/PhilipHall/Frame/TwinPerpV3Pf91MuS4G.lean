module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf2Fourth
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinMuLayer
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUAE5Cent
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf2Alpha
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3PfDefs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Asc77.MuTab (muTabElt muTabElt_mem)

section Adapted


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y}

theorem exists_member_adapted (hStd : V3Std n Y R S t K K' K₃ u₁ u₂ u₃)
    (h2g : ∀ J ∈ CoreAssembly.conjClass (tightCore R), IsPGroup 2 ↥J)
    {W : Subgroup Y} (hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R)))
    (hKD : K ∈ DSet (CoreAssembly.conjClass (tightCore R)) W)
    (hK'D : K' ∈ DSet (CoreAssembly.conjClass (tightCore R)) W)
    (hK₃D : K₃ ∈ DSet (CoreAssembly.conjClass (tightCore R)) W) (hu₁ : u₁ ∈ W) (hu₂ : u₂ ∈ W) :
    ∃ L : Subgroup Y, L ∈ CoreAssembly.conjClass (tightCore R) ∧
      L ≤ Subgroup.centralizer ({u₁ * u₂} : Set Y) ∧
      L ∈ omegaStarNbr (CoreAssembly.conjClass (tightCore R)) K₃ ∧
      ∃ zL : Y, IsUniqueInvolution L zL ∧ zL ∈ W ∧ zL ≠ t := by
  classical
  have hd := hStd.datum
  have hC := CoreData.of_S hStd.perp.core
  have hP : Q3CL.PartIHypG (CoreAssembly.conjClass (tightCore R)) := hC.partIHypG
  have hΩ := hd.hyp
  have hperp := kPerp_datum hStd.perp hd.mem hd.hz
  have hself : ∀ J ∈ CoreAssembly.conjClass (tightCore R), IsSylow2In J J := fun J hJ =>
    ⟨le_rfl, h2g J hJ, fun V' hV' _ hle => le_antisymm hV' hle⟩
  let ρa : Rep (CoreAssembly.conjClass (tightCore R)) W :=
    Q3CL.T8.mkRep hP hW hd.mem hKD (hself K hd.mem)
  let ρb : Rep (CoreAssembly.conjClass (tightCore R)) W :=
    Q3CL.T8.mkRep hP hW hd.hK'.1 hK'D (hself K' hd.hK'.1)
  let ρc : Rep (CoreAssembly.conjClass (tightCore R)) W :=
    Q3CL.T8.mkRep hP hW hd.hK₃.1 hK₃D (hself K₃ hd.hK₃.1)
  have hρa : ρa.K = K := rfl
  have hρb : ρb.K = K' := rfl
  have hρc : ρc.K = K₃ := rfl
  have hKt : K ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K := mem_twinSet_self hd.mem hd.hz
  have hKK' : ρa.K ≠ ρb.K := by rw [hρa, hρb]; exact Ne.symm hd.hne
  have hKK₃ : ρa.K ≠ ρc.K := by rw [hρa, hρc]; exact Ne.symm hd.hK₃K
  have hK'K₃ : ρb.K ≠ ρc.K := by rw [hρb, hρc]; exact Ne.symm hd.hK₃K'
  have hab : muTabElt ρa ≠ muTabElt ρb := fun h => hKK' ((Q3T6.Mu.muTabElt_eq_iff hP hW ρa ρb).mp h)
  have hac : muTabElt ρa ≠ muTabElt ρc := fun h => hKK₃ ((Q3T6.Mu.muTabElt_eq_iff hP hW ρa ρc).mp h)
  have hbc : muTabElt ρb ≠ muTabElt ρc := fun h => hK'K₃ ((Q3T6.Mu.muTabElt_eq_iff hP hW ρb ρc).mp h)
  have nab : ρb.K ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) ρa.K := by
    rw [hρa, hρb]; exact adj_of_twins' hd hperp hKt hd.hK' hd.hne
  have nac : ρc.K ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) ρa.K := by
    rw [hρa, hρc]; exact adj_of_twins' hd hperp hKt hd.hK₃ hd.hK₃K
  have cab : muTabElt ρa * muTabElt ρb = muTabElt ρb * muTabElt ρa :=
    (Q3T6.Mu.muTab_commute_iff hP hW ρa ρb hKK').mpr nab
  have cac : muTabElt ρa * muTabElt ρc = muTabElt ρc * muTabElt ρa :=
    (Q3T6.Mu.muTab_commute_iff hP hW ρa ρc hKK₃).mpr nac
  have hnc : ¬ DbarConnected (CoreAssembly.conjClass (tightCore R)) W :=
    not_dbarConnected_of_wyl' hP hd hperp hW ρa hρa (hStd.wyl W hW)
  obtain ⟨ρS, hρSC, hconn⟩ := TwinMu.exists_S hP hW hnc hab hac hbc cab cac
    (w := u₁) (v := u₂) ⟨hd.hu₁.1, hu₁⟩ ⟨hd.hu₂.1, hu₂⟩ hd.hu₁.2 hd.hu₂.2
  have hSΩ : ρS.K ∈ CoreAssembly.conjClass (tightCore R) := ρS.hK
  have hSL : ρS.K = ρS.R := ρS.hRK.2.2 ρS.K le_rfl (h2g _ hSΩ) ρS.hRK.1
  have hSC : ρS.K ≤ Subgroup.centralizer ({u₁ * u₂} : Set Y) := hSL ▸ hρSC
  obtain ⟨zS, hzS⟩ := Sec6Gen.exists_uniqueInvolution hΩ hSΩ
  have ctx := Q3CL.T8.ctxOf hP hW
  obtain ⟨ws, hws, hws4⟩ := Q3T8.Asc77.Thompson.exists_orderOf_four ctx.hΩ hW ρS.hR
  have hwsK : ws ∈ ρS.K ⊓ W := ⟨ρS.hRK.1 hws.1, hws.2⟩
  have hws2 : ws * ws = zS := sq_eq_involution_of_orderOf_four hzS hwsK.1 hws4
  have hzSW : zS ∈ W := hws2 ▸ W.mul_mem hws.2 hws.2
  have hxa := muTabElt_mem ρa
  have hxc := muTabElt_mem ρc
  have hxS := muTabElt_mem ρS
  have hzSt : zS ≠ t := by
    intro heq
    subst heq
    have hS' : ρS.K ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K := ⟨hSΩ, zS, hd.hz, hzS⟩
    rw [← hperp] at hS'
    rcases hS' with h | h
    · exact hconn (by
        rw [(Q3T6.Mu.muTabElt_eq_iff hP hW ρa ρS).mpr (by rw [hρa]; exact h.symm)]
        exact Relation.ReflTransGen.refl)
    · have hne : ρa.K ≠ ρS.K := by
        rw [hρa]; exact fun h' => hconn (by
          rw [(Q3T6.Mu.muTabElt_eq_iff hP hW ρa ρS).mpr (by rw [hρa]; exact h')]
          exact Relation.ReflTransGen.refl)
      exact hconn (Star3T.conn_of_commute hxa hxS
        ((Q3T6.Mu.muTab_commute_iff hP hW ρa ρS hne).mpr (by rw [hρa]; exact h)))
  have hcS : ρc.K ≠ ρS.K := by
    intro h
    apply hconn
    have h' : muTabElt ρc = muTabElt ρS := (Q3T6.Mu.muTabElt_eq_iff hP hW ρc ρS).mpr h
    exact (Star3T.conn_of_commute hxa hxc cac).trans (by rw [h']; exact Relation.ReflTransGen.refl)
  have hstar : ρS.K ∈ omegaStarNbr (CoreAssembly.conjClass (tightCore R)) ρc.K :=
    Q3T6.Mu.muTab_omegaStar hP hW ρc ρS hcS
  refine ⟨ρS.K, hSΩ, hSC, by rw [hρc] at hstar; exact hstar, zS, hzS, hzSW, hzSt⟩

end Adapted

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
