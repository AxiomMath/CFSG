module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf91MuS4Loc
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf91MuS4Sec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf91MuS4G
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf29ExitCases
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf31Residual
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf9Layer

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
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open scoped commutatorElement

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

section MuS4

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ K₄ : Subgroup Y} {u₁ u₂ u₃ : Y}

theorem v3_secPair (hStd : V3Std n Y R S t K K' K₃ u₁ u₂ u₃)
    (hF : FourthTwin (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃ K₄)
    (h2g : ∀ J ∈ CoreAssembly.conjClass (tightCore R), IsPGroup 2 ↥J) :
    (∀ M ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
        M ∈ omegaNbr (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))
          (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃) →
        M = secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₄) ∧
      (∀ M ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
        M ∈ omegaNbr (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))
          (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₄) →
        M = secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃) ∧
      secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₄ ∈
        omegaNbr (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))
          (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃) ∧
      K₃ ≤ Subgroup.centralizer ({u₁ * u₂} : Set Y) := by
  have hd := hStd.datum
  have hΩ := hd.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers (u₁ * u₂)) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.sq_12
  obtain ⟨hmem, hmem4⟩ := v3_tq_members hStd hF
  obtain ⟨-, ⟨R₃, h3, c3⟩, ⟨R₄, h4', c4⟩⟩ := v3_layerBasics hStd hF
  have hK₄ := hF.1
  have hp3 := v3_perp_tq hStd hd.hK₃ hK₄ (Ne.symm hF.2.2.2.1) hd.hK₃K hd.hK₃K' hF.2.1 hF.2.2.1
  have hp4 := v3_perp_tq hStd hK₄ hd.hK₃ hF.2.2.2.1 hF.2.1 hF.2.2.1 hd.hK₃K hd.hK₃K'
  have hperp3 := kPerp_datum hStd.perp hd.hK₃.1 hd.hzK₃
  have hnb : ∀ M ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
      M ∈ omegaNbr (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))
        (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃) →
      M = secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₄ := by
    intro M hM hn
    obtain ⟨J, hJq, rfl⟩ := exists_of_mem_secFam hM
    exact TwinLayerGen.secNbr_eq_of_perp hΩ hc2 hmem hJq (K' := K₄)
      (fun J₀ hJ₀ hJ₀p => hp3 J₀ hJ₀ (by rw [hperp3] at *; exact hJ₀p)) hn
  have hnb' : ∀ M ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
      M ∈ omegaNbr (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))
        (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₄) →
      M = secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃ := by
    intro M hM hn
    obtain ⟨J, hJq, rfl⟩ := exists_of_mem_secFam hM
    exact TwinLayerGen.secNbr_eq_of_perp hΩ hc2 hmem4 hJq (K' := K₃)
      (fun J₀ hJ₀ hJ₀p => hp4 J₀ hJ₀ hJ₀p) hn
  have hz4 : IsUniqueInvolution K₄ t := isUniqueInvolution_of_mem_twinSet hd.hz hF.1
  have hn34 : K₃ ≤ Subgroup.normalizer (K₄ : Set Y) :=
    Sec6Gen.le_normalizer_of_twin hΩ hd.hK₃.1 hF.1.1 (Ne.symm hF.2.2.2.1) hd.hzK₃ hz4
  have hn43 : K₄ ≤ Subgroup.normalizer (K₃ : Set Y) :=
    Sec6Gen.le_normalizer_of_twin hΩ hF.1.1 hd.hK₃.1 hF.2.2.2.1 hz4 hd.hzK₃
  have hcomm34 : Commutes K₃ K₄ :=
    Sec6Gen.commutes_of_twin_of_isPGroup hΩ hd.hK₃.1 hF.1.1 (Ne.symm hF.2.2.2.1) hd.hzK₃ hz4 le_rfl
      le_rfl ((h2g K₃ hd.hK₃.1).to_sup_of_normal_right' (h2g K₄ hF.1.1) hn34)
  have hK₃C : K₃ ≤ Subgroup.centralizer ({u₁ * u₂} : Set Y) := by
    have hR₃ : K₃ = R₃ := h3.2.2 K₃ le_rfl (h2g K₃ hd.hK₃.1) h3.1
    exact hR₃ ▸ c3
  exact ⟨hnb, hnb',
    omegaNbr_secImg hΩ hc2 hmem hmem4 h3 h4' c3 c4
      (fun x hx y hy => hcomm34 x (h3.1 hx) y (h4'.1 hy)) (fun y hy => hn43 (h4'.1 hy)), hK₃C⟩

theorem v3SecMuS4_adapted (hin : V3ExitIn n R S t K K' K₃ u₁ u₂ u₃ K₄)
    {W : Subgroup Y} (hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R)))
    (hKD : K ∈ DSet (CoreAssembly.conjClass (tightCore R)) W)
    (hK'D : K' ∈ DSet (CoreAssembly.conjClass (tightCore R)) W)
    (hK₃D : K₃ ∈ DSet (CoreAssembly.conjClass (tightCore R)) W) (hu₁ : u₁ ∈ W) (hu₂ : u₂ ∈ W) :
    ∀ W' ∈ WSet (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)),
      MuIsoS4 (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) W' := by
  intro W' hW'
  obtain ⟨hStd, hF, -, h2g, -⟩ := hin
  have hd := hStd.datum
  have hΩ := hd.hyp
  have hC := CoreData.of_S hStd.perp.core
  have hP : Q3CL.PartIHypG (CoreAssembly.conjClass (tightCore R)) := hC.partIHypG
  have hc2 : IsPGroup 2 (Subgroup.zpowers (u₁ * u₂)) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.sq_12
  obtain ⟨hmem, hmem4⟩ := v3_tq_members hStd hF
  obtain ⟨hnb, hnb', hedge, hK₃C⟩ := v3_secPair hStd hF h2g
  obtain ⟨L, hLΩ, hLC, hLstar, zL, hzL, hzLW, hzLt⟩ :=
    exists_member_adapted hStd h2g hW hKD hK'D hK₃D hu₁ hu₂
  have hLmem : L ∈ tqMembers3 (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) :=
    mem_tqMembers3_of_le_centralizer hLΩ hLC
  have hz4 : IsUniqueInvolution K₄ t := isUniqueInvolution_of_mem_twinSet hd.hz hF.1
  have htW : t ∈ W := hd.sq₁ ▸ W.mul_mem hu₁ hu₁
  have hcomm : zL * t = t * zL := (Q3CL.T8.ctxOf hP hW).comm_W _ hzLW _ htW
  have hne3 : secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) L ≠
      secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃ :=
    Sec.secImg_ne_of_involution hΩ hc2 hLmem hmem hzL hd.hzK₃ hzLt hcomm
  have hne4 : secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) L ≠
      secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₄ :=
    Sec.secImg_ne_of_involution hΩ hc2 hLmem hmem4 hzL hz4 hzLt hcomm
  have hstar := Sec.omegaStarNbr_secImg hΩ hc2 hmem hLmem (h2g _ hd.hK₃.1) (h2g _ hLΩ) hK₃C hLC
    hLstar hne3
  have hS := layer_q8Section hStd.perp hd.sq_12
  have h2Φ : ∀ M ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
      IsPGroup 2 M := by
    intro M hM
    obtain ⟨J, hJ, rfl⟩ := exists_of_mem_secFam hM
    exact secImg_isPGroup' (h2g J hJ.1)
  have hPΦ : Q3CL.PartIHypG (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) :=
    ⟨hS.hyp, classicalClause_of_two hS.hyp h2Φ, hS.aEmpty⟩
  have hA := secImg_mem_secFam hmem
  have hB := secImg_mem_secFam hmem4
  have hone : ∀ a ∈ omegaNbr (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))
      (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃),
      ∀ b ∈ omegaNbr (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))
        (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃), a = b :=
    fun a ha b hb => (hnb a ha.1 ha).trans (hnb b hb.1 hb).symm
  have hcomp : dComp (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))
      (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃) ≠
      dstarComp (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))
        (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃) := by
    intro heq
    have hLd : secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) L ∈
        dstarComp (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))
          (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃) :=
      Relation.ReflTransGen.single ⟨secImg_mem_secFam hLmem, Or.inl hstar⟩
    rw [← heq] at hLd
    rcases Sec.dComp_subset_pair hS.hyp hA hB hnb hnb' hLd with h | h
    · exact hne3 h
    · exact hne4 h
  exact Loc.muIsoS4_of_local hPΦ hW' hA hedge hone hcomp

end MuS4

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
