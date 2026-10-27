module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23WEW
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf91MuS4
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3WFB0Sec

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open scoped commutatorElement
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

section B0Dat




variable {n : ℕ}

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ K₄ : Subgroup Y} {u₁ u₂ u₃ : Y}

theorem v3_secPartI (hin : V3ExitIn n R S t K K' K₃ u₁ u₂ u₃ K₄) :
    Q3CL.PartIHypG (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) ∧
      ∀ M ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂), IsPGroup 2 ↥M := by
  obtain ⟨hStd, hF, -, h2g, -⟩ := hin
  have hd := hStd.datum
  have hS := layer_q8Section hStd.perp hd.sq_12
  have h2Φ : ∀ M ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
      IsPGroup 2 M := by
    intro M hM
    obtain ⟨J, hJ, rfl⟩ := TwinDisc.exists_of_mem_secFam hM
    exact secImg_isPGroup' (h2g J hJ.1)
  exact ⟨⟨hS.hyp, classicalClause_of_two hS.hyp h2Φ, hS.aEmpty⟩, h2Φ⟩

theorem v3SecSwap_adapted (hin : V3ExitIn n R S t K K' K₃ u₁ u₂ u₃ K₄)
    {W : Subgroup Y} (hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R)))
    (hKD : K ∈ DSet (CoreAssembly.conjClass (tightCore R)) W)
    (hK'D : K' ∈ DSet (CoreAssembly.conjClass (tightCore R)) W)
    (hK₃D : K₃ ∈ DSet (CoreAssembly.conjClass (tightCore R)) W) (hu₁ : u₁ ∈ W) (hu₂ : u₂ ∈ W)
    {V : Subgroup (TwinPerpV3.LSec (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))}
    (hV : V ∈ WSet (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))) :
    ∃ e : ↥(muGroup (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) V) ≃*
        Equiv.Perm (Fin 4),
      ∀ x, x ∈ Thompson.muDelta (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) V ↔
        (e x).IsSwap := by

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
  have hne3 : TwinDisc.secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) L ≠
      TwinDisc.secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃ :=
    Sec.secImg_ne_of_involution hΩ hc2 hLmem hmem hzL hd.hzK₃ hzLt hcomm
  have hne4 : TwinDisc.secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) L ≠
      TwinDisc.secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₄ :=
    Sec.secImg_ne_of_involution hΩ hc2 hLmem hmem4 hzL hz4 hzLt hcomm
  have hstar := Sec.omegaStarNbr_secImg hΩ hc2 hmem hLmem (h2g _ hd.hK₃.1) (h2g _ hLΩ) hK₃C hLC
    hLstar hne3
  have hS := layer_q8Section hStd.perp hd.sq_12
  have h2Φ : ∀ M ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
      IsPGroup 2 M := by
    intro M hM
    obtain ⟨J, hJ, rfl⟩ := TwinDisc.exists_of_mem_secFam hM
    exact secImg_isPGroup' (h2g J hJ.1)
  have hPΦ : Q3CL.PartIHypG (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) :=
    ⟨hS.hyp, classicalClause_of_two hS.hyp h2Φ, hS.aEmpty⟩
  have hA := TwinDisc.secImg_mem_secFam hmem
  have hB := TwinDisc.secImg_mem_secFam hmem4
  have hone : ∀ a ∈ omegaNbr (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))
      (TwinDisc.secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃),
      ∀ b ∈ omegaNbr (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))
        (TwinDisc.secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃), a = b :=
    fun a ha b hb => (hnb a ha.1 ha).trans (hnb b hb.1 hb).symm
  have hcomp : dComp (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))
      (TwinDisc.secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃) ≠
      dstarComp (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))
        (TwinDisc.secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃) := by
    intro heq
    have hLd : TwinDisc.secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) L ∈
        dstarComp (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))
          (TwinDisc.secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃) :=
      Relation.ReflTransGen.single ⟨secImg_mem_secFam hLmem, Or.inl hstar⟩
    rw [← heq] at hLd
    rcases Sec.dComp_subset_pair hS.hyp hA hB hnb hnb' hLd with h | h
    · exact hne3 h
    · exact hne4 h
  exact exists_swap_of_local hPΦ hV hA hedge hone hcomp


theorem v3_secKlein (hin : V3ExitIn n R S t K K' K₃ u₁ u₂ u₃ K₄)
    {W : Subgroup Y} (hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R)))
    (hKD : K ∈ DSet (CoreAssembly.conjClass (tightCore R)) W)
    (hK'D : K' ∈ DSet (CoreAssembly.conjClass (tightCore R)) W)
    (hK₃D : K₃ ∈ DSet (CoreAssembly.conjClass (tightCore R)) W) (hu₁ : u₁ ∈ W) (hu₂ : u₂ ∈ W)
    {V : Subgroup (TwinPerpV3.LSec (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))}
    (hV : WSet (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) = {V}) :
    ∃ z₀ j : TwinPerpV3.LSec (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
      IsUniqueInvolution (TwinDisc.secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃) z₀ ∧
        ∀ J' ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
          ∀ z' : TwinPerpV3.LSec (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
            IsUniqueInvolution J' z' → z' = z₀ ∨ z' = j ∨ z' = z₀ * j := by
  obtain ⟨hPΦ, h2Φ⟩ := v3_secPartI hin
  have hVW : V ∈ WSet (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) := by
    rw [hV]; exact Set.mem_singleton V
  obtain ⟨e, he⟩ := v3SecSwap_adapted hin hW hKD hK'D hK₃D hu₁ hu₂ hVW
  obtain ⟨hStd, hF, -, h2g, -⟩ := hin
  have hd := hStd.datum
  have hΩ := hd.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers (u₁ * u₂)) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.sq_12
  obtain ⟨hmem, hmem4⟩ := v3_tq_members hStd hF
  obtain ⟨-, -, hedge, -⟩ := v3_secPair hStd hF h2g
  have hz4 : IsUniqueInvolution K₄ t := isUniqueInvolution_of_mem_twinSet hd.hz hF.1
  obtain ⟨htC, htY, hinv3⟩ := TwinDisc.isUniqueInvolution_secImg hΩ hc2 hmem hd.hzK₃
  obtain ⟨htC4, htY4, hinv4⟩ := TwinDisc.isUniqueInvolution_secImg hΩ hc2 hmem4 hz4
  have hVn : V.Normal := TwinPerp23.W.wset_normal (TwinDisc.hypOmegaGen_secFam hΩ hc2) hV
  obtain ⟨j, -, -, hj⟩ := sec_klein_involutions hPΦ hVW hVn h2Φ (TwinDisc.secImg_mem_secFam hmem)
    hinv3 hinv4 hedge he
  exact ⟨_, j, hinv3, hj⟩

end B0Dat

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF
