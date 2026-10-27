module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinMuPf3D
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf10U3
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf9Lie
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinMuLayer
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinMuPf3A
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinMuPf3C
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinMuSetting

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinMu

namespace Pf3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Asc77.Star3T CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.ClassicalInvolution.Asc77.MuTab (muTabElt muTabElt_mem)

section Main

theorem exists_rep_of_mem_muDeltaCent {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {W : Subgroup G} {u : G} {x : ↥(muGroup Ω W)} (hx : x ∈ muDeltaCent Ω W u) :
    ∃ ρ : Rep Ω W, ρ.R ≤ Subgroup.centralizer ({u} : Set G) ∧ muTabElt ρ = x := by
  obtain ⟨T, ⟨hTD, hTu⟩, r, hrT, hrW, hxr⟩ := hx
  obtain ⟨K₀, hK₀, hTK⟩ := exists_isSylow2In_of_mem_RSet hTD.1
  exact ⟨⟨K₀, T, r, hK₀, hTD, hTK, hrT, hrW⟩, hTu, Subtype.ext hxr.symm⟩

variable {n : ℕ}

theorem transY_of_witness (hT4 : Thm4RTwinBelow 3 n) {Y : Type} [Group Y] [Finite Y]
    {R : Subgroup Y} {S : Sylow 2 R} {t₀ : Y} {K K' J W : Subgroup Y} {z u t : Y}
    (s : Setting n R S t₀ K K' z u J t W)
    (hne : dComp (CoreAssembly.conjClass (tightCore R)) K ≠
      dstarComp (CoreAssembly.conjClass (tightCore R)) K)
    (hTW : ThompsonWitness (CoreAssembly.conjClass (tightCore R)) K K' z u J) :
    ∀ M ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) u,
      ∀ N ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) u,
        ∃ g : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) u) ⧸
          classicalInvolutionOddCore ↥(coreHull (CoreAssembly.conjClass (tightCore R)) u),
            conjSub g M = N := by
  intro M hM N hN
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hf := s.data.frame
  have hΩ : HypOmegaGen Ω := s.core.hyp
  obtain ⟨h2, hq, hA⟩ := setup_members s
  have hc2 : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hf.hu2
  have hlt : Nat.card (↥(coreHull Ω u) ⧸ classicalInvolutionOddCore ↥(coreHull Ω u)) < n :=
    s.core.card ▸ card_secQuot_lt (not_mem_center_of_ne_one s hf.hu1)
  have hS := q8Section_secFam hΩ hc2 h2 hq hA
  have h4' := hT4 _ hlt _ hS.hyp hS.two hS.q8 hS.aEmpty hS.oddFree
  have hP : Q3CL.PartIHypG Ω := TwinPerp.partIHypG s.core
  have : Fact (Q3CL.ClassicalClause Ω) := ⟨hP.cls⟩
  have hK : K ∈ Ω := hf.mem
  have hK'Ω : K' ∈ Ω := hf.hK'.1
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hf.hz hf.hK'
  obtain ⟨W', hW', ρa, ρb, ρc, w, v, hKa, hKb, hKc, hw, hv, hw2, hv2, huv⟩ :=
    id hTW
  have ctx := Q3CL.T8.ctxOf hP hW'
  have hnc : ¬ DbarConnected Ω W' := Q3T6.Mu.thompsonGraphAll hP hK hne hW'
  have n12 : K' ∈ omegaNbr Ω K :=
    Q3.Q3CL.T3.twin_mem_omegaNbr hP.hyp hK hK'Ω hf.hne hf.hz hzK'
  have n13 : J ∈ omegaNbr Ω K := hf.hJ.2 K (mem_twinSet_self hK hf.hz)
  have n23 : J ∈ omegaNbr Ω K' := hf.hJ.2 K' hf.hK'
  have h12 : ρb.K ∈ omegaNbr Ω ρa.K := by rw [hKa, hKb]; exact n12
  have h13 : ρc.K ∈ omegaNbr Ω ρa.K := by rw [hKa, hKc]; exact n13
  have h23 : ρc.K ∈ omegaNbr Ω ρb.K := by rw [hKb, hKc]; exact n23
  have cab : muTabElt ρa * muTabElt ρb = muTabElt ρb * muTabElt ρa :=
    Subtype.ext (Q3T6.Mu.ctx_comm_of_omega ctx ρa ρb h12)
  have cac : muTabElt ρa * muTabElt ρc = muTabElt ρc * muTabElt ρa :=
    Subtype.ext (Q3T6.Mu.ctx_comm_of_omega ctx ρa ρc h13)
  have hab : muTabElt ρa ≠ muTabElt ρb := fun h => h12.2.1 (by
    have := ctx.K_eq_of_img_eq ρa ρb (congrArg Subtype.val h)
    exact this.symm)
  have hac : muTabElt ρa ≠ muTabElt ρc := fun h => h13.2.1 (by
    have := ctx.K_eq_of_img_eq ρa ρc (congrArg Subtype.val h)
    exact this.symm)
  have hbc : muTabElt ρb ≠ muTabElt ρc := fun h => h23.2.1 (by
    have := ctx.K_eq_of_img_eq ρb ρc (congrArg Subtype.val h)
    exact this.symm)
  have hza : IsUniqueInvolution ρa.K z := by rw [hKa]; exact hf.hz
  have hzb : IsUniqueInvolution ρb.K z := by rw [hKb]; exact hzK'
  have hwa : w ∈ ρa.K ⊓ W' := by rw [hKa]; exact hw
  have hvb : v ∈ ρb.K ⊓ W' := by rw [hKb]; exact hv
  have hwR : w ∈ ρa.R ⊓ W' := by
    rw [(Q3CL.Thompson.inf_W_of_mem_D hΩ hW' ρa.hR ρa.hK ρa.hRK).1]; exact hwa
  have hvR : v ∈ ρb.R ⊓ W' := by
    rw [(Q3CL.Thompson.inf_W_of_mem_D hΩ hW' ρb.hR ρb.hK ρb.hRK).1]; exact hvb
  have hw4 : orderOf w = 4 := orderOf_four_of_sq hw2 hza.sq hza.ne_one
  have hv4 : orderOf v = 4 := orderOf_four_of_sq hv2 hza.sq hza.ne_one
  obtain ⟨ψ, hψ⟩ := perm_four_twin hP hW' hnc hab hac hbc cab cac hwR hvR hw4 hv4
  subst huv
  have huW : w * v ∈ W' := W'.mul_mem hwa.2 hvb.2
  have hcl : ∀ ρ σ : Rep Ω W', ρ.R ≤ Subgroup.centralizer ({w * v} : Set Y) →
      σ.R ≤ Subgroup.centralizer ({w * v} : Set Y) →
      muTabElt ρ ∈ muDeltaCent Ω W' (w * v) → muTabElt σ ∈ muDeltaCent Ω W' (w * v) →
      ∃ g : ↥(coreHull Ω (w * v)) ⧸ classicalInvolutionOddCore ↥(coreHull Ω (w * v)),
        conjSub g (secImg Ω (w * v) ρ.K) = secImg Ω (w * v) σ.K := by
    intro ρ σ hρu hσu hρE hσE
    have hρcl : muTabElt ρ ∈ Subgroup.closure (muDeltaCent Ω W' (w * v)) :=
      Subgroup.subset_closure hρE
    have hσcl : muTabElt σ ∈ Subgroup.closure (muDeltaCent Ω W' (w * v)) :=
      Subgroup.subset_closure hσE
    have hs₁ := (hψ _ hρcl).mp hρE
    have hs₂ := (hψ _ hσcl).mp hσE
    obtain ⟨s₃, hs₃, h31, h32⟩ := exists_swap_noncomm hs₁ hs₂
    have e3 : ψ (ψ.symm s₃) = s₃ := ψ.apply_symm_apply s₃
    have hx₃E : ((ψ.symm s₃ : ↥(Subgroup.closure (muDeltaCent Ω W' (w * v)))) :
        ↥(muGroup Ω W')) ∈ muDeltaCent Ω W' (w * v) := by
      refine (hψ _ (ψ.symm s₃).2).mpr ?_
      rw [show (⟨((ψ.symm s₃ : ↥(Subgroup.closure (muDeltaCent Ω W' (w * v)))) : ↥(muGroup Ω W')),
        (ψ.symm s₃).2⟩ : ↥(Subgroup.closure (muDeltaCent Ω W' (w * v)))) = ψ.symm s₃ from rfl, e3]
      exact hs₃
    obtain ⟨τ, hτu, hτx⟩ := exists_rep_of_mem_muDeltaCent hx₃E
    have htq : ∀ ρ : Rep Ω W', ρ.R ≤ Subgroup.centralizer ({w * v} : Set Y) →
        ρ.K ∈ tqMembers3 Ω (w * v) := fun ρ hρ =>
      ⟨ρ.hK, TwinADescent3.mem_tq_of_sylCent hΩ h2 ρ.hK ⟨ρ.R, ρ.hRK, hρ⟩⟩
    have conj_of_nc : ∀ ρ σ : Rep Ω W', ρ.R ≤ Subgroup.centralizer ({w * v} : Set Y) →
        σ.R ≤ Subgroup.centralizer ({w * v} : Set Y) → ρ.img * σ.img ≠ σ.img * ρ.img →
        ∃ g : ↥(coreHull Ω (w * v)) ⧸ classicalInvolutionOddCore ↥(coreHull Ω (w * v)),
          conjSub g (secImg Ω (w * v) ρ.K) = secImg Ω (w * v) σ.K := by
      intro ρ σ hρ hσ hnc'
      by_contra hno
      exact not_commutes_secImg ctx h2 hq hc2 huW ρ σ hρ hσ hnc'
        (h4' _ (secImg_mem_secFam (htq ρ hρ)) _ (secImg_mem_secFam (htq σ hσ)) hno)
    have hnc₁ : ρ.img * τ.img ≠ τ.img * ρ.img := by
      intro h
      apply h31
      have hcomm : (⟨muTabElt ρ, hρcl⟩ : ↥(Subgroup.closure (muDeltaCent Ω W' (w * v)))) *
          ψ.symm s₃ = ψ.symm s₃ * ⟨muTabElt ρ, hρcl⟩ := by
        apply Subtype.ext
        show muTabElt ρ * ((ψ.symm s₃ : ↥(Subgroup.closure (muDeltaCent Ω W' (w * v)))) :
          ↥(muGroup Ω W')) = ((ψ.symm s₃ : ↥(Subgroup.closure (muDeltaCent Ω W' (w * v)))) :
          ↥(muGroup Ω W')) * muTabElt ρ
        rw [← hτx]
        exact Subtype.ext h
      have := congrArg ψ hcomm
      rw [map_mul, map_mul, e3] at this
      exact this.symm
    have hnc₂ : τ.img * σ.img ≠ σ.img * τ.img := by
      intro h
      apply h32
      have hcomm : ψ.symm s₃ * (⟨muTabElt σ, hσcl⟩ : ↥(Subgroup.closure (muDeltaCent Ω W' (w * v)))) =
          ⟨muTabElt σ, hσcl⟩ * ψ.symm s₃ := by
        apply Subtype.ext
        show ((ψ.symm s₃ : ↥(Subgroup.closure (muDeltaCent Ω W' (w * v)))) :
          ↥(muGroup Ω W')) * muTabElt σ = muTabElt σ *
          ((ψ.symm s₃ : ↥(Subgroup.closure (muDeltaCent Ω W' (w * v)))) : ↥(muGroup Ω W'))
        rw [← hτx]
        exact Subtype.ext h
      have := congrArg ψ hcomm
      rw [map_mul, map_mul, e3] at this
      exact this
    obtain ⟨g₁, hg₁⟩ := conj_of_nc ρ τ hρu hτu hnc₁
    obtain ⟨g₂, hg₂⟩ := conj_of_nc τ σ hτu hσu hnc₂
    exact ⟨g₂ * g₁, by rw [conjSub_mul, hg₁, hg₂]⟩
  have hrep : ∀ J₀ ∈ tqMembers3 Ω (w * v), ∃ ρ : Rep Ω W',
      ρ.R ≤ Subgroup.centralizer ({w * v} : Set Y) ∧ muTabElt ρ ∈ muDeltaCent Ω W' (w * v) ∧
      ∃ g : ↥(coreHull Ω (w * v)) ⧸ classicalInvolutionOddCore ↥(coreHull Ω (w * v)),
        conjSub g (secImg Ω (w * v) J₀) = secImg Ω (w * v) ρ.K := by
    intro J₀ hJ₀
    obtain ⟨R₀, hR₀, hR₀c⟩ := TwinADescent.exists_sylow_centralizer_of_tq hc2 hJ₀.2
    have hR₀S : R₀ ∈ RSet Ω := mem_RSet_of_isSylow2In hJ₀.1 hR₀
    obtain ⟨y, hy, hTD, hTc⟩ := exists_conj_mem_D hΩ hW' huW hR₀S hR₀c
    have hJy : conjSub y J₀ ∈ Ω := hΩ.conjInvariant y J₀ hJ₀.1
    have hTK : IsSylow2In (conjSub y R₀) (conjSub y J₀) := hR₀.conj y
    refine ⟨Q3CL.T8.mkRep hP hW' hJy hTD hTK, hTc, ?_, ?_⟩
    · exact ⟨conjSub y R₀, ⟨hTD, hTc⟩, _, (Q3CL.T8.mkRep hP hW' hJy hTD hTK).hr,
        (Q3CL.T8.mkRep hP hW' hJy hTD hTK).hrW, rfl⟩
    · exact exists_conj_secImg (rLayer_le_coreLayer hΩ h2 hc2 hy)
  obtain ⟨J₁, hJ₁, rfl⟩ := exists_of_mem_secFam hM
  obtain ⟨J₂, hJ₂, rfl⟩ := exists_of_mem_secFam hN
  obtain ⟨ρ₁, hρ₁u, hρ₁E, g₁, hg₁⟩ := hrep J₁ hJ₁
  obtain ⟨ρ₂, hρ₂u, hρ₂E, g₂, hg₂⟩ := hrep J₂ hJ₂
  obtain ⟨g₃, hg₃⟩ := hcl ρ₁ ρ₂ hρ₁u hρ₂u hρ₁E hρ₂E
  refine ⟨g₂⁻¹ * g₃ * g₁, ?_⟩
  rw [conjSub_mul, conjSub_mul, hg₁, hg₃, ← hg₂, conjSub_inv_conjSub]

end Main

end Pf3

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinMu
