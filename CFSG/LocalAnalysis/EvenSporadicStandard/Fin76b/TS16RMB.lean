module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RMA
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYLD
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYKBar
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYeD
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYR
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16R9
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RNKer
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYI
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYPInd
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYPG
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYPM
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYPE
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8EFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWIso2

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

namespace OuterS16Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {Q : Sylow 2 G} {x : G} {B : Subgroup G} {β : G} {S : Subgroup G}
  (c : OuterS16Ctx G L z t T E Q x B β S)

include c

theorem loc
    (hKB : S16KBar G L z t E β S) (hH : Harada75E8) :
    ∃ (M Q' P : Subgroup G), Q' ≤ M ∧ IsPGroup 2 Q' ∧ ¬ 2 ∣ (Q'.subgroupOf M).index ∧ z ∈ Q' ∧
      P ≤ Q' ∧ P.relIndex Q' = 2 ∧ z ∉ P ∧
      (∃ R : Subgroup G, IsPGroup 2 R ∧ R ≤ M ⊓ centralizer ({z} : Set G) ∧ Nat.card R = 512) ∧
      (∀ y ∈ Q', (∃ g : G, y = g * z * g⁻¹) →
        Nat.card ↥(Q' ⊓ centralizer ({y} : Set G)) = 512 → ∃ m ∈ M, y = m * z * m⁻¹) ∧
      ∀ η ∈ P, η * η = 1 → η ≠ 1 →
        ∃ R : Subgroup G, IsPGroup 2 R ∧ R ≤ centralizer ({η} : Set G) ∧ 512 < Nat.card R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcfg := c.hyp.outerE.cfg
  have hz2 : z * z = 1 := hcfg.z_sq
  have ht2 : t * t = 1 := hcfg.t_sq
  obtain ⟨e⟩ := hKB.S_dih
  obtain ⟨s, hsS, hord, hzs, hs4, hgen⟩ := exists_dihedral_gen e c.zS c.t_mem_S hz2 hcfg.z_ne
    hcfg.z_ne_t ht2 hcfg.t_ne c.t_comm_S
  have hS : S16Gen S s z t := s16Gen_of_gen hsS c.zS hord hzs hs4 hz2 hgen c.card16
  obtain ⟨σ₀, v, ξ, hD0, hD1⟩ := c.hyp.exists_lData
  obtain ⟨σ, hD, hσs⟩ := exists_sigma_five hS hD0 hD1 (hKB.sigma_s σ₀ v ξ hD0 s hsS hord)
  have hξ := hKB.zsigma σ v ξ hD s hsS hord hσs
  obtain ⟨R, hR2, hRξ, hξR, h5⟩ := c.exists_R hS hD hσs
  obtain ⟨V0, hV0L, hV02, hV0max, hV0D⟩ := hD.V0
  obtain ⟨g₀, hg₀⟩ := c.z_conj_sigma_five hH hD.σ_sq hD.σ_z hD.σ_notL hV0L hV02 hV0max hV0D hξ
    hR2 hRξ hξR h5
  obtain ⟨K0, -, hcls⟩ := hKB.K0
  have hE69 : EFacts69 E t := c.hyp.outerE.eFacts69 c.hyp.wFacts c.hyp.sporadic
  have h9 := c.involutions_W_conj hE69 hS hD hcls
  obtain ⟨eD, he1, he4, he2, hza, hzb, -⟩ := exists_eD hS c.card16
  obtain ⟨eltE, hlab⟩ : ∃ eltE : ℕ → G, ELabelling E t W16.mulE0 W16.eT eltE := by
    rcases c.hyp.outerE.exists_eLabelling_sporadic c.hyp.wFacts c.hyp.sporadic with
      ⟨elt, hl⟩ | ⟨elt, hl⟩
    · exact ⟨elt, W16.eLab_of_J2 hl⟩
    · exact ⟨_, W16.eLab_of_J3 hl⟩
  have hDS : Dsub s z ≤ S := Dsub_le hS.hs hS.hzS
  have hcomm : ∀ d ∈ Dsub s z, ∀ e ∈ E, d * e = e * d := fun d hd e he =>
    (mem_centralizer_iff.1 (c.SC (hDS hd)) e he).symm
  have hctx : W16.DECtx (Dsub s z) E eD t eltE := ⟨hlab, t_mem_Dsub hS.hs4, hcomm⟩
  haveI hNm := normal_sup_subgroupOf_normalizer (Dsub s z) E
  have hσW : σ ∈ normalizer ((Dsub s z ⊔ E : Subgroup G) : Set G) :=
    c.sigma_norm_W hS hD.σ_sq hD.σ_z hσs hD.σ_E
  have hσE : ∀ e ∈ E, σ * e * σ⁻¹ ∈ E := fun e he => (mem_normalizer_iff.1 hD.σ_E e).1 he
  have hσa : σ * sElt eD 1 * σ⁻¹ = sElt eD 1 := by
    rw [he1]
    exact sigma_act_a hS.hs8 hσs
  have hσb : σ * sElt eD 4 * σ⁻¹ = sElt eD 2 * sElt eD 4 := by
    rw [he4, he2, ← hS.hs4]
    exact sigma_act_b hD.σ_z hσs
  obtain ⟨hE0, hD0card, hD0gen⟩ := partI_E0D_G hctx hσW hD.σ_sq hσa hσb hσE hD.card_CE
    (hD.exists_fixed_invol hcfg.t_ne)
  obtain ⟨g, hgM, hgz⟩ := c.fusion_in_normW hS hD.σ_sq hD.σ_z hD.σ_notL hD.σ_E hσs h9 hE0 hD0card
    hD0gen hg₀
  obtain ⟨N, hNodd, hNcov, -, hker⟩ := cent_W_split c e hsS c.zS hS.hs8 hS.hs4 hz2 hS.hzs hS.hord
    hS.hgen
  have hzM : z ∈ normalizer ((Dsub s z ⊔ E : Subgroup G) : Set G) :=
    mem_normalizer_sup_of_inv hz2
      (normalizes_Dsub hS (Subgroup.le_normalizer hS.hzS) (by rw [mul_assoc, mul_inv_cancel,
        mul_one]))
      (fun e he => by
        have h1 : z * e = e * z := (mem_centralizer_iff.1 (c.SC hS.hzS) e he).symm
        rw [h1, mul_assoc, mul_inv_cancel, mul_one]
        exact he)
  have hzE : ∀ e ∈ E, z * e = e * z := fun e he =>
    (mem_centralizer_iff.1 (c.SC hS.hzS) e he).symm
  have hΓ0 := inducedStab_subgroupOf (fun α hD' hE' => c.induced_stab hS α hD' hE')
  obtain ⟨Q', P', hP⟩ : ∃ Q' P : Subgroup ↥(normalizer ((Dsub s z ⊔ E : Subgroup G) : Set G)),
      _ := partI_clauses_M hctx hΓ0 hNodd hNcov hker hz2 hzM hzE hza hzb hσW hσa ⟨g, hgM, hgz⟩
  have hcard : ∀ (g : G) (R : Subgroup G), IsPGroup 2 R →
      R ≤ centralizer ({g * z * g⁻¹} : Set G) → Nat.card ↥R ≤ 512 := by
    intro g R hR hRc
    have h1 := hcfg.card_le_of_two_subgroup_cent_conj hR hRc
    rw [c.hyp.cardT] at h1
    exact h1
  obtain ⟨Q'', P'', hQP⟩ := clauses_to_G hzM hz2 hcard ⟨Q', P', hP⟩
  exact ⟨normalizer ((Dsub s z ⊔ E : Subgroup G) : Set G), Q'', P'', hQP⟩

end OuterS16Ctx

end CFSG.EvenSporadicStandard.Fin76b
