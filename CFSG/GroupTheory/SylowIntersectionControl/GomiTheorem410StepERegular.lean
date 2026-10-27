module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410StepEBar
public import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410
import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410Lift
import CFSG.GroupTheory.SylowIntersectionControl.GomiOverCore
import CFSG.GroupTheory.SubnormalResidualTwo
import CFSG.CGT.PushingUpLit.CGT6.EmbQuotShort
import CFSG.Quasithin.Background.A4V
import TauCeti.GroupTheory.Elementary

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.RankThree.PartOne Subgroup
open scoped commutatorElement Pointwise

variable {Ω : Type} [Group Ω] [Finite Ω] {f : PSubgroupSelection 2 Ω}
  {hyp : Subgroup Ω → Prop} {G : Subgroup Ω}

private theorem pCoreOf_le_pCoreOf_of_le_ereg {H : Subgroup Ω} (hHG : H ≤ G)
    (hQH : pCoreOf 2 G ≤ H) : pCoreOf 2 G ≤ pCoreOf 2 H :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQH
    (hHG.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G)

omit [Finite Ω] in
private theorem gomiBarOf_mono_ereg {K L : Subgroup Ω} (hKL : K ≤ L) (hLG : L ≤ G) :
    gomiBarOf G K ≤ gomiBarOf G L := by
  rw [gomiBarOf_eq_map (hKL.trans hLG), gomiBarOf_eq_map hLG]
  exact Subgroup.map_mono (Subgroup.subgroupOf_mono G hKL)

omit [Finite Ω] in
private theorem gomiBarPre_normalizer_ereg {M K : Subgroup ↥(autOn G (gomiV G))}
    (hKn : M ≤ Subgroup.normalizer (K : Set ↥(autOn G (gomiV G)))) :
    gomiBarPre G M ≤ Subgroup.normalizer (gomiBarPre G K : Set Ω) := by
  have hHG : gomiBarPre G M ≤ G := gomiBarPre_le G M
  have hKG : gomiBarPre G K ≤ G := gomiBarPre_le G K
  have key : ∀ h ∈ gomiBarPre G M, ∀ x ∈ gomiBarPre G K,
      h * x * h⁻¹ ∈ gomiBarPre G K := by
    intro h hh x hx
    have hhG := hHG hh
    have hxG := hKG hx
    have hbarM : gomiBar G ⟨h, hhG⟩ ∈ M := by
      have hmem : gomiBar G ⟨h, hhG⟩ ∈ gomiBarOf G (gomiBarPre G M) := by
        rw [gomiBarOf_eq_map hHG]
        exact Subgroup.mem_map.mpr ⟨⟨h, hhG⟩, by rw [Subgroup.mem_subgroupOf]; exact hh, rfl⟩
      rwa [gomiBarOf_gomiBarPre G M] at hmem
    have hxbarK : gomiBar G ⟨x, hxG⟩ ∈ K := by
      have hmem : gomiBar G ⟨x, hxG⟩ ∈ gomiBarOf G (gomiBarPre G K) := by
        rw [gomiBarOf_eq_map hKG]
        exact Subgroup.mem_map.mpr ⟨⟨x, hxG⟩, by rw [Subgroup.mem_subgroupOf]; exact hx, rfl⟩
      rwa [gomiBarOf_gomiBarPre G K] at hmem
    have hconj : gomiBar G
        ⟨h * x * h⁻¹, G.mul_mem (G.mul_mem hhG hxG) (G.inv_mem hhG)⟩ =
        gomiBar G ⟨h, hhG⟩ * gomiBar G ⟨x, hxG⟩ * (gomiBar G ⟨h, hhG⟩)⁻¹ := by
      rw [show (⟨h * x * h⁻¹, G.mul_mem (G.mul_mem hhG hxG) (G.inv_mem hhG)⟩ : ↥G) =
        ⟨h, hhG⟩ * ⟨x, hxG⟩ * (⟨h, hhG⟩)⁻¹ by ext; rfl]
      simp only [map_mul, map_inv]
    have hmemK : gomiBar G
        ⟨h * x * h⁻¹, G.mul_mem (G.mul_mem hhG hxG) (G.inv_mem hhG)⟩ ∈ K := by
      rw [hconj]
      exact (Subgroup.mem_normalizer_iff.mp (hKn hbarM) _).mp hxbarK
    exact Subgroup.mem_map.mpr ⟨_, by rw [Subgroup.mem_comap]; exact hmemK, rfl⟩
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key h hh x
  · intro hx
    have := key h⁻¹ ((gomiBarPre G M).inv_mem hh) (h * x * h⁻¹) hx
    simpa [mul_assoc] using this

private theorem commutator_pCoreOf_map_le_gomiV_ereg (hchar : CharTwo G)
    {H : Subgroup Ω} (hHG : H ≤ G) (hQH : pCoreOf 2 G ≤ H)
    {B₀ : Subgroup ↥H} (hB₀ : IsAschbacherBlockGomi B₀) :
    ⁅pCoreOf 2 G, B₀.map H.subtype⁆ ≤ gomiV G :=
  (Subgroup.commutator_mono (pCoreOf_le_pCoreOf_of_le_ereg hHG hQH) le_rfl).trans
    ((IsAschbacherBlockGomi.commutator_map_le_gomiV hB₀).trans
      (gomiV_le_gomiV_of_pCoreOf_le hchar hHG hQH))

omit [Finite Ω] in
private theorem oResidualTwo_map_subtype_top_ereg {H : Subgroup Ω} {B₀ : Subgroup ↥H}
    (hres : oResidualTwo ↥B₀ = ⊤) : oResidualTwo ↥(B₀.map H.subtype) = ⊤ :=
  CFSG.CGT.PushingUpLit.CGT6.oResidualTwo_eq_top_of_surjective
    (B₀.equivMapOfInjective H.subtype H.subtype_injective).toMonoidHom
    (B₀.equivMapOfInjective H.subtype H.subtype_injective).surjective hres

private theorem isPGroup_ker_gomiBar_ereg
    (hCQ : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) = pCoreOf 2 G) :
    IsPGroup 2 (gomiBar G).ker := by
  rw [gomiBar_ker G]
  have hCeq : (Subgroup.centralizer (gomiV G : Set Ω)).subgroupOf G =
      (pCoreOf 2 G).subgroupOf G := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have hx' : (x : Ω) ∈ G ⊓ Subgroup.centralizer (gomiV G : Set Ω) := ⟨x.2, hx⟩
      rwa [hCQ] at hx'
    · intro hx
      have hx' : (x : Ω) ∈ G ⊓ Subgroup.centralizer (gomiV G : Set Ω) := by
        rw [hCQ]
        exact hx
      exact hx'.2
  rw [hCeq]
  exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G).comap_subtype (K := G)

private theorem isPGroup_gomiBarPre_pCoreOf_ereg
    (hCQ : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) = pCoreOf 2 G)
    (M : Subgroup ↥(autOn G (gomiV G))) :
    IsPGroup 2 (gomiBarPre G (pCoreOf 2 M)) := by
  have hpre : IsPGroup 2 ((pCoreOf 2 M).comap (gomiBar G)) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).comap_of_ker_isPGroup
      (gomiBar G) (isPGroup_ker_gomiBar_ereg hCQ)
  change IsPGroup 2 (((pCoreOf 2 M).comap (gomiBar G)).map G.subtype)
  exact hpre.map G.subtype

omit [Finite Ω] in
private theorem gomiBarOf_gomiV_eq_bot_ereg : gomiBarOf G (gomiV G) = ⊥ := by
  rw [gomiBarOf]
  have hbot : autOn (gomiV G) (gomiV G) = ⊥ :=
    CFSG.Quasithin.AutOn.autOn_eq_bot_of_le_centralizer fun v hv => by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact CFSG.Quasithin.A4.mul_comm_of_mem_omegaOneCenterOf hw hv
  rw [hbot]
  simp

private theorem gomiBarPre_pCoreOf_le_pCoreOf_ereg
    (hCQ : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) = pCoreOf 2 G)
    {M : Subgroup ↥(autOn G (gomiV G))} :
    gomiBarPre G (pCoreOf 2 M) ≤ pCoreOf 2 (gomiBarPre G M) := by
  have hP2 : IsPGroup 2 (gomiBarPre G (pCoreOf 2 M)) :=
    isPGroup_gomiBarPre_pCoreOf_ereg hCQ M
  have hPH : gomiBarPre G (pCoreOf 2 M) ≤ gomiBarPre G M :=
    Subgroup.map_mono (Subgroup.comap_mono (CFSG.LieType.BorelTits.pCoreOf_le 2 M))
  have hPnorm : gomiBarPre G M ≤
      Subgroup.normalizer (gomiBarPre G (pCoreOf 2 M) : Set Ω) :=
    gomiBarPre_normalizer_ereg (M := M) (K := pCoreOf 2 M)
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hPH hPnorm hP2

omit [Finite Ω] in
private theorem commutator_gomiBarOf_eq_bot_ereg {P D : Subgroup Ω}
    (hPG : P ≤ G) (hDG : D ≤ G) (hPDV : ⁅P, D⁆ ≤ gomiV G) :
    ⁅gomiBarOf G P, gomiBarOf G D⁆ = ⊥ := by
  have hVG : gomiV G ≤ G :=
    (CFSG.Quasithin.A4.omegaOneCenterOf_le (pCoreOf 2 G)).trans
      (CFSG.LieType.BorelTits.pCoreOf_le 2 G)
  have hsubcom : ⁅P.subgroupOf G, D.subgroupOf G⁆ ≤ (⁅P, D⁆).subgroupOf G := by
    rw [← Subgroup.map_le_map_iff_of_injective (f := G.subtype) G.subtype_injective]
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hPG,
      Subgroup.map_subgroupOf_eq_of_le hDG, Subgroup.map_subgroupOf_eq_of_le (hPDV.trans hVG)]
  have hmono : (⁅P.subgroupOf G, D.subgroupOf G⁆).map (gomiBar G) ≤
      ((⁅P, D⁆).subgroupOf G).map (gomiBar G) := Subgroup.map_mono hsubcom
  have hmono2 : ((⁅P, D⁆).subgroupOf G).map (gomiBar G) ≤
      ((gomiV G).subgroupOf G).map (gomiBar G) :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono G hPDV)
  have hVbar' : ((gomiV G).subgroupOf G).map (gomiBar G) = ⊥ := by
    rw [← gomiBarOf_eq_map hVG]
    exact gomiBarOf_gomiV_eq_bot_ereg
  rw [gomiBarOf_eq_map hPG, gomiBarOf_eq_map hDG, ← Subgroup.map_commutator]
  exact le_antisymm (hmono.trans (hmono2.trans (le_of_eq hVbar'))) bot_le

private theorem commutator_pCoreOf_gomiBarPre_map_le_gomiV_ereg
    (hchar : CharTwo G) {M : Subgroup ↥(autOn G (gomiV G))}
    (hHG : gomiBarPre G M ≤ G)
    (hQH : pCoreOf 2 G ≤ gomiBarPre G M)
    {B₀ : Subgroup ↥(gomiBarPre G M)} (hB₀ : IsAschbacherBlockGomi B₀) :
    ⁅pCoreOf 2 (gomiBarPre G M), B₀.map (gomiBarPre G M).subtype⁆ ≤ gomiV G :=
  (IsAschbacherBlockGomi.commutator_map_le_gomiV hB₀).trans
    (gomiV_le_gomiV_of_pCoreOf_le hchar hHG hQH)

private theorem commutator_gomiBarPre_pCoreOf_map_le_gomiV_ereg
    (hchar : CharTwo G) (hCQ : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) = pCoreOf 2 G)
    {M : Subgroup ↥(autOn G (gomiV G))} (hHG : gomiBarPre G M ≤ G)
    (hQH : pCoreOf 2 G ≤ gomiBarPre G M)
    {B₀ : Subgroup ↥(gomiBarPre G M)} (hB₀ : IsAschbacherBlockGomi B₀) :
    ⁅gomiBarPre G (pCoreOf 2 M), B₀.map (gomiBarPre G M).subtype⁆ ≤ gomiV G := by
  have h1 : gomiBarPre G (pCoreOf 2 M) ≤ pCoreOf 2 (gomiBarPre G M) :=
    gomiBarPre_pCoreOf_le_pCoreOf_ereg hCQ
  have h2 : ⁅pCoreOf 2 (gomiBarPre G M), B₀.map (gomiBarPre G M).subtype⁆ ≤ gomiV G :=
    commutator_pCoreOf_gomiBarPre_map_le_gomiV_ereg hchar hHG hQH hB₀
  exact (Subgroup.commutator_mono h1 le_rfl).trans h2

omit [Finite Ω] in
private theorem le_centralizer_of_commutator_eq_bot_ereg
    {A B : Subgroup ↥(autOn G (gomiV G))} (h : ⁅B, A⁆ = ⊥) :
    B ≤ Subgroup.centralizer (A : Set ↥(autOn G (gomiV G))) :=
  Subgroup.commutator_eq_bot_iff_le_centralizer.mp h

private theorem gomiBarOf_le_centralizer_pCoreOf_ereg
    (hchar : CharTwo G) (hCQ : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) = pCoreOf 2 G)
    {M : Subgroup ↥(autOn G (gomiV G))} (hHG : gomiBarPre G M ≤ G)
    (hQH : pCoreOf 2 G ≤ gomiBarPre G M)
    {B₀ : Subgroup ↥(gomiBarPre G M)} (hB₀ : IsAschbacherBlockGomi B₀) :
    gomiBarOf G (B₀.map (gomiBarPre G M).subtype) ≤
      Subgroup.centralizer (pCoreOf 2 M : Set ↥(autOn G (gomiV G))) := by
  have hPDV : ⁅gomiBarPre G (pCoreOf 2 M), B₀.map (gomiBarPre G M).subtype⁆ ≤ gomiV G :=
    commutator_gomiBarPre_pCoreOf_map_le_gomiV_ereg hchar hCQ hHG hQH hB₀
  have hcommbot : ⁅gomiBarOf G (gomiBarPre G (pCoreOf 2 M)),
      gomiBarOf G (B₀.map (gomiBarPre G M).subtype)⁆ = ⊥ :=
    commutator_gomiBarOf_eq_bot_ereg (gomiBarPre_le G _)
      ((Subgroup.map_subtype_le B₀).trans hHG) hPDV
  have hPbar : gomiBarOf G (gomiBarPre G (pCoreOf 2 M)) = pCoreOf 2 M :=
    gomiBarOf_gomiBarPre G (pCoreOf 2 M)
  have hcommDP : ⁅gomiBarOf G (B₀.map (gomiBarPre G M).subtype),
      gomiBarOf G (gomiBarPre G (pCoreOf 2 M))⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact hcommbot
  have hle := le_centralizer_of_commutator_eq_bot_ereg hcommDP
  rwa [hPbar] at hle

omit [Finite Ω] in
private theorem gomiBarOf_map_le_twoResidual_ereg {H : Subgroup Ω}
    {X : Subgroup ↥(autOn G (gomiV G))}
    {B₀ : Subgroup ↥H} (hHG : H ≤ G)
    (hresD : oResidualTwo ↥(B₀.map H.subtype) = ⊤)
    (hDbarX : gomiBarOf G (B₀.map H.subtype) ≤ X) :
    gomiBarOf G (B₀.map H.subtype) ≤ twoResidual X := by
  let D : Subgroup Ω := B₀.map H.subtype
  have hDG : D ≤ G := (Subgroup.map_subtype_le B₀).trans hHG
  have hresD' : oResidualTwo ↥D = ⊤ := hresD
  have hDbarX' : gomiBarOf G D ≤ X := hDbarX
  intro y hy
  rw [mem_twoResidual_iff]
  intro N hNX hNnorm hN2
  rw [gomiBarOf_eq_map hDG] at hy
  obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
  let d : ↥D := ⟨x, Subgroup.mem_subgroupOf.mp hx⟩
  let NX : Subgroup ↥X := N.subgroupOf X
  have hNXnormal : NX.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNX).mpr hNnorm
  let : NX.Normal := hNXnormal
  have hquot2 : IsPGroup 2 (↥X ⧸ NX) := by
    refine TauCeti.isPGroup_quotient_of_forall_exists_pow_mem ?_
    intro z
    obtain ⟨k, hk⟩ := hN2 z.1 z.2
    exact ⟨k, by rw [Subgroup.mem_subgroupOf]; exact hk⟩
  let g : ↥D →* ↥X :=
    ((gomiBar G).comp (Subgroup.inclusion hDG)).codRestrict X fun d => by
      have hmem : (gomiBar G) (Subgroup.inclusion hDG d) ∈ gomiBarOf G D := by
        rw [gomiBarOf_eq_map hDG]
        exact Subgroup.mem_map.mpr ⟨Subgroup.inclusion hDG d, by
          rw [Subgroup.mem_subgroupOf]; exact d.2, rfl⟩
      exact hDbarX' hmem
  let f : ↥D →* ↥X ⧸ NX := (QuotientGroup.mk' NX).comp g
  have hf : f d = 1 :=
    CFSG.CGT.PushingUpLit.CGT6.eq_one_of_oResidualTwo_eq_top hresD' hquot2 f d
  have hmemNX : g d ∈ NX := by
    have h1 : (QuotientGroup.mk' NX) (g d) = 1 := hf
    exact (QuotientGroup.eq_one_iff (N := NX) (g d)).1 h1
  have hmemN : (g d : ↥(autOn G (gomiV G))) ∈ N :=
    Subgroup.mem_subgroupOf.mp hmemNX
  have hincl : Subgroup.inclusion hDG d = x := Subtype.ext rfl
  have hgd : (g d : ↥(autOn G (gomiV G))) = y := by
    rw [← hxy]
    change gomiBar G (Subgroup.inclusion hDG d) = gomiBar G x
    rw [hincl]
  rwa [← hgd]

theorem Gomi410Cex.exists_block_of_not_isRegular (h : Gomi410Cex f hyp G) (hchar : CharTwo G)
    (hmono : ∀ H : Subgroup Ω, H ≤ G → pCoreOf 2 G ≤ H → hyp H)
    (hCQ : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) = pCoreOf 2 G)
    {M : Subgroup ↥(autOn G (gomiV G))} (hM : M ≠ ⊤) (hreg : ¬ f.IsRegular (gomiBarPre G M)) :
    ∃ D : Subgroup ↥(gomiBarPre G M), IsAschbacherBlockGomi D ∧
      gomiBarOf G (D.map (gomiBarPre G M).subtype) ≤
        twoResidual (M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set ↥(autOn G (gomiV G)))) := by
  let H : Subgroup Ω := gomiBarPre G M
  have hHG : H ≤ G := gomiBarPre_le G M
  have hHne : H ≠ G := by
    intro hEq
    apply hM
    have htop : gomiBarOf G G = ⊤ := by
      rw [gomiBarOf]
      exact Subgroup.subgroupOf_self _
    have hbar : gomiBarOf G H = M := gomiBarOf_gomiBarPre G M
    rw [hEq, htop] at hbar
    exact hbar.symm
  have hHlt : H < G := lt_of_le_of_ne hHG hHne
  have hQH : pCoreOf 2 G ≤ H := pCoreOf_le_gomiBarPre G M
  have hhypH : hyp H := hmono H hHG hQH
  obtain ⟨D₀, hD₀⟩ := h.minimal H hHlt hQH hhypH hreg
  refine ⟨D₀, hD₀, ?_⟩
  have hDbarM : gomiBarOf G (D₀.map H.subtype) ≤ M := by
    have hm := gomiBarOf_mono_ereg (Subgroup.map_subtype_le D₀) hHG
    have hm' : gomiBarOf G (D₀.map H.subtype) ≤ gomiBarOf G (gomiBarPre G M) := hm
    rwa [gomiBarOf_gomiBarPre G M] at hm'
  have hDbarC : gomiBarOf G (D₀.map H.subtype) ≤
      Subgroup.centralizer (pCoreOf 2 M : Set ↥(autOn G (gomiV G))) :=
    gomiBarOf_le_centralizer_pCoreOf_ereg hchar hCQ hHG hQH hD₀
  have hresD : oResidualTwo ↥(D₀.map H.subtype) = ⊤ :=
    oResidualTwo_map_subtype_top_ereg hD₀.residual
  have hDbarX : gomiBarOf G (D₀.map H.subtype) ≤
      M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set ↥(autOn G (gomiV G))) :=
    le_inf hDbarM hDbarC
  exact gomiBarOf_map_le_twoResidual_ereg hHG hresD hDbarX

omit [Finite Ω] in
private theorem commutator_conjClosure_le_pCoreOf_ereg
    (hCQ : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) = pCoreOf 2 G)
    {B : Subgroup Ω} (hB : IsGomiTwoComponent G B) {D : Subgroup Ω} (hDG : D ≤ G)
    {X : Subgroup ↥(autOn G (gomiV G))}
    (hle : twoResidual X ≤
      Subgroup.normalClosure (gomiBarOf G B : Set ↥(autOn G (gomiV G))) ⊓
        Subgroup.centralizer
          (Subgroup.normalClosure (gomiBarOf G B : Set ↥(autOn G (gomiV G))) :
            Set ↥(autOn G (gomiV G))))
    (hDbar_le : gomiBarOf G D ≤ twoResidual X) :
    ⁅conjClosure B G, D⁆ ≤ pCoreOf 2 G := by
  let N : Subgroup Ω := conjClosure B G
  have hNG : N ≤ G :=
    conjClosure_le fun h hh z hz => G.mul_mem (G.mul_mem hh (hB.le hz)) (G.inv_mem hh)
  have hDbar_N : gomiBarOf G D ≤
      Subgroup.normalClosure (gomiBarOf G B : Set ↥(autOn G (gomiV G))) :=
    (hDbar_le.trans hle).trans inf_le_left
  have hDbar_C : gomiBarOf G D ≤
      Subgroup.centralizer
        (Subgroup.normalClosure (gomiBarOf G B : Set ↥(autOn G (gomiV G))) :
          Set ↥(autOn G (gomiV G))) :=
    (hDbar_le.trans hle).trans inf_le_right
  have hcommDbarNbar : ⁅gomiBarOf G D,
      Subgroup.normalClosure (gomiBarOf G B : Set ↥(autOn G (gomiV G)))⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hDbar_C
  have hcommNbarDbar : ⁅Subgroup.normalClosure (gomiBarOf G B : Set ↥(autOn G (gomiV G))),
      gomiBarOf G D⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact hcommDbarNbar
  refine commutator_le_pCoreOf_of_gomiBarOf hCQ hNG hDG ?_
  rw [show gomiBarOf G N =
    Subgroup.normalClosure (gomiBarOf G B : Set ↥(autOn G (gomiV G))) from
      gomiBarOf_conjClosure hB.le]
  exact hcommNbarDbar

private theorem normalizer_conjClosure_map_ereg {H : Subgroup Ω}
    (hHG : H ≤ G) (hQH : pCoreOf 2 G ≤ H) {D₀ : Subgroup ↥H}
    (hD₀ : IsAschbacherBlockGomi D₀) {B : Subgroup Ω} (hB : IsGomiTwoComponent G B)
    (hcommND : ⁅conjClosure B G, D₀.map H.subtype⁆ ≤ pCoreOf 2 G) :
    conjClosure B G ≤ Subgroup.normalizer (D₀.map H.subtype : Set Ω) := by
  have hNG : conjClosure B G ≤ G :=
    conjClosure_le fun h hh z hz => G.mul_mem (G.mul_mem hh (hB.le hz)) (G.inv_mem hh)
  have hQD : pCoreOf 2 G ≤ Subgroup.normalizer (D₀.map H.subtype : Set Ω) :=
    (pCoreOf_le_pCoreOf_of_le_ereg hHG hQH).trans
      (IsAschbacherBlockGomi.pCoreOf_le_normalizer hD₀)
  have hNQ : conjClosure B G ≤ Subgroup.normalizer (pCoreOf 2 G : Set Ω) :=
    hNG.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G)
  have hresD : oResidualTwo ↥(D₀.map H.subtype) = ⊤ :=
    oResidualTwo_map_subtype_top_ereg hD₀.residual
  exact le_normalizer_of_commutator_le (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G)
    hQD hresD hNQ hcommND

private theorem eq_sup_of_sylow_of_odd_relIndex_ereg {H N : Subgroup Ω} (hHG : H ≤ G)
    (hNG : N ≤ G) (hodd : ¬ 2 ∣ H.relIndex G)
    (hGNS : ∀ S : Subgroup Ω, IsSylowTwoOf S G → G = N ⊔ S) :
    G = N ⊔ H := by
  obtain ⟨T, hT⟩ := CFSG.QuasithinUnique.exists_isSylowTwoOf H
  have hTH : T ≤ H := hT.1
  have hTG : T ≤ G := hTH.trans hHG
  have hTsylG : IsSylowTwoOf T G := by
    refine ⟨hTG, hT.2.1, ?_⟩
    change ¬ 2 ∣ T.relIndex G
    rw [← Subgroup.relIndex_mul_relIndex T H G hTH hHG]
    exact fun hd => (Nat.Prime.dvd_mul Nat.prime_two).mp hd |>.elim hT.2.2 hodd
  have hGNT : G = N ⊔ T := hGNS T hTsylG
  apply le_antisymm
  · rw [hGNT]
    exact sup_le le_sup_left (hTH.trans le_sup_right)
  · exact sup_le hNG hHG

theorem Gomi410Cex.isRegular_gomiBarPre_of_le_center (h : Gomi410Cex f hyp G)
    (hchar : CharTwo G) (hmono : ∀ H : Subgroup Ω, H ≤ G → pCoreOf 2 G ≤ H → hyp H)
    {B : Subgroup Ω} (hB : IsGomiTwoComponent G B)
    (hGB : ∀ S : Subgroup Ω, IsSylowTwoOf S G → G = conjClosure B G ⊔ S)
    (hCQ : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) = pCoreOf 2 G)
    {M : Subgroup ↥(autOn G (gomiV G))} (hM : M ≠ ⊤) (hodd : Odd M.index)
    (hle : twoResidual (M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set ↥(autOn G (gomiV G)))) ≤
      Subgroup.normalClosure (gomiBarOf G B : Set ↥(autOn G (gomiV G))) ⊓
        Subgroup.centralizer
          (Subgroup.normalClosure (gomiBarOf G B : Set ↥(autOn G (gomiV G))) :
            Set ↥(autOn G (gomiV G)))) :
    f.IsRegular (gomiBarPre G M) := by
  by_contra hnotreg
  let H : Subgroup Ω := gomiBarPre G M
  have hHG : H ≤ G := gomiBarPre_le G M
  obtain ⟨D₀, hD₀, hDbar_le⟩ :=
    h.exists_block_of_not_isRegular hchar hmono hCQ hM hnotreg
  have hcommND : ⁅conjClosure B G, D₀.map H.subtype⁆ ≤ pCoreOf 2 G :=
    commutator_conjClosure_le_pCoreOf_ereg hCQ hB
      ((Subgroup.map_subtype_le D₀).trans hHG) hle hDbar_le
  have hNG : conjClosure B G ≤ G :=
    conjClosure_le fun h hh z hz => G.mul_mem (G.mul_mem hh (hB.le hz)) (G.inv_mem hh)
  have hQH : pCoreOf 2 G ≤ H := pCoreOf_le_gomiBarPre G M
  have hND : conjClosure B G ≤ Subgroup.normalizer (D₀.map H.subtype : Set Ω) :=
    normalizer_conjClosure_map_ereg hHG hQH hD₀ hB hcommND
  have hHodd : ¬ 2 ∣ H.relIndex G := by
    rw [show H.relIndex G = M.index from relIndex_gomiBarPre G M]
    exact hodd.not_two_dvd_nat
  have hGNH : G = conjClosure B G ⊔ H :=
    eq_sup_of_sylow_of_odd_relIndex_ereg hHG hNG hHodd (hGB ·)
  have hQB : ⁅pCoreOf 2 G, D₀.map H.subtype⁆ ≤ gomiV G :=
    commutator_pCoreOf_map_le_gomiV_ereg hchar hHG hQH hD₀
  exact h.not_block
    (hasGomiBlock_of_le_normalizer hHG hD₀ hNG (le_normalizer_conjClosure B G)
      hGNH hND hQB)

end CFSG.GroupTheory
