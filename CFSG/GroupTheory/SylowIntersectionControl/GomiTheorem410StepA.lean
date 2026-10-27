module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410
import CFSG.GroupTheory.SubnormalResidualTwo
import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C56b
import CFSG.GroupTheory.SylowIntersectionControl.GomiOverCore
import CFSG.GroupTheory.SylowIntersectionControl.Regular
import CFSG.GroupTheory.SylowQuotientSup
import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410Lift
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Basic
import CFSG.CGT.PushingUpLit.Transport
import CFSG.Quasithin.Background.A4V
import CFSG.Quasithin.Background.C1GNNotation
import CFSG.Quasithin.Background.B6Basic
import TauCeti.GroupTheory.Elementary
public import CFSG.GroupTheory.SylowIntersectionControl.CharPair
import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.GroupTheory

open CFSG CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.RankThree.PartOne Subgroup
open CFSG.QuasithinUnique.Setup
open scoped commutatorElement Pointwise

variable {Ω : Type} [Group Ω] [Finite Ω] {f : PSubgroupSelection 2 Ω}
  {hyp : Subgroup Ω → Prop} {G : Subgroup Ω}

omit [Finite Ω] in
private theorem le_normalizer_gomiV_s4a : G ≤ Subgroup.normalizer (gomiV G : Set Ω) :=
  (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G).trans
    (CFSG.Quasithin.A4.normalizer_le_normalizer_omegaOneCenterOf (pCoreOf 2 G))

omit [Finite Ω] in
private theorem hQC_s4a :
    pCoreOf 2 G ≤ G ⊓ Subgroup.centralizer (gomiV G : Set Ω) := by
  refine le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 G) ?_
  intro q hq
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact (Subgroup.mem_centralizer_iff.mp
    (CFSG.Quasithin.C1GN.omegaOneCenterOf_le_centerOf (pCoreOf 2 G) hv).2 q hq).symm

omit [Finite Ω] in
private theorem core_C_normal_s4a :
    G ≤ Subgroup.normalizer
      ((G ⊓ Subgroup.centralizer (gomiV G : Set Ω) : Subgroup Ω) : Set Ω) := by
  have hVG : G ≤ Subgroup.normalizer (gomiV G : Set Ω) := le_normalizer_gomiV_s4a
  have hC : G ≤ Subgroup.normalizer
      (Subgroup.centralizer (gomiV G : Set Ω) : Set Ω) :=
    CFSG.Quasithin.B6.le_normalizer_centralizer (H := G) (V := gomiV G) hVG
  exact (le_inf (Subgroup.le_normalizer (H := G)) hC).trans
    (Subgroup.inf_normalizer_le_normalizer_inf
      (H := (G : Subgroup Ω)) (K := Subgroup.centralizer (gomiV G : Set Ω)))

private theorem gomi410_comm_QB_s4a {H T B : Subgroup Ω}
    (hchar : CharTwo G) (hHG : H ≤ G) (hQH : pCoreOf 2 G ≤ H)
    (hQT : pCoreOf 2 G ≤ T) (hTH : T ≤ pCoreOf 2 H)
    (hcommH : ⁅pCoreOf 2 H, B⁆ ≤ gomiV H) :
    ⁅pCoreOf 2 G, B⁆ ≤ gomiV G :=
  (Subgroup.commutator_mono (hQT.trans hTH) le_rfl).trans
    (hcommH.trans (gomiV_le_gomiV_of_pCoreOf_le hchar hHG hQH))

private theorem gomi410_comm_CB_s4a {B : Subgroup Ω}
    (hchar : CharTwo G) (hBG : B ≤ G) (hQBV : ⁅pCoreOf 2 G, B⁆ ≤ gomiV G) :
    ⁅G ⊓ Subgroup.centralizer (gomiV G : Set Ω), B⁆ ≤ pCoreOf 2 G := by
  set C : Subgroup Ω := G ⊓ Subgroup.centralizer (gomiV G : Set Ω) with hC
  have hQnormV : pCoreOf 2 G ≤ Subgroup.normalizer (gomiV G : Set Ω) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 G).trans le_normalizer_gomiV_s4a
  have hCnormV : C ≤ Subgroup.normalizer (gomiV G : Set Ω) := by
    rw [hC]; exact inf_le_left.trans le_normalizer_gomiV_s4a
  have hCQ : C ≤ Subgroup.normalizer (pCoreOf 2 G : Set Ω) := by
    rw [hC]; exact inf_le_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G)
  have hXleC : ⁅C, B⁆ ≤ C := by
    have hBC : B ≤ Subgroup.normalizer (C : Set Ω) := by
      rw [hC]; exact hBG.trans core_C_normal_s4a
    rw [Subgroup.commutator_comm]
    exact (Subgroup.le_normalizer_iff_commutator_le_right).mp hBC
  have hBQ : ⁅B, pCoreOf 2 G⁆ ≤ gomiV G := by
    rw [Subgroup.commutator_comm]; exact hQBV
  have hVC : ⁅gomiV G, C⁆ ≤ gomiV G :=
    (Subgroup.le_normalizer_iff_commutator_le_left).mp hCnormV
  have h₁ : ⁅⁅B, pCoreOf 2 G⁆, C⁆ ≤ gomiV G :=
    (Subgroup.commutator_mono hBQ le_rfl).trans hVC
  have hQCQ : ⁅pCoreOf 2 G, C⁆ ≤ pCoreOf 2 G := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.le_normalizer_iff_commutator_le_right).mp hCQ
  have h₂ : ⁅⁅pCoreOf 2 G, C⁆, B⁆ ≤ gomiV G :=
    (Subgroup.commutator_mono hQCQ le_rfl).trans hQBV
  have hrot : ⁅⁅C, B⁆, pCoreOf 2 G⁆ ≤ gomiV G :=
    F53.Stellmacher.S35.C56.three_subgroups_mod (hBG.trans le_normalizer_gomiV_s4a) hQnormV
      hCnormV h₁ h₂
  intro x hx
  refine mem_pCoreOf_of_commutator_mem_gomiV hchar (hXleC hx).1 (hXleC hx).2 ?_
  intro q hq
  have h1 : ⁅x, q⁆ ∈ gomiV G := hrot (Subgroup.commutator_mem_commutator hx hq)
  rw [← commutatorElement_inv x q]
  exact (gomiV G).inv_mem h1

private theorem gomi410_normalizes_s4a (N : Subgroup Ω) {H T B : Subgroup Ω} {B₀ : Subgroup ↥H}
    (hB₀ : IsAschbacherBlockGomi B₀) (hB : B = B₀.map H.subtype)
    (hCBQ : ⁅G ⊓ Subgroup.centralizer (gomiV G : Set Ω), B⁆ ≤ pCoreOf 2 G)
    (hQleT : pCoreOf 2 G ≤ T) (hTlePCH : T ≤ pCoreOf 2 H)
    (hNCT : N = (G ⊓ Subgroup.centralizer (gomiV G : Set Ω)) ⊔ T) :
    N ≤ Subgroup.normalizer (B : Set Ω) := by
  have hPCH : pCoreOf 2 H ≤ Subgroup.normalizer (B : Set Ω) := by
    rw [hB]
    exact IsAschbacherBlockGomi.pCoreOf_le_normalizer hB₀
  have hQnorm : pCoreOf 2 G ≤ Subgroup.normalizer (B : Set Ω) := hQleT.trans (hTlePCH.trans hPCH)
  have hTnorm : T ≤ Subgroup.normalizer (B : Set Ω) := hTlePCH.trans hPCH
  have hresB : oResidualTwo ↥B = ⊤ := by
    rw [hB]
    exact CFSG.CGT.PushingUpLit.oResidualTwo_eq_top_of_mulEquiv
      (B₀.equivMapOfInjective H.subtype H.subtype_injective) hB₀.residual
  have hQ2 : IsPGroup 2 (pCoreOf 2 G) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G
  have hCQ : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) ≤
      Subgroup.normalizer (pCoreOf 2 G : Set Ω) :=
    inf_le_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G)
  have hCnorm : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) ≤
      Subgroup.normalizer (B : Set Ω) :=
    le_normalizer_of_commutator_le hQ2 hQnorm hresB hCQ hCBQ
  rw [hNCT]
  exact sup_le hCnorm hTnorm

private theorem gomi410_reg_sup_s4a (hchar : CharTwo G)
    (hfZ : ∀ P : Subgroup Ω, IsPGroup 2 P → omegaOneCenterOf P ∈ f.sets P)
    (S : Subgroup Ω) (hS : IsSylowTwoOf S G) :
    f.IsRegular ((G ⊓ Subgroup.centralizer (gomiV G : Set Ω)) ⊔ S) := by
  have hVle : omegaOneCenterOf S ≤ gomiV G :=
    omegaOneCenterOf_le_gomiV_of_pCoreOf_le hchar hS.1
      (CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hS)
  have hCSleG : (G ⊓ Subgroup.centralizer (gomiV G : Set Ω)) ⊔ S ≤ G :=
    sup_le inf_le_left hS.1
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 S
      ((G ⊓ Subgroup.centralizer (gomiV G : Set Ω)) ⊔ S) :=
    CFSG.ABGLocalTools.IsSylowOf.of_le (X6.isSylowTwoOf_iff_isSylowOf.mp hS) le_sup_right hCSleG
  refine PSubgroupSelection.isRegular_of_le_normalizer hSyl (hfZ S hS.2.1) ?_
  refine sup_le ?_ ?_
  · intro c hc
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_iff.mp hc.2 x (hVle hx)
  · intro s hs
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp
      (CFSG.Quasithin.C1GN.omegaOneCenterOf_le_centerOf S hx).2 s hs).symm

omit [Finite Ω] in
private theorem gomi410_H_ne_s4a (N T H : Subgroup Ω)
    (hT : IsSylowTwoOf T N) (hTG : T ≤ G)
    (hH : H = G ⊓ Subgroup.normalizer (T : Set Ω))
    (hQleT : pCoreOf 2 G ≤ T) (hQnot : ¬ IsSylowTwoOf (pCoreOf 2 G) N) : H ≠ G := by
  intro hHG
  have hGnormT : G ≤ Subgroup.normalizer (T : Set Ω) := by
    have h : G ≤ G ⊓ Subgroup.normalizer (T : Set Ω) := by
      rw [← hH, hHG]
    exact h.trans inf_le_right
  have hTnormal : (T.subgroupOf G).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTG).mpr hGnormT
  have hTleQ : T ≤ pCoreOf 2 G :=
    CFSG.LieType.BorelTits.le_pCoreOf 2 hTG hTnormal hT.2.1
  have hQT : T = pCoreOf 2 G := le_antisymm hTleQ hQleT
  exact hQnot (hQT ▸ hT)

private structure Gomi410Setup_s4a (G : Subgroup Ω) (N : Subgroup Ω) where
  S : Subgroup Ω
  T : Subgroup Ω
  H : Subgroup Ω
  hS : IsSylowTwoOf S G
  hT : IsSylowTwoOf T N
  hTleG : T ≤ G
  hTleH : T ≤ H
  hSleH : S ≤ H
  hHdef : H = G ⊓ Subgroup.normalizer (T : Set Ω)
  hQleT : pCoreOf 2 G ≤ T
  hNCT : N = (G ⊓ Subgroup.centralizer (gomiV G : Set Ω)) ⊔ T
  hGNH : G = N ⊔ H
  hQleH : pCoreOf 2 G ≤ H
  hHne : H ≠ G

private noncomputable def gomi410_setup_s4a (N : Subgroup Ω)
    (hCN : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) ≤ N) (hNG : N ≤ G)
    (hN : G ≤ Subgroup.normalizer (N : Set Ω))
    (h2 : ∀ x ∈ N, ∃ k : ℕ, x ^ 2 ^ k ∈ G ⊓ Subgroup.centralizer (gomiV G : Set Ω))
    (hQnot : ¬ IsSylowTwoOf (pCoreOf 2 G) N) :
    Gomi410Setup_s4a G N := by
  classical
  let S : Subgroup Ω := Classical.choose (CFSG.QuasithinUnique.exists_isSylowTwoOf G)
  have hS : IsSylowTwoOf S G :=
    Classical.choose_spec (CFSG.QuasithinUnique.exists_isSylowTwoOf G)
  let T : Subgroup Ω := S ⊓ N
  have hT : IsSylowTwoOf T N :=
    X6.isSylowTwoOf_iff_isSylowOf.mpr
      (CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer
        (X6.isSylowTwoOf_iff_isSylowOf.mp hS) hNG hN)
  have hTleG : T ≤ G := inf_le_left.trans hS.1
  let H : Subgroup Ω := G ⊓ Subgroup.normalizer (T : Set Ω)
  have hSleH : S ≤ H :=
    le_inf hS.1 ((le_inf Subgroup.le_normalizer (hS.1.trans hN)).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := S) (K := N)))
  have hTleH : T ≤ H := inf_le_left.trans hSleH
  have hQleT : pCoreOf 2 G ≤ T :=
    le_inf (CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hS) (hQC_s4a.trans hCN)
  have hNCT : N = (G ⊓ Subgroup.centralizer (gomiV G : Set Ω)) ⊔ T := by
    refine le_antisymm ?_ (sup_le hCN hT.1)
    have hCnormalN : ((G ⊓ Subgroup.centralizer (gomiV G : Set Ω)).subgroupOf N).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hCN).mpr (hNG.trans core_C_normal_s4a)
    have hquot : IsPGroup 2
        (↥N ⧸ (G ⊓ Subgroup.centralizer (gomiV G : Set Ω)).subgroupOf N) := by
      refine TauCeti.isPGroup_quotient_of_forall_exists_pow_mem ?_
      intro g
      obtain ⟨k, hk⟩ := h2 g.val g.2
      exact ⟨k, by rw [Subgroup.mem_subgroupOf]; simpa using hk⟩
    exact le_sup_of_isPGroup_quotient_of_isSylowOf hCN (X6.isSylowTwoOf_iff_isSylowOf.mp hT) hquot
  have hGNH : G = N ⊔ H :=
    le_antisymm (CFSG.Quasithin.B6.frattini_two hNG hN hT) (sup_le hNG inf_le_left)
  have hQleH : pCoreOf 2 G ≤ H :=
    le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 G) (hQleT.trans Subgroup.le_normalizer)
  have hHne : H ≠ G := gomi410_H_ne_s4a N T H hT hTleG rfl hQleT hQnot
  exact ⟨S, T, H, hS, hT, hTleG, hTleH, hSleH, rfl, hQleT, hNCT, hGNH, hQleH, hHne⟩

private theorem gomi410Core_s4a (h : Gomi410Cex f hyp G)
    (hfZ : ∀ P : Subgroup Ω, IsPGroup 2 P → omegaOneCenterOf P ∈ f.sets P)
    (hchar : CharTwo G)
    (hmono : ∀ H : Subgroup Ω, H ≤ G → pCoreOf 2 G ≤ H → hyp H)
    {N : Subgroup Ω}
    (hCN : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) ≤ N) (hNG : N ≤ G)
    (hN : G ≤ Subgroup.normalizer (N : Set Ω))
    (h2 : ∀ x ∈ N, ∃ k : ℕ, x ^ 2 ^ k ∈ G ⊓ Subgroup.centralizer (gomiV G : Set Ω)) :
    IsSylowTwoOf (pCoreOf 2 G) N := by
  classical
  by_contra hQnot
  obtain ⟨S, T, H, hS, hT, hTleG, hTleH, hSleH, hH, hQleT, hNCT, hGNH, hQleH, hHne⟩ :=
    gomi410_setup_s4a N hCN hNG hN h2 hQnot
  have hHltG : H < G := lt_of_le_of_ne (hH.le.trans inf_le_left) hHne
  have hhypH : hyp H := hmono H (hH.le.trans inf_le_left) hQleH
  have hregCS : f.IsRegular ((G ⊓ Subgroup.centralizer (gomiV G : Set Ω)) ⊔ S) :=
    gomi410_reg_sup_s4a hchar hfZ S hS
  have hnotregH : ¬ f.IsRegular H := by
    intro hregH
    have hGHC : G = (G ⊓ Subgroup.centralizer (gomiV G : Set Ω)) ⊔ H := by
      have h1 : N ⊔ H = (G ⊓ Subgroup.centralizer (gomiV G : Set Ω)) ⊔ H := by
        rw [hNCT, sup_assoc, sup_eq_right.mpr hTleH]
      exact hGNH.trans h1
    have hmul : (H : Set Ω) *
        (((G ⊓ Subgroup.centralizer (gomiV G : Set Ω)) ⊔ S : Subgroup Ω) : Set Ω)
        = (G : Set Ω) :=
      mul_eq_of_eq_sup hGHC ((hH.le.trans inf_le_left).trans core_C_normal_s4a)
        le_sup_left (sup_le inf_le_left (hSleH.trans (hH.le.trans inf_le_left)))
    exact h.singular (PSubgroupSelection.IsRegular.of_mul_eq
      (X6.isSylowTwoOf_iff_isSylowOf.mp hS) hSleH le_sup_right hmul hregH hregCS)
  obtain ⟨B₀, hB₀⟩ := h.minimal H hHltG hQleH hhypH hnotregH
  let B : Subgroup Ω := B₀.map H.subtype
  have hBH : B ≤ H := Subgroup.map_subtype_le B₀
  have hTlePCH : T ≤ pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hTleH
      (hH.le.trans inf_le_right) hT.2.1
  have hcommH : ⁅pCoreOf 2 H, B⁆ ≤ gomiV H := IsAschbacherBlockGomi.commutator_map_le_gomiV hB₀
  have hQBV : ⁅pCoreOf 2 G, B⁆ ≤ gomiV G :=
    gomi410_comm_QB_s4a hchar (hH.le.trans inf_le_left) hQleH hQleT hTlePCH hcommH
  have hCBQ : ⁅G ⊓ Subgroup.centralizer (gomiV G : Set Ω), B⁆ ≤ pCoreOf 2 G :=
    gomi410_comm_CB_s4a hchar (hBH.trans (hH.le.trans inf_le_left)) hQBV
  have hNnorm : N ≤ Subgroup.normalizer (B : Set Ω) :=
    gomi410_normalizes_s4a N hB₀ rfl hCBQ hQleT hTlePCH hNCT
  exact h.not_block
    (hasGomiBlock_of_le_normalizer (hH.le.trans inf_le_left) hB₀ hNG hN hGNH hNnorm hQBV)

theorem Gomi410Cex.sylow_centralizer (h : Gomi410Cex f hyp G)
    (hfZ : ∀ P : Subgroup Ω, IsPGroup 2 P → omegaOneCenterOf P ∈ f.sets P)
    (hchar : CharTwo G) (hmono : ∀ H : Subgroup Ω, H ≤ G → pCoreOf 2 G ≤ H → hyp H) :
    IsSylowTwoOf (pCoreOf 2 G) (G ⊓ Subgroup.centralizer (gomiV G : Set Ω)) := by
  refine gomi410Core_s4a h hfZ hchar hmono le_rfl inf_le_left core_C_normal_s4a ?_
  intro x hx
  exact ⟨0, by simpa using hx⟩

theorem Gomi410Cex.le_centralizer_of_normal (h : Gomi410Cex f hyp G)
    (hfZ : ∀ P : Subgroup Ω, IsPGroup 2 P → omegaOneCenterOf P ∈ f.sets P)
    (hchar : CharTwo G) (hmono : ∀ H : Subgroup Ω, H ≤ G → pCoreOf 2 G ≤ H → hyp H)
    {N : Subgroup Ω} (hCN : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) ≤ N) (hNG : N ≤ G)
    (hN : G ≤ Subgroup.normalizer (N : Set Ω))
    (h2 : ∀ x ∈ N, ∃ k : ℕ, x ^ 2 ^ k ∈ Subgroup.centralizer (gomiV G : Set Ω)) :
    N ≤ Subgroup.centralizer (gomiV G : Set Ω) := by
  have h2' : ∀ x ∈ N, ∃ k : ℕ,
      x ^ 2 ^ k ∈ G ⊓ Subgroup.centralizer (gomiV G : Set Ω) := fun x hx => by
    obtain ⟨k, hk⟩ := h2 x hx
    exact ⟨k, ⟨G.pow_mem (hNG hx) _, hk⟩⟩
  have hSyl : IsSylowTwoOf (pCoreOf 2 G) N :=
    gomi410Core_s4a h hfZ hchar hmono hCN hNG hN h2'
  have hCnormalN : ((G ⊓ Subgroup.centralizer (gomiV G : Set Ω)).subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCN).mpr (hNG.trans core_C_normal_s4a)
  have hquot : IsPGroup 2
      (↥N ⧸ (G ⊓ Subgroup.centralizer (gomiV G : Set Ω)).subgroupOf N) := by
    refine TauCeti.isPGroup_quotient_of_forall_exists_pow_mem ?_
    intro g
    obtain ⟨k, hk⟩ := h2' g.val g.2
    exact ⟨k, by rw [Subgroup.mem_subgroupOf]; simpa using hk⟩
  have hNCQ : N ≤ (G ⊓ Subgroup.centralizer (gomiV G : Set Ω)) ⊔ pCoreOf 2 G :=
    le_sup_of_isPGroup_quotient_of_isSylowOf hCN (X6.isSylowTwoOf_iff_isSylowOf.mp hSyl) hquot
  have hQC : pCoreOf 2 G ≤ G ⊓ Subgroup.centralizer (gomiV G : Set Ω) := hQC_s4a
  exact (hNCQ.trans (sup_le le_rfl hQC)).trans inf_le_right

end CFSG.GroupTheory
