module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueRelativeBMinimal
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zMSingle
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zH2Local
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zH2Key
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zH2Plane
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62ySetup
import CFSG.HardMathSupport.Timmesfeld.Proving.ElemAbelianSubgroup
import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Bridge
public import CFSG.Open.GorensteinWalterLBalanceMilestoneDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup CFSG.ComponentClassification
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem k631b_finish {f : ℕ} {E F : Subgroup G} (ctx : k631b_Ctx f E F) {a : G}
    (hL : LayerHyp f (centralizer ({a} : Set G)) E) {J : Subgroup G}
    (hJ : GLAPComponent f (centralizer ({a} : Set G)) J)
    (h3 : CFSG.Open.pRank f (E ⊓ J) = 3) :
    lBalanceIsPComponent f (centralizer ({a} : Set G)) J ∧ CFSG.Open.pRank f J = 3 ∧
      CFSG.Open.pRank f (F ⊓ J) = 3 := by
  refine ⟨(CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPComponent_iff.mp hJ).2, ?_, ?_⟩
  · have hS : IsPGroup f ↥(E ⊓ J) := ctx.pgroup.to_le inf_le_left
    have h1 := k631b_pRank_le_of_sylow ctx.prime (inf_le_right : E ⊓ J ≤ J) hS
      (k631_comp_sylow hL hJ)
    have h2 := CFSG.SectionRank.pRank_mono ctx.prime.one_lt (inf_le_right : E ⊓ J ≤ J)
    omega
  · have hFJ : F ⊓ J = F ⊓ (E ⊓ J) :=
      le_antisymm (le_inf inf_le_left (le_inf (inf_le_left.trans ctx.le) inf_le_right))
        (inf_le_inf_left F inf_le_right)
    rw [hFJ, ctx.pRank_inf inf_le_left, h3]

omit [Finite G] in
theorem k631b_comm_cancel {p z j : G} (hp : p * (z⁻¹ * j * z) = (z⁻¹ * j * z) * p) :
    ⁅p * z⁻¹, j⁆ = ⁅z⁻¹, j⁆ := by
  simp only [commutatorElement_def]
  calc p * z⁻¹ * j * (p * z⁻¹)⁻¹ * j⁻¹ = (p * (z⁻¹ * j * z) * p⁻¹) * j⁻¹ := by group
    _ = ((z⁻¹ * j * z) * p * p⁻¹) * j⁻¹ := by rw [hp]
    _ = z⁻¹ * j * z⁻¹⁻¹ * j⁻¹ := by group

omit [Finite G] in
theorem k631b_claim {u s : G} {E J J₁ J₀ O : Subgroup G} (hsE : s ∈ E)
    (hcomm : u * s⁻¹ = s⁻¹ * u) (hs : u * s⁻¹ ∈ k631Triv O J)
    (hJ₁u : J₁ ≤ centralizer ({u} : Set G)) (hJ₀J : J₀ ≤ J) (hJ₀J₁ : J₀ ≤ J₁)
    (hfaith : ∀ g ∈ E ⊓ J₁, (∀ j ∈ J₀, ⁅g, j⁆ ∈ O) → g = 1) :
    ∀ x ∈ zpowers s, x ∈ J₁ → x = 1 := by
  intro x hx hxJ₁
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
  have hw : u ^ n * (s ^ n)⁻¹ ∈ k631Triv O J := by
    have h1 := (k631Triv O J).zpow_mem hs n
    rwa [Commute.mul_zpow (show Commute u s⁻¹ from hcomm), inv_zpow] at h1
  have hzE : s ^ n ∈ E := E.zpow_mem hsE n
  refine inv_eq_one.mp (hfaith (s ^ n)⁻¹ ⟨E.inv_mem hzE, J₁.inv_mem hxJ₁⟩ fun j hj => ?_)
  have h1 := (k631b_mem_triv_iff.mp hw).2.2 j (hJ₀J hj)
  have hcJ₁ : (s ^ n)⁻¹ * j * s ^ n ∈ J₁ :=
    J₁.mul_mem (J₁.mul_mem (J₁.inv_mem hxJ₁) (hJ₀J₁ hj)) hxJ₁
  have hcu : u * ((s ^ n)⁻¹ * j * s ^ n) = ((s ^ n)⁻¹ * j * s ^ n) * u :=
    (mem_centralizer_singleton_iff.mp (hJ₁u hcJ₁)).symm
  have hcun : u ^ n * ((s ^ n)⁻¹ * j * s ^ n) = ((s ^ n)⁻¹ * j * s ^ n) * u ^ n :=
    (Commute.zpow_left (show Commute u ((s ^ n)⁻¹ * j * s ^ n) from hcu) n).eq
  rwa [k631b_comm_cancel hcun] at h1

theorem k631b_rank_three (hInn : KFactInnerAction) {f : ℕ} {E F : Subgroup G}
    (ctx : k631b_Ctx f E F) {u a : G} (huF : u ∈ F) (haF : a ∈ F) (ha1 : a ≠ 1)
    (hLa : LayerHyp f (centralizer ({a} : Set G)) E) {J J₁ J₀ : Subgroup G}
    (hJ : GLAPComponent f (centralizer ({a} : Set G)) J) (hJ₁u : J₁ ≤ centralizer ({u} : Set G))
    (hJ₀J : J₀ ≤ J) (hJ₀J₁ : J₀ ≤ J₁) (hEJ₁ : E ⊓ J₁ ≤ J₀)
    (hfaith : ∀ g ∈ E ⊓ J₁,
      (∀ j ∈ J₀, ⁅g, j⁆ ∈ GLAPPrimeCoreOf f (centralizer ({a} : Set G))) → g = 1)
    (hr1 : CFSG.Open.pRank f (E ⊓ J₁) = 2)
    (hu : u ∉ k631Triv (GLAPPrimeCoreOf f (centralizer ({a} : Set G))) J) :
    CFSG.Open.pRank f (E ⊓ J) = 3 := by
  have hf := ctx.prime
  have hf1 : 1 < f := hf.one_lt
  have : Fact f.Prime := ⟨hf⟩
  obtain ⟨s, hsEJ, hs⟩ := k631_comp_inner hInn hLa hJ (ctx.le huF)
  have hs1 : s ≠ 1 := by
    rintro rfl
    exact hu (by simpa using hs)
  have hcomm : u * s⁻¹ = s⁻¹ * u := ctx.mul_comm (ctx.le huF) (E.inv_mem hsEJ.1)
  have hclaim := k631b_claim hsEJ.1 hcomm hs hJ₁u hJ₀J hJ₀J₁ hfaith
  have hEJ : E ⊓ J₁ ≤ E ⊓ J := le_inf inf_le_left (hEJ₁.trans hJ₀J)
  obtain ⟨x, hxs, hxf, hx1⟩ := k631b_exists_order_f hf ctx.pgroup hsEJ.1 hs1
  have hBe : IsElemAbelian f (F ⊓ (E ⊓ J₁)) :=
    CFSG.HardMathSupport.Timmesfeld.Proving.isElemAbelian_of_le ctx.elem inf_le_left
  have hBc : Nat.card (F ⊓ (E ⊓ J₁) : Subgroup G) = f ^ 2 := by
    rw [ctx.card_inf inf_le_left, hr1]
  have hxEJ : x ∈ E ⊓ J := (zpowers_le.mpr hsEJ) hxs
  have hxB : x ∉ F ⊓ (E ⊓ J₁) := fun hxB => hx1 (hclaim x hxs hxB.2.2)
  have h3 : 2 + 1 ≤ CFSG.Open.pRank f (E ⊓ J) :=
    k631b_succ_rank hf hBe hBc (fun y hy => hEJ hy.2) hxEJ hxf hxB
      (fun b hb => ctx.mul_comm hb.2.1 hxEJ.1)
  have haT : a ∈ k631Triv (GLAPPrimeCoreOf f (centralizer ({a} : Set G))) J :=
    k631b_mem_triv (CFSG.LocalAnalysis.GLTheoremB.le_normalizer_glaPPrimeCoreOf f _
      (mem_centralizer_singleton_iff.mpr rfl)) hJ.1
  have h4 : CFSG.Open.pRank f (E ⊓ J) ≤ 3 := by
    obtain ⟨B, hBle, hBe', hBc'⟩ := CFSG.SectionRank.exists_pRank hf1 (E ⊓ J)
    have haB : a ∉ B := by
      intro haB
      have ha' : a ∈ E ⊓ J ⊓ k631Triv (GLAPPrimeCoreOf f (centralizer ({a} : Set G))) J :=
        ⟨hBle haB, haT⟩
      rw [k631_comp_triv_inf hLa hJ, Subgroup.mem_bot] at ha'
      exact ha1 ha'
    have h5 := k631b_succ_rank hf hBe' hBc' (fun y hy => (hBle hy).1) (ctx.le haF)
      (ctx.elem.2 a haF) haB (fun b hb => ctx.mul_comm (hBle hb).1 (ctx.le haF))
    rw [ctx.rank] at h5
    omega
  omega

theorem k631b_round2 (hSch : CatalogueRelativeB.CatalogueSchreier) (hInn : KFactInnerAction)
    {f : ℕ} {E F : Subgroup G} (ctx : k631b_Ctx f E F) (hchar : IsCharTwoType G)
    (hKG : ∀ a : G, a ≠ 1 → IsKGroup ↥(centralizer ({a} : Set G)))
    (hrank : rankThreeLocalRank f G ≤ 3) {u : G} (huF : u ∈ F) (hu1 : u ≠ 1)
    {J₁ : Subgroup G} (hJ₁ : GLAPComponent f (centralizer ({u} : Set G)) J₁)
    (hr0 : CFSG.Open.pRank f
      (E ⊓ k631Triv (GLAPPrimeCoreOf f (centralizer ({u} : Set G))) J₁) = 2)
    (hr1 : CFSG.Open.pRank f (E ⊓ J₁) = 2) :
    ∃ a ∈ F, a ≠ 1 ∧ ∃ J : Subgroup G, GLAPComponent f (centralizer ({a} : Set G)) J ∧
      CFSG.Open.pRank f (E ⊓ J) = 3 := by
  have hf := ctx.prime
  have hf1 : 1 < f := hf.one_lt
  have : Fact f.Prime := ⟨hf⟩
  have hLu := k631b_layerHyp ctx hKG hrank huF hu1
  have hu_f : u ^ f = 1 := ctx.elem.2 u huF
  set T := k631Triv (GLAPPrimeCoreOf f (centralizer ({u} : Set G))) J₁ with hT
  set A : Subgroup G := F ⊓ (E ⊓ T) with hA
  have hAe : IsElemAbelian f A :=
    CFSG.HardMathSupport.Timmesfeld.Proving.isElemAbelian_of_le ctx.elem inf_le_left
  have hAc : Nat.card A = f ^ 2 := by rw [hA, ctx.card_inf inf_le_left, hr0]
  have hAF : A ≤ F := inf_le_left
  have hAE : A ≤ E := fun x hx => hx.2.1
  have hAT : A ≤ T := fun x hx => hx.2.2
  have huT : u ∈ T :=
    k631b_mem_triv (CFSG.LocalAnalysis.GLTheoremB.le_normalizer_glaPPrimeCoreOf f _
      (mem_centralizer_singleton_iff.mpr rfl)) hJ₁.1
  have huA : u ∈ A := ⟨huF, ctx.le huF, huT⟩
  obtain ⟨t₁, -, ht₁2, ht₁1, ht₁A⟩ := k631_involution_centralized hLu hJ₁ hAE hAT
  have hAt₁ : A ≤ centralizer ({t₁} : Set G) := fun x hx =>
    mem_centralizer_singleton_iff.mpr (ht₁A x hx)
  obtain ⟨a, haA, ha1, W, hW1, hW2, hWa, hAW, hWA⟩ :=
    k631b_plane_Y hchar hf ctx.ne_two ht₁2 ht₁1 hAt₁ hAe hAc
  have haF : a ∈ F := hAF haA
  have hLa := k631b_layerHyp ctx hKG hrank haF ha1
  have hWLa : W ≤ GLAPLayer f (centralizer ({a} : Set G)) :=
    k631_layer hInn hLa hWa hW2 hAE hWA
  have hr1' : 2 ≤ CFSG.Open.pRank f (E ⊓ J₁) := hr1.ge
  have hau : a ∉ zpowers u := by
    intro hmem
    have hCle : centralizer ({a} : Set G) ≤ centralizer ({u} : Set G) :=
      sr629_centralizer_singleton_le_of_mem_zpowers hf hu1 hu_f hmem ha1
    have hWu : W ≤ GLAPLayer f (centralizer ({u} : Set G)) :=
      k631_layer hInn hLu (hWa.trans hCle) hW2 hAE hWA
    exact k631b_key hf hrank hLu hJ₁ hr1' hAe hAc hAE hAT hW1 hW2 hWu hAW hWA
  have hAeq : zpowers u ⊔ zpowers a = A := by
    have hcu : Nat.card (zpowers u) = f ^ 1 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hu_f hu1, pow_one]
    have hZ : zpowers u ≤ E := zpowers_le.mpr (ctx.le huF)
    obtain ⟨-, hZc⟩ := k631b_sup_zpowers hf (k631b_isElemAbelian_zpowers hu_f) hcu
      (ctx.elem.2 a haF) hau (fun b hb => ctx.mul_comm (hZ hb) (ctx.le haF))
    have hle : zpowers u ⊔ zpowers a ≤ A := sup_le (zpowers_le.mpr huA) (zpowers_le.mpr haA)
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hZc, hAc])
  obtain ⟨J, J₀, hJ, hJ₀J, hJ₀J₁, hEJ₁, hfaith⟩ :=
    k631m_single_component hSch hLu (hKG a ha1) ctx.sylow (ctx.le huF) hu_f (ctx.le haF) hJ₁
        (hAT haA)
  have hEJ : E ⊓ J₁ ≤ E ⊓ J := le_inf inf_le_left (hEJ₁.trans hJ₀J)
  have hr2 : 2 ≤ CFSG.Open.pRank f (E ⊓ J) := hr1'.trans (CFSG.SectionRank.pRank_mono hf1 hEJ)
  have haT : a ∈ k631Triv (GLAPPrimeCoreOf f (centralizer ({a} : Set G))) J :=
    k631b_mem_triv (CFSG.LocalAnalysis.GLTheoremB.le_normalizer_glaPPrimeCoreOf f _
      (mem_centralizer_singleton_iff.mpr rfl)) hJ.1
  have hunot : u ∉ k631Triv (GLAPPrimeCoreOf f (centralizer ({a} : Set G))) J := by
    intro huTa
    have hAle : A ≤ k631Triv (GLAPPrimeCoreOf f (centralizer ({a} : Set G))) J := by
      rw [← hAeq]
      exact sup_le (zpowers_le.mpr huTa) (zpowers_le.mpr haT)
    exact k631b_key hf hrank hLa hJ hr2 hAe hAc hAE hAle hW1 hW2 hWLa hAW hWA
  exact ⟨a, haF, ha1, J, hJ,
    k631b_rank_three hInn ctx huF haF ha1 hLa hJ hJ₁.1 hJ₀J hJ₀J₁ hEJ₁ hfaith hr1 hunot⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
