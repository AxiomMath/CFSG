module

public import CFSG.LocalAnalysis.GLTheoremA.Lemma44

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_sSup {S : Set (Subgroup G)} {g : G}
    (h : ∀ L ∈ S, g ∈ Subgroup.normalizer (L : Set G)) :
    g ∈ Subgroup.normalizer ((sSup S : Subgroup G) : Set G) := by
  have key : ∀ g' : G, (∀ L ∈ S, g' ∈ Subgroup.normalizer (L : Set G)) →
      sSup S ≤ GLBConj g' (sSup S) := fun g' hg' =>
    sSup_le fun L hL => by
      rw [← mem_normalizer_iff_gLBConj_eq.1 (hg' L hL)]
      exact gLBConj_mono (le_sSup hL)
  rw [mem_normalizer_iff_gLBConj_eq]
  refine le_antisymm ?_ (key g h)
  have h' := gLBConj_mono (g := g) (key g⁻¹ fun L hL => Subgroup.inv_mem _ (h L hL))
  rwa [gLBConj_gLBConj, inv_mul_cancel, gLBConj_one] at h'

theorem card_eq_card_pQuot_mul (p : ℕ) (K : Subgroup G) :
    Nat.card K = Nat.card (PQuot p K) * Nat.card (GLAPPrimeCoreOf p K) := by
  rw [GLAPPrimeCoreOf, Subgroup.card_map_of_injective K.subtype_injective]
  exact Subgroup.card_eq_card_quotient_mul_card_subgroup _

theorem card_pQuot_lt_of_le_normalizer {p : ℕ} (hp : p.Prime) {M N : Subgroup G} (hMN : M ≤ N)
    (hNM : N ≤ Subgroup.normalizer (M : Set G)) (hne : ¬ N ≤ M ⊔ GLAPPrimeCoreOf p N) :
    Nat.card (PQuot p M) < Nat.card (PQuot p N) := by
  set O := GLAPPrimeCoreOf p N with hO
  have hsn : IsSubnormal M N :=
    IsSubnormal.step hMN ((Subgroup.normal_subgroupOf_iff_le_normalizer hMN).2 hNM)
      (IsSubnormal.refl N)
  have hMO : M ⊓ O = GLAPPrimeCoreOf p M := glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hsn
  have hON : O ≤ N := Subgroup.map_subtype_le _
  have hMnO : M ≤ Subgroup.normalizer (O : Set G) := hMN.trans (le_normalizer_glaPPrimeCoreOf p N)
  have h1 := card_sup_mul_card_inf_of_le_normalizer hMnO
  rw [sup_comm, inf_comm, hMO] at h1
  have h2 := card_eq_card_pQuot_mul p M
  have h3 := card_eq_card_pQuot_mul p N
  have hpos : 0 < Nat.card (GLAPPrimeCoreOf p M) := Nat.card_pos
  have hs : Nat.card (M ⊔ O : Subgroup G) = Nat.card (PQuot p M) * Nat.card O := by
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [h1, h2]
    ring
  have hle : M ⊔ O ≤ N := sup_le hMN hON
  have hlt : Nat.card (M ⊔ O : Subgroup G) < Nat.card N := by
    refine lt_of_le_of_ne (Subgroup.card_le_of_le hle) fun h => hne ?_
    exact (Subgroup.eq_of_le_of_card_ge hle h.ge).ge
  rw [hs, h3] at hlt
  exact Nat.lt_of_mul_lt_mul_right hlt

theorem card_pQuot_sSup_le_mxB {p : ℕ} (hp : p.Prime) {Exc Club : Subgroup G → Prop}
    (hEC : ExcClubHyp G p Exc Club) (h183 : Input18_3_4) (hKP : CFSG.Open.IsKProper G)
    (hsimple : IsSimpleGroup G) (hnonab : ∃ a b : G, a * b ≠ b * a)
    {B' : Subgroup G} {x x' : G} (hB' : GLAIsBmax p B') (hx' : IsEssential p B' x')
    (hxB' : x ∈ B') (S : Set (Subgroup G))
    (hS : ∀ L ∈ S, GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L ∧
      B' ≤ Subgroup.normalizer (L : Set G) ∧ CentMod p L x' ∧ ¬ Club L) :
    Nat.card (PQuot p (sSup S)) ≤ mxB p Club B' x' := by
  classical
  set Cx' := Subgroup.centralizer ({x'} : Set G)
  have hx'p : IsPGroup p (Subgroup.zpowers x') := isPGroup_zpowers_of_mem hB'.1 hx'.1
  have hSX : sSup S ≤ Subgroup.centralizer ({x} : Set G) := sSup_le fun L hL => (hS L hL).1.1
  have hI : ∀ L ∈ S, GLAPLayer p (L ⊓ Cx') ≤ L ∧
      GLAPLayer p (L ⊓ Cx') ⊔ GLAPPrimeCoreOf p L = L := fun L hL => by
    obtain ⟨hIc, -, -, -, hsup, -⟩ := glaPLayer_inf_centralizer hp (hS L hL).1 hx'p (hS L hL).2.2.1
    exact ⟨hIc.1.trans inf_le_left, hsup⟩
  set H : Subgroup G := ⨆ L ∈ S, GLAPLayer p (L ⊓ Cx')
  have hHS : H ≤ sSup S := iSup₂_le fun L hL => (hI L hL).1.trans (le_sSup hL)
  refine card_pQuot_le_of_cover hp hHS (le_antisymm (sup_le hHS (Subgroup.map_subtype_le _))
    (sSup_le fun L hL => ?_)) (iSup₂_le fun L hL => ?_)
  · rw [← (hI L hL).2]
    refine sup_le_sup (le_biSup (fun L => GLAPLayer p (L ⊓ Cx')) hL) ?_
    have hsn : IsSubnormal L (sSup S) :=
      isSubnormal_of_le_of_le (hS L hL).1.2.1 (le_sSup hL) hSX
    rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hsn]
    exact inf_le_right
  · obtain ⟨hLc, hB'L, hx'L, hnc⟩ := hS L hL
    exact (le_closureIn_self _ _).trans
      (le_MxB (lemma44b_closure hp hEC h183 hKP hsimple hnonab hB' hx' hxB' hB'L hLc hx'L hnc).1)

theorem lemma45 {p : ℕ} (hp : p.Prime) {Exc Club : Subgroup G → Prop}
    (hEC : ExcClubHyp G p Exc Club) (h183 : Input18_3_4) (hKP : CFSG.Open.IsKProper G)
    (hsimple : IsSimpleGroup G) (hnonab : ∃ a b : G, a * b ≠ b * a)
    {B B' : Subgroup G} {x x' : G} (hB' : GLAIsBmax p B') (hxB' : x ∈ B')
    (hdec : ∀ b ∈ B', ∃ u ∈ B ⊓ B', ∃ v ∈ B',
      (∀ K, IsGoodComp p Club B x K → CentMod p K v) ∧ b = u * v)
    (hx' : IsEssential p B' x') (hx'M : ∀ K, IsGoodComp p Club B x K → CentMod p K x') :
    mxB p Club B x ≤ mxB p Club B' x' := by
  refine card_pQuot_sSup_le_mxB hp hEC h183 hKP hsimple hnonab hB' hx' hxB' _
    fun K hK => ⟨hK.1, fun b hb => ?_, hx'M K hK, hK.2.2⟩
  obtain ⟨u, hu, v, -, hv, rfl⟩ := hdec b hb
  exact Subgroup.mul_mem _ (hK.2.1 hu.1) (hv K hK).1

end CFSG.LocalAnalysis.GLTheoremA
