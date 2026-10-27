module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Ambient
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.NoUp
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Single
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Prof
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.LitCyclic
import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Final
import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.SolStdInL

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup Relation CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

@[expose] def Thm24Hex (s' : TauCeti.SporadicName) : Prop :=
  ∀ (X : Type) [Group X], CFSG.IsQuasisimple X → Odd (Nat.card (center X)) →
    IsSporadic (X ⧸ center X) s' →
      (¬ ∃ n : ℕ, 5 ≤ n ∧ Nonempty (X ≃* alternatingGroup (Fin n))) ∧
        ¬ CFSG.Blueprint.LieModel X .PSL 3 2 2 ∧ ¬ CFSG.Blueprint.SuzukiModel X 2 3 ∧
        ¬ CFSG.Blueprint.LieModel X .G2 0 2 2

@[expose] def FourAFacts (IsK : GroupClass) (S : List TauCeti.SporadicName) : Prop :=
  ∃ (Q : GroupClass) (tw : Prop), (tw → TwoSylowStd S) ∧
    (∀ (X Y : Type) [Group X] [Group Y] (f : X →* Y), Function.Injective f → Q Y → Q X) ∧
    (∀ (G : Type) [Group G] [Finite G] (L K₁ N₀ T : Subgroup G) (s : G),
      (∃ s' ∈ S, OddCover s' L) → T ≠ ⊥ → Sol78Link5bData K₁ L T s → CFSG.IsQuasisimple ↥K₁ →
        IsK (↥K₁ ⧸ CFSG.oddCore ↥K₁) → CanLoc K₁ N₀ →
        (∀ P : Sylow 2 (centralizer (L : Set G)), IsCyclic ↥P) →
        (tw → ∀ P : Sylow 2 (centralizer (L : Set G)), Nat.card ↥P = 2) → Q ↥(lam L N₀)) ∧
    (∀ (K₂ : Type) [Group K₂] [Finite K₂], Group.IsPerfect K₂ →
      (∃ (X : Type) (_ : Group X), IsK X ∧ Nonempty ((K₂ ⧸ center K₂) ≃* (X ⧸ center X))) →
      ∀ α : MulAut K₂, α ≠ 1 → α * α = 1 →
        ¬ Q (↥(fixSubgroup α) × Multiplicative (ZMod 2)) ∧
          ((∃ k : K₂, α = MulAut.conj k) → ¬ Q ↥(fixSubgroup α))) ∧
    (∀ (G : Type) [Group G] [Finite G] (K₁ N₀ : Subgroup G), CFSG.IsQuasisimple ↥K₁ →
      IsK (↥K₁ ⧸ CFSG.oddCore ↥K₁) → CanLoc K₁ N₀ → ∀ (Y : Type) [Group Y] [Finite Y], Q Y →
        ¬ IsSectionOf ↥((N₀.subgroupOf K₁).map (QuotientGroup.mk' (center ↥K₁))) Y)

structure Hyp31RowFacts (IsK : GroupClass) (S Up Lo : List TauCeti.SporadicName) : Prop where
  reach : ∃ R : GroupClass, ReachRow IsK S Up Lo R
  evenOut : ∀ s ∈ S, EvenCoverOutHered Up s
  up : UpFacts Up
  thm24 : ∀ s ∈ S, s = .M ∨ (s ≠ .M ∧ Thm24Hex s)
  inRows : ∀ s ∈ S, s ∈ Sol78Rows := by decide
  std_row : ∀ (G : Type) [Group G] [Finite G] (L K₁ T : Subgroup G) (s : G),
    (∃ s' ∈ S, OddCover s' L) → T ≠ ⊥ → Sol78Link5bData K₁ L T s → CFSG.IsQuasisimple ↥K₁ →
      IsK (↥K₁ ⧸ CFSG.oddCore ↥K₁) →
        SolStd (K₁.subgroupOf L) ∧ twoAdic (autCentralizer L K₁) ≤ 2
  four_a : FourAFacts IsK S

variable {H : Type} [Group H] [Finite H]

omit [Finite H] in
theorem inL_of_solStd {L : Subgroup H} (h : SolStd L) : InL L :=
  h.inL

omit [Finite H] in
theorem _root_.CFSG.EvenSporadicStandard.Induction.Sol78Link5bData.le_left
    {K₁ L₁ T : Subgroup H} {s : H} (h : Sol78Link5bData K₁ L₁ T s) : K₁ ≤ L₁ := by
  have := h.incl.1
  rw [← h.link.1, sup_idem] at this
  exact this

theorem _root_.CFSG.EvenSporadicStandard.Induction.Sol78Link5bData.lt_of_ne
    {K₁ L₁ T : Subgroup H} {s : H} (h : Sol78Link5bData K₁ L₁ T s) (hT : T ≠ ⊥) :
    Lt K₁ L₁ := by
  have hSN : T ⊔ zpowers s ≤ normalizer (T : Set H) :=
    sup_le Subgroup.le_normalizer (by rw [Subgroup.zpowers_le]; exact h.s_norm)
  refine ⟨T ⊔ zpowers s, T, fun hbot => hT (le_bot_iff.1 (hbot ▸ le_sup_left)), hT,
    isPGroup_sup_zpowers h.T_two h.s_norm h.s_sq, h.T_two, ?_, h.K_comp, h.L_comp, ?_⟩
  · refine Subgroup.commutator_le.2 fun x hx y hy => ⟨?_, ?_⟩
    · have hy' : y ∈ T ⊔ zpowers s := (le_sup_left : T ≤ T ⊔ zpowers s) hy
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy')
        (Subgroup.inv_mem _ hx)) (Subgroup.inv_mem _ hy')
    · have h1 : x * y * x⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 (hSN hx) y).1 hy
      exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hy)
  · refine h.incl.1.trans (sup_le ?_ ?_)
    · exact le_iSup₂_of_le 1 (one_mem _) fun x hx => ⟨x, hx, by simp⟩
    · exact le_iSup₂_of_le s (mem_sup_right (mem_zpowers _)) le_rfl

theorem _root_.CFSG.EvenSporadicStandard.Induction.Sol78Link5bData.inL_left
    {K₁ L₁ T : Subgroup H} {s : H} (h : Sol78Link5bData K₁ L₁ T s) (hT : T ≠ ⊥) : InL K₁ := by
  refine ⟨T ⊔ zpowers s, fun hbot => hT (le_bot_iff.1 (hbot ▸ le_sup_left)),
    isPGroup_sup_zpowers h.T_two h.s_norm h.s_sq, h.K_comp⟩

theorem hyp31OfBelow_of_rowFacts {IsK : GroupClass} {S Up Lo : List TauCeti.SporadicName}
    (rf : Hyp31RowFacts IsK S Up Lo) (lx : Hyp31LitX) :
    Hyp31OfBelowAt IsK S (S ++ Up ++ Lo) Up := by
  intro lit hrow H _ _ ih hUpH N hN hidx hkp L hL hcov
  obtain ⟨R, rr⟩ := rf.reach
  have hjunc : JunctionStmtAt H :=
    Junction.sol78JunctionAt_of_cor23SSec (lit.cor23.sec ih.uHered)
  have ihUp : BelowSec (Sol78PredS Up) H :=
    BelowSec.mono_types (fun s hs => List.mem_append_left _ (List.mem_append_right _ hs)) ih
  have hUp : NoUp Up H :=
    noUp_of_hUp hjunc (lit.thm22 H ih.uHered) ihUp hUpH rf.up hN hidx hkp
  have rc : ReachFacts IsK S Up Lo R :=
    { rr with evenOut := rf.evenOut }
  have c : DescCtx H N IsK S Up Lo R :=
    ⟨hjunc, lit.thm22.sec ih.uHered, ih, hUp, rc, hrow.isK_inv, hN, hidx, hkp⟩
  have hL₀ : InL L := inL_of_solStd hL
  obtain ⟨Q, tw, htw, hQinj, hlam, hfix, hsec⟩ := rf.four_a
  have htab : TwoAdicTable IsK S H := fun L P T s hL hT hdata hPq hK =>
    (rf.std_row H L P T s hL hT hdata hPq hK).2
  have hstdL : ∀ L₁ : Subgroup H, InL L₁ → Maximal L₁ → ∀ s' ∈ S, OddCover s' L₁ →
      SolStd L₁ ∧ ∃ P : Sylow 2 (centralizer (L₁ : Set H)), IsCyclic ↥P := by
    intro L₁ hL₁ hmax s' hs' hcov₁
    have hrank : 3 ≤ CFSG.pRank 2 ↥L₁ :=
      (hrow.quasi_L ↥L₁ ⟨s', hs', hcov₁⟩).2.2
    have hstd : StdBare L₁ :=
      stdBare_of_maximal (lit.thm22 H ih.uHered) hkp hN hidx hmax hrank
    have hsol : SolStd L₁ := solStd_of_inL_of_stdBare hL₁ hstd
    exact ⟨hsol, cyclic_sylow_of_lit lit.toSol78LitCore lx.oddLie hN hidx hkp hsol
      (rf.inRows s' hs') hcov₁⟩
  refine ⟨⟨hN, hidx, ?_, ?_, ?_, ?_⟩, ⟨?_⟩⟩
  ·
    intro L₁ hL₁ hLS
    obtain ⟨s', hs', hq, hodd, hsp⟩ := hLS
    have hcov₁ : OddCover s' L₁ := ⟨hq, hodd, hsp⟩
    have hmax : Maximal L₁ :=
      maximal_of_central_type hjunc ih hUp hN hidx hkp hL₁
        (List.mem_append_left _ (List.mem_append_left _ hs')) hsp
        (rc.fi23 s' (List.mem_append_left Up hs')) (rc.evenOut s' hs')
        (rc.sp_not_exc s' (List.mem_append_left Up hs'))
    exact ⟨hmax, (hstdL L₁ hL₁ hmax s' hs' hcov₁).2⟩
  ·
    intro K₁ hK₁L hK₁ G₁ hNG
    exact not_max_of_reach c hL₀ hcov hK₁L hK₁ hNG
  ·
    intro K₁ L₁ hK₁L hK₁ hL₁L h
    rcases desc_of_reach c hL₀ hcov hK₁L hK₁ h with h1 | ⟨hty, hK⟩
    · exact Or.inl h1
    · exact Or.inr ⟨hty, hK⟩
  ·
    intro K₁ L₁ T s hT hmax hdata hK
    have hK₁L : InL K₁ := hdata.inL_left hT
    have hKL : K₁ ≤ L₁ := hdata.le_left
    obtain ⟨hty, -⟩ := single_link_of_lt_le c hL₀ hcov htab hK₁L hmax (hdata.lt_of_ne hT) hKL hK
    exact rf.std_row H L₁ K₁ T s hty hT hdata hK₁L.isQuasisimple hK
  ·
    intro K₁ L₁ hK₁L hmax hlt hKL hK N₀ hcan
    obtain ⟨hty, T, s, hT, hdata⟩ := single_link_of_lt_le c hL₀ hcov htab hK₁L hmax hlt hKL hK
    obtain ⟨s', hs', hcov₁⟩ := hty
    obtain ⟨hsol, hcyc⟩ := hstdL L₁ hmax.1 hmax s' hs' hcov₁
    have hcyc' := forall_sylow_isCyclic hcyc
    have hq : CFSG.IsQuasisimple ↥K₁ := hK₁L.isQuasisimple
    have hQΛ : Q ↥(lam L₁ N₀) :=
      hlam H L₁ K₁ N₀ T s ⟨s', hs', hcov₁⟩ hT hdata hq hK hcan hcyc'
        (fun htw' => htw htw' s' hs' H N L₁ hN hidx hkp hcov₁ hsol hcyc)
    refine ⟨?_, ?_⟩
    ·
      rintro ⟨A, f, hf⟩
      exact hsec H K₁ N₀ hq hK hcan ↥(lam L₁ N₀) hQΛ ⟨A, f, hf⟩
    ·
      intro K₂ _ _ hperf hiso α hα1 hα2
      obtain ⟨e₂⟩ := hiso
      have : Group.IsPerfect ↥K₁ := hq.1
      obtain ⟨e₃⟩ := cqEquiv_of_cover (QuotientGroup.mk' (CFSG.oddCore ↥K₁))
        (QuotientGroup.mk'_surjective _) (by
          rw [QuotientGroup.ker_mk']
          exact oddCore_le_center hq)
      obtain ⟨h1, h2⟩ := hfix K₂ hperf ⟨_, inferInstance, hK, ⟨e₂.trans e₃⟩⟩ α hα1 hα2
      exact ⟨fun ⟨f, hf⟩ => h1 (hQinj _ _ f hf hQΛ),
        fun hin' ⟨f, hf⟩ => h2 hin' (hQinj _ _ f hf hQΛ)⟩

theorem fourAFacts_of_lamProfile {IsK : GroupClass} {S : List TauCeti.SporadicName}
    (ab : Prop) (m e : ℕ) (hm : m ≤ 2)
    (hautC : ∀ (G : Type) [Group G] [Finite G] (L K₁ N₀ T : Subgroup G) (s : G),
      (∃ s' ∈ S, OddCover s' L) → T ≠ ⊥ → Sol78Link5bData K₁ L T s → CFSG.IsQuasisimple ↥K₁ →
        IsK (↥K₁ ⧸ CFSG.oddCore ↥K₁) → CanLoc K₁ N₀ →
          Group.IsSolvable ↥(autCentralizer L N₀) ∧ twoAdic (autCentralizer L N₀) ≤ m ∧
          ElemBound e ↥(autCentralizer L N₀) ∧
          (ab → ∀ α ∈ autCentralizer L N₀, ∃ g : ↥L, α = MulAut.conj g))
    (hfix : ∀ (K₂ : Type) [Group K₂] [Finite K₂], Group.IsPerfect K₂ →
      (∃ (X : Type) (_ : Group X), IsK X ∧ Nonempty ((K₂ ⧸ center K₂) ≃* (X ⧸ center X))) →
      ∀ α : MulAut K₂, α ≠ 1 → α * α = 1 →
        ¬ LamProfile ab (2 * e) (↥(fixSubgroup α) × Multiplicative (ZMod 2)) ∧
          ((∃ k : K₂, α = MulAut.conj k) → ¬ LamProfile ab (2 * e) ↥(fixSubgroup α)))
    (hsec : ∀ (G : Type) [Group G] [Finite G] (K₁ N₀ : Subgroup G), CFSG.IsQuasisimple ↥K₁ →
      IsK (↥K₁ ⧸ CFSG.oddCore ↥K₁) → CanLoc K₁ N₀ →
        ¬ (Group.IsSolvable ↥((N₀.subgroupOf K₁).map (QuotientGroup.mk' (center ↥K₁))) ∧
          (ab → TwoSubgroupsAbelian
            ↥((N₀.subgroupOf K₁).map (QuotientGroup.mk' (center ↥K₁)))))) :
    FourAFacts IsK S := by
  refine ⟨fun X _ => LamProfile ab (2 * e) X, False, fun h => h.elim,
    fun X Y _ _ f hf h => h.of_injective hf, ?_, hfix, ?_⟩
  · intro G _ _ L K₁ N₀ T s hL hT hdata hq hK hcan hcyc _
    obtain ⟨hAs, hA, he, hin⟩ := hautC G L K₁ N₀ T s hL hT hdata hq hK hcan
    obtain ⟨s', -, hcov⟩ := hL
    have hN₀L : N₀ ≤ L := hcan.le.trans hdata.le_left
    exact ⟨lam_isSolvable hcyc hAs, elemBound_lam_of_elem hcyc he,
      fun hab => twoSubgroupsAbelian_lam hm hcyc hA (hin hab) hN₀L hcov.2.1⟩
  · intro G _ _ K₁ N₀ hq hK hcan Y _ _ hY ⟨A, f, hf⟩
    have := hY.1
    have hAs : Group.IsSolvable ↥A := Group.isSolvable_of_isSolvable_injective A.subtype_injective
    exact hsec G K₁ N₀ hq hK hcan ⟨Group.isSolvable_of_surjective hf, fun hab =>
      twoSubgroupsAbelian_of_section (hY.2.2 hab) ⟨A, f, hf⟩⟩

end CFSG.EvenSporadicStandard.Induction.Hyp
