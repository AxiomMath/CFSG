module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3AInnerLay
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514Ns
  CFSG.RankThree.PartTwo.KFacts

theorem center_barOf_eq_bot_of_extremal {G : Type} [Group G] [Finite G] {X L : Subgroup G}
    (hL : GLAPComponent 3 X L) (hty : IsExtremalType (barOf 3 L)) :
    Subgroup.center (barOf 3 L) = ⊥ := by
  have e := quotEquivBarX Nat.prime_three hL.1 hL.2.1
  exact center_eq_bot_of_mulEquiv' e (center_barX_of_isExtremalType hL hty)

theorem center_barOf_comp_eq_bot {G : Type} [Group G] [Finite G] {X L J : Subgroup G} {x : G}
    (hL : GLAPComponent 3 X L) (hty : IsExtremalType (barOf 3 L))
    (hxN : x ∈ Subgroup.normalizer (L : Set G)) (hx3 : x ^ 3 = 1)
    (hfld : IsFieldAutThree (barAut 3 L ⟨x, hxN⟩))
    (hJ : GLAPComponent 3 (L ⊓ Subgroup.centralizer ({x} : Set G)) J) :
    Subgroup.center (barOf 3 J) = ⊥ := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hZL := center_barOf_eq_bot_of_extremal hL hty
  have hqL : CFSG.Open.IsQuasisimple (barOf 3 L) := isQuasisimple_quotient_of_glaPComponent hL
  have hJL : J ≤ L := hJ.1.trans inf_le_left
  obtain ⟨-, hcen⟩ := amb_centre gap510_Centre_holds hL (Or.inl hty) hxN hx3 hfld hJ
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥J) z
  have hjp : QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) j ∈ CFSG.pCore 3 (↥J ⧸ GLAPPrimeCore 3 ↥J) :=
    mem_pCore_of_forall_comm_aux hp fun w => (Subgroup.mem_center_iff.1 hz w)
  have hjO : (j : G) ∈ oPrimePOf 3 J := ⟨j, hjp, rfl⟩
  have hjL := hcen ⟨j.2, hjO⟩
  obtain ⟨l, hl, hll⟩ := hjL
  have hlc : QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) l ∈ Subgroup.center (barOf 3 L) :=
    pCore_le_center hp hqL hl
  rw [hZL, Subgroup.mem_bot] at hlc
  have hlcore : l ∈ GLAPPrimeCore 3 ↥L := (QuotientGroup.eq_one_iff _).1 hlc
  have hjcore : (j : G) ∈ GLAPPrimeCoreOf 3 L := by
    rw [← hll]
    exact (mem_GLAPPrimeCore_iff l).1 hlcore
  have h3 : GLAPPrimeCoreOf 3 L ⊓ J ≤ GLAPPrimeCoreOf 3 J := by
    have := gLAPPrimeCoreOf_inf_le hp L J
    rwa [inf_eq_right.2 hJL] at this
  have hjJ : (j : G) ∈ GLAPPrimeCoreOf 3 J := h3 ⟨hjcore, j.2⟩
  rw [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff _).2 ((mem_GLAPPrimeCore_iff j).2 hjJ)

theorem exists_centreless_comp {G : Type} [Group G] [Finite G] {m : ℕ} (hS : GLStanding G m 3)
    {b x : G} {L : Subgroup G} (hb3 : b ^ 3 = 1) (hx3 : x ^ 3 = 1) (hb1 : b ≠ 1)
    (hLC : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L)
    (hty : IsExtremalType (barOf 3 L)) (hxN : x ∈ Subgroup.normalizer (L : Set G))
    (hfld : IsFieldAutThree (barAut 3 L ⟨x, hxN⟩))
    (hK : GLAPComponent 3 (Subgroup.centralizer ({x} : Set G)) (pumpUp L x))
    (hbK : InducesFieldAut 3 (pumpUp L x) b) :
    ∃ S : Subgroup (barOf 3 (pumpUp L x)),
      GLAPComponent 3 (fixSub (barAut 3 (pumpUp L x) ⟨b, hbK.1⟩)) S ∧
        Subgroup.center (barOf 3 S) = ⊥ := by
  have := hS.simple
  have hp : (3 : ℕ).Prime := Nat.prime_three
  set Cb : Subgroup G := Subgroup.centralizer ({b} : Set G) with hCb
  set Cx : Subgroup G := Subgroup.centralizer ({x} : Set G) with hCx
  have hCbne : Cb ≠ ⊤ := centralizer_ne_top_of_simple hS.nonabelian hb1
  have hne := amb_nontrivial gap510_Nontrivial_holds hLC (Or.inl hty) hxN hx3 hfld
  obtain ⟨J, hJ⟩ : ∃ J : Subgroup G, GLAPComponent 3 (L ⊓ Cx) J := by
    by_contra hno
    push Not at hno
    apply hne
    have : {J : Subgroup G | GLAPComponent 3 (L ⊓ Cx) J} = ∅ := Set.eq_empty_of_forall_notMem hno
    show sSup {J : Subgroup G | GLAPComponent 3 (L ⊓ Cx) J} = ⊥
    rw [this, sSup_empty]
  have hNKL : CFSG.Open.IsKGroup ↥(Subgroup.normalizer (L : Set G)) := by
    refine isKGroup_of_isKProper hS.kProper ?_
    intro htop
    have hnorm : L.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal L with h | h
    · exact glaPComponent_ne_bot hLC h
    · apply hCbne
      rw [← top_le_iff, ← h]
      exact hLC.1
  have hJu : ∀ J' : Subgroup G, GLAPComponent 3 (L ⊓ Cx) J' → J' = J := fun J' hJ' =>
    eq_of_glaPComponent_inf_centralizer input14_5L3_holds (Or.inl hty) hNKL hLC hxN hx3 hJ' hJ
  have hlayer : GLAPLayer 3 (L ⊓ Cx) = J :=
    le_antisymm (sSup_le fun A hA => (hJu A hA).le) (le_sSup hJ)
  have hpump : pumpUp L x = ⨆ g ∈ GLAPLayer 3 Cx, GLBConj g J := by
    unfold pumpUp; rw [hlayer]
  have hJK : J ≤ pumpUp L x := by
    have := le_iSup₂ (f := fun g (_ : g ∈ GLAPLayer 3 Cx) => GLBConj g J)
      1 (Subgroup.one_mem _)
    rw [gLBConj_one] at this
    rw [hpump]
    exact this
  have hJC : GLAPComponent 3 (Cb ⊓ Cx) J := glaPComponent_inf_centralizer hLC x hJ
  have hJC' : GLAPComponent 3 (Cx ⊓ Cb) J := by rwa [inf_comm]
  have hJK' : GLAPComponent 3 (pumpUp L x ⊓ Cb) J :=
    glaPComponent_of_le hp hJC' (le_inf hJK (hJC'.1.trans inf_le_right))
      (inf_le_inf_right _ hK.1)
  have hZJ := center_barOf_comp_eq_bot hLC hty hxN hx3 hfld hJ
  obtain ⟨J₁, hJ₁, hJ₁J⟩ := exists_comp_subgroupOf
    (inf_le_left : pumpUp L x ⊓ Cb ≤ pumpUp L x) hJK'
  refine ⟨J₁.map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥(pumpUp L x))),
    comp_map_fixSub hbK.1 hb3 hJ₁, ?_⟩
  rw [← hJ₁J] at hZJ
  exact center_eq_bot_of_mulEquiv' (liftEquiv J₁).symm hZJ

end CFSG.HardMathSupport.Solomon.Coordinator
