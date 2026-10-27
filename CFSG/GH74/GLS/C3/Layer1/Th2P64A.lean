module

public import CFSG.GH74.GLS.C3.Layer1.Th2V2ss
public import CFSG.GH74.GLS.C3.Layer1.Th2P73
public import CFSG.GH74.GLS.C3.Layer1.Th2L627Syl
public import CFSG.GH74.GLS.C3.Layer1.Th2P61Strong
public import CFSG.GH74.GLS.C3.Layer1.St1RigMain

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.C3.Layer1.PumpRigid
  CFSG.GH74.GLS.Th2

@[expose] def B_a7_rigid_step : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (u : G) (L : Subgroup G) (u' : G) (L' : Subgroup G),
    PumpUpLT 2 u L u' L' → Nonempty (kBar L ≃* alternatingGroup (Fin 7)) →
      Nonempty (kBar L' ≃* alternatingGroup (Fin 7))

@[expose] def B_thm1_A7_any : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (u v : G) (L : Subgroup G),
    Is2TerminalU2Triple u v L → Nonempty (kBar L ≃* alternatingGroup (Fin 7)) →
      2 < twoPartCard (CxK u L) → 2 ≤ pRank 2 ↥(CxK u L) ∨ IsExceptionalA7Triple u v L

@[expose] def A7StepClosure (G : Type) [Group G] : Prop :=
  ∀ (u : G) (L : Subgroup G) (u' : G) (L' : Subgroup G),
    PumpUpLT 2 u L u' L' →
      Nonempty (kBar L ≃* alternatingGroup (Fin 7)) →
        Nonempty (kBar L' ≃* alternatingGroup (Fin 7))

section Stage

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_CxK_self' {t : G} {J : Subgroup G} (hJC : J ≤ centralizer ({t} : Set G)) :
    t ∈ CxK t J := by
  refine ⟨mem_centralizer_singleton_iff.2 rfl,
    C3.Layer1.Back.mem_centralizerSection_of_centralizes ?_ ?_⟩
  · intro k hk
    exact (mem_centralizer_singleton_iff.1 (hJC hk)).symm
  · unfold pPrimeCoreOf
    intro z hz
    obtain ⟨z', -, rfl⟩ := hz
    exact z'.2

theorem a7_rigid_rtg_of_step (hstep : A7StepClosure G) {p q : G × Subgroup G}
    (h : Relation.ReflTransGen (fun a b : G × Subgroup G => PumpUpLT 2 a.1 a.2 b.1 b.2) p q)
    (hA : Nonempty (kBar p.2 ≃* alternatingGroup (Fin 7))) :
    Nonempty (kBar q.2 ≃* alternatingGroup (Fin 7)) := by
  induction h with
  | refl => exact hA
  | tail _ hlt ih => exact hstep _ _ _ _ hlt ih

theorem a7_rigid_long_of_step (hstep : A7StepClosure G) {u u' : G} {L L' : Subgroup G}
    (hlong : LongPumpUp 2 u L u' L') (hA : Nonempty (kBar L ≃* alternatingGroup (Fin 7))) :
    Nonempty (kBar L' ≃* alternatingGroup (Fin 7)) :=
  a7_rigid_rtg_of_step hstep hlong.2 hA

theorem a7_rigid_long (hR : B_a7_rigid_step) (hG : C3Hyp G) {u u' : G} {L L' : Subgroup G}
    (hlong : LongPumpUp 2 u L u' L') (hA : Nonempty (kBar L ≃* alternatingGroup (Fin 7))) :
    Nonempty (kBar L' ≃* alternatingGroup (Fin 7)) :=
  a7_rigid_long_of_step (fun u L u' L' hlt hA => hR G hG u L u' L' hlt hA) hlong hA

theorem prop51a_A7_of
    (h102 : B_ivk_10_2) (h14 : B_prop14) (h103 : B_ivk_10_3) (hL34 : B_gen4_noL34_elem)
    (hA7C2 : B_A7_notC2) (hR : B_a7_rigid_step) (hT1 : B_thm1_A7_any)
    (hG : C3Hyp G) {x y : G} {K : Subgroup G} (hV : IsV2StarTriple x y K)
    (hKA : ¬ Nonempty (kBar K ≃* alternatingGroup (Fin 7)))
    {u : G} {L : Subgroup G} (hL : IsIL2Pair u L)
    (hA : Nonempty (kBar L ≃* alternatingGroup (Fin 7))) :
    twoPartCard (CxK u L) = 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hr4 : pRank 2 G = 4 := hG.pRank_eq_four
  have hKU : InU2 (kBar K) := h102 G hG x y K hV.1.1.1.1.1
  have hU2 : ∀ {u : G} {L : Subgroup G}, IsIL2Pair u L →
      Nonempty (kBar L ≃* alternatingGroup (Fin 7)) → InU2 (kBar L) :=
    fun hL hA => ⟨TwoThin.isQuasisimple_hat hL.2, Or.inr (Or.inl hA)⟩
  have hone : ∀ {u : G} {L : Subgroup G}, IsIL2Pair u L → 1 ≤ pRank 2 ↥(CxK u L) ∧
      2 ≤ twoPartCard (CxK u L) := by
    intro u L hL
    have hz : IsPGroup 2 ↥(zpowers u) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hL.1]; norm_num)
    have hzle : zpowers u ≤ CxK u L := zpowers_le.2 (mem_CxK_self' hL.2.1)
    refine ⟨?_, ?_⟩
    · have := C3.Layer1.Back.pRank_mono' hzle
      rwa [Th2.pRank_zpowers_of_orderOf_two hL.1] at this
    · have := Th2.L627.card_le_twoPartCard hz hzle
      rwa [Nat.card_zpowers, hL.1] at this
  by_contra hne
  have hlt : 2 < twoPartCard (CxK u L) := lt_of_le_of_ne (hone hL).2 (Ne.symm hne)
  let 𝒮 : Set (G × Subgroup G) := {p | IsIL2Pair p.1 p.2 ∧
    Nonempty (kBar p.2 ≃* alternatingGroup (Fin 7)) ∧ 2 < twoPartCard (CxK p.1 p.2)}
  have hne𝒮 : Nonempty ↥𝒮 := ⟨⟨(u, L), hL, hA, hlt⟩⟩
  obtain ⟨⟨⟨u₀, L₀⟩, hL₀, hA₀, hc₀⟩, hmax⟩ := Finite.exists_max
    (fun p : ↥𝒮 => toLex (pRank 2 ↥(CxK p.1.1 p.1.2), sylVal p.1.1 p.1.2))
  simp only at hL₀ hA₀ hc₀
  have hU₀ := hU2 hL₀ hA₀
  have hILo₀ : IsILo 2 u₀ L₀ := by
    refine ⟨hL₀.1, ?_, hL₀.2⟩
    have := h14 G hG u₀ L₀ hL₀ hU₀
    simp only [oBound, ite_true]
    omega
  have hrig : IsPRigid 2 u₀ L₀ := ⟨hILo₀, fun u' L' hlong => by
    obtain ⟨e₁⟩ := hA₀
    obtain ⟨e₂⟩ := a7_rigid_long hR hG hlong ⟨e₁⟩
    exact ⟨e₂.trans e₁.symm⟩⟩
  have hgm : IsGilmanMax u₀ L₀ := by
    intro u' L' hlong
    by_contra hnot
    push Not at hnot
    have hILo' : IsILo 2 u' L' := hlong.isILo_right
    have hA' := a7_rigid_long hR hG hlong hA₀
    have hpair' : IsIL2Pair u' L' := ⟨hILo'.1, hILo'.2.2⟩
    have hrk0 := (hone hL₀).1
    have hsyl0 : 2 ≤ sylVal u₀ L₀ := by
      by_contra h
      push Not at h
      have : twoPartCard (CxK u₀ L₀) ≤ 2 ^ 1 := by
        show 2 ^ sylVal u₀ L₀ ≤ 2 ^ 1
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hlt' : 2 < twoPartCard (CxK u' L') := by
      by_cases hrk : pRank 2 ↥(CxK u' L') = pRank 2 ↥(CxK u₀ L₀)
      · have h1 := hnot.2 hrk
        show 2 < 2 ^ sylVal u' L'
        calc 2 < 2 ^ 2 := by norm_num
          _ ≤ 2 ^ sylVal u' L' := Nat.pow_le_pow_right (by norm_num) (by omega)
      · have hrk2 : 2 ≤ pRank 2 ↥(CxK u' L') := by omega
        obtain ⟨E, hE, hEel, hErk⟩ := Th2.exists_elemAbelian_pRank (CxK u' L')
        have hcard := C3.Layer1.Back.card_eq_two_pow_pRank hEel
        have hle := Th2.L627.card_le_twoPartCard (CFSG.IsElementaryAbelian.isPGroup 2 ↥E) hE
        have h4 : 2 ^ 2 ≤ 2 ^ pRank 2 ↥E :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        rw [hcard] at hle
        omega
    have hmem : (u', L') ∈ 𝒮 := ⟨hpair', hA', hlt'⟩
    have hle := hmax ⟨(u', L'), hmem⟩
    rw [Prod.Lex.le_iff] at hle
    simp only [ofLex_toLex] at hle
    omega
  have hR3 : ∀ y : G, orderOf y = 2 → 3 ≤ pRank 2 ↥(centralizer ({y} : Set G)) := fun y hy =>
    rankThreeCentralizers G hG.kproper.1 hG.kproper.2.1 (by rw [hr4]; norm_num) y hy
  have hterm : IsTwoTerminal u₀ L₀ :=
    isTwoTerminal_of_noDiag hrig hgm (noDiag_of_rigid_gilman hR3 hrig hgm)
  have hbad : ¬ InC2 (kBar L₀) := by
    obtain ⟨e⟩ := hA₀
    exact fun h => hA7C2 (CFSG.GH74.E2.inC2_of_mulEquiv e h)
  obtain ⟨v, hv⟩ := h103 G hG u₀ L₀ hL₀ hU₀ hbad
  have hstar : IsStar2 u₀ := by
    refine ⟨hL₀.1, le_antisymm (le_of_le_of_eq (pRank_le_top' _) rfl) ?_⟩
    have := h14 G hG u₀ L₀ hL₀ hU₀
    omega
  have hcen : center (kBar L₀) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    exact centerlessBar_of_A7 hA₀ z (fun b => (Subgroup.mem_center_iff.1 hz b).symm)
  have hT2 : Is2TerminalU2Triple u₀ v L₀ := by
    refine ⟨hv, hterm, hstar, ?_, ?_⟩
    · intro hl34
      exfalso
      refine hL34 G hG.gen4 u₀ L₀ hL₀.1 hL₀.2 ⟨hl34, ?_, ?_⟩
      · rw [hcen]; exact isElementaryAbelian_bot
      · rw [hcen, Subgroup.card_bot]; norm_num
    · intro h9
      exact absurd hA₀ (Th2.not_nonempty_A7_of_hasL2Model h9)
  have hdich := hT1 G hG u₀ v L₀ hT2 hA₀ hc₀
  have hV2 : IsV2Triple u₀ v L₀ := ⟨hv, hterm, hdich, fun _ => hT2⟩
  exact hV.1.1.1.2 u₀ v L₀ hV2 ⟨hU₀, hKU, Or.inl ⟨hA₀, hKA⟩⟩

theorem cor62b_of
    (h102 : B_ivk_10_2) (h14 : B_prop14) (h103 : B_ivk_10_3) (hL34 : B_gen4_noL34_elem)
    (hA7C2 : B_A7_notC2) (hR : B_a7_rigid_step) (hT1 : B_thm1_A7_any)
    (hG : C3Hyp G) {x y : G} {K : Subgroup G} (hV : IsV2StarTriple x y K)
    (hKA : ¬ Nonempty (kBar K ≃* alternatingGroup (Fin 7)))
    {B : Subgroup G} {b : G} {J : Subgroup G} (hBel : CFSG.IsElementaryAbelian 2 ↥B)
    (hobs : Th2.Obs.Obstr52 B b J) (hA : Nonempty (kBar J ≃* alternatingGroup (Fin 7))) :
    twoPartCard (CxK b J) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hBel
  have hb2 : orderOf b = 2 := orderOf_eq_prime (by rw [sq]; exact hBsq b hobs.mem) hobs.ne_one
  exact prop51a_A7_of h102 h14 h103 hL34 hA7C2 hR hT1 hG hV hKA ⟨hb2, hobs.comp⟩ hA

end Stage

end CFSG.GH74.GLS
