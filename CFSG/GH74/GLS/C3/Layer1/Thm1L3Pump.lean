module

public import CFSG.GH74.GLS.C3.Layer1.St1RigOrd
public import CFSG.GH74.GLS.C3.Layer1.St1PumpH1

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1Pump

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin
  CFSG.GH74.GLS.C3.Layer1.PumpRigid CFSG.GH74.GLS.C3.Layer1.PumpCalc CFSG.GH74.GLS.C3.Layer1.PumpH1
  CFSG.GH74.GLS.C3.Layer1.Bk

variable {G : Type} [Group G] [Finite G]

theorem step_back_of_mem {x t : G} {K K' : Subgroup G} (hlt : PumpUpLT 2 x K t K')
    (hxC : x ∈ CxK t K') (h1 : pRank 2 ↥(CxK t K') ≤ 1) : x = t ∧ K' = K := by
  have hpair' : IsIL2Pair t K' := ⟨hlt.2.1.1, hlt.2.1.2.2⟩
  have hxt : x = t := eq_of_mem_CxK_of_pRank_le_one hpair' hxC hlt.1.1 h1
  have hpair : IsIL2Pair x K := ⟨hlt.1.1, hlt.1.2.2⟩
  have hK' := hlt.2.2.2.2
  rw [← hxt, pumpUp_self hpair.2] at hK'
  exact ⟨hxt, eq_of_isPCompIn_self (isPCompIn_of_le hpair.2 le_rfl hpair.2.1) hK'⟩

theorem step_back_rigid (hr4 : pRank 2 G = 4) {x t : G} {K K' : Subgroup G}
    (hlt : PumpUpLT 2 x K t K') (hs : IsSimpleGroup (kBar K')) (hle : hatCard K' ≤ hatCard K)
    (h1 : pRank 2 ↥(CxK t K') ≤ 1) : x = t ∧ K' = K := by
  have hxY : x ∈ centralizer ({t} : Set G) := mem_centralizer_symm hlt.2.2.1
  obtain ⟨Λ, hΛ, hK'c, -, -, hcent, hcases⟩ := rigid_step hlt hxY hle
  have hpair' : IsIL2Pair t K' := ⟨hlt.2.1.1, hK'c⟩
  have hq : CFSG.IsQuasisimple (kBar K') := isQuasisimple_hat hK'c
  have hcen : center (kBar K') = ⊥ := center_eq_bot_of_isSimple hs hq
  have hxN : x ∈ normalizer (K' : Set G) :=
    PumpGen.mem_normalizer_of_centerless hr4 hpair' hq hcen hxY
  have hvert : bar t Λ = bar t K' := (hcases.resolve_right (fun h => h.1 hxN)).2
  have hpair : IsIL2Pair x K := ⟨hlt.1.1, hlt.1.2.2⟩
  have hxC : x ∈ CxK t K' := mem_CxK_of_centralizes hK'c hxY (fun w hw => by
    rw [← hvert] at hw
    exact hcent x hxY hpair.x_mem_CxK w hw)
  exact step_back_of_mem hlt hxC h1

theorem card_le_factorial_index {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (C : Subgroup S)
    (hC : C ≠ ⊤) : Nat.card S ≤ Nat.factorial C.index := by
  have hcore : C.normalCore = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal C.normalCore with h | h
    · exact h
    · exact absurd (top_le_iff.mp (h ▸ C.normalCore_le)) hC
  have := Subgroup.index_normalCore_le_factorial_index C
  rwa [hcore, Subgroup.index_bot] at this

theorem step_back_num (hr4 : pRank 2 G = 4) {x t : G} {K K' : Subgroup G}
    (hlt : PumpUpLT 2 x K t K') (hs : IsSimpleGroup (kBar K')) {j B : ℕ} (hj : j ≤ hatCard K)
    (hB : hatCard K' ≤ B) (hBj : B < 7 * j) (h720 : 720 < j)
    (h1 : pRank 2 ↥(CxK t K') ≤ 1) : x = t ∧ K' = K := by
  have hxY : x ∈ centralizer ({t} : Set G) := mem_centralizer_symm hlt.2.2.1
  obtain ⟨Λ, hΛ, hK'c, -, hKI, hIK', -⟩ := PumpRigid.step_core hlt hxY
  have hpair' : IsIL2Pair t K' := ⟨hlt.2.1.1, hK'c⟩
  have hq : CFSG.IsQuasisimple (kBar K') := isQuasisimple_hat hK'c
  have hcen : center (kBar K') = ⊥ := center_eq_bot_of_isSimple hs hq
  have hxN : x ∈ normalizer (K' : Set G) :=
    PumpGen.mem_normalizer_of_centerless hr4 hpair' hq hcen hxY
  have hpair : IsIL2Pair x K := ⟨hlt.1.1, hlt.1.2.2⟩
  have hΛM : bar t Λ ≤ bar t K' := bar_le_of_stable hlt hΛ hxN
  have hΛc := bar_lam_le_centralizer hxY hΛ
  obtain ⟨e⟩ := kBar_equiv_bar hK'c
  have := hs
  have hMs : IsSimpleGroup ↥(bar t K') := e.symm.isSimpleGroup
  have := hMs
  have hMcard : Nat.card ↥(bar t K') = hatCard K' := (Nat.card_congr e.toEquiv).symm
  have hcentM : ∀ w ∈ bar t K', sbar x hxY * w * (sbar x hxY)⁻¹ = w := by
    by_contra hcon
    push Not at hcon
    obtain ⟨w₀, hw₀, hne⟩ := hcon
    set s := sbar x hxY with hs'
    set Cb : Subgroup (barQ ↥(centralizer ({t} : Set G))) :=
      Subgroup.centralizer ({s} : Set _) ⊓ bar t K' with hCb
    set C' : Subgroup ↥(bar t K') := Cb.subgroupOf (bar t K') with hC'
    have hCbM : Cb ≤ bar t K' := inf_le_right
    have hproper : C' ≠ ⊤ := by
      intro htop
      have : (⟨w₀, hw₀⟩ : ↥(bar t K')) ∈ C' := by rw [htop]; trivial
      have h2 : w₀ ∈ Cb := Subgroup.mem_subgroupOf.mp this
      have h3 : w₀ ∈ Subgroup.centralizer ({s} : Set _) := h2.1
      rw [Subgroup.mem_centralizer_iff] at h3
      have h4 := h3 s (Set.mem_singleton s)
      apply hne
      calc s * w₀ * s⁻¹ = w₀ * s * s⁻¹ := by rw [h4]
        _ = w₀ := by group
    have hfact := card_le_factorial_index C' hproper
    rw [hMcard] at hfact
    have hΛCb : bar t Λ ≤ Cb := by
      intro w hw
      refine Subgroup.mem_inf.mpr ⟨?_, hΛM hw⟩
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff.mp hg]
      have := hΛc w hw
      calc s * w = s * w * s⁻¹ * s := by group
        _ = w * s := by rw [this]
    have hC'card : Nat.card ↥C' = Nat.card ↥Cb :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCbM).toEquiv
    have hΛCard : j ≤ Nat.card ↥Cb :=
      hj.trans (hKI.trans (Subgroup.card_le_of_le hΛCb))
    have hmul := Subgroup.card_mul_index C'
    rw [hMcard] at hmul
    have hidx : C'.index < 7 := by
      by_contra hge
      push Not at hge
      have h5 : 7 * j ≤ C'.index * Nat.card ↥C' := by
        calc 7 * j ≤ C'.index * j := Nat.mul_le_mul_right j hge
          _ ≤ C'.index * Nat.card ↥C' := Nat.mul_le_mul_left _ (hC'card ▸ hΛCard)
      have : C'.index * Nat.card ↥C' = hatCard K' := by rw [mul_comm]; exact hmul
      omega
    have hfac6 : Nat.factorial C'.index ≤ 720 := by
      have : Nat.factorial C'.index ≤ Nat.factorial 6 := Nat.factorial_le (by omega)
      simpa [Nat.factorial] using this
    have hKK' : hatCard K ≤ hatCard K' := PumpRigid.hat_le_of_pumpUpLT hlt
    omega
  have hxC : x ∈ CxK t K' := PumpRigid.mem_CxK_of_centralizes hK'c hxY hcentM
  exact step_back_of_mem hlt hxC h1

abbrev PStep (G : Type) [Group G] : G × Subgroup G → G × Subgroup G → Prop :=
  fun a b => PumpUpLT 2 a.1 a.2 b.1 b.2

theorem chain_back_rigid (hr4 : pRank 2 G = 4) {p q : G × Subgroup G}
    (h1 : pRank 2 ↥(CxK q.1 q.2) ≤ 1) (hchain : Relation.ReflTransGen (PStep G) p q) :
    hatCard q.2 ≤ hatCard p.2 →
      (∀ a, Relation.ReflTransGen (PStep G) p a → IsSimpleGroup (kBar a.2)) →
        pRank 2 ↥(CxK p.1 p.2) ≤ 1 := by
  induction hchain using Relation.ReflTransGen.head_induction_on with
  | refl => intro _ _; exact h1
  | @head a c hac hcq ih =>
    intro hsq hS
    have hac' : hatCard a.2 ≤ hatCard c.2 := PumpRigid.hat_le_of_pumpUpLT hac
    have hcq' : hatCard c.2 ≤ hatCard q.2 := PumpRigid.hat_le_of_chain hcq
    have ih' := ih (hsq.trans hac') (fun b hb => hS b (Relation.ReflTransGen.head hac hb))
    have hs : IsSimpleGroup (kBar c.2) := hS c (Relation.ReflTransGen.single hac)
    obtain ⟨hx, hK⟩ := step_back_rigid hr4 hac hs (hcq'.trans hsq) ih'
    rw [hx, ← hK]
    exact ih'

theorem chain_back_num (hr4 : pRank 2 G = 4) {p q : G × Subgroup G} {j B : ℕ}
    (h1 : pRank 2 ↥(CxK q.1 q.2) ≤ 1) (hBj : B < 7 * j) (h720 : 720 < j)
    (hchain : Relation.ReflTransGen (PStep G) p q) :
    hatCard q.2 ≤ B → j ≤ hatCard p.2 →
      (∀ a, Relation.ReflTransGen (PStep G) p a → IsSimpleGroup (kBar a.2)) →
        pRank 2 ↥(CxK p.1 p.2) ≤ 1 := by
  induction hchain using Relation.ReflTransGen.head_induction_on with
  | refl => intro _ _ _; exact h1
  | @head a c hac hcq ih =>
    intro hB hj hS
    have hac' : hatCard a.2 ≤ hatCard c.2 := PumpRigid.hat_le_of_pumpUpLT hac
    have hcq' : hatCard c.2 ≤ hatCard q.2 := PumpRigid.hat_le_of_chain hcq
    have ih' := ih hB (hj.trans hac') (fun b hb => hS b (Relation.ReflTransGen.head hac hb))
    have hs : IsSimpleGroup (kBar c.2) := hS c (Relation.ReflTransGen.single hac)
    obtain ⟨hx, hK⟩ := step_back_num hr4 hac hs hj (hcq'.trans hB) hBj h720 ih'
    rw [hx, ← hK]
    exact ih'

theorem exists_u2_of_terminal
    (h14 : B_prop14) (h103 : B_ivk_10_3) (hL34 : B_gen4_noL34_elem) (hL29 : B_inC2_L29)
    (hG : C3Hyp G) {t : G} {L : Subgroup G} (hILo : IsILo 2 t L) (hterm : IsTwoTerminal t L)
    (hU : InU2 (kBar L)) (hN : ¬ InC2 (kBar L)) : ∃ v : G, Is2TerminalU2Triple t v L := by
  have hpair : IsIL2Pair t L := ⟨hILo.1, hILo.2.2⟩
  have hr4 : pRank 2 G = 4 := hG.pRank_eq_four
  have hstar : IsStar2 t :=
    ⟨hILo.1, le_antisymm (Bg.pRank_subgroup_le one_lt_two _)
      (by rw [hr4]; exact h14 G hG t L hpair hU)⟩
  obtain ⟨y, hy⟩ := h103 G hG t L hpair hU hN
  refine ⟨y, hy, hterm, hstar, ?_, ?_⟩
  · intro hl34
    exfalso
    have hc := inU2_center hU
    exact hL34 G hG.gen4 t L hpair.1 hpair.2 ⟨hl34, hc.1, hc.2⟩
  · intro hl29
    exact absurd (hL29 _ hU hl29) hN

end CFSG.GH74.GLS.C3.Layer1.Thm1Pump
