module

public import CFSG.Goldschmidt.Steps.G63Basic
import CFSG.Goldschmidt.Steps.G53Tools
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalizerEqOfNontrivialNormalInCoatom
import CFSG.Walter.Bender1970.S3.CoreExchange

public section

namespace CFSG.Goldschmidt.G63

open CFSG.GorensteinWalter hiding oddCoreOf
open CFSG.Walter
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A : Subgroup G}

theorem key (h37 : S_G37) (h312 : S_G312) (h51 : S_G51) (h62 : S_G62)
    (hG : GoldSetting G S A) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) {H : Subgroup G}
    (hH : H ∈ benderM a) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hU : UniquenessA a H)
    (hPnc : ¬ IsCyclic (qCoreOf H p)) {a₁ : G} (ha₁ : a₁ ∈ A) (ha₁1 : a₁ ≠ 1)
    {H₁ : Subgroup G} (hH₁ : H₁ ∈ benderM a₁) (hne : H₁ ≠ H)
    (hQ1 : qCoreOf (fstarZero H) p ⊓ H₁ ≠ ⊥)
    (hnot : ¬ ((qCoreOf (fstarZero H) p ⊓ H₁ ⊓ qCoreOf H₁ p = ⊥ ∧
      ⁅qCoreOf (fstarZero H) p ⊓ H₁, Subgroup.zpowers a⁆ = ⊥) ∧
      IsCyclic (qCoreOf (fstarZero H) p ⊓ H₁ : Subgroup G))) :
    pResidualOf (generalizedFittingSubgroupOf H₁) p ≤ H ∧ qCoreOf H p ≤ H₁ ∧
      3 ≤ CFSG.Open.pRank p (qCoreOf H₁ p) := by
  have hsimple := hG.isSimpleGroup
  have : Fact p.Prime := ⟨hp⟩
  set P := qCoreOf H p with hPdef
  set P₁ := qCoreOf H₁ p with hP₁def
  set B := qCoreOf (fstarZero H) p with hBdef
  set Q := B ⊓ H₁ with hQdef
  set R₁ := pResidualOf (generalizedFittingSubgroupOf H₁) p with hR₁def
  have hHco := isCoatom_of_mem_benderM hH
  have hH₁co := isCoatom_of_mem_benderM hH₁
  have hCH := centralizer_le_of_mem_benderM hH
  have haH : a ∈ H := mem_of_mem_benderM hH
  have haH₁ : a ∈ H₁ := le_of_mem_benderM hG ha₁ hH₁ ha
  have ha₁H : a₁ ∈ H := le_of_mem_benderM hG ha hH ha₁
  have ha₁H₁ : a₁ ∈ H₁ := mem_of_mem_benderM hH₁
  obtain ⟨A₁', hS₁, hA₁'el, hAA₁'⟩ := exists_sstar hG hH₁co.1
  have haA₁' : a ∈ A₁' := hAA₁' ⟨ha, haH₁⟩
  have hPp : IsPGroup p P := qCoreOf_isPGroup H p
  have hP₁p : IsPGroup p P₁ := qCoreOf_isPGroup H₁ p
  have hBp : IsPGroup p B := qCoreOf_isPGroup _ p
  have hBn : IsNormalIn B H := qCoreOf_fstarZero_isNormalIn H p
  have hQp : IsPGroup p Q := hBp.to_le inf_le_left
  have hHB : H ≤ Subgroup.normalizer (B : Set G) := le_normalizer_of_isNormalIn hBn
  have hHP : H ≤ Subgroup.normalizer (P : Set G) :=
    le_normalizer_of_isNormalIn (qCoreOf_normal_in H p)
  have hH₁P₁ : H₁ ≤ Subgroup.normalizer (P₁ : Set G) :=
    le_normalizer_of_isNormalIn (qCoreOf_normal_in H₁ p)
  have hR₁n : IsNormalIn R₁ H₁ := pResidualOf_generalizedFitting_isNormalIn H₁ p
  have hH₁R₁ : H₁ ≤ Subgroup.normalizer (R₁ : Set G) := le_normalizer_of_isNormalIn hR₁n
  have hR₁P₁ : R₁ ≤ Subgroup.centralizer (P₁ : Set G) :=
    pResidualOf_generalizedFitting_le_centralizer H₁ hp
  have hP₁R₁ : P₁ ≤ Subgroup.centralizer (R₁ : Set G) := Subgroup.le_centralizer_iff.mp hR₁P₁
  have hP1 : P ≠ ⊥ := fun h => hPnc (h ▸ inferInstance)
  have hFH := not_isPGroup_fstar h62 hG ha ha1 hH hp hp2 hP1
  have hNle : ∀ Y : Subgroup G, Y ≤ B → Y ≠ ⊥ → a ∈ Subgroup.normalizer (Y : Set G) →
      Subgroup.normalizer (Y : Set G) ≤ H := fun Y hY hY1 haY =>
    normalizer_le_of_uniqueness hsimple hHco hU hFH hp hY hY1 haY
  have hQN : H₁ ⊓ Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (Q : Set G) :=
    fun x hx => mem_normalizer_inf (hHB (hCH hx.2)) (Subgroup.le_normalizer hx.1)
  have haQ : a ∈ Subgroup.normalizer (Q : Set G) :=
    hQN ⟨haH₁, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have ha₁Q : a₁ ∈ Subgroup.normalizer (Q : Set G) :=
    mem_normalizer_inf (hHB ha₁H) (Subgroup.le_normalizer ha₁H₁)
  have hQa : ⁅Q, Subgroup.zpowers a⁆ ≤ P₁ :=
    G53.commutator_le_qCoreOf_of_isPGroup h37 hS₁ hA₁'el haA₁' ha1 inf_le_right hQN hp hp2 hQp
  have hQK : Q ≤ normalClosureIn H₁ A₁' ⊔ oddCoreOf H₁ :=
    le_normalClosureIn_sup_of_isPGroup h37 hS₁ hA₁'el haA₁' ha1 hp hp2 hQp inf_le_right hQN
  have hQaQ : ⁅Q, Subgroup.zpowers a⁆ ≤ Q := commutator_zpowers_le_of_mem_normalizer haQ
  have hR₁1 : R₁ ≠ ⊥ := fun h =>
    h62 G S A hG a₁ ha₁ ha₁1 H₁ hH₁ p hp hp2 (isPGroup_of_pResidualOf_eq_bot _ p hp h)
  have hNR₁ : Subgroup.normalizer (R₁ : Set G) = H₁ :=
    normalizer_eq_of_nontrivial_normal_in_coatom hsimple hH₁co hR₁n.1 hR₁1
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hR₁n.1).mpr hH₁R₁)
  have hR₁H : R₁ ≤ H := by
    by_cases hQ₀ : Q ⊓ P₁ = ⊥
    · have hQa1 : ⁅Q, Subgroup.zpowers a⁆ = ⊥ := le_bot_iff.mp (hQ₀ ▸ le_inf hQaQ hQa)
      have hQnc : ¬ IsCyclic Q := fun hc => hnot ⟨⟨hQ₀, hQa1⟩, hc⟩
      have hCx : ∀ x ∈ Q, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ≤ H := by
        intro x hx hx1
        have hxB : Subgroup.zpowers x ≤ B := Subgroup.zpowers_le.mpr hx.1
        have hx1' : Subgroup.zpowers x ≠ ⊥ := fun h =>
          hx1 (Subgroup.mem_bot.mp (h ▸ Subgroup.mem_zpowers x))
        have hxa : x * a = a * x := by
          rw [Subgroup.commutator_comm, commutator_zpowers_eq_bot_iff] at hQa1
          exact hQa1 x hx
        have haC : a ∈ Subgroup.centralizer
            ((Subgroup.zpowers x : Subgroup G) : Set G) := by
          rw [centralizer_zpowers_eq', Subgroup.mem_centralizer_singleton_iff]
          exact hxa.symm
        have hCC : Subgroup.centralizer ({x} : Set G) ≤
            Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
          rw [← centralizer_zpowers_eq']
          exact Subgroup.centralizer_le_normalizer _
        exact hCC.trans (hNle _ hxB hx1' (Subgroup.centralizer_le_normalizer _ haC))
      obtain ⟨E, hEQ, hE, hEcard⟩ := exists_isElemAbelian_card_sq hp hp2 hQp hQnc
      have hcompl : qCoreCompl H₁ p ≤ H := by
        refine sSup_le ?_
        rintro _ ⟨q, hq, hqp, rfl⟩
        have hEN : E ≤ Subgroup.normalizer (qCoreOf H₁ q : Set G) :=
          (hEQ.trans inf_le_right).trans (le_normalizer_of_isNormalIn (qCoreOf_normal_in H₁ q))
        refine (le_iSup_inf_centralizer hp hE.1 hE.2 hEcard.ge hEN
          (not_dvd_card_qCoreOf hp hq hqp)).trans ?_
        exact iSup₂_le fun e he => iSup_le fun he1 => inf_le_right.trans (hCx e (hEQ he) he1)
      have hE₁ : componentLayerOf H₁ ≤ H := by
        refine sSup_le fun L hL => ?_
        obtain ⟨v, hvQ, hv1, hLv⟩ := G53.exists_ne_one_le_centralizer_of_isComponentOf h37 hS₁
          hA₁'el haA₁' ha1 inf_le_right hQN (G53.eq_layer_sup_oddFitting_of_isPGroup hp hp2 hQp)
          (G53.oddFitting_eq_of_isPGroup hp hp2 hQp).ge hQnc hL
        exact hLv.trans (hCx v hvQ hv1)
      exact (pResidualOf_generalizedFitting_le H₁ hp).trans (sup_le hcompl hE₁)
    · exact (hR₁P₁.trans (Subgroup.centralizer_le inf_le_right)).trans
        ((Subgroup.centralizer_le_normalizer _).trans (hNle (Q ⊓ P₁)
          (inf_le_left.trans inf_le_left) hQ₀ (mem_normalizer_inf haQ (hH₁P₁ haH₁))))
  have hR₁Q : ⁅R₁, Q⁆ = ⊥ :=
    commutator_pResidual_eq_bot H₁ hp hBp inf_le_left (hR₁H.trans hHB)
      (inf_le_right.trans hH₁R₁)
  have hQR₁ : Q ≤ Subgroup.centralizer (R₁ : Set G) :=
    Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hR₁Q)
  obtain ⟨V, hV1, hVP₁, hVH, hNV⟩ : ∃ V : Subgroup G, V ≠ ⊥ ∧ V ≤ P₁ ∧ V ≤ H ∧
      Subgroup.normalizer (V : Set G) ≤ H₁ := by
    by_cases hQ₀ : Q ⊓ P₁ = ⊥
    ·
      have hm : 3 ≤ CFSG.Open.pRank p P₁ := by
        by_contra hm
        push Not at hm
        obtain ⟨-, hSyl⟩ := h312 G H₁ A₁' hS₁ p hp hp2
          (Nat.lt_succ_iff.mp hm : CFSG.Open.pRank p P₁ ≤ 2)
        have hQP₁ : Q ≤ P₁ :=
          le_of_fusionIsSylowIn hSyl (le_inf hQK hQR₁) hQp (inf_le_right.trans hH₁P₁)
        exact hQ1 (le_bot_iff.mp (hQ₀ ▸ le_inf le_rfl hQP₁))
      have hP₁1 : P₁ ≠ ⊥ := by
        intro h
        have : rank P₁ ≤ 1 :=
          rank_le_one_of_card_le hp hP₁p (by rw [h, Subgroup.card_bot]; exact hp.one_lt.le)
        rw [rank_eq_pRank_of_isPGroup hp hP₁p] at this
        omega
      have hQP₁N : Q ⊔ P₁ ≤ Subgroup.normalizer (P₁ : Set G) :=
        sup_le (inf_le_right.trans hH₁P₁) Subgroup.le_normalizer
      have hQP₁p : IsPGroup p (Q ⊔ P₁ : Subgroup G) :=
        hQp.to_sup_of_normal_right' hP₁p (inf_le_right.trans hH₁P₁)
      set V := P₁ ⊓ Subgroup.centralizer ((Q ⊔ P₁ : Subgroup G) : Set G) with hVdef
      have hV1 : V ≠ ⊥ := inf_centralizer_ne_bot_of_isPGroup hp hQP₁p hP₁p hQP₁N hP₁1
      have hVC : V ≤ Subgroup.centralizer (Q : Set G) :=
        inf_le_right.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left))
      have hVH : V ≤ H := hVC.trans ((Subgroup.centralizer_le_normalizer _).trans
        (hNle Q inf_le_left hQ1 haQ))
      have hVB₁ : V ≤ qCoreOf (fstarZero H₁) p := by
        refine le_qCoreOf_fstarZero H₁ hp inf_le_left ?_
        have hP₁V : P₁ ≤ Subgroup.centralizer (V : Set G) :=
          Subgroup.le_centralizer_iff.mp (inf_le_right.trans
            (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_right)))
        exact (Bender35.commutator_self_le P₁).trans hP₁V
      have ha₁V : a₁ ∈ Subgroup.normalizer (V : Set G) :=
        mem_normalizer_inf (hH₁P₁ ha₁H₁)
          (Bender35.mem_normalizer_centralizer (mem_normalizer_sup ha₁Q (hH₁P₁ ha₁H₁)))
      have hU₁ := uniquenessA_of h51 hG ha₁ ha₁1 hH₁ hp hp2 (Or.inr hm)
      have hFH₁ := not_isPGroup_fstar h62 hG ha₁ ha₁1 hH₁ hp hp2 hP₁1
      exact ⟨V, hV1, inf_le_left, hVH,
        normalizer_le_of_uniqueness hsimple hH₁co hU₁ hFH₁ hp hVB₁ hV1 ha₁V⟩
    · have hP₁1 : P₁ ≠ ⊥ := fun h => hQ₀ (le_bot_iff.mp (h ▸ inf_le_right))
      set V := P₁ ⊓ Subgroup.centralizer (P₁ : Set G) with hVdef
      have hV1 : V ≠ ⊥ :=
        inf_centralizer_ne_bot_of_isPGroup hp hP₁p hP₁p Subgroup.le_normalizer hP₁1
      have hVH : V ≤ H := (inf_le_right.trans (Subgroup.centralizer_le inf_le_right)).trans
        ((Subgroup.centralizer_le_normalizer _).trans (hNle (Q ⊓ P₁)
          (inf_le_left.trans inf_le_left) hQ₀ (mem_normalizer_inf haQ (hH₁P₁ haH₁))))
      have hVn : IsNormalIn V H₁ := isNormalIn_of_le_normalizer
        (inf_le_left.trans (qCoreOf_normal_in H₁ p).1) fun h hh =>
          mem_normalizer_inf (hH₁P₁ hh) (Bender35.mem_normalizer_centralizer (hH₁P₁ hh))
      exact ⟨V, hV1, inf_le_left, hVH,
        (normalizer_eq_of_nontrivial_normal_in_coatom hsimple hH₁co hVn.1 hV1
          ((Subgroup.normal_subgroupOf_iff_le_normalizer hVn.1).mpr
            (le_normalizer_of_isNormalIn hVn))).le⟩
  have hVp : IsPGroup p V := hP₁p.to_le hVP₁
  have hVR₁ : ⁅V, R₁⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hVP₁.trans hP₁R₁)
  have hCPV : ⁅P ⊓ Subgroup.centralizer (V : Set G), R₁⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact commutator_pResidual_eq_bot H₁ hp hPp inf_le_left (hR₁H.trans hHP)
      ((inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans hNV)).trans hH₁R₁)
  have hT : Centralizes R₁ P :=
    bender1970_1_1_thompson p hp V R₁ P hVp hPp (pResidualOf_pResidualOf _ p hp)
      (hVH.trans hHP) (hR₁H.trans hHP) hVR₁ hCPV
  have hPR₁ : P ≤ Subgroup.centralizer (R₁ : Set G) := Subgroup.le_centralizer_iff.mp hT
  have hPH₁ : P ≤ H₁ := hPR₁.trans ((Subgroup.centralizer_le_normalizer _).trans hNR₁.le)
  refine ⟨hR₁H, hPH₁, ?_⟩
  by_contra hm
  push Not at hm
  obtain ⟨-, hSyl⟩ := h312 G H₁ A₁' hS₁ p hp hp2
    (Nat.lt_succ_iff.mp hm : CFSG.Open.pRank p P₁ ≤ 2)
  have hPK : P ≤ normalClosureIn H₁ A₁' ⊔ oddCoreOf H₁ :=
    le_normalClosureIn_sup_of_isPGroup h37 hS₁ hA₁'el haA₁' ha1 hp hp2 hPp hPH₁
      fun x hx => hHP (hCH hx.2)
  have hPP₁ : P ≤ P₁ := le_of_fusionIsSylowIn hSyl (le_inf hPK hPR₁) hPp (hPH₁.trans hH₁P₁)
  have hrank : rank P₁ ≤ rank P := by
    have := two_le_rank_of_not_isCyclic hp hp2 hPp hPnc
    rw [rank_eq_pRank_of_isPGroup hp hP₁p]
    omega
  set W := omegaOneCenter P₁ p with hWdef
  have hWP : W ≤ P := omegaOneCenter_le_of_rank_le hp hP₁p hPP₁ hrank
  have hW1 : W ≠ ⊥ :=
    omegaOneCenter_ne_bot hp hP₁p (fun h => hP1 (le_bot_iff.mp (h ▸ hPP₁)))
  have hWZ : W ≤ P ⊓ Subgroup.centralizer (P : Set G) :=
    le_inf hWP ((omegaOneCenter_le_centralizer P₁ p).trans (Subgroup.centralizer_le hPP₁))
  have hWB : W ≤ B := hWZ.trans (center_qCoreOf_le_qCoreOf_fstarZero H hp)
  have hH₁W : H₁ ≤ Subgroup.normalizer (W : Set G) :=
    le_normalizer_omegaOneCenter (qCoreOf_normal_in H₁ p) p
  exact hne (eq_of_isCoatom_of_le hHco hH₁co ((hH₁W.trans (hNle W hWB hW1 (hH₁W haH₁)))))

end CFSG.Goldschmidt.G63
