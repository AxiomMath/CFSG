module

public import CFSG.LocalAnalysis.GLTheoremA.Lemma46
public import CFSG.LocalAnalysis.GLTheoremA.Sec5BTools

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped commutatorElement

@[expose] def Prop51CoreAt (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ (B J D Q : Subgroup G) (a : G), IsS0Max p B a J → D ≤ B → ¬ IsCyclic D → a ∈ D →
    (∀ d ∈ D, CentMod p J d) →
    (∀ K : Subgroup G, GLAPComponent p (Subgroup.centralizer ({a} : Set G)) K →
      Nonempty (PQuot p K ≃* PQuot p J) → D ≤ Subgroup.normalizer (K : Set G)) →
    IsPGroup 2 Q → B ≤ Subgroup.normalizer (Q : Set G) → Q ≤ Subgroup.centralizer ({a} : Set G) →
    (⁅D, Q⁆ : Subgroup G) ≠ ⊥ → False

variable {G : Type} [Group G] [Finite G]

theorem mem_centModSubgroup_of_mk_mem_center {p : ℕ} {L : Subgroup G} {z : G} (hzL : z ∈ L)
    (hz : (QuotientGroup.mk (⟨z, hzL⟩ : L) : PQuot p L) ∈ Subgroup.center (PQuot p L)) :
    z ∈ centModSubgroup p L := by
  refine ⟨Subgroup.le_normalizer hzL, fun l hl => ?_⟩
  have h1 : (QuotientGroup.mk (⁅(⟨l, hl⟩ : L), ⟨z, hzL⟩⁆ : L) : PQuot p L) = 1 := by
    rw [← QuotientGroup.mk'_apply, map_commutatorElement]
    simp only [QuotientGroup.mk'_apply]
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_center_iff.1 hz _
  rw [QuotientGroup.eq_one_iff] at h1
  exact ⟨_, h1, rfl⟩

theorem not_centModEqZpowers_of_not_isCyclic {p : ℕ} {B L : Subgroup G} {x : G}
    (h : ¬ IsCyclic (B ⊓ centModSubgroup p L : Subgroup G)) : ¬ CentModEqZpowers p B L x := by
  intro hE
  apply h
  have hle : (B ⊓ centModSubgroup p L : Subgroup G) ≤ Subgroup.zpowers x := fun b hb =>
    (hE b hb.1).1 (centMod_iff.2 hb.2)
  exact Subgroup.isCyclic_of_le hle

theorem isPGroup_pCoreOf (r : ℕ) (N : Subgroup G) : IsPGroup r (pCoreOf r N) := by
  unfold pCoreOf
  exact CFSG.pCore_isPGroup.map _

theorem centralizer_zpowers_eq (a : G) :
    Subgroup.centralizer (Subgroup.zpowers a : Set G) = Subgroup.centralizer ({a} : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem prop51 {p : ℕ} (hc : Sec5Ctx G p) {Exc Club : Subgroup G → Prop}
    (hEC : ExcClubHyp G p Exc Club) (h113 : I113UsedAt G p) (hcore : Prop51CoreAt G p) :
    Prop51At G p := by
  classical
  have hp := hc.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have h183 := hc.input18_3_4
  have hS4 := hc.stage4Order
  by_contra hfail
  set F : Set (Triple G) := {t | IsS0Max p t.1 t.2.1 t.2.2 ∧ ¬ CentModEqZpowers p t.1 t.2.2 t.2.1}
  have hFne : F.Nonempty := by
    unfold Prop51At at hfail
    push Not at hfail
    obtain ⟨B, x, L, h1, h2⟩ := hfail
    exact ⟨(B, x, L), h1, h2⟩
  obtain ⟨⟨B, x, L⟩, ⟨hBxL, hfailBxL⟩, hmax⟩ :=
    Set.exists_max_image F (fun t => mxB p Club t.1 t.2.1) (Set.toFinite F) hFne
  have key : ∀ (B' : Subgroup G) (x' : G) (L' : Subgroup G), IsS0Max p B' x' L' →
      ¬ IsCyclic (B' ⊓ centModSubgroup p L' : Subgroup G) → mxB p Club B' x' ≤ mxB p Club B x :=
    fun B' x' L' h1 h2 => hmax (B', x', L') ⟨h1, not_centModEqZpowers_of_not_isCyclic h2⟩
  set Cx := Subgroup.centralizer ({x} : Set G)
  have hS : IsSTriple p B x L := hBxL.1.1
  have hB : GLAIsBmax p B := hS.1
  have hx : IsEssential p B x := hS.2.1
  have hLc : GLAPComponent p Cx L := hS.2.2
  have hBL : B ≤ Subgroup.normalizer (L : Set G) := hBxL.2.2
  have hinv : ∀ K : Subgroup G, GLAPComponent p Cx K → Nonempty (PQuot p K ≃* PQuot p L) →
      B ≤ Subgroup.normalizer (K : Set G) := by
    intro K hK ⟨eKL⟩
    by_contra hBK
    have hExcL : Exc L := (hEC.exc_congr K L ⟨eKL⟩).1 (hEC.exc_of_not_le B x K hB hx hK hBK)
    have hLg : IsGoodComp p Club B x L := ⟨hLc, hBL, hEC.not_club_of_exc L hExcL⟩
    obtain ⟨B', x', L', hrel, -, hlt, hnc⟩ :=
      lemma46 hp hEC h183 hc.kProper hc.simple hc.nonabelian hc.stage3 hS4 h113 hBxL.2.1
        (le_MxB hLg) hK hBK
    have := key B' x' L'
      ((hS4.2.2.2.2.2.2.1 _ _ (pumpLe_of_reflTransGen hBxL.1.1 hrel)).2 hBxL) hnc
    exact absurd hlt (not_lt.2 this)
  have hxC : x ∈ Subgroup.centralizer (L : Set G) := IsSTriple.mem_centralizer hS
  have hxE : CentMod p L x := centMod_of_mem_centralizer hxC
  obtain ⟨b, hbB, hbL, hbx⟩ : ∃ b ∈ B, CentMod p L b ∧ b ∉ Subgroup.zpowers x := by
    by_contra h
    push Not at h
    exact hfailBxL fun b hb =>
      ⟨h b hb, fun hbx => centMod_of_mem_centralizer ((Subgroup.zpowers_le.2 hxC) hbx)⟩
  obtain ⟨c, hcB, hcL, hcx, hzD⟩ : ∃ c ∈ B, CentMod p L c ∧ c ∉ Subgroup.zpowers x ∧
      ∀ _ : Exc L, ∃ z ∈ B, ∃ hzL : z ∈ L, orderOf z = p ∧
        (QuotientGroup.mk (⟨z, hzL⟩ : L) : PQuot p L) ∈ Subgroup.center (PQuot p L) ∧
        z ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers c := by
    by_cases hExc : Exc L
    · obtain ⟨z, hzB, hzL, hzo, hzc⟩ :=
        lemma48 hp hc.odd hB hx hLc (hEC.card_center_of_exc L hExc) hinv
      by_cases hzx : z ∈ Subgroup.zpowers x
      · exact ⟨b, hbB, hbL, hbx, fun _ => ⟨z, hzB, hzL, hzo, hzc, Subgroup.mem_sup_left hzx⟩⟩
      · exact ⟨z, hzB, centMod_iff.2 (mem_centModSubgroup_of_mk_mem_center hzL hzc), hzx,
          fun _ => ⟨z, hzB, hzL, hzo, hzc, Subgroup.mem_sup_right (Subgroup.mem_zpowers z)⟩⟩
    · exact ⟨b, hbB, hbL, hbx, fun h => absurd h hExc⟩
  set D := Subgroup.zpowers x ⊔ Subgroup.zpowers c with hDdef
  have hDB : D ≤ B := sup_le (Subgroup.zpowers_le.2 hx.1) (Subgroup.zpowers_le.2 hcB)
  have hxp : x ^ p = 1 := hB.1.2 x hx.1
  have hx1 : x ≠ 1 := hx.2.1
  have hDcard : Nat.card D = p ^ 2 := by
    rw [hDdef, sup_comm]
    exact (Prop53.isElemAbelian_card_sup_zpowers hp (isElemAbelian_commute hB.1 hcB hx.1)
      (hB.1.2 c hcB) hxp hx1 hcx).2
  have hDnc : ¬ IsCyclic D := fun hcyc => hcx (mem_zpowers_of_card_sup_le hp hxp hx1
    (card_le_of_isCyclic_of_pow hp hcyc fun d hd => hB.1.2 d (hDB hd)))
  have hDE : ∀ d ∈ D, CentMod p L d := by
    have hle : D ≤ centModSubgroup p L := sup_le (Subgroup.zpowers_le.2 (centMod_iff.1 hxE))
      (Subgroup.zpowers_le.2 (centMod_iff.1 hcL))
    exact fun d hd => centMod_iff.2 (hle hd)
  obtain ⟨N₁, hN₁, hBN₁⟩ := GLAIsBmax.exists_maxTwoLocal hB
  obtain ⟨D₀, hD₀D, hD₀card, hD₀e, hR⟩ := hc.stage3.2.2.1 B D N₁ hB hDB hDnc hN₁ hBN₁
  have hD₀p : Nat.card D₀ = p := by
    have h : Nat.card D₀ * p = p * p := by rw [hD₀card, hDcard, sq]
    exact Nat.eq_of_mul_eq_mul_right hp.pos h
  obtain ⟨a, haD₀, ha1⟩ : ∃ a ∈ D₀, a ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : D₀ = ⊥ := (Subgroup.eq_bot_iff_forall D₀).2 h
    rw [hbot, Subgroup.card_bot] at hD₀p
    exact hp.one_lt.ne hD₀p
  have haD : a ∈ D := hD₀D haD₀
  have haB : a ∈ B := hDB haD
  have hap' : a ^ p = 1 := hB.1.2 a haB
  have haE : IsEssential p B a := hD₀e a haD₀ ha1
  have hD₀a : D₀ = Subgroup.zpowers a :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 haD₀)
      (by rw [hD₀p, card_zpowers_eq_of_pow hp hap' ha1])).symm
  rw [hD₀a, centralizer_zpowers_eq] at hR
  have haL : CentMod p L a := hDE a haD
  have hap : IsPGroup p (Subgroup.zpowers a) := isPGroup_zpowers_of_mem hB.1 haB
  set Ca := Subgroup.centralizer ({a} : Set G)
  have hBdec : ∀ b ∈ B, ∃ u ∈ B ⊓ B, ∃ v ∈ B, CentMod p L v ∧ b = u * v :=
    fun b hb => ⟨b, ⟨hb, hb⟩, 1, B.one_mem, centMod_one p L, (mul_one b).symm⟩
  obtain ⟨J, -, hJc, hrel, -, hBJ, ⟨eLJ⟩, hIJ, -, -, hcmJ⟩ :=
    pump_step h183 hp hS4 hc.kProper hc.simple hc.nonabelian hBxL.2.1 hBL hB hx.1 hBdec haE haL
  have hBaJ : IsS0Max p B a J :=
    (hS4.2.2.2.2.2.2.1 _ _
      (pumpLe_of_reflTransGen hBxL.1.1 (Relation.ReflTransGen.single hrel))).2 hBxL
  have hDJ : ∀ d ∈ D, CentMod p J d := fun d hd => hcmJ d (hDB hd) (hDE d hd)
  have hDinv : ∀ K : Subgroup G, GLAPComponent p Ca K → Nonempty (PQuot p K ≃* PQuot p J) →
      D ≤ Subgroup.normalizer (K : Set G) := by
    intro K hK ⟨eKJ⟩
    by_contra hDK
    have hBK : ¬ B ≤ Subgroup.normalizer (K : Set G) := fun h => hDK (hDB.trans h)
    have hExcJ : Exc J := (hEC.exc_congr K J ⟨eKJ⟩).1 (hEC.exc_of_not_le B a K hB haE hK hBK)
    have hExcL : Exc L := (hEC.exc_congr L J ⟨eLJ⟩).2 hExcJ
    obtain ⟨z, hzB, hzL, hzo, hzc, hzD'⟩ := hzD hExcL
    have hz1 : z ≠ 1 := fun h => hp.one_lt.ne (by rw [← hzo, h, orderOf_one])
    have hzCa : z ∈ Ca :=
      Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hB.1 hzB haB)
    obtain ⟨-, -, -, hIall, -, -⟩ := glaPLayer_inf_centralizer hp hLc hap haL
    have hzJ : z ∈ J := hIJ (hIall z ⟨hzL, hzCa⟩ (isPGroup_zpowers_of_mem hB.1 hzB))
    have hzN : z ∈ Subgroup.normalizer (K : Set G) := by
      by_cases hKJ : K = J
      · rw [hKJ]
        exact Subgroup.le_normalizer hzJ
      · exact CFSG.HardMathSupport.Solomon.LocalBalance.mem_normalizer_of_ne hp hK hJc hKJ hzJ
    have haN : a ∈ Subgroup.normalizer (K : Set G) := by
      refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun k hk => ?_)
      exact Subgroup.mem_centralizer_singleton_iff.1 (hK.1 hk)
    have hza : z ∈ Subgroup.zpowers a := by
      by_contra hza
      apply hDK
      have hzaD : Subgroup.zpowers z ⊔ Subgroup.zpowers a = D := by
        refine Subgroup.eq_of_le_of_card_ge
          (sup_le (Subgroup.zpowers_le.2 hzD') (Subgroup.zpowers_le.2 haD)) ?_
        rw [hDcard, (Prop53.isElemAbelian_card_sup_zpowers hp
          (isElemAbelian_commute hB.1 hzB haB) (hB.1.2 z hzB) hap' ha1 hza).2]
      rw [← hzaD]
      exact sup_le (Subgroup.zpowers_le.2 hzN) (Subgroup.zpowers_le.2 haN)
    have haz : a ∈ Subgroup.zpowers z := by
      have he : Subgroup.zpowers z = Subgroup.zpowers a :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hza)
          (by rw [card_zpowers_eq_of_pow hp hap' ha1, card_zpowers_eq_of_pow hp
            (hB.1.2 z hzB) hz1])
      rw [he]
      exact Subgroup.mem_zpowers a
    have hzcm : z ∈ centModSubgroup p L := mem_centModSubgroup_of_mk_mem_center hzL hzc
    have haM : ∀ K', IsGoodComp p Club B x K' → CentMod p K' a := by
      intro K' hK'
      have hzK' : z ∈ centModSubgroup p K' := by
        by_cases hK'L : K' = L
        · rw [hK'L]
          exact hzcm
        · exact le_centModSubgroup_of_ne hp hLc hK'.1 (Ne.symm hK'L) hzL
      exact centMod_iff.2 ((Subgroup.zpowers_le.2 hzK') haz)
    have h45 : mxB p Club B x ≤ mxB p Club B a :=
      lemma45 hp hEC h183 hc.kProper hc.simple hc.nonabelian hB hx.1
        (fun b hb => ⟨b, ⟨hb, hb⟩, 1, B.one_mem, fun K' _ => centMod_one p K', (mul_one b).symm⟩)
        haE haM
    have hJg : IsGoodComp p Club B a J := ⟨hJc, hBJ, hEC.not_club_of_exc J hExcJ⟩
    obtain ⟨B', x', L', hrel', -, hlt, hnc⟩ :=
      lemma46 hp hEC h183 hc.kProper hc.simple hc.nonabelian hc.stage3 hS4 h113 hBaJ.2.1
        (le_MxB hJg) hK hBK
    have := key B' x' L'
      ((hS4.2.2.2.2.2.2.1 _ _ (pumpLe_of_reflTransGen hBaJ.1.1 hrel')).2 hBaJ) hnc
    omega
  have hBQ : B ≤ Subgroup.normalizer ((pCoreOf 2 N₁ ⊓ Ca : Subgroup G) : Set G) := by
    intro g hg
    have h1 : GLBConj g (pCoreOf 2 N₁) = pCoreOf 2 N₁ :=
      mem_normalizer_iff_gLBConj_eq.1 (le_normalizer_pCoreOf 2 N₁ (hBN₁ hg))
    have h2 : GLBConj g Ca = Ca := mem_normalizer_iff_gLBConj_eq.1
      (Subgroup.le_normalizer (isElemAbelian_le_centralizer hB.1 haB hg))
    rw [mem_normalizer_iff_gLBConj_eq, gLBConj_inf, h1, h2]
  exact hcore B J D (pCoreOf 2 N₁ ⊓ Ca) a hBaJ hDB hDnc haD hDJ hDinv
    ((isPGroup_pCoreOf 2 N₁).to_le inf_le_left) hBQ inf_le_right hR

end CFSG.LocalAnalysis.GLTheoremA
