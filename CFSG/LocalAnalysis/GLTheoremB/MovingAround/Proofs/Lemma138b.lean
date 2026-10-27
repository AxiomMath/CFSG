module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma138
public import CFSG.LocalAnalysis.GL83PartI.I_22_6

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped MatrixGroups

namespace Lemma138b

section QLevel

variable {Q : Type} [Group Q] [Finite Q] {p : ℕ}

theorem glaPLayer_top_normal (p : ℕ) : (GLAPLayer p (⊤ : Subgroup Q)).Normal := by
  have hle : ∀ g : Q, GLBConj g (GLAPLayer p (⊤ : Subgroup Q)) ≤ GLAPLayer p (⊤ : Subgroup Q) := by
    intro g
    unfold GLBConj
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun L hL => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    have h1 := glaPComponent_gLBConj hL g
    have e : GLBConj g (⊤ : Subgroup Q) = ⊤ :=
      top_unique fun y _ => mem_gLBConj.2 (Subgroup.mem_top _)
    rw [e] at h1
    exact le_sSup h1
  refine ⟨fun n hn g => ?_⟩
  have h1 : g * n * g⁻¹ ∈ GLBConj g⁻¹ (GLAPLayer p (⊤ : Subgroup Q)) := by
    rw [mem_gLBConj]
    simpa [mul_assoc] using hn
  exact hle g⁻¹ h1

theorem glaPLayer_layer (hp : p.Prime) :
    GLAPLayer p (GLAPLayer p (⊤ : Subgroup Q)) = GLAPLayer p (⊤ : Subgroup Q) := by
  refine le_antisymm (Lemma138.glaPLayer_le_self p _) ?_
  refine sSup_le fun J hJ => ?_
  have hJY : J ≤ GLAPLayer p (⊤ : Subgroup Q) := le_sSup hJ
  exact le_sSup (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.glaPComponent_down hp hJ
    hJY le_top)

theorem gLALayer_layer (hp : p.Prime) (hcore : GLAPPrimeCore p Q = ⊥) :
    GLALayer (GLAPLayer p (⊤ : Subgroup Q)) = GLAPLayer p (⊤ : Subgroup Q) := by
  refine le_antisymm (sSup_le fun _ hK => hK.1) ?_
  refine sSup_le fun J hJ => ?_
  have hJY : J ≤ GLAPLayer p (⊤ : Subgroup Q) := le_sSup hJ
  have hJc : IsComponentOf J ⊤ :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.i116n_isComponentOf_of_glaPComponent hcore hJ
  exact le_sSup (show IsComponentOf J (GLAPLayer p (⊤ : Subgroup Q)) from
    ⟨hJY, isSubnormal_of_le_of_le hJc.2.1 hJY le_top, hJc.2.2⟩)

theorem exists_W (hp : p.Prime) (hI181 : Lemma138.InputI181) (hQK : IsKGroup Q)
    {K M' Ft : Subgroup Q} (hFp : IsPGroup p ↥Ft) (hKM : IsSubnormal K M')
    (hCF : Subgroup.centralizer (Ft : Set Q) ≤ M')
    (hLK : GLAPLayer p (K ⊓ Subgroup.centralizer (Ft : Set Q)) ≠ ⊥) :
    ∃ W : Subgroup Q, GLAPComponent p (GLAPLayer p (GLAPLayer p (⊤ : Subgroup Q) ⊓
      Subgroup.centralizer (Ft : Set Q))) W ∧ W ≤ K ∧ W ≠ ⊥ := by
  set X : Subgroup Q := Subgroup.centralizer (Ft : Set Q) with hX
  set Y : Subgroup Q := GLAPLayer p (⊤ : Subgroup Q) with hY
  obtain ⟨J, hJ, hJne⟩ : ∃ J : Subgroup Q, GLAPComponent p (K ⊓ X) J ∧ J ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    apply hLK
    refine le_bot_iff.1 (sSup_le fun J hJ => ?_)
    rw [hcon J hJ]
  have hZ0X : IsSubnormal (K ⊓ X) X := by
    have h1 := isSubnormal_inf hKM X
    rwa [inf_eq_right.2 hCF] at h1
  have hJX : GLAPComponent p X J :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.glaPComponent_up hp hJ inf_le_right
      (isSubnormal_trans' hJ.2.1 hZ0X)
  have hbal : GLAPLayer p X ≤ Y := hI181 Q p hp hQK Ft hFp
  have hJlay : J ≤ GLAPLayer p X := le_sSup hJX
  have hJY : J ≤ Y := hJlay.trans hbal
  have hJS : J ≤ Y ⊓ X := le_inf hJY hJX.1
  have hJS' : GLAPComponent p (Y ⊓ X) J :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.glaPComponent_down hp hJX hJS inf_le_right
  have hJL : J ≤ GLAPLayer p (Y ⊓ X) := le_sSup hJS'
  exact ⟨J, CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.glaPComponent_down hp hJS' hJL
    (Lemma138.glaPLayer_le_self p _), hJ.1.trans inf_le_left, hJne⟩

end QLevel

section GLevel

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem card_barX_of_isPGroup (hp : p.Prime) {N H : Subgroup G} (hH : IsPGroup p ↥H)
    (hHN : H ≤ N) : Nat.card ↥(barX p N H) = Nat.card ↥H := by
  have hinj := injective_barX_comp hp hH hHN
  have hr : ((QuotientGroup.mk' (GLAPPrimeCore p ↥N)).comp (H.subgroupOf N).subtype).range =
      barX p N H := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  rw [← hr, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHN).toEquiv]

theorem card_le_pow_of_isElemAbelian_quot (hp : p.Prime) {N : Subgroup G} {m : ℕ}
    (hm : CFSG.Open.pRank p N ≤ m) {A : Subgroup (↥N ⧸ GLAPPrimeCore p ↥N)}
    (hA : IsElemAbelian p A) : Nat.card ↥A ≤ p ^ m := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := (Lemma137.isPGroup_of_isElemAbelian hA).exists_card_eq
  have h1 : k ≤ CFSG.Open.pRank p A := CFSG.SectionRank.le_pRank hp.one_lt le_rfl hA hk
  have h2 : CFSG.Open.pRank p A ≤
      CFSG.Open.pRank p (⊤ : Subgroup (↥N ⧸ GLAPPrimeCore p ↥N)) :=
    CFSG.SectionRank.pRank_mono hp.one_lt le_top
  have h3 : CFSG.Open.pRank p (⊤ : Subgroup (↥N ⧸ GLAPPrimeCore p ↥N)) =
      CFSG.Open.pRank p N := by
    have := Lemma137.pRank_barX_eq hp (N := N) (K := N) le_rfl
    rwa [barX_self] at this
  rw [hk]
  exact Nat.pow_le_pow_right hp.pos (h1.trans (h2.trans (h3.le.trans hm)))

theorem normalizer_le_barX (hp : p.Prime) {N B M : Subgroup G} (hBp : IsPGroup p ↥B)
    (hBN : B ≤ N)
    (hnorm : ∀ E : Subgroup G, E ≤ B → 2 ≤ CFSG.Open.pRank p E →
      Subgroup.normalizer (E : Set G) ≤ M)
    {U : Subgroup (↥N ⧸ GLAPPrimeCore p ↥N)} (hU : U ≤ barX p N B)
    (hU2 : 2 ≤ CFSG.Open.pRank p U) :
    Subgroup.normalizer (U : Set (↥N ⧸ GLAPPrimeCore p ↥N)) ≤ barX p N (M ⊓ N) := by
  obtain ⟨E, hEB, hEU, hEr⟩ := exists_le_barX_eq hp hBp hBN hU
  have hEp : IsPGroup p ↥E := hBp.to_le hEB
  have hEN : E ≤ N := hEB.trans hBN
  rw [← hEU]
  refine (normalizer_barX_le hp hEp hEN).trans ?_
  have hE2 : 2 ≤ CFSG.Open.pRank p E := by rw [hEr]; exact hU2
  have hle : Subgroup.normalizer (E : Set G) ≤ M := hnorm E hEB hE2
  refine Subgroup.map_mono (fun y hy => ?_)
  exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨hle (Subgroup.mem_subgroupOf.1 hy), y.2⟩)

theorem center_barX_dvd (hp : p.Prime) (hp2 : p ≠ 2) (hI113 : Lemma138.InputI113p)
    {N B Lp : Subgroup G} (hNK : IsKGroup ↥N) (hBmax : GLAIsBmax p (B.subgroupOf N))
    (hBN : B ≤ N) (hLp : GLAPComponent p N Lp)
    (hnot : ¬ B ≤ Subgroup.normalizer (Lp : Set G)) :
    p ∣ Nat.card ↥(Subgroup.center ↥(barX p N Lp)) := by
  have hLpN : Lp ≤ N := hLp.1
  have hcomp : GLAPComponent p (⊤ : Subgroup ↥N) (Lp.subgroupOf N) := glaPComponent_top hLp
  have hnot' : ¬ B.subgroupOf N ≤
      Subgroup.normalizer ((Lp.subgroupOf N : Subgroup ↥N) : Set ↥N) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hLpN]
    intro h
    exact hnot fun b hb => Subgroup.mem_subgroupOf.1
      (h (Subgroup.mem_subgroupOf.2 hb : (⟨b, hBN hb⟩ : ↥N) ∈ B.subgroupOf N))
  have h1 := hI113 ↥N hNK p hp hp2 (B.subgroupOf N) hBmax (Lp.subgroupOf N) hcomp hnot'
  let e1 : (↥(Lp.subgroupOf N) ⧸ GLAPPrimeCore p ↥(Lp.subgroupOf N)) ≃*
      (↥Lp ⧸ GLAPPrimeCore p ↥Lp) :=
    QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hLpN)
      (glaPPrimeCore_map_iso p (Subgroup.subgroupOfEquivOfLe hLpN))
  let e : (↥(Lp.subgroupOf N) ⧸ GLAPPrimeCore p ↥(Lp.subgroupOf N)) ≃* ↥(barX p N Lp) :=
    e1.trans (quotEquivBarX hp hLpN hLp.2.1)
  have hcen := Subgroup.map_center_eq e
  have hcard : Nat.card ↥(Subgroup.center ↥(barX p N Lp)) =
      Nat.card ↥(Subgroup.center (↥(Lp.subgroupOf N) ⧸ GLAPPrimeCore p ↥(Lp.subgroupOf N))) := by
    rw [← hcen, Subgroup.card_map_of_injective e.injective]
  rw [hcard]
  exact h1

end GLevel

theorem sc_of_maximal {Q : Type} [Group Q] [Finite Q] {p : ℕ} {B : Subgroup Q}
    (hB : IsElemAbelian p B)
    (hmax : ∀ A : Subgroup Q, IsElemAbelian p A → Nat.card ↥A ≤ Nat.card ↥B) :
    ∀ y ∈ Subgroup.centralizer (B : Set Q), y ^ p = 1 → y ∈ B := by
  intro y hy hyp
  have hz : IsElemAbelian p (Subgroup.zpowers y) := isElemAbelian_zpowers hyp
  have hcomm : ∀ a ∈ B, ∀ b ∈ Subgroup.zpowers y, a * b = b * a := by
    intro a ha b hb
    have hb' : b ∈ Subgroup.centralizer (B : Set Q) := (Subgroup.zpowers_le.2 hy) hb
    exact (Subgroup.mem_centralizer_iff.1 hb') a ha
  have hsup : IsElemAbelian p (B ⊔ Subgroup.zpowers y) := IsElemAbelian.sup_of_commute hB hz hcomm
  have hle := hmax _ hsup
  have heq : B = B ⊔ Subgroup.zpowers y := Subgroup.eq_of_le_of_card_ge le_sup_left hle
  rw [heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)

theorem kt_package (hL133 : Lemma133Statement) (hL137i : Lemma137_iStatement)
    (hL137ii : Lemma137_ii_iiiStatement) (hPi : InputPiCenter) (hAb : InputAbIdx2)
    (hNo7 : Lemma137_noA7Statement) (hOm : InputOmegaTwoPerfect)
    {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A D T : Subgroup G}
    (h : Sec13 G m p B M E A D T) {L : Subgroup G}
    (hL : GLAPComponent p (Istar p M D) L) (hL1 : 3 < p ∨ 2 ≤ CFSG.Open.pRank p L) :
    IsSimpleGroup ↥(barX p (Nof T) (derivedInf (Nof T ⊓ L))) ∧
    ¬ IsMulCommutative ↥(barX p (Nof T) (derivedInf (Nof T ⊓ L))) ∧
    ((∃ k : ℕ, 5 ≤ k * p ∧ IsAltType (k * p) ↥(barX p (Nof T) (derivedInf (Nof T ⊓ L)))) ∨
      (∃ k : ℕ, IsAltType (k * p + 2) ↥(barX p (Nof T) (derivedInf (Nof T ⊓ L)))) ∨
      (∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧ HasFixedPointFreeOrder ε n p ∧
        Nonempty (↥(barX p (Nof T) (derivedInf (Nof T ⊓ L))) ≃*
          ↥(⁅(StatedSp n (ZMod 2)), (StatedSp n (ZMod 2))⁆ : Subgroup
            (GL (Fin n ⊕ Fin n) (ZMod 2))))) ∨
      (∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧
        IsOmegaTwo ε (n + 1) ↥(barX p (Nof T) (derivedInf (Nof T ⊓ L))) ∧
        HasFixedPointFreeOrder ε n p)) ∧
    p ∣ Nat.card ↥(barX p (Nof T) (derivedInf (Nof T ⊓ L))) ∧
    GLAPPrimeCoreOf p (derivedInf (Nof T ⊓ L)) ≤ GLAPPrimeCoreOf p (Nof T) ∧
    B ⊓ L ≤ derivedInf (Nof T ⊓ L) := by
  have hS : GLStanding G m p := h.standing
  have hp : p.Prime := hS.prime
  have hp2 : p ≠ 2 := hS.ne_two
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  have hBel : IsElemAbelian p B := h.bOne.1.1
  have hBN : B ≤ Nof T := hL137i h
  have h133 := (hL133 h).2 L hL
  have hPiL : IsPiGroup p (↥L ⧸ CFSG.pCore 2 ↥L) := h133.1.2.1
  have hnhL : ¬ IsHatSeven (↥L ⧸ CFSG.pCore 2 ↥L) := h133.1.2.2
  have hrankBL : CFSG.Open.pRank p (B ⊓ L) = CFSG.Open.pRank p L := h133.2.2.2.2
  have h137 := hL137ii h hL hL1
  have hKeq := h137.1
  have hsimp : IsSimpleGroup ↥(barX p (Nof T) (derivedInf (Nof T ⊓ L))) := h137.2.1
  have hnc := h137.2.2.1
  have hΩ : ∀ (ε : Bool) (n : ℕ), IsOmegaTwo ε (n + 1) (↥L ⧸ CFSG.pCore 2 ↥L) →
      (IsOmegaTwo ε (n + 1) ↥(barX p (Nof T) (Nof T ⊓ L)) ∨
        Nonempty (↥(barX p (Nof T) (Nof T ⊓ L)) ≃* ↥(StatedSp n (ZMod 2)))) := by
    intro ε n hX
    by_cases hc : barX p M T ≤ Subgroup.centralizer
        ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M))
    · exact Or.inl ((h137.2.2.2.1 ε n hX).1 hc)
    · exact Or.inr ((h137.2.2.2.1 ε n hX).2 hc)
  have hA : ∀ k : ℕ, IsAltType (k * p + 2) (↥L ⧸ CFSG.pCore 2 ↥L) →
      (IsAltType (k * p + 2) ↥(barX p (Nof T) (Nof T ⊓ L)) ∨
        Nonempty (↥(barX p (Nof T) (Nof T ⊓ L)) ≃* Equiv.Perm (Fin (k * p)))) := by
    intro k hX
    by_cases hc : barX p M T ≤ Subgroup.centralizer
        ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M))
    · exact Or.inl ((h137.2.2.2.2 k hX).1 hc)
    · exact Or.inr ((h137.2.2.2.2 k hX).2 hc)
  have hidx := Sec13d.index_pow_two_of_piType hPi hAb hp hp2 hPiL hnhL
    (fun h3 => hNo7 h hL h3) hΩ hA
  obtain ⟨j, hj⟩ := hidx
  have hLnt : Nontrivial (↥L ⧸ CFSG.pCore 2 ↥L) := by
    haveI := hPiL.1.2
    exact Function.Surjective.nontrivial
      (f := QuotientGroup.mk (s := Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)))
      QuotientGroup.mk_surjective
  have hdvdL : p ∣ Nat.card ↥L :=
    (Lemma137.dvd_card_of_pPrimeCore_eq_bot hp hPiL.2.1).trans (Subgroup.card_quotient_dvd_card _)
  have hJt1 : 1 ≤ CFSG.Open.pRank p (barX p (Nof T) (Nof T ⊓ L)) := by
    have hBLp : IsPGroup p ↥(B ⊓ L) :=
      Lemma137.isPGroup_of_isElemAbelian (Lemma137.isElemAbelian_mono (E := B ⊓ L) (F := B)
        inf_le_left hBel)
    have hBLN : B ⊓ L ≤ Nof T := inf_le_left.trans hBN
    have h1 : 1 ≤ CFSG.Open.pRank p (barX p (Nof T) (B ⊓ L)) := by
      rw [rank_barX_of_isPGroup hp hBLp hBLN, hrankBL]
      exact Lemma137.one_le_pRank_of_dvd hp hdvdL
    exact h1.trans (CFSG.SectionRank.pRank_mono hp1 (barX_mono_of_le p (inf_le_inf_right L hBN)))
  have hdvdJt : p ∣ Nat.card ↥(barX p (Nof T) (Nof T ⊓ L)) :=
    Lemma137.dvd_card_of_one_le_pRank hp hJt1
  have hJtTypes : (∃ k : ℕ, IsAltType (k * p + 2) ↥(barX p (Nof T) (Nof T ⊓ L))) ∨
      (∃ k : ℕ, Nonempty (↥(barX p (Nof T) (Nof T ⊓ L)) ≃* Equiv.Perm (Fin (k * p)))) ∨
      (∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧ HasFixedPointFreeOrder ε n p ∧
        Nonempty (↥(barX p (Nof T) (Nof T ⊓ L)) ≃* ↥(StatedSp n (ZMod 2)))) ∨
      (∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧ IsOmegaTwo ε (n + 1) ↥(barX p (Nof T) (Nof T ⊓ L)) ∧
        HasFixedPointFreeOrder ε n p) := by
    have hz : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := hPi _ p hp hp2 hPiL hnhL
    let hY : (↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
        (↥L ⧸ CFSG.pCore 2 ↥L) :=
      (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
    obtain ⟨-, -, hcases⟩ := hPiL
    rcases hcases with ⟨k, ⟨e⟩⟩ | ⟨n, ε, hn, hΩX, hfp⟩ | ⟨h3, ⟨e⟩⟩
    · have hAX : IsAltType (k * p + 2) (↥L ⧸ CFSG.pCore 2 ↥L) := ⟨hY.symm.trans e⟩
      rcases hA k hAX with h1 | ⟨e1⟩
      · exact Or.inl ⟨k, h1⟩
      · exact Or.inr (Or.inl ⟨k, e1⟩)
    · have hΩX' : IsOmegaTwo ε (n + 1) (↥L ⧸ CFSG.pCore 2 ↥L) :=
        Sec13d.isOmegaTwo_of_mulEquiv hY.symm hΩX
      rcases hΩ ε n hΩX' with h1 | ⟨e1⟩
      · exact Or.inr (Or.inr (Or.inr ⟨ε, n, hn, h1, hfp⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨ε, n, hn, hfp, e1⟩))
    · exact absurd ⟨hY.symm.trans e⟩ (hNo7 h hL h3)
  haveI : IsSimpleGroup ↥(barX p (Nof T) (derivedInf (Nof T ⊓ L))) := hsimp
  have hKt := Lemma137.kt_types hp hp2 hOm hKeq hnc hdvdJt hJtTypes
  have hKN : derivedInf (Nof T ⊓ L) ≤ Nof T := (Sec13d.derivedInf_le _).trans inf_le_left
  have hdvdKt : p ∣ Nat.card ↥(barX p (Nof T) (derivedInf (Nof T ⊓ L))) :=
    Lemma137.dvd_card_kt hp hp2 hKeq hdvdJt hj
  have hOK : GLAPPrimeCoreOf p (derivedInf (Nof T ⊓ L)) ≤ GLAPPrimeCoreOf p (Nof T) :=
    Lemma137.gLAPPrimeCoreOf_le_of_simple hp hKN hsimp hdvdKt
  have hBK : B ⊓ L ≤ derivedInf (Nof T ⊓ L) := by
    intro x hx
    obtain ⟨hxB, hxL⟩ := Subgroup.mem_inf.1 hx
    exact Sec13d.mem_derivedInf_of_pow_eq_one hp hp2 hKeq ⟨j, hj⟩ (hBN hxB) hxL (hBel.2 x hxB)
  exact ⟨hsimp, hnc, hKt, hdvdKt, hOK, hBK⟩

end Lemma138b

open Lemma138b

theorem lemma138_of_inputs (hL133 : Lemma133Statement) (hL137i : Lemma137_iStatement)
    (hL137ii : Lemma137_ii_iiiStatement) (hL137iv : Lemma137_iv_vStatement)
    (hNo7 : Lemma137_noA7Statement) (hPi : InputPiCenter) (hAb : InputAbIdx2)
    (hOm : InputOmegaTwoPerfect) (hI2710 : Lemma138.InputI27102) (hI2711 : Lemma138.InputI27111)
    (hI226 : Lemma138.InputI226) (hI181 : Lemma138.InputI181) (hI113 : Lemma138.InputI113p) :
    Lemma138Statement := by
  intro G _ _ m p B M E A D T h L hL hL1
  have hS : GLStanding G m p := h.standing
  have hp : p.Prime := hS.prime
  have hp2 : p ≠ 2 := hS.ne_two
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  have hBel : IsElemAbelian p B := h.bOne.1.1
  have hBp : IsPGroup p ↥B := Lemma137.isPGroup_of_isElemAbelian hBel
  have hBN : B ≤ Nof T := hL137i h
  have hcardB : Nat.card B = p ^ m := hS.card_eq h.bOne
  have hm4 : 4 ≤ m := hS.four_le
  have hT2 : IsPGroup 2 ↥T := (isPGroup_gammaStar p D).to_le h.hT2
  have hTne : T ≠ ⊥ := by
    intro hT0
    obtain ⟨P, hP, -, hPle⟩ := exists_ne_bot_le_pCoreOf h.pre.1.1
    exact hP (eq_bot_iff.2 (hPle.trans (h.hT1.trans hT0.le)))
  have hN2 : IsTwoLocal (Nof T) := ⟨T, hTne, hT2, rfl⟩
  have hNtop : Nof T ≠ ⊤ := isTwoLocal_ne_top hS hN2
  have hNK : IsKGroup ↥(Nof T) :=
    CFSG.KCore.KGroupNonab.kGroupAllSimple CFSG.Assembly.inCatalog_isoInvariant
      CFSG.Assembly.inCatalog_containsAbelianSimple (isKGroup_of_isKProper hS.kProper hNtop)
  have hBmax : GLAIsBmax p (B.subgroupOf (Nof T)) := glaIsBmax_subgroupOf hS h.bOne hN2 hBN
  have hQK : IsKGroup (↥(Nof T) ⧸ GLAPPrimeCore p ↥(Nof T)) := hNK.quotient _
  have hcoreQ : GLAPPrimeCore p (↥(Nof T) ⧸ GLAPPrimeCore p ↥(Nof T)) = ⊥ :=
    CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot p
  obtain ⟨hKs, hKnc, hKt, hdvdKt, hOK, hBK⟩ :=
    kt_package hL133 hL137i hL137ii hPi hAb hNo7 hOm h hL hL1
  obtain ⟨⟨F, hFB, hFcard, hLK⟩, -, hBdec, hrankK⟩ := hL137iv h hL hL1
  have h133 := (hL133 h).2 L hL
  have hBL : B ≤ Subgroup.normalizer (L : Set G) := h133.2.1
  have hrankBL : CFSG.Open.pRank p (B ⊓ L) = CFSG.Open.pRank p L := h133.2.2.2.2
  have hKN : derivedInf (Nof T ⊓ L) ≤ Nof T := (Sec13d.derivedInf_le _).trans inf_le_left
  haveI : IsSimpleGroup ↥(barX p (Nof T) (derivedInf (Nof T ⊓ L))) := hKs
  obtain ⟨-, hsplit2, hdirect, -, hpRank⟩ :=
    Lemma137.barX_transfer hp hKN hBN hOK hKnc hBdec hBel hrankK
  have hBt : IsElemAbelian p (barX p (Nof T) B) := isElemAbelian_barX hBel
  have hcardBt : Nat.card ↥(barX p (Nof T) B) = p ^ m :=
    (card_barX_of_isPGroup hp hBp hBN).trans hcardB
  have hB4 : 4 ≤ CFSG.Open.pRank p (barX p (Nof T) B) := by
    rw [rank_barX_of_isPGroup hp hBp hBN]
    exact hm4.trans (CFSG.SectionRank.le_pRank hp1 le_rfl hBel hcardB)
  have hrankN : CFSG.Open.pRank p (Nof T) ≤ m :=
    (pRank_le_glaTwoLocalRank hp1 hN2).trans hS.rank_eq.le
  have hmax : ∀ A : Subgroup (↥(Nof T) ⧸ GLAPPrimeCore p ↥(Nof T)), IsElemAbelian p A →
      Nat.card ↥A ≤ Nat.card ↥(barX p (Nof T) B) := fun A hA => by
    rw [hcardBt]
    exact card_le_pow_of_isElemAbelian_quot hp hrankN hA
  have hFel : IsElemAbelian p F := Lemma137.isElemAbelian_mono hFB hBel
  have hFp : IsPGroup p ↥F := Lemma137.isPGroup_of_isElemAbelian hFel
  have hFN : F ≤ Nof T := hFB.trans hBN
  have hFt : barX p (Nof T) F ≤ barX p (Nof T) B := barX_mono_of_le p hFB
  have hFtp : IsPGroup p ↥(barX p (Nof T) F) :=
    Lemma137.isPGroup_of_isElemAbelian (isElemAbelian_barX hFel)
  have hFi : Nat.card ↥(barX p (Nof T) B) ≤ p ^ 2 * Nat.card ↥(barX p (Nof T) F) := by
    rw [card_barX_of_isPGroup hp hBp hBN, card_barX_of_isPGroup hp hFp hFN]
    exact hFcard
  have hF2 : 2 ≤ CFSG.Open.pRank p (barX p (Nof T) F) := by
    rw [rank_barX_of_isPGroup hp hFp hFN]
    obtain ⟨j, hj⟩ := hFp.exists_card_eq
    have h1 : p ^ m ≤ p ^ (2 + j) := by
      calc p ^ m = Nat.card ↥B := hcardB.symm
        _ ≤ p ^ 2 * Nat.card ↥F := hFcard
        _ = p ^ (2 + j) := by rw [hj, pow_add]
    have h2 : m ≤ 2 + j := (Nat.pow_le_pow_iff_right hp1).1 h1
    have h3 : j ≤ CFSG.Open.pRank p F := CFSG.SectionRank.le_pRank hp1 le_rfl hFel hj
    omega
  have hnormM : ∀ E : Subgroup G, E ≤ B → 2 ≤ CFSG.Open.pRank p E →
      Subgroup.normalizer (E : Set G) ≤ M := by
    intro E hEB hE2
    refine le_trans ?_ h.uniq.clause_d
    unfold GLBCore
    exact le_sSup ⟨E, hEB, hE2, rfl⟩
  have hΓM : ∀ U : Subgroup (↥(Nof T) ⧸ GLAPPrimeCore p ↥(Nof T)), U ≤ barX p (Nof T) B →
      2 ≤ CFSG.Open.pRank p U →
      Subgroup.normalizer (U : Set (↥(Nof T) ⧸ GLAPPrimeCore p ↥(Nof T))) ≤
        barX p (Nof T) (M ⊓ Nof T) :=
    fun U hU hU2 => normalizer_le_barX hp hBp hBN hnormM hU hU2
  have hCF : Subgroup.centralizer ((barX p (Nof T) F : Subgroup _) :
      Set (↥(Nof T) ⧸ GLAPPrimeCore p ↥(Nof T))) ≤ barX p (Nof T) (M ⊓ Nof T) :=
    (Subgroup.centralizer_le_normalizer _).trans (hΓM _ hFt hF2)
  have hLM : IsSubnormal L M := isSubnormal_trans' hL.2.1 (istar_isSubnormal p M D)
  have hKsn : IsSubnormal (derivedInf (Nof T ⊓ L)) (Nof T ⊓ L) :=
    IsSubnormal.step (Sec13d.derivedInf_le _)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (Sec13d.derivedInf_le _)).2
        (fun b hb => Sec13d.mem_normalizer_derivedInf (Subgroup.le_normalizer hb)))
      (IsSubnormal.refl _)
  have hKM : IsSubnormal (barX p (Nof T) (derivedInf (Nof T ⊓ L))) (barX p (Nof T) (M ⊓ Nof T)) := by
    have h1 : IsSubnormal (Nof T ⊓ L) (Nof T ⊓ M) := by
      have := isSubnormal_inf hLM (Nof T)
      rwa [inf_comm L, inf_comm M] at this
    have h2 : IsSubnormal (derivedInf (Nof T ⊓ L)) (M ⊓ Nof T) := by
      rw [inf_comm M]
      exact isSubnormal_trans' hKsn h1
    exact isSubnormal_barX p h2
  have hBnorm : B ≤ Subgroup.normalizer ((derivedInf (Nof T ⊓ L) : Subgroup G) : Set G) := by
    intro b hb
    have hN : b ∈ Subgroup.normalizer ((Nof T : Subgroup G) : Set G) :=
      Lemma137.mem_normalizer_normalizer_of (hBN hb)
    exact Sec13d.mem_normalizer_derivedInf (Sec13d.mem_normalizer_inf_of hN (hBL hb))
  have hKB : barX p (Nof T) B ≤ Subgroup.normalizer
      ((barX p (Nof T) (derivedInf (Nof T ⊓ L)) : Subgroup _) : Set _) :=
    barX_le_normalizer hBnorm
  have hKn3 : ¬ (p = 3 ∧ IsAltType 5 ↥(barX p (Nof T) (derivedInf (Nof T ⊓ L)))) := by
    rintro ⟨hp3, ⟨e⟩⟩
    have hrk2 : 2 ≤ CFSG.Open.pRank p L := by
      rcases hL1 with h3 | h2
      · omega
      · exact h2
    have hr1 : 2 ≤ CFSG.Open.pRank p (derivedInf (Nof T ⊓ L)) :=
      hrk2.trans (hrankBL.symm.le.trans (CFSG.SectionRank.pRank_mono hp1 hBK))
    have hr2 : CFSG.Open.pRank p (barX p (Nof T) (derivedInf (Nof T ⊓ L))) =
        CFSG.Open.pRank p (derivedInf (Nof T ⊓ L)) := Lemma137.pRank_barX_eq hp hKN
    have hcard : Nat.card ↥(barX p (Nof T) (derivedInf (Nof T ⊓ L))) = 60 := by
      rw [Nat.card_congr e.toEquiv]
      have h2 := two_mul_nat_card_alternatingGroup (α := Fin 5)
      have hperm : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
        rw [Nat.card_perm, Nat.card_fin]
        rfl
      rw [hperm] at h2
      omega
    obtain ⟨E', hE'le, -, hE'card⟩ := CFSG.SectionRank.exists_pRank hp1
      (barX p (Nof T) (derivedInf (Nof T ⊓ L)))
    have hdvd : p ^ CFSG.Open.pRank p (barX p (Nof T) (derivedInf (Nof T ⊓ L))) ∣ 60 := by
      rw [← hcard, ← hE'card]
      exact Subgroup.card_dvd_of_le hE'le
    have h9 : p ^ 2 ∣ 60 :=
      (pow_dvd_pow p (hr2 ▸ hr1)).trans hdvd
    rw [hp3] at h9
    norm_num at h9
  have hKG : ∀ C : Subgroup (↥(Nof T) ⧸ GLAPPrimeCore p ↥(Nof T)), IsComponentOf C ⊤ →
      IsKGroup ↥C := fun C _ => hQK.subgroup C
  have hNI : ∀ C : Subgroup (↥(Nof T) ⧸ GLAPPrimeCore p ↥(Nof T)), IsComponentOf C ⊤ →
      ¬ barX p (Nof T) B ≤ Subgroup.normalizer (C : Set (↥(Nof T) ⧸ GLAPPrimeCore p ↥(Nof T))) →
      C ≤ barX p (Nof T) (M ⊓ Nof T) := by
    intro C hC hnot
    obtain ⟨Lp, hLp, rfl⟩ := exists_glaPComponent_barX_eq (p := p) (Nof T) hC
    have hnotB : ¬ B ≤ Subgroup.normalizer (Lp : Set G) := fun hB =>
      hnot (barX_le_normalizer hB)
    have hZ := center_barX_dvd hp hp2 hI113 hNK hBmax hBN hLp hnotB
    have hSC := sc_of_maximal hBt hmax
    have h22 := GL83.I_22_6_proved (↥(Nof T) ⧸ GLAPPrimeCore p ↥(Nof T)) p hp hp2
      (barX p (Nof T) B) (barX p (Nof T) Lp) hBt hSC hC hnot hZ
    refine h22.trans (sSup_le ?_)
    rintro _ ⟨U, hUB, hU2, rfl⟩
    exact hΓM U hUB hU2
  obtain ⟨W, hW, hWK, hWne⟩ := exists_W hp hI181 hQK hFtp hKM hCF hLK
  exact Lemma138.core_isComponent hp hp2 hI2710 hI2711 hI226 (glaPLayer_top_normal p)
    (glaPLayer_layer hp) (gLALayer_layer hp hcoreQ) hBt hB4 hmax hFt hFi hKs hKnc hKt hKn3 hKB
    hsplit2.symm hdirect hpRank hKM hΓM hNI hKG hLK hW hWK hWne

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
