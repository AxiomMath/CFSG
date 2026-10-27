module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95IvDefs
import CFSG.LocalAnalysis.GLTheoremB.Prop95IvAux
import CFSG.LocalAnalysis.GLTheoremB.Prop95IvBlock
import CFSG.LocalAnalysis.GLTheoremB.Prop95IvT2
import CFSG.GH74.GLS.AssemblyComponents

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Parts
open CFSG.LocalAnalysis.GLTheoremB.Prop95Assembly
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531 (FFChevConclusion)
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevTwo)
open scoped commutatorElement

section Setting

variable {G : Type} [Group G] [Finite G]
variable {m p : ℕ} {M D L : Subgroup G}

private theorem ivAlt_center_eq_bot_of_equiv {Y A : Type*} [Group Y] [Group A] (e : Y ≃* A)
    (hA : Subgroup.center A = ⊥) : Subgroup.center Y = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  have hx' : e x ∈ Subgroup.center A := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx y]
  rw [hA, Subgroup.mem_bot] at hx'
  exact e.injective (hx'.trans (map_one e).symm)

private theorem ivAlt_center_alt_eq_bot {n : ℕ} (hn : 4 ≤ n) :
    Subgroup.center ↥(alternatingGroup (Fin n)) = ⊥ :=
  alternatingGroup.center_eq_bot (by simpa using hn)

private noncomputable def ivAlt_quotCenterEquiv {Y : Type*} [Group Y] (hZ : Subgroup.center Y = ⊥) :
    (Y ⧸ Subgroup.center Y) ≃* Y :=
  (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot

private theorem ivAlt_isQuasisimple_of_open {Q : Type*} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q := by
  have hperf : Group.IsPerfect Q := ⟨h.1⟩
  refine ⟨hperf, h.2, ?_⟩
  by_contra hab
  have hcomm : ∀ x y : Q ⧸ Subgroup.center Q, x * y = y * x := by
    intro x y
    by_contra hne
    exact hab ⟨x, y, hne⟩
  have hsimple : IsSimpleGroup (Q ⧸ Subgroup.center Q) := h.2
  have hperf' : Group.IsPerfect (Q ⧸ Subgroup.center Q) :=
    Group.IsPerfect.ofSurjective (G := Q) (G' := Q ⧸ Subgroup.center Q)
      (f := QuotientGroup.mk' (Subgroup.center Q)) (QuotientGroup.mk'_surjective _)
  have hbot : _root_.commutator (Q ⧸ Subgroup.center Q) = ⊥ := by
    rw [_root_.commutator, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact hcomm y x
  have htop : (⊤ : Subgroup (Q ⧸ Subgroup.center Q)) = ⊥ :=
    (Group.IsPerfect.commutator_eq_top (G := Q ⧸ Subgroup.center Q)).symm.trans hbot
  have := hsimple.toNontrivial
  obtain ⟨x, hx⟩ := exists_ne (1 : Q ⧸ Subgroup.center Q)
  have hxbot : x ∈ (⊥ : Subgroup (Q ⧸ Subgroup.center Q)) := htop ▸ Subgroup.mem_top x
  exact hx (Subgroup.mem_bot.mp hxbot)

private theorem ivAlt_three_le_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : 3 ≤ p := by
  have := hp.two_le
  omega

private theorem ivAlt_five_le {k p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : 0 < k) :
    5 ≤ k * p + 2 := by
  have := ivAlt_three_le_prime hp hp2
  nlinarith

theorem bar_component_data (h : IvSetting m p M D L)
    (hAlt : ∃ n : ℕ, 5 ≤ n ∧
      Nonempty ((↥(tl M L) ⧸ Subgroup.center ↥(tl M L)) ≃* alternatingGroup (Fin n))) :
    IsComponentOf (barX p M L) ⊤ ∧ GLAPPrimeCore p ↥(barX p M L) = ⊥ ∧ InAlt ↥(barX p M L) := by
  have hcomp : IsComponentOf (barX p M L) ⊤ := h.hL.2.2.1
  haveI : Fact p.Prime := ⟨prime_of_standing h.standing⟩
  refine ⟨hcomp, ?_, ivAlt_isQuasisimple_of_open hcomp.2.2, ?_⟩
  · have hsn : (barX p M L).IsSubnormal := CFSG.Open.IsSubnormal.top_iff.1 hcomp.2.1
    have hle := CFSG.GH74.GLS.pPrimeCoreOf_le_of_subnormal p hsn
    have hbot : CFSG.pPrimeCore p (↥M ⧸ GLAPPrimeCore p ↥M) = ⊥ :=
      CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot p
    rw [hbot, le_bot_iff] at hle
    exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).1 hle
  · obtain ⟨n, hn, ⟨f⟩⟩ := hAlt
    exact ⟨n, hn, ⟨(psiHat h).symm.trans f⟩⟩

private theorem ivAlt_psiHat_mk (h : IvSetting m p M D L) (a : ↥(tl M L)) :
    psiHat h (QuotientGroup.mk a) = QuotientGroup.mk (psiL h a) := rfl

private theorem ivAlt_transposition_cq (h : IvSetting m p M D L) {k : ℕ} (hk : 0 < k)
    (e : ↥(barX p M L) ≃* ↥(alternatingGroup (Fin (k * p + 2))))
    {τ : Equiv.Perm (Fin (k * p + 2))}
    (hact : ActsLike (barX p M (gammaD D)) (barX p M L) e
      (Subgroup.zpowers (MulAut.conjNormal (H := alternatingGroup (Fin (k * p + 2))) τ))) :
    Subgroup.center ↥(barX p M L) = ⊥ ∧
      ∃ e' : (↥(tl M L) ⧸ Subgroup.center ↥(tl M L)) ≃* ↥(alternatingGroup (Fin (k * p + 2))),
        ActsLikeCQ (tl M (gammaD D)) (tl M L) e'
          (Subgroup.zpowers (MulAut.conjNormal (H := alternatingGroup (Fin (k * p + 2))) τ)) := by
  have h5 : 5 ≤ k * p + 2 :=
    ivAlt_five_le (prime_of_standing h.standing) (ne_two_of_standing h.standing) hk
  have hZ : Subgroup.center ↥(barX p M L) = ⊥ :=
    ivAlt_center_eq_bot_of_equiv e (ivAlt_center_alt_eq_bot (by omega))
  have hΓM : gammaD D ≤ M := gammaD_le h.hyp
  have hΓN := gammaD_le_normalizer (prime_of_standing h.standing) h.hyp h.hL h.hn
  have hCQ := (actsLike_iff_actsLikeCQ _ _ hZ e _).1 hact
  exact ⟨hZ, _, (actsLikeCQ_tl_iff_bar h _ _ hΓM hΓN).2 hCQ⟩

private theorem ivAlt_mem_tl_core_of_mem_ker (h : IvSetting m p M D L) {x : ↥(tl M L)}
    (hx : x ∈ (psiL h).ker) : (x : Mt M) ∈ tl M (GLAPPrimeCoreOf p M) := by
  have hx1 : projQ p M (pCore_two_le_glaPPrimeCore h.standing.beta.1 h.standing.beta.2.1 M)
      (x : Mt M) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
  have hx' : (x : Mt M) ∈ (L.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) := x.2
  obtain ⟨m, hm, hmx⟩ := Subgroup.mem_map.1 hx'
  have hmQ : m ∈ GLAPPrimeCore p ↥M := by
    rw [← hmx] at hx1
    exact (QuotientGroup.eq_one_iff m).1 hx1
  rw [← hmx]
  exact Subgroup.mem_map.2
    ⟨m, Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨m, hmQ, rfl⟩), rfl⟩

private theorem ivAlt_tl_gammaD_centralizes_center (h : IvSetting m p M D L)
    (hZ : Subgroup.center ↥(barX p M L) = ⊥) :
    ∀ w ∈ tl M (gammaD D), ∀ z ∈ Subgroup.center ↥(tl M L), w * (z : Mt M) = (z : Mt M) * w := by
  intro w hw z hz
  have hψz : psiL h z ∈ Subgroup.center ↥(barX p M L) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := psiL_surjective h g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz y]
  rw [hZ, Subgroup.mem_bot] at hψz
  have hzc : (z : Mt M) ∈ tl M (GLAPPrimeCoreOf p M) :=
    ivAlt_mem_tl_core_of_mem_ker h (MonoidHom.mem_ker.2 hψz)
  have hmem : ⁅w, (z : Mt M)⁆ ∈ ⁅tl M (gammaD D), tl M (GLAPPrimeCoreOf p M)⁆ :=
    Subgroup.commutator_mem_commutator hw hzc
  rw [commutator_tl_gammaD_glaPPrimeCore_eq_bot h.hyp h.hQ, Subgroup.mem_bot] at hmem
  exact commutatorElement_eq_one_iff_mul_comm.1 hmem

private theorem ivAlt_false_of_center_card_three {Y : Type*} [Group Y]
    (hc : Nat.card (Subgroup.center Y) = 3) (hinv : ∀ z ∈ Subgroup.center Y, z⁻¹ = z) : False := by
  have hall : ∀ z ∈ Subgroup.center Y, z = 1 := by
    intro z hz
    have h2 : z * z = 1 := mul_eq_one_iff_eq_inv.2 (hinv z hz).symm
    have h3 : (⟨z, hz⟩ : ↥(Subgroup.center Y)) ^ 3 = 1 := by
      have := pow_card_eq_one' (G := ↥(Subgroup.center Y)) (x := ⟨z, hz⟩)
      rwa [hc] at this
    have h3' : z * z * z = 1 := by
      have := congrArg Subtype.val h3
      simpa [pow_succ] using this
    rw [h2, one_mul] at h3'
    exact h3'
  have hbot : Subgroup.center Y = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hall
  rw [hbot, Subgroup.card_bot] at hc
  exact absurd hc (by norm_num)

private theorem ivAlt_not_isHatSeven_of_transposition_cq (hI : HatSevenOddInverts) {Yb : Type}
    [Group Yb] (W A : Subgroup Yb)
    (hcent : ∀ w ∈ W, ∀ z ∈ Subgroup.center ↥A, w * (z : Yb) = (z : Yb) * w)
    {n : ℕ} (hn : n = 7) (e : (↥A ⧸ Subgroup.center ↥A) ≃* ↥(alternatingGroup (Fin n)))
    (τ : Equiv.Perm (Fin n)) (hτ : τ.IsSwap)
    (hCQ : ActsLikeCQ W A e
      (Subgroup.zpowers (MulAut.conjNormal (H := alternatingGroup (Fin n)) τ)))
    (hH : IsHatSeven ↥A) : False := by
  subst hn
  obtain ⟨φ, hφ, hind⟩ := hCQ.2 _ (Subgroup.mem_zpowers _)
  have hsign : τ.sign = -1 := by
    obtain ⟨x, y, hxy, rfl⟩ := hτ
    exact Equiv.Perm.sign_swap hxy
  have hinv := hI ↥A hH e φ τ hsign hind
  obtain ⟨⟨w, hwN⟩, hwW, rfl⟩ := Subgroup.mem_map.1 hφ
  refine ivAlt_false_of_center_card_three hH.2.1 fun z hz => ?_
  have h1 := hinv z hz
  have h2 : (A.normalizerMonoidHom ⟨w, hwN⟩) z = z := by
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    have := hcent w (Subgroup.mem_subgroupOf.1 hwW) z hz
    simp [this]
  rw [h2] at h1
  exact h1.symm

theorem alt_transposition_tl (h : IvSetting m p M D L)
    (hT : ActsAsTransposition p (barX p M (gammaD D)) (barX p M L)) :
    InAlt ↥(tl M L) ∧ ∃ (k : ℕ) (e : (↥(tl M L) ⧸ Subgroup.center ↥(tl M L)) ≃*
        ↥(alternatingGroup (Fin (k * p + 2)))),
      0 < k ∧ ActsLikeTranspositionCQ (tl M (gammaD D)) (tl M L) (k * p + 2) e := by
  obtain ⟨k, hk, e, τ, hτ, hcard, hact⟩ := hT
  obtain ⟨-, e', hCQ⟩ := ivAlt_transposition_cq h hk e hact
  have h5 : 5 ≤ k * p + 2 :=
    ivAlt_five_le (prime_of_standing h.standing) (ne_two_of_standing h.standing) hk
  have hq := isComponentOf_tl (prime_of_standing h.standing) (ne_two_of_standing h.standing)
    h.hyp h.hL h.hn h.hnc h.hQ
  exact ⟨⟨ivAlt_isQuasisimple_of_open hq.2.2, k * p + 2, h5, ⟨e'⟩⟩, k, e', hk,
    (card_inducedAutGroup_tl_eq_bar h (gammaD_le h.hyp)
      (gammaD_le_normalizer (prime_of_standing h.standing) h.hyp h.hL h.hn)).trans hcard,
    τ, hτ, hCQ⟩

theorem not_A6_of_degree {Y : Type} [Group Y] {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : 0 < k)
    (e : (Y ⧸ Subgroup.center Y) ≃* ↥(alternatingGroup (Fin (k * p + 2)))) :
    ¬ Nonempty (Y ≃* alternatingGroup (Fin 6)) ∧ ¬ IsHatSix Y := by
  have h5 : 5 ≤ k * p + 2 := ivAlt_five_le hp hp2 hk
  have hp3 := ivAlt_three_le_prime hp hp2
  have key : ¬ Nonempty ((Y ⧸ Subgroup.center Y) ≃* alternatingGroup (Fin 6)) := by
    rintro ⟨f⟩
    have h6 : k * p + 2 = 6 := alt_degree_eq h5 (by norm_num) (e.symm.trans f)
    have hk1 : k = 1 := by
      by_contra hne
      have : 2 ≤ k := by omega
      nlinarith
    subst hk1
    have hp4 : p = 4 := by omega
    subst hp4
    exact absurd hp (by norm_num)
  refine ⟨?_, ?_⟩
  · rintro ⟨f⟩
    have hZ : Subgroup.center Y = ⊥ :=
      ivAlt_center_eq_bot_of_equiv f (ivAlt_center_alt_eq_bot (by norm_num))
    exact key ⟨(ivAlt_quotCenterEquiv hZ).trans f⟩
  · rintro ⟨-, -, hf⟩
    exact key hf

theorem not_isHatSeven_tl_of_transposition (hI : HatSevenOddInverts) (h : IvSetting m p M D L)
    (hT : ActsAsTransposition p (barX p M (gammaD D)) (barX p M L)) : ¬ IsHatSeven ↥(tl M L) := by
  intro hH
  obtain ⟨k, hk, e, τ, hτ, -, hact⟩ := hT
  obtain ⟨hZ, e', hCQ⟩ := ivAlt_transposition_cq h hk e hact
  have h5 : 5 ≤ k * p + 2 :=
    ivAlt_five_le (prime_of_standing h.standing) (ne_two_of_standing h.standing) hk
  obtain ⟨e7⟩ := hH.2.2
  have hn7 : k * p + 2 = 7 := alt_degree_eq h5 (by norm_num) (e'.symm.trans e7)
  exact ivAlt_not_isHatSeven_of_transposition_cq hI (tl M (gammaD D)) (tl M L)
    (ivAlt_tl_gammaD_centralizes_center h hZ) hn7 e' τ hτ hCQ hH

theorem alt_degree_kp (h : IvSetting m p M D L)
    (hT : ActsAsTransposition p (barX p M (gammaD D)) (barX p M L)) {n : ℕ}
    (e₂ : (↥(tl M L) ⧸ Subgroup.center ↥(tl M L)) ≃* ↥(alternatingGroup (Fin n))) (hn5 : 5 ≤ n) :
    ∃ k : ℕ, 0 < k ∧ n = k * p + 2 ∧ Subgroup.center ↥(barX p M L) = ⊥ := by
  obtain ⟨k, hk, e, -⟩ := hT
  have h5 : 5 ≤ k * p + 2 :=
    ivAlt_five_le (prime_of_standing h.standing) (ne_two_of_standing h.standing) hk
  have hZ : Subgroup.center ↥(barX p M L) = ⊥ :=
    ivAlt_center_eq_bot_of_equiv e (ivAlt_center_alt_eq_bot (by omega))
  exact ⟨k, hk, alt_degree_eq hn5 h5
    (e₂.symm.trans (((psiHat h).trans (ivAlt_quotCenterEquiv hZ)).trans e)), hZ⟩

theorem alt_alpha_action (h : IvSetting m p M D L) {k : ℕ}
    (hZ : Subgroup.center ↥(barX p M L) = ⊥)
    (e₂ : (↥(tl M L) ⧸ Subgroup.center ↥(tl M L)) ≃* ↥(alternatingGroup (Fin (k * p + 2))))
    (hTr : ActsLikeTranspositionCQ (tl M (gammaD D)) (tl M L) (k * p + 2) e₂) :
    ∃ (e : ↥(barX p M L) ≃* ↥(alternatingGroup (Fin (k * p + 2)))) (τ : Equiv.Perm (Fin (k * p + 2))),
      τ.IsSwap ∧ Nat.card (inducedAutGroup (barX p M (gammaD D)) (barX p M L)) = 2 ∧
        ActsLike (barX p M (gammaD D)) (barX p M L) e
          (Subgroup.zpowers (MulAut.conjNormal (H := alternatingGroup (Fin (k * p + 2))) τ)) ∧
        ∀ x : ↥L, e (barMap p h.hL.1 x) =
          e₂ (QuotientGroup.mk (toTl M L h.hL.1 x)) := by
  obtain ⟨hcard, τ, hτ, hCQ⟩ := hTr
  have hΓM : gammaD D ≤ M := gammaD_le h.hyp
  have hΓN := gammaD_le_normalizer (prime_of_standing h.standing) h.hyp h.hL h.hn
  let eB : (↥(barX p M L) ⧸ Subgroup.center ↥(barX p M L)) ≃*
      ↥(alternatingGroup (Fin (k * p + 2))) := (psiHat h).symm.trans e₂
  let e : ↥(barX p M L) ≃* ↥(alternatingGroup (Fin (k * p + 2))) :=
    (ivAlt_quotCenterEquiv hZ).symm.trans eB
  have heB : (QuotientGroup.quotientMulEquivOfEq hZ).trans
      (QuotientGroup.quotientBot.trans e) = eB := by
    ext q
    simp [e, ivAlt_quotCenterEquiv]
  have hpe : (psiHat h).trans eB = e₂ := by
    ext q
    simp [eB]
  have hCQ' : ActsLikeCQ (barX p M (gammaD D)) (barX p M L) eB
      (Subgroup.zpowers (MulAut.conjNormal (H := alternatingGroup (Fin (k * p + 2))) τ)) := by
    refine (actsLikeCQ_tl_iff_bar h eB _ hΓM hΓN).1 ?_
    rw [hpe]
    exact hCQ
  refine ⟨e, τ, hτ, (card_inducedAutGroup_tl_eq_bar h hΓM hΓN).symm.trans hcard, ?_, ?_⟩
  · refine (actsLike_iff_actsLikeCQ _ _ hZ e _).2 ?_
    rw [heB]
    exact hCQ'
  · intro x
    have hb : barMap p h.hL.1 x = psiL h (toTl M L h.hL.1 x) :=
      (DFunLike.congr_fun (psiL_comp_toTl h) x).symm
    have hq : (ivAlt_quotCenterEquiv hZ).symm (barMap p h.hL.1 x) =
        QuotientGroup.mk (barMap p h.hL.1 x) := rfl
    show eB ((ivAlt_quotCenterEquiv hZ).symm (barMap p h.hL.1 x)) = _
    rw [hq, hb]
    show e₂ ((psiHat h).symm (QuotientGroup.mk (psiL h (toTl M L h.hL.1 x)))) = _
    rw [← ivAlt_psiHat_mk, MulEquiv.symm_apply_apply]

theorem concl28b_module (h : IvSetting m p M D L) {n : ℕ}
    (e₂ : (↥(tl M L) ⧸ Subgroup.center ↥(tl M L)) ≃* ↥(alternatingGroup (Fin n)))
    (hmod : ∀ V U : Subgroup ↥M, IsNoncentralChiefFactor (L.subgroupOf M)
      (pCoreOf 2 (L.subgroupOf M)) V U →
      ChiefFactorIso (L.subgroupOf M) U V
        ((e₂.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥(tl M L)))).comp
          (toBar (CFSG.pCore 2 ↥M) (L.subgroupOf M)))
        (fun σ x => altHeartAct n (σ : Equiv.Perm (Fin n)) x)) :
    ∀ V U : Subgroup G, IsNoncentralChiefFactor L (pCoreOf 2 L) V U →
      ChiefFactorIso L U V
        ((e₂.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥(tl M L)))).comp
          (toTl M L h.hL.1))
        (fun σ x => altHeartAct n (σ : Equiv.Perm (Fin n)) x) := by
  intro V U hVU
  have hUM : U ≤ M := (hVU.2.1.trans (Subgroup.map_subtype_le _)).trans h.hL.1
  have h1 := hmod (V.subgroupOf M) (U.subgroupOf M) (isNoncentralChiefFactor_subgroupOf h.hL.1 hVU)
  have h2 := chiefFactorIso_of_subgroupOf h.hL.1 V U hUM _ _ h1
  have h3 : ((e₂.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥(tl M L)))).comp
      (toBar (CFSG.pCore 2 ↥M) (L.subgroupOf M))).comp
        (Subgroup.subgroupOfEquivOfLe h.hL.1).symm.toMonoidHom =
      (e₂.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥(tl M L)))).comp
        (toTl M L h.hL.1) := by
    refine MonoidHom.ext fun x => ?_
    exact congrArg (fun y : ↥(tl M L) => e₂ (QuotientGroup.mk y))
      (DFunLike.congr_fun (toBar_comp_subgroupOfEquiv h.hL.1) x)
  rwa [h3] at h2

end Setting

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
