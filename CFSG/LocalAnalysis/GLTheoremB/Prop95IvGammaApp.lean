module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95IvDefs
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.LocalAnalysis.GLTheoremB.CentralizerLift
import CFSG.LocalAnalysis.GLTheoremB.Prop95IvDescent
import CFSG.LocalAnalysis.GLTheoremB.Prop95IvFam
import CFSG.LocalAnalysis.GLTheoremB.Prop95IvT2

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

private theorem ga_isHatSeven_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsHatSeven X) : IsHatSeven Y := by
  obtain ⟨hc, hcard, ⟨f⟩⟩ := h
  have hcen : (Subgroup.center X).map e.toMonoidHom = Subgroup.center Y :=
    Subgroup.map_center_eq e
  refine ⟨?_, ?_, ⟨(QuotientGroup.congr _ _ e hcen).symm.trans f⟩⟩
  · have h1 := congrArg (Subgroup.map e.toMonoidHom) hc
    rw [commutator, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] at h1
    rw [commutator]
    exact h1
  · rw [← hcen, Subgroup.card_map_of_injective e.injective, hcard]

private noncomputable def ga_quotPCoreEquivTl (hLM : L ≤ M) (hsn : CFSG.Open.IsSubnormal L M) :
    (↥L ⧸ CFSG.pCore 2 ↥L) ≃* ↥(tl M L) := by
  have hker : (imageHom L M hLM).ker = CFSG.pCore 2 ↥L := by
    ext j
    rw [mem_ker_imageHom, ← CFSG.mem_openPCoreOf_iff j,
      ← inf_pCoreOf_eq_of_isSubnormal 2 hsn hLM, Subgroup.mem_inf]
    exact ⟨fun hj => ⟨j.2, hj⟩, fun hj => hj.2⟩
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (imageHom_surjective L M hLM))

private lemma ga_isQuasisimple_of_open {Q : Type*} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q := by
  obtain ⟨hcomm, hsimple⟩ := h
  refine ⟨Group.isPerfect_def.mpr hcomm, hsimple, ?_⟩
  by_contra hab
  push Not at hab
  have hle : commutator Q ≤ Subgroup.center Q := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff]
    change (QuotientGroup.mk' (Subgroup.center Q)) ⁅x, y⁆ = 1
    rw [map_commutatorElement, commutatorElement_def,
      hab ((QuotientGroup.mk' (Subgroup.center Q)) x), mul_inv_cancel_right, mul_inv_cancel]
  rw [hcomm] at hle
  haveI := hsimple
  obtain ⟨a, b, hne⟩ := exists_pair_ne (Q ⧸ Subgroup.center Q)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  exact hne (QuotientGroup.eq.mpr (hle (Subgroup.mem_top _)))

private theorem ga_mem_normalizer_iSup {X : Type*} [Group X] {ι : Sort*} {U : ι → Subgroup X}
    {g : X} (h : ∀ i, g ∈ Subgroup.normalizer (U i : Set X)) :
    g ∈ Subgroup.normalizer ((⨆ i, U i : Subgroup X) : Set X) := by
  have key : ∀ g : X, (∀ i, g ∈ Subgroup.normalizer (U i : Set X)) →
      ∀ x ∈ (⨆ i, U i : Subgroup X), g * x * g⁻¹ ∈ (⨆ i, U i : Subgroup X) := by
    intro g hg x hx
    refine Subgroup.iSup_induction U (C := fun x => g * x * g⁻¹ ∈ (⨆ i, U i : Subgroup X)) hx
      ?_ (by simp) ?_
    · intro i y hy
      exact Subgroup.mem_iSup_of_mem i ((Subgroup.mem_normalizer_iff.1 (hg i) y).1 hy)
    · intro a b ha hb
      have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ ha hb
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key g h x
  · intro hx
    have h' : ∀ i, g⁻¹ ∈ Subgroup.normalizer (U i : Set X) := fun i =>
      Subgroup.inv_mem _ (h i)
    have := key g⁻¹ h' _ hx
    simpa [mul_assoc] using this

theorem tl_glaPPrimeCore_three_eq_bot (hM : AltSixSevenCentre) (h : IvSetting m p M D L)
    (hp3 : p = 3)
    (hA7 : Nonempty ((↥(tl M L) ⧸ Subgroup.center ↥(tl M L)) ≃* alternatingGroup (Fin 7))) :
    GLAPPrimeCore 3 ↥(tl M L) = ⊥ := by
  have hcomp : IsComponentOf (tl M L) ⊤ :=
    isComponentOf_tl (prime_of_standing h.standing) (ne_two_of_standing h.standing) h.hyp h.hL
      h.hn h.hnc h.hQ
  have hperf : commutator ↥(tl M L) = ⊤ := hcomp.2.2.1
  have hcen : Nat.card (Subgroup.center ↥(tl M L)) ∣ 6 := hM 7 (Or.inr rfl) ↥(tl M L) hperf hA7
  have h2 : CFSG.pCore 2 ↥(tl M L) = ⊥ := pCore_tl_eq_bot h
  obtain ⟨e⟩ := hA7
  set K := tl M L with hK
  set N : Subgroup ↥K := GLAPPrimeCore 3 ↥K with hN
  have hNcop : Nat.Coprime 3 (Nat.card N) := CFSG.pPrimeCore_coprime_card
  have hNnormal : N.Normal := inferInstance
  have hNle : N ≤ Subgroup.center ↥K := by
    have hsimple : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hcomp.2.2.2
    set q := QuotientGroup.mk' (Subgroup.center ↥K) with hq
    have hnormal : (N.map q).Normal := hNnormal.map q (QuotientGroup.mk'_surjective _)
    rcases hnormal.eq_bot_or_eq_top with hbot | htop
    · intro x hx
      have : q x ∈ N.map q := Subgroup.mem_map_of_mem q hx
      rw [hbot, Subgroup.mem_bot, hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      exact this
    · exfalso
      have hdvd : Nat.card (↥K ⧸ Subgroup.center ↥K) ∣ Nat.card N := by
        have h1 := Subgroup.card_map_dvd (H := N) q
        rw [htop, Subgroup.card_top] at h1
        exact h1
      have h3 : 3 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) := by
        rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
          Fintype.card_fin]
        decide
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hNcop (h3.trans hdvd)
  have hNdvd : Nat.card N ∣ Nat.card (Subgroup.center ↥K) := Subgroup.card_dvd_of_le hNle
  have h6 : Nat.card N ∣ 2 * 3 := hNdvd.trans hcen
  have h2dvd : Nat.card N ∣ 2 := Nat.Coprime.dvd_of_dvd_mul_right hNcop.symm h6
  have hNp : IsPGroup 2 N := by
    rcases (Nat.dvd_prime Nat.prime_two).1 h2dvd with h1 | h2'
    · exact IsPGroup.of_card (n := 0) (by simpa using h1)
    · exact IsPGroup.of_card (n := 1) (by simpa using h2')
  have hle : N ≤ CFSG.pCore 2 ↥K := le_sSup ⟨hNnormal, hNp⟩
  rw [h2] at hle
  exact le_bot_iff.1 hle

theorem le_alphaOf_of_hatSeven (h : IvSetting m p M D L) (hp3 : p = 3)
    (hH : IsHatSeven ↥(tl M L)) : L ≤ alphaOf p M := by
  have hLM : L ≤ M := h.hL.1
  have hsn : CFSG.Open.IsSubnormal L M := h.hL.2.1
  have hH' : IsHatSeven (↥L ⧸ CFSG.pCore 2 ↥L) :=
    ga_isHatSeven_of_mulEquiv (ga_quotPCoreEquivTl hLM hsn).symm hH
  exact le_sup_of_le_right
    (le_iSup₂_of_le L ⟨hp3, hLM, hsn, glaPComponent_perfect h.hL, hH'⟩ le_rfl)

private theorem ga_pCoreOf_tl_le {R : Subgroup G} (hRM : R ≤ M) :
    pCoreOf 2 (tl M R) ≤ tl M (pCoreOf 2 R) := by
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hπ
  set T := tl M R with hT
  set Q := pCoreOf 2 T with hQ
  let f : ↥R →* Mt M := π.comp (Subgroup.inclusion hRM)
  have hQp : IsPGroup 2 ↥Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 T
  have hker : IsPGroup 2 ↥f.ker := by
    have h1 : f.ker = (CFSG.pCore 2 ↥M).comap (Subgroup.inclusion hRM) := by
      ext x
      simp [f, hπ, QuotientGroup.eq_one_iff]
    rw [h1]
    refine IsPGroup.comap_of_ker_isPGroup (CFSG.pCore_isPGroup) (Subgroup.inclusion hRM) ?_
    have : (Subgroup.inclusion hRM).ker = ⊥ := by
      rw [MonoidHom.ker_eq_bot_iff]
      exact Subgroup.inclusion_injective hRM
    rw [this]
    exact IsPGroup.of_bot
  have hY2 : IsPGroup 2 ↥(Q.comap f) := IsPGroup.comap_of_ker_isPGroup hQp f hker
  have hYnorm : (Q.comap f).Normal := by
    refine ⟨fun y hy r => ?_⟩
    have hfr : f r ∈ T := ⟨Subgroup.inclusion hRM r, r.2, rfl⟩
    have hmem := Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 T hfr) (f y)
    show f (r * y * r⁻¹) ∈ Q
    rw [map_mul, map_mul, map_inv]
    exact hmem.1 hy
  have hle : Q.comap f ≤ CFSG.pCore 2 ↥R := le_sSup ⟨hYnorm, hY2⟩
  intro q hq
  have hqT : q ∈ T := CFSG.LieType.BorelTits.pCoreOf_le 2 T hq
  obtain ⟨x, hxR, rfl⟩ := hqT
  have hxR' : (x : G) ∈ R := hxR
  have hxY : (⟨x, hxR'⟩ : ↥R) ∈ Q.comap f := hq
  have hx2 : (x : G) ∈ pCoreOf 2 R :=
    (CFSG.mem_openPCoreOf_iff (⟨x, hxR'⟩ : ↥R)).2 (hle hxY)
  exact ⟨x, (Subgroup.mem_subgroupOf).2 hx2, rfl⟩

private theorem ga_inf_centralizer_tl_le (hp : p.Prime) (hp2 : p ≠ 2) {d : G} (hdM : d ∈ M)
    (hdp : IsPGroup p (Subgroup.zpowers d)) {P : Subgroup G} (hWP : pCoreOf 2 M ≤ P)
    (hPM : P ≤ M) :
    tl M P ⊓ Subgroup.centralizer
        ({QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨d, hdM⟩} : Set (Mt M)) ≤
      tl M (P ⊓ Subgroup.centralizer ({d} : Set G)) := by
  have : Fact p.Prime := ⟨hp⟩
  rintro y ⟨⟨x, hxP, rfl⟩, hyc⟩
  have hxP' : (x : G) ∈ P := hxP
  have hyc' := Subgroup.mem_centralizer_singleton_iff.1 hyc
  have hcomm1 : ⁅(⟨d, hdM⟩ : ↥M), x⁆ ∈ CFSG.pCore 2 ↥M := by
    rw [← QuotientGroup.eq_one_iff]
    rw [show (QuotientGroup.mk ⁅(⟨d, hdM⟩ : ↥M), x⁆ : Mt M) =
        ⁅QuotientGroup.mk (⟨d, hdM⟩ : ↥M), (QuotientGroup.mk x : Mt M)⁆ from
      (map_commutatorElement (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) _ _)]
    exact commutatorElement_eq_one_iff_mul_comm.2 hyc'.symm
  have hcomm : d * (x : G) * d⁻¹ * (x : G)⁻¹ ∈ pCoreOf 2 M := ⟨_, hcomm1, rfl⟩
  have hVp : ¬ p ∣ Nat.card ↥(pCoreOf 2 M) := fun hd =>
    not_dvd_card_glaPPrimeCoreOf hp M
      (hd.trans (Subgroup.card_dvd_of_le (pCoreOf_two_le_glaPPrimeCoreOf hp hp2 M)))
  obtain ⟨v, hv, hvc⟩ := exists_mul_mem_centralizer hdp hVp
    (le_normalizer_pCoreOf 2 M hdM) (le_normalizer_pCoreOf 2 M x.2) hcomm
  have hvM : v ∈ M := CFSG.LieType.BorelTits.pCoreOf_le 2 M hv
  have hxvM : (x : G) * v ∈ M := M.mul_mem x.2 hvM
  have hxvP : (x : G) * v ∈ P := P.mul_mem hxP' (hWP hv)
  refine ⟨⟨(x : G) * v, hxvM⟩, (Subgroup.mem_subgroupOf).2 ⟨hxvP, hvc⟩, ?_⟩
  have hv2 : (⟨v, hvM⟩ : ↥M) ∈ CFSG.pCore 2 ↥M := (CFSG.mem_openPCoreOf_iff ⟨v, hvM⟩).1 hv
  have e1 : (⟨(x : G) * v, hxvM⟩ : ↥M) = x * ⟨v, hvM⟩ := rfl
  have hv1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (⟨v, hvM⟩ : ↥M) = 1 :=
    (QuotientGroup.eq_one_iff _).2 hv2
  rw [e1, map_mul, hv1, mul_one]

private theorem ga_isSubnormal_subgroupOf_of_le {K X Y : Subgroup G}
    (hsn : (K.subgroupOf X).IsSubnormal) (hYX : Y ≤ X) : (K.subgroupOf Y).IsSubnormal := by
  have h := hsn.comap (Subgroup.inclusion hYX)
  convert h using 1
  ext y
  simp [Subgroup.mem_subgroupOf]

private theorem ga_exists_preimage_tl (h : IvSetting m p M D L) :
    ∃ P : Subgroup G, P ≤ M ∧ pCoreOf 2 M ≤ P ∧ tl M P = tl M L ∧ (P.subgroupOf M).IsSubnormal ∧
      ∀ A : Subgroup G, L ≤ A → pCoreOf 2 M ≤ A → P ≤ A := by
  have hLM : L ≤ M := h.hL.1
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hπ
  let P : Subgroup G := ((tl M L).comap π).map M.subtype
  have hPsub : P.subgroupOf M = (tl M L).comap π :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
  refine ⟨P, Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    refine ⟨w, ?_, rfl⟩
    show π w ∈ tl M L
    have hw1 : π w = 1 := (QuotientGroup.eq_one_iff w).2 hw
    rw [hw1]
    exact (tl M L).one_mem
  · show (P.subgroupOf M).map π = tl M L
    rw [hPsub, Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  · rw [hPsub]
    exact ((CFSG.Open.IsSubnormal.top_iff).1 (isSubnormal_tl hLM h.hL.2.1)).comap π
  · intro A hLA hWA x hx
    obtain ⟨w, hw, rfl⟩ := hx
    obtain ⟨ℓ, hℓ, hℓw⟩ := hw
    have hker : ℓ⁻¹ * w ∈ CFSG.pCore 2 ↥M := (QuotientGroup.eq).1 hℓw
    have h1 : ((ℓ⁻¹ * w : ↥M) : G) ∈ pCoreOf 2 M := ⟨_, hker, rfl⟩
    have h2 : (ℓ : G) ∈ L := hℓ
    have h3 : (ℓ : G) * ((ℓ⁻¹ * w : ↥M) : G) ∈ A := A.mul_mem (hLA h2) (hWA h1)
    simpa using h3

private theorem ga_rootOf_le_Hfam (h : IvSetting m p M D L) (hLα : L ≤ alphaOf p M) {d : G}
    (hdD : d ∈ D) (hd1 : d ≠ 1) (hdM : d ∈ M) :
    rootOf (tl M L) (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨d, hdM⟩) ≤
      Hfam M D (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨d, hdM⟩) := by
  have hp : p.Prime := prime_of_standing h.standing
  have hp2 : p ≠ 2 := ne_two_of_standing h.standing
  obtain ⟨P, hPM, hWP, htl, hPsn, hPmin⟩ := ga_exists_preimage_tl h
  set C := Subgroup.centralizer ({d} : Set G) with hC
  set α := alphaOf p M with hα
  have hαM : α ≤ M := alphaOf_le p M
  have hWα : pCoreOf 2 M ≤ α := le_sup_left
  have hPα : P ≤ α := hPmin α hLα hWα
  have hdp : IsPGroup p (Subgroup.zpowers d) :=
    (isPGroup_of_isElemAbelian' h.hyp.plane.1).to_le (Subgroup.zpowers_le.2 hdD)
  set R := P ⊓ C with hR
  have hRM : R ≤ M := inf_le_left.trans hPM
  have hlift : tl M L ⊓ Subgroup.centralizer
      ({QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨d, hdM⟩} : Set (Mt M)) = tl M R := by
    refine le_antisymm ?_ ?_
    · rw [← htl]
      exact ga_inf_centralizer_tl_le hp hp2 hdM hdp hWP hPM
    · refine le_inf ((tl_mono' (inf_le_left : P ⊓ C ≤ P)).trans htl.le) ?_
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨-, hxd⟩ := (Subgroup.mem_subgroupOf).1 hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : (x : G) * d = d * x := Subgroup.mem_centralizer_singleton_iff.1 hxd
      have h2 : x * (⟨d, hdM⟩ : ↥M) = ⟨d, hdM⟩ * x := Subtype.ext h1
      rw [← map_mul, ← map_mul, h2]
  have h1 : rootOf (tl M L) (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨d, hdM⟩) ≤
      tl M (pCoreOf 2 R) := by
    unfold rootOf
    rw [hlift]
    exact ga_pCoreOf_tl_le hRM
  have h2 : pCoreOf 2 R ≤ pCoreOf 2 C := by
    have hRle : R ≤ α ⊓ C := inf_le_inf_right C hPα
    have hsnα : CFSG.Open.IsSubnormal R (α ⊓ C) := by
      refine (CFSG.Open.IsSubnormal.iff_subgroupOf hRle).2 ?_
      have h3 := ga_isSubnormal_subgroupOf_of_le hPsn ((inf_le_left : α ⊓ C ≤ α).trans hαM)
      convert h3 using 1
      ext y
      simp only [Subgroup.mem_subgroupOf, hR, Subgroup.mem_inf]
      exact ⟨fun hy => hy.1, fun hy => ⟨hy, (Subgroup.mem_inf.1 y.2).2⟩⟩
    exact (pCoreOf_le_of_isSubnormal 2 hsnα).trans (h.hyp.clause_b d hdD hd1)
  refine h1.trans ((tl_mono' h2).trans ?_)
  unfold Hfam
  exact le_iSup_of_le d (le_iSup_of_le hdM (le_iSup_of_le hdD (le_iSup_of_le rfl le_rfl)))

private theorem ga_mem_normalizer_tl_pCoreOf {c d : G} (hcM : c ∈ M)
    (hc : c ∈ Subgroup.centralizer ({d} : Set G)) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨c, hcM⟩ ∈
      Subgroup.normalizer
        ((tl M (pCoreOf 2 (Subgroup.centralizer ({d} : Set G))) : Subgroup (Mt M)) :
          Set (Mt M)) := by
  have h1 : (⟨c, hcM⟩ : ↥M) ∈ Subgroup.normalizer
      (((pCoreOf 2 (Subgroup.centralizer ({d} : Set G))).subgroupOf M : Subgroup ↥M) : Set ↥M) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 _ hc) (y : G)
  exact Subgroup.le_normalizer_map (QuotientGroup.mk' (CFSG.pCore 2 ↥M))
    (Subgroup.mem_map_of_mem _ h1)

private theorem ga_cinv_hfam (h : IvSetting m p M D L) :
    SignalizerFamily.CInvariant (tl M D) (Hfam M D) := by
  intro dt hdt hdt1 ct hct
  obtain ⟨⟨d, hdM⟩, hdD', rfl⟩ := hdt
  have hdD : d ∈ D := hdD'
  unfold Hfam
  refine ga_mem_normalizer_iSup fun d' => ga_mem_normalizer_iSup fun hdM' =>
    ga_mem_normalizer_iSup fun hdD'' => ga_mem_normalizer_iSup fun hπ => ?_
  rw [← hπ, ← tl_centralizer_eq h hdD'' hdM'] at hct
  obtain ⟨c, hc, rfl⟩ := hct
  exact ga_mem_normalizer_tl_pCoreOf c.2 ((Subgroup.mem_subgroupOf).1 hc)

theorem gamma7Data_tl (hM : AltSixSevenCentre) (h : IvSetting m p M D L) (hp3 : p = 3)
    (hA7 : Nonempty ((↥(tl M L) ⧸ Subgroup.center ↥(tl M L)) ≃* alternatingGroup (Fin 7))) :
    Gamma7Data (tl M L) (tl M D) (Hfam M D) := by
  have hcomp : IsComponentOf (tl M L) ⊤ :=
    isComponentOf_tl (prime_of_standing h.standing) (ne_two_of_standing h.standing) h.hyp h.hL
      h.hn h.hnc h.hQ
  refine ⟨hcomp, tl_glaPPrimeCore_three_eq_bot hM h hp3 hA7, hp3 ▸ hfam_family h,
    ga_cinv_hfam h, ?_⟩
  intro hHat dt hdt hdt1 _
  have hLα := le_alphaOf_of_hatSeven h hp3 hHat
  obtain ⟨⟨d, hdM⟩, hdD', rfl⟩ := hdt
  have hd1 : d ≠ 1 := by
    rintro rfl
    exact hdt1 (by rw [show (⟨1, hdM⟩ : ↥M) = 1 from rfl, map_one])
  exact ga_rootOf_le_Hfam h hLα hdD' hd1 hdM

private theorem ga_mem_normalizer_of_tl (h : IvSetting m p M D L) {g : G} (hgM : g ∈ M)
    (hg : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g, hgM⟩ ∈
      Subgroup.normalizer ((tl M L : Subgroup (Mt M)) : Set (Mt M))) :
    g ∈ Subgroup.normalizer (L : Set G) := by
  have hp : p.Prime := prime_of_standing h.standing
  refine mem_normalizer_of_barX_normalizes hp le_rfl h.hL hgM (Subgroup.le_normalizer hgM) ?_
  have h1 := Subgroup.le_normalizer_map
    (projQ p M (pCore_two_le_glaPPrimeCore h.standing.beta.1 h.standing.beta.2.1 M))
    (Subgroup.mem_map_of_mem _ hg)
  rw [map_projQ_tl h L] at h1
  exact h1

private theorem ga_actsLikeCQ_of_le_sup {Y : Type} [Group Y] (A W R : Subgroup Y)
    (e : (↥A ⧸ Subgroup.center ↥A) ≃* ↥(alternatingGroup (Fin 7)))
    (hRA : R ≤ A) (hWN : W ≤ Subgroup.normalizer (A : Set Y)) (hRW : R ≤ W)
    (hWle : W ≤ R ⊔ Subgroup.centralizer (A : Set Y)) :
    ActsLikeCQ W A e ((imgA7 A R e).map (MulAut.conj : ↥(alternatingGroup (Fin 7)) →* _)) := by
  have key : ∀ w ∈ R ⊔ Subgroup.centralizer (A : Set Y),
      ∃ r ∈ R, ∀ a ∈ A, w * a * w⁻¹ = r * a * r⁻¹ := by
    let T : Subgroup Y :=
      { carrier := {w | ∃ r ∈ R, ∀ a ∈ A, w * a * w⁻¹ = r * a * r⁻¹}
        mul_mem' := by
          rintro w₁ w₂ ⟨r₁, hr₁, h₁⟩ ⟨r₂, hr₂, h₂⟩
          refine ⟨r₁ * r₂, R.mul_mem hr₁ hr₂, fun a ha => ?_⟩
          have h2 : r₂ * a * r₂⁻¹ ∈ A :=
            A.mul_mem (A.mul_mem (hRA hr₂) ha) (A.inv_mem (hRA hr₂))
          calc w₁ * w₂ * a * (w₁ * w₂)⁻¹ = w₁ * (w₂ * a * w₂⁻¹) * w₁⁻¹ := by group
            _ = w₁ * (r₂ * a * r₂⁻¹) * w₁⁻¹ := by rw [h₂ a ha]
            _ = r₁ * (r₂ * a * r₂⁻¹) * r₁⁻¹ := h₁ _ h2
            _ = (r₁ * r₂) * a * (r₁ * r₂)⁻¹ := by group
        one_mem' := ⟨1, R.one_mem, fun a _ => by simp⟩
        inv_mem' := by
          rintro w ⟨r, hr, h1⟩
          refine ⟨r⁻¹, R.inv_mem hr, fun a ha => ?_⟩
          have h2 : r⁻¹ * a * r ∈ A := A.mul_mem (A.mul_mem (A.inv_mem (hRA hr)) ha) (hRA hr)
          have h4 : w * (r⁻¹ * a * r) * w⁻¹ = a := by rw [h1 _ h2]; group
          calc w⁻¹ * a * w⁻¹⁻¹ = w⁻¹ * (w * (r⁻¹ * a * r) * w⁻¹) * w := by rw [h4]; simp
            _ = r⁻¹ * a * r := by group
            _ = r⁻¹ * a * r⁻¹⁻¹ := by simp }
    have hRT : R ≤ T := fun r hr => ⟨r, hr, fun a _ => rfl⟩
    have hCT : Subgroup.centralizer (A : Set Y) ≤ T := by
      intro c hc
      refine ⟨1, R.one_mem, fun a ha => ?_⟩
      have := Subgroup.mem_centralizer_iff.1 hc a ha
      calc c * a * c⁻¹ = (a * c) * c⁻¹ := by rw [this]
        _ = 1 * a * 1⁻¹ := by group
    exact fun w hw => (sup_le hRT hCT) hw
  have hind : ∀ (r : Y) (hr : r ∈ A) (n : ↥(Subgroup.normalizer (A : Set Y))),
      (∀ a ∈ A, (n : Y) * a * (n : Y)⁻¹ = r * a * r⁻¹) →
      InducesOn e (A.normalizerMonoidHom n)
        (MulAut.conj (e (QuotientGroup.mk (⟨r, hr⟩ : ↥A)))) := by
    intro r hr n hn
    unfold InducesOn
    intro a
    have h1 : A.normalizerMonoidHom n a = (⟨r, hr⟩ : ↥A) * a * (⟨r, hr⟩ : ↥A)⁻¹ :=
      Subtype.ext (by
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
        simpa using hn a a.2)
    rw [h1]
    simp [MulAut.conj_apply]
  constructor
  · intro φ hφ
    obtain ⟨n, hn, rfl⟩ := hφ
    obtain ⟨r, hr, hra⟩ := key n.1 (hWle hn)
    refine ⟨MulAut.conj (e (QuotientGroup.mk (⟨r, hRA hr⟩ : ↥A))), ⟨_, ?_, rfl⟩,
      hind r (hRA hr) n hra⟩
    exact ⟨_, ⟨⟨r, hRA hr⟩, (Subgroup.mem_subgroupOf).2 hr, rfl⟩, rfl⟩
  · intro σ hσ
    obtain ⟨v, hv, rfl⟩ := hσ
    obtain ⟨_, ⟨r', hr', rfl⟩, rfl⟩ := hv
    have hr'R : (r' : Y) ∈ R := hr'
    refine ⟨A.normalizerMonoidHom ⟨(r' : Y), Subgroup.le_normalizer r'.2⟩,
      ⟨⟨(r' : Y), Subgroup.le_normalizer r'.2⟩, (Subgroup.mem_subgroupOf).2 (hRW hr'R), rfl⟩, ?_⟩
    exact hind (r' : Y) r'.2 ⟨(r' : Y), Subgroup.le_normalizer r'.2⟩ (fun a _ => rfl)

theorem hyp28Three_sigma (hAC : AltNotChevTwo) (h : IvSetting m p M D L)
    (e : (↥(tl M L) ⧸ Subgroup.center ↥(tl M L)) ≃* ↥(alternatingGroup (Fin 7)))
    (hG : Gamma7Concl (tl M L) e (tl M D) (Hfam M D)) :
    Hyp28Three (CFSG.pCore 2 ↥M) (L.subgroupOf M) ((sigmaOf D).subgroupOf M) ∧
      (sigmaOf D).subgroupOf M ≤ Subgroup.normalizer ((L.subgroupOf M : Subgroup ↥M) : Set ↥M) ∧
      Nat.card ↥(bar (CFSG.pCore 2 ↥M) ((sigmaOf D).subgroupOf M) ⊓
        bar (CFSG.pCore 2 ↥M) (L.subgroupOf M)) = 4 := by
  obtain ⟨hN, R, hRK, hRroot, hRint, hRle⟩ := hG
  have hp : p.Prime := prime_of_standing h.standing
  have hp2 : p ≠ 2 := ne_two_of_standing h.standing
  have hcomp : IsComponentOf (tl M L) ⊤ := isComponentOf_tl hp hp2 h.hyp h.hL h.hn h.hnc h.hQ
  have hSig : tl M (sigmaOf D) = pCoreOf 2 (sigmaFam (tl M D) (Hfam M D)) := tl_sigmaOf_eq h
  set S := pCoreOf 2 (sigmaFam (tl M D) (Hfam M D)) with hS
  have hSsig : S ≤ sigmaFam (tl M D) (Hfam M D) := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hSN : S ≤ Subgroup.normalizer ((tl M L : Subgroup (Mt M)) : Set (Mt M)) := hSsig.trans hN
  have hRS : R ≤ S := hRint ▸ inf_le_left
  have hnormL : (sigmaOf D).subgroupOf M ≤
      Subgroup.normalizer ((L.subgroupOf M : Subgroup ↥M) : Set ↥M) := by
    intro s hs
    have hs' : (QuotientGroup.mk' (CFSG.pCore 2 ↥M) s : Mt M) ∈ tl M (sigmaOf D) := ⟨s, hs, rfl⟩
    rw [hSig] at hs'
    have hsL := ga_mem_normalizer_of_tl h s.2 (hSN hs')
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.1 hsL (y : G)
  have hRZ : (R.subgroupOf (tl M L)) ⊓ Subgroup.center ↥(tl M L) = ⊥ := by
    have hR2 : IsPGroup 2 ↥R :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (sigmaFam (tl M D) (Hfam M D))).to_le hRS
    have hR2' : IsPGroup 2 ↥(R.subgroupOf (tl M L)) :=
      hR2.of_equiv (Subgroup.subgroupOfEquivOfLe hRK).symm
    have hI2 : IsPGroup 2 ↥((R.subgroupOf (tl M L)) ⊓ Subgroup.center ↥(tl M L)) :=
      hR2'.to_inf_left
    have hInorm : ((R.subgroupOf (tl M L)) ⊓ Subgroup.center ↥(tl M L)).Normal :=
      Subgroup.normal_of_le_center inf_le_right
    have hle : ((R.subgroupOf (tl M L)) ⊓ Subgroup.center ↥(tl M L)) ≤
        CFSG.pCore 2 ↥(tl M L) := le_sSup ⟨hInorm, hI2⟩
    rw [pCore_tl_eq_bot h] at hle
    exact le_bot_iff.1 hle
  have hcardR : Nat.card ↥R = 4 := by
    have hroot' := hRroot.1
    unfold imgA7 at hroot'
    rw [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective] at hroot'
    have hinj : Function.Injective
        ((QuotientGroup.mk' (Subgroup.center ↥(tl M L))).comp (R.subgroupOf (tl M L)).subtype) := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have hx1 : (QuotientGroup.mk' (Subgroup.center ↥(tl M L))) (x : ↥(tl M L)) = 1 := hx
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx1
      have hmem : (x : ↥(tl M L)) ∈ (R.subgroupOf (tl M L)) ⊓ Subgroup.center ↥(tl M L) :=
        ⟨x.2, hx1⟩
      rw [hRZ, Subgroup.mem_bot] at hmem
      exact Subtype.ext hmem
    have hrange : ((QuotientGroup.mk' (Subgroup.center ↥(tl M L))).comp
        (R.subgroupOf (tl M L)).subtype).range =
        (R.subgroupOf (tl M L)).map (QuotientGroup.mk' (Subgroup.center ↥(tl M L))) := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have hc1 : Nat.card ↥((R.subgroupOf (tl M L)).map
        (QuotientGroup.mk' (Subgroup.center ↥(tl M L)))) = Nat.card ↥(R.subgroupOf (tl M L)) := by
      rw [← hrange]
      exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    rw [hc1] at hroot'
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRK).toEquiv).symm.trans hroot'
  refine ⟨⟨⟨ga_isQuasisimple_of_open hcomp.2.2, 7, by norm_num, ⟨e⟩⟩, ?_, 7, e,
    imgA7 (tl M L) R e, imgA7 (tl M L) R e, hRroot, le_rfl, ?_⟩, hnormL, ?_⟩
  · rintro ⟨-, hCh⟩
    exact hAC 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.isChevTwo_of_mulEquiv e hCh)
  · show ActsLikeCQ (tl M (sigmaOf D)) (tl M L) e _
    rw [hSig]
    exact ga_actsLikeCQ_of_le_sup (tl M L) S R e hRK hSN hRS hRle
  · show Nat.card ↥(tl M (sigmaOf D) ⊓ tl M L) = 4
    rw [hSig, hRint]
    exact hcardR

theorem card_subgroupOf_eq {U : Subgroup G} (hUM : U ≤ M) : Nat.card ↥(U.subgroupOf M) = Nat.card ↥U :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv

theorem center_eq_bot_of_equiv_alt7 {Y : Type*} [Group Y] (e : Y ≃* ↥(alternatingGroup (Fin 7))) :
    Subgroup.center Y = ⊥ := by
  have hsimple : IsSimpleGroup ↥(alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hc : Subgroup.center ↥(alternatingGroup (Fin 7)) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center ↥(alternatingGroup (Fin 7))) with h | h
    · exact h
    · exfalso
      let u : alternatingGroup (Fin 7) := ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by
        rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
          Equiv.Perm.sign_swap (by decide)]
        rfl⟩
      let v : alternatingGroup (Fin 7) := ⟨Equiv.swap 0 1 * Equiv.swap 1 3, by
        rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
          Equiv.Perm.sign_swap (by decide)]
        rfl⟩
      have hu : u ∈ Subgroup.center (alternatingGroup (Fin 7)) := h ▸ Subgroup.mem_top u
      have huv : v * u = u * v := Subgroup.mem_center_iff.mp hu v
      have hne : (v * u : alternatingGroup (Fin 7)) ≠ u * v := by
        intro heq
        have := congrArg (fun g : alternatingGroup (Fin 7) => (g : Equiv.Perm (Fin 7)) 0) heq
        revert this
        decide
      exact hne huv
  have hcen : (Subgroup.center Y).map e.toMonoidHom = Subgroup.center ↥(alternatingGroup (Fin 7)) :=
    Subgroup.map_center_eq e
  rw [hc] at hcen
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 hcen

theorem gamma_action (h : IvSetting m p M D L) (hψ : Function.Bijective (psiL h))
    (hZ : Subgroup.center ↥(tl M L) = ⊥)
    (e : (↥(tl M L) ⧸ Subgroup.center ↥(tl M L)) ≃* ↥(alternatingGroup (Fin 7)))
    (hR : ActsLikeRootFourCQ (tl M (gammaD D)) (tl M L) 7 e) :
    ∃ e_bar : ↥(barX p M L) ≃* ↥(alternatingGroup (Fin 7)),
      Nat.card (inducedAutGroup (barX p M (gammaD D)) (barX p M L)) = 4 ∧
        ActsLikeRootFourGroup (barX p M (gammaD D)) (barX p M L) e_bar := by
  obtain ⟨V, hV, hact⟩ := hR
  have hp : p.Prime := prime_of_standing h.standing
  have hp2 : p ≠ 2 := ne_two_of_standing h.standing
  have hcomp : IsComponentOf (tl M L) ⊤ := isComponentOf_tl hp hp2 h.hyp h.hL h.hn h.hnc h.hQ
  have hperf : commutator ↥(tl M L) = ⊤ := hcomp.2.2.1
  let eL : ↥(tl M L) ≃* ↥(alternatingGroup (Fin 7)) :=
    ((QuotientGroup.quotientBot (G := ↥(tl M L))).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans e
  have hcomp' : ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      ((QuotientGroup.quotientBot).trans eL)) = e := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H x => simp [eL]
  let e_bar : ↥(barX p M L) ≃* ↥(alternatingGroup (Fin 7)) :=
    (MulEquiv.ofBijective (psiL h) hψ).symm.trans eL
  have hWM : gammaD D ≤ M := gammaD_le h.hyp
  have hWN : gammaD D ≤ Subgroup.normalizer (L : Set G) :=
    gammaD_le_normalizer hp h.hyp h.hL h.hn
  have h1 : ActsLike (tl M (gammaD D)) (tl M L) eL
      (V.map (MulAut.conj : ↥(alternatingGroup (Fin 7)) →* _)) := by
    rw [actsLike_iff_actsLikeCQ (tl M (gammaD D)) (tl M L) hZ eL, hcomp']
    exact hact
  have h2 : ActsLike (barX p M (gammaD D)) (barX p M L) e_bar
      (V.map (MulAut.conj : ↥(alternatingGroup (Fin 7)) →* _)) := by
    rw [actsLike_tl_iff_bar h hψ e_bar _ hWM hWN]
    have : (MulEquiv.ofBijective (psiL h) hψ).trans e_bar = eL :=
      MulEquiv.ext fun x => by
        show eL ((MulEquiv.ofBijective (psiL h) hψ).symm ((MulEquiv.ofBijective (psiL h) hψ) x)) =
          eL x
        rw [MulEquiv.symm_apply_apply]
    rw [this]
    exact h1
  have hcard1 := card_induced_of_actsLikeCQ (tl M (gammaD D)) (tl M L) hperf e _ hact
  have hconj_inj : Function.Injective
      (MulAut.conj : ↥(alternatingGroup (Fin 7)) →* MulAut ↥(alternatingGroup (Fin 7))) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgc : g ∈ Subgroup.center ↥(alternatingGroup (Fin 7)) := by
      rw [Subgroup.mem_center_iff]
      intro x
      have := congrArg (fun φ => φ x) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc x * g = (g * x * g⁻¹) * g := by rw [this]
        _ = g * x := by group
    have hc0 : Subgroup.center ↥(alternatingGroup (Fin 7)) = ⊥ :=
      center_eq_bot_of_equiv_alt7 (MulEquiv.refl _)
    rw [hc0, Subgroup.mem_bot] at hgc
    exact hgc
  have hcardV : Nat.card (V.map (MulAut.conj : ↥(alternatingGroup (Fin 7)) →* _)) = 4 := by
    rw [Subgroup.card_map_of_injective hconj_inj]
    exact hV.1
  have hfix : Nat.card {i : Fin 7 // ∀ v ∈ V, (v : Equiv.Perm (Fin 7)) i = i} = 3 := by
    classical
    have hsum := Nat.card_congr
      (Equiv.sumCompl (fun i : Fin 7 => ∀ v ∈ V, (v : Equiv.Perm (Fin 7)) i = i))
    rw [Nat.card_sum] at hsum
    have h4 := hV.2.2
    have h7 : Nat.card (Fin 7) = 7 := by simp
    omega
  refine ⟨e_bar, ?_, V, hV.1, hV.2.1, hfix, h2⟩
  rw [← card_inducedAutGroup_tl_eq_bar h hWM hWN, hcard1, hcardV]

end Setting

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
