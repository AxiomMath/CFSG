module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsL35ESporFact
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxH35M12
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxH35J2
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxH35HS
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35Triv
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36Spor
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5CovFix
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesB
public import CFSG.LocalAnalysis.SteinbergCCHSMultiplier

public section

namespace CFSG.ComponentClassification.SolMax.H35

open CFSG Subgroup CFSG.Blueprint GrSLit.L34Facts
open CFSG.ComponentClassification.HarrisLit CFSG.ComponentClassification.HarrisLit.L35
open CFSG.ComponentClassification.GSThmB

variable {G : Type} [Group G] [Finite G] {p : ℕ} {w v : G} {L K : Subgroup G}

abbrev tildeOf (K L : Subgroup G) : Subgroup (↥K ⧸ pPrimeCore 2 ↥K) :=
  (L.subgroupOf K).map (QuotientGroup.mk' (pPrimeCore 2 ↥K))

@[expose] noncomputable def tildeHom (h : Config G p w v L K) : ↥L →* ↥(tildeOf K L) where
  toFun x := ⟨QuotientGroup.mk (⟨x, h.L_le x.2⟩ : ↥K), ⟨⟨x, h.L_le x.2⟩, x.2, rfl⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem tildeHom_surjective (h : Config G p w v L K) : Function.Surjective (tildeHom h) := by
  rintro ⟨_, ⟨k, hk, rfl⟩⟩
  exact ⟨⟨k, hk⟩, rfl⟩

theorem tilde_perfect (h : Config G p w v L K) : ⁅tildeOf K L, tildeOf K L⁆ = tildeOf K L := by
  have hLp : Group.IsPerfect ↥L := h.compL.2.2.1
  have : Group.IsPerfect ↥(tildeOf K L) :=
    Group.IsPerfect.ofSurjective (f := tildeHom h) (tildeHom_surjective h)
  exact Subgroup.commutator_eq_self

theorem wbar_mem_tildeOf (h : Config G p w v L K) : h.wbar ∈ tildeOf K L :=
  ⟨⟨w, h.w_mem_K⟩, h.w_mem_L, rfl⟩

theorem tau_fix (h : Config G p w v L K) : ∀ y ∈ tildeOf K L, h.tau y = y := by
  rintro _ ⟨k, hk, rfl⟩
  change oddAut h.beta (QuotientGroup.mk k) = QuotientGroup.mk k
  rw [oddAut_mk]
  congr 1
  exact h.mem_fixedPoints_beta.mpr (h.compL.1 (mem_subgroupOf.mp hk)).2

theorem tau_mul_self (h : Config G p w v L K) : h.tau * h.tau = 1 :=
  MulEquiv.ext fun y => h.tau_tau y

theorem odd_orderOf_of_mem_pPrimeCore {X : Type*} [Group X] [Finite X] {x : X}
    (hx : x ∈ pPrimeCore 2 X) : Odd (orderOf x) := by
  have hd := Subgroup.orderOf_dvd_natCard _ hx
  exact Nat.coprime_two_left.mp (Nat.Coprime.coprime_dvd_right hd pPrimeCore_coprime_card)

theorem tilde_uniq (h : Config G p w v L K) :
    ∀ y ∈ tildeOf K L, y * y = 1 → y = 1 ∨ y = h.wbar := by
  intro y hy hyy
  obtain ⟨k, -, -, F, _, _, hF, ⟨eF⟩⟩ := h.slTwo
  have h2 : (2 : F) ≠ 0 := by
    have hodd : Fintype.card F % 2 = 1 := by
      rw [hF]
      exact Nat.odd_iff.mp (h.prime.odd_of_ne_two h.ne_two).pow
    have hchar : ringChar F ≠ 2 := fun hc => by
      rw [FiniteField.even_card_iff_char_two.mp hc] at hodd
      exact absurd hodd (by norm_num)
    exact Ring.two_ne_zero hchar
  have hker : ∀ x ∈ (tildeHom h).ker, Odd (orderOf x) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : (QuotientGroup.mk (⟨x, h.L_le x.2⟩ : ↥K) : ↥K ⧸ pPrimeCore 2 ↥K) = 1 :=
      congrArg Subtype.val hx
    rw [QuotientGroup.eq_one_iff] at h1
    have h3 := odd_orderOf_of_mem_pPrimeCore h1
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe] at h3
    exact h3
  have hw : orderOf (⟨w, h.w_mem_L⟩ : ↥L) = 2 := by rw [Subgroup.orderOf_mk, h.orderOf_w]
  have hwc : ∀ z : ↥(tildeOf K L), tildeHom h ⟨w, h.w_mem_L⟩ * z = z * tildeHom h ⟨w, h.w_mem_L⟩ :=
    fun z => Subtype.ext ((mem_center_iff.mp h.wbar_mem_center z).symm)
  rcases eq_one_or_eq_of_sl2 (tildeHom h) (tildeHom_surjective h) hker (pPrimeCore 2 ↥L)
      (fun x hx => odd_orderOf_of_mem_pPrimeCore hx) h2 eF hw hwc (y := ⟨y, hy⟩)
      (Subtype.ext hyy) with h1 | h1
  · exact Or.inl (congrArg Subtype.val h1)
  · exact Or.inr (congrArg Subtype.val h1)

theorem center_eq_zpowers (h : Config G p w v L K)
    (hc : Nat.card (center (↥K ⧸ pPrimeCore 2 ↥K)) ≤ 2) :
    center (↥K ⧸ pPrimeCore 2 ↥K) = zpowers h.wbar :=
  (Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr h.wbar_mem_center)
    (by rw [Nat.card_zpowers, h.orderOf_wbar]; exact hc)).symm

theorem comp_data (h : Config G p w v L K) {s : TauCeti.SporadicName}
    (hodd : CatalogueU.SporadicOddCoreFree s)
    (e : (↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K) ≃* NativeSporadic.Carrier s)
    {X : Type} [Group X] (eX : (↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K) ≃* X) :
    CFSG.Assembly.IsComponentOf ((tildeOf K L).map
        (eX.toMonoidHom.comp (QuotientGroup.mk' (center (↥K ⧸ pPrimeCore 2 ↥K)))))
      (Sporadic.Schreier.fixSub ((eX.symm.trans (quotAut h.tau)).trans eX)) ∧
    Cov.SmallQ (↥((tildeOf K L).map
        (eX.toMonoidHom.comp (QuotientGroup.mk' (center (↥K ⧸ pPrimeCore 2 ↥K))))) ⧸
      center ↥((tildeOf K L).map
        (eX.toMonoidHom.comp (QuotientGroup.mk' (center (↥K ⧸ pPrimeCore 2 ↥K)))))) := by
  have hq := h.quasisimple_quot
  have hS : IsSimpleGroup ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K)) := hq.2.1
  have hna := hq.2.2
  have hsq : quotAut h.tau * quotAut h.tau = 1 := by
    ext y
    exact h.quotAut_tau_sq y
  have hσ2 : orderOf (quotAut h.tau) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hsq) h.quotAut_tau_ne_one
  have hO := N36.pPrimeCore_fixedPoints_eq_bot_of_mulAut hna
    (fun i hi => N36.mulAut_oddCore_eq_bot hodd hna e i hi) hσ2
  obtain ⟨hB, k, hk, hs5, hL⟩ := h.isComponent_hat hO
  have hle : hatOf K L ≤ fixedPoints (quotAut h.tau) := (h.isTwoComponentIn_hat h.compLK).1
  have hM0 : CFSG.Assembly.IsComponentOf (hatOf K L)
      (Sporadic.Schreier.fixSub (quotAut h.tau)) := by
    rw [Hin.fixSub_eq_fixedPoints]
    exact (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hle).2 hB
  have hmap : (hatOf K L).map eX.toMonoidHom = (tildeOf K L).map
      (eX.toMonoidHom.comp (QuotientGroup.mk' (center (↥K ⧸ pPrimeCore 2 ↥K)))) := by
    rw [hatOf, Subgroup.map_map]
  refine ⟨hmap ▸ Cov.isComponentOf_fixSub_map eX (quotAut h.tau) hM0, Or.inl ⟨p, k, h.prime,
    h.ne_two, hk, hs5, ?_⟩⟩
  have e1 : ↥((hatOf K L).subgroupOf (fixedPoints (quotAut h.tau))) ≃* ↥((tildeOf K L).map
      (eX.toMonoidHom.comp (QuotientGroup.mk' (center (↥K ⧸ pPrimeCore 2 ↥K))))) :=
    ((subgroupOfEquivOfLe hle).trans ((hatOf K L).equivMapOfInjective _ eX.injective)).trans
      (MulEquiv.subgroupCongr hmap)
  exact OddQuot.lieModel_of_equiv (CovHS.quotCenterEquiv e1) hL

theorem harris81Lemma35IdentSporFact_holds :
    HarrisLit.Harris81Lemma35IdentSporFact := by
  intro G _ _ p w v L K h _ hS
  exfalso
  obtain ⟨eZ⟩ := h.nonempty_bar_equiv
  have hq := h.quasisimple_quot
  have hLq : CFSG.Assembly.IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K) :=
    (ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2 hq
  have hZ2 := N36.center_isPGroup (G := ↥K ⧸ pPrimeCore 2 ↥K)
    (pPrimeCore_quotient_pPrimeCore_eq_bot 2)
  have hα := tau_mul_self h
  have hLt := tilde_perfect h
  have htL := wbar_mem_tildeOf h
  have hfix := tau_fix h
  have huniq := tilde_uniq h
  have hπ : ∀ {X : Type} [Group X]
      (eX : (↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K) ≃* X),
      Function.Surjective
        (eX.toMonoidHom.comp (QuotientGroup.mk' (center (↥K ⧸ pPrimeCore 2 ↥K)))) :=
    fun eX => eX.surjective.comp (QuotientGroup.mk'_surjective _)
  have hβ : ∀ {X : Type} [Group X]
      (eX : (↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K) ≃* X)
      (y : ↥K ⧸ pPrimeCore 2 ↥K),
      (eX.toMonoidHom.comp (QuotientGroup.mk' (center (↥K ⧸ pPrimeCore 2 ↥K)))) (h.tau y) =
        ((eX.symm.trans (quotAut h.tau)).trans eX)
          ((eX.toMonoidHom.comp (QuotientGroup.mk' (center (↥K ⧸ pPrimeCore 2 ↥K)))) y) := by
    intro X _ eX y
    change eX (QuotientGroup.mk (h.tau y)) =
      eX (quotAut h.tau (eX.symm (eX (QuotientGroup.mk y))))
    rw [MulEquiv.symm_apply_apply, quotAut_mk]
  have hker : center (↥K ⧸ pPrimeCore 2 ↥K) = zpowers h.wbar →
      ∀ {X : Type} [Group X]
      (eX : (↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K) ≃* X),
      (eX.toMonoidHom.comp (QuotientGroup.mk' (center (↥K ⧸ pPrimeCore 2 ↥K)))).ker =
        zpowers h.wbar := by
    intro hZ X _ eX
    rw [MonoidHom.ker_comp_of_injective _ _ eX.injective, QuotientGroup.ker_mk', hZ]
  rcases hS with hS1 | hS2 | hS3
  ·
    obtain ⟨e⟩ : Nonempty (↥K ⧸ Open.fusionZStar ↥K ≃* NativeSporadic.M12) := hS1
    have eX : (↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K) ≃* NativeSporadic.M12 :=
      eZ.symm.trans e
    have hc : Nat.card (center (↥K ⧸ pPrimeCore 2 ↥K)) ≤ 2 :=
      StandardRecognition.m12J2CentralTwoGroupOrderBound _ hLq hZ2 (Or.inl ⟨eX⟩)
    have hZ := center_eq_zpowers h hc
    obtain ⟨hM, hMt⟩ := comp_data h CatalogueU.sporadicOddCoreFree_M12 eX eX
    exact M12.false_of_fixed hLq h.orderOf_wbar hZ
      (eX.toMonoidHom.comp (QuotientGroup.mk' (center (↥K ⧸ pPrimeCore 2 ↥K)))) (hπ eX)
      (hker hZ eX) h.tau hα ((eX.symm.trans (quotAut h.tau)).trans eX) (hβ eX)
      hLt htL hfix huniq hM hMt
  ·
    obtain ⟨e⟩ : Nonempty (↥K ⧸ Open.fusionZStar ↥K ≃* NativeSporadic.Carrier .J2) := hS2
    have eX : (↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K) ≃*
        NativeSporadic.Carrier .J2 := eZ.symm.trans e
    have hc : Nat.card (center (↥K ⧸ pPrimeCore 2 ↥K)) ≤ 2 :=
      StandardRecognition.m12J2CentralTwoGroupOrderBound _ hLq hZ2 (Or.inr ⟨eX⟩)
    have hZ := center_eq_zpowers h hc
    obtain ⟨hM, hMt⟩ := comp_data h CatalogueU.sporadicOddCoreFree_J2 eX eX
    exact J2.false_of_fixed hLq h.orderOf_wbar hZ
      (eX.toMonoidHom.comp (QuotientGroup.mk' (center (↥K ⧸ pPrimeCore 2 ↥K)))) (hπ eX)
      (hker hZ eX) h.tau hα ((eX.symm.trans (quotAut h.tau)).trans eX) (hβ eX)
      hLt htL hfix huniq hM hMt
  ·
    obtain ⟨e⟩ : Nonempty (↥K ⧸ Open.fusionZStar ↥K ≃* NativeSporadic.Carrier .HS) := hS3
    have eN : (↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K) ≃*
        NativeSporadic.Carrier .HS := eZ.symm.trans e
    have hM2 : Nat.card (RankThree.PerfectCover.hopfMultiplier (NativeSporadic.Carrier .HS)) = 2 :=
      LocalAnalysis.HigmanSimsCover.card_hopfMultiplier
    have hc : Nat.card (center (↥K ⧸ pPrimeCore 2 ↥K)) ≤ 2 := by
      have hd := GH74.Generic.card_center_dvd_hopfMultiplier hq eN
      rw [hM2] at hd
      exact Nat.le_of_dvd (by norm_num) hd
    have hZ := center_eq_zpowers h hc
    have eX : (↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K) ≃* Sporadic.Schreier.hsP :=
      eN.trans Sporadic.Schreier.hsPermEquiv
    obtain ⟨hM, hMt⟩ := comp_data h CatalogueU.sporadicOddCoreFree_HS eN eX
    exact HS.false_of_fixed hLq h.orderOf_wbar hZ
      (eX.toMonoidHom.comp (QuotientGroup.mk' (center (↥K ⧸ pPrimeCore 2 ↥K)))) (hπ eX)
      (hker hZ eX) h.tau hα ((eX.symm.trans (quotAut h.tau)).trans eX) (hβ eX)
      hfix huniq hM hMt

end CFSG.ComponentClassification.SolMax.H35
