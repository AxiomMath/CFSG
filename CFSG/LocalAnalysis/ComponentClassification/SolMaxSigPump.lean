module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSigDich

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup

variable {X : Type} [Group X]

theorem exact_of_le_of_alt [Finite X] {J M : Subgroup X} (hJM : J ≤ M) (hMperf : ⁅M, M⁆ = M)
    {n : ℕ} (hn : 5 ≤ n) (eJ : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n))
    (eM : M ⧸ Open.fusionZStar M ≃* alternatingGroup (Fin n)) :
    J ⊔ FooteLit.oddCoreIn M = M ∧
      Nonempty (M ⧸ pPrimeCore 2 M ≃* alternatingGroup (Fin n)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZJ := fusionZStar_eq_of_alt (by omega) eJ
  let eJZ : J ⧸ Open.fusionZStar J ≃* alternatingGroup (Fin n) :=
    (QuotientGroup.quotientMulEquivOfEq hZJ).trans eJ
  have hsup := FooteLit.sup_oddCoreIn_eq_of_fusionZStar_equiv hJM hMperf (eJZ.trans eM.symm)
  refine ⟨hsup, ?_⟩
  have hsup' : J.subgroupOf M ⊔ pPrimeCore 2 M = ⊤ := by
    have h1 : (J ⊔ FooteLit.oddCoreIn M).subgroupOf M = ⊤ := by
      rw [hsup]
      exact subgroupOf_self M
    rwa [FooteLit.oddCoreIn, subgroupOf_sup hJM (map_subtype_le _),
      subgroupOf_map_subtype_self] at h1
  set f : ↥J →* ↥M ⧸ pPrimeCore 2 ↥M :=
    (QuotientGroup.mk' (pPrimeCore 2 ↥M)).comp (inclusion hJM) with hfdef
  have hf : Function.Surjective f := by
    rw [← MonoidHom.range_eq_top, hfdef, MonoidHom.range_comp, Subgroup.inclusion_range]
    have h2 := congrArg (Subgroup.map (QuotientGroup.mk' (pPrimeCore 2 ↥M))) hsup'
    rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h2
  have hOJ : pPrimeCore 2 ↥J ≤ f.ker := by
    have hnorm : ((pPrimeCore 2 ↥J).map f).Normal := Subgroup.Normal.map inferInstance f hf
    have hodd : Nat.Coprime 2 (Nat.card ((pPrimeCore 2 ↥J).map f)) :=
      Nat.Coprime.coprime_dvd_right ((pPrimeCore 2 ↥J).card_map_dvd f) pPrimeCore_coprime_card
    have hle : (pPrimeCore 2 ↥J).map f ≤ pPrimeCore 2 (↥M ⧸ pPrimeCore 2 ↥M) :=
      le_sSup ⟨hnorm, hodd⟩
    rwa [pPrimeCore_quotient_pPrimeCore_eq_bot, le_bot_iff, Subgroup.map_eq_bot_iff] at hle
  set fb := QuotientGroup.lift (pPrimeCore 2 ↥J) f hOJ with hfb
  have hfb_surj : Function.Surjective fb := by
    intro q
    obtain ⟨j, rfl⟩ := hf q
    exact ⟨(j : ↥J ⧸ pPrimeCore 2 ↥J), rfl⟩
  have : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; omega)
  have : IsSimpleGroup (↥J ⧸ pPrimeCore 2 ↥J) := MulEquiv.isSimpleGroup eJ
  have hfb_inj : Function.Injective fb := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal fb.ker with h | h
    · exact h
    · exfalso
      have htriv : ∀ q : ↥M ⧸ pPrimeCore 2 ↥M, q = 1 := by
        intro q
        obtain ⟨p, rfl⟩ := hfb_surj q
        exact (MonoidHom.mem_ker).mp (h ▸ mem_top p)
      have hO : pPrimeCore 2 ↥M = ⊤ := by
        rw [eq_top_iff]
        intro m _
        rw [← QuotientGroup.eq_one_iff]
        exact htriv _
      have hZ : Open.fusionZStar ↥M = ⊤ := top_le_iff.mp (hO ▸ Sol78.pPrimeCore_le_fusionZStar _)
      have h3 : ∀ a b : alternatingGroup (Fin n), a = b := by
        intro a b
        obtain ⟨a', rfl⟩ := eM.surjective a
        obtain ⟨b', rfl⟩ := eM.surjective b
        obtain ⟨a'', rfl⟩ := QuotientGroup.mk'_surjective _ a'
        obtain ⟨b'', rfl⟩ := QuotientGroup.mk'_surjective _ b'
        congr 1
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
        rw [hZ]
        exact mem_top _
      have h4 : Nontrivial (alternatingGroup (Fin n)) :=
        IsSimpleGroup.toNontrivial
      obtain ⟨a, b, hab⟩ := h4
      exact hab (h3 a b)
  exact ⟨(MulEquiv.ofBijective fb ⟨hfb_inj, hfb_surj⟩).symm.trans eJ⟩

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  (S : Sig36 X t J n e E D)
include S

theorem subgroupOf_le_centralizer_mk {Y : Subgroup X} (htY : t ∈ Y) :
    J.subgroupOf Y ≤ centralizer ({(⟨t, htY⟩ : ↥Y)} : Set ↥Y) := by
  intro x hx
  rw [mem_centralizer_singleton_iff]
  exact Subtype.ext (mem_centralizer_singleton_iff.mp (S.pair.1.2.1 (mem_subgroupOf.mp hx)))

theorem isPComponent_subgroupOf_centralizer_mk {Y : Subgroup X}
    (hCY : centralizer ({t} : Set X) ≤ Y) (htY : t ∈ Y) :
    IsPComponent 2 ((J.subgroupOf Y).subgroupOf (centralizer ({(⟨t, htY⟩ : ↥Y)} : Set ↥Y))) := by
  rw [centralizer_mk_eq htY, inf_of_le_left hCY,
    UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' hCY 2 Nat.prime_two]
  exact S.pair.1.2.2.1

theorem exists_pumped_component (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput) (hPump : Sol78.AlternatingPumpUpInput)
    (hW : Sol78.signalizerCompletion E E ≠ ⊥) {M : Subgroup X}
    (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (htM : t ∈ normalizer (M : Set X)) (hJM : J ≤ M) :
    ∃ m : ℕ, Odd m ∧ n ≤ m ∧
      Nonempty (↥M ⧸ Open.fusionZStar ↥M ≃* alternatingGroup (Fin m)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCH := S.centralizer_le_normalizer_completion h33 h35 hT13 hML hSch
  have hHne := S.normalizer_completion_ne_top h33 hW
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  have htH : t ∈ H := hCH (mem_centralizer_singleton_iff.mpr rfl)
  have hJH : J ≤ H := S.pair.1.2.1.trans hCH
  have ht' : orderOf (⟨t, htH⟩ : ↥H) = 2 := by rw [Subgroup.orderOf_mk]; exact S.pair.1.1
  let eJ' : ↥(J.subgroupOf H) ⧸ pPrimeCore 2 ↥(J.subgroupOf H) ≃* alternatingGroup (Fin n) :=
    (Sol78.coreQuotCongr (subgroupOfEquivOfLe hJH)).trans e
  have hZJ' := fusionZStar_eq_of_alt (by have := S.nine_le; omega) eJ'
  have hK : SectionRank.IsKGroupCat ↥H := UnbalancedCorr.isKGroupCat_of_ne_top S.kProper hHne
  have hTM : J.subgroupOf H ≤ M.subgroupOf H := fun x hx => hJM hx
  have hZ : (Open.fusionZStar ↥(J.subgroupOf H)).map (J.subgroupOf H).subtype ≤
      (pPrimeCore 2 ↥(J.subgroupOf H)).map (J.subgroupOf H).subtype ⊔
        (Open.fusionZStar ↥(M.subgroupOf H)).map (M.subgroupOf H).subtype := by
    rw [hZJ']
    exact le_sup_left
  rcases hPump ↥H hK (M.subgroupOf H) hMpc ⟨t, htH⟩ ht' (mem_normalizer_subgroupOf_of_mem htH htM)
      (J.subgroupOf H) hTM (S.subgroupOf_le_centralizer_mk htH)
      (S.isPComponent_subgroupOf_centralizer_mk hCH htH) hZ n S.pair.2.1
      (by have := S.nine_le; omega) ⟨(QuotientGroup.quotientMulEquivOfEq hZJ').trans eJ'⟩ with
    ⟨m, hm, hnm, ⟨eM⟩⟩ | ⟨h7, -⟩
  · exact ⟨m, hm, hnm, ⟨(Sol78.fusionZStarQuotCongr (subgroupOfEquivOfLe hMH)).symm.trans eM⟩⟩
  · have := S.nine_le
    omega

end Sig36

end CFSG.ComponentClassification.SolMax
