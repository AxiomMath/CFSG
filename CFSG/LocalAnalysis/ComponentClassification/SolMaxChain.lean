module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxDescent
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Lemma212Proof

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G]

theorem nonempty_witness_coreQuot_equiv {K T : Subgroup G}
    (hKq : IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K)) (hT2 : IsPGroup 2 T)
    (hTQ : T ≤ coreActionKernel K) :
    Nonempty (↥(oddResidualIn (oddCoreIn (centralizer (T : Set G)) ⊔
        (K ⊓ centralizer (T : Set G)))) ⧸ pPrimeCore 2 ↥(oddResidualIn
        (oddCoreIn (centralizer (T : Set G)) ⊔ (K ⊓ centralizer (T : Set G)))) ≃*
      ↥K ⧸ pPrimeCore 2 ↥K) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer (T : Set G) with hC
  set Y := K ⊓ C with hY
  set OC := oddCoreIn C with hOC
  set H := OC ⊔ Y with hH
  set K0 := oddResidualIn H with hK0def
  have hYL : Y ≤ K := inf_le_left
  have hYH : Y ≤ H := le_sup_right
  have hOCH : OC ≤ H := le_sup_left
  have hHC : H ≤ C := sup_le (map_subtype_le _) inf_le_right
  have hK0eq : K0 = (CatalogueBPrimeJoin.primeResidual 2 ↥H).map H.subtype :=
    Sol76.oddResidualIn_eq_map_primeResidual H
  have hK0H : K0 ≤ H := by rw [hK0eq]; exact map_subtype_le _
  have hK0sub : K0.subgroupOf H = CatalogueBPrimeJoin.primeResidual 2 ↥H := by
    rw [hK0eq, ← comap_subtype, comap_map_eq_self_of_injective H.subtype_injective]
  have hOHodd : Odd (Nat.card (OC.subgroupOf H)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hOCH).toEquiv]
    exact Nat.coprime_two_left.mp (Sol76.coprime_card_oddCoreIn C)
  have hOHn : (OC.subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer hOCH).mpr (hHC.trans (Sol76.le_normalizer_oddCoreIn C))
  have hoddL : Odd (Nat.card (pPrimeCore 2 ↥K)) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥K))
  have hoddH : Odd (Nat.card (pPrimeCore 2 ↥H)) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥H))
  have hHsup : Y ⊔ (OC.subgroupOf H).map H.subtype = H := by
    rw [subgroupOf_map_subtype, inf_eq_left.mpr hOCH, sup_comm]
  have hLsup : Y ⊔ (pPrimeCore 2 ↥K).map K.subtype = K :=
    Sol76.inf_centralizer_sup_oddCoreIn_eq hT2 hTQ
  have e1 := Sol76.coreQuotEquivOfSurjective _ (Sol76.surjective_mk_comp_inclusion hYL hLsup)
    (Sol76.odd_card_ker_mk_comp_inclusion hYL (pPrimeCore 2 ↥K) hoddL)
  have e2 := Sol76.coreQuotEquivOfSurjective _ (Sol76.surjective_mk_comp_inclusion hYH hHsup)
    (Sol76.odd_card_ker_mk_comp_inclusion hYH (OC.subgroupOf H) hOHodd)
  have e3 := Sol76.coreQuotEquivOfSurjective (QuotientGroup.mk' (OC.subgroupOf H))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']; exact hOHodd)
  have eLH : ↥K ⧸ pPrimeCore 2 ↥K ≃* ↥H ⧸ pPrimeCore 2 ↥H :=
    (Sol76.coreQuotCoreQuotEquiv ↥K).symm.trans (e1.symm.trans (e2.trans e3.symm))
  have : Group.IsPerfect (↥K ⧸ pPrimeCore 2 ↥K) := hKq.1
  have hHperf : Group.IsPerfect (↥H ⧸ pPrimeCore 2 ↥H) :=
    Group.IsPerfect.ofSurjective (f := eLH.toMonoidHom) eLH.surjective
  set κ := (QuotientGroup.mk' (pPrimeCore 2 ↥H)).comp (Subgroup.inclusion hK0H) with hκ
  have hκs : Function.Surjective κ := by
    rw [← MonoidHom.range_eq_top]
    calc κ.range = (K0.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 ↥H)) := by
          rw [hκ, MonoidHom.range_comp, Subgroup.inclusion_range]
      _ = (CatalogueBPrimeJoin.primeResidual 2 ↥H).map (QuotientGroup.mk' (pPrimeCore 2 ↥H)) := by
          rw [hK0sub]
      _ = CatalogueBPrimeJoin.primeResidual 2 (↥H ⧸ pPrimeCore 2 ↥H) :=
          CatalogueBPrimeJoin.primeResidual_map_surjective 2 _ (QuotientGroup.mk'_surjective _)
      _ = ⊤ := Sol76.primeResidual_two_eq_top hHperf
  have e4 := Sol76.coreQuotEquivOfSurjective κ hκs
    (Sol76.odd_card_ker_mk_comp_inclusion hK0H (pPrimeCore 2 ↥H) hoddH)
  exact ⟨e4.trans ((Sol76.coreQuotCoreQuotEquiv ↥H).trans eLH.symm)⟩

theorem starAt_inv_of_witness {K T : Subgroup G} (hKq : IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K))
    (hT2 : IsPGroup 2 T) (hTQ : T ≤ coreActionKernel K)
    (hK0 : IsTwoComponentIn (oddResidualIn (oddCoreIn (centralizer (T : Set G)) ⊔
      (K ⊓ centralizer (T : Set G)))) (centralizer (T : Set G))) :
    StarAt K T ∧ InvAt K T := by
  classical
  refine ⟨Sol76.twoLayer_inf_centralizer_le_of_witness hKq hT2 hTQ hK0, fun M hM hmove => ?_⟩
  set K0 := oddResidualIn (oddCoreIn (centralizer (T : Set G)) ⊔ (K ⊓ centralizer (T : Set G)))
  obtain ⟨-, hLT, -, -⟩ := Sol76.cover_facts hKq inf_le_left
    (Sol76.inf_centralizer_sup_oddCoreIn_eq hT2 hTQ)
  have hJK0 : twoLayerIn (K ⊓ centralizer (T : Set G)) ≤ K0 := by
    rw [hLT]
    exact closure_mono fun x hx => ⟨mem_sup_right hx.1, hx.2⟩
  have hMK0 : M = K0 := by
    by_contra hne
    exact hmove (hJK0.trans (GSThmB.B5a.le_coreActionKernel_of_ne hM.1 hK0.1 hM.2 hK0.2 hne))
  rw [hMK0]
  obtain ⟨e⟩ := nonempty_witness_coreQuot_equiv hKq hT2 hTQ
  exact Nat.card_congr (Sol78.fusionZStarQuotOfCore e).toEquiv

section Transport

variable (φ : G ≃* G)

theorem map_layerAt {K : Subgroup G} (hK : K.map φ.toMonoidHom = K) (A : Subgroup G) :
    (twoLayerIn (K ⊓ centralizer (A : Set G))).map φ.toMonoidHom =
      twoLayerIn (K ⊓ centralizer ((A.map φ.toMonoidHom : Subgroup G) : Set G)) := by
  rw [Sol76.map_twoLayerIn, Subgroup.map_inf_eq _ _ _ φ.injective, hK, Sol76.map_centralizer]

end Transport

theorem starAt_inv_of_le {K P : Subgroup G} (hKq : IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K))
    (hP : IsPGroup 2 P) (hPQ : P ≤ coreActionKernel K) :
    ∀ A : Subgroup G, A ≤ P → StarAt K A → InvAt K A → StarAt K P ∧ InvAt K P := by
  suffices key : ∀ n : ℕ, ∀ A : Subgroup G, Nat.card P - Nat.card A = n → A ≤ P →
      StarAt K A → InvAt K A → StarAt K P ∧ InvAt K P from fun A => key _ A rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A hn hAP hA hA'
    by_cases hAP' : A = P
    · rw [← hAP']; exact ⟨hA, hA'⟩
    obtain ⟨s, hsP, hsN, hsA, hs2⟩ := Sol76.exists_sq_mem_of_ne hP hAP hAP'
    have hA'P : A ⊔ zpowers s ≤ P := sup_le hAP (zpowers_le.mpr hsP)
    have hAA' : A < A ⊔ zpowers s := lt_of_le_of_ne le_sup_left fun h =>
      hsA (h ▸ mem_sup_right (mem_zpowers s))
    have hcard : Nat.card A < Nat.card ↥(A ⊔ zpowers s) := Subgroup.card_lt_of_lt hAA'
    have hcardP : Nat.card ↥(A ⊔ zpowers s) ≤ Nat.card P := card_le_of_le hA'P
    obtain ⟨h1, h2⟩ := good_sup_zpowers hKq (hP.to_le hAP) (hAP.trans hPQ)
      (hP.to_le (zpowers_le.mpr hsP)) (hPQ hsP) hsN hs2 hA hA'
    exact ih _ (by omega) _ rfl hA'P h1 h2

theorem altAt_of_invAt {K P : Subgroup G} {n : ℕ} (hKq : IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K))
    (hP : IsPGroup 2 P) (hPQ : P ≤ coreActionKernel K) (hn : Odd n)
    (eK : ↥K ⧸ Open.fusionZStar ↥K ≃* alternatingGroup (Fin n)) (hstar : StarAt K P)
    (hinv : InvAt K P) : AltAt K P n := by
  intro M hM hmove
  obtain ⟨hJp, hJq, hJZ, ⟨eJ⟩⟩ := layerAt_facts hKq hP hPQ
  obtain ⟨-, heq⟩ := card_fusionZStar_quot_le hstar hJp hJq hM hmove
  obtain ⟨e⟩ := heq (hJZ.trans (hinv M hM hmove).symm)
  exact ⟨n, hn, le_rfl, ⟨e.symm.trans (eJ.trans eK)⟩⟩

theorem starAt_altAt_of_le (hPump : Sol78.AlternatingPumpUpInput) {K P : Subgroup G} {n : ℕ}
    (hKq : IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K)) (hP : IsPGroup 2 P)
    (hPQ : P ≤ coreActionKernel K) (hn9 : 9 ≤ n)
    (hKH : ∀ (A : Subgroup G) (x : G), A ≠ ⊥ → IsPGroup 2 A → x ∈ normalizer (A : Set G) →
      SectionRank.IsKGroupCat ↥(centralizer (A : Set G) ⊔ zpowers x))
    (hexact : ∀ B : Subgroup G, B ≠ ⊥ → IsPGroup 2 B → ∀ T : Subgroup G,
      IsTwoComponentIn T (centralizer (B : Set G)) →
      ∀ m : ℕ, Odd m → 9 ≤ m → Nonempty (↥T ⧸ Open.fusionZStar ↥T ≃* alternatingGroup (Fin m)) →
        Open.fusionZStar ↥T = pPrimeCore 2 ↥T)
    (hstarP : StarAt K P) (haltP : AltAt K P n) :
    ∀ S : Subgroup G, S ≤ P → S ≠ ⊥ → StarAt K S ∧ AltAt K S n := by
  suffices key : ∀ k : ℕ, ∀ S : Subgroup G, Nat.card P - Nat.card S = k → S ≤ P → S ≠ ⊥ →
      StarAt K S ∧ AltAt K S n from fun S => key _ S rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro S hk hSP hS
    by_cases hSP' : S = P
    · rw [hSP']; exact ⟨hstarP, haltP⟩
    obtain ⟨s, hsP, hsN, hsS, hs2⟩ := Sol76.exists_sq_mem_of_ne hP hSP hSP'
    have hS'P : S ⊔ zpowers s ≤ P := sup_le hSP (zpowers_le.mpr hsP)
    have hSS' : S < S ⊔ zpowers s := lt_of_le_of_ne le_sup_left fun h =>
      hsS (h ▸ mem_sup_right (mem_zpowers s))
    have hcard : Nat.card S < Nat.card ↥(S ⊔ zpowers s) := Subgroup.card_lt_of_lt hSS'
    have hcardP : Nat.card ↥(S ⊔ zpowers s) ≤ Nat.card P := card_le_of_le hS'P
    have hS'ne : S ⊔ zpowers s ≠ ⊥ := fun h => hS (eq_bot_iff.mpr (h ▸ le_sup_left))
    obtain ⟨h1, h2⟩ := ih _ (by omega) _ rfl hS'P hS'ne
    have hS2 : IsPGroup 2 S := hP.to_le hSP
    exact altAt_of_sup_zpowers hPump hKq hS2 (hSP.trans hPQ) (hP.to_le (zpowers_le.mpr hsP))
      (hPQ hsP) hsN hs2 hsS hn9 (hKH S s hS hS2 hsN)
      (fun T hT m hm hm9 e => hexact _ hS'ne (hP.to_le hS'P) T hT m hm hm9 e) h1 h2

end CFSG.ComponentClassification.SolMax
