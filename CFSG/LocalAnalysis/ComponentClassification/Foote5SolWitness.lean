module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5SolStar
public import CFSG.LocalAnalysis.ComponentClassification.Foote5SolOrbit

public section

namespace CFSG.ComponentClassification.Foote5.SolMax

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76

variable {G : Type} [Group G] [Finite G]

theorem witness_facts {L : Subgroup G} (hL : IsSolomonMember L) :
    ∃ T : Subgroup G, T ≠ ⊥ ∧ IsPGroup 2 T ∧ T ≤ coreActionKernel L ∧ ∃ Y : Subgroup G,
      IsTwoComponentIn Y (centralizer (T : Set G)) ∧
      twoLayerIn (L ⊓ centralizer (T : Set G)) ≤ Y ∧
      Nonempty (↥Y ⧸ pPrimeCore 2 ↥Y ≃* ↥L ⧸ pPrimeCore 2 ↥L) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLq := isQuasisimple_coreQuot_of_isSolomonMember hL
  obtain ⟨hLp, T, hT, hT2, hTQ, hK0⟩ := hL
  set C := centralizer (T : Set G) with hC
  set Y := L ⊓ C with hY
  set OC := oddCoreIn C with hOC
  set H := OC ⊔ Y with hH
  set K0 := oddResidualIn H with hK0def
  have hYL : Y ≤ L := inf_le_left
  have hYH : Y ≤ H := le_sup_right
  have hOCH : OC ≤ H := le_sup_left
  have hHC : H ≤ C := sup_le (map_subtype_le _) inf_le_right
  have hK0eq : K0 = (CatalogueBPrimeJoin.primeResidual 2 ↥H).map H.subtype :=
    oddResidualIn_eq_map_primeResidual H
  have hK0H : K0 ≤ H := by rw [hK0eq]; exact map_subtype_le _
  have hK0sub : K0.subgroupOf H = CatalogueBPrimeJoin.primeResidual 2 ↥H := by
    rw [hK0eq, ← comap_subtype, comap_map_eq_self_of_injective H.subtype_injective]
  have hOHn : (OC.subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer hOCH).mpr (hHC.trans (le_normalizer_oddCoreIn C))
  have hOHodd : Odd (Nat.card (OC.subgroupOf H)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hOCH).toEquiv]
    exact Nat.coprime_two_left.mp (coprime_card_oddCoreIn C)
  have hoddL : Odd (Nat.card (pPrimeCore 2 ↥L)) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥L))
  have hoddH : Odd (Nat.card (pPrimeCore 2 ↥H)) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥H))
  have hHsup : Y ⊔ (OC.subgroupOf H).map H.subtype = H := by
    rw [subgroupOf_map_subtype, inf_eq_left.mpr hOCH, sup_comm]
  have hLsup : Y ⊔ (pPrimeCore 2 ↥L).map L.subtype = L := inf_centralizer_sup_oddCoreIn_eq hT2 hTQ
  have e1 := coreQuotEquivOfSurjective _ (surjective_mk_comp_inclusion hYL hLsup)
    (odd_card_ker_mk_comp_inclusion hYL (pPrimeCore 2 ↥L) hoddL)
  have e2 := coreQuotEquivOfSurjective _ (surjective_mk_comp_inclusion hYH hHsup)
    (odd_card_ker_mk_comp_inclusion hYH (OC.subgroupOf H) hOHodd)
  have e3 := coreQuotEquivOfSurjective (QuotientGroup.mk' (OC.subgroupOf H))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']; exact hOHodd)
  have eLH : ↥L ⧸ pPrimeCore 2 ↥L ≃* ↥H ⧸ pPrimeCore 2 ↥H :=
    (coreQuotCoreQuotEquiv ↥L).symm.trans (e1.symm.trans (e2.trans e3.symm))
  have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hLp
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
      _ = ⊤ := primeResidual_two_eq_top hHperf
  have e4 := coreQuotEquivOfSurjective κ hκs
    (odd_card_ker_mk_comp_inclusion hK0H (pPrimeCore 2 ↥H) hoddH)
  refine ⟨T, hT, hT2, hTQ, K0, hK0, ?_,
    ⟨e4.trans ((coreQuotCoreQuotEquiv ↥H).trans eLH.symm)⟩⟩
  obtain ⟨-, hLT, -, -⟩ := cover_facts hLq inf_le_left (inf_centralizer_sup_oddCoreIn_eq hT2 hTQ)
  rw [hLT]
  exact closure_mono fun x hx => ⟨mem_sup_right hx.1, hx.2⟩

theorem single_sup_zpowers {L A Y : Subgroup G} {s : G}
    (hLq : IsQuasisimple (↥L ⧸ pPrimeCore 2 ↥L)) (hA2 : IsPGroup 2 A)
    (hAQ : A ≤ coreActionKernel L) (hs : IsPGroup 2 (zpowers s)) (hsQ : s ∈ coreActionKernel L)
    (hsA : s ∈ normalizer (A : Set G)) (hs2A : s ^ 2 ∈ A)
    (hY : IsTwoComponentIn Y (centralizer (A : Set G)))
    (hLY : twoLayerIn (L ⊓ centralizer (A : Set G)) ≤ Y)
    (hYcard : Nat.card (↥Y ⧸ Open.fusionZStar ↥Y) = Nat.card (↥L ⧸ Open.fusionZStar ↥L)) :
    ∃ Y' : Subgroup G,
      IsTwoComponentIn Y' (centralizer ((A ⊔ zpowers s : Subgroup G) : Set G)) ∧
      twoLayerIn (L ⊓ centralizer ((A ⊔ zpowers s : Subgroup G) : Set G)) ≤ Y' ∧
      Nat.card (↥Y' ⧸ Open.fusionZStar ↥Y') = Nat.card (↥L ⧸ Open.fusionZStar ↥L) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set CA := centralizer (A : Set G) with hCA
  set B := A ⊔ zpowers s with hB
  have hzA : zpowers s ≤ normalizer (A : Set G) := zpowers_le.mpr hsA
  have hB2 : IsPGroup 2 B := by
    have := IsPGroup.to_sup_of_normal_right' hs hA2 hzA
    rwa [sup_comm] at this
  have hBQ : B ≤ coreActionKernel L := sup_le hAQ (zpowers_le.mpr hsQ)
  have hstarA : twoLayerIn (L ⊓ CA) ≤ twoLayerIn CA :=
    hLY.trans (le_twoLayerIn_of_isTwoComponentIn hY)
  have htyp : ∀ K : Subgroup G, IsTwoComponentIn K CA → ¬ twoLayerIn (L ⊓ CA) ≤
      coreActionKernel K →
      Nat.card (↥K ⧸ Open.fusionZStar ↥K) = Nat.card (↥L ⧸ Open.fusionZStar ↥L) := by
    intro K hK hmv
    have hKY : K = Y := by
      by_contra hne
      exact hmv (hLY.trans (le_coreActionKernel_of_ne hK hY hne))
    rw [hKY]
    exact hYcard
  have hstarB := star_sup_zpowers hLq hA2 hAQ hs hsQ hsA hs2A hstarA htyp
  obtain ⟨hLAc, hLAr, -, ⟨eLA⟩⟩ := cover_facts hLq inf_le_left
    (inf_centralizer_sup_oddCoreIn_eq hA2 hAQ)
  obtain ⟨hLBc, hLBr, -, ⟨eLB⟩⟩ := cover_facts hLq inf_le_left
    (inf_centralizer_sup_oddCoreIn_eq hB2 hBQ)
  have hLAq : IsQuasisimple (↥(twoLayerIn (L ⊓ CA)) ⧸ pPrimeCore 2 ↥(twoLayerIn (L ⊓ CA))) := by
    rw [hLAr]
    exact LocalCores.isQuasisimple_of_mulEquiv eLA.symm hLq
  set LB := twoLayerIn (L ⊓ centralizer (B : Set G)) with hLB
  have hLBperf : ⁅LB, LB⁆ = LB := by
    rw [hLBr]
    exact UnbalancedCorr.commutator_eq_of_isPComponent hLBc.1 hLBc.2
  have hLBq : IsQuasisimple (↥LB ⧸ pPrimeCore 2 ↥LB) := by
    rw [hLBr]
    exact LocalCores.isQuasisimple_of_mulEquiv eLB.symm hLq
  have hLBcard : Nat.card (↥LB ⧸ Open.fusionZStar ↥LB) = Nat.card (↥L ⧸ Open.fusionZStar ↥L) := by
    rw [hLBr]
    exact Nat.card_congr (Sol78.fusionZStarQuotOfCore eLB).toEquiv
  have hLBA : LB ≤ twoLayerIn (L ⊓ CA) :=
    twoLayerIn_inf_centralizer_anti hLq hA2 hB2 hAQ hBQ le_sup_left
  have hLBY : LB ≤ Y := hLBA.trans hLY
  set X := CA ⊔ zpowers s with hX
  have hCAX : CA ≤ X := le_sup_left
  have hzCA : zpowers s ≤ normalizer (CA : Set G) := le_normalizer_centralizer hzA
  have hXN : X ≤ normalizer (CA : Set G) := sup_le le_normalizer hzCA
  have hCAn : (CA.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hCAX).mpr hXN
  have hYX : IsTwoComponentIn Y X :=
    ⟨hY.1.trans hCAX, GrSLit.isPComponent_subgroupOf_of_isSubnormal hY.1 hCAX
      hCAn.isSubnormal hY.2⟩
  have hLBX : LB ≤ twoLayerIn X := hLBY.trans ((le_twoLayerIn_of_isTwoComponentIn hY).trans
    (GrSLit.pLayer_map_le_of_isSubnormal hCAX hCAn.isSubnormal))
  have hmvY : ¬ LB ≤ coreActionKernel Y := not_le_coreActionKernel_of_le hLBY hLBq
  have hcardBY : Nat.card (↥LB ⧸ Open.fusionZStar ↥LB) = Nat.card (↥Y ⧸ Open.fusionZStar ↥Y) := by
    rw [hLBcard, hYcard]
  have hsY : s ∈ normalizer (Y : Set G) := by
    have hCAφ : CA.map (MulAut.conj s).toMonoidHom = CA :=
      mem_normalizer_iff_map_conj_eq.mp (hzCA (mem_zpowers s))
    have hLφ : L.map (MulAut.conj s).toMonoidHom = L :=
      mem_normalizer_iff_map_conj_eq.mp (mem_coreActionKernel.mp hsQ).1
    have hLAφ : (twoLayerIn (L ⊓ CA)).map (MulAut.conj s).toMonoidHom = twoLayerIn (L ⊓ CA) := by
      rw [Sol76.map_twoLayerIn, map_inf_eq _ _ _ (MulAut.conj s).injective, hLφ, hCAφ]
    have hYφ : IsTwoComponentIn (Y.map (MulAut.conj s).toMonoidHom) CA := by
      have := Sol76.isTwoComponentIn_map (MulAut.conj s) hY
      rwa [hCAφ] at this
    have hLYφ : twoLayerIn (L ⊓ CA) ≤ Y.map (MulAut.conj s).toMonoidHom := by
      rw [← hLAφ]
      exact map_mono hLY
    have heq : Y.map (MulAut.conj s).toMonoidHom = Y := by
      by_contra hne
      exact not_le_coreActionKernel_of_le hLY hLAq
        (hLYφ.trans (le_coreActionKernel_of_ne hY hYφ (Ne.symm hne)))
    exact mem_normalizer_iff_map_conj_eq.mpr heq
  have hsX : s ∈ X := mem_sup_right (mem_zpowers s)
  have hsYk : s ∈ coreActionKernel Y := by
    refine ((moved_facts hLBX hLBperf hLBq hYX hmvY).2 hcardBY).2 s hsX (fun r hr => ?_) hsY
    have hr' : r ∈ L ⊓ centralizer (B : Set G) := (map_subtype_le _) hr
    have hrs : r ∈ centralizer ({s} : Set G) := by
      rw [← centralizer_zpowers']
      exact centralizer_le (show ((zpowers s : Subgroup G) : Set G) ⊆ (B : Set G) from
        fun x hx => mem_sup_right hx) (mem_inf.mp hr').2
    exact (mem_centralizer_singleton_iff.mp hrs).symm
  have hYq : IsQuasisimple (↥Y ⧸ pPrimeCore 2 ↥Y) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 Y _ hY.1).1 hY.2).2.2
  have hYsub : (Y.subgroupOf X).IsSubnormal := by
    obtain ⟨-, -, h, -, -⟩ := hYX.2
    exact h
  have hY'p := GSLit.fixedLayer_isPComponent (X := X) (J := Y) (E := zpowers s) hYX.1 hYsub
    (zpowers_le.mpr hsX) (zpowers_le.mpr hsYk) hs hYq
  set Y' := twoLayerIn (Y ⊓ centralizer ((zpowers s : Subgroup G) : Set G)) with hY'
  have hCB : centralizer (B : Set G) = CA ⊓ centralizer ((zpowers s : Subgroup G) : Set G) :=
    centralizer_sup_eq A (zpowers s)
  have hY'le : Y' ≤ CA ⊓ centralizer ((zpowers s : Subgroup G) : Set G) :=
    (map_subtype_le _).trans (inf_le_inf_right _ hY.1)
  have hY'c : IsTwoComponentIn Y' (centralizer (B : Set G)) := by
    rw [hCB]
    exact ⟨hY'le, CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hY'le
      (inf_le_inf_right _ hCAX) hY'p⟩
  obtain ⟨-, hY'r, -, ⟨eY'⟩⟩ := cover_facts hYq inf_le_left
    (inf_centralizer_sup_oddCoreIn_eq hs (zpowers_le.mpr hsYk))
  have hLBY' : LB ≤ Y' := by
    have h1 : LB = oddResidualIn (L ⊓ centralizer (B : Set G)) := hLBr
    have h2 : LB ≤ Y := hLBY
    rw [hY', hY'r, h1]
    refine (closure_le _).mpr fun x hx => subset_closure ⟨mem_inf.mpr ⟨?_, ?_⟩, hx.2⟩
    · rw [h1] at h2
      exact h2 (subset_closure hx)
    · rw [hCB] at hx
      exact (mem_inf.mp (mem_inf.mp hx.1).2).2
  refine ⟨Y', hY'c, hLBY', ?_⟩
  rw [hY', hY'r, ← hYcard]
  exact Nat.card_congr (Sol78.fusionZStarQuotOfCore eY').toEquiv

theorem single_of_le {L T₀ P Y₀ : Subgroup G} (hLq : IsQuasisimple (↥L ⧸ pPrimeCore 2 ↥L))
    (hP2 : IsPGroup 2 P) (hPQ : P ≤ coreActionKernel L) (hT₀P : T₀ ≤ P)
    (hY₀ : IsTwoComponentIn Y₀ (centralizer (T₀ : Set G)))
    (hLY₀ : twoLayerIn (L ⊓ centralizer (T₀ : Set G)) ≤ Y₀)
    (hY₀card : Nat.card (↥Y₀ ⧸ Open.fusionZStar ↥Y₀) = Nat.card (↥L ⧸ Open.fusionZStar ↥L)) :
    ∃ Y : Subgroup G, IsTwoComponentIn Y (centralizer (P : Set G)) ∧
      twoLayerIn (L ⊓ centralizer (P : Set G)) ≤ Y ∧
      Nat.card (↥Y ⧸ Open.fusionZStar ↥Y) = Nat.card (↥L ⧸ Open.fusionZStar ↥L) := by
  suffices key : ∀ n : ℕ, ∀ A : Subgroup G, Nat.card P - Nat.card A = n → A ≤ P →
      ∀ Y : Subgroup G, IsTwoComponentIn Y (centralizer (A : Set G)) →
      twoLayerIn (L ⊓ centralizer (A : Set G)) ≤ Y →
      Nat.card (↥Y ⧸ Open.fusionZStar ↥Y) = Nat.card (↥L ⧸ Open.fusionZStar ↥L) →
      ∃ Y : Subgroup G, IsTwoComponentIn Y (centralizer (P : Set G)) ∧
        twoLayerIn (L ⊓ centralizer (P : Set G)) ≤ Y ∧
        Nat.card (↥Y ⧸ Open.fusionZStar ↥Y) = Nat.card (↥L ⧸ Open.fusionZStar ↥L) from
    key _ T₀ rfl hT₀P Y₀ hY₀ hLY₀ hY₀card
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A hn hAP Y hY hLY hYcard
    by_cases hAP' : A = P
    · rw [← hAP']; exact ⟨Y, hY, hLY, hYcard⟩
    obtain ⟨s, hsP, hsN, hsA, hs2⟩ := exists_sq_mem_of_ne hP2 hAP hAP'
    have hA'P : A ⊔ zpowers s ≤ P := sup_le hAP (zpowers_le.mpr hsP)
    have hAA' : A < A ⊔ zpowers s := lt_of_le_of_ne le_sup_left fun h =>
      hsA (h ▸ mem_sup_right (mem_zpowers s))
    have hcard : Nat.card A < Nat.card ↥(A ⊔ zpowers s) := Subgroup.card_lt_of_lt hAA'
    have hcardP : Nat.card ↥(A ⊔ zpowers s) ≤ Nat.card P := card_le_of_le hA'P
    obtain ⟨Y', hY', hLY', hY'card⟩ := single_sup_zpowers hLq (hP2.to_le hAP) (hAP.trans hPQ)
      (hP2.to_le (zpowers_le.mpr hsP)) (hPQ hsP) hsN hs2 hY hLY hYcard
    exact ih _ (by omega) _ rfl hA'P Y' hY' hLY' hY'card

theorem single_conj {L A Y : Subgroup G} {y : G} (hy : y ∈ normalizer (L : Set G))
    (hY : IsTwoComponentIn Y (centralizer (A : Set G)))
    (hLY : twoLayerIn (L ⊓ centralizer (A : Set G)) ≤ Y)
    (hYcard : Nat.card (↥Y ⧸ Open.fusionZStar ↥Y) = Nat.card (↥L ⧸ Open.fusionZStar ↥L)) :
    IsTwoComponentIn (Y.map (MulAut.conj y).toMonoidHom)
        (centralizer ((A.map (MulAut.conj y).toMonoidHom : Subgroup G) : Set G)) ∧
      twoLayerIn (L ⊓ centralizer ((A.map (MulAut.conj y).toMonoidHom : Subgroup G) : Set G)) ≤
        Y.map (MulAut.conj y).toMonoidHom ∧
      Nat.card (↥(Y.map (MulAut.conj y).toMonoidHom) ⧸
        Open.fusionZStar ↥(Y.map (MulAut.conj y).toMonoidHom)) =
        Nat.card (↥L ⧸ Open.fusionZStar ↥L) := by
  set φ := MulAut.conj y with hφ
  have hLφ : L.map φ.toMonoidHom = L := mem_normalizer_iff_map_conj_eq.mp hy
  have hC := Sol76.map_centralizer φ A
  refine ⟨?_, ?_, ?_⟩
  · have := Sol76.isTwoComponentIn_map φ hY
    rwa [hC] at this
  · have h1 := map_mono (f := φ.toMonoidHom) hLY
    rwa [Sol76.map_twoLayerIn, map_inf_eq _ _ _ φ.injective, hLφ, hC] at h1
  · rw [← hYcard]
    exact Nat.card_congr (Sol78.fusionZStarQuotCongr
      (Y.equivMapOfInjective φ.toMonoidHom φ.injective)).symm.toEquiv

omit [Finite G] in
theorem map_smul_sylow {N : Subgroup G} (P : Sylow 2 ↥N) (y : ↥N) :
    ((y • P : Sylow 2 ↥N) : Subgroup ↥N).map N.subtype =
      ((P : Subgroup ↥N).map N.subtype).map (MulAut.conj (y : G)).toMonoidHom := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [SetLike.mem_coe, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hu
    obtain ⟨v, hv, rfl⟩ := hu
    exact ⟨v, ⟨v, hv, rfl⟩, by simp [MulAut.smul_def, MulAut.conj_apply]⟩
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨(MulAut.conj y) • v, ?_, by simp [MulAut.smul_def, MulAut.conj_apply]⟩
    rw [SetLike.mem_coe, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul v (MulAut.conj y) _ hv

theorem single_of_sylow {L : Subgroup G} (hL : IsSolomonMember L)
    (P : Sylow 2 ↥(coreActionKernel L)) :
    ∃ Y : Subgroup G,
      IsTwoComponentIn Y (centralizer (((P : Subgroup _).map (coreActionKernel L).subtype :
        Subgroup G) : Set G)) ∧
      twoLayerIn (L ⊓ centralizer (((P : Subgroup _).map (coreActionKernel L).subtype :
        Subgroup G) : Set G)) ≤ Y ∧
      Nat.card (↥Y ⧸ Open.fusionZStar ↥Y) = Nat.card (↥L ⧸ Open.fusionZStar ↥L) := by
  classical
  have hLq := isQuasisimple_coreQuot_of_isSolomonMember hL
  obtain ⟨T₀, -, hT₀2, hT₀Q, Y₀, hY₀, hLY₀, ⟨e₀⟩⟩ := witness_facts hL
  have hY₀card : Nat.card (↥Y₀ ⧸ Open.fusionZStar ↥Y₀) = Nat.card (↥L ⧸ Open.fusionZStar ↥L) :=
    Nat.card_congr (Sol78.fusionZStarQuotOfCore e₀).toEquiv
  obtain ⟨P₁, hT₀P₁⟩ := (hT₀2.comap_subtype (K := coreActionKernel L)).exists_le_sylow
  set P₁' := (P₁ : Subgroup ↥(coreActionKernel L)).map (coreActionKernel L).subtype with hP₁'
  have hP₁'2 : IsPGroup 2 P₁' := P₁.isPGroup'.map (coreActionKernel L).subtype
  have hP₁'Q : P₁' ≤ coreActionKernel L := map_subtype_le _
  have hT₀P₁' : T₀ ≤ P₁' := fun x hx => ⟨⟨x, hT₀Q hx⟩, hT₀P₁ (mem_subgroupOf.mpr hx), rfl⟩
  obtain ⟨Y₁, hY₁, hLY₁, hY₁card⟩ := single_of_le hLq hP₁'2 hP₁'Q hT₀P₁' hY₀ hLY₀ hY₀card
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq ↥(coreActionKernel L) P₁ P
  have hyN : (y : G) ∈ normalizer (L : Set G) := (mem_coreActionKernel.mp y.2).1
  have hPeq : (P : Subgroup ↥(coreActionKernel L)).map (coreActionKernel L).subtype =
      P₁'.map (MulAut.conj (y : G)).toMonoidHom := by
    rw [← hy, map_smul_sylow]
  obtain ⟨h1, h2, h3⟩ := single_conj hyN hY₁ hLY₁ hY₁card
  rw [← hPeq] at h1 h2
  exact ⟨_, h1, h2, h3⟩

theorem star_of_isSolomonMember {L T : Subgroup G} (hL : IsSolomonMember L) (hT2 : IsPGroup 2 T)
    (hTQ : T ≤ coreActionKernel L) :
    twoLayerIn (L ⊓ centralizer (T : Set G)) ≤ twoLayerIn (centralizer (T : Set G)) := by
  have hLq := isQuasisimple_coreQuot_of_isSolomonMember hL
  obtain ⟨P, hTP⟩ := (hT2.comap_subtype (K := coreActionKernel L)).exists_le_sylow
  obtain ⟨Y, hY, hLY, -⟩ := single_of_sylow hL P
  set P' := (P : Subgroup ↥(coreActionKernel L)).map (coreActionKernel L).subtype with hP'
  have hP2 : IsPGroup 2 P' := P.isPGroup'.map (coreActionKernel L).subtype
  have hPQ : P' ≤ coreActionKernel L := map_subtype_le _
  have hTP' : T ≤ P' := fun x hx => ⟨⟨x, hTQ hx⟩, hTP (mem_subgroupOf.mpr hx), rfl⟩
  exact twoLayer_le_of_isPGroup hLq hP2 hPQ (hLY.trans (le_twoLayerIn_of_isTwoComponentIn hY))
    T hTP'

end CFSG.ComponentClassification.Foote5.SolMax
