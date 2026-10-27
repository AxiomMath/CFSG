module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76Transport
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Setting
public import CFSG.LocalAnalysis.ComponentClassification.Sol76StrongEmb

public section

namespace CFSG.ComponentClassification.Sol76

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer

theorem isKleinFour_map_mulEquiv {K K' : Type*} [Group K] [Group K'] (e : K ≃* K')
    {V : Subgroup K} (hV : IsKleinFour V) : IsKleinFour (V.map e.toMonoidHom) := by
  refine FooteLit.isKleinFour_of_card_eq_four ?_ fun x hx => ?_
  · rw [Subgroup.card_map_of_injective e.injective, hV.card_four]
  · obtain ⟨v, hv, rfl⟩ := hx
    rw [← map_pow, FooteLit.sq_eq_one_of_isKleinFour hV hv, map_one]

theorem isTwoDisconnected_of_mulEquiv {K K' : Type*} [Group K] [Group K'] (e : K ≃* K')
    (h : IsTwoDisconnected K) : IsTwoDisconnected K' := by
  obtain ⟨B, C, hB, hC, hBC⟩ := h
  refine ⟨B.map e.toMonoidHom, C.map e.toMonoidHom, isKleinFour_map_mulEquiv e hB,
    isKleinFour_map_mulEquiv e hC, fun hpath => hBC ?_⟩
  have hadj : ∀ X Y : Subgroup K',
      (IsKleinFour X ∧ IsKleinFour Y ∧ X ≤ centralizer (Y : Set K')) →
        IsKleinFour (X.map e.symm.toMonoidHom) ∧ IsKleinFour (Y.map e.symm.toMonoidHom) ∧
          X.map e.symm.toMonoidHom ≤
            centralizer ((Y.map e.symm.toMonoidHom : Subgroup K) : Set K) := by
    rintro X Y ⟨hX, hY, hXY⟩
    refine ⟨isKleinFour_map_mulEquiv e.symm hX, isKleinFour_map_mulEquiv e.symm hY, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    have h2 := (mem_centralizer_iff.mp (hXY hx)) y hy
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, h2]
  have h1 := Relation.ReflTransGen.lift
    (p := fun X Y : Subgroup K => IsKleinFour X ∧ IsKleinFour Y ∧ X ≤ centralizer (Y : Set K))
    (fun X : Subgroup K' => X.map e.symm.toMonoidHom) hadj _ _ hpath
  simp only [Function.onFun] at h1
  rwa [LocalCores.map_map_symm, LocalCores.map_map_symm] at h1

variable {G G' : Type} [Group G] [Group G'] (φ : G ≃* G')

theorem map_oddTwoCoreIn (H : Subgroup G) :
    (oddTwoCoreIn H).map φ.toMonoidHom = oddTwoCoreIn (H.map φ.toMonoidHom) := by
  set H' := H.map φ.toMonoidHom with hH'
  set e : ↥H ≃* ↥H' := H.equivMapOfInjective φ.toMonoidHom φ.injective with he
  have hO : (pPrimeCore 2 ↥H).map e.toMonoidHom = pPrimeCore 2 ↥H' := pPrimeCore_map_iso 2 e
  set eb : ↥H ⧸ pPrimeCore 2 ↥H ≃* ↥H' ⧸ pPrimeCore 2 ↥H' := QuotientGroup.congr _ _ e hO
    with heb
  have hP : (pCore 2 (↥H ⧸ pPrimeCore 2 ↥H)).map eb.toMonoidHom =
      pCore 2 (↥H' ⧸ pPrimeCore 2 ↥H') := pCore_map_iso 2 eb
  have heb_mk : ∀ y : ↥H, eb (QuotientGroup.mk y) = QuotientGroup.mk (e y) := fun y =>
    QuotientGroup.congr_mk _ _ e hO y
  have hsq : ((pCore 2 (↥H ⧸ pPrimeCore 2 ↥H)).comap
        (QuotientGroup.mk' (pPrimeCore 2 ↥H))).map e.toMonoidHom =
      (pCore 2 (↥H' ⧸ pPrimeCore 2 ↥H')).comap (QuotientGroup.mk' (pPrimeCore 2 ↥H')) := by
    rw [← hP]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨QuotientGroup.mk y, hy, heb_mk y⟩
    · rintro ⟨q, hq, hqx⟩
      refine ⟨e.symm x, ?_, by simp⟩
      have h1 : eb (QuotientGroup.mk (e.symm x)) = eb q := by
        rw [heb_mk, MulEquiv.apply_symm_apply]
        exact hqx.symm
      change QuotientGroup.mk (e.symm x) ∈ pCore 2 (↥H ⧸ pPrimeCore 2 ↥H)
      rw [eb.injective h1]
      exact hq
  have hsub : φ.toMonoidHom.comp H.subtype = H'.subtype.comp e.toMonoidHom := by
    ext x
    rfl
  rw [oddTwoCoreIn, oddTwoCoreIn, ← hsq, Subgroup.map_map, Subgroup.map_map, hsub]

variable [Finite G] [Finite G']

theorem isKBalanced_map {N : Subgroup G} (h : IsKBalanced N) :
    IsKBalanced (N.map φ.toMonoidHom) := by
  obtain ⟨r, K, hinj, hiff, h2, hcomm, hrank, h3⟩ := h
  have hcore : ∀ X : Subgroup G,
      ((oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel X).map φ.toMonoidHom =
        (oddTwoCoreIn (N.map φ.toMonoidHom) ⊔ twoLayerIn (N.map φ.toMonoidHom)) ⊓
          coreActionKernel (X.map φ.toMonoidHom) := by
    intro X
    rw [Subgroup.map_inf_eq _ _ _ φ.injective, Subgroup.map_sup, map_oddTwoCoreIn,
      map_twoLayerIn, map_coreActionKernel]
  refine ⟨r, fun i => (K i).map φ.toMonoidHom, fun i j hij =>
    hinj (Subgroup.map_injective φ.injective hij), fun J => ?_, h2, fun i j hij => ?_, ?_, ?_⟩
  · constructor
    · rintro ⟨hJ, hJs⟩
      have h1 := isTwoComponentIn_map φ.symm hJ
      rw [LocalCores.map_map_symm] at h1
      obtain ⟨i, hi⟩ := (hiff _).mp ⟨h1, map_mem_solomonKStar φ.symm hJs⟩
      refine ⟨i, ?_⟩
      change (K i).map φ.toMonoidHom = J
      rw [hi]
      simpa using LocalCores.map_map_symm φ.symm J
    · rintro ⟨i, rfl⟩
      obtain ⟨hKi, hKis⟩ := (hiff (K i)).mpr ⟨i, rfl⟩
      exact ⟨isTwoComponentIn_map φ hKi, map_mem_solomonKStar φ hKis⟩
  · change ⁅(K i).map φ.toMonoidHom, (K j).map φ.toMonoidHom⁆ ≤ _
    rw [← Subgroup.map_commutator, ← map_oddCoreIn]
    exact map_mono (hcomm i j hij)
  · obtain ⟨i, hi⟩ := hrank
    refine ⟨i, ?_⟩
    change 3 ≤ CFSG.pRank 2 ↥((oddTwoCoreIn (N.map φ.toMonoidHom) ⊔
      twoLayerIn (N.map φ.toMonoidHom)) ⊓ coreActionKernel ((K i).map φ.toMonoidHom))
    rw [← hcore, pRank_map]
    exact hi
  · rcases h3 with h3 | h3 | ⟨h3a, h3b, h3c⟩
    · exact Or.inl h3
    · refine Or.inr (Or.inl ?_)
      rw [← map_solomonKStarOf, ← hcore, pRank_map]
      exact h3
    · refine Or.inr (Or.inr ⟨?_, ?_, fun hs => ?_⟩)
      · change 3 ≤ CFSG.pRank 2 ↥((K ⟨0, by omega⟩).map φ.toMonoidHom)
        rw [pRank_map]
        exact h3a
      · change 3 ≤ CFSG.pRank 2 ↥((K ⟨1, h2⟩).map φ.toMonoidHom)
        rw [pRank_map]
        exact h3b
      · set e₀ := (K ⟨0, by omega⟩).equivMapOfInjective φ.toMonoidHom φ.injective
        set e₁ := (K ⟨1, h2⟩).equivMapOfInjective φ.toMonoidHom φ.injective
        have hs' : HasStronglyEmbedded ↥(K ⟨0, by omega⟩) ∨ HasStronglyEmbedded ↥(K ⟨1, h2⟩) :=
          hs.imp (hasStronglyEmbedded_of_mulEquiv e₀.symm)
            (hasStronglyEmbedded_of_mulEquiv e₁.symm)
        obtain ⟨hd0, hd1⟩ := h3c hs'
        exact ⟨isTwoDisconnected_of_mulEquiv e₀ hd0, isTwoDisconnected_of_mulEquiv e₁ hd1⟩

theorem kStarComponents_map (N : Subgroup G) :
    kStarComponents (N.map φ.toMonoidHom) =
      (fun J : Subgroup G => J.map φ.toMonoidHom) '' kStarComponents N := by
  ext J'
  constructor
  · rintro ⟨hJ', hJ's⟩
    refine ⟨J'.map φ.symm.toMonoidHom, ⟨?_, map_mem_solomonKStar φ.symm hJ's⟩, ?_⟩
    · have h1 := isTwoComponentIn_map φ.symm hJ'
      rwa [LocalCores.map_map_symm] at h1
    · simpa using LocalCores.map_map_symm φ.symm J'
  · rintro ⟨J, ⟨hJ, hJs⟩, rfl⟩
    exact ⟨isTwoComponentIn_map φ hJ, map_mem_solomonKStar φ hJs⟩

theorem map_kStarKernel (N : Subgroup G) :
    (kStarKernel N).map φ.toMonoidHom = kStarKernel (N.map φ.toMonoidHom) := by
  rw [kStarKernel, kStarKernel, Subgroup.map_inf_eq _ _ _ φ.injective, map_coreActionKernel,
    map_solomonKStarOf]

theorem kStarMeasure_map (N : Subgroup G) :
    kStarMeasure (N.map φ.toMonoidHom) = kStarMeasure N := by
  rw [kStarMeasure, kStarMeasure, kStarComponents_map,
    Set.ncard_image_of_injective _ (Subgroup.map_injective φ.injective), ← map_kStarKernel,
    pRank_map, Subgroup.card_map_of_injective φ.injective]

theorem isSolomonChoice_map {N : Subgroup G} (h : IsSolomonChoice N) :
    IsSolomonChoice (N.map φ.toMonoidHom) := by
  have htop : ∀ (X Y : Type) [Group X] [Group Y] [Finite X] [Finite Y] (ψ : X ≃* Y),
      (solomonKStarOf (⊤ : Subgroup X)).map ψ.toMonoidHom = solomonKStarOf (⊤ : Subgroup Y) := by
    intro X Y _ _ _ _ ψ
    rw [map_solomonKStarOf, Subgroup.map_top_of_surjective _ ψ.surjective]
  refine ⟨isKBalanced_map φ h.1, fun hle => h.2.1 ?_, fun N' hN' hv => ?_⟩
  · rw [← map_solomonKStarOf, ← htop G G' φ] at hle
    exact (Subgroup.map_le_map_iff_of_injective φ.injective).mp hle
  · have hN'' : (N'.map φ.symm.toMonoidHom).map φ.toMonoidHom = N' := by
      simpa using LocalCores.map_map_symm φ.symm N'
    have hv' : ¬ solomonKStarOf (N'.map φ.symm.toMonoidHom) ≤ solomonKStarOf (⊤ : Subgroup G) := by
      intro hle
      apply hv
      have h1 := map_mono (f := φ.toMonoidHom) hle
      rwa [map_solomonKStarOf, hN'', htop G G' φ] at h1
    have h1 := h.2.2 _ (isKBalanced_map φ.symm hN') hv'
    rw [kStarMeasure_map φ.symm N'] at h1
    rw [kStarMeasure_map φ N]
    exact h1

theorem isSolomonChoice_conjugate {N : Subgroup G} (h : IsSolomonChoice N) (g : G) :
    IsSolomonChoice (conjugate N g) :=
  isSolomonChoice_map (MulAut.conj g⁻¹) h

theorem kStarComponents_conjugate (N : Subgroup G) (g : G) :
    kStarComponents (conjugate N g) = (fun J : Subgroup G => conjugate J g) '' kStarComponents N :=
  kStarComponents_map (MulAut.conj g⁻¹) N

end CFSG.ComponentClassification.Sol76
