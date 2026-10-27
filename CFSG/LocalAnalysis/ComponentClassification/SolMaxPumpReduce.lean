module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78Inputs
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Lemma212Steps
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafL34Fixed
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafL34Swap

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup CFSG.ComponentClassification.CatLeaf

@[expose] def AltPumpOutcome (S : Type) [Group S] (m : ℕ) : Prop :=
  (∃ n : ℕ, Odd n ∧ m ≤ n ∧ Nonempty (S ≃* alternatingGroup (Fin n))) ∨
    (m = 7 ∧ Nonempty (S ≃* Blueprint.NativeSporadic.He))

@[expose] def AltPumpLeaf : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ x y : S, x * y ≠ y * x) →
    Blueprint.Catalog S → ∀ (σ : MulAut S) (P : Subgroup S), ProperFixedComponent σ P →
    Open.fusionZStar ↥P = pPrimeCore 2 ↥P → ∀ m : ℕ, Odd m → 7 ≤ m →
    Nonempty (↥P ⧸ Open.fusionZStar ↥P ≃* alternatingGroup (Fin m)) → AltPumpOutcome S m

@[expose] def AltPumpSporadicClause : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ x y : S, x * y ≠ y * x) →
    ∀ s : TauCeti.SporadicName, s ≠ .He → Nonempty (S ≃* Blueprint.NativeSporadic.Carrier s) →
    ∀ (σ : MulAut S) (P : Subgroup S), ProperFixedComponent σ P →
    Open.fusionZStar ↥P = pPrimeCore 2 ↥P → ∀ m : ℕ, Odd m → 7 ≤ m →
    Nonempty (↥P ⧸ Open.fusionZStar ↥P ≃* alternatingGroup (Fin m)) → False

theorem fusionZStar_eq_pPrimeCore_of_image {M : Type*} [Group M] [Finite M] {T : Subgroup M}
    [Group.IsPerfect T] (hTq : IsQuasisimple (T ⧸ pPrimeCore 2 T))
    (hZ : ∀ t : T, t ∈ Open.fusionZStar T →
      ∃ o : T, o ∈ pPrimeCore 2 T ∧ ((o⁻¹ * t : T) : M) ∈ Open.fusionZStar M)
    (hPO : pPrimeCore 2 ↥((T.map (QuotientGroup.mk' (pPrimeCore 2 M))).map
      (QuotientGroup.mk' (center (M ⧸ pPrimeCore 2 M)))) ≠ ⊤) :
    Open.fusionZStar ↥((T.map (QuotientGroup.mk' (pPrimeCore 2 M))).map
        (QuotientGroup.mk' (center (M ⧸ pPrimeCore 2 M)))) =
      pPrimeCore 2 ↥((T.map (QuotientGroup.mk' (pPrimeCore 2 M))).map
        (QuotientGroup.mk' (center (M ⧸ pPrimeCore 2 M)))) := by
  classical
  set π := QuotientGroup.mk' (pPrimeCore 2 M) with hπ
  set π₂ := QuotientGroup.mk' (center (M ⧸ pPrimeCore 2 M)) with hπ₂
  set P := (T.map π).map π₂ with hP
  let f : T →* P := ((π₂.comp π).comp T.subtype).codRestrict P fun t =>
    mem_map_of_mem π₂ (mem_map_of_mem π t.2)
  have hf : Function.Surjective f := by
    rintro ⟨q, hq⟩
    obtain ⟨y, hy, rfl⟩ := hq
    obtain ⟨t, ht, rfl⟩ := hy
    exact ⟨⟨t, ht⟩, rfl⟩
  have hfapp : ∀ t : T, ((f t : P) : (M ⧸ pPrimeCore 2 M) ⧸ center (M ⧸ pPrimeCore 2 M)) =
      π₂ (π t) := fun t => rfl
  have hcomap := GrSLit.comap_fusionZStar_of_surjective' f hf hTq hPO
  have hZM : ∀ w : M, w ∈ Open.fusionZStar M → π₂ (π w) = 1 := by
    intro w hw
    rw [Sol78.fusionZStar_eq_comap, mem_comap] at hw
    rw [hπ₂, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hw
  apply le_antisymm _ (Sol78.pPrimeCore_le_fusionZStar _)
  intro z hz
  obtain ⟨t, rfl⟩ := hf z
  have ht : t ∈ Open.fusionZStar T := by
    rw [← hcomap]
    exact hz
  obtain ⟨o, ho, hw⟩ := hZ t ht
  have h1 : f t = f o := by
    have h2 : f (o⁻¹ * t) = 1 := by
      apply Subtype.ext
      rw [hfapp]
      exact hZM _ hw
    calc f t = f o * f (o⁻¹ * t) := by rw [← map_mul, mul_inv_cancel_left]
      _ = f o := by rw [h2, mul_one]
  rw [h1]
  exact GrSLit.map_pPrimeCore_le_pPrimeCore f hf (mem_map_of_mem f ho)

theorem alternatingPumpUpInput_of_leaf (hleaf : AltPumpLeaf) : Sol78.AlternatingPumpUpInput := by
  intro H _ _ hK M hM x hx hxN T hTM hTC hTpc hZ m hm hm7 ⟨eT⟩
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMx : conjugate M x = M := mem_normalizer_iff_map_conj_eq.mp (inv_mem hxN)
  have hTC' : T ≤ (M ⊔ conjugate M x) ⊓ centralizer ({x} : Set H) := by
    rw [hMx, sup_idem]
    exact le_inf hTM hTC
  have hTpc' : IsPComponent 2 (T.subgroupOf ((M ⊔ conjugate M x) ⊓ centralizer ({x} : Set H))) :=
    CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hTC' inf_le_right hTpc
  obtain ⟨hle, -, heq⟩ := UnbalancedGS.involution_orbit_fixed_component_quotient_comparison hx M
    hM _ rfl _ rfl T hTC' hTpc'
  have : Group.IsPerfect T := by
    have := CatalogueBHeldSmallCore.pComponent_perfect 2 _ hTpc
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hTC).toMonoidHom)
      (subgroupOfEquivOfLe hTC).surjective
  have hTq : IsQuasisimple (T ⧸ pPrimeCore 2 T) :=
    CatalogueBPrimeJoin.quasisimple_primeCore_quotient_of_equiv 2 (subgroupOfEquivOfLe hTC)
      (CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple 2 _ hTpc)
  rcases hle.lt_or_eq with hlt | hidx
  swap
  ·
    obtain ⟨e⟩ := stable_case_type hM hTM hTq ((heq hidx).2 hMx.symm)
    exact Or.inl ⟨m, hm, le_rfl, ⟨e.symm.trans eT⟩⟩
  have hTM' : T ≤ M ⊓ centralizer ({x} : Set H) := le_inf hTM hTC
  have hTp' : IsPComponent 2 (T.subgroupOf (M ⊓ centralizer ({x} : Set H))) :=
    CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hTM' inf_le_right hTpc
  obtain ⟨σ, hPF, ⟨eP⟩⟩ := exists_properFixedComponent_of_stable_image hx hM hMx hTM' hTp' hlt
  have hMq : IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M) :=
    ((CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 M).mp hM).2.2
  have : IsSimpleGroup ((↥M ⧸ pPrimeCore 2 ↥M) ⧸ center (↥M ⧸ pPrimeCore 2 ↥M)) := hMq.2.1
  have hna := hMq.2.2
  have hcat : Blueprint.Catalog ((↥M ⧸ pPrimeCore 2 ↥M) ⧸ center (↥M ⧸ pPrimeCore 2 ↥M)) :=
    SectionRank.catalog_of_isKGroupCat_of_surjective hK M
      ((QuotientGroup.mk' (center (↥M ⧸ pPrimeCore 2 ↥M))).comp
        (QuotientGroup.mk' (pPrimeCore 2 ↥M)))
      ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
  set T' := T.subgroupOf M with hT'def
  let eTT : ↥T' ≃* ↥T := subgroupOfEquivOfLe hTM
  have : Group.IsPerfect T' := Group.IsPerfect.ofSurjective (f := eTT.symm.toMonoidHom)
    eTT.symm.surjective
  have hT'q : IsQuasisimple (T' ⧸ pPrimeCore 2 T') :=
    LocalCores.isQuasisimple_of_mulEquiv (Sol78.coreQuotCongr eTT).symm hTq
  have hZ' : ∀ t : T', t ∈ Open.fusionZStar T' →
      ∃ o : T', o ∈ pPrimeCore 2 T' ∧ ((o⁻¹ * t : T') : M) ∈ Open.fusionZStar M := by
    intro t ht
    have ht' : eTT t ∈ Open.fusionZStar T := by
      rw [← FooteLit.fusionZStar_map_mulEquiv eTT]
      exact mem_map_of_mem _ ht
    have hmem := hZ (mem_map_of_mem T.subtype ht')
    have hnorm : (pPrimeCore 2 ↥T).map T.subtype ≤
        normalizer (((Open.fusionZStar ↥M).map M.subtype : Subgroup H) : Set H) := by
      rintro _ ⟨o, -, rfl⟩
      rw [mem_normalizer_iff]
      intro y
      have hoM : ((o : T) : H) ∈ M := hTM o.2
      have hN : (Open.fusionZStar ↥M).Normal := by
        rw [Sol78.fusionZStar_eq_comap]
        exact Normal.comap inferInstance _
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨⟨o, hoM⟩ * w * ⟨o, hoM⟩⁻¹, hN.conj_mem w hw _, by simp⟩
      · rintro ⟨w, hw, hwe⟩
        refine ⟨⟨o, hoM⟩⁻¹ * w * ⟨o, hoM⟩, ?_, ?_⟩
        · have := hN.conj_mem w hw ⟨o, hoM⟩⁻¹
          rwa [inv_inv] at this
        · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hwe ⊢
          rw [hwe]
          group
    rw [sup_comm] at hmem
    obtain ⟨w, hw, o, ho, hwo⟩ := Sol76.exists_mul_of_mem_sup_normalizer hnorm hmem
    obtain ⟨o₀, ho₀, rfl⟩ := ho
    obtain ⟨w₀, hw₀, rfl⟩ := hw
    refine ⟨eTT.symm o₀, ?_, ?_⟩
    · rw [← pPrimeCore_map_iso 2 eTT.symm]
      exact mem_map_of_mem _ ho₀
    · have hval : (((eTT.symm o₀)⁻¹ * t : T') : M) = ⟨(o₀ : H)⁻¹ * (w₀ : H) * (o₀ : H),
          mul_mem (mul_mem (inv_mem (hTM o₀.2)) w₀.2) (hTM o₀.2)⟩ := by
        apply Subtype.ext
        have h1 : ((eTT t : T) : H) = (w₀ : H) * (o₀ : H) := hwo
        have h2 : (((eTT.symm o₀ : T') : M) : H) = (o₀ : H) := rfl
        have h3 : (((t : T') : M) : H) = ((eTT t : T) : H) := rfl
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, h2, h3, h1]
        group
      rw [hval]
      have hN : (Open.fusionZStar ↥M).Normal := by
        rw [Sol78.fusionZStar_eq_comap]
        exact Normal.comap inferInstance _
      have := hN.conj_mem w₀ hw₀ ⟨o₀, hTM o₀.2⟩⁻¹
      convert this using 1
      apply Subtype.ext
      simp
  have hPO : pPrimeCore 2 ↥((T'.map (QuotientGroup.mk' (pPrimeCore 2 ↥M))).map
      (QuotientGroup.mk' (center (↥M ⧸ pPrimeCore 2 ↥M)))) ≠ ⊤ := by
    intro htop
    have hZtop : Open.fusionZStar ↥((T'.map (QuotientGroup.mk' (pPrimeCore 2 ↥M))).map
        (QuotientGroup.mk' (center (↥M ⧸ pPrimeCore 2 ↥M)))) = ⊤ :=
      eq_top_iff.mpr (htop ▸ Sol78.pPrimeCore_le_fusionZStar _)
    have e1 := eP.symm.trans eT
    have : Subsingleton (alternatingGroup (Fin m)) := by
      have hs : Subsingleton (↥((T'.map (QuotientGroup.mk' (pPrimeCore 2 ↥M))).map
          (QuotientGroup.mk' (center (↥M ⧸ pPrimeCore 2 ↥M)))) ⧸ Open.fusionZStar
          ↥((T'.map (QuotientGroup.mk' (pPrimeCore 2 ↥M))).map
          (QuotientGroup.mk' (center (↥M ⧸ pPrimeCore 2 ↥M))))) :=
        QuotientGroup.subsingleton_iff.mpr hZtop
      exact e1.symm.toEquiv.subsingleton
    have : Nontrivial (alternatingGroup (Fin m)) :=
      alternatingGroup.nontrivial_of_three_le_card (by rw [Nat.card_fin]; omega)
    exact false_of_nontrivial_of_subsingleton (alternatingGroup (Fin m))
  have hPex := fusionZStar_eq_pPrimeCore_of_image hT'q hZ' hPO
  obtain ⟨eMS⟩ := GrSLit.nonempty_quotient_center_equiv_fusionZStar ↥M
  rcases hleaf _ inferInstance hna hcat σ _ hPF hPex m hm hm7 ⟨eP.symm.trans eT⟩ with
    ⟨n, hn, hmn, ⟨eS⟩⟩ | ⟨h7, ⟨eS⟩⟩
  · exact Or.inl ⟨n, hn, hmn, ⟨eMS.symm.trans eS⟩⟩
  · exact Or.inr ⟨h7, ⟨eMS.symm.trans eS⟩⟩

end CFSG.ComponentClassification.SolMax
