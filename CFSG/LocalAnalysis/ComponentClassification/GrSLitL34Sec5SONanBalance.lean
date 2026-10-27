module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SONanConfig
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SONanRank
public import CFSG.GH74.GLS.C3.Layer1.Thm1Layer
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
public import CFSG.GroupTheory.SubgroupOfLattice
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SONanEmbed
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.ComponentClassification.Foote5SolIdent
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsTransfer
public import CFSG.LocalAnalysis.ComponentClassification.Sol76RankOneClassPoint
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.FooteLit
open CFSG.Blueprint.NativeSporadic (IsSporadic)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ONPar
open scoped commutatorElement

theorem mem_solomonKStar_of_onan_setting
    {G : Type} [Group G] [Finite G] {t : G} {P W : Subgroup G} (hc : ONanWConfig G t P W) :
    P ∈ FooteLit.solomonKStar G := by
  have hbase := hc.base
  have ht2 := hc.order_two
  have hPt := hc.le_centralizer
  have hPp := hc.isPComponent
  have hML := hc.mirror
  have hPON := hc.isSporadic
  have := hbase.1
  have hJ : FooteLit.IsTwoComponentIn P (centralizer ({t} : Set G)) := ⟨hPt, hPp⟩
  have htop : GeneralizedFitting.subgroup G = ⊤ := GSLit.generalizedFitting_eq_top_of_simple
  let eF : GeneralizedFitting.subgroup G ≃* G := (MulEquiv.subgroupCongr htop).trans topEquiv
  have hsF : IsSimpleGroup (GeneralizedFitting.subgroup G) := eF.isSimpleGroup
  have hnF : ∃ u v : GeneralizedFitting.subgroup G, u * v ≠ v * u := by
    obtain ⟨u, v, huv⟩ := hbase.2.1
    exact ⟨eF.symm u, eF.symm v, fun h => huv (eF.symm.injective (by rw [map_mul, map_mul, h]))⟩
  refine ⟨Foote5.SolMax.isSolomonMaximal_of_gsMirrorMaximal hsF hnF ht2 hJ hML,
    Sol76.isSolomonMember_of_isTwoComponentIn_centralizer ht2 hJ, fun K hK => ?_⟩
  obtain ⟨e'⟩ := Sol76.nonempty_fusionZStar_equiv_of_reflTransGen hK.2
  obtain ⟨f⟩ := hPON
  exact le_trans (by norm_num) (three_le_pRank_of_sporadic_onan_fusionZStar ⟨e'.symm.trans f⟩)

theorem isKBalanced_of_two {X : Type} [Group X] [Finite X] {N K₁ K₂ : Subgroup X}
    (h₁ : FooteLit.IsTwoComponentIn K₁ N) (h₂ : FooteLit.IsTwoComponentIn K₂ N)
    (hs₁ : K₁ ∈ FooteLit.solomonKStar X) (hs₂ : K₂ ∈ FooteLit.solomonKStar X) (hne : K₁ ≠ K₂)
    (hr₁ : 3 ≤ CFSG.pRank 2 ↥K₁) (hr₂ : 3 ≤ CFSG.pRank 2 ↥K₂)
    (he₁ : ¬ FooteLit.HasStronglyEmbedded ↥K₁) (he₂ : ¬ FooteLit.HasStronglyEmbedded ↥K₂) :
    FooteLit.IsKBalanced N := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S : Set (Subgroup X) := {K | FooteLit.IsTwoComponentIn K N ∧ K ∈ FooteLit.solomonKStar X}
    with hSdef
  have hSfin : S.Finite := Set.toFinite S
  set s := hSfin.toFinset with hs
  have hK₁s : K₁ ∈ s := hSfin.mem_toFinset.mpr ⟨h₁, hs₁⟩
  have hK₂s : K₂ ∈ s := hSfin.mem_toFinset.mpr ⟨h₂, hs₂⟩
  have hr : 2 ≤ s.card := Finset.one_lt_card.mpr ⟨K₁, hK₁s, K₂, hK₂s, hne⟩
  set ee := s.equivFin.symm with hee
  set Kf : Fin s.card → Subgroup X := fun i => ((ee i : s) : Subgroup X) with hKf
  have hKfS : ∀ i, Kf i ∈ S := fun i => hSfin.mem_toFinset.mp (ee i).2
  refine ⟨s.card, Kf, fun i j hij => ee.injective (Subtype.ext hij), fun K => ⟨fun hK => ?_, ?_⟩,
    hr, fun i j hij => ?_, ?_, ?_⟩
  · refine ⟨ee.symm ⟨K, hSfin.mem_toFinset.mpr hK⟩, ?_⟩
    simp only [hKf, Equiv.apply_symm_apply]
  · rintro ⟨i, rfl⟩
    exact hKfS i
  · exact FooteLit.commutator_le_oddCoreIn_of_ne (hKfS i).1 (hKfS j).1
      (fun h => hij (ee.injective (Subtype.ext h)))
  ·
    refine ⟨ee.symm ⟨K₁, hK₁s⟩, ?_⟩
    have hKi : Kf (ee.symm ⟨K₁, hK₁s⟩) = K₁ := by simp only [hKf, Equiv.apply_symm_apply]
    rw [hKi]
    have hle : K₂ ≤ (FooteLit.oddTwoCoreIn N ⊔ FooteLit.twoLayerIn N) ⊓ coreActionKernel K₁ :=
      le_inf ((FooteLit.le_twoLayerIn_of_isTwoComponentIn h₂).trans le_sup_right)
        (GSThmB.B5a.le_coreActionKernel_of_ne h₁.1 h₂.1 h₁.2 h₂.2 hne)
    exact hr₂.trans (Sol78.pRank_le_of_le hle)
  ·
    by_cases h3 : 3 ≤ s.card
    · exact Or.inl h3
    · right; right
      have hsub : ({K₁, K₂} : Finset (Subgroup X)) ⊆ s := by
        intro K hK
        rw [Finset.mem_insert, Finset.mem_singleton] at hK
        rcases hK with rfl | rfl
        · exact hK₁s
        · exact hK₂s
      have hseq : ({K₁, K₂} : Finset (Subgroup X)) = s :=
        Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair hne]; omega)
      have hgood : ∀ i, 3 ≤ CFSG.pRank 2 ↥(Kf i) ∧ ¬ FooteLit.HasStronglyEmbedded ↥(Kf i) := by
        intro i
        have hi : Kf i ∈ ({K₁, K₂} : Finset (Subgroup X)) := by rw [hseq]; exact (ee i).2
        rw [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with hi | hi
        · rw [hi]
          exact ⟨hr₁, he₁⟩
        · rw [hi]
          exact ⟨hr₂, he₂⟩
      exact ⟨(hgood _).1, (hgood _).1, fun h => (h.elim (hgood _).2 (hgood _).2).elim⟩

private lemma map_conj_comp_conj_inv {X : Type*} [Group X] (L : Subgroup X) (g : X) :
    (L.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = L := by
  rw [Subgroup.map_map]
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private lemma map_conj_inv_comp_conj {X : Type*} [Group X] (L : Subgroup X) (g : X) :
    (L.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = L := by
  rw [Subgroup.map_map]
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private lemma map_conj_eq_iff_map_conj_inv_eq {X : Type*} [Group X] (L : Subgroup X) (g : X) :
    L.map (MulAut.conj g).toMonoidHom = L ↔ L.map (MulAut.conj g⁻¹).toMonoidHom = L := by
  constructor
  · intro h
    have h1 := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) h
    rw [map_conj_comp_conj_inv] at h1
    exact h1.symm
  · intro h
    have h1 := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) h
    rw [map_conj_inv_comp_conj] at h1
    exact h1.symm


private theorem le_of_perfect_le_sup {X : Type*} [Group X] {J C N : Subgroup X}
    (hJ : ⁅J, J⁆ = J) (hCN : C ≤ normalizer (N : Set X))
    (hC : Group.IsSolvable ↥C) (hJCN : J ≤ C ⊔ N) : J ≤ N := by
  by_contra hJN
  let _ : Group.IsSolvable ↥C := hC
  set M : Subgroup X := C ⊔ N with hM
  have hMN : M ≤ normalizer (N : Set X) := sup_le hCN le_normalizer
  have hNM : N ≤ M := le_sup_right
  have : (N.subgroupOf M).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mpr hMN
  set π := QuotientGroup.mk' (N.subgroupOf M) with hπ
  have hsurj : Function.Surjective (π.comp (Subgroup.inclusion (le_sup_left : C ≤ M))) := by
    intro q
    obtain ⟨⟨m, hm⟩, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf M) q
    have hm' := hm
    rw [hM, ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right C N hCN] at hm'
    obtain ⟨c, hc, n, hn, rfl⟩ := hm'
    refine ⟨⟨c, hc⟩, ?_⟩
    rw [MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    show ((Subgroup.inclusion le_sup_left ⟨c, hc⟩ : M)⁻¹ * ⟨c * n, hm⟩ : M) ∈ N.subgroupOf M
    rw [Subgroup.mem_subgroupOf]
    simpa using hn
  have hsol : Group.IsSolvable (↥M ⧸ N.subgroupOf M) :=
    Group.isSolvable_of_surjective hsurj
  have hJM : J ≤ M := by
    rw [hM]
    exact hJCN
  set ψ := π.comp (Subgroup.inclusion hJM) with hψ
  have : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.mpr hJ
  have hperf : Group.IsPerfect ψ.range := Group.IsPerfect.range ψ
  have hsolr : Group.IsSolvable ψ.range := inferInstance
  have hsub : Subsingleton ψ.range := by
    by_contra hn
    rw [not_subsingleton_iff_nontrivial] at hn
    have : Nontrivial ψ.range := hn
    exact Group.IsPerfect.not_isSolvable (G := ψ.range) hsolr
  have hJN' : J ≤ N := by
    intro x hx
    have h1 : ψ ⟨x, hx⟩ = 1 := by
      have := Subsingleton.elim (⟨ψ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩ : ψ.range) 1
      exact congrArg Subtype.val this
    rw [hψ, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at h1
    exact h1
  exact hJN hJN'

theorem exists_twoComponent_solomonEquiv_of_onan
    {G : Type} [Group G] [Finite G] {t : G} {P W M : Subgroup G} (hc : ONanWConfig G t P W)
    (hM : M = normalizer (W : Set G)) (htM : t ∈ M)
    {L : Subgroup (↥M ⧸ pPrimeCore 2 ↥M)} (hL : IsComponent L) (hZ : center ↥L = ⊥)
    (hLON : IsSporadic ↥L .ONan)
    (hPL : (P.subgroupOf M).map (QuotientGroup.mk' (pPrimeCore 2 ↥M)) = L)
    (hcent : ∀ x ∈ L, QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨t, htM⟩ * x =
      x * QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨t, htM⟩) :
    ∃ K : Subgroup G, FooteLit.IsTwoComponentIn K M ∧
      (K.subgroupOf M).map (QuotientGroup.mk' (pPrimeCore 2 ↥M)) = L ∧
      IsSporadic (↥K ⧸ pPrimeCore 2 ↥K) .ONan ∧ FooteLit.SolomonEquiv P K := by
  classical
  have hZuse := hZ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π : ↥M →* (↥M ⧸ pPrimeCore 2 ↥M) := QuotientGroup.mk' (pPrimeCore 2 ↥M)
  let O : Subgroup ↥M := pPrimeCore 2 ↥M
  obtain ⟨K₀, hK₀p, hK₀map⟩ :=
    GH74.GLS.C3.Layer1.Thm1.exists_pComponent_of_quotient_component hL
  let K : Subgroup G := K₀.map M.subtype
  have hKsub : K.subgroupOf M = K₀ := CFSG.subgroupOf_map_subtype_eq K₀
  have hKM : K ≤ M := by rintro _ ⟨x, -, rfl⟩; exact x.2
  have hK : FooteLit.IsTwoComponentIn K M := ⟨hKM, by rw [hKsub]; exact hK₀p⟩
  have hKmap : (K.subgroupOf M).map π = L := by
    rw [hKsub]
    simpa only [π] using hK₀map
  have hPM : P ≤ M := by rw [hM]; exact hc.le_normalizer'
  have hPsub : P.subgroupOf M ≤ K₀ := by
    have hPle : P.subgroupOf M ≤ O ⊔ K₀ := by
      intro x hx
      have hxP : (x : G) ∈ P := Subgroup.mem_subgroupOf.mp hx
      have hxL : π x ∈ L := by
        have h1 : π x ∈ (P.subgroupOf M).map π := Subgroup.mem_map_of_mem π hx
        have h2 : (P.subgroupOf M).map π = L := by simpa only [π] using hPL
        rwa [h2] at h1
      have hxK : π x ∈ K₀.map π := by
        have h2 : K₀.map π = L := by simpa only [π] using hK₀map
        rw [h2]
        exact hxL
      obtain ⟨k, hk, hkπ⟩ := Subgroup.mem_map.mp hxK
      have hker : π (k⁻¹ * x) = 1 := by
        rw [map_mul, map_inv, hkπ]
        group
      have hxO : k⁻¹ * x ∈ O := by
        have h1 : k⁻¹ * x ∈ (QuotientGroup.mk' O).ker := MonoidHom.mem_ker.mpr hker
        rwa [QuotientGroup.ker_mk'] at h1
      have hxeq : x = k * (k⁻¹ * x) := by group
      rw [hxeq]
      simpa only [sup_comm] using Subgroup.mul_mem_sup hk hxO
    have hJperf : ⁅P.subgroupOf M, P.subgroupOf M⁆ = P.subgroupOf M := by
      have hperf : Group.IsPerfect ↥(P.subgroupOf M) :=
        @Group.IsPerfect.ofSurjective ↥P ↥(P.subgroupOf M) _ _
          (subgroupOfEquivOfLe hPM).symm.toMonoidHom hc.isPerfect
          (subgroupOfEquivOfLe hPM).symm.surjective
      exact Subgroup.isPerfect_iff.mp hperf
    have hOsolv : Group.IsSolvable ↥O :=
      CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.coprime_two_left.mp
        (pPrimeCore_coprime_card (G := ↥M) (p := 2)))
    exact le_of_perfect_le_sup hJperf (pPrimeCore_le_normalizer hK₀p) hOsolv hPle
  have hPK : P ≤ K := (subgroupOf_le_iff_le_map_subtype hPM).mp hPsub
  let tM : ↥M := ⟨t, htM⟩
  let u : ↥M ⧸ pPrimeCore 2 ↥M := QuotientGroup.mk' (pPrimeCore 2 ↥M) tM
  have huL : L.map (MulAut.conj u⁻¹).toMonoidHom = L := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hcomm : u * z = z * u := hcent z hz
      have hzu : u⁻¹ * z * u = z := by
        calc u⁻¹ * z * u = u⁻¹ * (z * u) := by group
          _ = u⁻¹ * (u * z) := by rw [← hcomm]
          _ = z := by group
      have hz' : (MulAut.conj u⁻¹) z = z := by simpa [MulAut.conj_apply] using hzu
      change (MulAut.conj u⁻¹) z ∈ L
      rwa [hz']
    · intro hy
      have hcomm : u * y = y * u := hcent y hy
      have hyu : u⁻¹ * y * u = y := by
        calc u⁻¹ * y * u = u⁻¹ * (y * u) := by group
          _ = u⁻¹ * (u * y) := by rw [← hcomm]
          _ = y := by group
      exact ⟨y, hy, by simpa [MulAut.conj_apply] using hyu⟩
  have hKt : FooteLit.IsTwoComponentIn (conjugate K t) M := by
    have hh : t⁻¹ ∈ Subgroup.normalizer (M : Set G) := Subgroup.le_normalizer (inv_mem htM)
    simpa [CFSG.conjugate] using Sol76.isTwoComponentIn_map_conj hK hh
  have hKtmap : ((conjugate K t).subgroupOf M).map π = L := by
    have hsub : (conjugate K t).subgroupOf M = conjugate (K.subgroupOf M) tM := by
      simpa [CFSG.conjugate] using
        (CFSG.GroupTheory.conjugate_subgroupOf (B := K) (U := M) tM).symm
    calc
      ((conjugate K t).subgroupOf M).map π = (conjugate (K.subgroupOf M) tM).map π := by rw [hsub]
      _ = conjugate ((K.subgroupOf M).map π) (π tM) := map_conjugate π (K.subgroupOf M) tM
      _ = conjugate L u := by rw [hKmap]
      _ = L := by simpa [CFSG.conjugate] using huL
  have hKeq : K = conjugate K t := by
    have heq : K.subgroupOf M = (conjugate K t).subgroupOf M :=
      pComponent_eq_of_map_eq hK.2 hKt.2 (by rw [hKmap, hKtmap])
    have h := Subgroup.subgroupOf_inj.mp heq
    rwa [inf_eq_left.mpr hK.1, inf_eq_left.mpr hKt.1] at h
  have htNK : t ∈ Subgroup.normalizer (K : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change K.map (MulAut.conj t).toMonoidHom = K
    have h1 := congrArg (Subgroup.map (MulAut.conj t).toMonoidHom) hKeq
    simpa only [CFSG.conjugate, map_conj_inv_comp_conj] using h1
  have htQ : t ∈ UnbalancedLayer.coreActionKernel K := by
    refine UnbalancedLayer.mem_coreActionKernel.mpr ⟨htNK, ?_⟩
    intro j hj
    have hjM : j ∈ M := hK.1 hj
    have htinvNK : t⁻¹ ∈ Subgroup.normalizer (K : Set G) := inv_mem htNK
    have hcK : j⁻¹ * t⁻¹ * j * t ∈ K := by
      have h1 : t⁻¹ * j * t ∈ K := by
        simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp htinvNK j).mp hj
      have h2 : j⁻¹ * (t⁻¹ * j * t) ∈ K := K.mul_mem (K.inv_mem hj) h1
      simpa [mul_assoc] using h2
    have hcOM : j⁻¹ * t⁻¹ * j * t ∈ oddCoreIn M := by
      let jM : ↥M := ⟨j, hjM⟩
      let cM : ↥M := jM⁻¹ * tM⁻¹ * jM * tM
      have hπj : π jM ∈ L := by
        have hmem : jM ∈ K.subgroupOf M := Subgroup.mem_subgroupOf.mpr hj
        have h1 : π jM ∈ (K.subgroupOf M).map π := Subgroup.mem_map_of_mem π hmem
        rwa [hKmap] at h1
      have hcπ : π cM = 1 := by
        have hcomm : u * π jM = π jM * u := hcent (π jM) hπj
        have hcomm' : u⁻¹ * π jM = π jM * u⁻¹ :=
          (show Commute u (π jM) from hcomm).inv_left
        have h1 : (π jM)⁻¹ * u⁻¹ * (π jM) * u = 1 := by
          calc (π jM)⁻¹ * u⁻¹ * (π jM) * u = (π jM)⁻¹ * (u⁻¹ * (π jM)) * u := by group
            _ = (π jM)⁻¹ * ((π jM) * u⁻¹) * u := by rw [hcomm']
            _ = 1 := by group
        simpa only [cM, map_mul, map_inv, u] using h1
      have hcO : cM ∈ O := by
        have h1 : cM ∈ (QuotientGroup.mk' O).ker := MonoidHom.mem_ker.mpr hcπ
        rwa [QuotientGroup.ker_mk'] at h1
      have hcM : (cM : G) = j⁻¹ * t⁻¹ * j * t := by
        simp [cM, jM, tM]
      rw [← hcM]
      exact Subgroup.mem_map.mpr ⟨cM, hcO, rfl⟩
    change j⁻¹ * t⁻¹ * j * t ∈ oddCoreIn K
    rw [← Sol76.inf_oddCoreIn_eq hK]
    exact Subgroup.mem_inf.mpr ⟨hcK, hcOM⟩
  set C : Subgroup G := centralizer ({t} : Set G) with hC
  set D : Subgroup G := (K ⊓ C) ⊓ oddCoreIn M with hD
  set Z : Subgroup G := oddCoreIn C ⊔ D with hZ
  have hPKC : P ≤ K ⊓ C := le_inf hPK hc.le_centralizer
  have hKCD : K ⊓ C = P ⊔ D := by
    refine le_antisymm ?_ (sup_le hPKC inf_le_left)
    intro x hx
    obtain ⟨hxK, hxC⟩ := Subgroup.mem_inf.mp hx
    have hxM : x ∈ M := hK.1 hxK
    let xM : ↥M := ⟨x, hxM⟩
    have hxπ : π xM ∈ L := by
      have hmem : xM ∈ K.subgroupOf M := Subgroup.mem_subgroupOf.mpr hxK
      have h1 : π xM ∈ (K.subgroupOf M).map π := Subgroup.mem_map_of_mem π hmem
      rwa [hKmap] at h1
    have hxPL : π xM ∈ (P.subgroupOf M).map π := by
      have h2 : (P.subgroupOf M).map π = L := by simpa only [π] using hPL
      rw [h2]
      exact hxπ
    obtain ⟨pM, hpM, hpπ⟩ := Subgroup.mem_map.mp hxPL
    have hpP : (pM : G) ∈ P := Subgroup.mem_subgroupOf.mp hpM
    have hker : π (pM⁻¹ * xM) = 1 := by
      rw [map_mul, map_inv, hpπ]
      group
    have hO : pM⁻¹ * xM ∈ O := by
      have h1 : pM⁻¹ * xM ∈ (QuotientGroup.mk' O).ker := MonoidHom.mem_ker.mpr hker
      rwa [QuotientGroup.ker_mk'] at h1
    have hDmem : ((pM⁻¹ * xM : ↥M) : G) ∈ D := by
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
      · exact K.mul_mem (K.inv_mem (hPK hpP)) hxK
      · exact C.mul_mem (C.inv_mem (hc.le_centralizer hpP)) hxC
      · exact Subgroup.mem_map.mpr ⟨pM⁻¹ * xM, hO, rfl⟩
    have hxeq : x = (pM : G) * ((pM⁻¹ * xM : ↥M) : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, xM]
      group
    rw [hxeq]
    exact Subgroup.mul_mem_sup hpP hDmem
  have hYeq : (oddCoreIn C ⊔ (K ⊓ C)) = P ⊔ Z := by
    rw [hKCD, hZ]
    calc oddCoreIn C ⊔ (P ⊔ D) = (oddCoreIn C ⊔ P) ⊔ D := (sup_assoc _ _ _).symm
      _ = (P ⊔ oddCoreIn C) ⊔ D := by rw [sup_comm (oddCoreIn C) P]
      _ = P ⊔ (oddCoreIn C ⊔ D) := sup_assoc _ _ _
  have hPsubY : P ≤ oddCoreIn C ⊔ (K ⊓ C) := hPKC.trans le_sup_right
  have hCnP : C ≤ Subgroup.normalizer (P : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hc.le_centralizer).mp hc.normal
  have hYC : oddCoreIn C ⊔ (K ⊓ C) ≤ C :=
    sup_le (Subgroup.map_subtype_le _) inf_le_right
  have hPnY : (P.subgroupOf (oddCoreIn C ⊔ (K ⊓ C))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPsubY).mpr (hYC.trans hCnP)
  have hZnormP : Z ≤ Subgroup.normalizer (P : Set G) := by
    rw [hZ]
    exact sup_le ((Subgroup.map_subtype_le _).trans hCnP)
      ((inf_le_left.trans inf_le_right).trans hCnP)
  have hOddD : Odd (Nat.card D) :=
    Odd.of_dvd_nat (odd_card_oddCoreIn M)
      (Subgroup.card_dvd_of_le (show D ≤ oddCoreIn M from inf_le_right))
  have hDnormOC : D ≤ Subgroup.normalizer (oddCoreIn C : Set G) := by
    intro d hd
    have hdC : d ∈ C := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hd).1).2
    exact mem_normalizer_oddCoreIn (Subgroup.le_normalizer hdC)
  have hcardZ : Nat.card Z * Nat.card (D ⊓ oddCoreIn C : Subgroup G) =
      Nat.card D * Nat.card (oddCoreIn C) := by
    rw [hZ]
    simpa only [sup_comm] using
      CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf hDnormOC
  have hOddZ : Odd (Nat.card Z) := by
    have hodd : Odd (Nat.card D * Nat.card (oddCoreIn C)) := hOddD.mul (odd_card_oddCoreIn C)
    rw [← hcardZ] at hodd
    exact (Nat.odd_mul.mp hodd).1
  have hYeqP : oddResidualIn (oddCoreIn C ⊔ (K ⊓ C)) = P := by
    have hrel : P.relIndex (oddCoreIn C ⊔ (K ⊓ C)) = (P ⊓ Z).relIndex Z := by
      rw [hYeq]
      simpa [sup_comm, inf_comm] using
        (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer (H := Z) (K := P) hZnormP).2
    have hdvd : (P.subgroupOf (oddCoreIn C ⊔ (K ⊓ C))).index ∣ Nat.card Z := by
      have h1 : (P.subgroupOf (oddCoreIn C ⊔ (K ⊓ C))).index =
          P.relIndex (oddCoreIn C ⊔ (K ⊓ C)) := rfl
      rw [h1, hrel]
      exact Subgroup.relIndex_dvd_card (P ⊓ Z) Z
    have hOddQuot : Odd (Nat.card (↥(oddCoreIn C ⊔ (K ⊓ C)) ⧸
        P.subgroupOf (oddCoreIn C ⊔ (K ⊓ C)))) := by
      rw [← Subgroup.index_eq_card]
      exact Odd.of_dvd_nat hOddZ hdvd
    refine le_antisymm ?_ ?_
    · rw [oddResidualIn]
      refine (Subgroup.closure_le P).mpr ?_
      rintro x ⟨hxY, k, hk⟩
      let hNorm : (P.subgroupOf (oddCoreIn C ⊔ (K ⊓ C))).Normal := hPnY
      let xY : ↥(oddCoreIn C ⊔ (K ⊓ C)) := ⟨x, hxY⟩
      let q : ↥(oddCoreIn C ⊔ (K ⊓ C)) ⧸
          P.subgroupOf (oddCoreIn C ⊔ (K ⊓ C)) :=
        QuotientGroup.mk' (P.subgroupOf (oddCoreIn C ⊔ (K ⊓ C))) xY
      have hq2 : orderOf q ∣ 2 ^ k := by
        have h := orderOf_map_dvd (QuotientGroup.mk'
          (P.subgroupOf (oddCoreIn C ⊔ (K ⊓ C)))) xY
        have hxYk : orderOf xY = 2 ^ k := by
          rw [← Subgroup.orderOf_coe xY]
          exact hk
        rwa [hxYk] at h
      have hqodd : Odd (orderOf q) :=
        Odd.of_dvd_nat hOddQuot (orderOf_dvd_natCard q)
      have hq1 : orderOf q = 1 := by
        have hcop : Nat.Coprime (orderOf q) (2 ^ k) :=
          (Nat.coprime_two_left.mpr hqodd).symm.pow_right k
        exact Nat.Coprime.eq_one_of_dvd hcop hq2
      have hqeq : q = 1 := orderOf_eq_one_iff.mp hq1
      have hmem : xY ∈ P.subgroupOf (oddCoreIn C ⊔ (K ⊓ C)) :=
        (QuotientGroup.eq_one_iff xY).mp hqeq
      exact Subgroup.mem_subgroupOf.mp hmem
    · have hPRes : oddResidualIn P = P :=
        oddResidualIn_eq_self_of_isPComponent hc.le_centralizer hc.isPComponent
      rw [← hPRes]
      exact oddResidualIn_mono hPsubY
  set T : Subgroup G := zpowers t with hT
  have hCT : centralizer (T : Set G) = C := by
    rw [hT, hC]
    exact centralizer_zpowers_eq t
  have hTne : T ≠ ⊥ := by
    rw [hT]
    intro hbot
    have ht1 : t = 1 := zpowers_eq_bot.mp hbot
    have h2 := hc.order_two
    rw [ht1, orderOf_one] at h2
    norm_num at h2
  have hT2 : IsPGroup 2 T := by
    rw [hT]
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc.order_two, pow_one])
  have hTQ : T ≤ UnbalancedLayer.coreActionKernel K := by
    rw [hT]
    exact zpowers_le.mpr htQ
  have hKT : FooteLit.IsTwoComponentIn
      (oddResidualIn (oddCoreIn (centralizer (T : Set G)) ⊔ (K ⊓ centralizer (T : Set G))))
      (centralizer (T : Set G)) := by
    rw [hCT, hYeqP]
    exact ⟨hc.le_centralizer, hc.isPComponent⟩
  have hKmember : FooteLit.IsSolomonMember K :=
    ⟨UnbalancedCorr.commutator_eq_of_isPComponent hK.1 hK.2, T, hTne, hT2, hTQ, hKT⟩
  have hPmember : FooteLit.IsSolomonMember P :=
    Sol76.isSolomonMember_of_isTwoComponentIn_centralizer hc.order_two
      ⟨hc.le_centralizer, hc.isPComponent⟩
  have hlt : FooteLit.SolomonLt K P := by
    have h := Sol76.RankOneClass.solomonLt_witness hKmember hTne hT2 hTQ hKT
    simpa only [hCT, hYeqP] using h
  have hKON : IsSporadic (↥K ⧸ pPrimeCore 2 ↥K) .ONan := by
    let φ : ↥K →* (↥M ⧸ pPrimeCore 2 ↥M) :=
      (QuotientGroup.mk' (pPrimeCore 2 ↥M)).comp (Subgroup.inclusion hK.1)
    have hrange : φ.range = L := by
      have h1 : φ.range = (K.subgroupOf M).map (QuotientGroup.mk' (pPrimeCore 2 ↥M)) := by
        change ((QuotientGroup.mk' (pPrimeCore 2 ↥M)).comp
          (Subgroup.inclusion hK.1)).range = _
        rw [MonoidHom.range_comp]
        congr 1
        ext x
        constructor
        · rintro ⟨y, rfl⟩
          exact y.2
        · intro hx
          exact ⟨⟨x, hx⟩, rfl⟩
      rw [h1]
      simpa only [π] using hKmap
    have hker : φ.ker = pPrimeCore 2 ↥K := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      have h1 : K ⊓ oddCoreIn M = oddCoreIn K := Sol76.inf_oddCoreIn_eq hK
      constructor
      · intro hx
        have hxO : (x : G) ∈ K ⊓ oddCoreIn M :=
          ⟨x.2, Subgroup.mem_map.mpr ⟨Subgroup.inclusion hK.1 x, hx, rfl⟩⟩
        rw [h1] at hxO
        obtain ⟨y, hy, hyx⟩ := hxO
        rwa [Subtype.ext hyx] at hy
      · intro hx
        have hxO : (x : G) ∈ oddCoreIn K := ⟨x, hx, rfl⟩
        rw [← h1] at hxO
        obtain ⟨y, hy, hyx⟩ := hxO.2
        have : y = Subgroup.inclusion hK.1 x := Subtype.ext hyx
        rwa [this] at hy
    let e : ↥K ⧸ pPrimeCore 2 ↥K ≃* ↥L :=
      ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivRange φ)).trans (MulEquiv.subgroupCongr hrange)
    obtain ⟨eL⟩ := hLON
    exact ⟨e.trans eL⟩
  have hSol : FooteLit.SolomonEquiv P K := by
    refine ⟨hPmember, Relation.ReflTransGen.single ⟨?_, Or.inr hlt⟩⟩
    obtain ⟨eP⟩ := hc.isSporadic_pPrimeCore
    obtain ⟨eK⟩ := hKON
    exact ⟨(Sol78.fusionZStarQuotOfCore (eK.trans eP.symm)).symm⟩
  exact ⟨K, hK, by simpa only [π] using hKmap, hKON, hSol⟩

theorem false_of_onan_one_factor (h13 : Sol76T13.SolomonThm13Simple)
    {G : Type} [Group G] [Finite G] {t : G} {P W M : Subgroup G} (hc : ONanWConfig G t P W)
    (hM : M = normalizer (W : Set G)) (htM : t ∈ M)
    {L : Subgroup (↥M ⧸ pPrimeCore 2 ↥M)} (hL : IsComponent L) (hLn : ¬ L.Normal)
    (hZ : center ↥L = ⊥) (hLON : IsSporadic ↥L .ONan)
    (hPL : (P.subgroupOf M).map (QuotientGroup.mk' (pPrimeCore 2 ↥M)) = L)
    (hcent : ∀ x ∈ L, QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨t, htM⟩ * x =
      x * QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨t, htM⟩) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hK, hKL, hKON, hPK⟩ :=
    exists_twoComponent_solomonEquiv_of_onan hc hM htM hL hZ hLON hPL hcent
  have hKstar : K ∈ FooteLit.solomonKStar G :=
    Sol76.mem_solomonKStar_of_solomonEquiv (mem_solomonKStar_of_onan_setting hc) hPK
  have hxne : ∃ x : ↥M ⧸ pPrimeCore 2 ↥M, L.map (MulAut.conj x).toMonoidHom ≠ L := by
    by_contra h
    push Not at h
    exact hLn (Subgroup.normal_iff_map_conj_eq.mpr fun g => h g)
  obtain ⟨x, hxne⟩ := hxne
  obtain ⟨m, hm⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥M) x
  let K' : Subgroup G := K.map (MulAut.conj (m : G)⁻¹).toMonoidHom
  have hK' : FooteLit.IsTwoComponentIn K' M := by
    have hh : (m : G)⁻¹ ∈ Subgroup.normalizer (M : Set G) :=
      Subgroup.le_normalizer (inv_mem m.2)
    simpa [K'] using Sol76.isTwoComponentIn_map_conj hK hh
  have hK'star : K' ∈ FooteLit.solomonKStar G := by
    simpa [K', CFSG.conjugate] using Sol76.conjugate_mem_solomonKStar hKstar (m : G)
  have himg : (K'.subgroupOf M).map (QuotientGroup.mk' (pPrimeCore 2 ↥M)) =
      conjugate L x := by
    have hsub : K'.subgroupOf M = conjugate (K.subgroupOf M) m := by
      simpa [K', CFSG.conjugate] using
        (CFSG.GroupTheory.conjugate_subgroupOf (B := K) (U := M) m).symm
    calc
      (K'.subgroupOf M).map (QuotientGroup.mk' (pPrimeCore 2 ↥M)) =
          (conjugate (K.subgroupOf M) m).map
            (QuotientGroup.mk' (pPrimeCore 2 ↥M)) := by rw [hsub]
      _ = conjugate ((K.subgroupOf M).map (QuotientGroup.mk' (pPrimeCore 2 ↥M)))
            (QuotientGroup.mk' (pPrimeCore 2 ↥M) m) :=
          UnbalancedLayer.map_conjugate (QuotientGroup.mk' (pPrimeCore 2 ↥M))
            (K.subgroupOf M) m
      _ = conjugate L x := by rw [hKL, hm]
  have hne : K' ≠ K := by
    intro hEq
    have h1 : (K'.subgroupOf M).map (QuotientGroup.mk' (pPrimeCore 2 ↥M)) = L := by
      rw [hEq, hKL]
    rw [himg] at h1
    apply hxne
    exact (map_conj_eq_iff_map_conj_inv_eq L x).mpr h1
  have hK'ON : IsSporadic (↥K' ⧸ pPrimeCore 2 ↥K') .ONan := by
    obtain ⟨e⟩ := hKON
    let eKK' : ↥K ≃* ↥K' :=
      K.equivMapOfInjective (MulAut.conj (m : G)⁻¹).toMonoidHom
        (MulAut.conj (m : G)⁻¹).injective
    exact ⟨(Sol78.coreQuotCongr eKK').symm.trans e⟩
  have hr : 3 ≤ CFSG.pRank 2 ↥K := three_le_pRank_of_sporadic_onan_pPrimeCore hKON
  have hr' : 3 ≤ CFSG.pRank 2 ↥K' := by
    have h := Sol76.pRank_map (φ := MulAut.conj (m : G)⁻¹) K
    rw [show K.map (MulAut.conj (m : G)⁻¹).toMonoidHom = K' from rfl] at h
    rwa [h]
  have he : ¬ FooteLit.HasStronglyEmbedded ↥K := not_hasStronglyEmbedded_of_on hKON
  have he' : ¬ FooteLit.HasStronglyEmbedded ↥K' := not_hasStronglyEmbedded_of_on hK'ON
  exact h13 G hc.base.1 hc.base.2.1 hc.base.2.2.1 M
    (isKBalanced_of_two hK hK' hKstar hK'star hne.symm hr hr' he he')

end CFSG.ComponentClassification.GrSLit.L34Sec5S
