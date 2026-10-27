module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.E6HighIsoPlane
public import CFSG.LieType.SeitzGeneration.ExcHighThree.IsoPlaneBasic
public import CFSG.LieType.SeitzGeneration.ExcParabolic

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.SeitzGeneration
  CFSG.LieType.Steinberg.Isogeny CFSG.RankThree.PartOne.CTP

set_option linter.unusedSectionVars true

section Index


theorem card_le_three_mul_card_inf_innerAut_of_le_e6Inndiag (K : Type) [Field K] [Finite K]
    {D : Subgroup (MulAut (adjointGroup Tag.E6 K))} (hDd : D ≤ e6Inndiag K) :
    Nat.card D ≤ 3 * Nat.card ↥(D ⊓ innerAut (adjointGroup Tag.E6 K)) := by
  classical
  obtain ⟨Φ, -, hker, hdvd⟩ := exists_outer_hom_E (K := K) (τ := Tag.E6) (Or.inl rfl)
  set N := CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup Tag.E6 K)
    with hN
  set π := QuotientGroup.mk' N with hπ
  set φ : ↥D →* _ := π.comp D.subtype with hφ
  have hrange : φ.range ≤ Φ.ker := by
    rintro _ ⟨⟨d, hd⟩, rfl⟩
    have hdd : d ∈ ((N ⊔ (rootDiagAutHom Tag.E6 K).range : Subgroup _) : Set _) := hDd hd
    rw [Subgroup.normal_mul] at hdd
    obtain ⟨i, hi, r, ⟨a, rfl⟩, rfl⟩ := hdd
    rw [hker]
    refine ⟨a, ?_⟩
    change π (rootDiagAutHom Tag.E6 K a) = π (i * rootDiagAutHom Tag.E6 K a)
    have hpi : π i = 1 := (QuotientGroup.eq_one_iff i).2 hi
    rw [map_mul, hpi, one_mul]
  have h3 : Nat.card φ.range ∣ 3 := by
    refine (Subgroup.card_dvd_of_le hrange).trans ?_
    have h := hdvd
    rwa [show Tag.E6.cartan.det.natAbs = 3 by rw [det_cartan_E6]; rfl] at h
  have hkerφ : φ.ker = N.subgroupOf D := by
    rw [hφ, ← MonoidHom.comap_ker, hπ, QuotientGroup.ker_mk']
    rfl
  have hcardker : Nat.card φ.ker = Nat.card ↥(D ⊓ innerAut (adjointGroup Tag.E6 K)) := by
    rw [hkerφ, ← Subgroup.card_map_of_injective D.subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_comm]
    rfl
  have hmul : Nat.card φ.ker * Nat.card φ.range = Nat.card D := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  rw [hcardker] at hmul
  rw [← hmul, mul_comm]
  exact Nat.mul_le_mul_right _ (Nat.le_of_dvd (by norm_num) h3)

end Index

section Iso


theorem exists_isotropic_inner_plane_e6 (K : Type) [Field K] [Finite K]
    {Ē : Subgroup (MulAut (adjointGroup Tag.E6 K))} (hĒ : IsElemAbelian 3 Ē)
    (hcard : 3 ^ 4 ≤ Nat.card Ē) (hdiag : Ē ≤ e6Inndiag K) :
    ∃ E₀ : Subgroup (adjointGroup Tag.E6 K),
      E₀.map (MulAut.conj : adjointGroup Tag.E6 K →* MulAut (adjointGroup Tag.E6 K)) ≤ Ē ∧
      (∀ x ∈ E₀, x ^ 3 = 1) ∧ Nat.card E₀ = 3 ^ 2 ∧
      ∀ x ∈ E₀.comap (e6Isogeny K), ∀ y ∈ E₀.comap (e6Isogeny K), x * y = y * x := by
  classical
  have hinj : Function.Injective (MulAut.conj : adjointGroup Tag.E6 K →*
      MulAut (adjointGroup Tag.E6 K)) :=
    mulAut_conj_injective_adjointGroup (τ := Tag.E6) (K := K)
  have hI : 3 ^ 3 ≤ Nat.card ↥(Ē ⊓ innerAut (adjointGroup Tag.E6 K)) := by
    have h := card_le_three_mul_card_inf_innerAut_of_le_e6Inndiag K hdiag
    have h4 : (3 : ℕ) ^ 4 = 3 * 3 ^ 3 := by norm_num
    rw [h4] at hcard
    exact Nat.le_of_mul_le_mul_left (hcard.trans h) (by norm_num)
  have hĒI : IsElemAbelian 3 (Ē ⊓ innerAut (adjointGroup Tag.E6 K)) := hĒ.mono inf_le_left
  obtain ⟨D, hDle, hD27⟩ := exists_le_card_eq_pow_of_isElemAbelian Nat.prime_three hĒI hI
  have hDel : IsElemAbelian 3 D := hĒI.mono hDle
  obtain ⟨E, hED, hE9, habE⟩ := exists_isotropic_plane_E6 K (hDle.trans inf_le_right) hDel hD27
  obtain ⟨E₉, hE₉E, hE₉card⟩ :=
    exists_le_card_eq_pow_of_isElemAbelian Nat.prime_three (hDel.mono hED) hE9
  have hE₉D : E₉ ≤ D := hE₉E.trans hED
  have hE₉in : E₉ ≤ (MulAut.conj : adjointGroup Tag.E6 K →* MulAut (adjointGroup Tag.E6 K)).range :=
    fun x hx => (hDle (hE₉D hx)).2
  set E₀ : Subgroup (adjointGroup Tag.E6 K) := E₉.comap
    (MulAut.conj : adjointGroup Tag.E6 K →* MulAut (adjointGroup Tag.E6 K)) with hE₀
  have hmap : E₀.map (MulAut.conj : adjointGroup Tag.E6 K →* MulAut (adjointGroup Tag.E6 K)) =
      E₉ := Subgroup.map_comap_eq_self hE₉in
  have hE₉el : IsElemAbelian 3 E₉ := (hDel.mono hED).mono hE₉E
  refine ⟨E₀, ?_, ?_, ?_, ?_⟩
  · rw [hmap]
    exact hE₉D.trans (hDle.trans inf_le_left)
  · intro x hx
    have h1 : (MulAut.conj x) ∈ E₉ := hx
    apply hinj
    rw [map_pow, map_one]
    exact hE₉el.2 _ h1
  · rw [← Subgroup.card_map_of_injective hinj (K := E₀), hmap, hE₉card]
  · intro x hx y hy
    exact habE x (Subgroup.comap_mono hE₉E hx) y (Subgroup.comap_mono hE₉E hy)

end Iso

section Cat


theorem planeGen_e6_of_isotropic_plane {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.E6 q).Valid) (hq : q.card % 3 = 1) {K : Type} [Field K] [Finite K]
    (hKq : Nat.card K = q.card) (hKchar : CharP K q.p)
    (e : Cat ⟨.E6 q, hv⟩ ≃* ↥(adjointGroup Tag.E6 K)) (E₀ : Subgroup (Cat ⟨.E6 q, hv⟩))
    (hexp : ∀ x ∈ E₀, x ^ 3 = 1) (hcard : Nat.card E₀ = 3 ^ 2)
    (hab : ∀ x ∈ (E₀.map e.toMonoidHom).comap (e6Isogeny K),
      ∀ y ∈ (E₀.map e.toMonoidHom).comap (e6Isogeny K), x * y = y * x) :
    PlaneGen (E₀.map (MulAut.conj : Cat ⟨.E6 q, hv⟩ →* MulAut (Cat ⟨.E6 q, hv⟩))) := by
  classical
  have hinj : Function.Injective (MulAut.conj : Cat ⟨.E6 q, hv⟩ →* MulAut (Cat ⟨.E6 q, hv⟩)) :=
    conj_injective_of_mulEquiv e (mulAut_conj_injective_adjointGroup (τ := Tag.E6) (K := K))
  have hring : ringChar K = q.p := ringChar.eq K q.p
  have hq3 : 3 ≠ q.p := three_ne_p_of_card_mod_three_eq_one hq
  have hKq1 : Nat.card K % 3 = 1 := by rw [hKq]; exact hq
  have hE6 : IsE6Index (TauCeti.LieTypeIndex.E6 q) := ⟨q, rfl⟩
  have hcomm : IsMulCommutative E₀ := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact IsPGroup.isMulCommutative_of_card_eq_prime_sq hcard
  have hE₀el : IsElemAbelian 3 E₀ := ⟨hcomm, hexp⟩
  set E : Subgroup (MulAut (Cat ⟨.E6 q, hv⟩)) :=
    E₀.map (MulAut.conj : Cat ⟨.E6 q, hv⟩ →* MulAut (Cat ⟨.E6 q, hv⟩)) with hE
  have hEel : IsElemAbelian 3 E := hE₀el.map _
  have hEcard : Nat.card E = 3 ^ 2 := by
    rw [hE, Subgroup.card_map_of_injective hinj]
    exact hcard
  have hin : InnerPlane ⟨.E6 q, hv⟩ 3 E := by
    rintro _ ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  by_cases hN : NormalizesRSubgroup ⟨.E6 q, hv⟩ E
  · have hpd : 3 ≠ (⟨.E6 q, hv⟩ : TauCeti.ValidLieTypeIndex).1.characteristic := fun h =>
      hq3 (h.trans (TauCeti.LieTypeIndex.characteristic_E6 q))
    have hex : ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException 3
        (⟨.E6 q, hv⟩ : TauCeti.ValidLieTypeIndex).1 := by
      rintro (⟨-, ⟨q', -, -, hd'⟩ | ⟨q', -, -, hd'⟩ | ⟨q', -, -, hd'⟩ | ⟨q', -, -, hd' | hd'⟩ |
        hd'⟩ | ⟨h5, -⟩)
      all_goals first | nomatch hd' | omega
    exact seitzExcParabolic ⟨.E6 q, hv⟩ 3 Nat.prime_three (by norm_num) hpd hex E hEel hEcard
      ⟨hin, hE6.not_classical, hN⟩
  · have hnN : ¬ NormalizesRNative .E6 K (E₀.map e.toMonoidHom) := by
      rintro ⟨R, hR1, hRp, hRn⟩
      refine hN (exists_normalized_of_native e ⟨R, hR1, ?_, fun g hg =>
        (map_conj_eq_iff_mem_normalizer R g).2 (hRn hg)⟩)
      rw [TauCeti.LieTypeIndex.characteristic_E6, ← hring]
      exact hRp
    have hexp' : ∀ x ∈ E₀.map e.toMonoidHom, x ^ 3 = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hexp x hx, map_one]
    have hcard' : Nat.card (E₀.map e.toMonoidHom) = 3 ^ 2 := by
      rw [Subgroup.card_map_of_injective e.injective, hcard]
    exact planeGen_map_conj_of_planeCl e hinj
      (planeCl_e6_of_isotropic K hKq1 _ hexp' hcard' hnN hab)

theorem exists_planeGen_of_large_E6 {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.E6 q).Valid) (hq : q.card % 3 = 1)
    {Ē : Subgroup (MulAut (Cat ⟨.E6 q, hv⟩))} (hĒ : IsElemAbelian 3 Ē)
    (hcard : 3 ^ 4 ≤ Nat.card Ē) :
    ∃ E : Subgroup (MulAut (Cat ⟨.E6 q, hv⟩)), E ≤ Ē ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧
      PlaneGen E := by
  classical
  obtain ⟨K, _, _, hKq, hKchar, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv
  have hKq1 : Nat.card K % 3 = 1 := by rw [hKq]; exact hq
  have hK3 : ringChar K ≠ 3 := by
    rw [ringChar.eq K q.p]
    exact fun h => three_ne_p_of_card_mod_three_eq_one hq h.symm
  have hinj : Function.Injective (MulAut.conj : Cat ⟨.E6 q, hv⟩ →* MulAut (Cat ⟨.E6 q, hv⟩)) :=
    conj_injective_of_mulEquiv e (mulAut_conj_injective_adjointGroup (τ := Tag.E6) (K := K))
  set Ēn : Subgroup (MulAut ↥(adjointGroup Tag.E6 K)) := Ē.map (MulAut.congr e).toMonoidHom
    with hĒn
  have hĒnel : IsElemAbelian 3 Ēn := hĒ.map _
  have hcardn : Nat.card Ēn = Nat.card Ē :=
    Subgroup.card_map_of_injective (MulAut.congr e).injective
  by_cases hdiag : Ēn ≤ e6Inndiag K
  ·
    obtain ⟨E₀P, hle, hexpP, hcardP, hab⟩ :=
      exists_isotropic_inner_plane_e6 K hĒnel (by rw [hcardn]; exact hcard) hdiag
    set E₀ : Subgroup (Cat ⟨.E6 q, hv⟩) := E₀P.comap e.toMonoidHom with hE₀
    have hmap : E₀.map e.toMonoidHom = E₀P :=
      Subgroup.map_comap_eq_self_of_surjective e.surjective E₀P
    have hexp : ∀ x ∈ E₀, x ^ 3 = 1 := by
      intro x hx
      apply e.injective
      rw [map_pow, map_one]
      exact hexpP _ hx
    have hcard₀ : Nat.card E₀ = 3 ^ 2 := by
      rw [← hcardP, ← hmap, Subgroup.card_map_of_injective e.injective]
    have hcomm : IsMulCommutative E₀ := by
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact IsPGroup.isMulCommutative_of_card_eq_prime_sq hcard₀
    have hE₀el : IsElemAbelian 3 E₀ := ⟨hcomm, hexp⟩
    refine ⟨E₀.map (MulAut.conj : Cat ⟨.E6 q, hv⟩ →* MulAut (Cat ⟨.E6 q, hv⟩)), ?_,
      hE₀el.map _, ?_,
      planeGen_e6_of_isotropic_plane hv hq hKq hKchar e E₀ hexp hcard₀ (by rw [hmap]; exact hab)⟩
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hyx⟩ := hle ⟨e x, hx, rfl⟩
      have h1 : (MulAut.congr e).toMonoidHom (MulAut.conj x) = MulAut.conj (e x) :=
        mulAut_congr_conj e x
      have h2 : y = MulAut.conj x := (MulAut.congr e).injective (hyx.trans h1.symm)
      rwa [h2] at hy
    · rw [Subgroup.card_map_of_injective hinj, hcard₀]
  ·
    obtain ⟨En, hEnle, hEncard, hEnnot⟩ := exists_plane_not_le_of_isElemAbelian Nat.prime_three
      hĒnel (by
        rw [hcardn]
        exact le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)) hcard) hdiag
    have hEnel : IsElemAbelian 3 En := hĒnel.mono hEnle
    haveI : CFSG.IsElementaryAbelian 3 En := hEnel.isElementaryAbelian
    have hgen : Subgroup.closure (fixUnion En) = ⊤ :=
      ExcWideThree.e6_fieldPlanes_three ExcOuterLeOne.subfieldMaximalAllThree_E6 hK3 En hEncard
        hEnnot
    exact exists_plane_of_map_congr e hEnle hEnel hEncard
      ((planeGen_iff_closure_fixUnion En).mpr hgen)

end Cat

end CFSG.LieType.SeitzGeneration.ExcHighThree
