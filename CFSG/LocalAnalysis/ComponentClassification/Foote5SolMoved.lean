module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitGW36
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Lemma212Steps

public section

namespace CFSG.ComponentClassification.Foote5.SolMax

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mem_oddCoreIn_of_mem_pPrimeCore {X K : Subgroup G} (hKX : K ≤ X) {y : G} (hyK : y ∈ K)
    (hy : (⟨y, hKX hyK⟩ : X) ∈ pPrimeCore 2 ↥X) : y ∈ oddCoreIn K := by
  set ι : ↥K →* ↥X := Subgroup.inclusion hKX with hι
  set N : Subgroup ↥K := (pPrimeCore 2 ↥X).comap ι with hN
  have hNn : N.Normal := (pPrimeCore_normal (p := 2) (G := ↥X)).comap ι
  have hNodd : Odd (Nat.card N) := by
    have hinj : Function.Injective ι := Subgroup.inclusion_injective hKX
    have h1 : Nat.card N = Nat.card (N.map ι) := (Subgroup.card_map_of_injective hinj).symm
    have h2 : N.map ι ≤ pPrimeCore 2 ↥X := Subgroup.map_comap_le _ _
    have h3 : Nat.card (N.map ι) ∣ Nat.card (pPrimeCore 2 ↥X) := Subgroup.card_dvd_of_le h2
    have h4 : Odd (Nat.card (pPrimeCore 2 ↥X)) :=
      Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥X))
    rw [h1]
    exact h4.of_dvd_nat h3
  have hle : N ≤ pPrimeCore 2 ↥K := by
    unfold pPrimeCore
    exact le_sSup ⟨hNn, Nat.coprime_two_left.mpr hNodd⟩
  exact ⟨⟨y, hyK⟩, hle (by rw [hN, mem_comap]; exact hy), rfl⟩

theorem le_coreActionKernel_of_ne {X K K' : Subgroup G} (hK : IsTwoComponentIn K X)
    (hK' : IsTwoComponentIn K' X) (hne : K ≠ K') : K' ≤ coreActionKernel K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hKX, hKp⟩ := hK
  obtain ⟨hK'X, hK'p⟩ := hK'
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥X) with hπ
  have hN : ∀ x ∈ K', x ∈ normalizer (K : Set G) := by
    intro x hx
    have h0 : K'.subgroupOf X ≤ pLayer ↥X 2 := le_sSup hK'p
    have h1 : (⟨x, hK'X hx⟩ : ↥X) ∈ pLayer ↥X 2 := h0 (mem_subgroupOf.mpr hx)
    exact mem_normalizer_of_subgroupOf hKX (GrSLit.pLayer_le_normalizer_of_isPComponent hKp h1)
  obtain ⟨J, hJ, -, hKJ, -⟩ := id hKp
  obtain ⟨J', hJ', -, hK'J', -⟩ := id hK'p
  have hJne : J ≠ J' := by
    intro h
    apply hne
    have h1 : K.subgroupOf X = K'.subgroupOf X :=
      pComponent_eq_of_map_eq hKp hK'p (by rw [hKJ, hK'J', h])
    rw [subgroupOf_inj, inf_eq_left.mpr hKX, inf_eq_left.mpr hK'X] at h1
    exact h1
  have hcomm : ⁅J, J'⁆ = ⊥ := (distinct_components_commute hJ hJ').resolve_left hJne
  intro x hx
  refine ⟨hN x hx, fun k hk => ?_⟩
  have hkJ : π ⟨k⁻¹, hKX (inv_mem hk)⟩ ∈ J := by
    rw [← hKJ]; exact mem_map_of_mem π (mem_subgroupOf.mpr (inv_mem hk))
  have hxJ : π ⟨x⁻¹, hK'X (inv_mem hx)⟩ ∈ J' := by
    rw [← hK'J']; exact mem_map_of_mem π (mem_subgroupOf.mpr (inv_mem hx))
  have h1 : ⁅π ⟨k⁻¹, hKX (inv_mem hk)⟩, π ⟨x⁻¹, hK'X (inv_mem hx)⟩⁆ = 1 := by
    have := commutator_mem_commutator hkJ hxJ
    rwa [hcomm, mem_bot] at this
  have hyK : k⁻¹ * x⁻¹ * k * x ∈ K := by
    have h2 : x⁻¹ * k * x ∈ K := by
      have := (mem_normalizer_iff.mp (hN x⁻¹ (inv_mem hx)) k).mp hk
      simpa [mul_assoc] using this
    rw [show k⁻¹ * x⁻¹ * k * x = k⁻¹ * (x⁻¹ * k * x) by group]
    exact mul_mem (inv_mem hk) h2
  refine mem_oddCoreIn_of_mem_pPrimeCore hKX hyK ?_
  rw [← QuotientGroup.ker_mk' (pPrimeCore 2 ↥X), MonoidHom.mem_ker, ← hπ]
  rw [commutatorElement_def, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul] at h1
  convert h1 using 2
  ext
  simp [mul_assoc]

theorem mem_of_not_le_coreActionKernel {X J K : Subgroup G} {𝒰 : Set (Subgroup G)}
    (h𝒰 : ∀ U ∈ 𝒰, IsTwoComponentIn U X) (hJ : J ≤ ⨆ U ∈ 𝒰, U) (hK : IsTwoComponentIn K X)
    (hmove : ¬ J ≤ coreActionKernel K) : K ∈ 𝒰 := by
  by_contra hK𝒰
  apply hmove
  refine hJ.trans (iSup₂_le fun U hU => le_coreActionKernel_of_ne hK (h𝒰 U hU) ?_)
  rintro rfl
  exact hK𝒰 hU

omit [Finite G] in
theorem le_normalizer_iSup {X : Subgroup G} (Pk : Subgroup G → Prop)
    (hPk : ∀ K : Subgroup G, IsTwoComponentIn K X → ∀ x ∈ X, Pk K →
      Pk (K.map (MulAut.conj x).toMonoidHom)) :
    X ≤ normalizer ((⨆ (K : Subgroup G) (_ : IsTwoComponentIn K X ∧ Pk K), K : Subgroup G) :
      Set G) := by
  set D := ⨆ (K : Subgroup G) (_ : IsTwoComponentIn K X ∧ Pk K), K with hD
  have key : ∀ x ∈ X, D.map (MulAut.conj x).toMonoidHom ≤ D := by
    intro x hx
    rw [hD, Subgroup.map_iSup]
    refine iSup_le fun K => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hK => ?_
    have hXx : X.map (MulAut.conj x).toMonoidHom = X :=
      mem_normalizer_iff_map_conj_eq.mp (le_normalizer hx)
    have h1 := Sol76.isTwoComponentIn_map (MulAut.conj x) hK.1
    rw [hXx] at h1
    exact le_iSup₂_of_le (K.map (MulAut.conj x).toMonoidHom) ⟨h1, hPk K hK.1 x hx hK.2⟩ le_rfl
  intro x hx
  rw [mem_normalizer_iff_map_conj_eq]
  refine le_antisymm (key x hx) ?_
  have h1 := map_mono (f := (MulAut.conj x).toMonoidHom) (key x⁻¹ (inv_mem hx))
  rw [Subgroup.map_map] at h1
  have h2 : (MulAut.conj x).toMonoidHom.comp (MulAut.conj x⁻¹).toMonoidHom = MonoidHom.id G := by
    ext y
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MonoidHom.id_apply]
    group
  rw [h2, Subgroup.map_id] at h1
  exact h1

theorem le_iSup_of_moved {X J : Subgroup G} (Pk : Subgroup G → Prop)
    (hPk : ∀ K : Subgroup G, IsTwoComponentIn K X → ∀ x ∈ X, Pk K →
      Pk (K.map (MulAut.conj x).toMonoidHom))
    (hJX : J ≤ twoLayerIn X) (hJ : ⁅J, J⁆ = J)
    (hmov : ∀ K : Subgroup G, IsTwoComponentIn K X → ¬ J ≤ coreActionKernel K → Pk K) :
    J ≤ ⨆ (K : Subgroup G) (_ : IsTwoComponentIn K X ∧ Pk K), K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJX' : J ≤ X := hJX.trans (map_subtype_le _)
  have hJperf : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.mpr hJ
  set O := pPrimeCore 2 ↥X with hO
  have hOn : O.Normal := pPrimeCore_normal
  have hOcop : Nat.Coprime 2 (Nat.card O) := pPrimeCore_coprime_card (p := 2) (G := ↥X)
  set π := QuotientGroup.mk' O with hπ
  let ρ : ↥J →* ↥X ⧸ O := π.comp (Subgroup.inclusion hJX')
  have hρ : ∀ j : ↥J, ρ j = π ⟨j, hJX' j.2⟩ := fun _ => rfl
  set Jb := ρ.range with hJb
  have hJE : Jb ≤ layer (↥X ⧸ O) := by
    refine le_trans ?_ (LBalance.Quot.map_pLayer_eq_layer_quotient (H := ↥X) (p := 2)).le
    rintro _ ⟨j, rfl⟩
    refine mem_map_of_mem π ?_
    obtain ⟨y, hy, hyj⟩ := hJX j.2
    have : Subgroup.inclusion hJX' j = y := Subtype.ext hyj.symm
    rw [this]
    exact hy
  have hJp : ⁅Jb, Jb⁆ = Jb := Subgroup.isPerfect_iff.mp (Group.IsPerfect.range ρ)
  set D := ⨆ (K : Subgroup G) (_ : IsTwoComponentIn K X ∧ Pk K), K with hD
  have hDX : D ≤ X := iSup₂_le fun K hK => hK.1.1
  set T := (D.subgroupOf X).map π with hT
  have hfix : ∀ K : Subgroup (↥X ⧸ O), IsComponent K → ¬ Jb ≤ centralizer (K : Set _) →
      K.map (MulAut.conj (1 : ↥X ⧸ O)).toMonoidHom = K → K ≤ T := by
    intro K hK hJK _
    obtain ⟨hK0, hK0map, -, -⟩ := (CatalogueBPrimeJoin.canonical_prime_component_lift
      (X := ↥X) 2).1 K hK
    set K0 := CatalogueBPrimeJoin.canonicalPrimeLift 2 K with hK0def
    set Kt := K0.map X.subtype with hKt
    have hKtX : IsTwoComponentIn Kt X := by
      refine ⟨map_subtype_le _, ?_⟩
      rw [hKt, ← comap_subtype, comap_map_eq_self_of_injective X.subtype_injective]
      exact hK0
    have hmove : ¬ J ≤ coreActionKernel Kt := by
      intro hc
      apply hJK
      rintro _ ⟨j, rfl⟩
      rw [mem_centralizer_iff]
      intro x hx
      rw [SetLike.mem_coe, ← hK0map] at hx
      obtain ⟨k, hk, rfl⟩ := hx
      have h1 := (hc j.2).2 (k : G) (mem_map_of_mem X.subtype hk)
      have h2 := oddCoreIn_le_of_isTwoComponentIn hKtX h1
      obtain ⟨o, ho, hoe⟩ := h2
      have h3 : o = k⁻¹ * ⟨j, hJX' j.2⟩⁻¹ * k * ⟨j, hJX' j.2⟩ :=
        Subtype.ext (by simpa using hoe)
      rw [h3] at ho
      rw [hρ, ← map_mul, ← map_mul]
      refine (QuotientGroup.eq (s := O)).mpr ?_
      have e : (k * ⟨(j : G), hJX' j.2⟩)⁻¹ * (⟨(j : G), hJX' j.2⟩ * k) =
          (k⁻¹ * ⟨(j : G), hJX' j.2⟩⁻¹ * k * ⟨(j : G), hJX' j.2⟩)⁻¹ := by group
      rw [e]
      exact inv_mem ho
    have hKtD : Kt ≤ D := le_iSup₂_of_le Kt ⟨hKtX, hmov Kt hKtX hmove⟩ le_rfl
    rw [← hK0map, hT]
    exact map_mono fun k hk => mem_subgroupOf.mpr (hKtD (mem_map_of_mem X.subtype hk))
  have hTb : Jb ≤ T := by
    refine Sol76.le_of_pieces hJp hJE (fun _ _ => Commute.one_left _) (fun x _ => by simp)
      (fun x _ => mem_centralizer_singleton_iff.mpr (by simp)) hfix ?_
    intro K _ _ hK1
    exfalso
    apply hK1
    have : (MulAut.conj (1 : ↥X ⧸ O)).toMonoidHom = MonoidHom.id _ := by
      ext x; simp
    rw [this, map_id]
  have hDn : (D.subgroupOf X).Normal :=
    (normal_subgroupOf_iff_le_normalizer hDX).mpr (le_normalizer_iSup Pk hPk)
  set J2 := J.subgroupOf X with hJ2
  have hJ2sup : J2 ≤ D.subgroupOf X ⊔ O := by
    intro x hx
    have h1 : π x ∈ T := hTb ⟨⟨x, mem_subgroupOf.mp hx⟩, rfl⟩
    rw [hT, ← mem_comap, comap_map_eq, QuotientGroup.ker_mk'] at h1
    exact h1
  have hJ2res : CatalogueBPrimeJoin.primeResidual 2 ↥J2 = ⊤ := by
    have : Group.IsPerfect ↥J2 :=
      Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hJX').symm.toMonoidHom)
        (subgroupOfEquivOfLe hJX').symm.surjective
    exact Sol76.primeResidual_two_eq_top this
  have hJ2D : J2 ≤ D.subgroupOf X := by
    have h1 := LBalance.Quot.range_le_of_range_le_sup hJ2res hOcop J2.subtype
      (by rw [range_subtype]; exact hJ2sup)
    rwa [range_subtype] at h1
  calc J = J2.map X.subtype := (map_subgroupOf_eq_of_le hJX').symm
    _ ≤ (D.subgroupOf X).map X.subtype := map_mono hJ2D
    _ = D := map_subgroupOf_eq_of_le hDX

theorem isTwoComponentIn_twoLayerIn_iff {X K : Subgroup G} :
    IsTwoComponentIn K (twoLayerIn X) ↔ IsTwoComponentIn K X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLX : twoLayerIn X ≤ X := map_subtype_le _
  have hLn : ((twoLayerIn X).subgroupOf X).Normal := by
    rw [normal_subgroupOf_iff_le_normalizer hLX]
    exact Sol76.le_normalizer_twoLayerIn X
  constructor
  · intro hK
    exact ⟨hK.1.trans hLX, GrSLit.isPComponent_subgroupOf_of_isSubnormal hK.1 hLX
      hLn.isSubnormal hK.2⟩
  · intro hK
    have hKL : K ≤ twoLayerIn X := le_twoLayerIn_of_isTwoComponentIn hK
    exact ⟨hKL, CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hKL hLX hK.2⟩

theorem twoLayerIn_twoLayerIn (X : Subgroup G) : twoLayerIn (twoLayerIn X) = twoLayerIn X := by
  have hLX : twoLayerIn X ≤ X := map_subtype_le _
  apply le_antisymm
  · exact (map_subtype_le _)
  · rintro _ ⟨y, hy, rfl⟩
    have h1 : (pLayer ↥X 2).map X.subtype ≤ twoLayerIn (twoLayerIn X) := by
      rw [Subgroup.map_le_iff_le_comap]
      refine sSup_le fun K hK => ?_
      rw [← Subgroup.map_le_iff_le_comap]
      have hKX : IsTwoComponentIn (K.map X.subtype) X := by
        refine ⟨map_subtype_le _, ?_⟩
        rw [← comap_subtype, comap_map_eq_self_of_injective X.subtype_injective]
        exact hK
      exact le_twoLayerIn_of_isTwoComponentIn (isTwoComponentIn_twoLayerIn_iff.mpr hKX)
    exact h1 ⟨y, hy, rfl⟩

theorem le_iSup_moved {X J : Subgroup G} (hJX : J ≤ twoLayerIn X) (hJ : ⁅J, J⁆ = J) :
    J ≤ ⨆ (K : Subgroup G) (_ : IsTwoComponentIn K X ∧ ¬ J ≤ coreActionKernel K), K := by
  have h1 := le_iSup_of_moved (X := twoLayerIn X) (J := J) (fun K => ¬ J ≤ coreActionKernel K)
    (fun K hK x hx hmv => ?_) (by rw [twoLayerIn_twoLayerIn]; exact hJX) hJ
    (fun K _ hmv => hmv)
  · refine h1.trans (iSup₂_le fun K hK => le_iSup₂_of_le K
      ⟨isTwoComponentIn_twoLayerIn_iff.mp hK.1, hK.2⟩ le_rfl)
  ·
    have hK' := isTwoComponentIn_twoLayerIn_iff.mp hK
    have hxN : x ∈ normalizer (K : Set G) := by
      obtain ⟨y, hy, rfl⟩ := hx
      exact mem_normalizer_of_subgroupOf hK'.1
        (GrSLit.pLayer_le_normalizer_of_isPComponent hK'.2 hy)
    have h2 : K.map (MulAut.conj x).toMonoidHom = K := mem_normalizer_iff_map_conj_eq.mp hxN
    rwa [h2]

end CFSG.ComponentClassification.Foote5.SolMax
