module

public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesConfining

public section

namespace CFSG.QuasithinUnique

open CFSG.Open

section Invariance

variable {G : Type*} [Group G] {M : Subgroup G} {f : G ≃* G}

theorem map_equiv_le_iff_of_fixes (hf : M.map f.toMonoidHom = M) {X : Subgroup G} :
    X.map f.toMonoidHom ≤ M ↔ X ≤ M := by
  conv_lhs => rw [← hf]
  exact map_equiv_le_map_equiv_iff f

theorem map_symm_eq_self_of_map_eq_self (hf : M.map f.toMonoidHom = M) :
    M.map f.symm.toMonoidHom = M := by
  conv_lhs => rw [← hf]
  exact map_equiv_symm_map_equiv f M

theorem pCoreOf_map_equiv_ne_bot_iff (p : ℕ) (f : G ≃* G) (H : Subgroup G) :
    pCoreOf p (H.map f.toMonoidHom) ≠ ⊥ ↔ pCoreOf p H ≠ ⊥ := by
  rw [pCoreOf_map_equiv, Ne, map_equiv_eq_bot_iff, Ne]

theorem IsConfining.map_equiv (hf : M.map f.toMonoidHom = M) {U : Subgroup G}
    (hU : IsConfining M U) : IsConfining M (U.map f.toMonoidHom) := by
  have hf' : M.map f.symm.toMonoidHom = M := map_symm_eq_self_of_map_eq_self hf
  obtain ⟨hUM, hU1, hU2, hUN, hUC⟩ := hU
  refine ⟨(map_equiv_le_iff_of_fixes hf).mpr hUM, fun h => hU1 ((map_equiv_eq_bot_iff f U).mp h),
    (isPGroup_map_equiv_iff 2 f U).mpr hU2, ?_, ?_⟩
  · intro V hV hUV hVM
    have hV' : V.map f.symm.toMonoidHom ≤ M := (map_equiv_le_iff_of_fixes hf').mpr hVM
    have hUV' : U ≤ V.map f.symm.toMonoidHom := by
      have := Subgroup.map_mono (f := f.symm.toMonoidHom) hUV
      rwa [map_equiv_symm_map_equiv] at this
    have h1 := hUN _ ((isPGroup_map_equiv_iff 2 f.symm V).mpr hV) hUV' hV'
    have h2 := Subgroup.map_mono (f := f.toMonoidHom) h1
    rw [← normalizer_map_equiv, map_equiv_map_equiv_symm, hf] at h2
    exact h2
  · rw [centralizer_map_equiv]
    have hM : pCoreOf 2 M = (pCoreOf 2 M).map f.toMonoidHom := by
      conv_lhs => rw [← hf]
      exact pCoreOf_map_equiv 2 f M
    rw [hM, ← map_equiv_inf]
    exact Subgroup.map_mono hUC

theorem isConfining_map_equiv_iff (hf : M.map f.toMonoidHom = M) {U : Subgroup G} :
    IsConfining M (U.map f.toMonoidHom) ↔ IsConfining M U := by
  refine ⟨fun h => ?_, IsConfining.map_equiv hf⟩
  have := IsConfining.map_equiv (map_symm_eq_self_of_map_eq_self hf) h
  rwa [map_equiv_symm_map_equiv] at this

theorem IsWitnessPair.map_equiv (hf : M.map f.toMonoidHom = M) {U HU : Subgroup G}
    (h : IsWitnessPair M U HU) :
    IsWitnessPair M (U.map f.toMonoidHom) (HU.map f.toMonoidHom) :=
  ⟨h.1.map_equiv hf, Subgroup.map_mono h.2.1, (pCoreOf_map_equiv_ne_bot_iff 2 f HU).mpr h.2.2.1,
    (charTwo_map_equiv_iff f HU).mpr h.2.2.2.1,
    fun hle => h.2.2.2.2 ((map_equiv_le_iff_of_fixes hf).mp hle)⟩

theorem isWitnessPair_map_equiv_iff (hf : M.map f.toMonoidHom = M) {U HU : Subgroup G} :
    IsWitnessPair M (U.map f.toMonoidHom) (HU.map f.toMonoidHom) ↔ IsWitnessPair M U HU := by
  refine ⟨fun h => ?_, IsWitnessPair.map_equiv hf⟩
  have := IsWitnessPair.map_equiv (map_symm_eq_self_of_map_eq_self hf) h
  rwa [map_equiv_symm_map_equiv, map_equiv_symm_map_equiv] at this

theorem IsWitness.map_equiv (hf : M.map f.toMonoidHom = M) {U : Subgroup G}
    (h : IsWitness M U) : IsWitness M (U.map f.toMonoidHom) := by
  obtain ⟨HU, hp⟩ := h
  exact ⟨HU.map f.toMonoidHom, hp.map_equiv hf⟩

theorem isWitness_map_equiv_iff (hf : M.map f.toMonoidHom = M) {U : Subgroup G} :
    IsWitness M (U.map f.toMonoidHom) ↔ IsWitness M U := by
  refine ⟨fun h => ?_, IsWitness.map_equiv hf⟩
  have := IsWitness.map_equiv (map_symm_eq_self_of_map_eq_self hf) h
  rwa [map_equiv_symm_map_equiv] at this

theorem IsGamma.map_equiv (hf : M.map f.toMonoidHom = M) {H : Subgroup G} (h : IsGamma M H) :
    IsGamma M (H.map f.toMonoidHom) := by
  obtain ⟨hcore, U, HU, hp, hle⟩ := h
  exact ⟨(pCoreOf_map_equiv_ne_bot_iff 2 f H).mpr hcore, U.map f.toMonoidHom,
    HU.map f.toMonoidHom, hp.map_equiv hf, Subgroup.map_mono hle⟩

theorem isGamma_map_equiv_iff (hf : M.map f.toMonoidHom = M) {H : Subgroup G} :
    IsGamma M (H.map f.toMonoidHom) ↔ IsGamma M H := by
  refine ⟨fun h => ?_, IsGamma.map_equiv hf⟩
  have := IsGamma.map_equiv (map_symm_eq_self_of_map_eq_self hf) h
  rwa [map_equiv_symm_map_equiv] at this

theorem IsGammaTop.map_equiv (hf : M.map f.toMonoidHom = M) {H : Subgroup G}
    (h : IsGammaTop M H) : IsGammaTop M (H.map f.toMonoidHom) := by
  obtain ⟨hcore, U, HU, hp, hle, hmax⟩ := h
  refine ⟨(pCoreOf_map_equiv_ne_bot_iff 2 f H).mpr hcore, U.map f.toMonoidHom,
    HU.map f.toMonoidHom, hp.map_equiv hf, Subgroup.map_mono hle, fun V hV => ?_⟩
  have hV' : IsWitness M (V.map f.symm.toMonoidHom) :=
    IsWitness.map_equiv (map_symm_eq_self_of_map_eq_self hf) hV
  have := hmax _ hV'
  rwa [card_map_equiv, ← card_map_equiv f U] at this

theorem isGammaTop_map_equiv_iff (hf : M.map f.toMonoidHom = M) {H : Subgroup G} :
    IsGammaTop M (H.map f.toMonoidHom) ↔ IsGammaTop M H := by
  refine ⟨fun h => ?_, IsGammaTop.map_equiv hf⟩
  have := IsGammaTop.map_equiv (map_symm_eq_self_of_map_eq_self hf) h
  rwa [map_equiv_symm_map_equiv] at this

theorem IsGammaU.map_equiv (hf : M.map f.toMonoidHom = M) {H : Subgroup G} (h : IsGammaU M H) :
    IsGammaU M (H.map f.toMonoidHom) := by
  refine ⟨h.1.map_equiv hf, fun K hK => ?_⟩
  have hK' : IsGammaTop M (K.map f.symm.toMonoidHom) :=
    IsGammaTop.map_equiv (map_symm_eq_self_of_map_eq_self hf) hK
  have := h.2 _ hK'
  rwa [twoPart_map_equiv, ← twoPart_map_equiv f H] at this

theorem isGammaU_map_equiv_iff (hf : M.map f.toMonoidHom = M) {H : Subgroup G} :
    IsGammaU M (H.map f.toMonoidHom) ↔ IsGammaU M H := by
  refine ⟨fun h => ?_, IsGammaU.map_equiv hf⟩
  have := IsGammaU.map_equiv (map_symm_eq_self_of_map_eq_self hf) h
  rwa [map_equiv_symm_map_equiv] at this

theorem IsGamma2.map_equiv (hf : M.map f.toMonoidHom = M) {H : Subgroup G} (h : IsGamma2 M H) :
    IsGamma2 M (H.map f.toMonoidHom) := by
  refine ⟨h.1.map_equiv hf, fun K hK => ?_⟩
  have hK' : IsGamma M (K.map f.symm.toMonoidHom) :=
    IsGamma.map_equiv (map_symm_eq_self_of_map_eq_self hf) hK
  have := h.2 _ hK'
  rwa [twoPart_map_equiv, ← twoPart_map_equiv f H] at this

theorem isGamma2_map_equiv_iff (hf : M.map f.toMonoidHom = M) {H : Subgroup G} :
    IsGamma2 M (H.map f.toMonoidHom) ↔ IsGamma2 M H := by
  refine ⟨fun h => ?_, IsGamma2.map_equiv hf⟩
  have := IsGamma2.map_equiv (map_symm_eq_self_of_map_eq_self hf) h
  rwa [map_equiv_symm_map_equiv] at this

theorem IsGamma0.map_equiv (hf : M.map f.toMonoidHom = M) {H : Subgroup G} (h : IsGamma0 M H) :
    IsGamma0 M (H.map f.toMonoidHom) :=
  h.imp (IsGammaU.map_equiv hf) (IsGamma2.map_equiv hf)

theorem isGamma0_map_equiv_iff (hf : M.map f.toMonoidHom = M) {H : Subgroup G} :
    IsGamma0 M (H.map f.toMonoidHom) ↔ IsGamma0 M H :=
  or_congr (isGammaU_map_equiv_iff hf) (isGamma2_map_equiv_iff hf)

theorem IsEscaping.map_equiv (hf : M.map f.toMonoidHom = M) {D : Subgroup G}
    (h : IsEscaping M D) : IsEscaping M (D.map f.toMonoidHom) := by
  obtain ⟨hDM, hD1, hD2, hDchar, hDnot⟩ := h
  refine ⟨(map_equiv_le_iff_of_fixes hf).mpr hDM, fun h => hD1 ((map_equiv_eq_bot_iff f D).mp h),
    (isPGroup_map_equiv_iff 2 f D).mpr hD2, ?_, ?_⟩
  · rw [normalizer_map_equiv]
    exact (charTwo_map_equiv_iff f _).mpr hDchar
  · rw [normalizer_map_equiv]
    exact fun hle => hDnot ((map_equiv_le_iff_of_fixes hf).mp hle)

theorem isEscaping_map_equiv_iff (hf : M.map f.toMonoidHom = M) {D : Subgroup G} :
    IsEscaping M (D.map f.toMonoidHom) ↔ IsEscaping M D := by
  refine ⟨fun h => ?_, IsEscaping.map_equiv hf⟩
  have := IsEscaping.map_equiv (map_symm_eq_self_of_map_eq_self hf) h
  rwa [map_equiv_symm_map_equiv] at this

theorem maximal_isEscaping_map_equiv_iff (hf : M.map f.toMonoidHom = M) {D : Subgroup G} :
    Maximal (IsEscaping M) (D.map f.toMonoidHom) ↔ Maximal (IsEscaping M) D := by
  have key : ∀ g : G ≃* G, M.map g.toMonoidHom = M → ∀ D : Subgroup G,
      Maximal (IsEscaping M) D → Maximal (IsEscaping M) (D.map g.toMonoidHom) := by
    intro g hg D hD
    refine ⟨hD.1.map_equiv hg, fun y hy hle => ?_⟩
    have hy' : IsEscaping M (y.map g.symm.toMonoidHom) :=
      IsEscaping.map_equiv (map_symm_eq_self_of_map_eq_self hg) hy
    have hDy : D ≤ y.map g.symm.toMonoidHom := by
      have := Subgroup.map_mono (f := g.symm.toMonoidHom) hle
      rwa [map_equiv_symm_map_equiv] at this
    have := Subgroup.map_mono (f := g.toMonoidHom) (hD.2 hy' hDy)
    rwa [map_equiv_map_equiv_symm] at this
  refine ⟨fun h => ?_, key f hf D⟩
  have := key f.symm (map_symm_eq_self_of_map_eq_self hf) _ h
  rwa [map_equiv_symm_map_equiv] at this

end Invariance

section Families

variable {G : Type*} [Group G] {M : Subgroup G}

theorem IsGammaTop.isGamma {H : Subgroup G} (h : IsGammaTop M H) : IsGamma M H := by
  obtain ⟨hcore, U, HU, hp, hle, -⟩ := h
  exact ⟨hcore, U, HU, hp, hle⟩

theorem IsGammaU.isGamma {H : Subgroup G} (h : IsGammaU M H) : IsGamma M H := h.1.isGamma

theorem IsGamma2.isGamma {H : Subgroup G} (h : IsGamma2 M H) : IsGamma M H := h.1

theorem IsGamma0.isGamma {H : Subgroup G} (h : IsGamma0 M H) : IsGamma M H :=
  h.elim IsGammaU.isGamma IsGamma2.isGamma

theorem IsGamma.not_le {H : Subgroup G} (h : IsGamma M H) : ¬ H ≤ M := by
  obtain ⟨-, U, HU, hp, hle⟩ := h
  exact fun hHM => hp.2.2.2.2 (hle.trans hHM)

theorem IsWitnessPair.isWitness {U HU : Subgroup G} (h : IsWitnessPair M U HU) : IsWitness M U :=
  ⟨HU, h⟩

theorem IsWitnessPair.isGamma_of_le {U HU K : Subgroup G} (h : IsWitnessPair M U HU) (hle : HU ≤ K)
    (hK : pCoreOf 2 K ≠ ⊥) : IsGamma M K :=
  ⟨hK, U, HU, h, hle⟩

theorem IsWitnessPair.isGamma {U HU : Subgroup G} (h : IsWitnessPair M U HU) : IsGamma M HU :=
  h.isGamma_of_le le_rfl h.2.2.1

theorem IsWitnessPair.isGammaTop_of_le {U HU K : Subgroup G} (h : IsWitnessPair M U HU)
    (hle : HU ≤ K) (hK : pCoreOf 2 K ≠ ⊥)
    (hmax : ∀ V : Subgroup G, IsWitness M V → Nat.card V ≤ Nat.card U) : IsGammaTop M K :=
  ⟨hK, U, HU, h, hle, hmax⟩

theorem IsGammaTop.of_le {H K : Subgroup G} (h : IsGammaTop M H) (hHK : H ≤ K)
    (hK : IsGamma M K) : IsGammaTop M K := by
  obtain ⟨-, U, HU, hp, hle, hmax⟩ := h
  exact ⟨hK.1, U, HU, hp, hle.trans hHK, hmax⟩

variable [Finite G]

theorem IsGammaTop.card_le_twoPart {H : Subgroup G} (h : IsGammaTop M H) {V : Subgroup G}
    (hV : IsWitness M V) : Nat.card V ≤ twoPart H := by
  obtain ⟨-, U, HU, hp, hle, hmax⟩ := h
  exact (hmax V hV).trans (CFSG.QuasithinUnique.card_le_twoPart (hp.2.1.trans hle) hp.1.2.2.1)

theorem IsGammaTop.card_le_of_isSylowTwoOf {H S : Subgroup G} (h : IsGammaTop M H)
    (hS : IsSylowTwoOf S H) {V : Subgroup G} (hV : IsWitness M V) : Nat.card V ≤ Nat.card S := by
  rw [hS.card_eq]
  exact h.card_le_twoPart hV

theorem IsGamma0.card_le_twoPart {H V : Subgroup G} (hH : IsGamma0 M H) (hV : IsWitness M V) :
    Nat.card V ≤ twoPart H := by
  rcases hH with hH | hH
  · exact hH.1.card_le_twoPart hV
  · obtain ⟨HV, hp⟩ := hV
    exact (CFSG.QuasithinUnique.card_le_twoPart hp.2.1 hp.1.2.2.1).trans (hH.2 HV hp.isGamma)

theorem exists_maximal_isEscaping (hδ : ∃ D : Subgroup G, IsEscaping M D) :
    ∃ D : Subgroup G, Maximal (IsEscaping M) D :=
  Set.Finite.exists_maximal (s := {D : Subgroup G | IsEscaping M D}) (Set.toFinite _) hδ

theorem isSylowTwoOf_of_twoPart_le {S K : Subgroup G} (hSK : S ≤ K) (hSM : S ≤ M)
    (hS : IsPGroup 2 S) (hle : twoPart K ≤ Nat.card S) :
    IsSylowTwoOf S K ∧ IsSylowTwoOf S (K ⊓ M) := by
  have h1 : Nat.card S = twoPart K := le_antisymm (card_le_twoPart hSK hS) hle
  refine ⟨isSylowTwoOf_of_card_eq hSK hS h1, isSylowTwoOf_of_card_eq (le_inf hSK hSM) hS ?_⟩
  exact le_antisymm (card_le_twoPart (le_inf hSK hSM) hS) ((twoPart_mono inf_le_left).trans hle)

theorem IsSylowTwoOf.map_equiv {S H : Subgroup G} (f : G ≃* G) (h : IsSylowTwoOf S H) :
    IsSylowTwoOf (S.map f.toMonoidHom) (H.map f.toMonoidHom) := by
  rw [isSylowTwoOf_iff] at h ⊢
  obtain ⟨hle, hS, hc⟩ := h
  exact ⟨Subgroup.map_mono hle, (isPGroup_map_equiv_iff 2 f S).mpr hS,
    by rw [card_map_equiv, twoPart_map_equiv, hc]⟩

end Families

section Tools

variable {G : Type*} [Group G]

theorem le_pCoreOf_of_normalizes {p : ℕ} {N K : Subgroup G} (hNK : N ≤ K)
    (hK : K ≤ Subgroup.normalizer (N : Set G)) (hN : IsPGroup p N) : N ≤ pCoreOf p K :=
  CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf p N K hNK
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mpr hK) hN

theorem normalizer_le_normalizer_of_characteristic {S R : Subgroup G} (hRS : R ≤ S)
    (hchar : (R.subgroupOf S).Characteristic) :
    Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (R : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  have hfix := hchar.fixed (S.normalizerMonoidHom ⟨g, hg⟩)
  have key : ∀ x : G, x ∈ S → (x ∈ R ↔ g * x * g⁻¹ ∈ R) := by
    intro x hxS
    have hmem : (⟨x, hxS⟩ : S) ∈ R.subgroupOf S ↔
        (S.normalizerMonoidHom ⟨g, hg⟩ ⟨x, hxS⟩ : S) ∈ R.subgroupOf S := by
      have h1 : (⟨x, hxS⟩ : S) ∈ (R.subgroupOf S).comap
          (S.normalizerMonoidHom ⟨g, hg⟩).toMonoidHom ↔ (⟨x, hxS⟩ : S) ∈ R.subgroupOf S := by
        rw [hfix]
      rw [Subgroup.mem_comap] at h1
      exact h1.symm
    simpa [Subgroup.mem_subgroupOf, Subgroup.normalizerMonoidHom_apply_apply_coe] using hmem
  intro x
  have hSx : x ∈ S ↔ g * x * g⁻¹ ∈ S := Subgroup.mem_normalizer_iff.mp hg x
  constructor
  · intro hx
    exact (key x (hRS hx)).mp hx
  · intro hx
    exact (key x (hSx.mpr (hRS hx))).mpr hx

end Tools


section WitnessFamilies

theorem witness_local_families_conj_invariant {G : Type*} [Group G] {M : Subgroup G} {m : G}
    (hm : m ∈ M) :
    (∀ D : Subgroup G,
      IsEscaping M D ↔ IsEscaping M (D.map (MulAut.conj m).toMonoidHom)) ∧
    (∀ D : Subgroup G,
      Maximal (IsEscaping M) D ↔ Maximal (IsEscaping M) (D.map (MulAut.conj m).toMonoidHom)) ∧
    (∀ U : Subgroup G,
      IsConfining M U ↔ IsConfining M (U.map (MulAut.conj m).toMonoidHom)) ∧
    (∀ U HU : Subgroup G, IsWitnessPair M U HU ↔
      IsWitnessPair M (U.map (MulAut.conj m).toMonoidHom) (HU.map (MulAut.conj m).toMonoidHom)) ∧
    (∀ U : Subgroup G, IsWitness M U ↔ IsWitness M (U.map (MulAut.conj m).toMonoidHom)) ∧
    (∀ H : Subgroup G, IsGamma M H ↔ IsGamma M (H.map (MulAut.conj m).toMonoidHom)) ∧
    (∀ H : Subgroup G, IsGammaTop M H ↔ IsGammaTop M (H.map (MulAut.conj m).toMonoidHom)) ∧
    (∀ H : Subgroup G, IsGammaU M H ↔ IsGammaU M (H.map (MulAut.conj m).toMonoidHom)) ∧
    (∀ H : Subgroup G, IsGamma2 M H ↔ IsGamma2 M (H.map (MulAut.conj m).toMonoidHom)) ∧
    (∀ H : Subgroup G, IsGamma0 M H ↔ IsGamma0 M (H.map (MulAut.conj m).toMonoidHom)) := by
  have hf := map_conj_eq_self_of_mem hm
  exact ⟨fun D => (isEscaping_map_equiv_iff hf).symm,
    fun D => (maximal_isEscaping_map_equiv_iff hf).symm,
    fun U => (isConfining_map_equiv_iff hf).symm,
    fun U HU => (isWitnessPair_map_equiv_iff hf).symm,
    fun U => (isWitness_map_equiv_iff hf).symm,
    fun H => (isGamma_map_equiv_iff hf).symm,
    fun H => (isGammaTop_map_equiv_iff hf).symm,
    fun H => (isGammaU_map_equiv_iff hf).symm,
    fun H => (isGamma2_map_equiv_iff hf).symm,
    fun H => (isGamma0_map_equiv_iff hf).symm⟩

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem IsGamma.sylow_properties (h : UniqueSetting G T M) {H S : Subgroup G} (hH : IsGamma M H)
    (hS : IsSylowTwoOf S (H ⊓ M)) :
    IsSylowTwoOf S H ∧ IsConfining M S ∧ Nat.card S < Nat.card T := by
  obtain ⟨hcore, U, HU, hpair, hUH⟩ := hH
  have hUH' : U ≤ H := hpair.2.1.trans hUH
  obtain ⟨S₀, hUS₀, hS₀⟩ := exists_isSylowTwoOf_of_le hUH' hpair.1.2.2.1
  obtain ⟨hS₀M, hS₀c⟩ := hpair.1.sylow_le_and_isConfining hS₀ hUS₀
  have hpart : twoPart H = twoPart (H ⊓ M) := hpair.1.twoPart_eq_inf hUH'
  have hS₀' : IsSylowTwoOf S₀ (H ⊓ M) :=
    isSylowTwoOf_of_card_eq (le_inf hS₀.le hS₀M) hS₀.isPGroup (hS₀.card_eq.trans hpart)
  obtain ⟨x, hx, hxS⟩ := hS₀'.exists_conj hS
  have hSc : IsConfining M S := by
    rw [hxS]
    exact hS₀c.map_equiv (map_conj_eq_self_of_mem hx.2)
  have hSH : IsSylowTwoOf S H :=
    isSylowTwoOf_of_card_eq (hS.le.trans inf_le_left) hS.isPGroup (by rw [hS.card_eq, hpart])
  refine ⟨hSH, hSc, lt_of_le_of_ne (h.card_le_of_isPGroup hS.isPGroup) fun hcard => ?_⟩
  have hSM : IsSylowTwoOf S M :=
    isSylowTwoOf_of_card_eq (hS.le.trans inf_le_right) hS.isPGroup (by rw [hcard, h.twoPart_M])
  have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 H : Set G)) :=
    ⟨pCoreOf 2 H, hcore, CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H, rfl⟩
  have hHN : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H
  have hNM := h.le_of_isTwoLocal_of_isSylowTwoOf_M hSM hloc (hS.le.trans (inf_le_left.trans hHN))
  exact hpair.2.2.2.2 (hUH.trans (hHN.trans hNM))

theorem IsGamma.twoPart_lt (h : UniqueSetting G T M) {K : Subgroup G} (hK : IsGamma M K) :
    twoPart K < Nat.card T := by
  obtain ⟨S, hS⟩ := exists_isSylowTwoOf (K ⊓ M)
  obtain ⟨hSK, -, hlt⟩ := IsGamma.sylow_properties h hK hS
  rwa [hSK.card_eq] at hlt

theorem exists_witness_families_of_isEscaping (h : UniqueSetting G T M)
    (hδ : ∃ D : Subgroup G, IsEscaping M D) :
    (∃ U HU : Subgroup G, IsWitnessPair M U HU) ∧ (∃ U : Subgroup G, IsWitness M U) ∧
      (∃ H : Subgroup G, IsGamma M H) ∧ (∃ H : Subgroup G, IsGammaTop M H) ∧
      (∃ H : Subgroup G, IsGammaU M H) ∧ (∃ H : Subgroup G, IsGamma2 M H) ∧
      (∃ H : Subgroup G, IsGamma0 M H) := by
  obtain ⟨D, hDmax⟩ := exists_maximal_isEscaping hδ
  obtain ⟨S, hS⟩ := exists_isSylowTwoOf (M ⊓ Subgroup.normalizer (D : Set G))
  obtain ⟨hE, -, -, -, hSc, -, -⟩ := maximal_escaping_normalizer_witness h hDmax hS
  obtain ⟨-, hD1, -, hDchar, hDnot⟩ := hDmax.1
  have hpair : IsWitnessPair M S (Subgroup.normalizer (D : Set G)) :=
    ⟨hSc, hS.le.trans inf_le_right, by rw [hE]; exact hD1, hDchar, hDnot⟩
  obtain ⟨U, hUW, hUmax⟩ := Set.exists_max_image {V : Subgroup G | IsWitness M V}
    (fun V => Nat.card V) (Set.toFinite _) ⟨S, hpair.isWitness⟩
  obtain ⟨HU, hHU⟩ := hUW
  have hTop : IsGammaTop M HU := hHU.isGammaTop_of_le le_rfl hHU.2.2.1 hUmax
  obtain ⟨K, hK, hKmax⟩ := Set.exists_max_image {K : Subgroup G | IsGammaTop M K} twoPart
    (Set.toFinite _) ⟨HU, hTop⟩
  have hKU : IsGammaU M K := ⟨hK, fun K' hK' => hKmax K' hK'⟩
  obtain ⟨K2, hK2, hK2max⟩ := Set.exists_max_image {K : Subgroup G | IsGamma M K} twoPart
    (Set.toFinite _) ⟨_, hpair.isGamma⟩
  have hK2' : IsGamma2 M K2 := ⟨hK2, fun K' hK' => hK2max K' hK'⟩
  exact ⟨⟨S, _, hpair⟩, ⟨S, hpair.isWitness⟩, ⟨_, hpair.isGamma⟩, ⟨HU, hTop⟩, ⟨K, hKU⟩,
    ⟨K2, hK2'⟩, ⟨K, Or.inl hKU⟩⟩

end WitnessFamilies


section ExtremalOvergroups

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem IsGamma0.isSylowTwoOf_of_inf (h : UniqueSetting G T M) {H S : Subgroup G}
    (hH : IsGamma0 M H) (hS : IsSylowTwoOf S (H ⊓ M)) : IsSylowTwoOf S H :=
  (IsGamma.sylow_properties h hH.isGamma hS).1

theorem IsGamma0.overgroup_of_sylow_le (h : UniqueSetting G T M) {H S K : Subgroup G}
    (hH : IsGamma0 M H) (hS : IsSylowTwoOf S (H ⊓ M)) (hK : IsGamma M K) (hSK : S ≤ K)
    (hcase : IsGamma2 M H ∨ (IsGammaU M H ∧ IsGammaTop M K)) :
    IsGamma0 M K ∧ IsSylowTwoOf S K ∧ IsSylowTwoOf S (K ⊓ M) ∧
      (IsGamma2 M H → IsGamma2 M K) ∧ (IsGammaU M H → IsGammaTop M K → IsGammaU M K) := by
  have hSH : Nat.card S = twoPart H := (hH.isSylowTwoOf_of_inf h hS).card_eq
  have hSM : S ≤ M := hS.le.trans inf_le_right
  have hle : twoPart K ≤ Nat.card S := by
    rw [hSH]
    rcases hcase with h2 | ⟨hU, hT⟩
    · exact h2.2 K hK
    · exact hU.2 K hT
  obtain ⟨hSK', hSKM⟩ := isSylowTwoOf_of_twoPart_le hSK hSM hS.isPGroup hle
  have hcardK : twoPart H = twoPart K := hSH.symm.trans hSK'.card_eq
  have h2K : IsGamma2 M H → IsGamma2 M K := fun h2 =>
    ⟨hK, fun K' hK' => (h2.2 K' hK').trans hcardK.le⟩
  have hUK : IsGammaU M H → IsGammaTop M K → IsGammaU M K := fun hU hT =>
    ⟨hT, fun K' hK' => (hU.2 K' hK').trans hcardK.le⟩
  refine ⟨?_, hSK', hSKM, h2K, hUK⟩
  rcases hcase with h2 | ⟨hU, hT⟩
  · exact Or.inr (h2K h2)
  · exact Or.inl (hUK hU hT)

theorem IsGamma0.overgroup_of_le (h : UniqueSetting G T M) {H S K : Subgroup G}
    (hH : IsGamma0 M H) (hS : IsSylowTwoOf S (H ⊓ M)) (hK : IsGamma M K) (hHK : H ≤ K) :
    IsGamma0 M K ∧ IsSylowTwoOf S K ∧ IsSylowTwoOf S (K ⊓ M) ∧
      (IsGammaU M H → IsGammaU M K) ∧ (IsGamma2 M H → IsGamma2 M K) := by
  have hSK : S ≤ K := (hS.le.trans inf_le_left).trans hHK
  have hcase : IsGamma2 M H ∨ (IsGammaU M H ∧ IsGammaTop M K) := by
    rcases hH with hU | h2
    · exact Or.inr ⟨hU, hU.1.of_le hHK hK⟩
    · exact Or.inl h2
  obtain ⟨hK0, hSK', hSKM, h2K, hUK⟩ := hH.overgroup_of_sylow_le h hS hK hSK hcase
  exact ⟨hK0, hSK', hSKM, fun hU => hUK hU (hU.1.of_le hHK hK), h2K⟩

theorem IsGamma0.isGamma2_of_card_eq_two_mul (h : UniqueSetting G T M) {H S : Subgroup G}
    (hH : IsGamma0 M H) (hS : IsSylowTwoOf S (H ⊓ M)) (hT : Nat.card T = 2 * Nat.card S) :
    IsGamma2 M H ∧ ∀ K : Subgroup G, IsGamma M K → Nat.card S ≤ twoPart K →
      twoPart K = Nat.card S ∧ IsGamma2 M K := by
  have hSH : Nat.card S = twoPart H := (hH.isSylowTwoOf_of_inf h hS).card_eq
  have hbound : ∀ K : Subgroup G, IsGamma M K → twoPart K ≤ Nat.card S := by
    intro K hK
    have hlt := IsGamma.twoPart_lt h hK
    obtain ⟨a, ha⟩ : ∃ a, Nat.card S = 2 ^ a := hS.isPGroup.exists_card_eq
    unfold twoPart at hlt ⊢
    rw [hT, ha, ← pow_succ'] at hlt
    have := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt
    rw [ha]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  refine ⟨⟨hH.isGamma, fun K hK => by rw [← hSH]; exact hbound K hK⟩, fun K hK hKS => ?_⟩
  have heq : twoPart K = Nat.card S := le_antisymm (hbound K hK) hKS
  exact ⟨heq, hK, fun K' hK' => (hbound K' hK').trans heq.ge⟩

end ExtremalOvergroups


section CoreNormalizer

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem IsGamma0.core_normalizer (h : UniqueSetting G T M) {H S : Subgroup G}
    (hH : IsGamma0 M H) (hS : IsSylowTwoOf S (H ⊓ M)) :
    pCoreOf 2 H ≠ ⊥ ∧ IsGamma0 M (Subgroup.normalizer (pCoreOf 2 H : Set G)) ∧
      IsSylowTwoOf S H ∧ IsSylowTwoOf S (Subgroup.normalizer (pCoreOf 2 H : Set G)) ∧
      IsSylowTwoOf S (M ⊓ Subgroup.normalizer (pCoreOf 2 H : Set G)) ∧
      (IsGammaU M H → IsGammaU M (Subgroup.normalizer (pCoreOf 2 H : Set G))) ∧
      (IsGamma2 M H → IsGamma2 M (Subgroup.normalizer (pCoreOf 2 H : Set G))) := by
  have hcore : pCoreOf 2 H ≠ ⊥ := hH.isGamma.1
  have hHN : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H
  have hNΓ : IsGamma M (Subgroup.normalizer (pCoreOf 2 H : Set G)) := by
    obtain ⟨-, U, HU, hp, hle⟩ := hH.isGamma
    refine ⟨fun hbot => hcore (le_bot_iff.mp ?_), U, HU, hp, hle.trans hHN⟩
    have : pCoreOf 2 H ≤ pCoreOf 2 (Subgroup.normalizer (pCoreOf 2 H : Set G)) :=
      le_pCoreOf_of_normalizes Subgroup.le_normalizer le_rfl
        (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H)
    rwa [hbot] at this
  obtain ⟨hN0, hSN, hSNM, hUN, h2N⟩ := hH.overgroup_of_le h hS hNΓ hHN
  refine ⟨hcore, hN0, hH.isSylowTwoOf_of_inf h hS, hSN, ?_, hUN, h2N⟩
  rwa [inf_comm] at hSNM

theorem IsGamma0.core_centralizer_le (h : UniqueSetting G T M) {H S : Subgroup G}
    (hH : IsGamma0 M H) (hS : IsSylowTwoOf S (H ⊓ M)) :
    pCoreOf 2 M ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ≤ S := by
  obtain ⟨-, -, -, -, hSNM, -, -⟩ := hH.core_normalizer h hS
  have hEK : pCoreOf 2 M ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ≤
      M ⊓ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    le_inf (inf_le_left.trans (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 M))
      (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))
  have hKE : M ⊓ Subgroup.normalizer (pCoreOf 2 H : Set G) ≤
      Subgroup.normalizer ((pCoreOf 2 M ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) :
        Subgroup G) : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.common_normalizer_le_normalizer_inf _ _ _
      (inf_le_left.trans
        (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M))
      (inf_le_right.trans
        (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_centralizer _))
  exact hSNM.le_of_normalizes hEK hKE
    ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M).to_le inf_le_left)

theorem IsGamma0.center_le_of_le_sylow (h : UniqueSetting G T M) {H S T' : Subgroup G}
    (hH : IsGamma0 M H) (hS : IsSylowTwoOf S (H ⊓ M)) (hT' : IsSylowTwoOf T' M) (hST' : S ≤ T') :
    T' ⊓ Subgroup.centralizer (T' : Set G) ≤ S ⊓ Subgroup.centralizer (S : Set G) ∧ S < T' ∧
      ∀ z ∈ T' ⊓ Subgroup.centralizer (T' : Set G), z ≠ 1 →
        Subgroup.centralizer ({z} : Set G) ≤ M := by
  obtain ⟨-, hSc, hlt⟩ := IsGamma.sylow_properties h hH.isGamma hS
  refine ⟨h.center_le_center_of_isConfining hT' hST' hSc,
    lt_of_le_of_ne hST' fun heq => ?_, ?_⟩
  · rw [heq, h.card_eq_of_isSylowTwoOf_M hT'] at hlt
    exact lt_irrefl _ hlt
  · intro z hz hz1
    have hzpow : Subgroup.zpowers z ≤ T' := (Subgroup.zpowers_le).mpr hz.1
    have hZ : Subgroup.zpowers z ≠ ⊥ := by
      rw [Ne, Subgroup.zpowers_eq_bot]
      exact hz1
    have hAZ : (T' : Set G) ⊆ (Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) :
        Subgroup G) := by
      intro t ht
      show t ∈ Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G)
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
        Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hz.2 t ht
    have hMT : {K : Subgroup G | CFSG.Assembly.Quasithin.quasithinIsMaxTwoLocal K ∧
        (T' : Set G) ⊆ (K : Set G)} = {M} := by
      ext K
      constructor
      · rintro ⟨hK, hTK⟩
        exact h.unique_of_isSylowTwoOf_M hT' K hK hTK
      · intro hK
        rw [Set.mem_singleton_iff] at hK
        subst hK
        exact ⟨h.maxLocal, hT'.le⟩
    have htrans := maxTwoLocal_centralizer_transfer hZ (hT'.isPGroup.to_le hzpow) hAZ hMT
    have hcent : Subgroup.centralizer ({z} : Set G) =
        Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [hcent]
    exact htrans.1.trans htrans.2.1

theorem IsGamma0.charTwo_core_normalizer (h : UniqueSetting G T M) {H S : Subgroup G}
    (hH : IsGamma0 M H) (hS : IsSylowTwoOf S (H ⊓ M)) (hchar : CharTwo H) :
    CharTwo (Subgroup.normalizer (pCoreOf 2 H : Set G)) ∧
      pCoreOf 2 (Subgroup.normalizer (pCoreOf 2 H : Set G)) = pCoreOf 2 H := by
  obtain ⟨-, U, HU, hp, hle⟩ := hH.isGamma
  obtain ⟨-, hcharN⟩ := hp.1.charTwo_normalizer_core h (hp.2.1.trans hle) hchar
  refine ⟨hcharN, ?_⟩
  obtain ⟨-, -, hSH, hSN, -, -, -⟩ := hH.core_normalizer h hS
  have hHN : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H
  have hQR : pCoreOf 2 H ≤ pCoreOf 2 (Subgroup.normalizer (pCoreOf 2 H : Set G)) :=
    le_pCoreOf_of_normalizes Subgroup.le_normalizer le_rfl
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H)
  have hRS : pCoreOf 2 (Subgroup.normalizer (pCoreOf 2 H : Set G)) ≤ S :=
    hSN.le_of_normalizes (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _)
      (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 _)
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _)
  have hRH : pCoreOf 2 (Subgroup.normalizer (pCoreOf 2 H : Set G)) ≤ pCoreOf 2 H :=
    le_pCoreOf_of_normalizes (hRS.trans hSH.le)
      (hHN.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 _))
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _)
  exact le_antisymm hRH hQR

end CoreNormalizer

section CharacteristicNormalizers

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem IsGamma0.normalizer_inf_le_of_characteristic (h : UniqueSetting G T M) {H S : Subgroup G}
    (hH : IsGamma0 M H) (hchar : CharTwo H) (hS : IsSylowTwoOf S (H ⊓ M)) {R : Subgroup G}
    (hR1 : R ≠ ⊥) (hRS : R ≤ S) (hRchar : (R.subgroupOf S).Characteristic) :
    H ⊓ Subgroup.normalizer (R : Set G) ≤ H ⊓ M := by
  have hHΓ : IsGamma M H := hH.isGamma
  obtain ⟨hSH, hSc, hlt⟩ := IsGamma.sylow_properties h hHΓ hS
  have hRH : R ≤ H := hRS.trans hSH.le
  have hR2 : IsPGroup 2 R := hSH.isPGroup.to_le hRS
  have hNS : S ≤ Subgroup.normalizer (R : Set G) := by
    have := hRchar
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hRS).mp inferInstance
  have hSNS : Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (R : Set G) :=
    normalizer_le_normalizer_of_characteristic hRS hRchar
  refine le_inf inf_le_left ?_
  by_contra hnot
  have hnotM : ¬ H ⊓ Subgroup.normalizer (R : Set G) ≤ M := hnot
  have hcoreHR : pCoreOf 2 (H ⊓ Subgroup.normalizer (R : Set G)) ≠ ⊥ := by
    intro hbot
    have : R ≤ pCoreOf 2 (H ⊓ Subgroup.normalizer (R : Set G)) :=
      le_pCoreOf_of_normalizes (le_inf hRH Subgroup.le_normalizer) inf_le_right hR2
    rw [hbot] at this
    exact hR1 (le_bot_iff.mp this)
  have hpair : IsWitnessPair M S (H ⊓ Subgroup.normalizer (R : Set G)) :=
    ⟨hSc, le_inf (hS.le.trans inf_le_left) hNS, hcoreHR, hchar.inf_normalizer hRH hR2, hnotM⟩
  have hcoreN : pCoreOf 2 (Subgroup.normalizer (R : Set G)) ≠ ⊥ := by
    intro hbot
    have : R ≤ pCoreOf 2 (Subgroup.normalizer (R : Set G)) :=
      le_pCoreOf_of_normalizes Subgroup.le_normalizer le_rfl hR2
    rw [hbot] at this
    exact hR1 (le_bot_iff.mp this)
  have hKΓ : IsGamma M (Subgroup.normalizer (R : Set G)) :=
    hpair.isGamma_of_le inf_le_right hcoreN
  have hcase : IsGamma2 M H ∨ (IsGammaU M H ∧ IsGammaTop M (Subgroup.normalizer (R : Set G))) := by
    rcases hH with hU | h2
    · exact Or.inr ⟨hU, hpair.isGammaTop_of_le inf_le_right hcoreN
        (fun V hV => hU.1.card_le_of_isSylowTwoOf hSH hV)⟩
    · exact Or.inl h2
  obtain ⟨-, hSK, -, -, -⟩ := hH.overgroup_of_sylow_le h hS hKΓ hNS hcase
  obtain ⟨T', hST', hT'⟩ := exists_isSylowTwoOf_of_le hSc.1 hS.isPGroup
  have hne : S ≠ T' := by
    intro heq
    rw [heq, h.card_eq_of_isSylowTwoOf_M hT'] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨x, hx, hxS⟩ := exists_mem_inf_normalizer_of_ne (p := 2) hT'.isPGroup hST' hne
  have hlt' : S < T' ⊓ Subgroup.normalizer (S : Set G) :=
    lt_of_le_of_ne (le_inf hST' Subgroup.le_normalizer) fun heq => hxS (heq ▸ hx)
  have hle : T' ⊓ Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (R : Set G) :=
    inf_le_right.trans hSNS
  have hcard := CFSG.QuasithinUnique.card_le_twoPart hle (hT'.isPGroup.to_le inf_le_left)
  rw [← hSK.card_eq] at hcard
  exact absurd (Subgroup.card_lt_of_lt hlt') (not_lt.mpr hcard)

theorem IsGamma0.iSup_normalizer_inf_le_of_characteristic (h : UniqueSetting G T M)
    {H S : Subgroup G} (hH : IsGamma0 M H) (hchar : CharTwo H) (hS : IsSylowTwoOf S (H ⊓ M)) :
    (⨆ R : Subgroup G, ⨆ (_ : R ≠ ⊥ ∧ R ≤ S ∧ (R.subgroupOf S).Characteristic),
      H ⊓ Subgroup.normalizer (R : Set G)) ≤ H ⊓ M :=
  iSup₂_le fun _ hR =>
    hH.normalizer_inf_le_of_characteristic h hchar hS hR.1 hR.2.1 hR.2.2

end CharacteristicNormalizers

section ConstrainedContainment

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem IsGamma0.le_of_charTwo_of_forall_not_charTwo (h : UniqueSetting G T M)
    (hno : ∀ K : Subgroup G, IsGamma0 M K → ¬ CharTwo K) {H S : Subgroup G}
    (hH : IsGamma0 M H) (hS : IsSylowTwoOf S (H ⊓ M)) {X : Subgroup G} (hSX : S ≤ X)
    (hX : CharTwo X) : X ≤ M := by
  obtain ⟨hSH, hSc, -⟩ := IsGamma.sylow_properties h hH.isGamma hS
  by_contra hXM
  have hcoreX : pCoreOf 2 X ≠ ⊥ := by
    intro hbot
    have hXbot : X ≤ ⊥ := by
      intro x hx
      have hx' : x ∈ X ⊓ Subgroup.centralizer (pCoreOf 2 X : Set G) := by
        refine ⟨hx, ?_⟩
        rw [hbot]
        simp [Subgroup.mem_centralizer_iff]
      have := hX hx'
      rwa [hbot] at this
    exact hSc.2.1 (le_bot_iff.mp (hSX.trans hXbot))
  have hpair : IsWitnessPair M S X := ⟨hSc, hSX, hcoreX, hX, hXM⟩
  have hXΓ : IsGamma M X := hpair.isGamma_of_le le_rfl hcoreX
  have hH0 := hH
  rcases hH with hU | h2
  · have hXtop : IsGammaTop M X :=
      hpair.isGammaTop_of_le le_rfl hcoreX (fun V hV => hU.1.card_le_of_isSylowTwoOf hSH hV)
    obtain ⟨hX0, -, -, -, -⟩ := IsGamma0.overgroup_of_sylow_le h hH0 hS hXΓ hSX
      (Or.inr ⟨hU, hXtop⟩)
    exact hno X hX0 hX
  · obtain ⟨hX0, -, -, -, -⟩ := IsGamma0.overgroup_of_sylow_le h hH0 hS hXΓ hSX (Or.inl h2)
    exact hno X hX0 hX

theorem IsGamma0.maximal_inf_of_forall_not_charTwo (h : UniqueSetting G T M)
    (hno : ∀ K : Subgroup G, IsGamma0 M K → ¬ CharTwo K) {H S : Subgroup G}
    (hH : IsGamma0 M H) (hS : IsSylowTwoOf S (H ⊓ M)) (hHM : CharTwo (H ⊓ M)) :
    (H ⊓ M ≤ H ∧ S ≤ H ⊓ M ∧ CharTwo (H ⊓ M)) ∧
      (∀ X : Subgroup G, X ≤ H → S ≤ X → CharTwo X → X ≤ H ⊓ M) ∧
      Maximal (fun X : Subgroup G => X ≤ H ∧ S ≤ X ∧ CharTwo X) (H ⊓ M) ∧
      ∀ X : Subgroup G, Maximal (fun X : Subgroup G => X ≤ H ∧ S ≤ X ∧ CharTwo X) X →
        X = H ⊓ M := by
  have hmem : H ⊓ M ≤ H ∧ S ≤ H ⊓ M ∧ CharTwo (H ⊓ M) := ⟨inf_le_left, hS.le, hHM⟩
  have hgreat : ∀ X : Subgroup G, X ≤ H → S ≤ X → CharTwo X → X ≤ H ⊓ M :=
    fun X hXH hSX hX => le_inf hXH (hH.le_of_charTwo_of_forall_not_charTwo h hno hS hSX hX)
  refine ⟨hmem, hgreat, ⟨hmem, fun Y hY _ => hgreat Y hY.1 hY.2.1 hY.2.2⟩, fun X hX => ?_⟩
  have hXle := hgreat X hX.1.1 hX.1.2.1 hX.1.2.2
  exact le_antisymm hXle (hX.2 hmem hXle)

end ConstrainedContainment

section UnconstrainedConfiguration

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem exists_unconstrained_normalizer_configuration (h : UniqueSetting G T M)
    (hδ : ∃ D : Subgroup G, IsEscaping M D)
    (hno : ∀ K : Subgroup G, IsGamma0 M K → ¬ CharTwo K) :
    ∃ B H S : Subgroup G, B ≠ ⊥ ∧ IsPGroup 2 B ∧ H = Subgroup.normalizer (B : Set G) ∧
      IsGammaU M H ∧ IsSylowTwoOf S (H ⊓ M) ∧ IsSylowTwoOf S H ∧ IsConfining M S ∧ S < T ∧
      pCoreOf 2 H ≠ ⊥ ∧ pCoreOf 2 M ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ≤ S ∧
      T ⊓ Subgroup.centralizer (T : Set G) ≤ S ⊓ Subgroup.centralizer (S : Set G) ∧
      (∀ z ∈ T ⊓ Subgroup.centralizer (T : Set G), z ≠ 1 →
        Subgroup.centralizer ({z} : Set G) ≤ M) ∧
      ∀ X : Subgroup G, S ≤ X → CharTwo X → X ≤ M := by
  obtain ⟨-, -, -, -, ⟨H₀, hH₀⟩, -, -⟩ := exists_witness_families_of_isEscaping h hδ
  have hH₀0 : IsGamma0 M H₀ := Or.inl hH₀
  obtain ⟨S₀, hS₀⟩ := exists_isSylowTwoOf (H₀ ⊓ M)
  obtain ⟨hB₀, -, -, -, -, hUN, -⟩ := hH₀0.core_normalizer h hS₀
  have hH₁ : IsGammaU M (Subgroup.normalizer (pCoreOf 2 H₀ : Set G)) := hUN hH₀
  obtain ⟨S₁, hS₁⟩ := exists_isSylowTwoOf (Subgroup.normalizer (pCoreOf 2 H₀ : Set G) ⊓ M)
  obtain ⟨hS₁H, hS₁c, -⟩ := IsGamma.sylow_properties h hH₁.isGamma hS₁
  obtain ⟨T', hS₁T', hT'⟩ := exists_isSylowTwoOf_of_le hS₁c.1 hS₁H.isPGroup
  obtain ⟨m, hmM, hmT⟩ := hT'.exists_conj h.isSylowTwoOf_M
  have hf := map_conj_eq_self_of_mem hmM
  have hST : S₁.map (MulAut.conj m).toMonoidHom ≤ T := by
    rw [hmT]
    exact Subgroup.map_mono hS₁T'
  have hH : IsGammaU M ((Subgroup.normalizer (pCoreOf 2 H₀ : Set G)).map
      (MulAut.conj m).toMonoidHom) := hH₁.map_equiv hf
  have hSyl : IsSylowTwoOf (S₁.map (MulAut.conj m).toMonoidHom)
      ((Subgroup.normalizer (pCoreOf 2 H₀ : Set G)).map (MulAut.conj m).toMonoidHom ⊓ M) := by
    have := hS₁.map_equiv (MulAut.conj m)
    rwa [map_equiv_inf, hf] at this
  have hSH := hS₁H.map_equiv (MulAut.conj m)
  have hSc := hS₁c.map_equiv hf
  have hH0 : IsGamma0 M ((Subgroup.normalizer (pCoreOf 2 H₀ : Set G)).map
      (MulAut.conj m).toMonoidHom) := Or.inl hH
  obtain ⟨hcentre, hlt, hcent⟩ :=
    hH0.center_le_of_le_sylow h hSyl h.isSylowTwoOf_M hST
  refine ⟨(pCoreOf 2 H₀).map (MulAut.conj m).toMonoidHom,
    (Subgroup.normalizer (pCoreOf 2 H₀ : Set G)).map (MulAut.conj m).toMonoidHom,
    S₁.map (MulAut.conj m).toMonoidHom, ?_, ?_, ?_, hH, hSyl, hSH, hSc, hlt, ?_,
    hH0.core_centralizer_le h hSyl, hcentre, hcent,
    fun X hSX hX => hH0.le_of_charTwo_of_forall_not_charTwo h hno hSyl hSX hX⟩
  · exact fun hb => hB₀ ((map_equiv_eq_bot_iff _ _).mp hb)
  · exact (isPGroup_map_equiv_iff 2 _ _).mpr
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H₀)
  · exact (normalizer_map_equiv _ _).symm
  · exact (hH0.core_normalizer h hSyl).1

end UnconstrainedConfiguration

end CFSG.QuasithinUnique
