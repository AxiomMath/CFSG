module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLift
public import CFSG.GroupTheory.ABGLocalTools.Basic

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ABGLocalTools

variable {X : Type} [Group X]

@[expose] def centralizerResidual (L : Subgroup X) (g : X) : Subgroup X :=
  (perfectResidual ↥(L ⊓ centralizer {g})).map (L ⊓ centralizer {g}).subtype

variable {L : Subgroup X} {g : X}

theorem centralizerResidual_le : centralizerResidual L g ≤ L ⊓ centralizer {g} :=
  map_subtype_le _

theorem centralizerResidual_le_left : centralizerResidual L g ≤ L :=
  centralizerResidual_le.trans inf_le_left

theorem le_normalizer_centralizerResidual [Finite X] :
    L ⊓ centralizer {g} ≤ normalizer (centralizerResidual L g : Set X) := by
  have : (perfectResidual ↥(L ⊓ centralizer {g})).Characteristic :=
    perfect_residual_characterization.2.1
  exact le_normalizer.trans
    (UnbalancedGS.normalizer_le_normalizer_map_of_characteristic _ _)

theorem relIndex_mul_card {Y : Type*} [Group Y] {A B : Subgroup Y} (hBA : B ≤ A) :
    B.relIndex A * Nat.card B = Nat.card A := by
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBA).toEquiv, mul_comm]
  exact (B.subgroupOf A).card_mul_index

theorem perfectResidual_map_mono {Y : Type*} [Group Y] [Finite Y] {M H : Subgroup Y}
    (hMH : M ≤ H) : (perfectResidual ↥M).map M.subtype ≤ (perfectResidual ↥H).map H.subtype := by
  have h1 := (perfect_residual_transport (Subgroup.inclusion hMH)).1
  have h2 := (perfect_residual_transport (MonoidHom.id ↥H)).2.1
  have h3 : (perfectResidual ↥M).map (Subgroup.inclusion hMH) ≤ perfectResidual ↥H := by
    rw [h1]
    exact h2 _
  have h4 := Subgroup.map_mono (f := H.subtype) h3
  rwa [Subgroup.map_map, Subgroup.subtype_comp_inclusion] at h4

theorem isPerfect_perfectResidual_map {Y : Type*} [Group Y] [Finite Y] (C : Subgroup Y) :
    Group.IsPerfect ↥((perfectResidual ↥C).map C.subtype) := by
  have : Group.IsPerfect ↥(perfectResidual ↥C) := perfect_residual_characterization.2.2.1
  exact Group.IsPerfect.ofSurjective
    (f := (equivMapOfInjective (perfectResidual ↥C) C.subtype C.subtype_injective).toMonoidHom)
    (MulEquiv.surjective _)

theorem le_perfectResidual_map {Y : Type*} [Group Y] [Finite Y] {P C : Subgroup Y} (hPC : P ≤ C)
    (hP : Group.IsPerfect ↥P) : P ≤ (perfectResidual ↥C).map C.subtype := by
  have hP' : Group.IsPerfect ↥(P.subgroupOf C) := Group.IsPerfect.ofSurjective
    (f := (Subgroup.subgroupOfEquivOfLe hPC).symm.toMonoidHom) (MulEquiv.surjective _)
  have h := (perfect_residual_transport (MonoidHom.id ↥C)).2.2 (P.subgroupOf C) hP'
  intro x hx
  exact ⟨⟨x, hPC hx⟩, h hx, rfl⟩

theorem le_normalizer_perfectResidual_map {Y : Type*} [Group Y] [Finite Y] (C : Subgroup Y) :
    C ≤ normalizer (((perfectResidual ↥C).map C.subtype : Subgroup Y) : Set Y) := by
  have : (perfectResidual ↥C).Characteristic := perfect_residual_characterization.2.1
  exact le_normalizer.trans (UnbalancedGS.normalizer_le_normalizer_map_of_characteristic _ _)

variable [Finite X]

theorem range_facts (hg : g ∈ normalizer (L : Set X))
    (hg2 : IsPGroup 2 (zpowers g)) {p f : ℕ} (hp2 : p ≠ 2)
    (hP : Blueprint.LieModel ↥(perfectResidual ↥(fixedPoints (barAction L ⟨g, hg⟩))) .PSL 2 p f) :
    IsSimpleGroup ↥(barMap L (centralizerResidual_le_left (g := g))).range ∧
      Even (Nat.card ↥(barMap L (centralizerResidual_le_left (g := g))).range) ∧
      Nonempty (↥(barMap L (centralizerResidual_le_left (g := g))).range ≃*
        ↥(perfectResidual ↥(fixedPoints (barAction L ⟨g, hg⟩)))) := by
  set A := fixedPoints (barAction L ⟨g, hg⟩)
  have hrange : (barMap L (centralizerResidual_le_left (g := g))).range =
      (perfectResidual ↥A).map A.subtype := range_barMap_perfectResidual hg hg2
  let e : ↥(barMap L (centralizerResidual_le_left (g := g))).range ≃* ↥(perfectResidual ↥A) :=
    (MulEquiv.subgroupCongr hrange).trans
      (equivMapOfInjective (perfectResidual ↥A) A.subtype A.subtype_injective).symm
  have := isSimpleGroup_of_lieModel_psl2 hP
  refine ⟨e.isSimpleGroup, ?_, ⟨e⟩⟩
  rw [Nat.card_congr e.toEquiv]
  exact even_card_of_lieModel_psl2 hp2 hP

theorem coprime_card_ker_barMap {K : Subgroup X} (hKL : K ≤ L) :
    Nat.Coprime 2 (Nat.card (barMap L hKL).ker) := by
  have hle : (barMap L hKL).ker.map K.subtype ≤ (pPrimeCore 2 ↥L).map L.subtype := by
    rintro _ ⟨k, hk, rfl⟩
    exact (mem_ker_barMap hKL k).mp hk
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [Subgroup.card_map_of_injective K.subtype_injective,
    Subgroup.card_map_of_injective L.subtype_injective] at hdvd
  exact Nat.Coprime.coprime_dvd_right hdvd pPrimeCore_coprime_card

theorem ker_barMap_le_pPrimeCore {K : Subgroup X} (hKL : K ≤ L) :
    (barMap L hKL).ker ≤ pPrimeCore 2 ↥K :=
  le_sSup ⟨MonoidHom.normal_ker _, coprime_card_ker_barMap hKL⟩

theorem odd_card_map_pPrimeCore {Y Z : Type*} [Group Y] [Finite Y] [Group Z] (φ : Y →* Z) :
    Odd (Nat.card ((pPrimeCore 2 Y).map φ)) := by
  have hcop : Nat.Coprime 2 (Nat.card ((pPrimeCore 2 Y).map φ)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ _) pPrimeCore_coprime_card
  exact Nat.odd_iff.mpr (by
    rcases Nat.even_or_odd (Nat.card ((pPrimeCore 2 Y).map φ)) with he | ho
    · exact absurd (Nat.Coprime.eq_one_of_dvd hcop (even_iff_two_dvd.mp he)) (by norm_num)
    · exact Nat.odd_iff.mp ho)

theorem conj_mem_map_pPrimeCore {Y Z : Type*} [Group Y] [Group Z] (φ : Y →* Z) :
    ∀ a ∈ φ.range, ∀ n ∈ (pPrimeCore 2 Y).map φ, a * n * a⁻¹ ∈ (pPrimeCore 2 Y).map φ := by
  rintro _ ⟨a, rfl⟩ _ ⟨n, hn, rfl⟩
  exact ⟨a * n * a⁻¹, (pPrimeCore_normal (p := 2) (G := Y)).conj_mem n hn a, by simp⟩

theorem pPrimeCore_centralizerResidual (hg : g ∈ normalizer (L : Set X))
    (hg2 : IsPGroup 2 (zpowers g)) {p f : ℕ} (hp2 : p ≠ 2)
    (hP : Blueprint.LieModel ↥(perfectResidual ↥(fixedPoints (barAction L ⟨g, hg⟩))) .PSL 2 p f) :
    pPrimeCore 2 ↥(centralizerResidual L g) =
      (barMap L (centralizerResidual_le_left (g := g))).ker := by
  obtain ⟨hsimp, heven, -⟩ := range_facts hg hg2 hp2 hP
  apply le_antisymm _ (ker_barMap_le_pPrimeCore _)
  have hN := eq_bot_of_odd_of_simple le_rfl (by rw [relIndex_self]; norm_num) hsimp heven
    (map_le_range _ _) (conj_mem_map_pPrimeCore _) (odd_card_map_pPrimeCore _)
  rwa [Subgroup.map_eq_bot_iff] at hN

theorem map_pPrimeCore_centralizerResidual (hg : g ∈ normalizer (L : Set X))
    (hg2 : IsPGroup 2 (zpowers g)) {p f : ℕ} (hp2 : p ≠ 2)
    (hP : Blueprint.LieModel ↥(perfectResidual ↥(fixedPoints (barAction L ⟨g, hg⟩))) .PSL 2 p f) :
    (pPrimeCore 2 ↥(centralizerResidual L g)).map (centralizerResidual L g).subtype =
      centralizerResidual L g ⊓ (pPrimeCore 2 ↥L).map L.subtype := by
  rw [pPrimeCore_centralizerResidual hg hg2 hp2 hP]
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k.2, (mem_ker_barMap _ k).mp hk⟩
  · rintro ⟨hxK, hxO⟩
    exact ⟨⟨x, hxK⟩, (mem_ker_barMap _ ⟨x, hxK⟩).mpr hxO, rfl⟩

theorem lieModel_bar_centralizerResidual (hg : g ∈ normalizer (L : Set X))
    (hg2 : IsPGroup 2 (zpowers g)) {p f : ℕ} (hp2 : p ≠ 2)
    (hP : Blueprint.LieModel ↥(perfectResidual ↥(fixedPoints (barAction L ⟨g, hg⟩))) .PSL 2 p f) :
    Blueprint.LieModel (Bar (centralizerResidual L g)) .PSL 2 p f := by
  obtain ⟨-, -, ⟨e⟩⟩ := range_facts hg hg2 hp2 hP
  refine lieModel_psl2_of_mulEquiv ?_ hP
  exact ((QuotientGroup.quotientMulEquivOfEq (pPrimeCore_centralizerResidual hg hg2 hp2 hP)).trans
    (QuotientGroup.quotientKerEquivRange _)).trans e

theorem pPrimeCore_centralizer (hg : g ∈ normalizer (L : Set X))
    (hg2 : IsPGroup 2 (zpowers g)) {p f : ℕ} (hp2 : p ≠ 2)
    (hP : Blueprint.LieModel ↥(perfectResidual ↥(fixedPoints (barAction L ⟨g, hg⟩))) .PSL 2 p f)
    (hPA : 2 * Nat.card ↥(perfectResidual ↥(fixedPoints (barAction L ⟨g, hg⟩))) =
      Nat.card ↥(fixedPoints (barAction L ⟨g, hg⟩))) :
    pPrimeCore 2 ↥(L ⊓ centralizer {g}) =
      (barMap L (inf_le_left : L ⊓ centralizer {g} ≤ L)).ker := by
  set A := fixedPoints (barAction L ⟨g, hg⟩)
  set B := (perfectResidual ↥A).map A.subtype
  have hrange : (barMap L (inf_le_left : L ⊓ centralizer {g} ≤ L)).range = A :=
    range_barMap_centralizer hg hg2
  have hBA : B ≤ A := map_subtype_le _
  have hcardB : Nat.card B = Nat.card (perfectResidual ↥A) :=
    Subgroup.card_map_of_injective A.subtype_injective
  have hrel : B.relIndex A = 2 := by
    have h1 := relIndex_mul_card hBA
    rw [← hPA, hcardB] at h1
    have hpos : 0 < Nat.card (perfectResidual ↥A) := Nat.card_pos
    nlinarith
  have hsimp : IsSimpleGroup ↥B := by
    have := isSimpleGroup_of_lieModel_psl2 hP
    exact (equivMapOfInjective (perfectResidual ↥A) A.subtype
      A.subtype_injective).symm.isSimpleGroup
  have heven : Even (Nat.card B) := by
    rw [hcardB]
    exact even_card_of_lieModel_psl2 hp2 hP
  apply le_antisymm _ (ker_barMap_le_pPrimeCore _)
  have hN := eq_bot_of_odd_of_simple hBA hrel.le hsimp heven
    (N := (pPrimeCore 2 ↥(L ⊓ centralizer {g})).map
      (barMap L (inf_le_left : L ⊓ centralizer {g} ≤ L)))
    (by rw [← hrange]; exact map_le_range _ _)
    (by rw [← hrange]; exact conj_mem_map_pPrimeCore _) (odd_card_map_pPrimeCore _)
  rwa [Subgroup.map_eq_bot_iff] at hN

theorem map_pPrimeCore_centralizer (hg : g ∈ normalizer (L : Set X))
    (hg2 : IsPGroup 2 (zpowers g)) {p f : ℕ} (hp2 : p ≠ 2)
    (hP : Blueprint.LieModel ↥(perfectResidual ↥(fixedPoints (barAction L ⟨g, hg⟩))) .PSL 2 p f)
    (hPA : 2 * Nat.card ↥(perfectResidual ↥(fixedPoints (barAction L ⟨g, hg⟩))) =
      Nat.card ↥(fixedPoints (barAction L ⟨g, hg⟩))) :
    (pPrimeCore 2 ↥(L ⊓ centralizer {g})).map (L ⊓ centralizer {g}).subtype =
      (L ⊓ centralizer {g}) ⊓ (pPrimeCore 2 ↥L).map L.subtype := by
  rw [pPrimeCore_centralizer hg hg2 hp2 hP hPA]
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k.2, (mem_ker_barMap _ k).mp hk⟩
  · rintro ⟨hxK, hxO⟩
    exact ⟨⟨x, hxK⟩, (mem_ker_barMap _ ⟨x, hxK⟩).mpr hxO, rfl⟩

theorem factorization_card_centralizerResidual (hg : g ∈ normalizer (L : Set X))
    (hg2 : IsPGroup 2 (zpowers g)) {p f : ℕ} (hp2 : p ≠ 2)
    (hP : Blueprint.LieModel ↥(perfectResidual ↥(fixedPoints (barAction L ⟨g, hg⟩))) .PSL 2 p f) :
    (Nat.card (centralizerResidual L g)).factorization 2 =
      (Nat.card ↥(perfectResidual ↥(fixedPoints (barAction L ⟨g, hg⟩)))).factorization 2 := by
  obtain ⟨-, -, ⟨e⟩⟩ := range_facts hg hg2 hp2 hP
  set φ := barMap L (centralizerResidual_le_left (g := g))
  have h1 : Nat.card (centralizerResidual L g) = Nat.card φ.range * Nat.card φ.ker := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
    exact φ.ker.card_eq_card_quotient_mul_card_subgroup
  rw [h1, ← Nat.card_congr e.toEquiv, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp (coprime_card_ker_barMap _)), add_zero]

theorem isSylowOf_inf_centralizerResidual {D : Subgroup X} (hD : IsSylowOf 2 D L)
    (hDg : D ≤ centralizer {g}) :
    IsSylowOf 2 (D ⊓ centralizerResidual L g) (centralizerResidual L g) :=
  (hD.of_le (le_inf hD.le hDg) inf_le_left).inf_of_le_normalizer centralizerResidual_le
    le_normalizer_centralizerResidual

theorem relIndex_inf_centralizerResidual (hg : g ∈ normalizer (L : Set X))
    (hg2 : IsPGroup 2 (zpowers g)) {p f : ℕ} (hp2 : p ≠ 2)
    (hP : Blueprint.LieModel ↥(perfectResidual ↥(fixedPoints (barAction L ⟨g, hg⟩))) .PSL 2 p f)
    (hPA : 2 * Nat.card ↥(perfectResidual ↥(fixedPoints (barAction L ⟨g, hg⟩))) =
      Nat.card ↥(fixedPoints (barAction L ⟨g, hg⟩)))
    (hA2 : (Nat.card ↥(fixedPoints (barAction L ⟨g, hg⟩))).factorization 2 =
      (Nat.card (Bar L)).factorization 2)
    {D : Subgroup X} (hD : IsSylowOf 2 D L) (hDg : D ≤ centralizer {g}) :
    (D ⊓ centralizerResidual L g).relIndex D = 2 := by
  have hK := factorization_card_centralizerResidual hg hg2 hp2 hP
  have hS := isSylowOf_inf_centralizerResidual hD hDg
  have hA : (Nat.card ↥(fixedPoints (barAction L ⟨g, hg⟩))).factorization 2 =
      (Nat.card ↥(perfectResidual ↥(fixedPoints (barAction L ⟨g, hg⟩)))).factorization 2 + 1 := by
    rw [← hPA, Nat.factorization_mul two_ne_zero Nat.card_pos.ne', Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_two, add_comm]
  have hL : (Nat.card L).factorization 2 = (Nat.card (Bar L)).factorization 2 := by
    rw [(pPrimeCore 2 ↥L).card_eq_card_quotient_mul_card_subgroup,
      Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp pPrimeCore_coprime_card), add_zero]
  have h1 := relIndex_mul_card (inf_le_left : D ⊓ centralizerResidual L g ≤ D)
  rw [hS.card_eq, hD.card_eq, hK, hL, ← hA2, hA, pow_succ] at h1
  exact Nat.eq_of_mul_eq_mul_right (pow_pos two_pos _) (h1.trans (mul_comm _ _))

theorem dihedral_inf_centralizerResidual (hg : g ∈ normalizer (L : Set X))
    (hg2 : IsPGroup 2 (zpowers g)) {p f : ℕ} (hp2 : p ≠ 2)
    (hP : Blueprint.LieModel ↥(perfectResidual ↥(fixedPoints (barAction L ⟨g, hg⟩))) .PSL 2 p f)
    {D : Subgroup X} (hD : IsSylowOf 2 D L) (hDg : D ≤ centralizer {g}) :
    ∃ m : ℕ, 1 ≤ m ∧ Nonempty (↥(D ⊓ centralizerResidual L g) ≃* DihedralGroup (2 ^ m)) := by
  obtain ⟨-, -, ⟨e⟩⟩ := range_facts hg hg2 hp2 hP
  set φ := barMap L (centralizerResidual_le_left (g := g))
  have hdih : GorensteinWalter.HasDihedralSylowTwo ↥φ.range :=
    hasDihedralSylowTwo_of_mulEquiv e (hasDihedralSylowTwo_of_lieModel_psl2 hp2 hP)
  obtain ⟨Q, hQ⟩ := (isSylowOf_inf_centralizerResidual hD hDg).exists_sylow_eq_subgroupOf
  obtain ⟨m, hm, ⟨d⟩⟩ := hdih (Q.mapSurjective φ.rangeRestrict_surjective)
  refine ⟨m, hm, ⟨?_⟩⟩
  have hinj : Function.Injective
      (φ.rangeRestrict.comp (Q : Subgroup ↥(centralizerResidual L g)).subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxk : (x : ↥(centralizerResidual L g)) ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      have := congrArg Subtype.val hx
      simpa using this
    obtain ⟨k, hk⟩ := Q.isPGroup' x
    have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    have h2 : orderOf (x : ↥(centralizerResidual L g)) ∣ Nat.card φ.ker :=
      Subgroup.orderOf_dvd_natCard φ.ker hxk
    rw [Subgroup.orderOf_coe] at h2
    have hcop : Nat.Coprime (2 ^ k) (Nat.card φ.ker) :=
      Nat.Coprime.pow_left k
        (coprime_card_ker_barMap (L := L) (centralizerResidual_le_left (g := g)))
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  refine ((Subgroup.subgroupOfEquivOfLe (inf_le_right : D ⊓ centralizerResidual L g ≤ _)).symm.trans
    ?_).trans d
  refine (MulEquiv.subgroupCongr hQ.symm).trans ?_
  refine (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr ?_)
  rw [MonoidHom.range_comp, Subgroup.range_subtype, Sylow.coe_mapSurjective]

end CFSG.ComponentClassification.HarrisLit
