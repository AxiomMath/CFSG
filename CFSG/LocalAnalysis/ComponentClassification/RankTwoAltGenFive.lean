module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltGenSmallRoot
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltGenLocal
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltGenCent
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveCaseIDefs
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XTheorem4
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2S0LeQuotientTorus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import CFSG.Timmesfeld.Opposite.Moufang
public import CFSG.Timmesfeld.RankOne

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup

@[expose] def treeEven : Subgroup (Perm (Fin 4 × Fin 2)) :=
  treePerm ⊓ alternatingGroup (Fin 4 × Fin 2)

theorem sign_pairFlip_zero : sign (pairFlip (fun k => decide (k = 0))) = -1 := by
  decide

theorem pairFlip_zero_mem_treePerm : pairFlip (fun k => decide (k = 0)) ∈ treePerm :=
  ⟨1, one_mem _, fun k => decide (k = 0), by rw [map_one, one_mul]⟩

theorem card_treeEven : Nat.card treeEven = 2 ^ 6 := by
  let f : treePerm →* ℤˣ := sign.comp treePerm.subtype
  have hf : Function.Surjective f := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, map_one f⟩
    · exact ⟨⟨_, pairFlip_zero_mem_treePerm⟩, sign_pairFlip_zero⟩
  have h1 := card_ker_mul_card_range f
  rw [MonoidHom.range_eq_top.mpr hf, Subgroup.card_top, Nat.card_eq_fintype_card (α := ℤˣ),
    Fintype.card_units_int, card_treePerm] at h1
  have hker : f.ker = treeEven.subgroupOf treePerm := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    constructor
    · intro hx
      exact ⟨x.2, mem_alternatingGroup.mpr hx⟩
    · intro hx
      exact mem_alternatingGroup.mp hx.2
  have h2 : Nat.card f.ker = Nat.card treeEven := by
    rw [hker]
    exact Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [h2] at h1
  omega

theorem treeEven_le_alternatingGroup : treeEven ≤ alternatingGroup (Fin 4 × Fin 2) :=
  inf_le_right

section Embed

variable {N : ℕ}

@[expose] noncomputable def treeEvenAlt (h : 2 * 4 ≤ N) : Subgroup (alternatingGroup (Fin N)) :=
  (treeEven.subgroupOf (alternatingGroup (Fin 4 × Fin 2))).map (pairAlt h)

theorem card_treeEvenAlt (h : 2 * 4 ≤ N) : Nat.card (treeEvenAlt h) = 2 ^ 6 := by
  rw [treeEvenAlt, Subgroup.card_map_of_injective (pairAlt_injective h), ← card_treeEven]
  exact Nat.card_congr (subgroupOfEquivOfLe treeEven_le_alternatingGroup).toEquiv

theorem treeEvenAlt_le_centralizer (h : 2 * 4 ≤ N) :
    treeEvenAlt h ≤ centralizer ({pairAlt h (zAlt (m := 4) ⟨2, rfl⟩)} :
      Set (alternatingGroup (Fin N))) := by
  rintro _ ⟨y, hy, rfl⟩
  have hy' : (y : Perm (Fin 4 × Fin 2)) ∈ treePerm := (mem_subgroupOf.mp hy).1
  have hyz : y * zAlt (m := 4) ⟨2, rfl⟩ = zAlt (m := 4) ⟨2, rfl⟩ * y :=
    Subtype.ext (treePerm_commute_zPair hy')
  rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hyz]

theorem exists_card_eq_le_centralizer_of_cycleType_even (h : 2 * 4 ≤ N)
    {π : alternatingGroup (Fin N)} (hπ : (π : Perm (Fin N)).cycleType = {2, 2, 2, 2}) :
    ∃ P : Subgroup (alternatingGroup (Fin N)), Nat.card P = 2 ^ 6 ∧
      P ≤ centralizer ({π} : Set (alternatingGroup (Fin N))) := by
  set z := pairAlt h (zAlt (m := 4) ⟨2, rfl⟩) with hz
  have hzc : (z : Perm (Fin N)).cycleType = (π : Perm (Fin N)).cycleType := by
    rw [hz, coe_pairAlt, cycleType_viaEmbeddingHom', hπ]
    exact cycleType_zPair
  have hzz : zAlt (m := 4) ⟨2, rfl⟩ * zAlt (m := 4) ⟨2, rfl⟩ = 1 := zAlt_mul_self _
  have hz2 : z * z = 1 := by rw [hz, ← map_mul, hzz, map_one]
  have hz1 : z ≠ 1 := fun h1 =>
    zAlt_ne_one _ (by norm_num) (pairAlt_injective _ (h1.trans (map_one _).symm))
  obtain ⟨β, hβ⟩ := exists_conj_eq_of_cycleType_eq hzc hz2 hz1
  refine ⟨(treeEvenAlt h).map (MulAut.conj β).toMonoidHom, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (MulAut.conj β).injective, card_treeEvenAlt]
  · rintro _ ⟨y, hy, rfl⟩
    have hyz : y * z = z * y := mem_centralizer_singleton_iff.mp (treeEvenAlt_le_centralizer h hy)
    rw [mem_centralizer_singleton_iff, ← hβ]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc β * y * β⁻¹ * (β * z * β⁻¹) = β * (y * z) * β⁻¹ := by group
      _ = β * (z * y) * β⁻¹ := by rw [hyz]
      _ = β * z * β⁻¹ * (β * y * β⁻¹) := by group

end Embed

namespace AltGenCore

open CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.RankTwoStandard
  CFSG.ComponentClassification.RankTwoClassical CFSG.Quasithin.SteinbergCB

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G} {n : ℕ}
  {Φ : alternatingGroup (Fin (n + 4)) →* G} (s : AltGenCore A R T g n Φ)
include s

@[expose] noncomputable def actNat : normalizer (A : Set G) →* MulAut (alternatingGroup (Fin n)) :=
  (MulAut.congr s.psiNat.symm).toMonoidHom.comp (Lemma39.normConj A)

theorem actNat_spec (x : normalizer (A : Set G)) (z : alternatingGroup (Fin n)) :
    Φ (liftNat n (s.actNat x z)) = (x : G) * Φ (liftNat n z) * (x : G)⁻¹ := by
  show Φ (liftNat n ((MulAut.congr s.psiNat.symm) (Lemma39.normConj A x) z)) = _
  rw [MulAut.congr_apply, MulEquiv.symm_symm, MulEquiv.trans_apply, MulEquiv.trans_apply,
    ← psiNat_apply s, MulEquiv.apply_symm_apply, Lemma39.normConj_apply, psiNat_apply]

theorem actNat_eq_one_iff (x : normalizer (A : Set G)) :
    s.actNat x = 1 ↔ (x : G) ∈ centralizer (A : Set G) := by
  constructor
  · intro h
    rw [mem_centralizer_iff]
    intro a ha
    obtain ⟨z, rfl⟩ := s.exists_liftNat_eq ha
    have h1 := s.actNat_spec x z
    rw [h, MulAut.one_apply] at h1
    calc Φ (liftNat n z) * (x : G) = (x : G) * Φ (liftNat n z) * (x : G)⁻¹ * x := by rw [← h1]
      _ = x * Φ (liftNat n z) := by group
  · intro h
    ext z : 1
    apply liftNat_injective
    apply s.injective
    rw [s.actNat_spec, MulAut.one_apply]
    have hc : Φ (liftNat n z) * (x : G) = x * Φ (liftNat n z) :=
      mem_centralizer_iff.mp h _ (s.liftNat_mem z)
    calc (x : G) * Φ (liftNat n z) * (x : G)⁻¹ = Φ (liftNat n z) * x * (x : G)⁻¹ := by rw [hc]
      _ = Φ (liftNat n z) := by group

end AltGenCore

namespace AltGenCore

open CFSG.Open CFSG.ABGLocalTools CFSG.Blueprint
  CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoClassical
  CFSG.Quasithin.SteinbergCB

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G}
  {Φ : alternatingGroup (Fin (5 + 4)) →* G} (s : AltGenCore A R T g 5 Φ)
include s

theorem card_le_of_isPGroup_le_normalizer_five {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPN : P ≤ normalizer (A : Set G)) : Nat.card P ≤ 2 ^ 5 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f : ↥P →* MulAut (alternatingGroup (Fin 5)) := s.actNat.comp (inclusion hPN) with hf
  have hker : Nat.card f.ker ≤ 4 := by
    have h1 : Nat.card f.ker = Nat.card (f.ker.map P.subtype) :=
      (Subgroup.card_map_of_injective P.subtype_injective).symm
    rw [h1]
    refine s.card_le_four_of_isPGroup_centralizer (hP.to_le (Subgroup.map_subtype_le f.ker)) ?_
    rintro _ ⟨y, hy, rfl⟩
    have hy' : f y = 1 := hy
    rw [hf, MonoidHom.comp_apply] at hy'
    exact (s.actNat_eq_one_iff _).mp hy'
  have himg : Nat.card f.range ≤ 2 ^ 3 := by
    obtain ⟨a, ha⟩ := (hP.of_surjective f.rangeRestrict f.rangeRestrict_surjective).exists_card_eq
    have hcard : Nat.card (MulAut (alternatingGroup (Fin 5))) = 120 := by
      rw [← Nat.card_congr (Equiv.ofBijective (conjPerm 5)
        ⟨conjPerm_injective (by norm_num), conjPerm_surjective (Or.inl rfl)⟩), Nat.card_perm,
        Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
    have hdvd : Nat.card f.range ∣ 120 := hcard ▸ Subgroup.card_subgroup_dvd_card f.range
    rw [ha] at hdvd ⊢
    have hle : a ≤ 3 := by
      by_contra hgt
      have h4 : 2 ^ 4 ∣ 120 := (Nat.pow_dvd_pow 2 (by omega)).trans hdvd
      exact absurd h4 (by decide)
    exact Nat.pow_le_pow_right (by norm_num) hle
  have h := card_ker_mul_card_range f
  calc Nat.card P = Nat.card f.ker * Nat.card f.range := h.symm
    _ ≤ 4 * 2 ^ 3 := Nat.mul_le_mul hker himg
    _ = 2 ^ 5 := by norm_num

theorem rootFusionAt_five : RootFusionAt A Φ := by
  intro π x hπ2 hπ1 hx
  have hπ2' : (π : Perm (Fin (5 + 4))) * π = 1 := by
    rw [← Subgroup.coe_mul, hπ2]
    rfl
  have hπ1' : (π : Perm (Fin (5 + 4))) ≠ 1 := fun h => hπ1 (Subtype.ext h)
  obtain ⟨j, hj1, hct, hj4⟩ := exists_cycleType_eq_replicate hπ1' hπ2' π.2
  rw [Fintype.card_fin] at hj4
  rcases (by omega : j = 1 ∨ j = 2) with rfl | rfl
  · rw [hct]
    rfl
  · exfalso
    obtain ⟨P, hPcard, hPC⟩ := exists_card_eq_le_centralizer_of_cycleType_even
      (N := 5 + 4) (by norm_num) (π := π) (by rw [hct]; rfl)
    set t := x * Φ π * x⁻¹ with ht
    have ht2 : t ^ 2 = 1 := by
      rw [sq, ht]
      calc x * Φ π * x⁻¹ * (x * Φ π * x⁻¹) = x * Φ (π * π) * x⁻¹ := by rw [map_mul]; group
        _ = 1 := by rw [hπ2, map_one, mul_one, mul_inv_cancel]
    have ht1 : t ≠ 1 := by
      intro h1
      apply hπ1
      apply s.injective
      rw [map_one]
      calc Φ π = x⁻¹ * (x * Φ π * x⁻¹) * x := by group
        _ = 1 := by rw [← ht, h1, mul_one, inv_mul_cancel]
    have hCN : centralizer ({t} : Set G) ≤ normalizer (A : Set G) := by
      have h := Lemma39.centralizer_le_normalizer_rightConjugate s.sec3.hyp 1 (t := t)
        (by rw [rightConjugate_one]; exact hx) ht1 ht2
      rwa [rightConjugate_one] at h
    set P' : Subgroup G := (P.map Φ).map (MulAut.conj x).toMonoidHom with hP'
    have hP'card : Nat.card P' = 2 ^ 6 := by
      rw [hP', Subgroup.card_map_of_injective (MulAut.conj x).injective,
        Subgroup.card_map_of_injective s.injective, hPcard]
    have hP'N : P' ≤ normalizer (A : Set G) := by
      refine le_trans ?_ hCN
      rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      have hpπ : p * π = π * p := mem_centralizer_singleton_iff.mp (hPC hp)
      rw [mem_centralizer_singleton_iff]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ht]
      calc x * Φ p * x⁻¹ * (x * Φ π * x⁻¹) = x * Φ (p * π) * x⁻¹ := by rw [map_mul]; group
        _ = x * Φ (π * p) * x⁻¹ := by rw [hpπ]
        _ = x * Φ π * x⁻¹ * (x * Φ p * x⁻¹) := by rw [map_mul]; group
    have h := s.card_le_of_isPGroup_le_normalizer_five (IsPGroup.of_card hP'card) hP'N
    rw [hP'card] at h
    exact absurd h (by norm_num)

theorem rankTwoX_eq_five
    (h34 : Asc08Lemma34) (hGA : Asc76X.GoldschmidtTheoremA) :
    rankTwoX A = A ⊔ rightConjugate A g :=
  s.rankTwoX_eq_of_local h34 (s.normalizer_le_of (Or.inl rfl)) s.rootFusionAt_five
    (s.typeTwoCentralizerAt_of hGA (s.normalizer_le_of (Or.inl rfl)) s.rootFusionAt_five)

end AltGenCore

theorem altGenerationFive_of
    (h34 : AS76b.Asc08Lemma34) (hGA : Asc76X.GoldschmidtTheoremA) : AltGenerationFive :=
  fun _ _ _ _ _ _ _ _ s => s.rankTwoX_eq_five h34 hGA

end CFSG.ComponentClassification.RankTwoAlt
