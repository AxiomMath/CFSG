module

public import CFSG.CharacterTheory.Semidihedral.ProperSubgroupRegularity
public import CFSG.CharacterTheory.Semidihedral.LocalCoverFocal
public import CFSG.CharacterTheory.Wreathed.OriginalSylowNormalizerWitness

public noncomputable section

namespace CFSG.Semidihedral.LocalCoverFactorization

open CFSG.Open
open CFSG.TwoRankLowerBound.Helpers
open CFSG.Semidihedral.ProperSubgroupRegularity
open CFSG.Semidihedral.QuaternionFocalFactorization
open CFSG.Semidihedral.SameParameterInheritance
open CFSG.Semidihedral.StationaryOddLocalization
open CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.SameParameterRegularity
open CFSG.Semidihedral.SameParameterQuotientTransport
open CFSG.Semidihedral.Local
open CFSG.Semidihedral.Local.OddKernel
open CFSG.Semidihedral.LocalCoverFocal
open CFSG.Wreathed.OriginalSylowNormalizerWitness

theorem original_layer_cover_preserves_intrinsic_local_parameter
    {G : Type} [Group G] [Finite G] (U : Subgroup G) (t : U) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma (t : G)))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma (t : G)), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer
      (CFSG.generalizedFitting (Gamma (t : G)) : Set (Gamma (t : G))) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma (t : G))), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma (t : G))) .PSL 2 p f)
    (hcover : (U.subgroupOf (C (t : G)) ⊓
      ((CFSG.generalizedFitting (Gamma (t : G))).comap (barKappa (t : G))).comap
        (nu (t : G))).map (nu (t : G)) =
          (CFSG.generalizedFitting (Gamma (t : G))).comap (barKappa (t : G))) :
    let L := CFSG.generalizedFitting (Gamma (t : G))
    let LU := CFSG.generalizedFitting (Gamma t)
    IsSimpleGroup LU ∧ (∃ a b : LU, a * b ≠ b * a) ∧
      Subgroup.centralizer (LU : Set (Gamma t)) = ⊥ ∧
      (∀ P : Sylow 2 LU, ¬ IsCyclic P) ∧
      CFSG.Assembly.LowTwoRank.StatedClassicalModel LU .PSL 2 p f ∧
      (N t).map
        ((U.subgroupOf (C (t : G))).subtype.comp
          (subgroupCentralizerEquiv U t).toMonoidHom) =
        U.subgroupOf (C (t : G)) ⊓ N (t : G) ∧
      ∃ iota : Gamma t →* Gamma (t : G), Function.Injective iota ∧
        (∀ x : C t, iota (kappa t x) =
          kappa (t : G) (subgroupCentralizerEquiv U t x)) ∧
        iota.range = (U.subgroupOf (C (t : G))).map (kappa (t : G)) ∧
        LU.map iota = L ∧
        ∃ eL : LU ≃* L, ∀ x : LU, (eL x : Gamma (t : G)) = iota x := by
  intro L LU
  let B := U.subgroupOf (C (t : G))
  let R := CFSG.pPrimeCore 2 B
  let Delta := B ⧸ (R ⊔ (Z (t : G)).subgroupOf B)
  let J := CFSG.generalizedFitting Delta
  have htG : orderOf (t : G) = 2 := (Subgroup.orderOf_coe t).trans ht
  have htC : orderOf (tInC (t : G)) = 2 :=
    (Subgroup.orderOf_coe (tInC (t : G))).symm.trans htG
  have hLB : L ≤ B.map (kappa (t : G)) := by
    intro x hx
    obtain ⟨y, rfl⟩ := barKappa_surjective (t : G) x
    have hy : y ∈ L.comap (barKappa (t : G)) := hx
    obtain ⟨b, hb, rfl⟩ := hcover.ge hy
    exact ⟨b, hb.1, rfl⟩
  obtain ⟨hR, iotaB, hinjB, hrepB, hrangeB, hJB, hJcentral, ⟨eJ, _⟩,
      hJmodel, hJnc⟩ := centralizer_layer_cover_preserves_actual_local_parameter
    (tInC (t : G)) (tInC_central (t : G)) htC hnonab
      (even_card_of_noncyclic_sylow hnc) hcentral B t.property hLB
  have : IsSimpleGroup J := eJ.isSimpleGroup
  have hJnonab : ∃ a b : J, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    refine ⟨eJ.symm a, eJ.symm b, fun h => hab ?_⟩
    simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg eJ h
  let theta : Gamma t ≃* Delta := subgroupGammaEquiv U t
  have hJmap : J.map theta.symm.toMonoidHom = LU :=
    generalizedFitting_map_of_mulEquiv theta.symm hJnonab hJcentral
  let eU : J ≃* LU := (J.equivMapOfInjective theta.symm.toMonoidHom
    theta.symm.injective).trans (MulEquiv.subgroupCongr hJmap)
  have hLUsimple : IsSimpleGroup LU := eU.symm.isSimpleGroup
  have hLUnonab : ∃ a b : LU, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hJnonab
    refine ⟨eU a, eU b, fun h => hab (eU.injective ?_)⟩
    simpa only [map_mul] using h
  have hLUcentral : Subgroup.centralizer (LU : Set (Gamma t)) = ⊥ := by
    rw [← hJmap]
    exact centralizer_map_eq_bot_of_mulEquiv theta.symm J hJcentral
  have hLUnc : ∀ P : Sylow 2 LU, ¬ IsCyclic P :=
    not_isCyclic_sylow_of_mulEquiv eU.symm (hJnc hnc)
  have hLUmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel LU .PSL 2 p f :=
    statedClassicalModel_PSL_of_mulEquiv eU.symm (hJmodel p f hp hpodd hf hmodel)
  let iota := iotaB.comp theta.toMonoidHom
  have hthetaLU : LU.map theta.toMonoidHom = J := by
    rw [← hJmap, Subgroup.map_map]
    have hcomp : theta.toMonoidHom.comp theta.symm.toMonoidHom = MonoidHom.id Delta := by
      ext x
      exact theta.apply_symm_apply x
    rw [hcomp, Subgroup.map_id]
  have hLUmap : LU.map iota = L := by
    rw [← Subgroup.map_map, hthetaLU]
    exact hJB
  have hcore : (N t).map (B.subtype.comp (subgroupCentralizerEquiv U t).toMonoidHom) =
      B ⊓ N (t : G) := by
    change (N t).map
      ((Subgroup.comap (C (t : G)).subtype U).subtype.comp
        (subgroupCentralizerEquiv U t).toMonoidHom) =
      Subgroup.comap (C (t : G)).subtype U ⊓ N (t : G)
    rw [← Subgroup.map_map, subgroupCentralizerEquiv_oddCore]
    exact hR
  refine ⟨hLUsimple, hLUnonab, hLUcentral, hLUnc, hLUmodel, hcore, iota,
    hinjB.comp theta.injective, ?_, ?_, hLUmap, ?_⟩
  · intro x
    change iotaB (theta (kappa t x)) = _
    rw [subgroupGammaEquiv_kappa]
    exact hrepB (subgroupCentralizerEquiv U t x)
  · have hthetaRange : theta.toMonoidHom.range = ⊤ :=
      MonoidHom.range_eq_top.mpr theta.surjective
    change (iotaB.comp theta.toMonoidHom).range = _
    rw [MonoidHom.range_comp, hthetaRange, Subgroup.map_top]
    exact hrangeB
  · let eL := (LU.equivMapOfInjective iota (hinjB.comp theta.injective)).trans
      (MulEquiv.subgroupCongr hLUmap)
    exact ⟨eL, fun _ => rfl⟩

theorem odd_core_eq_bot_of_original_involution
    {X : Type*} [Group X] [Finite X] [IsSimpleGroup X]
    (t : X) (ht : orderOf t = 2) : CFSG.pPrimeCore 2 X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pPrimeCore 2 X) with hbot | htop
  · exact hbot
  · have hcop := CFSG.pPrimeCore_coprime_card (p := 2) (G := X)
    rw [htop, Subgroup.card_top] at hcop
    have hdiv : 2 ∣ Nat.card X := ht ▸ orderOf_dvd_natCard t
    exact False.elim ((Nat.prime_two.coprime_iff_not_dvd.mp hcop) hdiv)

theorem proper_same_parameter_subgroup_forces_simple_ambient_regularity
    (X : Type) [Group X] [Finite X] [IsSimpleGroup X]
    (hXnonab : ∃ a b : X, a * b ≠ b * a)
    (hrecognition : SmallerSimpleRecognition X)
    (H : Subgroup X) (hproper : H ≠ ⊤) (hH : ∀ U : Subgroup H, U.index ≠ 2)
    (n m : ℕ) (hn : 4 ≤ n) (hm : 4 ≤ m)
    (SX : Sylow 2 X) (fX : SemidihedralGroup n ≃* SX)
    (SH : Sylow 2 H) (fH : SemidihedralGroup m ≃* SH) (t : H)
    (ht : t = (fH (r m) : H) ^ 2 ^ (m - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma (t : X)))]
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonabX : ∃ a b : CFSG.generalizedFitting (Gamma (t : X)), a * b ≠ b * a)
    (hnonabH : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentralX : Subgroup.centralizer
      (CFSG.generalizedFitting (Gamma (t : X)) : Set (Gamma (t : X))) = ⊥)
    (hcentralH : Subgroup.centralizer
      (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hncX : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma (t : X))), ¬ IsCyclic U)
    (hncH : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodelX : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma (t : X))) .PSL 2 p f)
    (hmodelH : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    n = m ∧ ∃ (S : Sylow 2 X) (eS : SemidihedralGroup m ≃* S),
      (S : Subgroup X) = (SH : Subgroup H).map H.subtype ∧
      (∀ a, (eS a : X) = ((fH a : H) : X)) ∧
      CFSG.pPrimeCore 2 H = ⊥ ∧
      (padicValNat p (Nat.card X) : ℤ) =
        3 * (padicValNat p (Nat.card (C (t : X))) : ℤ) -
          2 * (padicValNat p (Nat.card
            (C (t : X) ⊓ C ((fH (s m) : H) : X) : Subgroup X)) : ℤ) ∧
      (Nat.card X : ℚ) = (Nat.card (C (t : X)) : ℚ) ^ 3 /
        (Nat.card (C (t : X) ⊓ C ((fH (s m) : H) : X) : Subgroup X) : ℚ) ^ 2 *
          ((((p ^ f : ℕ) : ℚ) ^ 2 - (if p ^ f % 4 = 1 then 1 else -1) * p ^ f + 1) /
            (((p ^ f : ℕ) : ℚ) - (if p ^ f % 4 = 1 then 1 else -1)) ^ 2) := by
  classical
  let : Fintype X := Fintype.ofFinite X
  obtain ⟨_, ht2, hcent, _, _, _⟩ :=
    CFSG.Semidihedral.Principal.supplied_t_s_facts hm fH ht
  have hHval := (smaller_simple_recognition_produces_proper_subgroup_regularity X
    hrecognition H hproper hH m hm SH fH t ht hnonabH hcentralH hncH p f hp hpodd hf hq
      hmodelH).1
  obtain ⟨⟨ideal, hmax, htwo⟩, hchar⟩ := CFSG.BlockBasics.residue_prime_existence 2 Nat.prime_two
  have : ideal.IsMaximal := hmax
  have : CharP (ComplexAlgebraicIntegers ⧸ ideal) 2 := hchar ideal hmax htwo
  have hXindex : ∀ U : Subgroup X, U.index ≠ 2 :=
    CFSG.Semidihedral.Principal.index_ne_two_of_isSimpleGroup hXnonab
  obtain ⟨hnm, S, eS, hS, himages, horder, hval, hcore, _, _⟩ :=
    actual_same_parameter_regularity_and_odd_core_intersection H t ht2 n m hn hm SX fX SH
      fH hXindex hH hcent hnonabX hnonabH hcentralX hcentralH hncX hncH p f hp hpodd hf
        hq hmodelX hmodelH ideal (le_of_eq hHval.symm)
  have htX : orderOf (t : X) = 2 := (Subgroup.orderOf_coe t).trans ht2
  have hXcore := odd_core_eq_bot_of_original_involution (t : X) htX
  have hHcore : CFSG.pPrimeCore 2 H = ⊥ := by
    rw [hcore, hXcore]
    change H.subtype.ker = ⊥
    exact H.ker_subtype
  exact ⟨hnm, S, eS, hS, himages, hHcore, hval, horder⟩


theorem original_nontrivial_odd_core_subgroup_proper
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (t : G) (ht : orderOf t = 2) (H : Subgroup G)
    (hR : CFSG.pPrimeCore 2 H ≠ ⊥) : H ≠ ⊤ := by
  intro htop
  have hGcore := odd_core_eq_bot_of_original_involution t ht
  subst H
  have hmap := CFSG.pPrimeCore_map_iso 2 (Subgroup.topEquiv (G := G))
  rw [hGcore] at hmap
  apply hR
  exact (Subgroup.map_eq_bot_iff_of_injective _ Subgroup.topEquiv.injective).mp hmap

theorem original_layer_cover_nontrivial_odd_core_forces_index_two
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrecognition : SmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* S)
    (t s : G) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hsC : s ∈ C t) (hts : t ≠ s)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (H : Subgroup G) (hVH : Subgroup.closure ({t, s} : Set G) ≤ H)
    (hR : CFSG.pPrimeCore 2 H ≠ ⊥)
    (hcover : (H.subgroupOf (C t) ⊓
      ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map (nu t) =
        (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)) :
    H ≠ ⊤ ∧ ∃ K : Subgroup H, K.index = 2 := by
  classical
  have hproper := original_nontrivial_odd_core_subgroup_proper t ht H hR
  refine ⟨hproper, ?_⟩
  by_contra hnone
  have hH : ∀ K : Subgroup H, K.index ≠ 2 := by simpa using hnone
  let tH : H := ⟨t, hVH (Subgroup.mem_closure_of_mem (Set.mem_insert t _))⟩
  have htH : orderOf tH = 2 := (Subgroup.orderOf_coe tH).symm.trans ht
  have hG : ∀ U : Subgroup G, U.index ≠ 2 :=
    CFSG.Semidihedral.Principal.index_ne_two_of_isSimpleGroup hGnonab
  obtain ⟨_, SH, fH, SG, fG, _, _, _, _, _, _, _, hcenter, _⟩ :=
    actual_covering_subgroup_original_pair_sylow_presentation n hn S fS hG t s ht hs hsC
      hts hnonab hcentral hnc p f hp hpodd hf hmodel H hVH hcover
  have hcenterPow : tH = (fH (r n) : H) ^ 2 ^ (n - 2) := by
    have hhalf : CFSG.Semidihedral.modulus n / 2 = 2 ^ (n - 2) := by
      rw [CFSG.Semidihedral.modulus_eq_two_mul_half (by omega)]
      simpa only [CFSG.Semidihedral.half] using
        (Nat.mul_div_cancel_left (CFSG.Semidihedral.half n) (by decide : 0 < 2))
    rw [hhalf] at hcenter
    exact hcenter.symm
  have hsimpleG : IsSimpleGroup (CFSG.generalizedFitting (Gamma (tH : G))) := by
    change IsSimpleGroup (CFSG.generalizedFitting (Gamma t))
    infer_instance
  have := hsimpleG
  obtain ⟨hLsimple, hLnonab, hLcentral, hLnc, hLmodel, _⟩ :=
    original_layer_cover_preserves_intrinsic_local_parameter H tH htH hnonab hcentral hnc
      p f hp hpodd hf hmodel hcover
  have := hLsimple
  obtain ⟨_, S', eS, _, _, hcore, _⟩ :=
    proper_same_parameter_subgroup_forces_simple_ambient_regularity G hGnonab hrecognition
      H hproper hH n n hn hn S fS SH fH tH hcenterPow hnonab hLnonab hcentral hLcentral
        hnc hLnc p f hp hpodd hf hq hmodel hLmodel
  exact hR hcore


theorem original_index_two_and_quaternion_containment_force_focal
    {H : Type*} [Group H] [Finite H]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 H) (fS : SemidihedralGroup n ≃* S)
    (K : Subgroup H) (hKindex : K.index = 2)
    (hQcomm : originalQuaternion n S fS ≤ commutator H) :
    (S : Subgroup H) ⊓ commutator H = originalQuaternion n S fS := by
  have hKnormal : K.Normal := Subgroup.normal_of_index_eq_two hKindex
  let : K.Normal := hKnormal
  have hKcard : Nat.card (H ⧸ K) = 2 := by
    rw [← Subgroup.index_eq_card]
    exact hKindex
  have : Fact (Nat.Prime (Nat.card (H ⧸ K))) := ⟨hKcard ▸ Nat.prime_two⟩
  have : IsCyclic (H ⧸ K) := isCyclic_of_prime_card rfl
  let : CommGroup (H ⧸ K) := IsCyclic.commGroup
  have hcommK : commutator H ≤ K := by
    simpa only [QuotientGroup.ker_mk'] using
      Abelianization.commutator_subset_ker (QuotientGroup.mk' K)
  have hSnotK : ¬ (S : Subgroup H) ≤ K := by
    intro hSK
    have hdiv := Subgroup.index_dvd_of_le hSK
    rw [hKindex] at hdiv
    exact S.not_dvd_index hdiv
  let T : Subgroup S := (commutator H).subgroupOf (S : Subgroup H)
  let Q : Subgroup S := (originalQuaternion n S fS).subgroupOf (S : Subgroup H)
  have hQT : Q ≤ T := Subgroup.comap_mono hQcomm
  have hQindex : Q.index = 2 := originalQuaternion_index n hn S fS
  have hTnotTop : T ≠ ⊤ := by
    intro htop
    apply hSnotK
    intro x hx
    have hxT : (⟨x, hx⟩ : S) ∈ T := by rw [htop]; trivial
    exact hcommK hxT
  have hQeqT : Q = T := by
    by_contra hne
    have hstrict : T.index < Q.index := Subgroup.index_strictAnti (lt_of_le_of_ne hQT hne)
    rw [hQindex] at hstrict
    have hTpos : 0 < T.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have hTone : T.index = 1 := by omega
    exact hTnotTop (Subgroup.index_eq_one.mp hTone)
  have hmap := congrArg (Subgroup.map (S : Subgroup H).subtype) hQeqT
  rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype] at hmap
  have hQS : originalQuaternion n S fS ≤ (S : Subgroup H) :=
    originalQuaternion_le_sylow n S fS
  rw [inf_eq_left.mpr hQS] at hmap
  exact (inf_comm _ _).trans hmap.symm


theorem literal_quaternion_focal_inclusion_produces_ambient_quaternion_containment
    {B H : Type*} [Group B] [Group H]
    (n : ℕ) (SB : Sylow 2 B) (fB : SemidihedralGroup n ≃* SB)
    (SH : Sylow 2 H) (fH : SemidihedralGroup n ≃* SH) (i : B →* H)
    (hr : i (fB (r n) : B) = (fH (r n) : H))
    (hs : i (fB (s n) : B) = (fH (s n) : H))
    (hfocal : (SB : Subgroup B) ⊓ commutator B = originalQuaternion n SB fB) :
    originalQuaternion n SH fH = (originalQuaternion n SB fB).map i ∧
      originalQuaternion n SH fH ≤ commutator H := by
  have hQmap : (originalQuaternion n SB fB).map i = originalQuaternion n SH fH := by
    unfold originalQuaternion originalRotation originalReflection
    rw [MonoidHom.map_closure]
    simp only [Set.image_insert_eq, Set.image_singleton, map_pow, map_mul, hr, hs]
  have hcomm : (commutator B).map i ≤ commutator H := by
    rw [map_commutator_eq, commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  refine ⟨hQmap.symm, ?_⟩
  rw [← hQmap]
  exact (Subgroup.map_mono (hfocal ▸ inf_le_right)).trans hcomm

@[expose] def OriginalCoverFocalConclusion {G : Type} [Group G]
    (n : ℕ) (t : G) (H : Subgroup G) : Prop :=
    let B := H.subgroupOf (C t)
    H ≠ ⊤ ∧ Odd B.index ∧ Odd H.index ∧
      (∀ SB : Sylow 2 B, Nonempty (SemidihedralGroup n ≃* SB) ∧
        ∃ (SH : Sylow 2 H) (SG : Sylow 2 G),
          (SG : Subgroup G) = ((SB : Subgroup B).map B.subtype).map (C t).subtype ∧
          (SG : Subgroup G) = (SH : Subgroup H).map H.subtype ∧
          (SH : Subgroup H) ≤ (H ⊓ C t).subgroupOf H ∧
          ∀ fB : SemidihedralGroup n ≃* SB,
            (((fB (z n) : B) : C t) : G) = t ∧
            (SB : Subgroup B) ⊓ commutator B = originalQuaternion n SB fB ∧
            ∃ (fH : SemidihedralGroup n ≃* SH) (fG : SemidihedralGroup n ≃* SG),
              (fG (z n) : G) = t ∧ ((fH (z n) : H) : G) = t ∧
              (∀ x, (fG x : G) = (((fB x : B) : C t) : G) ∧
                (fG x : G) = ((fH x : H) : G)) ∧
              (SH : Subgroup H) ⊓ commutator H = originalQuaternion n SH fH) ∧
      (Subgroup.closure {x : H | Odd (orderOf x)}).index = 2 ∧
      (∀ K : Subgroup H, K.index = 2 →
        K = Subgroup.closure {x : H | Odd (orderOf x)}) ∧
      (∀ x : H, ∃ a ∈ CFSG.pPrimeCore 2 H,
        ∃ c ∈ Subgroup.centralizer ({t} : Set G), (a : G) * c = (x : G)) ∧
      ambientOddCore H ⊔ (H ⊓ C t) = H ∧
      ambientOddCore H ⊓ C t = (N t).map (C t).subtype ⊓ H

@[expose] def OriginalCoverParameterConclusion {G : Type} [Group G]
    (t : G) (p f : ℕ) (H : Subgroup G) : Prop :=
  let B := H.subgroupOf (C t)
  let R := CFSG.pPrimeCore 2 B
  let Delta := B ⧸ (R ⊔ (Z t).subgroupOf B)
  let J := CFSG.generalizedFitting Delta
  R.map B.subtype = B ⊓ N t ∧
    ∃ iota : Delta →* Gamma t, Function.Injective iota ∧
      (∀ b : B, iota (QuotientGroup.mk' (R ⊔ (Z t).subgroupOf B) b) = kappa t b) ∧
      iota.range = B.map (kappa t) ∧
      J.map iota = CFSG.generalizedFitting (Gamma t) ∧
      IsSimpleGroup J ∧ (∃ a b : J, a * b ≠ b * a) ∧
      Subgroup.centralizer (J : Set Delta) = ⊥ ∧
      (∀ P : Sylow 2 J, ¬ IsCyclic P) ∧
      CFSG.Assembly.LowTwoRank.StatedClassicalModel J .PSL 2 p f ∧
      ∃ eL : J ≃* CFSG.generalizedFitting (Gamma t),
        ∀ x : J, (eL x : Gamma t) = iota x

@[expose] def OriginalCoverQuaternionConclusion {G : Type} [Group G]
    (n : ℕ) (t : G) (p f : ℕ) (H : Subgroup G) : Prop :=
  OriginalCoverFocalConclusion n t H ∧ OriginalCoverParameterConclusion t p f H

theorem original_layer_cover_produces_focal_and_factorization
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrecognition : SmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (t s : G) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hsC : s ∈ C t) (hts : t ≠ s)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (H : Subgroup G) (hVH : Subgroup.closure ({t, s} : Set G) ≤ H)
    (hR : CFSG.pPrimeCore 2 H ≠ ⊥)
    (hcover : (H.subgroupOf (C t) ⊓
      ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map (nu t) =
        (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)) :
    let B := H.subgroupOf (C t)
    H ≠ ⊤ ∧ Odd B.index ∧ Odd H.index ∧
      (∀ SB : Sylow 2 B, Nonempty (SemidihedralGroup n ≃* SB) ∧
        ∃ (SH : Sylow 2 H) (SG : Sylow 2 G),
          (SG : Subgroup G) = ((SB : Subgroup B).map B.subtype).map (C t).subtype ∧
          (SG : Subgroup G) = (SH : Subgroup H).map H.subtype ∧
          (SH : Subgroup H) ≤ (H ⊓ C t).subgroupOf H ∧
          ∀ fB : SemidihedralGroup n ≃* SB,
            (((fB (z n) : B) : C t) : G) = t ∧
            (SB : Subgroup B) ⊓ commutator B = originalQuaternion n SB fB ∧
            ∃ (fH : SemidihedralGroup n ≃* SH) (fG : SemidihedralGroup n ≃* SG),
              (fG (z n) : G) = t ∧ ((fH (z n) : H) : G) = t ∧
              (∀ x, (fG x : G) = (((fB x : B) : C t) : G) ∧
                (fG x : G) = ((fH x : H) : G)) ∧
              (SH : Subgroup H) ⊓ commutator H = originalQuaternion n SH fH) ∧
      (Subgroup.closure {x : H | Odd (orderOf x)}).index = 2 ∧
      (∀ K : Subgroup H, K.index = 2 →
        K = Subgroup.closure {x : H | Odd (orderOf x)}) ∧
      (∀ x : H, ∃ a ∈ CFSG.pPrimeCore 2 H,
        ∃ c ∈ Subgroup.centralizer ({t} : Set G), (a : G) * c = (x : G)) ∧
      ambientOddCore H ⊔ (H ⊓ C t) = H ∧
      ambientOddCore H ⊓ C t = (N t).map (C t).subtype ⊓ H := by
  intro B
  have hG : ∀ U : Subgroup G, U.index ≠ 2 :=
    CFSG.Semidihedral.Principal.index_ne_two_of_isSimpleGroup hGnonab
  obtain ⟨hproper, K, hK⟩ := original_layer_cover_nontrivial_odd_core_forces_index_two
    G hGnonab hrecognition n hn S0 f0 t s ht hs hsC hts hnonab hcentral hnc p f hp hpodd
      hf hq hmodel H hVH hR hcover
  obtain ⟨hBindex, hHindex, hall⟩ :=
    actual_covering_centralizer_every_sylow_commutator_quaternion
      n hn S0 f0 hG t s ht hs hsC hts hnonab hcentral hnc p f hp hpodd hf hq hmodel
        H hVH hcover
  have hlift : ∀ SB : Sylow 2 B, Nonempty (SemidihedralGroup n ≃* SB) ∧
        ∃ (SH : Sylow 2 H) (SG : Sylow 2 G),
          (SG : Subgroup G) = ((SB : Subgroup B).map B.subtype).map (C t).subtype ∧
          (SG : Subgroup G) = (SH : Subgroup H).map H.subtype ∧
          (SH : Subgroup H) ≤ (H ⊓ C t).subgroupOf H ∧
          ∀ fB : SemidihedralGroup n ≃* SB,
            (((fB (z n) : B) : C t) : G) = t ∧
            (SB : Subgroup B) ⊓ commutator B = originalQuaternion n SB fB ∧
            ∃ (fH : SemidihedralGroup n ≃* SH) (fG : SemidihedralGroup n ≃* SG),
              (fG (z n) : G) = t ∧ ((fH (z n) : H) : G) = t ∧
              (∀ x, (fG x : G) = (((fB x : B) : C t) : G) ∧
                (fG x : G) = ((fH x : H) : G)) ∧
              (SH : Subgroup H) ⊓ commutator H = originalQuaternion n SH fH := by
    intro SB
    obtain ⟨hSD, SH, SG, hSG, hSH, hSHC, hpresent⟩ := hall SB
    refine ⟨hSD, SH, SG, hSG, hSH, hSHC, ?_⟩
    intro fB
    obtain ⟨hzB, hfocalB, fH, fG, hzG, hzH, hrep⟩ := hpresent fB
    let i : B →* H :=
      { toFun := fun x => ⟨((x : C t) : G), x.property⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hi (x : SemidihedralGroup n) : i (fB x : B) = (fH x : H) := by
      apply Subtype.ext
      exact (hrep x).1.symm.trans (hrep x).2
    have hQcomm := (literal_quaternion_focal_inclusion_produces_ambient_quaternion_containment
      n SB fB SH fH i (hi (r n)) (hi (CFSG.Semidihedral.s n)) hfocalB).2
    have hfocalH := original_index_two_and_quaternion_containment_force_focal
      n hn SH fH K hK hQcomm
    exact ⟨hzB, hfocalB, fH, fG, hzG, hzH, hrep, hfocalH⟩
  let SB : Sylow 2 B := Classical.choice Sylow.nonempty
  obtain ⟨⟨fB⟩, SH, SG, -, -, -, hpresent⟩ := hlift SB
  obtain ⟨-, -, fH, fG, -, hzH, -, hfocalH⟩ := hpresent fB
  let tH : H := ⟨t, hVH (Subgroup.mem_closure_of_mem (Set.mem_insert t _))⟩
  have htH : (fH (z n) : H) = tH := Subtype.ext hzH
  have hinv : originalInvolution n SH fH = tH :=
    (originalInvolution_eq_image n SH fH).trans htH
  have hindex := oddGenerated_index n hn SH fH hfocalH
  have hunique : ∀ J : Subgroup H, J.index = 2 → J = oddGenerated H := by
    intro J hJ
    rw [oddGenerated_eq_primeResidual_two]
    exact primeResidual_unique_normal_index SH
      (focal_abelianization_index n hn SH fH hfocalH) J
        (Subgroup.normal_of_index_eq_two hJ) hJ
  have hfactor : CFSG.pPrimeCore 2 H ⊔ C tH = ⊤ := by
    have h := original_oddCore_centralizer_sup n hn SH fH hfocalH
    simpa only [oddCore_eq_twoPrimeCore, hinv] using h
  have hcentralizerMap : (C tH).map H.subtype = H ⊓ C t := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.property, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy))
    · intro hx
      refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hx.2))
  have hfactorAmbient : ambientOddCore H ⊔ (H ⊓ C t) = H := by
    have h := congrArg (Subgroup.map H.subtype) hfactor
    rw [Subgroup.map_sup, hcentralizerMap, Subgroup.map_top, Subgroup.range_subtype] at h
    simpa only [ambientOddCore, oddCore_eq_twoPrimeCore] using h
  have hwitness : ∀ x : H, ∃ a ∈ CFSG.pPrimeCore 2 H,
        ∃ c ∈ Subgroup.centralizer ({t} : Set G), (a : G) * c = (x : G) := by
    intro x
    obtain ⟨a, ha, c, hc, hac⟩ :=
      original_element_oddCore_centralizer_factorization n hn SH fH hfocalH x
    have hcG : (c : G) ∈ C t := by
      rw [hinv] at hc
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hc))
    have haR : a ∈ CFSG.pPrimeCore 2 H := by
      rwa [oddCore_eq_twoPrimeCore] at ha
    exact ⟨a, haR, c, hcG, congrArg Subtype.val hac⟩
  have htHorder : orderOf tH = 2 := (Subgroup.orderOf_coe tH).symm.trans ht
  obtain ⟨-, -, -, -, -, hcore, -⟩ :=
    original_layer_cover_preserves_intrinsic_local_parameter H tH htHorder hnonab
      hcentral hnc p f hp hpodd hf hmodel hcover
  have hNtH : N tH = (CFSG.pPrimeCore 2 H).subgroupOf (C tH) := by
    have h := originalCentralizer_oddCore n hn SH fH hfocalH
    change CFSG.oddCore (C (originalInvolution n SH fH)) =
      (CFSG.oddCore H).subgroupOf (C (originalInvolution n SH fH)) at h
    rw [hinv] at h
    simpa only [oddCore_eq_twoPrimeCore] using h
  have hcommute : (C t).subtype.comp
      (B.subtype.comp (subgroupCentralizerEquiv H tH).toMonoidHom) =
        H.subtype.comp (C tH).subtype := rfl
  have hcoreAmbient := congrArg (Subgroup.map (C t).subtype) hcore
  rw [Subgroup.map_map, hcommute, ← Subgroup.map_map, hNtH,
    Subgroup.subgroupOf_map_subtype,
    Subgroup.map_inf _ _ _ H.subtype_injective, hcentralizerMap] at hcoreAmbient
  rw [Subgroup.map_inf _ _ _ (C t).subtype_injective,
    Subgroup.subgroupOf_map_subtype, inf_comm H (C t)] at hcoreAmbient
  have hRle : (CFSG.pPrimeCore 2 H).map H.subtype ≤ H := Subgroup.map_subtype_le _
  have hNle : (N t).map (C t).subtype ≤ C t := Subgroup.map_subtype_le _
  have hleft : (CFSG.pPrimeCore 2 H).map H.subtype ⊓ (H ⊓ C t) =
      (CFSG.pPrimeCore 2 H).map H.subtype ⊓ C t := by
    rw [← inf_assoc, inf_eq_left.mpr hRle]
  have hright : (H ⊓ C t) ⊓ (N t).map (C t).subtype =
      (N t).map (C t).subtype ⊓ H := by
    rw [inf_assoc, inf_eq_right.mpr hNle, inf_comm]
  have hinter : ambientOddCore H ⊓ C t = (N t).map (C t).subtype ⊓ H := by
    rw [ambientOddCore, oddCore_eq_twoPrimeCore]
    rw [inf_comm (C t) H] at hcoreAmbient
    change (CFSG.pPrimeCore 2 H).map H.subtype ⊓ (H ⊓ C t) =
      (H ⊓ C t) ⊓ (N t).map (C t).subtype at hcoreAmbient
    rw [hleft, hright] at hcoreAmbient
    exact hcoreAmbient
  exact ⟨hproper, hBindex, hHindex, hlift, hindex, hunique, hwitness,
    hfactorAmbient, hinter⟩


theorem original_layer_cover_preserves_original_centralizer_quotient_parameter
    {G : Type} [Group G] [Finite G] (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (H : Subgroup G) (htH : t ∈ H)
    (hcover : (H.subgroupOf (C t) ⊓
      ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map (nu t) =
        (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)) :
    OriginalCoverParameterConclusion t p f H := by
  let B := H.subgroupOf (C t)
  have htC : orderOf (tInC t) = 2 := (Subgroup.orderOf_coe (tInC t)).symm.trans ht
  have hLB : CFSG.generalizedFitting (Gamma t) ≤ B.map (kappa t) := by
    intro x hx
    obtain ⟨y, rfl⟩ := barKappa_surjective t x
    have hy : y ∈ (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) := hx
    obtain ⟨b, hb, rfl⟩ := hcover.ge hy
    exact ⟨b, hb.1, rfl⟩
  obtain ⟨hR, iota, hinj, hrep, hrange, hJmap, hJcentral, ⟨eL, heL⟩, hJmodel, hJnc⟩ :=
    CFSG.Semidihedral.Local.centralizer_layer_cover_preserves_actual_local_parameter
      (tInC t) (tInC_central t) htC hnonab
        (CFSG.Semidihedral.SameParameterQuotientTransport.even_card_of_noncyclic_sylow hnc)
          hcentral B htH hLB
  have hJsimple : IsSimpleGroup
      (CFSG.generalizedFitting (B ⧸
        (CFSG.pPrimeCore 2 B ⊔ (Z t).subgroupOf B))) := eL.isSimpleGroup
  have hJnonab : ∃ a b : CFSG.generalizedFitting
      (B ⧸ (CFSG.pPrimeCore 2 B ⊔ (Z t).subgroupOf B)), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    refine ⟨eL.symm a, eL.symm b, fun h => hab ?_⟩
    simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg eL h
  exact ⟨hR, iota, hinj, hrep, hrange, hJmap, hJsimple, hJnonab,
    hJcentral, hJnc hnc, hJmodel p f hp hpodd hf hmodel, eL, heL⟩

theorem original_layer_cover_complete_quaternion_data
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrecognition : SmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (t s : G) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hsC : s ∈ C t) (hts : t ≠ s)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (H : Subgroup G) (hVH : Subgroup.closure ({t, s} : Set G) ≤ H)
    (hR : CFSG.pPrimeCore 2 H ≠ ⊥)
    (hcover : (H.subgroupOf (C t) ⊓
      ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map (nu t) =
        (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)) :
    OriginalCoverQuaternionConclusion n t p f H := by
  constructor
  · exact original_layer_cover_produces_focal_and_factorization
      G hGnonab hrecognition n hn S0 f0 t s ht hs hsC hts hnonab hcentral hnc
      p f hp hpodd hf hq hmodel H hVH hR hcover
  · exact original_layer_cover_preserves_original_centralizer_quotient_parameter
      t ht hnonab hcentral hnc p f hp hpodd hf hmodel H
        (hVH (Subgroup.mem_closure_of_mem (Set.mem_insert t _))) hcover

theorem nontrivial_odd_core_local_layer_cover_forces_quaternion_factorization
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrecognition : SmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (t s : G) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hsC : s ∈ C t) (hts : t ≠ s)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (H : Subgroup G) (hVH : Subgroup.closure ({t, s} : Set G) ≤ H)
    (hR : CFSG.pPrimeCore 2 H ≠ ⊥)
    (hcover : (H.subgroupOf (C t) ⊓
      ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map (nu t) =
        (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)) :
    OriginalCoverQuaternionConclusion n t p f H ∧
      ∀ U : Subgroup G, U ≠ ⊥ → U ≤ (N t).map (C t).subtype →
        Subgroup.closure ({t, s} : Set G) ≤ Subgroup.normalizer (U : Set G) →
        ((Subgroup.centralizer (U : Set G)).subgroupOf (C t) ⊓
          ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map
            (nu t) = (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) →
        OriginalCoverQuaternionConclusion n t p f (Subgroup.normalizer (U : Set G)) := by
  refine ⟨original_layer_cover_complete_quaternion_data
    G hGnonab hrecognition n hn S0 f0 t s ht hs hsC hts hnonab hcentral hnc
      p f hp hpodd hf hq hmodel H hVH hR hcover, ?_⟩
  intro U hU hUN hVU hUcover
  let K := Subgroup.normalizer (U : Set G)
  have hUodd : Odd (Nat.card U) := by
    have hNodd : Odd (Nat.card ((N t).map (C t).subtype)) := by
      rw [Subgroup.card_map_of_injective (C t).subtype_injective]
      exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := C t))
    exact hNodd.of_dvd_nat (Subgroup.card_dvd_of_le hUN)
  have hUK : U ≤ K := U.le_normalizer
  have hUknormal : (U.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUK).mpr le_rfl
  have hUkodd : Odd (Nat.card (U.subgroupOf K)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUK).toEquiv]
    exact hUodd
  have hUcore : U.subgroupOf K ≤ CFSG.pPrimeCore 2 K :=
    le_sSup ⟨hUknormal, Nat.coprime_two_left.mpr hUkodd⟩
  have hRk : CFSG.pPrimeCore 2 K ≠ ⊥ := by
    intro hbot
    have h := Subgroup.map_mono (f := K.subtype) hUcore
    rw [Subgroup.map_subgroupOf_eq_of_le hUK, hbot, Subgroup.map_bot] at h
    exact hU (le_bot_iff.mp h)
  have hKcover : (K.subgroupOf (C t) ⊓
      ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map (nu t) =
        (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) := by
    apply le_antisymm
    · exact (Subgroup.map_mono inf_le_right).trans (Subgroup.map_comap_le _ _)
    · calc
        (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) =
            ((Subgroup.centralizer (U : Set G)).subgroupOf (C t) ⊓
              ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map
                (nu t) := hUcover.symm
        _ ≤ (K.subgroupOf (C t) ⊓
              ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map
                (nu t) := Subgroup.map_mono (inf_le_inf
          (Subgroup.subgroupOf_mono (C t) (Subgroup.centralizer_le_normalizer (U : Set G)))
            le_rfl)
  exact original_layer_cover_complete_quaternion_data G hGnonab hrecognition n hn S0 f0
    t s ht hs hsC hts hnonab hcentral hnc p f hp hpodd hf hq hmodel K hVU hRk hKcover

end CFSG.Semidihedral.LocalCoverFactorization
