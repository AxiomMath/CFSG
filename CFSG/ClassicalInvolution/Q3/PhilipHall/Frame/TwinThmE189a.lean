module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEDefs
public import CFSG.ClassicalInvolution.Q3.Q3T8Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open scoped commutatorElement

namespace TwinThmE

section A

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G}
  {S : Sylow 2 G} {R W H : Subgroup G}

theorem EStandQ8.conj {K R W : Subgroup G} {S : Sylow 2 G} (h : EStandQ8 Ω K S R W) (g : G) :
    EStandQ8 Ω (conjSub g K) (conjSylow g S) (conjSub g R) (conjSub g W) where
  hyp := h.hyp
  cls := h.cls
  q8 := h.q8
  two := h.two
  ih := h.ih
  mem := h.hyp.conjInvariant g K h.mem
  aEmpty := aEmpty_conj h.hyp.conjInvariant h.aEmpty g
  twin := by
    obtain ⟨K', hK', hne, R', hR', hR'K', hR'S⟩ := h.twin
    refine ⟨conjSub g K', twinSet_conj h.hyp.conjInvariant hK' g,
      fun h' => hne ((conjSub_inj g).mp h'), conjSub g R', RSet.conj h.hyp.conjInvariant hR' g,
      conjSub_mono hR'K', ?_⟩
    rw [coe_conjSylow]
    exact conjSub_mono hR'S
  hR := by
    obtain ⟨hR, hRK, hRS⟩ := h.hR
    refine ⟨RSet.conj h.hyp.conjInvariant hR g, conjSub_mono hRK, ?_⟩
    rw [coe_conjSylow]
    exact conjSub_mono hRS
  hW := by
    obtain ⟨hW, hWS, hWn⟩ := h.hW
    refine ⟨WSet.conj h.hyp.conjInvariant hW g, ?_, ?_⟩
    · rw [coe_conjSylow]
      exact conjSub_mono hWS
    · intro s hs
      rw [coe_conjSylow, mem_conjSub_iff] at hs
      have := hWn _ hs
      calc conjSub s (conjSub g W) = conjSub g (conjSub (g⁻¹ * s * g) W) := by
            rw [← conjSub_mul, ← conjSub_mul]
            congr 1
            group
        _ = conjSub g W := by rw [this]

theorem e189_caseA (hΩ : HypOmegaGen Ω) {K J : Subgroup G}
    {z t : G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hz : IsUniqueInvolution K z)
    (ht : IsUniqueInvolution J t) (htz : t ≠ z) (hzt : z * t = t * z)
    (hnorm : conjSub t K = K) : (∃ g : G, g * t * g⁻¹ = z * t) ∨ J ∈ KPerp Ω K := by
  have hJnt : J ∉ twinSet Ω K := by
    rintro ⟨-, z', hz', hz'J⟩
    exact htz ((ht.eq hz'J).trans (hz.eq hz').symm)
  have hKcent : ∀ w ∈ K, z * w = w * z := fun w hw => e189_commute_of_mem hz hw
  have hKC : K ≤ Subgroup.centralizer ({z} : Set G) := fun w hw => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hKcent w hw).symm
  have ht2 : IsPGroup 2 (Subgroup.zpowers t) := isPGroup_zpowers_of_involution ht.ne_one ht.sq
  have htle : Subgroup.zpowers t ≤ J ⊓ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.zpowers_le]
    exact ⟨ht.mem, Subgroup.mem_centralizer_singleton_iff.mpr hzt.symm⟩
  obtain ⟨V, hV, htV⟩ := IsSylow2In.exists_ge ht2 htle
  have htVm : t ∈ V := htV (Subgroup.mem_zpowers t)
  have hVJ : V ≤ J := hV.1.trans inf_le_left
  have hVC : V ≤ Subgroup.centralizer ({z} : Set G) := hV.1.trans inf_le_right
  rcases Sec6Gen.l6_2Gen G Ω hΩ K hK z hz J hJ hJnt t ht V hV htVm with
    ⟨-, hne⟩ | ⟨hVeq, hVN, R₁, hR₁, hR₁K, hVR, hsd⟩ | ⟨hVU, hVN, R₁, hR₁, hR₁K, hVR, hwr⟩ |
    ⟨hVR, hcomm⟩
  · exact absurd hnorm hne
  ·
    left
    have hR₁2 : IsPGroup 2 R₁ := by
      obtain ⟨-, -, -, h, -⟩ := mem_RSet_iff.mp hR₁
      exact h
    have hV2 : IsPGroup 2 V := hVeq ▸ ht2
    have hP2 : IsPGroup 2 ↥(R₁ ⊔ V) := hR₁2.to_sup_of_normal_left' hV2 hVR
    have hzR : z ∈ R₁ := mem_of_isUniqueInvolution_of_isPGroup hz hR₁K hR₁2
      (by have := hΩ.eight_le_of_mem_RSet hR₁; omega)
    have hzc : ∀ x ∈ R₁ ⊔ V, z * x = x * z := by
      have : R₁ ⊔ V ≤ Subgroup.centralizer ({z} : Set G) := sup_le (hR₁K.trans hKC) hVC
      intro x hx
      exact (Subgroup.mem_centralizer_singleton_iff.mp (this hx)).symm
    obtain ⟨g, -, hg⟩ := exists_conj_of_isSemidihedral hsd hP2 (Subgroup.mem_sup_left hzR) hz.sq
      hz.ne_one hzc (Subgroup.mem_sup_right htVm) ht.sq ht.ne_one htz
    exact ⟨g, hg⟩
  ·
    left
    have hR₁2 : IsPGroup 2 R₁ := by
      obtain ⟨-, -, -, h, -⟩ := mem_RSet_iff.mp hR₁
      exact h
    have hV2 : IsPGroup 2 V := hV.2.1
    have hP2 : IsPGroup 2 ↥(R₁ ⊔ V) := hR₁2.to_sup_of_normal_left' hV2 hVR
    have hzR : z ∈ R₁ := mem_of_isUniqueInvolution_of_isPGroup hz hR₁K hR₁2
      (by have := hΩ.eight_le_of_mem_RSet hR₁; omega)
    have hzc : ∀ x ∈ R₁ ⊔ V, z * x = x * z := by
      have : R₁ ⊔ V ≤ Subgroup.centralizer ({z} : Set G) := sup_le (hR₁K.trans hKC) hVC
      intro x hx
      exact (Subgroup.mem_centralizer_singleton_iff.mp (this hx)).symm
    obtain ⟨g, -, hg⟩ := exists_conj_of_isWreathed hwr hP2 (Subgroup.mem_sup_left hzR) hz.sq
      hz.ne_one hzc (Subgroup.mem_sup_right htVm) ht.sq ht.ne_one htz
    exact ⟨g, hg⟩
  ·
    right
    have hJK : J ≠ K := by
      rintro rfl
      exact htz (hz.eq ht).symm
    refine Or.inr ⟨hJ, hJK, V, hVR, hVJ, fun v hv => ?_⟩
    exact le_normalizer_of_commutator_le_oddCoreOf hcomm hv

theorem exists_commuting_sylow_pair (hΩ : HypOmegaGen Ω)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ omegaNbr Ω K) :
    ∃ R T : Subgroup G, IsSylow2In R K ∧ IsSylow2In T J ∧ T ≤ Subgroup.normalizer (K : Set G) ∧
      Commutes R T := by
  obtain ⟨hJΩ, hne, T, hT, hTJ, hTN⟩ := hJ
  have hTsyl : IsSylow2In T J := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hJΩ hT hTJ
  have hT2 : IsPGroup 2 ↥T := hTsyl.2.1
  have h8 : 8 ≤ Nat.card T := hΩ.eight_le_of_mem_RSet hT
  obtain ⟨R, hR, hRinv⟩ := AscL62.exists_sylow_normalized hT2 hTN
  have hRset : R ∈ RSet Ω := mem_RSet_of_isSylow2In hK hR
  have hTnR : T ≤ Subgroup.normalizer (R : Set G) := fun t ht =>
    mem_normalizer_iff_conjSub_eq.mpr (hRinv t ht)
  have hTR2 : IsPGroup 2 ↥(T ⊔ R) := hT2.to_sup_of_normal_right' hR.2.1 hTnR
  obtain ⟨S, hS⟩ := hTR2.exists_le_sylow
  have hTneR : T ≠ R := by
    intro h
    exact hne (hΩ.eq_of_le_of_le hJΩ hK hT2 (by omega) hTJ (h ▸ hR.1))
  exact ⟨R, T, hR, hTsyl, hTN,
    (Q3CP.l67Gen G Ω hΩ S T hT R hRset (le_sup_left.trans hS) (le_sup_right.trans hS)
      hTneR).symm⟩

theorem omegaNbr_subgroupOf (hΩ : HypOmegaGen Ω) {Y K J : Subgroup G}
    (hKY : K ≤ Y) (hJY : J ≤ Y) (hJ : J ∈ Ω) (h : J ∈ omegaNbr Ω K) :
    J.subgroupOf Y ∈ omegaNbr (restrictFamily Ω Y) (K.subgroupOf Y) := by
  obtain ⟨-, hne, T, hT, hTJ, hTN⟩ := h
  have hTsyl : IsSylow2In T J := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hJ hT hTJ
  refine ⟨subgroupOf_mem_restrictFamily hJ hJY, subgroupOf_ne_of_ne hKY hJY hne, T.subgroupOf Y,
    mem_RSet_restrict hJ hJY hTsyl, Subgroup.subgroupOf_mono Y hTJ, fun x hx => ?_⟩
  exact (mem_normalizer_subgroupOf_iff hKY).mp (hTN (Subgroup.mem_subgroupOf.mp hx))

theorem AEmpty.restrict (hΩ : HypOmegaGen Ω) {Y K : Subgroup G}
    (hKY : K ≤ Y) (hA : AEmpty Ω K) : AEmpty (restrictFamily Ω Y) (K.subgroupOf Y) := by
  intro J' hJ'star hJ'nbr zK' zJ' hzK' hzJ'
  set J : Subgroup G := J'.map Y.subtype with hJdef
  have hJ'eq : J.subgroupOf Y = J' := subgroupOf_map_subtype' J'
  have hJY : J ≤ Y := Subgroup.map_subtype_le J'
  have hJ : J ∈ Ω := mem_restrictFamily_iff.mp hJ'star.1
  have hstar : J ∈ omegaStarNbr Ω K :=
    omegaStarNbr_of_restrict hKY hJY (by rwa [hJ'eq])
  have hnbr : J ∉ omegaNbr Ω K := fun h =>
    hJ'nbr (by rw [← hJ'eq]; exact omegaNbr_subgroupOf hΩ hKY hJY hJ h)
  have hzK : IsUniqueInvolution K (zK' : G) := isUniqueInvolution_of_subgroupOf hzK' hKY
  have hzJ : IsUniqueInvolution J (zJ' : G) :=
    isUniqueInvolution_of_subgroupOf (by rwa [hJ'eq]) hJY
  obtain ⟨g, hg, hgK⟩ := hA J hstar hnbr _ _ hzK hzJ
  set Z' : Subgroup Y := Subgroup.closure ({zK', zJ'} : Set Y) with hZ'
  have hZ : Z'.map Y.subtype = Subgroup.closure ({(zK' : G), (zJ' : G)} : Set G) :=
    map_closure_pair_subtype zK' zJ'
  have hZY : Subgroup.closure ({(zK' : G), (zJ' : G)} : Set G) ≤ Y := by
    rw [← hZ]; exact Subgroup.map_subtype_le _
  have hgY : g ∈ Y := by
    have : pairNormalizers K J (zK' : G) (zJ' : G) ≤ Y := by
      unfold pairNormalizers
      exact sup_le (inf_le_left.trans hKY) (inf_le_left.trans hJY)
    exact this hg
  have hN : ∀ {A : Subgroup G}, A ≤ Y →
      (A ⊓ Subgroup.normalizer ((Subgroup.closure ({(zK' : G), (zJ' : G)} : Set G) :
        Subgroup G) : Set G)).subgroupOf Y ≤
        A.subgroupOf Y ⊓ Subgroup.normalizer ((Z' : Subgroup Y) : Set Y) := by
    intro A hAY x hx
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hx
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mpr hx.1, ?_⟩
    have := (mem_normalizer_subgroupOf_iff hZY).mp hx.2
    rwa [← hZ, subgroupOf_map_subtype'] at this
  have hAY : K ⊓ Subgroup.normalizer ((Subgroup.closure ({(zK' : G), (zJ' : G)} : Set G) :
      Subgroup G) : Set G) ≤ Y := inf_le_left.trans hKY
  have hBY : J ⊓ Subgroup.normalizer ((Subgroup.closure ({(zK' : G), (zJ' : G)} : Set G) :
      Subgroup G) : Set G) ≤ Y := inf_le_left.trans hJY
  have hmem : (⟨g, hgY⟩ : Y) ∈ (pairNormalizers K J (zK' : G) (zJ' : G)).subgroupOf Y :=
    Subgroup.mem_subgroupOf.mpr hg
  have hmem' : (⟨g, hgY⟩ : Y) ∈ pairNormalizers (K.subgroupOf Y) J' zK' zJ' := by
    have h1 := hmem
    unfold pairNormalizers at h1
    rw [Subgroup.subgroupOf_sup hAY hBY] at h1
    have h2 := hN (A := K) hKY
    have h3 := hN (A := J) hJY
    rw [hJ'eq] at h3
    exact sup_le_sup h2 h3 h1
  refine ⟨⟨g, hgY⟩, hmem', ?_⟩
  rw [conjSub_subgroupOf Y ⟨g, hgY⟩ K]
  show (conjSub g K).subgroupOf Y = J'
  rw [hgK]
  exact hJ'eq

end A

end TwinThmE

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
