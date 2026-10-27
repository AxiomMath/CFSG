module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4KSwMemTools
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5TWComp
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Lemma53

public section

namespace CFSG.ComponentClassification.GrSLit.KSw

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

variable {G : Type} [Group G] [Finite G]

theorem mem_zStarIn_of_fixedLayer {X Y F : Subgroup G} (hFX : F ≤ X) (hFY : F ≤ Y)
    (hYsup : F ⊔ oddIn Y = Y) {y : G} (hyF : y ∈ F) (hyZ : y ∈ zStarIn X) : y ∈ zStarIn Y := by
  have hyK := GrS5.zStarIn_le_coreActionKernel X hyZ
  have hOF : oddIn X ⊓ F ≤ oddIn Y :=
    (GrS5.inf_oddIn_le_oddIn hFX).trans (GrS4.oddIn_le_oddIn_of_eq_sup hFY hYsup.symm)
  have hyN : y ∈ normalizer (X : Set G) := (mem_coreActionKernel.mp hyK).1
  refine GrS5S.mem_zStarIn_of_mem_coreActionKernel (hFY hyF)
    (mem_coreActionKernel_of_conj_mem_oddIn hFY hYsup (le_normalizer (hFY hyF)) fun f hf => ?_)
  refine hOF (mem_inf.mpr ⟨?_, mul_mem (mul_mem (mul_mem hyF hf) (inv_mem hyF)) (inv_mem hf)⟩)
  have h1 := (mem_coreActionKernel.mp hyK).2 f⁻¹ (inv_mem (hFX hf))
  have h2 := GrS4.conj_mem_oddIn_of_mem_normalizer hyN h1
  rwa [show y * (f⁻¹⁻¹ * y⁻¹ * f⁻¹ * y) * y⁻¹ = y * f * y⁻¹ * f⁻¹ by group] at h2

theorem inf_eq_of_fixedLayer {J L F S T' : Subgroup G} (hSJ : IsSylowTwoIn (S ⊓ J) J)
    (hFJ : F ≤ J) (hPF : S ⊓ J ≤ F) (hFL : F ≤ L) (hLsup : F ⊔ oddIn L = L) (hST : S ≤ T')
    (hT2 : IsPGroup 2 T') : T' ⊓ L = S ⊓ J := by
  have hPF' : IsSylowTwoIn (S ⊓ J) F := GrS4.isSylowTwoIn_of_le hSJ hPF hFJ
  have hPL : IsSylowTwoIn (S ⊓ J) L :=
    GrS5S.isSylowTwoIn_of_le_sup_oddIn hPF' hFL (by rw [sup_comm, hLsup])
  exact hPL.eq_of_le (le_inf (inf_le_left.trans hST) (hPF.trans hFL)) inf_le_right
    (hT2.to_le inf_le_left)

theorem inf_zStarIn_eq_of_fixedLayer {J L F S T' : Subgroup G} (hFJ : F ≤ J) (hFL : F ≤ L)
    (hJsup : F ⊔ oddIn J = J) (hLsup : F ⊔ oddIn L = L) (hPF : S ⊓ J ≤ F)
    (heq : T' ⊓ L = S ⊓ J) : T' ⊓ zStarIn L = S ⊓ zStarIn J := by
  apply le_antisymm
  · intro y hy
    obtain ⟨hyT, hyZ⟩ := mem_inf.mp hy
    have hyL : y ∈ L := (map_subtype_le _ : zStarIn L ≤ L) hyZ
    have hySJ : y ∈ S ⊓ J := heq ▸ mem_inf.mpr ⟨hyT, hyL⟩
    exact mem_inf.mpr ⟨(mem_inf.mp hySJ).1, mem_zStarIn_of_fixedLayer hFL hFJ hJsup (hPF hySJ) hyZ⟩
  · intro y hy
    obtain ⟨hyS, hyZ⟩ := mem_inf.mp hy
    have hyJ : y ∈ J := (map_subtype_le _ : zStarIn J ≤ J) hyZ
    have hyF : y ∈ F := hPF (mem_inf.mpr ⟨hyS, hyJ⟩)
    have hyT : y ∈ T' ⊓ L := heq ▸ mem_inf.mpr ⟨hyS, hyJ⟩
    exact mem_inf.mpr ⟨(mem_inf.mp hyT).1, mem_zStarIn_of_fixedLayer hFJ hFL hLsup hyF hyZ⟩

theorem normalizer_le_of_wGroup46 (hGW : GWTwoBalanced G) (h44 : L34Lemma44)
    (hU : L34UnbalancingUnitaryStep) (hC : L34UnitaryCentralizerFact)
    (hCF : L34CentralFourFact) {a x : G} {J S A W : Subgroup G}
    (hset : L34Sec4Setting G a x J S) (hrun : L34Sec4Running J A)
    (hexp : Monoid.exponent ↥(S ⊓ zStarIn J) = 4) (hcyc : ¬ IsCyclic ↥(S ⊓ zStarIn J))
    (hWR : wGroup (S ⊓ J ⊓ centralizer ({x} : Set G)) = W) :
    normalizer (J : Set G) ≤ normalizer (W : Set G) := by
  obtain ⟨-, hU3, hL34, -, hS, -, hxS⟩ := id hset
  have hJa : J ≤ centralizer ({a} : Set G) := hU3.2.2.2.1
  have hJc := hU3.2.2.2.2.1
  have hJper : ⁅J, J⁆ = J := commutator_eq_of_isPComponent hJa hJc
  have hSN : S ≤ normalizer (J : Set G) := hS.1
  set P : Subgroup G := S ⊓ J with hPdef
  have hP : IsSylowTwoIn P J := GrS4.isSylowTwoIn_inf hS
  have hZJ : zStarIn J ≤ J := map_subtype_le _
  have hZP : P ⊓ zStarIn J = S ⊓ zStarIn J := by
    rw [hPdef, inf_assoc, inf_eq_right.mpr hZJ]
  have hxU : IsL34Unitary J x := hU G a x J hU3 hL34
  have hxP : x ∈ normalizer (P : Set G) := GrS4.inf_mem_normalizer (le_normalizer hxS) (hSN hxS)
  obtain ⟨-, h8, -, -, -, hel, -, -⟩ := hC G J P x hJper hL34 hxU hP hxP
  set R : Subgroup G := P ⊓ centralizer ({x} : Set G) with hRdef
  have hR : IsEightGroup R := ⟨hel (by rwa [hZP]), h8⟩
  obtain ⟨⟨hBe, -⟩, hgen⟩ := h44 G a x J S A hset hrun hcyc
  have hWB : wGroup (R ⊔ zpowers x) = W :=
    (wGroup_eq_of_le_eight hGW hBe le_sup_left hR.2).trans hWR
  obtain ⟨C, hCP, hCe, hC16, hRC, hCZ, hNC⟩ := hCF G J P x hJper hL34 hP hxU hxP
    (by rwa [hZP]) (by rw [hZP]; exact GrS4.exists_sq_ne_one_of_exponent_eq_four hexp)
  have hWC : wGroup C = W := (wGroup_eq_of_le_eight hGW hCe hRC hR.2).trans hWR
  have hJeq := hgen C hCP hCe hC16 hRC (by rwa [hZP] at hCZ)
  have hJM : J ≤ normalizer (W : Set G) := by
    rw [hJeq]
    refine iSup_le fun E => iSup_le fun hE => iSup_le fun hE8 => ?_
    have hWE : wGroup E = W := by
      rcases hE with hEB | hEC
      · rw [← hWB]
        exact (wGroup_eq_of_le_eight hGW hBe hEB hE8.2).symm
      · rw [← hWC]
        exact (wGroup_eq_of_le_eight hGW hCe hEC hE8.2).symm
    intro g hg
    have := GrS4.mem_normalizer_wGroup (mem_inf.mp hg).2
    rwa [hWE] at this
  intro n hn
  obtain ⟨m, hmJ, k, hkN, rfl⟩ := GrS4.exists_mul_mem_normalizer_of_isSylowTwoIn hP hn
  have hk : k ∈ normalizer (W : Set G) := by
    have := GrS4.mem_normalizer_wGroup (hNC hkN)
    rwa [hWC] at this
  exact mul_mem (hJM hmJ) hk

theorem inf_eq_of_sup_oddIn {J K S : Subgroup G} (hSJ : IsSylowTwoIn (S ⊓ J) J) (hJK : J ≤ K)
    (hKsup : J ⊔ oddIn K = K) (hS2 : IsPGroup 2 S) : S ⊓ K = S ⊓ J := by
  have hPK : IsSylowTwoIn (S ⊓ J) K :=
    GrS5S.isSylowTwoIn_of_le_sup_oddIn hSJ hJK (by rw [sup_comm, hKsup])
  exact hPK.eq_of_le (inf_le_inf_left _ hJK) inf_le_right (hS2.to_le inf_le_left)

theorem l34ZConjClosed_of_le_normalizer {J K S M : Subgroup G} (hJK : J ≤ K)
    (hKsup : J ⊔ oddIn K = K) (hMK : M ≤ normalizer (K : Set G))
    (hSJ : IsSylowTwoIn (S ⊓ J) J) (hS2 : IsPGroup 2 S) : L34ZConjClosed J S M := by
  intro c hc _ m hm hmS
  have hcZ : c ∈ zStarIn J := (mem_inf.mp hc).2
  have hcJ : c ∈ J := (map_subtype_le _ : zStarIn J ≤ J) hcZ
  have hcK : c ∈ zStarIn K := mem_zStarIn_of_fixedLayer le_rfl hJK hKsup hcJ hcZ
  have hmK : m⁻¹ * c * m ∈ zStarIn K := by
    have h := GrS4.conj_mem_zStarIn (inv_mem (hMK hm)) hcK
    rwa [inv_inv] at h
  have hmSJ : m⁻¹ * c * m ∈ S ⊓ J := by
    rw [← inf_eq_of_sup_oddIn hSJ hJK hKsup hS2]
    exact mem_inf.mpr ⟨hmS, (map_subtype_le _ : zStarIn K ≤ K) hmK⟩
  exact GrS4.mem_zStarIn_of_le hJK (mem_inf.mp hmSJ).2 hmK

omit [Finite G] in
theorem le_normalizer_sup_oddIn {K M : Subgroup G} (hMK : M ≤ normalizer (K : Set G)) :
    M ≤ normalizer ((K ⊔ oddIn M : Subgroup G) : Set G) := by
  intro m hm
  refine mem_normalizer_iff_map_conj_eq.mpr ?_
  rw [Subgroup.map_sup, mem_normalizer_iff_map_conj_eq.mp (hMK hm),
    mem_normalizer_iff_map_conj_eq.mp (GrS4.self_le_normalizer_oddIn M hm)]

omit [Finite G] in
theorem normal_oddIn_sup_of_normalizer {J K M : Subgroup G} (hJM : J ≤ M)
    (hsup : J ⊔ oddIn M = K ⊔ oddIn M) (hMK : M ≤ normalizer (K : Set G)) :
    ((oddIn M ⊔ J).subgroupOf M).Normal := by
  have hle : oddIn M ⊔ J ≤ M := sup_le (map_subtype_le _) hJM
  rw [normal_subgroupOf_iff_le_normalizer hle,
    show oddIn M ⊔ J = K ⊔ oddIn M by rw [sup_comm, hsup]]
  exact le_normalizer_sup_oddIn hMK

end CFSG.ComponentClassification.GrSLit.KSw
