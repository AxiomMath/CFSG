module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76LStruct
public import CFSG.LocalAnalysis.ComponentClassification.Sol76AltClass
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Transport
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitLayerTools
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitBalanceCore
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Props
public import CFSG.LocalAnalysis.ComponentClassification.Sol76TwoComp
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Seven
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitOuterTools
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm32

public section

namespace CFSG.ComponentClassification.Sol76

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_mul_of_mem_sup_normalizer {N H : Subgroup G} (hH : H ≤ normalizer (N : Set G))
    {y : G} (hy : y ∈ N ⊔ H) : ∃ n ∈ N, ∃ h ∈ H, y = n * h := by
  have hy' : y ∈ ((N : Set G) * (H : Set G)) := by
    rw [← coe_mul_of_right_le_normalizer_left N H hH]
    exact hy
  obtain ⟨n, hn, h, hh, rfl⟩ := hy'
  exact ⟨n, hn, h, hh, rfl⟩

omit [Finite G] in
theorem le_normalizer_centralizer {A H : Subgroup G} (hH : H ≤ normalizer (A : Set G)) :
    H ≤ normalizer (centralizer (A : Set G) : Set G) := by
  refine le_normalizer_of_forall_conj_mem fun h hh x hx => ?_
  rw [mem_centralizer_iff]
  intro a ha
  have ha' : h⁻¹ * a * h ∈ A := by
    have := (mem_normalizer_iff.mp (hH (inv_mem hh)) a).mp ha
    simpa using this
  have h1 : h⁻¹ * a * h * x = x * (h⁻¹ * a * h) := (mem_centralizer_iff.mp hx) _ ha'
  calc a * (h * x * h⁻¹) = h * (h⁻¹ * a * h * x) * h⁻¹ := by group
    _ = h * (x * (h⁻¹ * a * h)) * h⁻¹ := by rw [h1]
    _ = h * x * h⁻¹ * a := by group

theorem le_normalizer_twoLayerIn (C : Subgroup G) : C ≤ normalizer (twoLayerIn C : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (pLayer ↥C 2).Characteristic := CatalogueBPrimeJoin.pLayer_characteristic
  refine le_normalizer_of_forall_conj_mem fun c hc x hx => ?_
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨⟨c, hc⟩ * y * ⟨c, hc⟩⁻¹, Normal.conj_mem inferInstance y hy _, ?_⟩
  simp

omit [Finite G] in
theorem oddResidualIn_le (Y : Subgroup G) : oddResidualIn Y ≤ Y :=
  (closure_le _).mpr fun _ hx => hx.1

omit [Finite G] in
theorem mem_of_eq_mul_of_odd {H N : Subgroup G} (hNH : N ≤ H) (hHN : H ≤ normalizer (N : Set G))
    {x o b : G} (hx : x = o * b) (hoH : o ∈ H) (hb : b ∈ N) (ho : Odd (orderOf o)) {k : ℕ}
    (hk : orderOf x = 2 ^ k) : x ∈ N := by
  have hN : (N.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hNH).mpr hHN
  have hxH : x ∈ H := by rw [hx]; exact mul_mem hoH (hNH hb)
  set π := QuotientGroup.mk' (N.subgroupOf H) with hπ
  have h1 : π ⟨x, hxH⟩ = π ⟨o, hoH⟩ := by
    have e : (⟨x, hxH⟩ : ↥H) = ⟨o, hoH⟩ * ⟨b, hNH hb⟩ := Subtype.ext hx
    rw [e, map_mul, show π ⟨b, hNH hb⟩ = 1 from (QuotientGroup.eq_one_iff _).mpr hb, mul_one]
  have h2 : orderOf (π ⟨x, hxH⟩) ∣ 2 ^ k := by
    have := orderOf_map_dvd π (⟨x, hxH⟩ : ↥H)
    rwa [Subgroup.orderOf_mk, hk] at this
  have h3 : orderOf (π ⟨x, hxH⟩) ∣ orderOf o := by
    rw [h1]
    have := orderOf_map_dvd π (⟨o, hoH⟩ : ↥H)
    rwa [Subgroup.orderOf_mk] at this
  have h4 : Nat.Coprime (orderOf (π ⟨x, hxH⟩)) (2 ^ k) :=
    Nat.Coprime.coprime_dvd_left h3 (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr ho))
  have h5 := Nat.Coprime.eq_one_of_dvd h4 h2
  rw [orderOf_eq_one_iff, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    mem_subgroupOf] at h5
  exact h5

theorem isSolomonMember_of_isTwoComponentIn {T K : Subgroup G} (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T)
    (hK : IsTwoComponentIn K (centralizer (T : Set G))) : IsSolomonMember K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hKC, hKp⟩ := hK
  set C := centralizer (T : Set G) with hC
  refine ⟨UnbalancedCorr.commutator_eq_of_isPComponent hKC hKp, T, hT, hT2, fun t ht => ?_, ?_⟩
  · exact Sol78.mem_coreActionKernel_of_commute fun k hk =>
      ((mem_centralizer_iff.mp (hKC hk)) t ht).symm
  · rw [inf_eq_left.mpr hKC, Sol78.oddResidualIn_eq_oPrimeResidualOf]
    change GH74.GLS.IsPCompIn 2 C (GH74.GLS.oPrimeResidualOf 2 (GH74.GLS.pPrimeCoreOf 2 C ⊔ K))
    rw [Sol78.oPrimeResidualOf_core_sup_eq hKC hKp]
    exact ⟨hKC, hKp⟩

theorem twoLayer_inf_centralizer_le_map_conj {L A : Subgroup G} {y : G}
    (hy : y ∈ normalizer (L : Set G))
    (h : twoLayerIn (L ⊓ centralizer (A : Set G)) ≤ twoLayerIn (centralizer (A : Set G))) :
    twoLayerIn (L ⊓ centralizer ((A.map (MulAut.conj y).toMonoidHom : Subgroup G) : Set G)) ≤
      twoLayerIn (centralizer ((A.map (MulAut.conj y).toMonoidHom : Subgroup G) : Set G)) := by
  set φ := MulAut.conj y with hφ
  have hL : L.map φ.toMonoidHom = L := mem_normalizer_iff_map_conj_eq.mp hy
  have hC := map_centralizer φ A
  have h1 : L ⊓ centralizer ((A.map φ.toMonoidHom : Subgroup G) : Set G) =
      (L ⊓ centralizer (A : Set G)).map φ.toMonoidHom := by
    rw [map_inf_eq _ _ _ φ.injective, hL, hC]
  rw [h1, ← hC, ← map_twoLayerIn, ← map_twoLayerIn]
  exact map_mono h

theorem twoLayer_inf_centralizer_le_of_witness {L T : Subgroup G}
    (hLq : IsQuasisimple (↥L ⧸ pPrimeCore 2 ↥L)) (hT2 : IsPGroup 2 T)
    (hTQ : T ≤ coreActionKernel L)
    (hK : IsTwoComponentIn (oddResidualIn (oddCoreIn (centralizer (T : Set G)) ⊔
      (L ⊓ centralizer (T : Set G)))) (centralizer (T : Set G))) :
    twoLayerIn (L ⊓ centralizer (T : Set G)) ≤ twoLayerIn (centralizer (T : Set G)) := by
  obtain ⟨-, hLT, -, -⟩ := cover_facts hLq inf_le_left (inf_centralizer_sup_oddCoreIn_eq hT2 hTQ)
  rw [hLT]
  refine le_trans ?_ (le_twoLayerIn_of_isTwoComponentIn hK)
  refine closure_mono fun x hx => ⟨mem_sup_right hx.1, hx.2⟩

theorem twoLayer_inf_centralizer_le_of_normalizes {L A B : Subgroup G}
    (hLq : IsQuasisimple (↥L ⧸ pPrimeCore 2 ↥L)) (hA2 : IsPGroup 2 A) (hB2 : IsPGroup 2 B)
    (hAB : A ≤ B) (hBA : B ≤ normalizer (A : Set G)) (hBQ : B ≤ coreActionKernel L)
    (hB : twoLayerIn (L ⊓ centralizer (B : Set G)) ≤ twoLayerIn (centralizer (B : Set G))) :
    twoLayerIn (L ⊓ centralizer (A : Set G)) ≤ twoLayerIn (centralizer (A : Set G)) := by
  classical
  set CA := centralizer (A : Set G) with hCA
  set CB := centralizer (B : Set G) with hCB
  have hAQ : A ≤ coreActionKernel L := hAB.trans hBQ
  have hCBA : CB ≤ CA := centralizer_le hAB
  obtain ⟨-, hLA, -, -⟩ := cover_facts hLq inf_le_left (inf_centralizer_sup_oddCoreIn_eq hA2 hAQ)
  obtain ⟨-, hLB, hJBsup, -⟩ := cover_facts hLq inf_le_left
    (inf_centralizer_sup_oddCoreIn_eq hB2 hBQ)
  have hB' : twoLayerIn CB ≤ twoLayerIn CA := by
    have h := GrSLit.pLayer_inf_centralizer_le_of_normalizes hB2 (le_normalizer_centralizer hBA)
    rw [inf_eq_right.mpr hCBA] at h
    exact h
  have hLBE : oddResidualIn (L ⊓ CB) ≤ twoLayerIn CA := by
    rw [← hLB]; exact hB.trans hB'
  have hEn := le_normalizer_twoLayerIn CA
  rw [hLA]
  refine (closure_le _).mpr ?_
  rintro x ⟨hxY, k, hk⟩
  obtain ⟨hxL, hxC⟩ := mem_inf.mp hxY
  have hnorm : oddResidualIn (L ⊓ CB) ≤ normalizer (oddCoreIn L : Set G) :=
    ((oddResidualIn_le _).trans inf_le_left).trans (le_normalizer_oddCoreIn L)
  have hx : x ∈ oddCoreIn L ⊔ oddResidualIn (L ⊓ CB) := by
    rw [sup_comm, hJBsup]; exact hxL
  obtain ⟨o, ho, b, hb, rfl⟩ := exists_mul_of_mem_sup_normalizer hnorm hx
  have hbC : b ∈ CA := hCBA ((mem_inf.mp ((oddResidualIn_le _) hb)).2)
  have hoC : o ∈ CA := by
    have : o = o * b * b⁻¹ := by group
    rw [this]; exact mul_mem hxC (inv_mem hbC)
  have hoodd : Odd (orderOf o) := by
    have h1 := orderOf_dvd_natCard (⟨o, ho⟩ : oddCoreIn L)
    rw [Subgroup.orderOf_mk] at h1
    exact (Nat.coprime_two_left.mp (coprime_card_oddCoreIn L)).of_dvd_nat h1
  exact mem_of_eq_mul_of_odd (map_subtype_le _) hEn rfl hoC (hLBE hb) hoodd hk

theorem twoLayer_inf_centralizer_sup_zpowers {L A : Subgroup G} {s : G}
    (hL : L ∈ solomonKStar G) (hLq : IsQuasisimple (↥L ⧸ pPrimeCore 2 ↥L)) (hA : A ≠ ⊥)
    (hA2 : IsPGroup 2 A) (hAQ : A ≤ coreActionKernel L) (hs : IsPGroup 2 (zpowers s))
    (hsQ : s ∈ coreActionKernel L) (hsA : s ∈ normalizer (A : Set G)) (hs2A : s ^ 2 ∈ A)
    (h : twoLayerIn (L ⊓ centralizer (A : Set G)) ≤ twoLayerIn (centralizer (A : Set G))) :
    twoLayerIn (L ⊓ centralizer ((A ⊔ zpowers s : Subgroup G) : Set G)) ≤
      twoLayerIn (centralizer ((A ⊔ zpowers s : Subgroup G) : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B := A ⊔ zpowers s with hB
  set CA := centralizer (A : Set G) with hCA
  set Cs := centralizer ({s} : Set G) with hCs
  set X := CA ⊔ zpowers s with hX
  have hzA : zpowers s ≤ normalizer (A : Set G) := zpowers_le.mpr hsA
  have hB2 : IsPGroup 2 B := by
    have := IsPGroup.to_sup_of_normal_right' hs hA2 hzA
    rwa [sup_comm] at this
  have hBQ : B ≤ coreActionKernel L := sup_le hAQ (zpowers_le.mpr hsQ)
  have hzCA : zpowers s ≤ normalizer (CA : Set G) := le_normalizer_centralizer hzA
  have hCB : centralizer (B : Set G) = CA ⊓ Cs := by
    ext x
    constructor
    · intro hx
      refine mem_inf.mpr ⟨centralizer_le (le_sup_left : A ≤ B) hx, ?_⟩
      rw [hCs, mem_centralizer_singleton_iff]
      exact ((mem_centralizer_iff.mp hx) s (mem_sup_right (mem_zpowers s))).symm
    · intro hx
      obtain ⟨hxA, hxs⟩ := mem_inf.mp hx
      have hle : B ≤ centralizer ({x} : Set G) := by
        refine sup_le (fun a ha => ?_) (zpowers_le.mpr ?_)
        · rw [mem_centralizer_singleton_iff]
          exact (mem_centralizer_iff.mp hxA) a ha
        · rw [mem_centralizer_singleton_iff]
          exact (mem_centralizer_singleton_iff.mp hxs).symm
      rw [mem_centralizer_iff]
      intro b hb
      exact mem_centralizer_singleton_iff.mp (hle hb)
  obtain ⟨hJc, hLB, -, ⟨eJ⟩⟩ := cover_facts hLq inf_le_left
    (inf_centralizer_sup_oddCoreIn_eq hB2 hBQ)
  obtain ⟨-, hLA, -, -⟩ := cover_facts hLq inf_le_left (inf_centralizer_sup_oddCoreIn_eq hA2 hAQ)
  set J := twoLayerIn (L ⊓ centralizer (B : Set G)) with hJ
  have hJLA : J ≤ twoLayerIn (L ⊓ CA) := by
    rw [hLB, hLA]
    refine closure_mono fun x hx => ⟨?_, hx.2⟩
    exact inf_le_inf_left L (centralizer_le (le_sup_left : A ≤ B)) hx.1
  have hJA : J ≤ twoLayerIn CA := hJLA.trans h
  have hCAX : CA ≤ X := le_sup_left
  have hXn : X ≤ normalizer (CA : Set G) := sup_le le_normalizer hzCA
  have hJX : J ≤ twoLayerIn X :=
    hJA.trans (GrSLit.pLayer_map_le_of_isSubnormal hCAX
      (Normal.isSubnormal ((normal_subgroupOf_iff_le_normalizer hCAX).mpr hXn)))
  have hJs : J ≤ Cs := by
    intro x hx
    have hx1 : x ∈ L ⊓ centralizer (B : Set G) := (map_subtype_le _) hx
    rw [hCB] at hx1
    exact (mem_inf.mp (mem_inf.mp hx1).2).2
  have hJp : ⁅J, J⁆ = J := by
    rw [hLB]
    exact UnbalancedCorr.commutator_eq_of_isPComponent hJc.1 hJc.2
  have hJq : IsQuasisimple (↥J ⧸ pPrimeCore 2 ↥J) := by
    rw [hLB]
    exact LocalCores.isQuasisimple_of_mulEquiv eJ.symm hLq
  have hJZ : Nat.card (↥J ⧸ Open.fusionZStar ↥J) = Nat.card (↥L ⧸ Open.fusionZStar ↥L) := by
    rw [hLB]
    exact Nat.card_congr (Sol78.fusionZStarQuotOfCore eJ).toEquiv
  have htype : ∀ K : Subgroup G, IsTwoComponentIn K X → ¬ J ≤ coreActionKernel K →
      Nat.card (↥K ⧸ Open.fusionZStar ↥K) = Nat.card (↥J ⧸ Open.fusionZStar ↥J) := by
    intro K hKX hmove
    have hXA : twoLayerIn X ≤ twoLayerIn CA :=
      GrSLit.pLayer_map_le_of_le_sup hCAX le_rfl hs hzCA
    have hKCA : K ≤ CA :=
      (le_twoLayerIn_of_isTwoComponentIn hKX).trans (hXA.trans (map_subtype_le _))
    have hKc : IsTwoComponentIn K CA :=
      ⟨hKCA, CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hKCA hCAX hKX.2⟩
    have hKP : K ≤ conjClosure (twoLayerIn (L ⊓ CA)) (twoLayerIn CA) :=
      (le_conjClosure_of_not_le_coreActionKernel hKc hJA hmove).trans (conjClosure_mono hJLA _)
    have hPC : conjClosure (twoLayerIn (L ⊓ CA)) (twoLayerIn CA) ≤ CA :=
      Sol78.conjClosure_le ((map_subtype_le _).trans inf_le_right)
        ((map_subtype_le _).trans le_normalizer)
    have hKc' : IsTwoComponentIn K (conjClosure (twoLayerIn (L ⊓ CA)) (twoLayerIn CA)) :=
      ⟨hKP, CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hKP hPC hKc.2⟩
    have hlt : SolomonLt L K :=
      ⟨hL.1.1, isSolomonMember_of_isTwoComponentIn hA hA2 hKc, A, hA2, hAQ, hKc'⟩
    have heq : SolomonEquiv L K := hL.1.2 L K ⟨hL.1.1, Relation.ReflTransGen.refl⟩ hlt
    obtain ⟨e⟩ := nonempty_fusionZStar_equiv_of_reflTransGen heq.2
    rw [hJZ]
    exact (Nat.card_congr e.toEquiv).symm
  have hsX : s ∈ X := mem_sup_right (mem_zpowers s)
  have hs2X : ∀ x ∈ X, s ^ 2 * x = x * s ^ 2 := by
    have hle : X ≤ centralizer ({s ^ 2} : Set G) := by
      refine sup_le (fun c hc => ?_) (zpowers_le.mpr ?_)
      · rw [mem_centralizer_singleton_iff]
        exact ((mem_centralizer_iff.mp hc) _ hs2A).symm
      · rw [mem_centralizer_singleton_iff]
        exact ((Commute.refl s).pow_right 2).eq
    intro x hx
    exact (mem_centralizer_singleton_iff.mp (hle hx)).symm
  have hmain := le_twoLayerIn_inf_centralizer hsX hs2X hs hJX hJs hJp hJq htype
  refine hmain.trans ?_
  rw [hCB]
  have hsCs : s ∈ Cs := mem_centralizer_singleton_iff.mpr rfl
  have hQY : CA ⊓ Cs ≤ X ⊓ Cs := inf_le_inf_right _ hCAX
  have hYQ : X ⊓ Cs ≤ (CA ⊓ Cs) ⊔ zpowers s := by
    intro y hy
    obtain ⟨hyX, hys⟩ := mem_inf.mp hy
    obtain ⟨c, hc, t, ht, rfl⟩ := exists_mul_of_mem_sup_normalizer hzCA hyX
    have htC : t ∈ Cs := zpowers_le.mpr hsCs ht
    have hcC : c ∈ Cs := by
      have : c = c * t * t⁻¹ := by group
      rw [this]
      exact mul_mem hys (inv_mem htC)
    exact mul_mem (mem_sup_left (mem_inf.mpr ⟨hc, hcC⟩)) (mem_sup_right ht)
  have hzQ : zpowers s ≤ normalizer ((CA ⊓ Cs : Subgroup G) : Set G) := by
    rw [zpowers_le]
    exact mem_normalizer_inf (hzCA (mem_zpowers s)) (le_normalizer hsCs)
  exact GrSLit.pLayer_map_le_of_le_sup hQY hYQ hs hzQ

end CFSG.ComponentClassification.Sol76
