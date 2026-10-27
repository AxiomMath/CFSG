module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Sylow
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingAction
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingSylow

public section

namespace CFSG.ComponentClassification.Asc76.Lemma22

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type} [Group G] [Finite G]

theorem card_le_of_isSylowOf {M P X : Subgroup G} (hP : IsSylowOf 2 P M) (hX : IsPGroup 2 X)
    (hXM : X ≤ M) : Nat.card X ≤ Nat.card P := by
  obtain ⟨D, hD, hXD⟩ := AschbacherTheorem3.exists_isSylowOf_le hX hXM
  rw [hP.card_eq, ← hD.card_eq]
  exact Subgroup.card_le_of_le hXD

theorem card_le_of_factorization_eq {K J B R : Subgroup G}
    (hfac : (Nat.card K).factorization 2 = (Nat.card J).factorization 2) (hB : IsPGroup 2 B)
    (hBJ : B ≤ J) (hR : IsSylowOf 2 R K) : Nat.card B ≤ Nat.card R := by
  obtain ⟨D, hD⟩ := exists_isSylowOf 2 J
  rw [hR.card_eq, hfac, ← hD.card_eq]
  exact card_le_of_isSylowOf hD hB hBJ

theorem inf_eq_bot_of_le {K J T : Subgroup G}
    (hKJ : Odd (Nat.card (K ⊓ J : Subgroup G))) (hT : IsPGroup 2 T) (hTJ : T ≤ J) :
    T ⊓ K = ⊥ :=
  two_subgroup_of_odd_eq_bot (T ⊓ K) (K ⊓ J) (hT.to_le inf_le_left) hKJ
    (le_inf inf_le_right (inf_le_left.trans hTJ))

omit [Finite G] in
theorem sup_inf_eq {K R T : Subgroup G} (hRK : R ≤ K) (hTR : T ≤ normalizer (R : Set G))
    (hTK : T ⊓ K = ⊥) : (R ⊔ T) ⊓ K = R := by
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_left hRK)
  obtain ⟨r, hr, t, ht, rfl⟩ := NormalizedProduct.coordinates R T hTR x hx.1
  have htK : t ∈ K := by
    have h := K.mul_mem (K.inv_mem (hRK hr)) hx.2
    rwa [inv_mul_cancel_left] at h
  have ht1 : t = 1 := by
    have hmem : t ∈ T ⊓ K := ⟨ht, htK⟩
    rw [hTK] at hmem
    exact hmem
  rw [ht1, mul_one]
  exact hr

omit [Finite G] in
theorem relativeNormalizer_sup_inf {K R T : Subgroup G} (hRK : R ≤ K)
    (hTR : T ≤ normalizer (R : Set G)) (hTK : T ⊓ K = ⊥) :
    relativeNormalizer T (R ⊔ T) ⊓ K = R ⊓ normalizer (T : Set G) := by
  rw [relativeNormalizer, inf_assoc, sup_inf_eq hRK hTR hTK, inf_comm]

theorem isSylowOf_sup {K R T : Subgroup G} (hR : IsSylowOf 2 R K) (hT : IsPGroup 2 T)
    (hTK : T ≤ normalizer (K : Set G)) (hTR : T ≤ normalizer (R : Set G)) (hTKb : T ⊓ K = ⊥) :
    IsSylowOf 2 (R ⊔ T) (K ⊔ T) := by
  have hRT : R ⊓ T = ⊥ := le_bot_iff.mp (by
    rw [inf_comm]
    exact (inf_le_inf_left T hR.le).trans hTKb.le)
  have hKT : K ⊓ T = ⊥ := by rw [inf_comm]; exact hTKb
  have hle : R ⊔ T ≤ K ⊔ T := sup_le_sup_right hR.le T
  rw [isSylowOf_iff]
  refine ⟨hle, hR.isPGroup.to_sup_of_normal_left' hT hTR, ?_⟩
  have h1 := Subgroup.relIndex_mul_card (R ⊔ T) (K ⊔ T)
  rw [inf_eq_left.mpr hle, AschbacherTheorem3.card_sup_of_le_normalizer hTR hRT,
    AschbacherTheorem3.card_sup_of_le_normalizer hTK hKT] at h1
  have h2 := Subgroup.relIndex_mul_card R K
  rw [inf_eq_left.mpr hR.le] at h2
  have h3 : (R ⊔ T).relIndex (K ⊔ T) = R.relIndex K := by
    have hpos : 0 < Nat.card R * Nat.card T := Nat.mul_pos Nat.card_pos Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc (R ⊔ T).relIndex (K ⊔ T) * (Nat.card R * Nat.card T) = Nat.card K * Nat.card T := h1
      _ = R.relIndex K * Nat.card R * Nat.card T := by rw [h2]
      _ = R.relIndex K * (Nat.card R * Nat.card T) := by ring
  rw [h3]
  exact (isSylowOf_iff.mp hR).2.2

theorem card_le_card_relativeNormalizer_inf {K J T S : Subgroup G} (hJ : TightlyEmbedded J)
    (hKJ : Odd (Nat.card (K ⊓ J : Subgroup G)))
    (hfac : (Nat.card K).factorization 2 = (Nat.card J).factorization 2)
    (hTK : T ≤ normalizer (K : Set G)) (hTJ : T ≤ J) (hTS : T ≤ S) (hS : S ≤ K ⊔ T)
    (hS2 : IsPGroup 2 S) (hSK : IsSylowOf 2 (S ⊓ K) K) :
    Nat.card T ≤ Nat.card (relativeNormalizer T S ⊓ K : Subgroup G) := by
  have hJK : Odd (Nat.card (J ⊓ K : Subgroup G)) := by rwa [inf_comm]
  rcases complement_normalizer_alternative J K T S hJ hJK hTK hTJ hTS hS hS2 with
    hnormal | ⟨φ, hφ⟩
  · have heq : relativeNormalizer T S ⊓ K = S ⊓ K := by
      rw [show relativeNormalizer T S = S from inf_eq_right.mpr hnormal]
    rw [heq]
    exact card_le_of_factorization_eq hfac (hS2.to_le hTS) hTJ hSK
  · exact (Nat.card_le_card_of_injective φ hφ).trans (Subgroup.card_le_card_group _)

theorem card_relativeNormalizer_inf_le {K J T S : Subgroup G} (hK : TightlyEmbedded K)
    (hJ : TightlyEmbedded J) (hKJ : Odd (Nat.card (K ⊓ J : Subgroup G)))
    (hfac : (Nat.card K).factorization 2 = (Nat.card J).factorization 2)
    (hT : IsSylowOf 2 T (J ⊓ normalizer (K : Set G))) (hT1 : T ≠ ⊥) (hS2 : IsPGroup 2 S) :
    Nat.card (relativeNormalizer T S ⊓ K : Subgroup G) ≤ Nat.card T := by
  set C := relativeNormalizer T S ⊓ K with hCdef
  have hC2 : IsPGroup 2 C := hS2.to_le (inf_le_left.trans inf_le_right)
  by_cases hCbot : C = ⊥
  · rw [hCbot, Subgroup.card_bot]
    exact Nat.card_pos
  have hTJ : T ≤ J := hT.le.trans inf_le_left
  have hTK : T ≤ normalizer (K : Set G) := hT.le.trans inf_le_right
  have hT2 : IsPGroup 2 T := hT.isPGroup
  have hCJ : C ≤ normalizer (J : Set G) :=
    (inf_le_left.trans inf_le_left).trans (normalizer_two_subgroup_le J T hJ hT2 hTJ hT1)
  have hTKJ : T ≤ normalizer ((K ⊓ normalizer (J : Set G) : Subgroup G) : Set G) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hTK ht, Subgroup.le_normalizer (Subgroup.le_normalizer (hTJ ht))⟩
  obtain ⟨D, hD⟩ := TwoActionInvariantSylow.subgroup (K ⊓ normalizer (J : Set G)) T hT2 hTKJ
  set B := sylowImage (K ⊓ normalizer (J : Set G)) D with hBdef
  have hBK : B ≤ K := (sylowImage_le _ D).trans inf_le_left
  have hBJ : B ≤ normalizer (J : Set G) := (sylowImage_le _ D).trans inf_le_right
  have hTB : T ≤ normalizer (B : Set G) := hD
  have hB2 : IsPGroup 2 B := sylowImage_isPGroup _ D
  have hCB : Nat.card C ≤ Nat.card B :=
    two_subgroup_card_le_sylowImage _ C hC2 (le_inf inf_le_right hCJ) D
  have hBne : B ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hCB
    exact hCbot (C.eq_bot_of_card_le hCB)
  have hTB2 : IsPGroup 2 (T ⊔ B : Subgroup G) := by
    rw [sup_comm]
    exact hB2.to_sup_of_normal_left' hT2 hTB
  obtain ⟨F, hF, hTBF⟩ :=
    AschbacherTheorem3.exists_isSylowOf_le hTB2 (sup_le (hTJ.trans le_sup_left) le_sup_right)
  have hFJ : IsSylowOf 2 (F ⊓ J) J :=
    hF.inf_of_le_normalizer le_sup_left (sup_le Subgroup.le_normalizer hBJ)
  have hBbound := card_le_card_relativeNormalizer_inf hK (by rwa [inf_comm]) hfac.symm hBJ hBK
    (le_sup_right.trans hTBF) hF.le hF.isPGroup hFJ
  have hle : relativeNormalizer B F ⊓ J ≤ J ⊓ normalizer (K : Set G) := fun x hx =>
    ⟨hx.2, normalizer_two_subgroup_le K B hK hB2 hBK hBne hx.1.1⟩
  exact hCB.trans (hBbound.trans
    (card_le_of_isSylowOf hT (hF.isPGroup.to_le (inf_le_left.trans inf_le_right)) hle))

theorem card_inf_normalizer {K J T R : Subgroup G} (hK : TightlyEmbedded K)
    (hJ : TightlyEmbedded J) (hKJ : Odd (Nat.card (K ⊓ J : Subgroup G)))
    (hfac : (Nat.card K).factorization 2 = (Nat.card J).factorization 2)
    (hT : IsSylowOf 2 T (J ⊓ normalizer (K : Set G))) (hT1 : T ≠ ⊥) (hR : IsSylowOf 2 R K)
    (hTR : T ≤ normalizer (R : Set G)) :
    Nat.card (R ⊓ normalizer (T : Set G) : Subgroup G) = Nat.card T := by
  have hTJ : T ≤ J := hT.le.trans inf_le_left
  have hTK : T ≤ normalizer (K : Set G) := hT.le.trans inf_le_right
  have hTKb := inf_eq_bot_of_le hKJ hT.isPGroup hTJ
  have hS2 : IsPGroup 2 (R ⊔ T : Subgroup G) := hR.isPGroup.to_sup_of_normal_left' hT.isPGroup hTR
  rw [← relativeNormalizer_sup_inf hR.le hTR hTKb]
  refine le_antisymm (card_relativeNormalizer_inf_le hK hJ hKJ hfac hT hT1 hS2) ?_
  refine card_le_card_relativeNormalizer_inf hJ hKJ hfac hTK hTJ le_sup_right
    (sup_le_sup_right hR.le T) hS2 ?_
  rw [sup_inf_eq hR.le hTR hTKb]
  exact hR

theorem normalizer_alternative {K J T R : Subgroup G} (hJ : TightlyEmbedded J)
    (hKJ : Odd (Nat.card (K ⊓ J : Subgroup G))) (hT : IsSylowOf 2 T (J ⊓ normalizer (K : Set G)))
    (hR : IsSylowOf 2 R K) (hTR : T ≤ normalizer (R : Set G)) :
    R ≤ normalizer (T : Set G) ∨ ∃ φ : T →* (R ⊓ normalizer (T : Set G) : Subgroup G),
      Function.Injective φ ∧ ∀ a b : T, φ a * φ b = φ b * φ a := by
  have hTJ : T ≤ J := hT.le.trans inf_le_left
  have hTKb := inf_eq_bot_of_le hKJ hT.isPGroup hTJ
  have hJK : Odd (Nat.card (J ⊓ K : Subgroup G)) := by rwa [inf_comm]
  rcases complement_normalizer_alternative J K T (R ⊔ T) hJ hJK (hT.le.trans inf_le_right) hTJ
    le_sup_right (sup_le_sup_right hR.le T)
    (hR.isPGroup.to_sup_of_normal_left' hT.isPGroup hTR) with hnormal | ⟨φ, hφ⟩
  · exact Or.inl (le_sup_left.trans hnormal)
  · let e := MulEquiv.subgroupCongr (relativeNormalizer_sup_inf hR.le hTR hTKb)
    refine Or.inr ⟨e.toMonoidHom.comp ((center _).subtype.comp φ),
      e.injective.comp ((center _).subtype_injective.comp hφ), fun a b => ?_⟩
    change e (φ a : _) * e (φ b : _) = e (φ b : _) * e (φ a : _)
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (φ b).2 (φ a)]

theorem nonempty_inf_normalizer_mulEquiv {K J T R : Subgroup G} (hK : TightlyEmbedded K)
    (hJ : TightlyEmbedded J) (hKJ : Odd (Nat.card (K ⊓ J : Subgroup G)))
    (hfac : (Nat.card K).factorization 2 = (Nat.card J).factorization 2)
    (hT : IsSylowOf 2 T (J ⊓ normalizer (K : Set G))) (hT1 : T ≠ ⊥) (hR : IsSylowOf 2 R K)
    (hTR : T ≤ normalizer (R : Set G)) (hlt : Nat.card T < Nat.card R) :
    Nonempty ((R ⊓ normalizer (T : Set G) : Subgroup G) ≃* T) := by
  have hcard := card_inf_normalizer hK hJ hKJ hfac hT hT1 hR hTR
  rcases normalizer_alternative hJ hKJ hT hR hTR with hnormal | ⟨φ, hφ, -⟩
  · rw [inf_eq_left.mpr hnormal] at hcard
    omega
  · have hbij : Function.Bijective φ := by
      have := Fintype.ofFinite T
      have := Fintype.ofFinite (R ⊓ normalizer (T : Set G) : Subgroup G)
      refine (Fintype.bijective_iff_injective_and_card φ).mpr ⟨hφ, ?_⟩
      simpa only [Nat.card_eq_fintype_card] using hcard.symm
    exact ⟨(MulEquiv.ofBijective φ hbij).symm⟩

theorem isMulCommutative {K J T R : Subgroup G} (hK : TightlyEmbedded K)
    (hJ : TightlyEmbedded J) (hKJ : Odd (Nat.card (K ⊓ J : Subgroup G)))
    (hfac : (Nat.card K).factorization 2 = (Nat.card J).factorization 2)
    (hT : IsSylowOf 2 T (J ⊓ normalizer (K : Set G))) (hT1 : T ≠ ⊥) (hR : IsSylowOf 2 R K)
    (hTR : T ≤ normalizer (R : Set G)) (hTJ : ¬ IsSylowOf 2 T J) : IsMulCommutative T := by
  rcases normalizer_alternative hJ hKJ hT hR hTR with hnormal | ⟨φ, hφ, hcomm⟩
  · exfalso
    apply hTJ
    have hcard := card_inf_normalizer hK hJ hKJ hfac hT hT1 hR hTR
    rw [inf_eq_left.mpr hnormal] at hcard
    refine isSylowOf_of_card (hT.le.trans inf_le_left) ?_
    rw [← hcard, hR.card_eq, hfac]
  · exact ⟨⟨fun a b => hφ (by rw [map_mul, map_mul, hcomm a b])⟩⟩

end CFSG.ComponentClassification.Asc76.Lemma22
