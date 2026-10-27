module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76Lemma22PartTwo

public section

namespace CFSG.ComponentClassification.Asc76.Lemma22

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem5
open CFSG.ComponentClassification.AschbacherTheorem5.SectionSix
open CFSG.SignalizerFunctor.Helpers (relativeWeakClosure)

variable {G : Type} [Group G] [Finite G]

theorem weakClosure_eq_and {K J T R : Subgroup G} (hK : TightlyEmbedded K)
    (hJ : TightlyEmbedded J) (hKJ : Odd (Nat.card (K ⊓ J : Subgroup G)))
    (hfac : (Nat.card K).factorization 2 = (Nat.card J).factorization 2)
    (hT : IsSylowOf 2 T (J ⊓ normalizer (K : Set G))) (hT1 : T ≠ ⊥) (hR : IsSylowOf 2 R K)
    (hTR : T ≤ normalizer (R : Set G)) (hel : ¬ CFSG.Open.IsElemAbelian 2 T)
    (hW : T ≠ weakClosure K T (R ⊔ T)) :
    weakClosure K T (R ⊔ T) = T ⊔ (R ⊓ normalizer (T : Set G)) ∧
      (∀ E : Subgroup G, R ⊓ normalizer (T : Set G) ≤ E → E ≤ R →
        (∀ x ∈ E, x ^ 2 ∈ R ⊓ normalizer (T : Set G)) →
        (∀ x ∈ E, ∀ y ∈ E, x * y * x⁻¹ * y⁻¹ ∈ R ⊓ normalizer (T : Set G)) →
        (R ⊓ normalizer (T : Set G)).relIndex E ≤ 2) ∧
      ∀ r ∈ R, r ∉ R ⊓ normalizer (T : Set G) → r ^ 2 ∈ R ⊓ normalizer (T : Set G) →
        ∀ x ∈ R ⊓ normalizer (T : Set G), r * x * r⁻¹ = x⁻¹ := by
  set N := R ⊓ normalizer (T : Set G) with hNdef
  have hTJ : T ≤ J := hT.le.trans inf_le_left
  have hTK : T ≤ normalizer (K : Set G) := hT.le.trans inf_le_right
  have hT2 : IsPGroup 2 T := hT.isPGroup
  have hTKb := inf_eq_bot_of_le hKJ hT2 hTJ
  have hKN : K ≤ normalizer (K : Set G) := le_normalizer
  have hRN : R ≤ normalizer (K : Set G) := hR.le.trans hKN
  have hS2 : IsPGroup 2 (R ⊔ T : Subgroup G) := hR.isPGroup.to_sup_of_normal_left' hT2 hTR
  have hSN : R ⊔ T ≤ normalizer (K : Set G) := sup_le hRN hTK
  have hSsyl : IsSylowOf 2 (R ⊔ T) (K ⊔ T) := isSylowOf_sup hR hT2 hTK hTR hTKb
  have hSNT := isSylowOf_sup_inf_normalizer hK hJ hKJ hfac hT hT1 hR hTR
  have hSbar : bar K (R ⊔ T) ⊓ normalizer (bar K T : Set (Bar K)) =
      bar K ((R ⊔ T) ⊓ normalizer (T : Set G)) :=
    (bar_inf_normalizer (sup_le hKN hTK) ((core_le K).trans le_sup_left) hT2 hTK hSsyl.le hS2
      hSNT).1
  have hNS : (R ⊔ T) ⊓ normalizer (T : Set G) = T ⊔ N := by
    have h41 := (AschbacherTheorem3.lemma_4_1 ⟨hTK, hTKb, hT2⟩ (sup_le_sup_right hR.le T)
      (le_sup_right : T ≤ R ⊔ T)).1
    rwa [inf_right_comm, sup_inf_eq hR.le hTR hTKb] at h41
  have h3 := hyp3 hK hJ hKJ hfac hT hT1 hR hTR
  have hWne := relativeWeakClosure_ne hR hT2 hTK hTR hW
  have helb : ¬ CFSG.Open.IsElemAbelian 2 (bar K T) := by
    obtain ⟨eT⟩ := nonempty_mulEquiv_bar hTK hT2
    exact fun h => hel (isElemAbelian_of_mulEquiv eT h)
  obtain ⟨g, -, h45, hHS, hWM⟩ := Asc75L47.weakClosure_eq_of_not_isElemAbelian h3 hWne helb
  set H := (bar K K ⊔ bar K T) ⊓ normalizer (bar K (J ⊓ (K ⊔ T)) : Set (Bar K)) with hHdef
  have hM : H ⊓ bar K (R ⊔ T) = bar K ((R ⊔ T) ⊓ normalizer (T : Set G)) := by
    rw [h45.inf_eq_normalizer, hSbar]
  have hSM : bar K (R ⊔ T) ≤ normalizer ((H ⊓ bar K (R ⊔ T) : Subgroup (Bar K)) : Set (Bar K)) := by
    rw [hHS, ← hWM]
    exact AschbacherTheorem3.le_normalizer_relativeWeakClosure h45.frame h45.le_sup h45.le_S
  have hmemM : ∀ y : normalizer (K : Set G), (y : G) ∈ R →
      (toBar K y ∈ H ⊓ bar K (R ⊔ T) ↔ (y : G) ∈ N) := by
    intro y hy
    rw [hM]
    constructor
    · intro h
      exact ⟨hy, (mem_of_toBar_mem_bar inf_le_left hS2 (mem_sup_left hy) h).2⟩
    · intro h
      exact toBar_mem_bar K ⟨mem_sup_left hy, h.2⟩
  have hmemS : ∀ y : normalizer (K : Set G), (y : G) ∈ R → toBar K y ∈ bar K (R ⊔ T) :=
    fun y hy => toBar_mem_bar K (mem_sup_left hy)
  refine ⟨?_, ?_, ?_⟩
  ·
    rw [← hNS]
    refine eq_of_bar_eq (weakClosure_le K T (R ⊔ T)) inf_le_left hS2 hSN ?_
    rw [bar_weakClosure hSN hTK hT2, hWM, ← hHS, hM]
  ·
    intro E hNE hER hE2 hEc
    refine AschbacherTheorem3.Elem47.relIndex_le_two hNE fun u hu v hv huN hvN => ?_
    by_contra huv
    apply helb
    set u' : normalizer (K : Set G) := ⟨u, hRN (hER hu)⟩ with hu'
    set v' : normalizer (K : Set G) := ⟨v, hRN (hER hv)⟩ with hv'
    have huR : u ∈ R := hER hu
    have hvR : v ∈ R := hER hv
    have huvN : u * v ∉ N := by
      intro h
      apply huv
      have h1 := N.mul_mem h (N.inv_mem (hE2 v hv))
      rwa [show u * v * (v ^ 2)⁻¹ = u * v⁻¹ by group] at h1
    refine AschbacherTheorem3.lemma_4_5_three h45 ⟨toBar K u',
      ⟨hmemS u' huR, hSM (hmemS u' huR)⟩, toBar K v', ⟨hmemS v' hvR, hSM (hmemS v' hvR)⟩,
      fun h => huN ((hmemM u' huR).mp h), fun h => hvN ((hmemM v' hvR).mp h), ?_, ?_, ?_, ?_⟩
    · rw [← map_mul]
      exact fun h => huvN ((hmemM (u' * v') (R.mul_mem huR hvR)).mp h)
    · rw [← map_pow]
      exact (hmemM (u' ^ 2) (R.pow_mem huR 2)).mpr (hE2 u hu)
    · rw [← map_pow]
      exact (hmemM (v' ^ 2) (R.pow_mem hvR 2)).mpr (hE2 v hv)
    · rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      exact (hmemM (u' * v' * u'⁻¹ * v'⁻¹) (R.mul_mem (R.mul_mem (R.mul_mem huR hvR)
        (R.inv_mem huR)) (R.inv_mem hvR))).mpr (hEc u hu v hv)
  ·
    intro r hr hrN hr2 x hx
    set r' : normalizer (K : Set G) := ⟨r, hRN hr⟩ with hr'
    set x' : normalizer (K : Set G) := ⟨x, hRN hx.1⟩ with hx'
    have hrS := hmemS r' hr
    have hrH : (toBar K r')⁻¹ ∉ H := by
      intro h
      apply hrN
      refine (hmemM r' hr).mp ⟨?_, hrS⟩
      simpa using H.inv_mem h
    have hr2H : (toBar K r')⁻¹ ^ 2 ∈ H := by
      rw [inv_pow, ← map_pow]
      exact H.inv_mem ((hmemM (r' ^ 2) (R.pow_mem hr 2)).mpr hr2).1
    obtain ⟨-, -, -, hinv⟩ := h45.commutator_map (inv_mem hrS) (hSM (inv_mem hrS)) hrH hr2H
    have hxW : toBar K x' ∈
        (bar K T ⊔ rightConjugate (bar K T) g) ⊓ bar K K := by
      refine ⟨?_, toBar_mem_bar K (hR.le hx.1)⟩
      rw [← hHS]
      exact (hmemM x' hx.1).mpr hx
    have h1 := hinv _ hxW
    rw [inv_inv, ← map_inv, ← map_mul, ← map_mul, ← map_inv] at h1
    have h2 := toBar_injOn_of_isPGroup hS2
      (mem_sup_left (R.mul_mem (R.mul_mem hr hx.1) (R.inv_mem hr)) : (r' * x' * r'⁻¹ : G) ∈ R ⊔ T)
      (mem_sup_left (R.inv_mem hx.1) : ((x'⁻¹ : normalizer (K : Set G)) : G) ∈ R ⊔ T) h1
    exact congrArg Subtype.val h2

end CFSG.ComponentClassification.Asc76.Lemma22
