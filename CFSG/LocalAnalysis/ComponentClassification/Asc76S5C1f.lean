module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76S5C1e
public import CFSG.LocalAnalysis.ComponentClassification.Asc76S5C1b

public section

namespace CFSG.ComponentClassification.Asc76.Sec5

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Overlap

variable {A R T : Subgroup G} {g : G}

theorem inf_eq_bot_K (h : Overlap A R g T) : centralizer (A : Set G) ⊓ T = ⊥ :=
  two_subgroup_of_odd_eq_bot _ _ h.sylow.isPGroup.to_inf_right (h.tight.2 g h.not_mem_K)
    (inf_le_inf_left _ (h.sylow.le.trans inf_le_left))

variable (h22 : Asc76Lemma22)

include h22 in
theorem le_normalizer_sup_oddCoreIn (h : Overlap A R g T)
    (hm : 1 < Open.pRank 2 (centralizer (A : Set G))) (hRd : ¬ IsDihedralTwoGroup R)
    (hnot : ¬ IsSylowOf 2 T (AschbacherTightEmbedding.rightConjugate (centralizer (A : Set G)) g))
    (hTe : ¬ IsElemAbelian 2 T) :
    centralizer (A : Set G) ≤ normalizer
      ((R ⊓ centralizer (T : Set G) ⊔ oddCoreIn (centralizer (A : Set G)) : Subgroup G) :
        Set G) := by
  set K := centralizer (A : Set G) with hKdef
  set C := R ⊓ centralizer (T : Set G) with hCdef
  set J := C ⊔ oddCoreIn K with hJdef
  obtain ⟨hK, hKg, hodd, hfac, hmg⟩ := h.lemma22_hyps hm
  obtain ⟨-, -, h3, -, -, h6, -⟩ :=
    h22 G _ _ T R hK hKg hodd hfac h.sylowK h.ne_bot h.sylowR h.normalizesR hm hmg
  have hW := (h6 hTe (h.ne_weakClosure h22 hm hnot)).1
  rw [h.inf_normalizer_eq] at hW
  have hTc := h.isMulCommutative h22 hm hnot
  rcases h3 with hN | ⟨n, -, φ, -, hker⟩ | hcyc
  · rw [hW] at hN
    have hXN := le_normalizer_of_normalIn hN
    have hTJ : T ≤ normalizer (J : Set G) := by
      intro t ht
      refine mem_normalizer_sup ?_ ?_
      · refine centralizer_le_normalizer C ?_
        rw [mem_centralizer_iff]
        intro c hc
        exact (mem_centralizer_iff.mp hc.2 t ht).symm
      · exact normalizer_le_normalizer_oddCoreIn K (h.sylowK.le ht).2
    have hX : (T ⊔ C ⊔ oddCoreIn K : Subgroup G) = J ⊔ T := by
      rw [hJdef, sup_comm T C, sup_assoc, sup_comm T, ← sup_assoc]
    have hXK : (T ⊔ C ⊔ oddCoreIn K : Subgroup G) ⊓ K = J := by
      refine le_antisymm ?_ (le_inf ?_ (sup_le (inf_le_left.trans h.sylowR.le) (oddCoreIn_le K)))
      · rintro x ⟨hx, hxK⟩
        have hx' : x ∈ ((J : Set G) * (T : Set G)) := by
          rw [← coe_mul_of_right_le_normalizer_left J T hTJ, ← hX]
          exact hx
        obtain ⟨j, hj, t, ht, hjt⟩ := hx'
        have hjt' : j * t = x := hjt
        have hjK : j ∈ K := (sup_le (inf_le_left.trans h.sylowR.le) (oddCoreIn_le K)) hj
        have htK : t ∈ K := by
          have : t = j⁻¹ * x := by rw [← hjt']; group
          rw [this]
          exact K.mul_mem (K.inv_mem hjK) hxK
        have ht1 : t ∈ K ⊓ T := ⟨htK, ht⟩
        rw [h.inf_eq_bot_K, mem_bot] at ht1
        rw [← hjt', ht1, mul_one]
        exact hj
      · rw [hX]
        exact le_sup_left
    intro k hk
    rw [← hXK]
    exact mem_normalizer_inf (hXN (mem_sup_left hk)) (Subgroup.le_normalizer hk)
  · exfalso
    apply hTe
    have hR2 := sq_eq_one_of_caseL2 h.sylowR φ hker
    obtain ⟨e⟩ := h.mulEquiv
    refine Asc76X.isElemAbelian_of_mulEquiv e ⟨isMulCommutative_of_mulEquiv' e hTc, fun c hc =>
      hR2 c hc.1⟩
  · exact absurd hcyc (h.not_isCyclic h22 hm hRd hnot)

theorem normalizer_le_normalizer_sup_oddCoreIn (h : Overlap A R g T)
    (hJ : centralizer (A : Set G) ≤ normalizer
      ((R ⊓ centralizer (T : Set G) ⊔ oddCoreIn (centralizer (A : Set G)) : Subgroup G) :
        Set G))
    (hC : normalizer (R : Set G) ≤
      normalizer ((R ⊓ centralizer (T : Set G) : Subgroup G) : Set G)) :
    normalizer (centralizer (A : Set G) : Set G) ≤ normalizer
      ((R ⊓ centralizer (T : Set G) ⊔ oddCoreIn (centralizer (A : Set G)) : Subgroup G) :
        Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := centralizer (A : Set G) with hKdef
  intro n hn
  have hKn : AschbacherTightEmbedding.rightConjugate K n = K :=
    (rightConjugate_eq_self_iff K n).mpr hn
  have hRn : IsSylowOf 2 (AschbacherTightEmbedding.rightConjugate R n) K := by
    have := isSylowOf_rightConjugate h.sylowR n
    rwa [hKn] at this
  obtain ⟨c, hc, hcR⟩ := exists_rightConjugate_eq_of_isSylowOf hRn h.sylowR
  have hcn : c * n⁻¹ ∈ normalizer (R : Set G) := by
    rw [← rightConjugate_eq_self_iff, ← rightConjugate_mul, hcR, rightConjugate_mul,
      mul_inv_cancel, rightConjugate_one]
  have hReven : Even (Nat.card R) :=
    even_iff_two_dvd.mpr (two_dvd_card_of_isSylowOf h.sylowR h.tight.1)
  have hNRK : normalizer (R : Set G) ≤ normalizer (K : Set G) :=
    normalizer_le_normalizer_of_tightlyEmbedded h.tight h.sylowR.le hReven
  have hmJ := mem_normalizer_sup (hC hcn) (normalizer_le_normalizer_oddCoreIn K (hNRK hcn))
  have hcJ := hJ hc
  have hn' : n = (c * n⁻¹)⁻¹ * c := by group
  rw [hn']
  exact mul_mem (inv_mem hmJ) hcJ

end Overlap

omit [Finite G] in
theorem oUpperTwoPrime_oUpperTwoPrime (X : Subgroup G) :
    oUpperTwoPrime (oUpperTwoPrime X) = oUpperTwoPrime X := by
  refine le_antisymm (oUpperTwoPrime_le _) ?_
  refine (closure_le _).mpr ?_
  rintro x ⟨hx, k, hk⟩
  exact mem_oUpperTwoPrime (mem_oUpperTwoPrime hx hk) hk

theorem isSylowOf_oUpperTwoPrime_sup {C K : Subgroup G} (hCK : C ≤ K) (hC : IsPGroup 2 C) :
    IsSylowOf 2 C (oUpperTwoPrime (C ⊔ oddCoreIn K)) ∧ C ≤ oUpperTwoPrime (C ⊔ oddCoreIn K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCJ₀ : C ≤ oUpperTwoPrime (C ⊔ oddCoreIn K) := fun c hc => by
    obtain ⟨m, hm⟩ := hC ⟨c, hc⟩
    exact mem_oUpperTwoPrime (mem_sup_left hc) (n := m) (by simpa using congrArg Subtype.val hm)
  have hsyl := (isSylowOf_and_isTwoNilpotent_oddCoreIn_sup hCK hC).1
  rw [sup_comm] at hsyl
  exact ⟨hsyl.of_le hCJ₀ (oUpperTwoPrime_le _), hCJ₀⟩

end CFSG.ComponentClassification.Asc76.Sec5
