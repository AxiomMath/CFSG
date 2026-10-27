module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76S5C1e

public section

namespace CFSG.ComponentClassification.Asc76.Sec5

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3

variable {G : Type} [Group G] [Finite G]

theorem Overlap.isSylowOf_or_eq_rightConjugate {A R T : Subgroup G} {g : G}
    (h : Overlap A R g T)
    (H : ∀ (x : G) (V : Subgroup G), Overlap A R x V →
      IsSylowOf 2 V (rightConjugate (centralizer (A : Set G)) x) ∨
        R ⊓ centralizer (V : Set G) = R ⊓ centralizer (T : Set G))
    {z : G} (hz : z ∉ normalizer (A : Set G)) {V' : Subgroup G}
    (hV' : IsSylowOf 2 V' (centralizer (A : Set G) ⊓
      normalizer (rightConjugate (centralizer (A : Set G)) z : Set G))) (hV'1 : V' ≠ ⊥) :
    IsSylowOf 2 V' (centralizer (A : Set G)) ∨
      ∃ k ∈ centralizer (A : Set G), V' = rightConjugate (R ⊓ centralizer (T : Set G)) k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := centralizer (A : Set G) with hKdef
  have hK := h.tight
  have hNA : normalizer (K : Set G) = normalizer (A : Set G) := normalizer_centralizer_eq h.standard
  have hzK : z ∉ normalizer (K : Set G) := by rwa [hNA]
  set Kz := rightConjugate K z with hKzdef
  have hKz : TightlyEmbedded Kz := tightlyEmbedded_rightConjugate hK z
  have hV'K : V' ≤ K := hV'.le.trans inf_le_left
  have hV'N : V' ≤ normalizer (Kz : Set G) := hV'.le.trans inf_le_right
  have hV'p : IsPGroup 2 V' := hV'.isPGroup
  have hV'even : Even (Nat.card V') := even_card_of_isPGroup hV'p hV'1
  obtain ⟨S, hS, hV'S⟩ := exists_isSylowOf_le (le_sup_right : V' ≤ Kz ⊔ V') hV'p
  have hRz : IsSylowOf 2 (S ⊓ Kz) Kz :=
    hS.inf_of_le_normalizer le_sup_left (sup_le le_normalizer hV'N)
  have hV'Rz : V' ≤ normalizer ((S ⊓ Kz : Subgroup G) : Set G) := fun v hv =>
    mem_normalizer_inf (le_normalizer (hV'S hv)) (hV'N hv)
  have hzz : rightConjugate Kz z⁻¹ = K := by
    rw [hKzdef, rightConjugate_mul, mul_inv_cancel, rightConjugate_one]
  have hz' : z⁻¹ ∉ normalizer (Kz : Set G) := by
    intro hzN
    apply hzK
    have h1 := (rightConjugate_eq_self_iff Kz z⁻¹).mpr hzN
    rw [hzz] at h1
    exact (rightConjugate_eq_self_iff K z).mp h1.symm
  have hV'' : IsSylowOf 2 V' (rightConjugate Kz z⁻¹ ⊓ normalizer (Kz : Set G)) := by
    rw [hzz]; exact hV'
  obtain ⟨e⟩ := inf_centralizer_mulEquiv_of_tightlyEmbedded hKz hz' hV'' hV'1 hRz hV'Rz
  set V'' := S ⊓ Kz ⊓ centralizer (V' : Set G) with hV''def
  have hV''le : V'' ≤ Kz ⊓ normalizer (K : Set G) :=
    le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans ((centralizer_le_normalizer _).trans
      (normalizer_le_normalizer_of_tightlyEmbedded hK hV'K hV'even)))
  obtain ⟨P, hP⟩ := exists_isSylowOf 2 (Kz ⊓ normalizer (rightConjugate Kz z⁻¹ : Set G))
  have hcardP := card_eq_card_of_overlap hKz hz' hV'' hV'1 hP
  have hP' : IsSylowOf 2 P (Kz ⊓ normalizer (K : Set G)) := by rwa [hzz] at hP
  have hcardV'' : Nat.card V'' = Nat.card V' := Nat.card_congr e.toEquiv
  have hV''syl : IsSylowOf 2 V'' (Kz ⊓ normalizer (K : Set G)) :=
    isSylowOf_of_card hV''le (by rw [hcardV'', ← hcardP, hP'.card_eq])
  have hV''p : IsPGroup 2 V'' := hRz.isPGroup.to_le inf_le_left
  have hV''N : V'' ≤ normalizer (K : Set G) := hV''le.trans inf_le_right
  have hcomm : V'' ≤ normalizer (V' : Set G) := inf_le_right.trans (centralizer_le_normalizer _)
  have hVV : IsPGroup 2 (V' ⊔ V'' : Subgroup G) := hV'p.to_sup_of_normal_left' hV''p hcomm
  obtain ⟨S', hS', hS'le⟩ := exists_isSylowOf_le (sup_le_sup_right hV'K V'') hVV
  have hR' : IsSylowOf 2 (S' ⊓ K) K :=
    hS'.inf_of_le_normalizer le_sup_left (sup_le le_normalizer hV''N)
  have hV'R' : V' ≤ S' ⊓ K := le_inf (le_sup_left.trans hS'le) hV'K
  have hV''R' : V'' ≤ normalizer ((S' ⊓ K : Subgroup G) : Set G) := fun v hv =>
    mem_normalizer_inf (le_normalizer (hS'le (mem_sup_right hv))) (hV''N hv)
  have hV''1 : V'' ≠ ⊥ := by
    intro hb
    rw [hb, card_bot] at hcardV''
    exact hV'1 (card_eq_one.mp hcardV''.symm)
  have hO' : Overlap A (S' ⊓ K) z V'' :=
    ⟨h.standard, hz, by rw [← hNA]; exact hV''syl, hV''1, hR', hV''R'⟩
  obtain ⟨c, hc, hcR⟩ := exists_rightConjugate_eq_of_isSylowOf hR' h.sylowR
  have hcA : c⁻¹ ∈ normalizer (A : Set G) := by
    rw [← hNA]
    exact le_normalizer (K.inv_mem hc)
  have hO'' := hO'.conj hcA
  have hRc : rightConjugate (S' ⊓ K) c⁻¹ = R := by
    rw [← hcR, rightConjugate_mul, mul_inv_cancel, rightConjugate_one]
  rw [hRc] at hO''
  rcases H _ _ hO'' with hs | heq
  · left
    refine isSylowOf_of_card hV'K ?_
    rw [← hcardV'', ← rightConjugate_card V'' c⁻¹, hs.card_eq, rightConjugate_card]
  · right
    refine ⟨c, hc, ?_⟩
    have h1 : rightConjugate (R ⊓ centralizer (rightConjugate V'' c⁻¹ : Set G)) c =
        S' ⊓ K ⊓ centralizer (V'' : Set G) := by
      rw [AschbacherTheorem3.rightConjugate_inf, AschbacherTheorem3.rightConjugate_centralizer,
        hcR, rightConjugate_mul, inv_mul_cancel, rightConjugate_one]
    rw [heq] at h1
    have hV'C : V' ≤ S' ⊓ K ⊓ centralizer (V'' : Set G) :=
      le_inf hV'R' (le_centralizer_iff.mp inf_le_right)
    have hcard2 : Nat.card (S' ⊓ K ⊓ centralizer (V'' : Set G) : Subgroup G) = Nat.card V' := by
      rw [hO'.card_inf_centralizer, hcardV'']
    have hle : V' ≤ rightConjugate (R ⊓ centralizer (T : Set G)) c := by
      rw [h1]
      exact hV'C
    exact eq_of_le_of_card_ge hle (by rw [h1, hcard2])

end CFSG.ComponentClassification.Asc76.Sec5
