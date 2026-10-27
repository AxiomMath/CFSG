module

public import CFSG.GH74.QTGen4.DSGen4.OpenLeaves
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.CharTwo

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

private theorem sylowS_relIndex_inf {G : Type} [Group G] [Finite G] {S K : Subgroup G}
    (hS : S ≤ Subgroup.normalizer (K : Set G)) :
    (S ⊓ K).relIndex K = S.relIndex (S ⊔ K) := by
  have h1 := Subgroup.relIndex_mul_relIndex (S ⊓ K) S (S ⊔ K) inf_le_left le_sup_left
  have h2 := Subgroup.relIndex_mul_relIndex (S ⊓ K) K (S ⊔ K) inf_le_right le_sup_right
  have h3 : K.relIndex (S ⊔ K) = (S ⊓ K).relIndex S := by
    rw [F1.relIndex_sup_eq_of_le_normalizer hS, Subgroup.inf_relIndex_left]
  rw [h3] at h2
  have hpos : 0 < (S ⊓ K).relIndex S :=
    Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := (S ⊓ K).subgroupOf S))
  have key : (S ⊓ K).relIndex S * (S ⊓ K).relIndex K =
      (S ⊓ K).relIndex S * S.relIndex (S ⊔ K) := by
    rw [mul_comm ((S ⊓ K).relIndex S) ((S ⊓ K).relIndex K), h2, h1]
  exact Nat.eq_of_mul_eq_mul_left hpos key

private theorem sylowS_odd_borel_sup {G : Type} [Group G] [Finite G] {Li Lj S : Subgroup G}
    (h : Hyp111R Li Lj S) {T : Subgroup G} (hT : S ⊓ Li ≤ T)
    (hTN : borelOf Li S ≤ Subgroup.normalizer (T : Set G)) :
    ¬ 2 ∣ T.relIndex (borelOf Li S ⊔ T) := by
  have hB : IsSylowTwoOf (S ⊓ Li) (borelOf Li S) :=
    F7.isSylowTwoOf_mono_right h.hyp.h1.sylow (F1.sylow_le_borelOf Li S) (F1.borelOf_le Li S)
  rw [F1.relIndex_sup_eq_of_le_normalizer hTN, ← Subgroup.inf_relIndex_right T (borelOf Li S)]
  intro hd
  exact F7.isSylowTwoOf_odd_relIndex hB
    (hd.trans (Subgroup.relIndex_dvd_of_le_left (borelOf Li S)
      (le_inf hT (F1.sylow_le_borelOf Li S))))

private theorem sylowS_odd_sup {G : Type} [Group G] [Finite G] {B1 B2 T : Subgroup G}
    (hT1 : ¬ 2 ∣ T.relIndex (B1 ⊔ T)) (hT2 : ¬ 2 ∣ T.relIndex (B2 ⊔ T))
    (hN : B2 ≤ Subgroup.normalizer ((B1 ⊔ T : Subgroup G) : Set G))
    (hTN : T ≤ Subgroup.normalizer ((B1 ⊔ T : Subgroup G) : Set G))
    (hTK : T ≤ B1 ⊔ B2) : ¬ 2 ∣ T.relIndex (B1 ⊔ B2) := by
  have hN1K : B1 ⊔ T ≤ B1 ⊔ B2 := sup_le le_sup_left hTK
  have hK : B1 ⊔ B2 = (B2 ⊔ T) ⊔ (B1 ⊔ T) :=
    le_antisymm (sup_le (le_sup_left.trans le_sup_right) (le_sup_left.trans le_sup_left))
      (sup_le (sup_le le_sup_right hTK) hN1K)
  have idx1 : T.relIndex (B1 ⊔ B2) = T.relIndex (B1 ⊔ T) * (B1 ⊔ T).relIndex (B1 ⊔ B2) :=
    (Subgroup.relIndex_mul_relIndex T (B1 ⊔ T) (B1 ⊔ B2) le_sup_right hN1K).symm
  have idx2 : (B1 ⊔ T).relIndex (B1 ⊔ B2) = (B1 ⊔ T).relIndex (B2 ⊔ T) := by
    rw [hK]
    exact F1.relIndex_sup_eq_of_le_normalizer (sup_le hN hTN)
  have hTN12 : T ≤ (B1 ⊔ T) ⊓ (B2 ⊔ T) := le_inf le_sup_right le_sup_right
  have hdvd : (B1 ⊔ T).relIndex (B2 ⊔ T) ∣ T.relIndex (B2 ⊔ T) := by
    rw [← Subgroup.relIndex_mul_relIndex T ((B1 ⊔ T) ⊓ (B2 ⊔ T)) (B2 ⊔ T) hTN12 inf_le_right,
      Subgroup.inf_relIndex_right]
    exact dvd_mul_left _ _
  rw [idx1, idx2]
  intro hd
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hd with h1 | h1
  · exact hT1 h1
  · exact hT2 (h1.trans hdvd)

private theorem sylowS_sylow_sup {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}
    (h : Hyp111R L1 L2 S) :
    IsSylowTwoOf (S ⊓ L1 ⊔ S ⊓ L2) (borelOf L1 S ⊔ borelOf L2 S) := by
  have hBS := F1.bigB_le_normalizer_sylow h
  have hTS : S ⊓ L1 ⊔ S ⊓ L2 ≤ S := sup_le inf_le_left inf_le_left
  have hTB : S ⊓ L1 ⊔ S ⊓ L2 ≤ bigB L1 L2 S := hTS.trans (le_sup_right : S ≤ bigB L1 L2 S)
  have hTK : S ⊓ L1 ⊔ S ⊓ L2 ≤ borelOf L1 S ⊔ borelOf L2 S :=
    sup_le ((F1.sylow_le_borelOf L1 S).trans le_sup_left)
      ((F1.sylow_le_borelOf L2 S).trans le_sup_right)
  have hTN : bigB L1 L2 S ≤ Subgroup.normalizer ((S ⊓ L1 ⊔ S ⊓ L2 : Subgroup G) : Set G) :=
    F1.le_normalizer_sup hBS.1 hBS.2
  have hB1T : borelOf L1 S ≤ Subgroup.normalizer ((S ⊓ L1 ⊔ S ⊓ L2 : Subgroup G) : Set G) :=
    (le_sup_left.trans le_sup_left : borelOf L1 S ≤ bigB L1 L2 S).trans hTN
  have hB2T : borelOf L2 S ≤ Subgroup.normalizer ((S ⊓ L1 ⊔ S ⊓ L2 : Subgroup G) : Set G) :=
    (le_sup_right.trans le_sup_left : borelOf L2 S ≤ bigB L1 L2 S).trans hTN
  have hT1 : ¬ 2 ∣ (S ⊓ L1 ⊔ S ⊓ L2).relIndex (borelOf L1 S ⊔ (S ⊓ L1 ⊔ S ⊓ L2)) :=
    sylowS_odd_borel_sup h (le_sup_left : S ⊓ L1 ≤ S ⊓ L1 ⊔ S ⊓ L2) hB1T
  have hT2 : ¬ 2 ∣ (S ⊓ L1 ⊔ S ⊓ L2).relIndex (borelOf L2 S ⊔ (S ⊓ L1 ⊔ S ⊓ L2)) :=
    sylowS_odd_borel_sup h.symm (le_sup_right : S ⊓ L2 ≤ S ⊓ L1 ⊔ S ⊓ L2) hB2T
  have hN : borelOf L2 S ≤ Subgroup.normalizer
      ((borelOf L1 S ⊔ (S ⊓ L1 ⊔ S ⊓ L2) : Subgroup G) : Set G) :=
    F1.le_normalizer_sup (F1.borelOf_le_normalizer_borelOf h) hB2T
  have hTN' : S ⊓ L1 ⊔ S ⊓ L2 ≤ Subgroup.normalizer
      ((borelOf L1 S ⊔ (S ⊓ L1 ⊔ S ⊓ L2) : Subgroup G) : Set G) :=
    F1.le_normalizer_sup (hTB.trans (F1.bigB_le_normalizer_borelOf h).1) Subgroup.le_normalizer
  exact F7.isSylowTwoOf_of_relIndex hTK (h.hyp.h1.pgroup.to_le hTS)
    (sylowS_odd_sup hT1 hT2 hN hTN' hTK)

private theorem sylowS_bigB {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}
    (h : Hyp111R L1 L2 S) : IsSylowTwoOf S (bigB L1 L2 S) := by
  have hSK : S ≤ Subgroup.normalizer ((borelOf L1 S ⊔ borelOf L2 S : Subgroup G) : Set G) :=
    F1.le_normalizer_sup (F1.le_normalizer_borelOf h.hyp.h1.normalizes)
      (F1.le_normalizer_borelOf h.hyp.h2.normalizes)
  have hTK := (sylowS_sylow_sup h).1
  have hTS : S ⊓ L1 ⊔ S ⊓ L2 ≤ S := sup_le inf_le_left inf_le_left
  have hodd : ¬ 2 ∣ S.relIndex (bigB L1 L2 S) := by
    have hBSK : bigB L1 L2 S = S ⊔ (borelOf L1 S ⊔ borelOf L2 S) := by
      unfold bigB
      exact sup_comm _ _
    rw [hBSK, ← sylowS_relIndex_inf hSK]
    intro hd
    exact F7.isSylowTwoOf_odd_relIndex (sylowS_sylow_sup h)
      (hd.trans (Subgroup.relIndex_dvd_of_le_left (borelOf L1 S ⊔ borelOf L2 S)
        (le_inf hTS hTK)))
  exact F7.isSylowTwoOf_of_relIndex (le_sup_right : S ≤ bigB L1 L2 S) h.hyp.h1.pgroup hodd

theorem leafSylowS : LeafSylowS := by
  intro G _ _ L1 L2 S h
  have hB : IsSylowTwoOf S (bigB L1 L2 S) := sylowS_bigB h
  have hBN1 : bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) :=
    (F1.bigB_le_normalizer_left h).1
  have hinf : bigB L1 L2 S ⊓ L1 = borelOf L1 S := by
    rw [inf_comm]
    exact F1.inf_bigB_eq_borelOf h
  have hBL : (bigB L1 L2 S).relIndex (L1 ⊔ bigB L1 L2 S) = (borelOf L1 S).relIndex L1 := by
    rw [sup_comm, ← hinf, sylowS_relIndex_inf hBN1]
  have hodd1 : ¬ 2 ∣ (borelOf L1 S).relIndex L1 := fun hd =>
    F7.isSylowTwoOf_odd_relIndex h.hyp.h1.sylow
      (hd.trans (Subgroup.relIndex_dvd_of_le_left L1 (F1.sylow_le_borelOf L1 S)))
  have hS_B : S ≤ bigB L1 L2 S := hB.1
  have hP : IsSylowTwoOf S (L1 ⊔ bigB L1 L2 S) := by
    refine F7.isSylowTwoOf_of_relIndex (hS_B.trans le_sup_right) h.hyp.h1.pgroup ?_
    rw [← Subgroup.relIndex_mul_relIndex S (bigB L1 L2 S) (L1 ⊔ bigB L1 L2 S) hS_B le_sup_right,
      hBL]
    intro hd
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hd with h1 | h1
    · exact F7.isSylowTwoOf_odd_relIndex hB h1
    · exact hodd1 h1
  have hQ : pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ≤ S := by
    have hQB : pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ≤ bigB L1 L2 S :=
      F1.pCoreOf_parabolic_le_bigB h
    have hBN : bigB L1 L2 S ≤ Subgroup.normalizer (pCoreOf 2 (L1 ⊔ bigB L1 L2 S) : Set G) :=
      (le_sup_right : bigB L1 L2 S ≤ L1 ⊔ bigB L1 L2 S).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
    exact (CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer hQB hBN
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)).trans (F7.isSylowTwoOf_pCoreOf_le hB)
  exact ⟨hB, hP, hQ⟩

end CFSG.GH74.QTGen4.DSGen4
