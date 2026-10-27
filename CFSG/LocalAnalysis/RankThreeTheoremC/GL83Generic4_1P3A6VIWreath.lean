module

public import CFSG.RankThree.PartTwo.KFacts.K73Recognition
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6VITools

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.ABGLocalTools Subgroup
open CFSG.RankThree.PartTwo.KFacts (WreathData eConj eBase)

variable {G : Type} [Group G]

theorem a6vi_mem_normalizer_of_map_eq {A : Subgroup G} {g : G}
    (h : A.map (MulAut.conj g).toMonoidHom = A) : g ∈ normalizer (A : Set G) := by
  rw [mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    rw [← h]
    exact ⟨w, hw, rfl⟩
  · intro hw
    rw [← h] at hw
    obtain ⟨w', hw', hww'⟩ := hw
    have : w' = w := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hww'
      exact mul_left_cancel (mul_right_cancel hww')
    rwa [← this]

variable [Finite G]

theorem a6vi_inf_eq_bot_of_ne {a b : G} (ha : Nat.card (zpowers a) = 3)
    (hb : Nat.card (zpowers b) = 3) (hne : zpowers a ≠ zpowers b) :
    zpowers a ⊓ zpowers b = ⊥ := by
  have hdvd : Nat.card (zpowers a ⊓ zpowers b : Subgroup G) ∣ 3 := by
    rw [← ha]; exact Subgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · exfalso
    apply hne
    have h1 : zpowers a ⊓ zpowers b = zpowers a :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [ha, h3])
    have h2 : zpowers a ⊓ zpowers b = zpowers b :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hb, h3])
    rw [← h1, h2]

theorem a6vi_mem_of_mem_normalizer {Q : Subgroup G} {x u : G}
    (hQsyl : IsSylowOf 3 Q (centralizer ({x} : Set G))) {e : ℕ} (hu : u ^ (3 ^ e) = 1)
    (huN : u ∈ normalizer (Q : Set G)) (huC : u ∈ centralizer ({x} : Set G)) : u ∈ Q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hVp : IsPGroup 3 ↥(Q ⊔ zpowers u) :=
    hQsyl.isPGroup.to_sup_of_normal_left' (a6vi_isPGroup_zpowers hu) (zpowers_le.mpr huN)
  have hV : Q ⊔ zpowers u = Q :=
    hQsyl.eq_of_le le_sup_left (sup_le hQsyl.le (zpowers_le.mpr huC)) hVp
  rw [← hV]
  exact mem_sup_right (mem_zpowers _)

theorem a6vi_eq_eBase_of_abelian {x t : G} (hW : WreathData x t)
    (hz3 : (eConj x t 0 * eConj x t 1 * eConj x t 2) ^ 3 = 1) {A : Subgroup G}
    (hAR : A ≤ closure ({x, t} : Set G)) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hA : Nat.card A = 27) : A = eBase x t := by
  by_contra hne
  have hnle : ¬ A ≤ eBase x t := fun hle =>
    hne (Subgroup.eq_of_le_of_card_ge hle (by rw [hW.card_eBase, hA]))
  obtain ⟨a, haA, haE⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
  have hle : eBase x t ⊓ A ≤ eBase x t ⊓ centralizer ({a} : Set G) := fun b hb =>
    Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hb).1,
      mem_centralizer_singleton_iff.mpr (hAc b (Subgroup.mem_inf.mp hb).2 a haA)⟩
  rw [hW.eBase_inf_centralizer (hAR haA) haE] at hle
  have hz : Nat.card (eBase x t ⊓ A : Subgroup G) ≤ 3 :=
    (Subgroup.card_le_of_le hle).trans
      (by rw [Nat.card_zpowers]; exact orderOf_le_of_pow_eq_one (by norm_num) hz3)
  have hidx : (eBase x t).relIndex (closure ({x, t} : Set G)) = 3 := by
    have h := Subgroup.relIndex_mul_card (eBase x t) (closure ({x, t} : Set G))
    rw [inf_eq_left.mpr hW.eBase_le, hW.card_closure, hW.card_eBase] at h
    omega
  have hidxA : (eBase x t).relIndex A ≤ 3 := by
    have h := Subgroup.relIndex_le_of_le_right (H := eBase x t) hAR (by rw [hidx]; norm_num)
    rwa [hidx] at h
  have hcardA := Subgroup.relIndex_mul_card (eBase x t) A
  rw [hA] at hcardA
  have := Nat.mul_le_mul hidxA hz
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC
