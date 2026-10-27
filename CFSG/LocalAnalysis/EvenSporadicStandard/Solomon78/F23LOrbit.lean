module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.F23LCentral
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.F23LHW
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Open

section Orbit

variable {G : Type} [Group G] {L WL : Subgroup G} {t u : G}

theorem comm_of_isElemAbelian {p : ℕ} {E : Subgroup G} (h : IsElemAbelian p E) {a b : G}
    (ha : a ∈ E) (hb : b ∈ E) : a * b = b * a := CFSG.Open.IsElemAbelian.comm h ha hb

@[expose] def conjSetIn (L WL : Subgroup G) (u : G) : Set G :=
  {x | x ∈ WL ∧ ∃ l ∈ L, x = l * u * l⁻¹}

theorem orbit_eq (hs : Setting612 G L t) (hW : WSupHyp L WL t) (hab : IsElemAbelian 2 WL)
    (hfus : ∀ a ∈ L, orderOf a = 2 → IsConj t (t * a) → ∃ l ∈ L, a = l * u * l⁻¹)
    (hm : ∃ m ∈ normalizer ((WL ⊔ zpowers t : Subgroup G) : Set G), m * t * m⁻¹ = t * u)
    (htrans : ∀ p : G, p ∈ WL → (∃ l ∈ L, p = l * u * l⁻¹) →
      ∃ n ∈ normalizer (WL : Set G) ⊓ L, n * u * n⁻¹ = p)
    (hC : centralizer ({t} : Set G) = L ⊔ zpowers t) :
    {x : G | ∃ n ∈ normalizer ((WL ⊔ zpowers t : Subgroup G) : Set G), x = n * t * n⁻¹} =
      {t} ∪ (fun p => t * p) '' conjSetIn L WL u := by
  set W : Subgroup G := WL ⊔ zpowers t with hWdef
  have htW : t ∈ W := mem_sup_right (mem_zpowers t)
  have hWab : IsElemAbelian 2 W := hW.isElemAbelian hab
  ext x
  constructor
  · rintro ⟨n, hn, rfl⟩
    have hxW : n * t * n⁻¹ ∈ W := (mem_normalizer_iff.1 hn t).1 htW
    have hxc : n * t * n⁻¹ ∈ centralizer ({t} : Set G) :=
      mem_centralizer_singleton_iff.2 (comm_of_isElemAbelian hWab hxW htW)
    obtain ⟨a, ha, hxa⟩ := hs.exists_eq_mul hxc
    rcases hxa with hxa | hxa
    · exact absurd (hxa ▸ ha) (hs.conj_not_mem n)
    · by_cases ha1 : a = 1
      · left
        rw [hxa, ha1, one_mul]
        rfl
      · right
        have hxx : (n * t * n⁻¹) * (n * t * n⁻¹) = 1 := by
          calc (n * t * n⁻¹) * (n * t * n⁻¹) = n * (t * t) * n⁻¹ := by group
            _ = 1 := by rw [hs.t_sq]; group
        have hc : t * a = a * t := (hs.comm_of_mem ha).symm
        have haa : a * a = 1 := by
          have h1 : (a * t) * (a * t) = 1 := hxa ▸ hxx
          calc a * a = a * a * (t * t) := by rw [hs.t_sq, mul_one]
            _ = a * (a * t) * t := by simp only [mul_assoc]
            _ = a * (t * a) * t := by rw [hc]
            _ = (a * t) * (a * t) := by simp only [mul_assoc]
            _ = 1 := h1
        have ha2 : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact haa) ha1
        have hconj : IsConj t (t * a) := by
          have h1 : IsConj t (n * t * n⁻¹) := isConj_iff.2 ⟨n, rfl⟩
          rwa [hxa, ← hc] at h1
        obtain ⟨l, hl, hal⟩ := hfus a ha ha2 hconj
        have haW : a ∈ W := by
          have : a = (n * t * n⁻¹) * t := by rw [hxa, mul_assoc, hs.t_sq, mul_one]
          rw [this]
          exact W.mul_mem hxW htW
        have haWL : a ∈ WL := by
          have := hW.sup_inf_left
          rw [← this]
          exact ⟨haW, ha⟩
        refine ⟨a, ⟨haWL, l, hl, hal⟩, ?_⟩
        show t * a = n * t * n⁻¹
        rw [hxa, hc]
  · rintro (rfl | ⟨p, ⟨hpWL, l, hl, hp⟩, rfl⟩)
    · exact ⟨1, one_mem _, by simp⟩
    · obtain ⟨n, hnN, hnu⟩ := htrans p hpWL ⟨l, hl, hp⟩
      obtain ⟨m, hm, hmt⟩ := hm
      have hnN' : n ∈ normalizer (W : Set G) := by
        have h6 := hW.normalizer_inf_centralizer hC
        have : n ∈ (normalizer (WL : Set G) ⊓ L) ⊔ zpowers t := Subgroup.mem_sup_left hnN
        rw [← h6] at this
        exact this.1
      refine ⟨n * m, mul_mem hnN' hm, ?_⟩
      have hnt : n * t = t * n := hs.comm_of_mem hnN.2
      calc t * p = t * (n * u * n⁻¹) := by rw [hnu]
        _ = (t * n) * u * n⁻¹ := by simp only [mul_assoc]
        _ = (n * t) * u * n⁻¹ := by rw [hnt]
        _ = n * (t * u) * n⁻¹ := by simp only [mul_assoc]
        _ = n * (m * t * m⁻¹) * n⁻¹ := by rw [hmt]
        _ = (n * m) * t * (n * m)⁻¹ := by group

theorem ncard_orbit [Finite G] (hs : Setting612 G L t) (hW : WSupHyp L WL t)
    (hab : IsElemAbelian 2 WL) (hu2 : orderOf u = 2)
    (hfus : ∀ a ∈ L, orderOf a = 2 → IsConj t (t * a) → ∃ l ∈ L, a = l * u * l⁻¹)
    (hm : ∃ m ∈ normalizer ((WL ⊔ zpowers t : Subgroup G) : Set G), m * t * m⁻¹ = t * u)
    (htrans : ∀ p : G, p ∈ WL → (∃ l ∈ L, p = l * u * l⁻¹) →
      ∃ n ∈ normalizer (WL : Set G) ⊓ L, n * u * n⁻¹ = p)
    (hC : centralizer ({t} : Set G) = L ⊔ zpowers t) (hP : (conjSetIn L WL u).ncard = 23) :
    Set.ncard {x : G | ∃ n ∈ normalizer ((WL ⊔ zpowers t : Subgroup G) : Set G),
      x = n * t * n⁻¹} = 24 := by
  rw [orbit_eq hs hW hab hfus hm htrans hC]
  have hdisj : Disjoint ({t} : Set G) ((fun p => t * p) '' conjSetIn L WL u) := by
    rw [Set.disjoint_singleton_left]
    rintro ⟨p, ⟨_, l, _, hp⟩, hpt⟩
    have hp1 : p = 1 := by simpa using hpt
    rw [hp1] at hp
    have hu1 : u = 1 := by
      calc u = l⁻¹ * (l * u * l⁻¹) * l := by group
        _ = l⁻¹ * 1 * l := by rw [← hp]
        _ = 1 := by group
    exact ne_one_of_orderOf_eq_two hu2 hu1
  rw [Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), Set.ncard_singleton,
    Set.ncard_image_of_injective _ (mul_right_injective t), hP]

end Orbit

end CFSG.EvenSporadicStandard.Solomon78
