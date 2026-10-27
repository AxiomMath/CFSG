module

public import CFSG.CGT.PushingUpLit.LIT.Foote.GroupAux
public import CFSG.Foundations.Basic
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc

open Subgroup
open scoped commutatorElement

theorem map_eq_one_of_isPerfect_of_commute {P Γ : Type*} [Group P] [Group Γ] [Group.IsPerfect P]
    (f : P →* Γ) (hf : ∀ x y : P, f x * f y = f y * f x) (x : P) : f x = 1 := by
  have hker : commutator P ≤ f.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hf a b
  exact MonoidHom.mem_ker.mp (hker (Group.IsPerfect.mem_commutator (g := x)))

theorem card_le_two_mul_card_of_inv_mul_mem {G : Type*} [Group G] [Finite G] {S N : Subgroup G}
    (hNS : N ≤ S) (h : ∀ a ∈ S, ∀ b ∈ S, a ∉ N → b ∉ N → a⁻¹ * b ∈ N) :
    Nat.card S ≤ 2 * Nat.card N := by
  by_cases hSN : S ≤ N
  · have hcard : Nat.card S ≤ Nat.card N := Subgroup.card_le_of_le hSN
    omega
  · obtain ⟨g, hgS, hgN⟩ := Set.not_subset.mp hSN
    have hrel : N.relIndex S = 2 := by
      refine Subgroup.relIndex_eq_two_iff_exists_notMem_and'.mpr
        ⟨g⁻¹, S.inv_mem hgS, fun hg => hgN (by simpa using N.inv_mem hg), fun b hb => ?_⟩
      by_cases hbN : b ∈ N
      · exact Or.inr hbN
      · exact Or.inl (by simpa using h g hgS b hb hgN hbN)
    have hcard := Subgroup.relIndex_mul_card N S
    rw [hrel, inf_of_le_left hNS] at hcard
    omega

theorem four_le_relIndex_center_sylow {B : Type*} [Group B] [Finite B]
    (hB : CFSG.IsQuasisimple B) (Q : Sylow 2 B) : 4 ≤ (center B).relIndex (Q : Subgroup B) := by
  classical
  haveI : Group.IsPerfect B := hB.1
  haveI : Nontrivial (B ⧸ center B) := by
    obtain ⟨a, b, hab⟩ := hB.2.2
    exact nontrivial_of_ne (a * b) (b * a) hab
  haveI : Finite (B ⧸ center B) :=
    ((finite_iff_subgroup_quotient (center B)).mp ‹Finite B›).2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let pi : B →* B ⧸ center B := QuotientGroup.mk' (center B)
  have hpi : Function.Surjective pi := QuotientGroup.mk'_surjective (center B)
  let Q' : Sylow 2 (B ⧸ center B) := Sylow.mapSurjective hpi Q
  have hcoe : (Q' : Subgroup (B ⧸ center B)) = (Q : Subgroup B).map pi := rfl
  have hker : pi.ker = center B := QuotientGroup.ker_mk' (center B)
  have h4 : 4 ∣ Nat.card (B ⧸ center B) :=
    CFSG.CGT.PushingUpLit.LIT.Foote.four_dvd_card_of_perfect
  have h2 : 2 ≤ (Nat.card (B ⧸ center B)).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two
      (Nat.card_pos (α := B ⧸ center B)).ne').mp (by simpa using h4)
  have hcard : Nat.card ((Q : Subgroup B).map pi) =
      2 ^ (Nat.card (B ⧸ center B)).factorization 2 := by
    rw [← hcoe]
    exact Sylow.card_eq_multiplicity Q'
  have hrel : (center B).relIndex (Q : Subgroup B) = Nat.card ((Q : Subgroup B).map pi) := by
    conv_lhs => rw [← hker]
    exact Subgroup.relIndex_ker (f := pi) (K := (Q : Subgroup B))
  calc
    4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (Nat.card (B ⧸ center B)).factorization 2 :=
        Nat.pow_le_pow_right (by norm_num) h2
    _ = Nat.card ((Q : Subgroup B).map pi) := hcard.symm
    _ = (center B).relIndex (Q : Subgroup B) := hrel.symm

variable {G : Type*} [Group G] [Finite G]

private theorem relIndex_ne_zero_of_finite (H K : Subgroup G) : H.relIndex K ≠ 0 := by
  intro h
  have hd := Subgroup.relIndex_dvd_card (H := H) (K := K)
  rw [h] at hd
  exact (Nat.card_pos (α := K)).ne' (Nat.eq_zero_of_zero_dvd hd)

theorem four_mul_card_le_of_isQuasisimple {A B C : Subgroup G}
    (hB : CFSG.IsQuasisimple ↥B) (hBA : ∀ b ∈ B, ∀ a ∈ A, b * a = a * b) (hC : IsPGroup 2 C)
    (hCA : ∀ c ∈ C, ∀ a ∈ A, c * a = a * c) (hCB : ∀ c ∈ C, ∀ b ∈ B, c * b = b * c) :
    4 * Nat.card C ≤ 2 ^ (Nat.card (centralizer (A : Set G))).factorization 2 := by
  classical
  let Q' : Sylow 2 ↥B := default
  let Q : Subgroup G := (Q' : Subgroup ↥B).map B.subtype
  let R : Subgroup G := Q ⊔ C
  let Z : Subgroup G := (center ↥B).map B.subtype
  let cA : Subgroup G := centralizer (A : Set G)
  have hQ2 : IsPGroup 2 Q := (Q'.isPGroup').map B.subtype
  have hQ_le_cent : Q ≤ centralizer (C : Set G) := by
    show (Q' : Subgroup ↥B).map B.subtype ≤ centralizer (C : Set G)
    rw [Subgroup.map_le_iff_le_comap]
    intro b hb
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro c hc
    exact hCB c hc (b : G) b.2
  have hQ_le_norm : Q ≤ normalizer C :=
    hQ_le_cent.trans (Subgroup.centralizer_le_normalizer (C : Set G))
  have hR2 : IsPGroup 2 R := hQ2.to_sup_of_normal_right' hC hQ_le_norm
  have hQ_le_cA : Q ≤ cA := by
    show (Q' : Subgroup ↥B).map B.subtype ≤ centralizer (A : Set G)
    rw [Subgroup.map_le_iff_le_comap]
    intro b hb
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro a ha
    exact (hBA (b : G) b.2 a ha).symm
  have hC_le_cA : C ≤ cA := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (hCA c hc a ha).symm
  have hR_le_cA : R ≤ cA := sup_le hQ_le_cA hC_le_cA
  have hCQ_le_Z : C ⊓ Q ≤ Z := by
    intro x hx
    obtain ⟨hxC, hxQ⟩ := hx
    rcases hxQ with ⟨b, _hbQ, rfl⟩
    rw [Subgroup.mem_map_iff_mem (Subgroup.subtype_injective B)]
    rw [Subgroup.mem_center_iff]
    intro y
    refine Subgroup.subtype_injective B ?_
    rw [map_mul, map_mul]
    exact (hCB (B.subtype b) hxC (y : G) y.2).symm
  have hZQ : Z.relIndex Q = (center ↥B).relIndex (Q' : Subgroup ↥B) :=
    Subgroup.relIndex_map_map_of_injective (center ↥B) (Q' : Subgroup ↥B)
      (Subgroup.subtype_injective B)
  have h4Z : 4 ≤ Z.relIndex Q := by
    rw [hZQ]
    exact four_le_relIndex_center_sylow hB Q'
  have hZ_le : Z.relIndex Q ≤ (C ⊓ Q).relIndex Q :=
    Subgroup.relIndex_le_of_le_left (H := C ⊓ Q) (K := Z) (L := Q) hCQ_le_Z
      (relIndex_ne_zero_of_finite (C ⊓ Q) Q)
  have hinf : (C ⊓ Q).relIndex Q = C.relIndex Q :=
    Subgroup.inf_relIndex_right (H := C) (K := Q)
  have hQ_le_R : Q ≤ R := le_sup_left
  have hCQ_le_CR : C.relIndex Q ≤ C.relIndex R :=
    Subgroup.relIndex_le_of_le_right (H := C) (K := Q) (L := R) hQ_le_R
      (relIndex_ne_zero_of_finite C R)
  have h4_CR : 4 ≤ C.relIndex R := by
    calc 4 ≤ Z.relIndex Q := h4Z
      _ ≤ (C ⊓ Q).relIndex Q := hZ_le
      _ = C.relIndex Q := hinf
      _ ≤ C.relIndex R := hCQ_le_CR
  have hcard_dvd : Nat.card R ∣ Nat.card cA := Subgroup.card_dvd_of_le hR_le_cA
  obtain ⟨k, hk⟩ := hR2.exists_card_eq
  have hk_le : k ≤ (Nat.card cA).factorization 2 :=
    (Nat.prime_two.pow_dvd_iff_le_factorization (Nat.card_pos (α := cA)).ne').mp
      (hk ▸ hcard_dvd)
  have hcard_bound : Nat.card R ≤ 2 ^ (Nat.card cA).factorization 2 := by
    rw [hk]
    exact Nat.pow_le_pow_right (by norm_num) hk_le
  have hC_le_R : C ≤ R := le_sup_right
  have hcardR : C.relIndex R * Nat.card C = Nat.card R := by
    have h := Subgroup.relIndex_mul_card (H := C) (K := R)
    rwa [inf_eq_left.mpr hC_le_R] at h
  calc 4 * Nat.card C ≤ C.relIndex R * Nat.card C := Nat.mul_le_mul_right _ h4_CR
    _ = Nat.card R := hcardR
    _ ≤ 2 ^ (Nat.card cA).factorization 2 := hcard_bound

theorem exists_isPGroup_card_eq {H T : Subgroup G} (hT : IsPGroup 2 T) (hTH : T ≤ H) :
    ∃ S : Subgroup G, T ≤ S ∧ S ≤ H ∧ IsPGroup 2 S ∧
      Nat.card S = 2 ^ (Nat.card H).factorization 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT' : IsPGroup 2 (T.subgroupOf H) :=
    hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm
  obtain ⟨Q, hTQ⟩ := hT'.exists_le_sylow
  refine ⟨(Q : Subgroup ↥H).map H.subtype, ?_,
    Subgroup.map_subtype_le (K := (Q : Subgroup ↥H)), ?_, ?_⟩
  · rintro t ht
    exact ⟨⟨t, hTH ht⟩, hTQ (by rw [Subgroup.mem_subgroupOf]; exact ht), rfl⟩
  · exact Q.isPGroup'.of_equiv
      (Subgroup.equivMapOfInjective (Q : Subgroup ↥H) H.subtype H.subtype_injective)
  · rw [Subgroup.card_map_of_injective H.subtype_injective, Sylow.card_eq_multiplicity Q]

end CFSG.EvenSporadicStandard.M12Std.Rbc
