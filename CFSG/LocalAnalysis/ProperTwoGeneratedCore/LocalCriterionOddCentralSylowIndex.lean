module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionOddCentralSylow

public section

namespace CFSG.ProperTwoGeneratedCore

variable {K : Type*} [Group K] [Finite K]

theorem sylow_fixed_intersection_relIndex_prime_part
    (p : ℕ) (hp : p.Prime) (B : Subgroup K) (t : K) (P : Sylow p B)
    (R : Sylow p (B ⊓ Subgroup.centralizer ({t} : Set K) : Subgroup K))
    (hRimage : (R : Subgroup (B ⊓ Subgroup.centralizer ({t} : Set K) : Subgroup K)).map
      (B ⊓ Subgroup.centralizer ({t} : Set K)).subtype =
        (P : Subgroup B).map B.subtype ⊓ Subgroup.centralizer ({t} : Set K)) :
    (Subgroup.centralizer ({t} : Set K)).relIndex ((P : Subgroup B).map B.subtype) =
      p ^ ((Subgroup.centralizer ({t} : Set K)).relIndex B).factorization p := by
  let : Fact p.Prime := ⟨hp⟩
  let C := Subgroup.centralizer ({t} : Set K)
  let U := (P : Subgroup B).map B.subtype
  have hUcard : Nat.card U = p ^ (Nat.card B).factorization p := by
    rw [Subgroup.card_map_of_injective B.subtype_injective, P.card_eq_multiplicity]
  have hfixedcard : Nat.card (U ⊓ C : Subgroup K) =
      p ^ (Nat.card (B ⊓ C : Subgroup K)).factorization p := by
    rw [← hRimage, Subgroup.card_map_of_injective
      (B ⊓ C : Subgroup K).subtype_injective, R.card_eq_multiplicity]
  have hinternalU : Nat.card (C.subgroupOf U) = Nat.card (U ⊓ C : Subgroup K) := by
    rw [← Subgroup.card_map_of_injective U.subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_comm]
  have hinternalB : Nat.card (C.subgroupOf B) = Nat.card (B ⊓ C : Subgroup K) := by
    rw [← Subgroup.card_map_of_injective B.subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_comm]
  have hdiv : Nat.card (B ⊓ C : Subgroup K) ∣ Nat.card B :=
    Subgroup.card_dvd_of_le inf_le_left
  have hfacLe : (Nat.card (B ⊓ C : Subgroup K)).factorization p ≤
      (Nat.card B).factorization p :=
    Nat.factorization_le_factorization_of_dvd_right hdiv Nat.card_pos.ne' Nat.card_pos.ne'
  have hidxB : C.relIndex B = Nat.card B / Nat.card (B ⊓ C : Subgroup K) := by
    change (C.subgroupOf B).index = _
    rw [Subgroup.index_eq_card_div, hinternalB]
  have hidxU : C.relIndex U = Nat.card U / Nat.card (U ⊓ C : Subgroup K) := by
    change (C.subgroupOf U).index = _
    rw [Subgroup.index_eq_card_div, hinternalU]
  have hfacIndex : (C.relIndex B).factorization p =
      (Nat.card B).factorization p - (Nat.card (B ⊓ C : Subgroup K)).factorization p := by
    rw [hidxB, Nat.factorization_div hdiv, Finsupp.tsub_apply]
  change C.relIndex U = p ^ (C.relIndex B).factorization p
  rw [hidxU, hUcard, hfixedcard, hfacIndex]
  exact Nat.pow_div hfacLe hp.pos

theorem odd_central_quotient_invariant_sylow_index
    (p : ℕ) (hp : p.Prime) (B J : Subgroup K) [J.Normal]
    (t : K) (ht : orderOf t = 2) (hJodd : Odd (Nat.card J)) (hJB : J ≤ B)
    (hcentral : QuotientGroup.mk' J t ∈ Subgroup.center (K ⧸ J))
    (P : Sylow p B)
    (hPnorm : t ∈ Subgroup.normalizer
      (((P : Subgroup B).map B.subtype : Subgroup K) : Set K)) :
    (Subgroup.centralizer ({t} : Set K)).relIndex ((P : Subgroup B).map B.subtype) =
      p ^ ((Subgroup.centralizer ({t} : Set K)).relIndex B).factorization p := by
  obtain ⟨R, hRimage⟩ := odd_central_quotient_invariant_sylow_fixed
    p hp B J t ht hJodd hJB hcentral P hPnorm
  exact sylow_fixed_intersection_relIndex_prime_part p hp B t P R hRimage

omit [Finite K] in
theorem sylow_involution_invariant_iff_ambient_conjugate_eq
    (p : ℕ) (B : Subgroup K) (t : K) (P : Sylow p B) :
    t ∈ Subgroup.normalizer (((P : Subgroup B).map B.subtype : Subgroup K) : Set K) ↔
      ((P : Subgroup B).map B.subtype).map (MulAut.conj t).toMonoidHom =
        (P : Subgroup B).map B.subtype :=
  Subgroup.mem_normalizer_iff_map_conj_eq

theorem odd_central_quotient_involution_invariant_sylows
    (B J : Subgroup K) [B.Normal] [J.Normal] (t : K) (ht : orderOf t = 2)
    (_hgenerated : B ⊔ Subgroup.zpowers t = ⊤)
    (hJodd : Odd (Nat.card J)) (hJB : J ≤ B)
    (hcentral : QuotientGroup.mk' J t ∈ Subgroup.center (K ⧸ J)) :
    (B ⊓ Subgroup.centralizer ({t} : Set K)) ⊔ J = B ∧
    (∀ b ∈ B, ∃ c ∈ B ⊓ Subgroup.centralizer ({t} : Set K), ∃ j ∈ J, c * j = b) ∧
    ∀ p : ℕ, p.Prime →
      (∃ P : Sylow p B,
        ((P : Subgroup B).map B.subtype).map (MulAut.conj t).toMonoidHom =
          (P : Subgroup B).map B.subtype) ∧
      ∀ P : Sylow p B,
        ((P : Subgroup B).map B.subtype).map (MulAut.conj t).toMonoidHom =
          (P : Subgroup B).map B.subtype →
        (∃ R : Sylow p (B ⊓ Subgroup.centralizer ({t} : Set K) : Subgroup K),
          (R : Subgroup (B ⊓ Subgroup.centralizer ({t} : Set K) : Subgroup K)).map
            (B ⊓ Subgroup.centralizer ({t} : Set K)).subtype =
              (P : Subgroup B).map B.subtype ⊓ Subgroup.centralizer ({t} : Set K)) ∧
        (Subgroup.centralizer ({t} : Set K)).relIndex ((P : Subgroup B).map B.subtype) =
          p ^ ((Subgroup.centralizer ({t} : Set K)).relIndex B).factorization p := by
  refine ⟨odd_central_quotient_subgroup_sup J B t ht hJodd hJB hcentral,
    odd_central_quotient_subgroup_factorization J B t ht hJodd hJB hcentral, ?_⟩
  intro p hp
  constructor
  · obtain ⟨P, hP⟩ := odd_central_quotient_invariant_sylow_exists
      p hp B J t ht hJodd hJB hcentral
    exact ⟨P, (sylow_involution_invariant_iff_ambient_conjugate_eq p B t P).mp hP⟩
  · intro P hP
    have hnorm := (sylow_involution_invariant_iff_ambient_conjugate_eq p B t P).mpr hP
    exact ⟨odd_central_quotient_invariant_sylow_fixed p hp B J t ht hJodd hJB hcentral P hnorm,
      odd_central_quotient_invariant_sylow_index p hp B J t ht hJodd hJB hcentral P hnorm⟩

end CFSG.ProperTwoGeneratedCore
