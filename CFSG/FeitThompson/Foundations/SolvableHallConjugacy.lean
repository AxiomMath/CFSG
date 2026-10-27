module

public import CFSG.FeitThompson.Foundations.HallImageQuotient
public import CFSG.FeitThompson.Foundations.SolvableGroupElemAbelianMinNormal
public import CFSG.FeitThompson.Foundations.CoprimeAbelianComplementsConjugate
public import CFSG.FeitThompson.Foundations.QuotientOrderByNormal
public import CFSG.FeitThompson.Foundations.SylowContainmentConjugacy
public import CFSG.FeitThompson.Foundations.PiSubgroupInHallSolvable
import CFSG.FeitThompson.Foundations.SolvableHallExistence

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Pointwise

universe u

variable {G G' : Type*} [Group G] [Group G'] {π : Set ℕ}

private theorem conj_smul_eq_map_conj (g : G) (H : Subgroup G) :
    MulAut.conj g • H = H.map (MulAut.conj g : G →* G) := by
  rw [Subgroup.pointwise_smul_def]
  rfl

private theorem map_conj_smul (f : G →* G') (g : G) (H : Subgroup G) :
    (MulAut.conj g • H).map f = MulAut.conj (f g) • H.map f := by
  rw [conj_smul_eq_map_conj, conj_smul_eq_map_conj, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext y
  simp [MulAut.conj_apply]

theorem index_conj_smul (g : G) (H : Subgroup G) :
    (MulAut.conj g • H : Subgroup G).index = H.index := by
  rw [conj_smul_eq_map_conj]
  exact Subgroup.index_map_equiv H (MulAut.conj g)

theorem isPiNumber_prime_pow_iff {p d : ℕ} (hp : p.Prime) (hd : d ≠ 0) :
    IsPiNumber π (p ^ d) ↔ p ∈ π := by
  rw [isPiNumber_iff]
  simp [Nat.primeFactors_pow _ hd, hp.primeFactors]

theorem inf_eq_bot_of_isPiNumber [Finite G] {H N : Subgroup G}
    (hH : IsPiNumber π (Nat.card H)) (hN : IsPiNumber πᶜ (Nat.card N)) : H ⊓ N = ⊥ := by
  rw [← Subgroup.card_eq_one]
  exact (hH.of_dvd (Subgroup.card_dvd_of_le inf_le_left) Nat.card_pos.ne').eq_one_of_compl
    (hN.of_dvd (Subgroup.card_dvd_of_le inf_le_right) Nat.card_pos.ne') Nat.card_pos.ne'

private theorem inf_subgroupOf (A B L : Subgroup G) :
    (A ⊓ B).subgroupOf L = A.subgroupOf L ⊓ B.subgroupOf L := by
  ext x
  simp [Subgroup.mem_subgroupOf]

private theorem natCard_subgroupOf {H L : Subgroup G} (h : H ≤ L) :
    Nat.card (H.subgroupOf L) = Nat.card H :=
  Nat.card_eq_of_bijective _ (Subgroup.subgroupOfEquivOfLe h).bijective

private theorem exists_conj_smul_eq_of_isHallSubgroup_aux :
    ∀ (n : ℕ) {G : Type u} [Group G] [Finite G] [Group.IsSolvable G] {π : Set ℕ}
      {H K : Subgroup G}, Nat.card G ≤ n → IsHallSubgroup π H → IsHallSubgroup π K →
      ∃ g : G, MulAut.conj g • H = K := by
  intro n
  induction n with
  | zero =>
    intro G _ _ _ π H K hcard _ _
    have := Nat.card_pos (α := G)
    omega
  | succ n ih =>
    intro G _ _ _ π H K hcard hH hK
    rcases subsingleton_or_nontrivial G with _ | _
    · exact ⟨1, by simp [Subgroup.eq_bot_of_subsingleton H, Subgroup.eq_bot_of_subsingleton K]⟩
    obtain ⟨N, hNmin⟩ := exists_minimal_normal_ne_bot (G := G)
    obtain ⟨hNnormal, hNbot, -⟩ := minimal_normal_ne_bot_iff.1 hNmin
    have _inst := hNnormal
    obtain ⟨p, d, hp, hd, hNcard⟩ := exists_prime_card_eq_pow_of_minimal_normal_ne_bot hNmin
    obtain ⟨q, m, -, -, ⟨e⟩⟩ := exists_prime_nonempty_mulEquiv_of_minimal_normal_ne_bot hNmin
    have : IsMulCommutative ↥N := isMulCommutative_of_mulEquiv e
    have hqcard : Nat.card (G ⧸ N) ≤ n := by
      have := natCard_quotient_lt_natCard_of_bot_lt N (bot_lt_iff_ne_bot.2 hNbot)
      omega
    have hHq : IsHallSubgroup π (H.map (QuotientGroup.mk' N)) := by
      rw [← map_sup_mk'_eq_map_mk']; exact hH.map_sup_mk' N
    have hKq : IsHallSubgroup π (K.map (QuotientGroup.mk' N)) := by
      rw [← map_sup_mk'_eq_map_mk']; exact hK.map_sup_mk' N
    obtain ⟨xq, hxq⟩ := ih hqcard hHq hKq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xq
    obtain ⟨H', hH'def⟩ : ∃ H' : Subgroup G, H' = MulAut.conj x • H := ⟨_, rfl⟩
    have hH' : IsHallSubgroup π H' := hH'def ▸ hH.conj_smul x
    have himg : H'.map (QuotientGroup.mk' N) = K.map (QuotientGroup.mk' N) := by
      rw [hH'def, map_conj_smul]
      exact hxq
    have hLeq : H' ⊔ N = K ⊔ N := by
      have h1 : ∀ S : Subgroup G,
          Subgroup.comap (QuotientGroup.mk' N) (S.map (QuotientGroup.mk' N)) = S ⊔ N := by
        intro S
        rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
      rw [← h1 H', ← h1 K, himg]
    by_cases hmem : p ∈ π
    ·
      have hNpi : IsPiNumber π (Nat.card ↥N) := by
        rw [hNcard]; exact (isPiNumber_prime_pow_iff hp (by omega)).2 hmem
      have h1 : H' = H' ⊔ N := (sup_eq_left.2 (hH'.normal_le hNpi)).symm
      have h2 : K ⊔ N = K := sup_eq_left.2 (hK.normal_le hNpi)
      exact ⟨x, hH'def ▸ h1.trans (hLeq.trans h2)⟩
    ·
      have hNpi' : IsPiNumber πᶜ (Nat.card ↥N) := by
        rw [hNcard]; exact (isPiNumber_prime_pow_iff hp (by omega)).2 hmem
      obtain ⟨L, hLdef⟩ : ∃ L : Subgroup G, L = K ⊔ N := ⟨_, rfl⟩
      have hKL : K ≤ L := hLdef ▸ le_sup_left
      have hNL : N ≤ L := hLdef ▸ le_sup_right
      have hH'L : H' ≤ L := hLdef ▸ hLeq ▸ le_sup_left
      have hinfH : N ⊓ H' = ⊥ := inf_eq_bot_of_isPiNumber (π := πᶜ) hNpi' (by
        rw [compl_compl]; exact hH'.natCard)
      have hinfK : N ⊓ K = ⊥ := inf_eq_bot_of_isPiNumber (π := πᶜ) hNpi' (by
        rw [compl_compl]; exact hK.natCard)
      have : IsMulCommutative ↥(N.subgroupOf L) :=
        isMulCommutative_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hNL)
      have hsupH : N.subgroupOf L ⊔ H'.subgroupOf L = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hNL hH'L, sup_comm, hLeq, ← hLdef,
          Subgroup.subgroupOf_self]
      have hsupK : N.subgroupOf L ⊔ K.subgroupOf L = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hNL hKL, sup_comm, ← hLdef, Subgroup.subgroupOf_self]
      have hinfH' : N.subgroupOf L ⊓ H'.subgroupOf L = ⊥ := by
        rw [← inf_subgroupOf, hinfH, Subgroup.bot_subgroupOf]
      have hinfK' : N.subgroupOf L ⊓ K.subgroupOf L = ⊥ := by
        rw [← inf_subgroupOf, hinfK, Subgroup.bot_subgroupOf]
      have hcop : (Nat.card ↥(N.subgroupOf L)).Coprime (Nat.card (↥L ⧸ N.subgroupOf L)) := by
        rw [← Subgroup.index_eq_card,
          (isComplement'_of_sup_eq_top_of_inf_eq_bot hsupH hinfH').index_eq_card,
          natCard_subgroupOf hNL, natCard_subgroupOf hH'L]
        exact hNpi'.coprime_of_compl (by rw [compl_compl]; exact hH'.natCard) Nat.card_pos.ne'
          Nat.card_pos.ne'
      obtain ⟨a, -, hconj⟩ := exists_mem_conj_smul_eq hcop hsupH hinfH' hsupK hinfK'
      refine ⟨(a : G) * x, ?_⟩
      have hmap := congrArg (fun S : Subgroup ↥L => S.map L.subtype) hconj
      simp only [map_conj_smul, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hH'L,
        inf_eq_left.2 hKL, Subgroup.coe_subtype] at hmap
      rw [map_mul, mul_smul, ← hH'def]
      exact hmap

theorem exists_conj_smul_eq_of_isHallSubgroup {G : Type*} [Group G] [Finite G]
    [Group.IsSolvable G] {π : Set ℕ} {H K : Subgroup G} (hH : IsHallSubgroup π H)
    (hK : IsHallSubgroup π K) : ∃ g : G, MulAut.conj g • H = K :=
  exists_conj_smul_eq_of_isHallSubgroup_aux (Nat.card G) le_rfl hH hK

theorem exists_forall_mem_iff_conj_mem_of_isHallSubgroup [Finite G] [Group.IsSolvable G]
    {H K : Subgroup G} (hH : IsHallSubgroup π H) (hK : IsHallSubgroup π K) :
    ∃ g : G, ∀ y : G, y ∈ K ↔ g⁻¹ * y * g ∈ H := by
  obtain ⟨g, hg⟩ := exists_conj_smul_eq_of_isHallSubgroup hH hK
  refine ⟨g, fun y => ?_⟩
  rw [← hg, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply]

theorem exists_map_conj_eq_of_isHallSubgroup [Finite G] [Group.IsSolvable G] {H K : Subgroup G}
    (hH : IsHallSubgroup π H) (hK : IsHallSubgroup π K) :
    ∃ g : G, H.map (MulAut.conj g : G →* G) = K := by
  obtain ⟨g, hg⟩ := exists_conj_smul_eq_of_isHallSubgroup hH hK
  exact ⟨g, by rwa [← conj_smul_eq_map_conj]⟩

theorem natCard_eq_natCard_of_isHallSubgroup [Finite G] [Group.IsSolvable G] {H K : Subgroup G}
    (hH : IsHallSubgroup π H) (hK : IsHallSubgroup π K) : Nat.card H = Nat.card K := by
  obtain ⟨g, hg⟩ := exists_conj_smul_eq_of_isHallSubgroup hH hK
  rw [← hg, natCard_conj_smul]

end CFSG.FeitThompson
