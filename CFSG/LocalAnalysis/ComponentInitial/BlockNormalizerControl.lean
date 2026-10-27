module

public import CFSG.LocalAnalysis.ComponentInitial.BlockTransporter
public import CFSG.LocalAnalysis.ComponentInitial.StandardCriterion
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalComponent

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup

variable {G : Type*} [Group G] [Finite G] {J : Subgroup G}

theorem mem_normalizer_blockGroup_of_involution (hJ : IsUniversalComponent J)
    (heven : Even (Nat.card J)) {K : Subgroup G} (hK : K ∈ block J) {t g : G}
    (ht2 : orderOf t = 2) (htK : t ∈ centralizer (K : Set G))
    (htKg : t ∈ centralizer (conjSub g K : Set G)) : g ∈ normalizer (blockGroup J : Set G) := by
  obtain ⟨c, hc⟩ := hK.1
  have hcomp1 : CFSG.Assembly.IsComponentOf K (centralizer ({t} : Set G)) := by
    rw [hc] at htK ⊢
    exact isUniversalComponent_conjSub hJ c t htK ht2
  have hcomp2 : CFSG.Assembly.IsComponentOf (conjSub g K) (centralizer ({t} : Set G)) := by
    rw [hc, ← conjSub_mul] at htKg ⊢
    exact isUniversalComponent_conjSub hJ (g * c) t htKg ht2
  have hrel : CommRel K (conjSub g K) := isComponentOf_eq_or_commute hcomp1 hcomp2
  have hKg : conjSub g K ∈ block J :=
    ⟨isConjOf_conjSub hK.1 g,
      commRel_trans hJ heven mem_block_self.1 hK.1 (isConjOf_conjSub hK.1 g) hK.2 hrel⟩
  exact mem_normalizer_blockGroup hJ heven hK hKg

theorem commuting_block_two_subgroup_normalizer_control (hq : CFSG.Assembly.IsQuasisimple J)
    (heven : Even (Nat.card J)) (hCeven : Even (Nat.card (centralizer (J : Set G))))
    (hJ : IsUniversalComponent J) :
    let C := centralizer (J : Set G)
    let H := normalizer (blockGroup J : Set G)
    normalizer (C : Set G) = normalizer (J : Set G) ∧
      (∀ g : G, g ∉ H → Odd (Nat.card ↥(C ⊓ CFSG.conjugate C g))) ∧
      (∀ K ∈ block J, ∀ Q : Subgroup G, Q ≤ centralizer (K : Set G) → IsPGroup 2 Q → Q ≠ ⊥ →
        normalizer (Q : Set G) ≤ H) ∧
      (∀ E : Subgroup G, IsElementaryAbelian 2 E → Nat.card E = 8 →
        ∀ K ∈ block J, 4 ≤ Nat.card ↥(E ⊓ centralizer (K : Set G)) → normalizer (E : Set G) ≤ H) := by
  intro C H
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : normalizer (C : Set G) = normalizer (J : Set G) := by
    refine le_antisymm (fun g hg => ?_) (normalizer_le_normalizer_centralizer J)
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 (even_iff_two_dvd.1 hCeven)
    have ht2 : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe, ht]
    have hCg : conjSub g C = C := conjSub_eq_of_mem_normalizer hg
    have htJg : (t : G) ∈ centralizer (conjSub g J : Set G) := by
      rw [← conjSub_centralizer, hCg]; exact t.2
    have h1 := hJ t t.2 ht2
    have h2 := isUniversalComponent_conjSub hJ g t htJg ht2
    rcases isComponentOf_eq_or_commute h1 h2 with h | h
    · have hgJ : conjSub g J = J := h.symm
      refine mem_normalizer_of_conjSub_le (le_of_eq hgJ) (le_of_eq ?_)
      calc conjSub g⁻¹ J = conjSub g⁻¹ (conjSub g J) := by rw [hgJ]
        _ = J := conjSub_inv_conjSub g J
    · exfalso
      have hJgC : conjSub g J ≤ C :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.1 (by rw [commutator_comm]; exact h)
      rw [← hCg, conjSub_centralizer] at hJgC
      exact not_le_centralizer_self_of_isQuasisimple (isQuasisimple_of_isConjOf hq ⟨g, rfl⟩) hJgC
  have hodd : ∀ g : G, g ∉ H → Odd (Nat.card ↥(C ⊓ CFSG.conjugate C g)) := by
    intro g hg
    rw [← Nat.not_even_iff_odd]
    intro hev
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥(C ⊓ CFSG.conjugate C g)) 2
      (even_iff_two_dvd.1 hev)
    have ht2 : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe, ht]
    obtain ⟨htC, htCg⟩ := Subgroup.mem_inf.1 t.2
    have htCg' : (t : G) ∈ centralizer (conjSub g⁻¹ J : Set G) := by
      rw [← conjSub_centralizer]; exact htCg
    apply hg
    have := mem_normalizer_blockGroup_of_involution hJ heven mem_block_self ht2 htC htCg'
    simpa using inv_mem this
  have hQ : ∀ K ∈ block J, ∀ Q : Subgroup G, Q ≤ centralizer (K : Set G) → IsPGroup 2 Q →
      Q ≠ ⊥ → normalizer (Q : Set G) ≤ H := by
    intro K hK Q hQK hQ2 hQ1 g hg
    have hQne : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).2 hQ1
    have hQcard : 2 ∣ Nat.card Q := by
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hQ2
      rcases n with _ | n
      · rw [pow_zero] at hn
        exact absurd hn (Finite.one_lt_card).ne'
      · rw [hn, pow_succ]; exact dvd_mul_left _ _
    obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := Q) 2 hQcard
    have hs2 : orderOf (s : G) = 2 := by rw [Subgroup.orderOf_coe, hs]
    have hQg : conjSub g Q = Q := conjSub_eq_of_mem_normalizer hg
    have hsK : (s : G) ∈ centralizer (K : Set G) := hQK s.2
    have hsKg : (s : G) ∈ centralizer (conjSub g K : Set G) := by
      have h1 : g * (g⁻¹ * s * g) * g⁻¹ ∈ centralizer (conjSub g K : Set G) := by
        refine conj_mem_centralizer_conjSub (hQK ?_) g
        have : g⁻¹ * (s : G) * g⁻¹⁻¹ ∈ conjSub g⁻¹ Q := ⟨s, s.2, rfl⟩
        have hQg' : conjSub g⁻¹ Q = Q := by
          calc conjSub g⁻¹ Q = conjSub g⁻¹ (conjSub g Q) := by rw [hQg]
            _ = Q := conjSub_inv_conjSub g Q
        rw [hQg'] at this
        simpa using this
      simpa [mul_assoc] using h1
    exact mem_normalizer_blockGroup_of_involution hJ heven hK hs2 hsK hsKg
  have hE : ∀ E : Subgroup G, IsElementaryAbelian 2 E → Nat.card E = 8 →
      ∀ K ∈ block J, 4 ≤ Nat.card ↥(E ⊓ centralizer (K : Set G)) →
        normalizer (E : Set G) ≤ H := by
    intro E hEel hE8 K hK hcard g hg
    have := hEel
    set D := E ⊓ centralizer (K : Set G) with hD
    have hD2 : IsPGroup 2 D := (IsElementaryAbelian.isPGroup 2 E).to_le inf_le_left
    have hDdvd : Nat.card D ∣ 2 ^ 3 := by
      rw [show (2 : ℕ) ^ 3 = 8 by norm_num, ← hE8]
      exact Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨i, hi, hDi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hDdvd
    have hi2 : 2 ≤ i := by
      by_contra h
      push Not at h
      interval_cases i <;> simp_all
    have h4 : 2 ^ 2 ∣ Nat.card D := by rw [hDi]; exact Nat.pow_dvd_pow 2 hi2
    obtain ⟨U', hU'⟩ := Sylow.exists_subgroup_card_pow_prime 2 h4
    set U := U'.map D.subtype with hU
    have hUcard : Nat.card U = 4 := by
      rw [hU, Subgroup.card_map_of_injective D.subtype_injective, hU']
      norm_num
    have hUD : U ≤ D := Subgroup.map_subtype_le U'
    have hUE : U ≤ E := hUD.trans inf_le_left
    have hUK : U ≤ centralizer (K : Set G) := hUD.trans inf_le_right
    have hEg : conjSub g E = E := conjSub_eq_of_mem_normalizer hg
    have hUgE : conjSub g U ≤ E := by
      rw [← hEg]; exact map_mono hUE
    have hcomm : ∀ x ∈ U, ∀ y ∈ conjSub g U, x * y = y * x := fun x hx y hy =>
      congrArg Subtype.val (hEel.is_comm.comm (⟨x, hUE hx⟩ : E) ⟨y, hUgE hy⟩)
    have hc := card_sup_mul_card_inf_of_commute hcomm
    rw [hUcard, card_conjSub, hUcard] at hc
    have hsup8 : Nat.card ↥(U ⊔ conjSub g U) ≤ 8 := by
      rw [← hE8]; exact Subgroup.card_le_of_le (sup_le hUE hUgE)
    have hinf2 : 2 ≤ Nat.card ↥(U ⊓ conjSub g U) := by
      by_contra h
      push Not at h
      have h1 : Nat.card ↥(U ⊔ conjSub g U) * Nat.card ↥(U ⊓ conjSub g U) ≤ 8 * 1 :=
        Nat.mul_le_mul hsup8 (by omega)
      omega
    have hne : U ⊓ conjSub g U ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hinf2
      omega
    obtain ⟨t, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
    obtain ⟨htU, htUg⟩ := Subgroup.mem_inf.1 t.2
    have ht1' : (t : G) ≠ 1 := fun h => ht1 (Subtype.ext h)
    have htsq : (t : G) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (t : G) (hUE htU)
    have ht2 : orderOf (t : G) = 2 := orderOf_eq_prime htsq ht1'
    have htKg : (t : G) ∈ centralizer (conjSub g K : Set G) := by
      rw [← conjSub_centralizer]
      exact map_mono hUK htUg
    exact mem_normalizer_blockGroup_of_involution hJ heven hK ht2 (hUK htU) htKg
  exact ⟨hN, hodd, hQ, hE⟩

end CFSG.LocalAnalysis.ComponentInitial
