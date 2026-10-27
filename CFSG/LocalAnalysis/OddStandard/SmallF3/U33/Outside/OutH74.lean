module

public import CFSG.GH74.GLS.Stage1.Thm6.Adapters13
public import Mathlib.GroupTheory.IndexNormal

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

open Subgroup
open CFSG.GH74.GLS.Stage1.Thm6.Sec13

theorem H74_dichotomy {G : Type} [Group G] [Finite G] {P Q : Subgroup G} (hP : IsPGroup 2 P)
    (hPi : ¬ 2 ∣ P.index) (hQP : Q ≤ P) (hQ2 : Q.relIndex P = 2) {t : G} (ht : t ∈ P)
    (htQ : t ∉ Q) (ht2 : t * t = 1) :
    (∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧ IsPGroup 2 (G ⧸ N) ∧ t ∉ N) ∨
    ∃ w : G, w * t * w⁻¹ ∈ Q ∧
      ¬ 2 ∣ (P ⊓ centralizer ({w * t * w⁻¹} : Set G)).relIndex
        (centralizer ({w * t * w⁻¹} : Set G)) ∧
      ∀ c ∈ P ⊓ centralizer ({t} : Set G),
        w * c * w⁻¹ ∈ P ⊓ centralizer ({w * t * w⁻¹} : Set G) := by
  have hSylow : Sylow2In P ⊤ :=
    ⟨le_top, hP, by simpa [Subgroup.relIndex_top_right] using hPi⟩
  have hQnorm : (Q.subgroupOf P).Normal := by
    apply Subgroup.normal_of_index_eq_two
    simpa [Subgroup.relIndex] using hQ2
  have hQn : ∀ g ∈ P, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q := by
    intro g hg q hq
    have hqmem : (⟨q, hQP hq⟩ : ↥P) ∈ Q.subgroupOf P := by
      change q ∈ Q
      exact hq
    have hmem : (⟨g, hg⟩ : ↥P) * (⟨q, hQP hq⟩ : ↥P) * (⟨g, hg⟩ : ↥P)⁻¹ ∈
        Q.subgroupOf P :=
      hQnorm.conj_mem ⟨q, hQP hq⟩ hqmem ⟨g, hg⟩
    exact (Subgroup.mem_subgroupOf).mp hmem
  have hQne : Q ≠ P := by
    intro h
    exact htQ (h ▸ ht)
  have hcyc : ∃ g ∈ P, P = Q ⊔ zpowers g := by
    refine ⟨t, ht, ?_⟩
    have hle : Q ⊔ zpowers t ≤ P := sup_le hQP (Subgroup.zpowers_le.mpr ht)
    have hne1 : Q.relIndex (Q ⊔ zpowers t) ≠ 1 := by
      intro h
      have hKQ : Q ⊔ zpowers t ≤ Q := (Subgroup.relIndex_eq_one).mp h
      exact htQ (hKQ (Subgroup.mem_sup_right (Subgroup.mem_zpowers t)))
    have hprod : Q.relIndex (Q ⊔ zpowers t) * (Q ⊔ zpowers t).relIndex P = 2 := by
      rw [← hQ2]
      exact Subgroup.relIndex_mul_relIndex (H := Q) (K := Q ⊔ zpowers t) (L := P)
        le_sup_left hle
    have hd : Q.relIndex (Q ⊔ zpowers t) = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp
        ⟨(Q ⊔ zpowers t).relIndex P, hprod.symm⟩ with h1 | h1
      · exact absurd h1 hne1
      · exact h1
    have he : (Q ⊔ zpowers t).relIndex P = 1 := by
      rw [hd] at hprod
      omega
    exact le_antisymm ((Subgroup.relIndex_eq_one).mp he) hle
  have hext : ∀ w : G, IsExtremal2 P (w * t * w⁻¹) →
      w * t * w⁻¹ ∈ Q ∨ ∃ q ∈ Q, w * t * w⁻¹ = q * t := by
    intro w hExt
    by_cases hyQ : w * t * w⁻¹ ∈ Q
    · exact Or.inl hyQ
    · right
      have hyP : w * t * w⁻¹ ∈ P := hExt.1
      have hidx : (Q.subgroupOf P).index = 2 := by
        simpa [Subgroup.relIndex] using hQ2
      have hmem : (⟨w * t * w⁻¹, hyP⟩ : ↥P) * (⟨t, ht⟩ : ↥P) ∈ Q.subgroupOf P := by
        rw [Subgroup.mul_mem_iff_of_index_two hidx]
        exact ⟨fun h => (hyQ ((Subgroup.mem_subgroupOf).mp h)).elim,
          fun h => (htQ ((Subgroup.mem_subgroupOf).mp h)).elim⟩
      refine ⟨(w * t * w⁻¹) * t, (Subgroup.mem_subgroupOf).mp hmem, ?_⟩
      rw [mul_assoc (w * t * w⁻¹) t t, ht2, mul_one]
  rcases ig_15_15_sec13 G P Q t hSylow hQP hQn hQne hcyc ht htQ ht2 hext with
    h | ⟨w, hw, hExt, hc⟩
  · exact Or.inl h
  · exact Or.inr ⟨w, hw, hExt.2.2.2, hc⟩

theorem H74Cor222 {G : Type} [Group G] [Finite G] {P Q : Subgroup G} (hP : IsPGroup 2 P)
    (hPi : ¬ 2 ∣ P.index) (hQP : Q ≤ P) (hQ2 : Q.relIndex P = 2) {t : G} (ht : t ∈ P)
    (htQ : t ∉ Q) (ht2 : t * t = 1)
    (hno : ¬ ∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧ IsPGroup 2 (G ⧸ N) ∧ t ∉ N) :
    ∃ w : G, w * t * w⁻¹ ∈ Q ∧
      ¬ 2 ∣ (P ⊓ centralizer ({w * t * w⁻¹} : Set G)).relIndex
        (centralizer ({w * t * w⁻¹} : Set G)) ∧
      ∀ c ∈ P ⊓ centralizer ({t} : Set G),
        w * c * w⁻¹ ∈ P ⊓ centralizer ({w * t * w⁻¹} : Set G) := by
  rcases H74_dichotomy hP hPi hQP hQ2 ht htQ ht2 with h | h
  · exact absurd h hno
  · exact h

theorem H74_of_mem_commutator {G : Type} [Group G] [Finite G] {P Q : Subgroup G}
    (hP : IsPGroup 2 P) (hPi : ¬ 2 ∣ P.index) (hQP : Q ≤ P) (hQ2 : Q.relIndex P = 2) {t : G}
    (ht : t ∈ P) (htQ : t ∉ Q) (ht2 : t * t = 1) (htc : t ∈ commutator G) :
    ∃ w : G, w * t * w⁻¹ ∈ Q ∧
      ¬ 2 ∣ (P ⊓ centralizer ({w * t * w⁻¹} : Set G)).relIndex
        (centralizer ({w * t * w⁻¹} : Set G)) ∧
      ∀ c ∈ P ⊓ centralizer ({t} : Set G),
        w * c * w⁻¹ ∈ P ⊓ centralizer ({w * t * w⁻¹} : Set G) := by
  apply H74Cor222 hP hPi hQP hQ2 ht htQ ht2
  rintro ⟨N, hN, hcyc, -, htN⟩
  haveI : N.Normal := hN
  haveI : IsCyclic (G ⧸ N) := hcyc
  haveI : IsMulCommutative (G ⧸ N) := IsCyclic.isMulCommutative
  have hle : _root_.commutator G ≤ N :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := N)).mp inferInstance
  exact htN (hle htc)

theorem H74_of_simple {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) {P Q : Subgroup G} (hP : IsPGroup 2 P)
    (hPi : ¬ 2 ∣ P.index) (hQP : Q ≤ P) (hQ2 : Q.relIndex P = 2) {t : G} (ht : t ∈ P)
    (htQ : t ∉ Q) (ht2 : t * t = 1) :
    ∃ w : G, w * t * w⁻¹ ∈ Q ∧
      ¬ 2 ∣ (P ⊓ centralizer ({w * t * w⁻¹} : Set G)).relIndex
        (centralizer ({w * t * w⁻¹} : Set G)) ∧
      ∀ c ∈ P ⊓ centralizer ({t} : Set G),
        w * c * w⁻¹ ∈ P ⊓ centralizer ({w * t * w⁻¹} : Set G) := by
  have htop : _root_.commutator G = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (_root_.commutator G) with hbot | htop
    · exfalso
      haveI : IsMulCommutative G := (_root_.commutator_eq_bot_iff G).mp hbot
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (mul_comm' a b)
    · exact htop
  exact H74_of_mem_commutator hP hPi hQP hQ2 ht htQ ht2 (htop ▸ Subgroup.mem_top t)

end CFSG.OddStandard.SmallF3.HarrisU33.Outside
