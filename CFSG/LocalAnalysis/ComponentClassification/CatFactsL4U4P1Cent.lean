module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1Facts
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1SL23
public import CFSG.RankThree.PartOne.K1214.Basic

public section

namespace CFSG.ComponentClassification.HarrisLit.P1

open CFSG Subgroup

variable {G : Type} [Group G]

theorem eq_oddPart_of_card_dvd [Finite G] {C H : Subgroup G} (hH : H ≤ Q81.oddPart C)
    (hcard : Nat.card ↥(Q81.oddPart C) ∣ 2 * Nat.card ↥H) : H = Q81.oddPart C := by
  set K := Q81.oddPart C with hK
  have hcH : Nat.card ↥(H.subgroupOf K) = Nat.card ↥H :=
    Nat.card_congr (subgroupOfEquivOfLe hH).toEquiv
  have hidx : (H.subgroupOf K).index ∣ 2 := by
    have h1 := card_mul_index (H.subgroupOf K)
    rw [hcH] at h1
    rw [← h1] at hcard
    have hpos : 0 < Nat.card ↥H := Nat.card_pos
    rw [mul_comm 2] at hcard
    exact Nat.dvd_of_mul_dvd_mul_left hpos hcard
  refine le_antisymm hH ?_
  rw [hK, Q81.oddPart, closure_le]
  rintro g ⟨hgC, hodd⟩
  have hgK : g ∈ K := Q81.mem_oddPart hgC hodd
  rcases (Nat.dvd_prime Nat.prime_two).mp hidx with h1 | h2
  · have htop := index_eq_one.mp h1
    have hmem : (⟨g, hgK⟩ : ↥K) ∈ H.subgroupOf K := htop ▸ mem_top _
    exact hmem
  · have hsq : (⟨g, hgK⟩ : ↥K) * ⟨g, hgK⟩ ∈ H.subgroupOf K := mul_self_mem_of_index_two h2 _
    rw [mem_subgroupOf] at hsq
    obtain ⟨k, hk⟩ := hodd
    have hg : g = (g * g) ^ (k + 1) := by
      rw [← pow_two, ← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, ← hk,
        pow_orderOf_eq_one, one_mul]
    rw [hg]
    exact pow_mem hsq _

theorem card_dvd_of_map_le {Q S : Type*} [Group Q] [Group S] [Finite Q] (π : Q →* S)
    {H : Subgroup Q} {M : Subgroup S} (hHM : H.map π ≤ M) :
    Nat.card ↥H ∣ Nat.card ↥π.ker * Nat.card ↥M := by
  set f := π.comp H.subtype
  have h1 : Nat.card ↥f.ker * Nat.card ↥f.range = Nat.card ↥H := by
    rw [← index_ker, card_mul_index]
  have h2 : f.range = H.map π := by
    rw [MonoidHom.range_comp, range_subtype]
  have h3 : Nat.card ↥f.ker ∣ Nat.card ↥π.ker := by
    have hle : f.ker.map H.subtype ≤ π.ker := by
      rintro _ ⟨k, hk, rfl⟩
      exact hk
    rw [← card_map_of_injective H.subtype_injective]
    exact card_dvd_of_le hle
  rw [← h1, h2]
  exact mul_dvd_mul h3 (card_dvd_of_le hHM)

theorem cent_of_models (hM : P1Models) (G : Type) [Group G] [Finite G] (Q : Subgroup G)
    (hQ : IsQuasisimple ↥Q)
    (hP : Blueprint.LieModel (↥Q ⧸ center ↥Q) .PSL 4 3 1 ∨
      Blueprint.LieModel (↥Q ⧸ center ↥Q) .PSU 4 3 1)
    (hZ : Nat.card ↥(center ↥Q) ∣ 2) (w : G) (hw : w ∈ Q) (hw2 : orderOf w = 2)
    (X₁ X₂ : Subgroup G) (_hne : X₁ ≠ X₂) (h₁ : X₁ ≤ Q ⊓ centralizer {w})
    (h₂ : X₂ ≤ Q ⊓ centralizer {w}) (hs₁ : (X₁.subgroupOf (Q ⊓ centralizer {w})).IsSubnormal)
    (_hs₂ : (X₂.subgroupOf (Q ⊓ centralizer {w})).IsSubnormal)
    (hc : X₁ ≤ centralizer (X₂ : Set G)) (hi : X₁ ⊓ X₂ = zpowers w)
    (hX₁ : IsSLTwoOver 3 ↥X₁) (hX₂ : IsSLTwoOver 3 ↥X₂) :
    X₁ ⊔ X₂ = closure {g : G | g ∈ Q ⊓ centralizer {w} ∧ Odd (orderOf g)} := by
  change X₁ ⊔ X₂ = Q81.oddPart (Q ⊓ centralizer {w})
  set C := Q ⊓ centralizer {w} with hCdef
  have hHK : X₁ ⊔ X₂ ≤ Q81.oddPart C := sup_le (le_oddPart hX₁ h₁) (le_oddPart hX₂ h₂)
  have hcardH : Nat.card ↥(X₁ ⊔ X₂) = 288 := by
    have hN : X₂ ≤ normalizer (X₁ : Set G) :=
      (le_centralizer_iff.mp hc).trans (centralizer_le_normalizer _)
    have h := RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hN
    rw [hi, Nat.card_zpowers, hw2, card_eq hX₁, card_eq hX₂] at h
    omega
  set wq : ↥Q := ⟨w, hw⟩ with hwq
  by_cases hwZ : wq ∈ center ↥Q
  ·
    exfalso
    have hCQ : C = Q := by
      refine inf_eq_left.mpr fun q hq => ?_
      rw [mem_centralizer_singleton_iff]
      have h := mem_center_iff.mp hwZ ⟨q, hq⟩
      exact congrArg Subtype.val h
    have hs : (X₁.subgroupOf Q).IsSubnormal := hCQ ▸ hs₁
    rcases LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hQ hs with htop | hZ1
    ·
      have hQX : Q ≤ X₁ := fun q hq => by
        have h := htop ▸ mem_top (⟨q, hq⟩ : ↥Q)
        exact h
      obtain ⟨a, b, hab⟩ := exists_mul_ne hX₂
      apply hab
      have ha : (a : G) ∈ X₁ := hQX (h₂ a.2).1
      exact Subtype.ext (mem_centralizer_iff.mp (hc ha) b b.2).symm
    ·
      obtain ⟨a, b, hab⟩ := exists_mul_ne hX₁
      apply hab
      have ha : (⟨a, (h₁ a.2).1⟩ : ↥Q) ∈ center ↥Q := hZ1 (show (a : G) ∈ X₁ from a.2)
      have h := mem_center_iff.mp ha ⟨b, (h₁ b.2).1⟩
      exact Subtype.ext (congrArg Subtype.val h).symm
  ·
    set π := QuotientGroup.mk' (center ↥Q) with hπ
    set s := π wq with hs
    have hs1 : s ≠ 1 := by
      rw [hs, hπ, QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
      exact hwZ
    have hs2 : orderOf s = 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      refine orderOf_eq_prime ?_ hs1
      have hwq2 : wq ^ 2 = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one, ← hw2]
        exact pow_orderOf_eq_one w
      rw [hs, ← map_pow, hwq2, map_one]
    set K₀ := (Q81.oddPart (centralizer ({s} : Set (↥Q ⧸ center ↥Q)))).comap π with hK₀
    have hKle : Q81.oddPart C ≤ K₀.map Q.subtype := by
      rw [Q81.oddPart, closure_le]
      rintro g ⟨hgC, hodd⟩
      obtain ⟨hgQ, hgw⟩ := mem_inf.mp hgC
      refine ⟨⟨g, hgQ⟩, ?_, rfl⟩
      show π ⟨g, hgQ⟩ ∈ Q81.oddPart (centralizer ({s} : Set (↥Q ⧸ center ↥Q)))
      refine Q81.mem_oddPart ?_ (Odd.of_dvd_nat hodd ?_)
      · rw [mem_centralizer_singleton_iff, hs, ← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        exact mem_centralizer_singleton_iff.mp hgw
      · rw [← Subgroup.orderOf_mk g hgQ]
        exact orderOf_map_dvd π _
    have hK₀card : Nat.card ↥K₀ ∣ Nat.card ↥(center ↥Q) *
        Nat.card ↥(Q81.oddPart (centralizer ({s} : Set (↥Q ⧸ center ↥Q)))) := by
      have h := card_dvd_of_map_le π (H := K₀) (map_comap_le _ _)
      rwa [hπ, QuotientGroup.ker_mk'] at h
    have hKcard : Nat.card ↥(Q81.oddPart C) ∣ 2 *
        Nat.card ↥(Q81.oddPart (centralizer ({s} : Set (↥Q ⧸ center ↥Q)))) := by
      have h1 := card_dvd_of_le hKle
      rw [card_map_of_injective Q.subtype_injective] at h1
      exact h1.trans (hK₀card.trans (mul_dvd_mul_right hZ _))
    rcases (hM _ hP).inner s hs2 with h288 | h360
    · refine eq_oddPart_of_card_dvd hHK (hKcard.trans ?_)
      rw [hcardH]
      exact mul_dvd_mul_left 2 h288
    · exfalso
      have h1 : Nat.card ↥(X₁ ⊔ X₂) ∣ 2 * 360 := by
        rw [← h360]
        exact (card_dvd_of_le hHK).trans hKcard
      rw [hcardH] at h1
      norm_num at h1

end CFSG.ComponentClassification.HarrisLit.P1
