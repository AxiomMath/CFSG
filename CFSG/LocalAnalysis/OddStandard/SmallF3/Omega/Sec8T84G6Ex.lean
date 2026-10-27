module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G6Odd
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec8t84g6_not_extra [Finite G] (hAutF : Asc82AutFacts) (hGi : Sec8T84FactGamInner)
    {t : G} {L : Subgroup G} (hL : IsOm6M L) {γ : G} (hγ2 : γ * γ = 1)
    (hout : InducesOutsideGStar L 6 (-1) γ) {K U : Subgroup G} (hKq : IsQuasisimple ↥K)
    (hCN : centralizer ({γ} : Set G) ≤ normalizer (K : Set G)) (hK0 : layerCent L γ ≤ K)
    (hU : IsElemAb2 U 4) (hUC : U ≤ centralizer ({γ} : Set G))
    (htC : t ∈ centralizer ({γ} : Set G)) (ht2 : t * t = 1)
    (htU : t ∈ normalizer (U : Set G)) (hUt : U ⊓ centralizer ({t} : Set G) ≤ L) :
    ¬ (IsL29 K ∨ IsL281 K ∨ IsL3Eps3 K) := by
  intro hex
  have hsimple : IsSimpleGroup (↥K ⧸ CFSG.oddCore ↥K) := by
    refine sec8t84g6_simple_of_shape ?_
    rcases hex with h | h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  have hZ := sec8t84g6_center_odd hKq hsimple
  have hUN : U ≤ normalizer (K : Set G) := hUC.trans hCN
  have hra := (hAutF.rank_aut G K U hKq hUN hU.1).1 hex
  have h4 : 4 ≤ CFSG.Open.pRank 2 U := CFSG.SectionRank.le_pRank (by norm_num) le_rfl hU.1 hU.2
  have hpos : 1 ≤ CFSG.Open.pRank 2 (U ⊓ centralizer (K : Set G)) := by omega
  obtain ⟨E, hEH, hEe, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := 2) (by norm_num) (U ⊓ centralizer (K : Set G))
  obtain ⟨a, haE, ha1⟩ : ∃ a ∈ E, a ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    have hbot : E = ⊥ := (Subgroup.eq_bot_iff_forall E).mpr hcon
    rw [hbot, Subgroup.card_bot] at hEcard
    have : 2 ^ 1 ≤ 2 ^ CFSG.Open.pRank 2 (U ⊓ centralizer (K : Set G)) :=
      Nat.pow_le_pow_right (by norm_num) hpos
    omega
  have haU : a ∈ U := (hEH haE).1
  have haK : a ∈ centralizer (K : Set G) := (hEH haE).2
  have haa : a * a = 1 := by rw [← pow_two]; exact hEe.2 a haE
  have hUcomm : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hU.1.1.is_comm.comm (⟨x, hx⟩ : U) ⟨y, hy⟩)
  have ht1 : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hti : t⁻¹ ∈ centralizer ({γ} : Set G) := Subgroup.inv_mem _ htC
  have ha'U : t * a * t⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp htU a).mp haU
  have ha'K : t * a * t⁻¹ ∈ centralizer (K : Set G) := by
    rw [mem_centralizer_iff]
    intro k hk
    have hk' : t⁻¹ * k * t ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp (hCN hti) k).mp hk
      simpa using this
    have hc := mem_centralizer_iff.mp haK _ hk'
    calc k * (t * a * t⁻¹) = t * ((t⁻¹ * k * t) * a) * t⁻¹ := by group
      _ = t * (a * (t⁻¹ * k * t)) * t⁻¹ := by rw [hc]
      _ = t * a * t⁻¹ * k := by group
  have ha'a' : (t * a * t⁻¹) * (t * a * t⁻¹) = 1 := by
    calc (t * a * t⁻¹) * (t * a * t⁻¹) = t * (a * a) * t⁻¹ := by group
      _ = 1 := by rw [haa]; group
  have hcomm' : a * (t * a * t⁻¹) = (t * a * t⁻¹) * a := hUcomm a haU _ ha'U
  have hmain : ∀ x : G, x ∈ U → x ∈ centralizer (K : Set G) → x * t = t * x → x * x = 1 →
      x = 1 := by
    intro x hxU hxK hxt hx2
    by_contra hx1
    have hxL : x ∈ L := hUt ⟨hxU, mem_centralizer_singleton_iff.mpr hxt⟩
    have hxK0 : x ∈ layerCent L γ :=
      sec8t84g6_inv_mem_K0 hGi hL hγ2 hout hxL (hUC hxU) hx2
    have hodd := hZ x ⟨hK0 hxK0, hxK⟩
    have hord : orderOf x = 2 := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1
    rw [hord] at hodd
    exact absurd hodd (by decide)
  by_cases hb : a * (t * a * t⁻¹) = 1
  · have h1 : t * a * t⁻¹ = a := by
      have h2 : t * a * t⁻¹ = a⁻¹ := eq_inv_of_mul_eq_one_right hb
      rw [h2]
      exact inv_eq_of_mul_eq_one_right haa
    refine ha1 (hmain a haU haK ?_ haa)
    calc a * t = (t * a * t⁻¹) * t := by rw [h1]
      _ = t * a := by group
  · refine hb (hmain _ (U.mul_mem haU ha'U) (Subgroup.mul_mem _ haK ha'K) ?_ ?_)
    ·
      rw [ht1] at hcomm' ha'a' ⊢
      calc a * (t * a * t) * t = a * t * a * (t * t) := by group
        _ = a * t * a := by rw [ht2, mul_one]
        _ = (t * t) * a * t * a := by rw [ht2, one_mul]
        _ = t * ((t * a * t) * a) := by group
        _ = t * (a * (t * a * t)) := by rw [hcomm']
    · rw [ht1] at hcomm' ha'a' ⊢
      calc a * (t * a * t) * (a * (t * a * t)) = a * (t * a * t) * ((t * a * t) * a) := by
            rw [hcomm']
        _ = a * ((t * a * t) * (t * a * t)) * a := by group
        _ = a * a := by rw [ha'a', mul_one]
        _ = 1 := haa

end CFSG.OddStandard.SmallF3.Omega
