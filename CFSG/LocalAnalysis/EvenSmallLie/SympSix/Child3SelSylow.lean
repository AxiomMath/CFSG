module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelStar

public section

namespace CFSG.EvenSmallLie.Child3

open Subgroup CFSG.ComponentClassification

theorem four_dvd_card_centralizer_of_orderOf_four {T : Type} [Group T] [Finite T] {p w : T}
    (hw : orderOf w = 4) (hc : w * p = p * w) :
    4 ∣ Nat.card (centralizer ({p} : Set T)) := by
  have hle : zpowers w ≤ centralizer ({p} : Set T) :=
    zpowers_le.2 (mem_centralizer_singleton_iff.2 hc)
  have := Subgroup.card_dvd_of_le hle
  rwa [Nat.card_zpowers, hw] at this

theorem four_dvd_card_centralizer_of_klein {T : Type} [Group T] [Finite T] {p u v : T}
    (hu : orderOf u = 2) (hv : orderOf v = 2) (huv : u ≠ v) (hcomm : u * v = v * u)
    (hup : u * p = p * u) (hvp : v * p = p * v) :
    4 ∣ Nat.card (centralizer ({p} : Set T)) := by
  have hnorm : zpowers v ≤ normalizer ((zpowers u : Subgroup T) : Set T) :=
    zpowers_le.2 (centralizer_le_normalizer _ (mem_centralizer_iff.2 fun x hx => by
      rcases (mem_zpowers_iff_of_orderOf_eq_two hu).1 hx with rfl | rfl
      · rw [one_mul, mul_one]
      · exact hcomm))
  have hdisj : Disjoint (zpowers u) (zpowers v) := by
    rw [disjoint_iff, eq_bot_iff]
    intro x hx
    obtain ⟨hxu, hxv⟩ := mem_inf.1 hx
    rcases (mem_zpowers_iff_of_orderOf_eq_two hv).1 hxv with rfl | rfl
    · exact one_mem _
    · rcases (mem_zpowers_iff_of_orderOf_eq_two hu).1 hxu with h1 | h1
      · rw [h1, orderOf_one] at hv
        exact absurd hv (by norm_num)
      · exact absurd h1.symm huv
  have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnorm hdisj
  rw [Nat.card_zpowers, Nat.card_zpowers, hu, hv] at hcard
  have hle : zpowers u ⊔ zpowers v ≤ centralizer ({p} : Set T) :=
    sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 hup))
      (zpowers_le.2 (mem_centralizer_singleton_iff.2 hvp))
  have := Subgroup.card_dvd_of_le hle
  rwa [hcard] at this

theorem card_centralizer_conj {T : Type} [Group T] (g x : T) :
    Nat.card (centralizer ({g * x * g⁻¹} : Set T)) = Nat.card (centralizer ({x} : Set T)) :=
  card_centralizer_mulEquiv (MulAut.conj g) x

theorem k3_of_sylow {T : Type} [Group T] [Finite T] (P : Subgroup T)
    (hP : Nat.card P = 3 ^ (Nat.card T).factorization 3)
    (hw : ∀ p ∈ P, orderOf p = 3 → 4 ∣ Nat.card (centralizer ({p} : Set T))) :
    ∀ x : T, orderOf x = 3 → 4 ∣ Nat.card (centralizer ({x} : Set T)) := by
  intro x hx
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let S₀ : Sylow 3 T := Sylow.ofCard P hP
  have hpx : IsPGroup 3 (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨S, hS⟩ := hpx.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq T S₀ S
  have hxS : x ∈ (S : Subgroup T) := hS (mem_zpowers x)
  rw [← hg, Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem] at hxS
  have hxP : g⁻¹ * x * g ∈ P := by
    have h' : (MulAut.conj g)⁻¹ • x ∈ P := hxS
    rwa [MulAut.smul_def, MulAut.conj_inv_apply] at h'
  have hord : orderOf (g⁻¹ * x * g) = 3 := by
    have h' := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) x
    rw [MulAut.conj_apply, inv_inv] at h'
    rw [h', hx]
  have hconj := card_centralizer_conj g⁻¹ x
  rw [inv_inv] at hconj
  rw [← hconj]
  exact hw _ hxP hord

end CFSG.EvenSmallLie.Child3
