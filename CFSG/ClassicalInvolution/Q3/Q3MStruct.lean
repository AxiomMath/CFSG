module

public import CFSG.ClassicalInvolution.Q3.Q3MOdd
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical

public section

namespace CFSG.ClassicalInvolution.Q3.M

open CFSG.Open CFSG.ClassicalInvolution CFSG.ComponentClassification

section Commuting

variable {G : Type*} [Group G]

theorem exists_mul_of_mem_sup {A B : Subgroup G} (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    {x : G} (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let μ : A × B →* G :=
    MonoidHom.noncommCoprod A.subtype B.subtype fun x y => hcomm x x.2 y y.2
  have hrange : μ.range = A ⊔ B := by
    refine (MonoidHom.noncommCoprod_range A.subtype B.subtype _).trans ?_
    rw [Subgroup.range_subtype, Subgroup.range_subtype]
  rw [← hrange] at hx
  obtain ⟨⟨a, b⟩, rfl⟩ := hx
  exact ⟨a, a.2, b, b.2, rfl⟩

theorem commute_of_three_element {T D : Subgroup G} (hcomm : ∀ t ∈ T, ∀ d ∈ D, t * d = d * t)
    (h2 : ∀ x ∈ T ⊓ D, ∃ j : ℕ, x ^ (2 ^ j) = 1) {t₀ d₀ t d : G} (ht₀ : t₀ ∈ T) (hd₀ : d₀ ∈ D)
    (ht : t ∈ T) (hd : d ∈ D) (hc : t * d * (t₀ * d₀) = t₀ * d₀ * (t * d)) {k : ℕ}
    (hk : (t * d) ^ (3 ^ k) = 1) : t * (t₀ * d₀) = t₀ * d₀ * t := by
  have hdt₀ : d * t₀ = t₀ * d := (hcomm t₀ ht₀ d hd).symm
  have hd₀t : d₀ * t = t * d₀ := (hcomm t ht d₀ hd₀).symm
  set w : G := t⁻¹ * t₀⁻¹ * t * t₀ with hw
  have hwT : w ∈ T := T.mul_mem (T.mul_mem (T.mul_mem (T.inv_mem ht) (T.inv_mem ht₀)) ht) ht₀
  have e1 : t * t₀ * (d * d₀) = t₀ * t * (d₀ * d) := by
    have h1 : t * d * (t₀ * d₀) = t * t₀ * (d * d₀) := by
      calc t * d * (t₀ * d₀) = t * (d * t₀) * d₀ := by group
        _ = t * (t₀ * d) * d₀ := by rw [hdt₀]
        _ = t * t₀ * (d * d₀) := by group
    have h2' : t₀ * d₀ * (t * d) = t₀ * t * (d₀ * d) := by
      calc t₀ * d₀ * (t * d) = t₀ * (d₀ * t) * d := by group
        _ = t₀ * (t * d₀) * d := by rw [hd₀t]
        _ = t₀ * t * (d₀ * d) := by group
    rw [← h1, ← h2']
    exact hc
  have hwD : w ∈ D := by
    have : w * (d * d₀) = d₀ * d := by
      calc w * (d * d₀) = t⁻¹ * t₀⁻¹ * (t * t₀ * (d * d₀)) := by simp only [hw]; group
        _ = t⁻¹ * t₀⁻¹ * (t₀ * t * (d₀ * d)) := by rw [e1]
        _ = d₀ * d := by group
    have h' : w = d₀ * d * (d * d₀)⁻¹ := eq_mul_inv_of_mul_eq this
    rw [h']
    exact D.mul_mem (D.mul_mem hd₀ hd) (D.inv_mem (D.mul_mem hd hd₀))
  have hwc : Commute t w := hcomm t ht w hwD
  have hconj : t₀⁻¹ * t * t₀ = t * w := by simp only [hw]; group
  have hpow : ∀ n : ℕ, t₀⁻¹ * t ^ n * t₀ = (t * w) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc t₀⁻¹ * t ^ (n + 1) * t₀ = (t₀⁻¹ * t ^ n * t₀) * (t₀⁻¹ * t * t₀) := by group
        _ = (t * w) ^ n * (t * w) := by rw [ih, hconj]
        _ = (t * w) ^ (n + 1) := (pow_succ _ _).symm
  have hcd : Commute t d := hcomm t ht d hd
  have htk : t ^ (3 ^ k) ∈ D := by
    have h1 : t ^ (3 ^ k) * d ^ (3 ^ k) = 1 := by
      rw [← hcd.mul_pow]
      exact hk
    have h2' : t ^ (3 ^ k) = (d ^ (3 ^ k))⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [h2']
    exact D.inv_mem (D.pow_mem hd _)
  have hcomm3 : t₀ * t ^ (3 ^ k) = t ^ (3 ^ k) * t₀ := hcomm t₀ ht₀ _ htk
  have hw3 : w ^ (3 ^ k) = 1 := by
    have h1 := hpow (3 ^ k)
    rw [hwc.mul_pow] at h1
    have h2' : t₀⁻¹ * t ^ (3 ^ k) * t₀ = t ^ (3 ^ k) := by
      calc t₀⁻¹ * t ^ (3 ^ k) * t₀ = t₀⁻¹ * (t ^ (3 ^ k) * t₀) := by group
        _ = t₀⁻¹ * (t₀ * t ^ (3 ^ k)) := by rw [hcomm3]
        _ = t ^ (3 ^ k) := by group
    rw [h2'] at h1
    exact mul_left_cancel (a := t ^ (3 ^ k)) (by rw [← h1, mul_one])
  obtain ⟨j, hj⟩ := h2 w ⟨hwT, hwD⟩
  have hw1 : w = 1 := eq_one_of_pow_two_pow_of_pow_three_pow hj hw3
  have htt₀ : t * t₀ = t₀ * t := by
    rw [hw1, mul_one] at hconj
    calc t * t₀ = t₀ * (t₀⁻¹ * t * t₀) := by group
      _ = t₀ * t := by rw [hconj]
  calc t * (t₀ * d₀) = (t * t₀) * d₀ := by group
    _ = (t₀ * t) * d₀ := by rw [htt₀]
    _ = t₀ * (t * d₀) := by group
    _ = t₀ * (d₀ * t) := by rw [hd₀t]
    _ = t₀ * d₀ * t := by group

end Commuting


section Component

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem radical_normal : (CFSG.solvableRadical X).Normal :=
  Subgroup.sSup_normal _ fun _ hN => hN.1

omit [Finite X] in
theorem layer_sup_radical_normal :
    (Layer.subgroup X ⊔ CFSG.solvableRadical X).Normal := by
  have : (CFSG.solvableRadical X).Normal := radical_normal
  have : (Layer.subgroup X).Normal := Layer.normal X
  infer_instance

theorem radical_le_centralizer {T : Subgroup X} (hT : IsComponentOf T ⊤) :
    CFSG.solvableRadical X ≤ Subgroup.centralizer (T : Set X) := by
  have : (CFSG.solvableRadical X).Normal := radical_normal
  have : Group.IsSolvable (CFSG.solvableRadical X) :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical
  have hsub : IsSubnormal (CFSG.solvableRadical X) ⊤ :=
    isSubnormal_of_normal_subgroupOf le_top inferInstance
  have hcomm := Layer.commutes_with_solvable_subnormal (CFSG.solvableRadical X) hsub
  have hle : Layer.subgroup X ≤
      Subgroup.centralizer ((CFSG.solvableRadical X : Subgroup X) : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  intro r hr
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  exact (Subgroup.mem_centralizer_iff.mp (hle (Layer.component_le hT ht)) r hr).symm

theorem layer_sup_radical_le_normalizer {T : Subgroup X} (hT : IsComponentOf T ⊤) :
    Layer.subgroup X ⊔ CFSG.solvableRadical X ≤ Subgroup.normalizer (T : Set X) := by
  refine sup_le ?_ ((radical_le_centralizer hT).trans
    (Subgroup.centralizer_le_normalizer (T : Set X)))
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (Layer.component_le hT)).mp
    (Layer.normal_component hT)

theorem le_sup_centralizer_inf {T : Subgroup X} (hT : IsComponentOf T ⊤) :
    Layer.subgroup X ⊔ CFSG.solvableRadical X ≤
      T ⊔ (Subgroup.centralizer (T : Set X) ⊓ (Layer.subgroup X ⊔ CFSG.solvableRadical X)) := by
  refine sup_le ?_ ?_
  · show sSup {c : Subgroup X | IsComponentOf c ⊤} ≤ _
    refine sSup_le fun S hS => ?_
    by_cases hST : S = T
    · exact hST ▸ le_sup_left
    · have hcomm := LocalComponents.commute_of_ne S T hS hT hST
      have hSle : S ≤ Subgroup.centralizer (T : Set X) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
      exact (le_inf hSle ((Layer.component_le hS).trans le_sup_left)).trans le_sup_right
  · exact (le_inf (radical_le_centralizer hT) le_sup_right).trans le_sup_right

theorem central_two_group (hO : classicalInvolutionOddCore X = ⊥) {N T D : Subgroup X}
    (hN : IsSubnormal N ⊤) (hTN : T ≤ N) (hcomm : ∀ t ∈ T, ∀ d ∈ D, t * d = d * t)
    (hND : N ≤ T ⊔ D) : ∀ x ∈ T ⊓ D, ∃ j : ℕ, x ^ (2 ^ j) = 1 := by
  intro x hx
  have hxc : ∀ n ∈ N, n * x = x * n := by
    intro n hn
    obtain ⟨t, ht, d, hd, rfl⟩ := exists_mul_of_mem_sup hcomm (hND hn)
    have h1 : t * x = x * t := hcomm t ht x hx.2
    have h2 : x * d = d * x := hcomm x hx.1 d hd
    calc t * d * x = t * (d * x) := by group
      _ = t * (x * d) := by rw [h2]
      _ = (t * x) * d := by group
      _ = (x * t) * d := by rw [h1]
      _ = x * (t * d) := by group
  obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  refine ⟨a, ?_⟩
  set y : X := x ^ (2 ^ a) with hy
  have hyord : orderOf y = m := by
    rw [hy, orderOf_pow_of_dvd (pow_ne_zero a two_ne_zero) ⟨m, hord⟩, hord,
      Nat.mul_div_cancel_left _ (pow_pos two_pos a)]
  have hyN : y ∈ N := N.pow_mem (hTN hx.1) _
  have hyc : ∀ n ∈ N, Commute n y := fun n hn => by
    have hc : Commute n x := hxc n hn
    exact hc.pow_right (2 ^ a)
  have hS : Subgroup.zpowers y ≤ N := Subgroup.zpowers_le.mpr hyN
  have hcentS : N ≤ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup X) : Set X) := by
    intro n hn
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact ((hyc n hn).zpow_right k).symm.eq
  have hsubN : IsSubnormal (Subgroup.zpowers y) N :=
    isSubnormal_of_normal_subgroupOf hS
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hS).mpr hcentS)
  have hsub : IsSubnormal (Subgroup.zpowers y) ⊤ := isSubnormal_trans hsubN hN
  have hodd : Odd (Nat.card (Subgroup.zpowers y)) := by
    rw [Nat.card_zpowers, hyord]
    exact hm
  have hbot := eq_bot_of_isSubnormal_odd hO hsub hodd
  have hmem : y ∈ Subgroup.zpowers y := Subgroup.mem_zpowers y
  rw [hbot] at hmem
  exact Subgroup.mem_bot.mp hmem

end Component

end CFSG.ClassicalInvolution.Q3.M
