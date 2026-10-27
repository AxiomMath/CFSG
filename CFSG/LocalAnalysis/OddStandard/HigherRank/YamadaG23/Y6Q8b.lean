module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Q8a2
public import Mathlib.Data.ZMod.QuotientGroup

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] {a₁ b₁ a₂ b₂ z : G}

theorem y6q8_commUW (h : Y6ARel a₁ b₁ a₂ b₂ z) :
    ∀ u ∈ (closure {a₁, b₁} : Subgroup G),
      ∀ w ∈ (closure {a₂, b₂} : Subgroup G), Commute u w := by
  have hgen : ∀ x ∈ ({a₁, b₁} : Set G), ∀ y ∈ ({a₂, b₂} : Set G), Commute x y := by
    intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact commutatorElement_eq_one_iff_commute.mp h.a1a2
    · exact commutatorElement_eq_one_iff_commute.mp h.a1b2
    · exact commutatorElement_eq_one_iff_commute.mp h.b1a2
    · exact commutatorElement_eq_one_iff_commute.mp h.b1b2
  intro u hu
  refine Subgroup.closure_induction (p := fun u _ =>
    ∀ w ∈ (closure {a₂, b₂} : Subgroup G), Commute u w) ?_ ?_ ?_ ?_ hu
  · intro x hx w hw
    exact Subgroup.closure_induction (p := fun w _ => Commute x w)
      (fun y hy => hgen x hx y hy)
      (Commute.one_right x)
      (fun y c _ _ hy hc => Commute.mul_right hy hc)
      (fun y _ hy => Commute.inv_right hy) hw
  · intro w _
    exact Commute.one_left w
  · intro x y _ _ hx hy w hw
    exact Commute.mul_left (hx w hw) (hy w hw)
  · intro x _ hx w hw
    exact Commute.inv_left (hx w hw)

private theorem y6q8_not_comm_of_commutator {x y w : G}
    (hxy : ⁅x, y⁆ = w) (hw : w ≠ 1) : ¬ x * y = y * x := by
  intro h
  exact hw (by rw [← hxy, commutatorElement_eq_one_iff_mul_comm]; exact h)

private theorem y6q8_mul_z_comm_iff (h : Y6ARel a₁ b₁ a₂ b₂ z) {w c : G}
    (hw : w ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G))
    (hc : c ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G)) :
    Commute (w * z) c ↔ Commute w c := by
  have hzc : z * c = c * z := (y6q8_z_central h c hc).symm
  rw [commute_iff_eq, commute_iff_eq]
  constructor
  · intro hh
    have hh' : (w * c) * z = (c * w) * z := by
      calc (w * c) * z = w * (c * z) := mul_assoc w c z
        _ = w * (z * c) := by rw [← hzc]
        _ = (w * z) * c := (mul_assoc w z c).symm
        _ = c * (w * z) := hh
        _ = (c * w) * z := (mul_assoc c w z).symm
    exact mul_right_cancel hh'
  · intro hh
    calc (w * z) * c = w * (z * c) := mul_assoc w z c
      _ = w * (c * z) := by rw [hzc]
      _ = (w * c) * z := (mul_assoc w c z).symm
      _ = (c * w) * z := by rw [hh]
      _ = c * (w * z) := mul_assoc c w z

private theorem y6q8_pair_cen (h : Y6ARel a₁ b₁ a₂ b₂ z) {x y : G}
    (hlist : ∀ u ∈ (closure {x, y} : Subgroup G),
      u = 1 ∨ u = z ∨ u = x ∨ u = x * z ∨ u = y ∨ u = y * z ∨ u = x * y ∨
        u = x * y * z)
    (hcomm : ⁅x, y⁆ = z) (hz : z ≠ 1) {u : G} (hu : u ∈ (closure {x, y} : Subgroup G))
    (hxA : x ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G))
    (hyA : y ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G))
    (h1 : Commute u x) (h2 : Commute u y) : u = 1 ∨ u = z := by
  rcases hlist u hu with hu1 | hu2 | hu3 | hu4 | hu5 | hu6 | hu7 | hu8
  · exact Or.inl hu1
  · exact Or.inr hu2
  · subst hu3
    exact absurd h2.eq (y6q8_not_comm_of_commutator hcomm hz)
  · subst hu4
    exact absurd ((y6q8_mul_z_comm_iff h hxA hyA).mp h2).eq
      (y6q8_not_comm_of_commutator hcomm hz)
  · subst hu5
    exact absurd h1.eq.symm (y6q8_not_comm_of_commutator hcomm hz)
  · subst hu6
    exact absurd ((y6q8_mul_z_comm_iff h hyA hxA).mp h1).eq.symm
      (y6q8_not_comm_of_commutator hcomm hz)
  · subst hu7
    have hh' : x * y = y * x := by
      have := h1.eq
      rw [mul_assoc] at this
      exact (mul_left_cancel this).symm
    exact absurd hh' (y6q8_not_comm_of_commutator hcomm hz)
  · subst hu8
    have hh : Commute (x * y) x :=
      (y6q8_mul_z_comm_iff h (mul_mem hxA hyA) hxA).mp h1
    have hh' : x * y = y * x := by
      have := hh.eq
      rw [mul_assoc] at this
      exact (mul_left_cancel this).symm
    exact absurd hh' (y6q8_not_comm_of_commutator hcomm hz)

theorem y6q8_U_le_A :
    (closure {a₁, b₁} : Subgroup G) ≤ (closure {a₁, b₁, a₂, b₂} : Subgroup G) := by
  apply Subgroup.closure_mono
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  tauto

theorem y6q8_W_le_A :
    (closure {a₂, b₂} : Subgroup G) ≤ (closure {a₁, b₁, a₂, b₂} : Subgroup G) := by
  apply Subgroup.closure_mono
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  tauto

private theorem y6q8_cen_aux (h : Y6ARel a₁ b₁ a₂ b₂ z) (hz : z ≠ 1)
    (hA : Nat.card ↥(closure {a₁, b₁, a₂, b₂} : Subgroup G) = 32) :
    ∀ a ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G),
      (∀ b ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G), a * b = b * a) → a = 1 ∨ a = z := by
  intro a ha hcomm
  obtain ⟨u, hu, w, hw, rfl⟩ := y6q8_A_elems h a ha
  have hA1 : a₁ ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G) :=
    Subgroup.subset_closure (by simp)
  have hB1 : b₁ ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G) :=
    Subgroup.subset_closure (by simp)
  have hA2 : a₂ ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G) :=
    Subgroup.subset_closure (by simp)
  have hB2 : b₂ ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G) :=
    Subgroup.subset_closure (by simp)
  have hcu : ∀ c ∈ ({a₁, b₁} : Set G), Commute u c := by
    intro c hc
    have h1 : Commute ((u * w) * w⁻¹) c :=
      Commute.mul_left (hcomm c (y6q8_U_le_A (Subgroup.subset_closure hc)))
        (Commute.inv_left (Commute.symm (y6q8_commUW h c (Subgroup.subset_closure hc) w hw)))
    simpa using h1
  have hcw : ∀ c ∈ ({a₂, b₂} : Set G), Commute w c := by
    intro c hc
    have h1 : Commute (u⁻¹ * (u * w)) c :=
      Commute.mul_left (Commute.inv_left (y6q8_commUW h u hu c (Subgroup.subset_closure hc)))
        (hcomm c (y6q8_W_le_A (Subgroup.subset_closure hc)))
    simpa using h1
  have huZ := y6q8_pair_cen h (y6q8_U_elems h) h.comm1 hz hu hA1 hB1
    (hcu a₁ (by simp)) (hcu b₁ (by simp))
  have hwZ := y6q8_pair_cen h (y6q8_W_elems h) h.comm2 hz hw hA2 hB2
    (hcw a₂ (by simp)) (hcw b₂ (by simp))
  rcases huZ with hu1 | hu2 <;> rcases hwZ with hw1 | hw2
  · exact Or.inl (by rw [hu1, hw1, one_mul])
  · exact Or.inr (by rw [hu1, hw2, one_mul])
  · exact Or.inr (by rw [hu2, hw1, mul_one])
  · exact Or.inl (by rw [hu2, hw2]; simpa [pow_two] using h.z_sq)

theorem y6q8_sq_cases (h : Y6ARel a₁ b₁ a₂ b₂ z) :
    ∀ a ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G), a ^ 2 = 1 ∨ a ^ 2 = z := by
  intro a ha
  obtain ⟨u, hu, w, hw, rfl⟩ := y6q8_A_elems h a ha
  have hcomm : Commute u w := y6q8_commUW h u hu w hw
  have hsq := y6q8_sq_mul h u (y6q8_U_le_A hu) w (y6q8_W_le_A hw)
  rw [hsq, commutatorElement_eq_one_iff_mul_comm.mpr hcomm.eq.symm, mul_one]
  obtain ⟨hu1, hu2⟩ := y6q8_sq_U h u hu
  obtain ⟨hw1, hw2⟩ := y6q8_sq_W h w hw
  have hzsq : z * z = 1 := by simpa [pow_two] using h.z_sq
  by_cases huZ : u = 1 ∨ u = z
  · rw [hu1 huZ, one_mul]
    by_cases hwZ : w = 1 ∨ w = z
    · rw [hw1 hwZ]; left; rfl
    · push Not at hwZ
      rw [hw2 hwZ.1 hwZ.2]; right; rfl
  · push Not at huZ
    rw [hu2 huZ.1 huZ.2]
    by_cases hwZ : w = 1 ∨ w = z
    · rw [hw1 hwZ, mul_one]; right; rfl
    · push Not at hwZ
      rw [hw2 hwZ.1 hwZ.2, hzsq]; left; rfl

private theorem y6q8_pair_card (h : Y6ARel a₁ b₁ a₂ b₂ z) (hz : z ≠ 1) {x y : G}
    (helems : ∀ u ∈ (closure {x, y} : Subgroup G),
      u = 1 ∨ u = z ∨ u = x ∨ u = x * z ∨ u = y ∨ u = y * z ∨ u = x * y ∨
        u = x * y * z)
    (hx2 : x ^ 2 = z) (hcomm : ⁅x, y⁆ = z)
    (hxmem : x ∈ (closure {x, y} : Subgroup G))
    (hymem : y ∈ (closure {x, y} : Subgroup G)) :
    Nat.card ↥(closure {x, y} : Subgroup G) = 8 := by
  classical
  have hsub : ((closure {x, y} : Subgroup G) : Set G) ⊆
      (↑({1, z, x, x * z, y, y * z, x * y, x * y * z} : Finset G) : Set G) := by
    intro u hu
    rcases helems u hu with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
    · rw [h1]; simp
    · rw [h2]; simp
    · rw [h3]; simp
    · rw [h4]; simp
    · rw [h5]; simp
    · rw [h6]; simp
    · rw [h7]; simp
    · rw [h8]; simp
  haveI : Finite ↥(closure {x, y} : Subgroup G) :=
    Set.finite_coe_iff.mp ((Finset.finite_toSet _).subset hsub)
  have hle : Nat.card ↥(closure {x, y} : Subgroup G) ≤ 8 := by
    change ((closure {x, y} : Subgroup G) : Set G).ncard ≤ 8
    calc ((closure {x, y} : Subgroup G) : Set G).ncard
        ≤ (↑({1, z, x, x * z, y, y * z, x * y, x * y * z} : Finset G) : Set G).ncard :=
          Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ = ({1, z, x, x * z, y, y * z, x * y, x * y * z} : Finset G).card :=
          Set.ncard_coe_finset _
      _ ≤ 8 := by
          have h6 : ({x, x * z, y, y * z, x * y, x * y * z} : Finset G).card ≤ 6 :=
            Finset.card_le_six
          have h7 : ({z, x, x * z, y, y * z, x * y, x * y * z} : Finset G).card ≤ 7 := by
            have := Finset.card_insert_le z ({x, x * z, y, y * z, x * y, x * y * z} : Finset G)
            omega
          have := Finset.card_insert_le 1 ({z, x, x * z, y, y * z, x * y, x * y * z} : Finset G)
          omega
  have horder : orderOf x = 4 := by
    have hnot : ¬ x ^ 2 ^ (1 : ℕ) = 1 := by rw [pow_one, hx2]; exact hz
    have hfin : x ^ 2 ^ (1 + 1) = 1 := by
      change x ^ 4 = 1
      rw [show (4 : ℕ) = 2 * 2 by omega, pow_mul, hx2, h.z_sq]
    simpa using orderOf_eq_prime_pow (p := 2) (n := 1) (x := x) hnot hfin
  have hzpow : Nat.card ↥(Subgroup.zpowers x) = 4 := by rw [Nat.card_zpowers, horder]
  have hle' : Subgroup.zpowers x ≤ (closure {x, y} : Subgroup G) :=
    Subgroup.zpowers_le.mpr hxmem
  have hsubcard : Nat.card ↥((Subgroup.zpowers x).subgroupOf
      (closure {x, y} : Subgroup G)) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle').toEquiv, hzpow]
  have hidx : ((Subgroup.zpowers x).subgroupOf (closure {x, y} : Subgroup G)).index * 4 =
      Nat.card ↥(closure {x, y} : Subgroup G) := by
    rw [← hsubcard]; exact Subgroup.index_mul_card _
  haveI : Nonempty ↥(closure {x, y} : Subgroup G) := ⟨⟨1, one_mem _⟩⟩
  have hpos : 0 < Nat.card ↥(closure {x, y} : Subgroup G) := Nat.card_pos
  have hidxle : ((Subgroup.zpowers x).subgroupOf
      (closure {x, y} : Subgroup G)).index ≤ 2 := by omega
  have hidxne : ((Subgroup.zpowers x).subgroupOf
      (closure {x, y} : Subgroup G)).index ≠ 1 := by
    intro h1
    have htop := Subgroup.index_eq_one.mp h1
    have hmem : y ∈ Subgroup.zpowers x := by
      have hb : (⟨y, hymem⟩ : ↥(closure {x, y} : Subgroup G)) ∈
          (Subgroup.zpowers x).subgroupOf (closure {x, y} : Subgroup G) := by
        rw [htop]; exact Subgroup.mem_top _
      simpa using Subgroup.mem_subgroupOf.mp hb
    have hccomm : x * y = y * x := by
      have hcent : Subgroup.zpowers x ≤ Subgroup.centralizer ({x} : Set G) :=
        Subgroup.zpowers_le.mpr (by
          rw [Subgroup.mem_centralizer_iff]
          intro t ht
          rw [Set.mem_singleton_iff] at ht
          rw [ht])
      exact (Subgroup.mem_centralizer_iff.mp (hcent hmem)) x (Set.mem_singleton x)
    exact y6q8_not_comm_of_commutator hcomm hz hccomm
  have hidx2 : ((Subgroup.zpowers x).subgroupOf
      (closure {x, y} : Subgroup G)).index = 2 := by omega
  have := hidx
  rw [hidx2] at this
  omega

theorem y6q8_card_UW (h : Y6ARel a₁ b₁ a₂ b₂ z) (hz : z ≠ 1)
    (hA : Nat.card ↥(closure {a₁, b₁, a₂, b₂} : Subgroup G) = 32) :
    Nat.card ↥(closure {a₁, b₁} : Subgroup G) = 8 ∧ Nat.card ↥(closure {a₂, b₂} : Subgroup G) = 8 ∧
      ∀ x : G, x ∈ (closure {a₁, b₁} : Subgroup G) ∧ x ∈ (closure {a₂, b₂} : Subgroup G) ↔
        x = 1 ∨ x = z := by
  have ha1U : a₁ ∈ (closure {a₁, b₁} : Subgroup G) := Subgroup.subset_closure (by simp)
  have hb1U : b₁ ∈ (closure {a₁, b₁} : Subgroup G) := Subgroup.subset_closure (by simp)
  have ha2W : a₂ ∈ (closure {a₂, b₂} : Subgroup G) := Subgroup.subset_closure (by simp)
  have hb2W : b₂ ∈ (closure {a₂, b₂} : Subgroup G) := Subgroup.subset_closure (by simp)
  have hUcard := y6q8_pair_card h hz (y6q8_U_elems h) h.a1_sq h.comm1 ha1U hb1U
  have hWcard := y6q8_pair_card h hz (y6q8_W_elems h) h.a2_sq h.comm2 ha2W hb2W
  refine ⟨hUcard, hWcard, ?_⟩
  intro x
  constructor
  · rintro ⟨hxU, hxW⟩
    refine y6q8_cen_aux h hz hA x (y6q8_U_le_A hxU) ?_
    intro b hb
    have hcomm : Commute x b := by
      refine Subgroup.closure_induction (p := fun b _ => Commute x b) ?_ ?_ ?_ ?_ hb
      · intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with hy1 | hy2 | hy3 | hy4
        · rw [hy1]; exact Commute.symm (y6q8_commUW h a₁ ha1U x hxW)
        · rw [hy2]; exact Commute.symm (y6q8_commUW h b₁ hb1U x hxW)
        · rw [hy3]; exact y6q8_commUW h x hxU a₂ ha2W
        · rw [hy4]; exact y6q8_commUW h x hxU b₂ hb2W
      · exact Commute.one_right x
      · intro y c _ _ hy hc
        exact Commute.mul_right hy hc
      · intro y _ hy
        exact Commute.inv_right hy
    exact hcomm.eq
  · rintro (rfl | rfl)
    · exact ⟨one_mem _, one_mem _⟩
    · exact ⟨by rw [← h.a1_sq]; exact pow_mem ha1U 2, by rw [← h.a2_sq]; exact pow_mem ha2W 2⟩

theorem y6q8_cen (h : Y6ARel a₁ b₁ a₂ b₂ z) (hz : z ≠ 1)
    (hA : Nat.card ↥(closure {a₁, b₁, a₂, b₂} : Subgroup G) = 32) :
    ∀ a ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G),
      (∀ b ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G), a * b = b * a) → a = 1 ∨ a = z :=
  y6q8_cen_aux h hz hA

end CFSG.OddStandard.HigherRank.YamadaG23
