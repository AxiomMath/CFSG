module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Q8b

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] {a₁ b₁ a₂ b₂ z : G}

theorem y6q8_sqz_iff (h : Y6ARel a₁ b₁ a₂ b₂ z) (hz : z ≠ 1)
    (hA : Nat.card ↥(closure {a₁, b₁, a₂, b₂} : Subgroup G) = 32) :
    ∀ a ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G), a ^ 2 = z ↔
      (a ∈ (closure {a₁, b₁} : Subgroup G) ∨ a ∈ (closure {a₂, b₂} : Subgroup G)) ∧ a ≠ 1 ∧
        a ≠ z := by
  intro a ha
  constructor
  · intro hsq
    obtain ⟨u, hu, w, hw, rfl⟩ := y6q8_A_elems h a ha
    have hcomm : Commute u w := y6q8_commUW h u hu w hw
    have hsq' : u ^ 2 * w ^ 2 = z := by
      have hs := y6q8_sq_mul h u (y6q8_U_le_A hu) w (y6q8_W_le_A hw)
      calc u ^ 2 * w ^ 2 = u ^ 2 * w ^ 2 * ⁅w, u⁆ := by
            rw [commutatorElement_eq_one_iff_mul_comm.mpr hcomm.eq.symm, mul_one]
        _ = z := by rw [← hs]; exact hsq
    have ha1 : u * w ≠ 1 := fun h1 => hz (by rw [← hsq, h1]; simp)
    have haz : u * w ≠ z := fun h1 => hz (by rw [← hsq, h1, h.z_sq])
    have hmem : u * w ∈ (closure {a₁, b₁} : Subgroup G) ∨
        u * w ∈ (closure {a₂, b₂} : Subgroup G) := by
      by_cases hwZ : w = 1 ∨ w = z
      · left
        have hwU : w ∈ (closure {a₁, b₁} : Subgroup G) := by
          rcases hwZ with rfl | rfl
          · exact one_mem _
          · rw [← h.a1_sq]; exact pow_mem (Subgroup.subset_closure (by simp)) 2
        exact mul_mem hu hwU
      · right
        push Not at hwZ
        have hzsq : z * z = 1 := by simpa [pow_two] using h.z_sq
        have hw2 : w ^ 2 = z := (y6q8_sq_W h w hw).2 hwZ.1 hwZ.2
        have hu2 : u ^ 2 = 1 := by
          have hh := hsq'
          rw [hw2] at hh
          calc u ^ 2 = u ^ 2 * (z * z) := by rw [hzsq, mul_one]
            _ = (u ^ 2 * z) * z := (mul_assoc _ _ _).symm
            _ = z * z := by rw [hh]
            _ = 1 := hzsq
        have huW : u ∈ (closure {a₂, b₂} : Subgroup G) := by
          by_cases hu1 : u = 1
          · rw [hu1]; exact one_mem _
          · by_cases huz : u = z
            · rw [huz, ← h.a2_sq]; exact pow_mem (Subgroup.subset_closure (by simp)) 2
            · exact absurd ((y6q8_sq_U h u hu).2 hu1 huz)
                (by rw [hu2]; exact fun hh => hz hh.symm)
        exact mul_mem huW hw
    exact ⟨hmem, ha1, haz⟩
  · rintro ⟨hUW, h1, hz'⟩
    rcases hUW with hu | hw
    · exact (y6q8_sq_U h a hu).2 h1 hz'
    · exact (y6q8_sq_W h a hw).2 h1 hz'

theorem y6q8_card (h : Y6ARel a₁ b₁ a₂ b₂ z) (hz : z ≠ 1)
    (hA : Nat.card ↥(closure {a₁, b₁, a₂, b₂} : Subgroup G) = 32) :
    Nat.card ↥{a : G | a ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G) ∧ a ^ 2 = z} = 12 ∧
      Nat.card ↥{a : G | a ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G) ∧ a ^ 2 = 1} = 20 := by
  set A : Subgroup G := closure {a₁, b₁, a₂, b₂} with hAdef
  set U : Subgroup G := closure {a₁, b₁} with hUdef
  set W : Subgroup G := closure {a₂, b₂} with hWdef
  set Sz : Set G := {a : G | a ∈ A ∧ a ^ 2 = z} with hSzdef
  set S1 : Set G := {a : G | a ∈ A ∧ a ^ 2 = 1} with hS1def
  obtain ⟨hUcard, hWcard, hinter⟩ := y6q8_card_UW h hz hA
  have hUsubA : U ≤ A := y6q8_U_le_A
  have hWsubA : W ≤ A := y6q8_W_le_A
  haveI : Finite ↥A := Nat.finite_of_card_ne_zero (by rw [hA]; decide)
  have hfinA : (A : Set G).Finite := Set.finite_coe_iff.mp inferInstance
  have hfinU : (U : Set G).Finite := hfinA.subset hUsubA
  have hfinW : (W : Set G).Finite := hfinA.subset hWsubA
  have hAncard : (A : Set G).ncard = 32 := by change Nat.card ↥A = 32; exact hA
  have hUncard : (U : Set G).ncard = 8 := by change Nat.card ↥U = 8; exact hUcard
  have hWncard : (W : Set G).ncard = 8 := by change Nat.card ↥W = 8; exact hWcard
  have hZfin : ({1, z} : Set G).Finite := (Set.finite_singleton z).insert 1
  have hZcard : ({1, z} : Set G).ncard = 2 := Set.ncard_pair (fun h1 => hz h1.symm)
  have hinter' : (U : Set G) ∩ (W : Set G) = ({1, z} : Set G) := by
    ext x
    rw [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact hinter x
  have hUWcard : ((U : Set G) ∪ (W : Set G)).ncard = 14 := by
    have hh := Set.ncard_union_add_ncard_inter (U : Set G) (W : Set G) hfinU hfinW
    rw [hinter', hZcard, hUncard, hWncard] at hh
    omega
  have hSz_eq : Sz = ((U : Set G) ∪ (W : Set G)) \ ({1, z} : Set G) := by
    rw [hSzdef]
    ext x
    constructor
    · rintro ⟨hxA, hx2⟩
      obtain ⟨hUW', h1, h2⟩ := (y6q8_sqz_iff h hz hA x hxA).mp hx2
      refine ⟨hUW', ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨h1, h2⟩
    · rintro ⟨hUW', hnot⟩
      have hxA : x ∈ A := by
        rcases hUW' with hx | hx
        · exact hUsubA hx
        · exact hWsubA hx
      rw [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hnot
      exact ⟨hxA, (y6q8_sqz_iff h hz hA x hxA).mpr ⟨hUW', hnot.1, hnot.2⟩⟩
  have hSzsub : ({1, z} : Set G) ⊆ (U : Set G) ∪ (W : Set G) := by
    rw [← hinter']; exact Set.inter_subset_left.trans Set.subset_union_left
  have hSzncard : Sz.ncard = 12 := by
    rw [hSz_eq, Set.ncard_sdiff hSzsub hZfin, hUWcard, hZcard]
  have hS1_eq : S1 = (A : Set G) \ Sz := by
    rw [hS1def, hSzdef]
    ext x
    constructor
    · rintro ⟨hxA, hx1⟩
      exact ⟨hxA, fun hx2 => hz (by rw [← hx2.2, hx1])⟩
    · rintro ⟨hxA, hnot⟩
      exact ⟨hxA, (y6q8_sq_cases h x hxA).elim id fun hz' => absurd ⟨hxA, hz'⟩ hnot⟩
  have hSzsubA : Sz ⊆ (A : Set G) := fun x hx => by rw [hSzdef] at hx; exact hx.1
  have hS1ncard : S1.ncard = 20 := by
    rw [hS1_eq, Set.ncard_sdiff hSzsubA (hfinA.subset hSzsubA), hAncard, hSzncard]
  constructor
  · change Sz.ncard = 12; exact hSzncard
  · change S1.ncard = 20; exact hS1ncard

theorem y6q8_gen_sq1 (h : Y6ARel a₁ b₁ a₂ b₂ z) (hz : z ≠ 1)
    (hA : Nat.card ↥(closure {a₁, b₁, a₂, b₂} : Subgroup G) = 32) :
    closure {a : G | a ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G) ∧ a ^ 2 = 1} =
      (closure {a₁, b₁, a₂, b₂} : Subgroup G) := by
  set A : Subgroup G := closure {a₁, b₁, a₂, b₂} with hAdef
  set S : Set G := {a : G | a ∈ A ∧ a ^ 2 = 1} with hSdef
  set Scl : Subgroup G := closure S with hScldef
  have hScard : Nat.card ↥S = 20 := by simpa only [hSdef] using (y6q8_card h hz hA).2
  have hScl_le_A : Scl ≤ A := by
    rw [hScldef, Subgroup.closure_le]
    intro x hx
    rw [hSdef] at hx
    exact hx.1
  haveI : Finite ↥A := Nat.finite_of_card_ne_zero (by rw [hA]; decide)
  haveI : Finite ↥Scl := Finite.of_injective (fun x => (⟨x.1, hScl_le_A x.2⟩ : ↥A))
    (by intro x y hxy; exact Subtype.ext (congrArg (Subtype.val : ↥A → G) hxy))
  have hle : Nat.card ↥S ≤ Nat.card ↥Scl := by
    refine Nat.card_le_card_of_injective (fun s : ↥S => (⟨s.1, ?_⟩ : ↥Scl)) ?_
    · rw [hScldef]; exact Subgroup.subset_closure s.2
    · intro x y hxy; exact Subtype.ext (congrArg (Subtype.val : ↥Scl → G) hxy)
  have hcard32 : Nat.card ↥Scl = 32 := by
    have hdvd : Nat.card ↥Scl ∣ 32 := by rw [← hA]; exact Subgroup.card_dvd_of_le hScl_le_A
    have h20 : 20 ≤ Nat.card ↥Scl := by rw [hScard] at hle; exact hle
    obtain ⟨k, hk⟩ := hdvd
    have hkle : k ≤ 1 := by
      by_contra hk2
      have hk2' : 2 ≤ k := by omega
      have hmul : 20 * 2 ≤ Nat.card ↥Scl * k := Nat.mul_le_mul h20 hk2'
      omega
    have hk1 : k = 1 := by
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · rw [hk0, Nat.mul_zero] at hk; omega
      · omega
    rw [hk1, Nat.mul_one] at hk
    omega
  exact Subgroup.eq_of_le_of_card_ge hScl_le_A (by simp [hcard32, hA])

theorem y6q8_comm_sq1 (h : Y6ARel a₁ b₁ a₂ b₂ z) (hz : z ≠ 1)
    (hA : Nat.card ↥(closure {a₁, b₁, a₂, b₂} : Subgroup G) = 32) {x : G}
    (hx : x ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G))
    (hc : ∀ a ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G), a ^ 2 = 1 → x * a = a * x) :
    x = 1 ∨ x = z := by
  have hgen := y6q8_gen_sq1 h hz hA
  have hxcomm : ∀ b ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G), x * b = b * x := by
    intro b hb
    have hb' : b ∈ closure {a : G | a ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G) ∧
        a ^ 2 = 1} := by rw [hgen]; exact hb
    have hcomm : Commute x b := by
      refine Subgroup.closure_induction (p := fun b _ => Commute x b) ?_ ?_ ?_ ?_ hb'
      · intro a ha
        rw [commute_iff_eq]
        exact hc a ha.1 ha.2
      · exact Commute.one_right x
      · intro y c _ _ hy hc'
        exact Commute.mul_right hy hc'
      · intro y _ hy
        exact Commute.inv_right hy
    exact hcomm.eq
  exact y6q8_cen h hz hA x hx hxcomm

end CFSG.OddStandard.HigherRank.YamadaG23
