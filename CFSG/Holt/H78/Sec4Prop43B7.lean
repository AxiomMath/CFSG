module

public import CFSG.Holt.H78.Sec4Prop43B6

public section

namespace CFSG.Holt.H78

open Equiv Equiv.Perm MulAction CFSG.Holt CFSG.Open
open scoped Pointwise

theorem exists_eq_two_pow_add_of_testBit {n : ℕ} (hn : 4 ≤ n)
    (h : ∀ a a', 2 ≤ a → 2 ≤ a' → a ≠ a' → n.testBit a → ¬ n.testBit a') :
    ∃ a, 2 ≤ a ∧ 2 ^ a ≤ n ∧ n < 2 ^ a + 4 := by
  have hn0 : n ≠ 0 := by omega
  set a := n.log2 with ha
  have hle : 2 ^ a ≤ n := Nat.log2_self_le hn0
  have hlt : n < 2 ^ (a + 1) := Nat.lt_log2_self
  have ha2 : 2 ≤ a := (Nat.le_log2 hn0).mpr (by norm_num; omega)
  refine ⟨a, ha2, hle, ?_⟩
  by_contra hm
  push Not at hm
  set m := n - 2 ^ a with hmdef
  have hm4 : 4 ≤ m := by omega
  have hm0 : m ≠ 0 := by omega
  have hmlt : m < 2 ^ a := by rw [pow_succ] at hlt; omega
  have hc := Nat.testBit_log2 hm0
  have hc2 : 2 ≤ m.log2 := (Nat.le_log2 hm0).mpr (by norm_num; omega)
  have hca : m.log2 < a := (Nat.log2_lt hm0).mpr hmlt
  have hnm : n = 2 ^ a + m := by omega
  have hnc : n.testBit m.log2 = true := by
    rw [hnm, Nat.testBit_two_pow_add_gt hca]
    exact hc
  exact h a m.log2 ha2 hc2 (Nat.ne_of_gt hca) (Nat.testBit_log2 hn0) hnc

namespace AltConfig

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} (C : AltConfig G Ω α β)

theorem false_of_odd_two_pow_add_three (hS : Sec4Setting G Ω) (hαβ : α ≠ β)
    (hP : fusionIsSylowIn 2 C.calP C.calG) (hr : ∃ j, j ≠ C.i₁) {a : ℕ} (ha : 2 ≤ a)
    (hcard : Fintype.card (C.D.Ψc C.i₁) = 2 ^ a + 3)
    (hodd : ¬ C.Qimg C.i₁ ≤ alternatingGroup (C.D.Ψc C.i₁)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU := C.fusionIsSylowIn_Qimg_inf_alternatingGroup hS hP C.i₁
  set U := C.Qimg C.i₁ ⊓ alternatingGroup (C.D.Ψc C.i₁) with hUdef
  have h4 : 4 ≤ Fintype.card (C.D.Ψc C.i₁) := by have := C.D.five_le_card C.i₁; omega
  have hbit : (Fintype.card (C.D.Ψc C.i₁)).testBit 1 := by
    rw [hcard, Nat.testBit_two_pow_add_gt (by omega)]
    decide
  obtain ⟨x₀, hx₀⟩ := (testBit_card_iff_of_fusionIsSylowIn_alternatingGroup h4 hU 1).mp hbit
  rw [pow_one] at hx₀
  obtain ⟨u, v, huv, hO⟩ := Set.ncard_eq_two.mp (by rw [← Nat.card_coe_set_eq]; exact hx₀)
  have hOQ : ∀ y, orbit (C.Qimg C.i₁) y = orbit U y := C.orbit_Qimg_eq hS hP C.i₁
  have huO : u ∈ orbit U x₀ := by rw [hO]; exact Set.mem_insert _ _
  have hvO : v ∈ orbit U x₀ := by rw [hO]; exact Set.mem_insert_of_mem _ rfl
  set γ₁ := C.D.coord C.γ C.i₁ with hγ₁
  have hγO : γ₁ ∉ orbit U x₀ := by
    intro h
    have h1 : orbit U x₀ = {γ₁} := by
      rw [← orbit_eq_iff.mpr h, ← hOQ, C.orbit_Qimg_γ]
    rw [h1, Nat.card_unique] at hx₀
    omega
  have hγu : γ₁ ≠ u := fun h => hγO (h ▸ huO)
  have hγv : γ₁ ≠ v := fun h => hγO (h ▸ hvO)
  set τ := Equiv.swap u v with hτ
  obtain ⟨g, hgQ, hgA⟩ : ∃ g ∈ C.Qimg C.i₁, g ∉ alternatingGroup (C.D.Ψc C.i₁) := by
    by_contra h
    push Not at h
    exact hodd h
  obtain ⟨q₁, hq₁P, hq₁⟩ := C.exists_of_mem_Qimg hgQ
  have hgγ : g γ₁ = γ₁ := by rw [← hq₁]; exact C.kerCHom_apply_γ q₁
  have hτγ : τ γ₁ = γ₁ := Equiv.swap_apply_of_ne_of_ne hγu hγv
  have hgτ : g⁻¹ * τ ∈ alternatingGroup (C.D.Ψc C.i₁) := by
    rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_inv, Equiv.Perm.sign_swap huv]
    rw [Equiv.Perm.mem_alternatingGroup] at hgA
    rcases Int.units_eq_one_or (Equiv.Perm.sign g) with h | h
    · exact absurd h hgA
    · rw [h]
      decide
  obtain ⟨q₀, hq₀⟩ := C.exists_kerCHom_eq hS hgτ (by
    rw [Equiv.Perm.mul_apply, hτγ, Equiv.Perm.inv_eq_iff_eq, hgγ])
  have hτrange : τ ∈ (⊤ : Subgroup (C.kerC C.i₁)).map (C.kerCHom C.i₁) :=
    ⟨q₁ * q₀, trivial, by rw [map_mul, hq₁, hq₀, mul_inv_cancel_left]⟩
  have hτc : ∀ w ∈ C.Qimg C.i₁, w * τ * w⁻¹ = τ := by
    intro w hw
    have hwu : w u ∈ ({u, v} : Set (C.D.Ψc C.i₁)) := by
      rw [← hO, ← orbit_eq_iff.mpr huO, ← hOQ]
      exact ⟨⟨w, hw⟩, rfl⟩
    have hwv : w v ∈ ({u, v} : Set (C.D.Ψc C.i₁)) := by
      rw [← hO, ← orbit_eq_iff.mpr huO, ← hOQ]
      exact (orbit_eq_iff.mpr (show v ∈ orbit (C.Qimg C.i₁) u by
        rw [hOQ, orbit_eq_iff.mpr huO]; exact hvO)) ▸ ⟨⟨w, hw⟩, rfl⟩
    rw [hτ, ← Equiv.swap_apply_apply]
    have hne : w u ≠ w v := fun h => huv (w.injective h)
    rcases hwu with h1 | h1 <;> rcases hwv with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · rw [h1, h2]
    · rw [h1, h2, Equiv.swap_comm]
    · exact absurd (h1.trans h2.symm) hne
  have hsyl := fusionIsSylowIn_map (C.kerCHom C.i₁)
    (fusionIsSylowIn_subgroupOf_top (C.fusionIsSylowIn_kerC hP C.i₁))
  have hτ2 : IsPGroup 2 (Subgroup.zpowers τ) := by
    have hτo : orderOf τ ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by rw [pow_one, hτ, sq,
      Equiv.swap_mul_self])
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hτo
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hm])
  have hτN : Subgroup.zpowers τ ≤ Subgroup.normalizer (C.Qimg C.i₁ : Set (Equiv.Perm _)) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun w hw => ?_)
    exact mul_inv_eq_iff_eq_mul.mp (hτc w hw)
  have hsup := IsPGroup.to_sup_of_normal_left' (C.isPGroup_Qimg C.i₁) hτ2 hτN
  have hτQ : τ ∈ C.Qimg C.i₁ := by
    have heq : C.Qimg C.i₁ ⊔ Subgroup.zpowers τ = C.Qimg C.i₁ :=
      hsyl.2.2 _ (sup_le hsyl.1 ((Subgroup.zpowers_le).mpr hτrange)) hsup le_sup_left
    have : τ ∈ C.Qimg C.i₁ ⊔ Subgroup.zpowers τ := Subgroup.mem_sup_right (Subgroup.mem_zpowers τ)
    rw [heq] at this
    exact this
  set O : Set (C.D.Ψc C.i₁) := orbit U x₀ with hOdef
  set Λc : ∀ j, Set (C.D.Ψc j) := Function.update (fun _ => Set.univ) C.i₁ Oᶜ with hΛc
  have hΛ₁ : Λc C.i₁ = Oᶜ := Function.update_self _ _ _
  have hΛj : ∀ j, j ≠ C.i₁ → Λc j = Set.univ := fun j hj => Function.update_of_ne hj _ _
  have hstab : ∀ p ∈ C.calP, ∀ δ δ' : holtDelta G Ω α β, (δ' : Ω) = p • (δ : Ω) →
      (∀ j, C.D.coord δ j ∈ Λc j) → ∀ j, C.D.coord δ' j ∈ Λc j := by
    intro p hp δ δ' e hδ j
    by_cases hj : j = C.i₁
    · subst hj
      have hδ₁ := hδ C.i₁
      rw [hΛ₁] at hδ₁ ⊢
      rw [C.coord_smul_eq_calGHom ⟨p, C.calP_le_calG hp⟩ e]
      intro hO'
      have h1 := C.calGHom_mem_orbit hS hP (C.calP.inv_mem hp) hO'
      rw [← Equiv.Perm.mul_apply, ← map_mul] at h1
      have h2 : (⟨p⁻¹, C.calP_le_calG (C.calP.inv_mem hp)⟩ * ⟨p, C.calP_le_calG hp⟩ : C.calG) =
          1 := Subtype.ext (inv_mul_cancel p)
      rw [h2, map_one, Equiv.Perm.one_apply] at h1
      exact hδ₁ h1
    · rw [hΛj j hj]
      exact Set.mem_univ _
  have hmove : ∀ δ : holtDelta G Ω α β, ¬ (∀ j, C.D.coord δ j ∈ Λc j) → ∃ w ∈ C.calP,
      (∀ δ' : holtDelta G Ω α β, (∀ j, C.D.coord δ' j ∈ Λc j) → w • (δ' : Ω) = δ') ∧
        w • (δ : Ω) ≠ δ := by
    intro δ hδ
    have hδO : C.D.coord δ C.i₁ ∈ O := by
      by_contra hδO
      refine hδ fun j => ?_
      by_cases hj : j = C.i₁
      · subst hj
        rw [hΛ₁]
        exact hδO
      · rw [hΛj j hj]
        exact Set.mem_univ _
    refine C.exists_mem_calP_of_mem_Qimg_fix hτQ (Λc := Λc) (fun c hc => ?_) ?_
    · rw [hΛ₁, hO] at hc
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hc
      exact Equiv.swap_apply_of_ne_of_ne hc.1 hc.2
    · rw [hO] at hδO
      rcases hδO with h | h
      · rw [h, hτ, Equiv.swap_apply_left]
        exact huv.symm
      · rw [Set.mem_singleton_iff] at h
        rw [h, hτ, Equiv.swap_apply_right]
        exact huv
  have hne : ∃ δ : holtDelta G Ω α β, ¬ ∀ j, C.D.coord δ j ∈ Λc j := by
    refine ⟨C.coordEquiv.symm (Function.update (C.D.coord C.γ) C.i₁ x₀), fun h => ?_⟩
    have := h C.i₁
    rw [C.coord_coordEquiv_symm, Function.update_self, hΛ₁] at this
    exact this (mem_orbit_self x₀)
  have h₁ : 5 ≤ (Λc C.i₁).ncard := by
    rw [hΛ₁]
    have h1 := Set.ncard_add_ncard_compl O
    rw [← Nat.card_coe_set_eq O, hx₀, Nat.card_eq_fintype_card, hcard] at h1
    have : 2 ^ 2 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
    omega
  have hsize : ∀ j, (Λc j).ncard = 1 ∨ 5 ≤ (Λc j).ncard := by
    intro j
    right
    by_cases hj : j = C.i₁
    · subst hj
      exact h₁
    · rw [hΛj j hj, C.ncard_univ_Ψc]
      exact C.D.five_le_card j
  have hj' : ∃ j, j ≠ C.i₁ ∧ 5 ≤ (Λc j).ncard := by
    obtain ⟨j, hj⟩ := hr
    exact ⟨j, hj, by rw [hΛj j hj, C.ncard_univ_Ψc]; exact C.D.five_le_card j⟩
  have h5 := C.four_le_card_fixSet_of_stab_box hS hαβ (C.sylow.2.1.to_le inf_le_left)
    C.calP_le_calG Λc hstab hmove hne hsize h₁ hj'
  rw [C.fix_three] at h5
  omega

@[expose] def IsRStar : Prop :=
  fusionIsSylowIn 2 C.calP C.calG ∧ (∃ j, j ≠ C.i₁) ∧
    (∀ j k, j ≠ C.i₁ → k ≠ C.i₁ → ∃ p ∈ C.calP, C.MapsDir p j k) ∧
    (∀ j, j ≠ C.i₁ → Fintype.card (C.D.Ψc j) = 5) ∧
    (Fintype.card (C.D.Ψc C.i₁) = 5 ∨ ∃ a, 2 ≤ a ∧ Fintype.card (C.D.Ψc C.i₁) = 2 ^ a + 3 ∧
      C.Qimg C.i₁ ≤ alternatingGroup (C.D.Ψc C.i₁))

theorem isRStar_of_odd (hS : Sec4Setting G Ω) (hαβ : α ≠ β)
    (hT : Odd (Nat.card (twoPointKernel G Ω α β))) (hP : fusionIsSylowIn 2 C.calP C.calG)
    (hr : ∃ j, j ≠ C.i₁) : C.IsRStar := by
  classical
  have htrans : ∀ j k, j ≠ C.i₁ → k ≠ C.i₁ → ∃ p ∈ C.calP, C.MapsDir p j k := by
    by_contra h
    push Not at h
    obtain ⟨j, k, hj, hk, hjk⟩ := h
    exact C.false_of_not_mapsDir hS hαβ hP hj hk hjk
  obtain ⟨j₀, hj₀⟩ := hr
  have h2₁ : ∀ a a', 2 ≤ a → 2 ≤ a' → a ≠ a' → (Fintype.card (C.D.Ψc C.i₁)).testBit a →
      ¬ (Fintype.card (C.D.Ψc C.i₁)).testBit a' := fun a a' ha ha' haa' h h' =>
    C.false_of_two_bits_i₁ hS hαβ hP ⟨j₀, hj₀⟩ ha ha' haa' h h'
  have h2₀ : ∀ a a', 2 ≤ a → 2 ≤ a' → a ≠ a' → (Fintype.card (C.D.Ψc j₀)).testBit a →
      ¬ (Fintype.card (C.D.Ψc j₀)).testBit a' := fun a a' ha ha' haa' h h' =>
    C.false_of_two_bits_ne hS hαβ hP htrans hj₀ ha ha' haa' h h'
  obtain ⟨a, ha, ha1, ha2⟩ := exists_eq_two_pow_add_of_testBit
    (by have := C.D.five_le_card C.i₁; omega) h2₁
  obtain ⟨b, hb, hb1, hb2⟩ := exists_eq_two_pow_add_of_testBit
    (by have := C.D.five_le_card j₀; omega) h2₀
  have hodd₁ := C.D.odd_card_Ψc C.i₁
  have hmod₀ := C.mod4 j₀ hj₀
  have h4a : 4 ∣ 2 ^ a := (Nat.pow_dvd_pow 2 ha : 2 ^ 2 ∣ 2 ^ a)
  have h4b : 4 ∣ 2 ^ b := (Nat.pow_dvd_pow 2 hb : 2 ^ 2 ∣ 2 ^ b)
  have hn₀ : Fintype.card (C.D.Ψc j₀) = 2 ^ b + 1 := by
    obtain ⟨t, ht⟩ := h4b
    omega
  have hb2' : b = 2 := by
    by_contra hb3
    exact C.false_of_half_ne hS hαβ hT hP htrans hj₀ (by omega) hn₀
  subst hb2'
  have hn₅ : ∀ j, j ≠ C.i₁ → Fintype.card (C.D.Ψc j) = 5 := by
    intro j hj
    obtain ⟨p, hp, hpj⟩ := htrans j₀ j hj₀ hj
    rw [← C.card_Ψc_eq_of_mapsDir hp hpj, hn₀]
    norm_num
  refine ⟨hP, ⟨j₀, hj₀⟩, htrans, hn₅, ?_⟩
  obtain ⟨t, ht⟩ := h4a
  rcases hodd₁ with ⟨u, hu⟩
  have hcases : Fintype.card (C.D.Ψc C.i₁) = 2 ^ a + 1 ∨
      Fintype.card (C.D.Ψc C.i₁) = 2 ^ a + 3 := by omega
  rcases hcases with h1 | h3
  ·
    left
    by_cases ha3 : 3 ≤ a
    · exact (C.false_of_half_i₁ hS hαβ hT hP ⟨j₀, hj₀⟩ ha3 h1).elim
    · rw [h1, show a = 2 by omega]
      norm_num
  · right
    refine ⟨a, ha, h3, ?_⟩
    by_contra hodd
    exact C.false_of_odd_two_pow_add_three hS hαβ hP ⟨j₀, hj₀⟩ ha h3 hodd

theorem false_of_odd_of_two_le_of_isRStar (hS : Sec4Setting G Ω) (hαβ : α ≠ β)
    (hT : Odd (Nat.card (twoPointKernel G Ω α β))) (hr : 2 ≤ Fintype.card C.D.ι)
    (hRstar : ∀ C' : AltConfig G Ω α β, C'.D = C.D → C'.IsRStar → False) : False := by
  obtain ⟨C', hD, -, -, -, hP⟩ := C.exists_sylow hS hαβ
  have hr' : 2 ≤ Fintype.card C'.D.ι := by
    rw [hD]
    exact hr
  obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card (by omega) C'.i₁
  exact hRstar C' hD (C'.isRStar_of_odd hS hαβ hT hP ⟨j, hj⟩)

end AltConfig

end CFSG.Holt.H78
