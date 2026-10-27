module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8L7NoLayerBase

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.L7

open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL
open scoped Pointwise

section Blocks

@[expose] def blocks (s : Fin 7) : Finset (Finset (Fin 7)) :=
  insert {s} ((fanoLines.toFinset.filter fun ℓ => s ∈ ℓ).image fun ℓ => ℓ.erase s)

theorem blocks_card : ∀ s : Fin 7, (blocks s).card = 4 := by decide +kernel

theorem blocks_card_le : ∀ s : Fin 7, ∀ B ∈ blocks s, B.card ≤ 2 := by decide +kernel

theorem blocks_cover : ∀ s : Fin 7, ∀ x : Fin 7, ∃ B ∈ blocks s, x ∈ B := by decide +kernel

abbrev Qstab (s : Fin 7) : Subgroup (Equiv.Perm (Fin 7)) :=
  MulAction.stabilizer (Equiv.Perm (Fin 7)) ((blocks s : Finset (Finset (Fin 7))) : Set (Finset (Fin 7)))

theorem mem_Qstab {s : Fin 7} {g : Equiv.Perm (Fin 7)} : g ∈ Qstab s ↔ ∀ B ∈ blocks s, g • B ∈ blocks s := by
  rw [Qstab, MulAction.stabilizer_coe_finset]
  exact MulAction.mem_stabilizer_finset'

end Blocks

section Solvable

theorem perm_sq_of_mapsTo {X : Type*} [DecidableEq X] (g : Equiv.Perm X) {B : Finset X} (hB : B.card ≤ 2)
    (hmap : ∀ x ∈ B, g x ∈ B) {x : X} (hx : x ∈ B) : g (g x) = x := by
  by_cases h : g x = x
  · rw [h, h]
  · have hsub : ({x, g x} : Finset X) ⊆ B := by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hx
      · rw [Finset.mem_singleton.mp hy]
        exact hmap x hx
    have hcard : ({x, g x} : Finset X).card = 2 := Finset.card_pair (Ne.symm h)
    have hBe : ({x, g x} : Finset X) = B := Finset.eq_of_subset_of_card_le hsub (by omega)
    have hmem : g (g x) ∈ ({x, g x} : Finset X) := by
      rw [hBe]
      exact hmap _ (hmap x hx)
    rcases Finset.mem_insert.mp hmem with h1 | h1
    · exact h1
    · exact absurd (g.injective (Finset.mem_singleton.mp h1)) h

theorem isSolvable_of_sq_eq_one {G : Type*} [Group G] (h : ∀ x : G, x * x = 1) : Group.IsSolvable G :=
  Group.isSolvable_of_comm fun a b => by
    have e1 : a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right (h (a * b))).symm
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (h a), inv_eq_of_mul_eq_one_right (h b)] at e1
    exact e1

theorem isSolvable_Qstab (s : Fin 7) : Group.IsSolvable ↥(Qstab s) := by
  let Ω : Set (Finset (Fin 7)) := ((blocks s : Finset (Finset (Fin 7))) : Set (Finset (Fin 7)))
  let φ : ↥(Qstab s) →* Equiv.Perm ↥Ω := MulAction.toPermHom ↥(Qstab s) ↥Ω
  haveI : Group.IsSolvable (Equiv.Perm ↥Ω) := by
    refine Equiv.Perm.isSolvable ?_
    rw [Nat.card_coe_set_eq, Set.ncard_coe_finset, blocks_card]
  have hsq : ∀ x : ↥φ.ker, x * x = 1 := by
    intro x
    have hB : ∀ B ∈ blocks s, (((x : ↥(Qstab s)) : Equiv.Perm (Fin 7)) • B) = B := by
      intro B hB
      have := congrArg (fun f : Equiv.Perm ↥Ω => ((f ⟨B, hB⟩ : ↥Ω) : Finset (Fin 7))) x.2
      simpa [φ] using this
    have hmap : ∀ B ∈ blocks s, ∀ y ∈ B, ((x : ↥(Qstab s)) : Equiv.Perm (Fin 7)) y ∈ B := by
      intro B hBs y hy
      have h1 := Finset.smul_mem_smul_finset (a := ((x : ↥(Qstab s)) : Equiv.Perm (Fin 7))) hy
      rw [hB B hBs] at h1
      exact h1
    apply Subtype.ext
    apply Subtype.ext
    refine Equiv.ext fun y => ?_
    obtain ⟨B, hBs, hyB⟩ := blocks_cover s y
    exact perm_sq_of_mapsTo _ (blocks_card_le s B hBs) (hmap B hBs) hyB
  haveI : Group.IsSolvable ↥φ.ker := isSolvable_of_sq_eq_one hsq
  exact Group.isSolvable_of_ker_le_range φ.ker.subtype φ (by rw [Subgroup.range_subtype])

end Solvable

section V4

theorem swap_mul_swap_smul_mem_blocks : ∀ ℓ ∈ fanoLines, ∀ s ∈ ℓ, ∀ x₀ ∈ ℓᶜ, ∀ x₁ ∈ ℓᶜ, ∀ x₂ ∈ ℓᶜ,
    ∀ x₃ ∈ ℓᶜ, x₀ ≠ x₁ → x₀ ≠ x₂ → x₀ ≠ x₃ → x₁ ≠ x₂ → x₁ ≠ x₃ → x₂ ≠ x₃ →
      ∀ B ∈ blocks s, (Equiv.swap x₀ x₁ * Equiv.swap x₂ x₃) • B ∈ blocks s := by
  decide +kernel

theorem V4S_le_Qstab {ℓ : Finset (Fin 7)} (hℓ : ℓ ∈ fanoLines) {s : Fin 7} (hs : s ∈ ℓ) (h : ℓᶜ.card = 4)
    (b : Bool) : V4S ℓᶜ h b ≤ Qstab s := by
  have hmem : ∀ i, emb ℓᶜ h i ∈ ℓᶜ := fun i => by
    have : emb ℓᶜ h i ∈ Set.range (emb ℓᶜ h) := ⟨i, rfl⟩
    rw [range_emb] at this
    exact this
  have hne : ∀ {i j : Fin 4}, i ≠ j → emb ℓᶜ h i ≠ emb ℓᶜ h j := fun hij e => hij ((emb ℓᶜ h).injective e)
  intro D hD
  rw [mem_Qstab]
  rcases V4S_cases ℓᶜ h b hD with rfl | rfl | rfl | rfl
  · intro B hB
    simpa using hB
  · exact swap_mul_swap_smul_mem_blocks ℓ hℓ s hs _ (hmem 0) _ (hmem 1) _ (hmem 2) _ (hmem 3)
      (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide))
      (hne (by decide))
  · exact swap_mul_swap_smul_mem_blocks ℓ hℓ s hs _ (hmem 0) _ (hmem 2) _ (hmem 1) _ (hmem 3)
      (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide))
      (hne (by decide))
  · exact swap_mul_swap_smul_mem_blocks ℓ hℓ s hs _ (hmem 0) _ (hmem 3) _ (hmem 1) _ (hmem 2)
      (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide))
      (hne (by decide))

end V4

section Main

theorem fano_inter : ∀ ℓ ∈ fanoLines, ∀ ℓ' ∈ fanoLines, ℓ ≠ ℓ' → ∃ s : Fin 7, ℓ ∩ ℓ' = {s} := by
  decide +kernel

theorem vec_apply_eq_zero {w : Wr 7} (hsum : wsum w = 0) {s : Fin 7} {c : ZMod 2}
    (hc : ∀ x, x ≠ s → w.vec x = c) : w.vec s = 0 := by
  have h1 : wsum w = w.vec s + ∑ x ∈ Finset.univ.erase s, w.vec x :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ s)).symm
  have h2 : ∑ x ∈ Finset.univ.erase s, w.vec x = ∑ x ∈ Finset.univ.erase s, c :=
    Finset.sum_congr rfl fun x hx => hc x (Finset.ne_of_mem_erase hx)
  have h3 : ∑ x ∈ Finset.univ.erase s, c = 0 := by
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ s), Finset.card_univ,
      Fintype.card_fin]
    exact (by decide : ∀ z : ZMod 2, (7 - 1) • z = 0) c
  rw [h2, h3, add_zero, hsum] at h1
  exact h1.symm

theorem not_mem_of_const_vec {w : Wr 7} {s : Fin 7} (hv : ∀ x, w.vec x = if x = s then 0 else 1)
    {γ : Finset (Fin 7)} (h : γ.card = 4) (hconst : ∀ x ∈ γ, ∀ y ∈ γ, w.vec x = w.vec y) : s ∉ γ := by
  intro hsγ
  obtain ⟨y, hyγ, hys⟩ := Finset.exists_mem_ne (by omega : 1 < γ.card) s
  have h1 := hconst s hsγ y hyγ
  rw [hv s, hv y, if_pos rfl, if_neg hys] at h1
  exact absurd h1 (by decide)

theorem modelNoLayer_e64 : ModelNoLayer 7 AE.e64Sets AE.e64Sub := by
  rintro a ⟨w, ⟨hw, -⟩, rfl⟩ ⟨hne, -, -, hns⟩
  obtain ⟨α, hα, α', hα', hαα', hcα, hcα'⟩ := exists_pair_of_not_isSolvable hns
  have hperm : w.perm = 1 := perm_eq_one_of_pair (le_refl 7) hw.2 hcα hcα' hαα'
  obtain ⟨-, c, hconst⟩ := exists_level_set (by norm_num) (le_refl 7) hperm hcα hcα' hαα'
  obtain ⟨ℓ, hℓ, rfl⟩ := hα
  obtain ⟨ℓ', hℓ', rfl⟩ := hα'
  obtain ⟨s, hs⟩ := fano_inter ℓ hℓ ℓ' hℓ' fun e => hαα' (by rw [e])
  have hlevel : ∀ x, x ≠ s → w.vec x = c := by
    intro x hxs
    apply hconst
    have hx : x ∉ ℓ ∩ ℓ' := by
      rw [hs, Finset.mem_singleton]
      exact hxs
    rw [Finset.mem_union, Finset.mem_compl, Finset.mem_compl]
    rw [Finset.mem_inter, not_and_or] at hx
    exact hx
  have hs0 : w.vec s = 0 := vec_apply_eq_zero hw.1 hlevel
  rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) c with rfl | rfl
  · refine absurd ?_ hne
    have h1 : w = 1 := by
      refine Wr.ext (funext fun x => ?_) hperm
      by_cases hxs : x = s
      · rw [hxs, hs0]
        rfl
      · rw [hlevel x hxs]
        rfl
    rw [h1, map_one]
  · have hv : ∀ x, w.vec x = if x = s then 0 else 1 := by
      intro x
      by_cases hxs : x = s
      · rw [if_pos hxs, hxs, hs0]
      · rw [if_neg hxs, hlevel x hxs]
    haveI := isSolvable_Qstab s
    refine hns (isSolvable_of_permBar_le _ (Qstab s) ?_)
    rw [Subgroup.map_le_iff_le_comap]
    refine Ea_le fun M hM hMc => ?_
    obtain ⟨γ, hγ, hγc, b, rfl⟩ := hM
    have hsγ : s ∉ γ :=
      not_mem_of_const_vec hv hγc (const_of_le_centralizer (by norm_num) hperm hMc)
    obtain ⟨ℓ'', hℓ'', rfl⟩ := hγ
    rw [← Subgroup.map_le_iff_le_comap]
    exact V4S_le_Qstab hℓ'' (by simpa using hsγ) hγc b

end Main

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.L7
