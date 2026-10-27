module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.PairBlocks

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def bsw : Perm Bool := swap false true

theorem perm_bool_eq (a : Perm Bool) : a = 1 ∨ a = bsw := by
  revert a; decide

theorem sign_bsw : sign bsw = -1 := sign_swap (by decide)

@[expose] def tI (i : ι) : ι → Perm Bool := Pi.mulSingle i bsw

theorem tI_apply (i k : ι) : tI i k = if k = i then bsw else 1 := Pi.mulSingle_apply i bsw k

@[expose] def fsign (T : Finset ι) : (ι → Perm Bool) →* ℤˣ where
  toFun g := ∏ i ∈ T, sign (g i)
  map_one' := by simp
  map_mul' g h := by simp [Finset.prod_mul_distrib]

theorem fsign_apply (T : Finset ι) (g : ι → Perm Bool) : fsign T g = ∏ i ∈ T, sign (g i) := rfl

theorem fsign_tI (T : Finset ι) (i : ι) : fsign T (tI i) = if i ∈ T then -1 else 1 := by
  rw [fsign_apply]
  by_cases hi : i ∈ T
  · rw [if_pos hi, Finset.prod_eq_single i]
    · rw [tI_apply, if_pos rfl, sign_bsw]
    · intro k _ hki; rw [tI_apply, if_neg hki]; simp
    · intro h; exact absurd hi h
  · rw [if_neg hi]
    apply Finset.prod_eq_one
    intro k hk
    have : k ≠ i := fun h => hi (h ▸ hk)
    rw [tI_apply, if_neg this]; simp

theorem ker_fsign_le (E' : Subgroup (ι → Perm Bool)) (T : Finset ι)
    (hT : ∀ i, i ∈ T ↔ tI i ∉ E') (hD : ∀ i ∈ T, ∀ j ∈ T, tI i * tI j ∈ E') :
    (fsign T).ker ≤ E' := by
  suffices H : ∀ n, ∀ g : ι → Perm Bool, (Finset.univ.filter fun i => g i ≠ 1).card = n →
      fsign T g = 1 → g ∈ E' from fun g hg => H _ g rfl (MonoidHom.mem_ker.1 hg)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro g hn hg
    by_cases hs : ∃ i, g i ≠ 1
    · obtain ⟨i, hi⟩ := hs
      have hgi : g i = bsw := (perm_bool_eq _).resolve_left hi
      have hmem : i ∈ Finset.univ.filter fun k => g k ≠ 1 := by simp [hi]
      by_cases hiT : i ∈ T
      · obtain ⟨j, hjT, hji, hj⟩ : ∃ j ∈ T, j ≠ i ∧ g j ≠ 1 := by
          by_contra hno
          push Not at hno
          have h1 : fsign T g = -1 := by
            rw [fsign_apply, Finset.prod_eq_single i]
            · rw [hgi, sign_bsw]
            · intro k hk hki
              rw [hno k hk hki]; simp
            · intro h; exact absurd hiT h
          rw [h1] at hg
          exact absurd hg (by decide)
        have hgj : g j = bsw := (perm_bool_eq _).resolve_left hj
        have hsub : (Finset.univ.filter fun k => (g * (tI i * tI j)) k ≠ 1) ⊆
            Finset.univ.filter fun k => g k ≠ 1 := by
          intro k hk
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.mul_apply, tI_apply] at hk ⊢
          by_cases hki : k = i
          · subst hki
            rw [if_pos rfl, if_neg (Ne.symm hji), hgi] at hk
            simp [bsw] at hk
          · by_cases hkj : k = j
            · subst hkj
              rw [if_neg hki, if_pos rfl, hgj] at hk
              simp [bsw] at hk
            · rw [if_neg hki, if_neg hkj] at hk
              simpa using hk
        have hnot : i ∉ Finset.univ.filter fun k => (g * (tI i * tI j)) k ≠ 1 := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.mul_apply, tI_apply, not_not]
          rw [if_pos trivial, if_neg (Ne.symm hji), hgi]
          simp [bsw]
        have hlt := Finset.card_lt_card (Finset.ssubset_iff_of_subset hsub |>.2 ⟨i, hmem, hnot⟩)
        have hf : fsign T (g * (tI i * tI j)) = 1 := by
          rw [map_mul, map_mul, hg, fsign_tI, fsign_tI, if_pos hiT, if_pos hjT]; decide
        have := ih _ (hn ▸ hlt) (g * (tI i * tI j)) rfl hf
        have hg' : g = g * (tI i * tI j) * (tI i * tI j)⁻¹ := by group
        rw [hg']
        exact E'.mul_mem this (E'.inv_mem (hD i hiT j hjT))
      · have hiE : tI i ∈ E' := by
          by_contra h; exact hiT ((hT i).2 h)
        have hsub : (Finset.univ.filter fun k => (g * tI i) k ≠ 1) ⊆
            Finset.univ.filter fun k => g k ≠ 1 := by
          intro k hk
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.mul_apply, tI_apply] at hk ⊢
          by_cases hki : k = i
          · subst hki
            rw [if_pos rfl, hgi] at hk
            simp [bsw] at hk
          · rw [if_neg hki] at hk
            simpa using hk
        have hnot : i ∉ Finset.univ.filter fun k => (g * tI i) k ≠ 1 := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.mul_apply, tI_apply, not_not]
          rw [if_pos trivial, hgi]
          simp [bsw]
        have hlt := Finset.card_lt_card (Finset.ssubset_iff_of_subset hsub |>.2 ⟨i, hmem, hnot⟩)
        have hf : fsign T (g * tI i) = 1 := by
          rw [map_mul, hg, fsign_tI, if_neg hiT]; simp
        have := ih _ (hn ▸ hlt) (g * tI i) rfl hf
        have hg' : g = g * tI i * (tI i)⁻¹ := by group
        rw [hg']
        exact E'.mul_mem this (E'.inv_mem hiE)
    · push Not at hs
      have : g = 1 := funext hs
      rw [this]; exact E'.one_mem

theorem eq_ker_fsign (E' : Subgroup (ι → Perm Bool)) (T : Finset ι)
    (hT : ∀ i, i ∈ T ↔ tI i ∉ E') (hD : ∀ i ∈ T, ∀ j ∈ T, tI i * tI j ∈ E') :
    E' = (fsign T).ker := by
  refine le_antisymm (fun g hg => ?_) (ker_fsign_le E' T hT hD)
  by_contra hne
  have hne' : fsign T g ≠ 1 := fun h => hne (MonoidHom.mem_ker.2 h)
  have hT0 : T.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    apply hne'
    rw [fsign_apply, h]; simp
  obtain ⟨i, hi⟩ := hT0
  have hm1 : fsign T g = -1 := by
    rcases Int.units_eq_one_or (fsign T g) with h | h
    · exact absurd h hne'
    · exact h
  have hker : g * tI i ∈ (fsign T).ker := by
    rw [MonoidHom.mem_ker, map_mul, hm1, fsign_tI, if_pos hi]; decide
  have h1 := ker_fsign_le E' T hT hD hker
  have : tI i ∈ E' := by
    have := E'.mul_mem (E'.inv_mem hg) h1
    simpa using this
  exact (hT i).1 hi this

@[expose] def liftBlocks (π : Perm ι) : Perm (ι × Bool) := prodCongrLeft (fun _ : Bool => π)

theorem liftBlocks_apply (π : Perm ι) (x : ι × Bool) : liftBlocks π x = (π x.1, x.2) := rfl

theorem liftBlocks_inv (π : Perm ι) : (liftBlocks π)⁻¹ = liftBlocks π⁻¹ := by
  ext ⟨i, b⟩ <;> simp [liftBlocks_apply, Perm.inv_def, liftBlocks]

theorem liftBlocks_conj_blockPerm (π : Perm ι) (g : ι → Perm Bool) :
    liftBlocks π * blockPerm g * (liftBlocks π)⁻¹ = blockPerm (fun i => g (π⁻¹ i)) := by
  ext ⟨i, b⟩ <;> simp [liftBlocks_apply, liftBlocks_inv, blockPerm_apply]

theorem fsign_comp (T : Finset ι) (π : Perm ι) (hπ : ∀ i, i ∈ T ↔ π i ∈ T) (g : ι → Perm Bool) :
    fsign T (fun i => g (π⁻¹ i)) = fsign T g := by
  rw [fsign_apply, fsign_apply]
  apply Finset.prod_equiv π⁻¹
  · intro i
    have := hπ (π⁻¹ i)
    simpa using this.symm
  · intro i _
    rfl

theorem liftBlocks_mem_normalizer (T : Finset ι) (E : Subgroup (Perm (ι × Bool)))
    (hE : E = ((fsign T).ker).map (blockPermHom ι)) (π : Perm ι) (hπ : ∀ i, i ∈ T ↔ π i ∈ T) :
    liftBlocks π ∈ Subgroup.normalizer (E : Set (Perm (ι × Bool))) := by
  have step : ∀ ρ : Perm ι, (∀ i, i ∈ T ↔ ρ i ∈ T) → ∀ e ∈ E, liftBlocks ρ * e * (liftBlocks ρ)⁻¹ ∈ E := by
    intro ρ hρ e he
    rw [hE] at he ⊢
    obtain ⟨g, hg, rfl⟩ := he
    refine ⟨fun i => g (ρ⁻¹ i), ?_, ?_⟩
    · exact MonoidHom.mem_ker.2 (by rw [fsign_comp T ρ hρ]; exact MonoidHom.mem_ker.1 hg)
    · exact (liftBlocks_conj_blockPerm ρ g).symm
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact step π hπ h
  · intro hh
    have hπ' : ∀ i, i ∈ T ↔ π⁻¹ i ∈ T := by
      intro i
      have := hπ (π⁻¹ i)
      simpa using this.symm
    have := step π⁻¹ hπ' _ hh
    rw [← liftBlocks_inv, inv_inv] at this
    simpa [mul_assoc] using this

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
