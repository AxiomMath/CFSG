module

public import CFSG.ClassicalInvolution.Q3.AE.PermElt

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

namespace TwinDisc

namespace AE5

theorem loc_perm : ∀ c : Equiv.Perm (Fin 4), c * d₁ = d₁ * c → c * d₂ = d₂ * c → c * d₃ = d₃ * c →
    c = 1 ∨ c = d₁ ∨ c = d₂ ∨ c = d₃ := by
  decide +kernel

theorem loc_vec : ∀ c ∈ [(1 : Equiv.Perm (Fin 4)), d₁, d₂, d₃], ∀ V : Fin 4 → ZMod 2,
    (∀ k ∈ kList ++ kStarList, ∀ i, V i + k.vec (c.symm i) = k.vec i + V (k.perm.symm i)) →
    c = 1 ∧ (V = 0 ∨ V = fun _ => 1) := by
  decide +kernel

theorem d1_fixed_free : ∀ i : Fin 4, d₁ i ≠ i := by decide

theorem exists_kList_d₁ : ∃ k ∈ kList, k.perm = d₁ := by decide +kernel
theorem exists_kList_d₂ : ∃ k ∈ kList, k.perm = d₂ := by decide +kernel
theorem exists_kList_d₃ : ∃ k ∈ kList, k.perm = d₃ := by decide +kernel

theorem eq_of_not_mem_range (ι : Fin 4 ↪ Fin 5) {y z : Fin 5} (hy : y ∉ Set.range ι)
    (hz : z ∉ Set.range ι) : y = z := by
  classical
  by_contra hne
  set s : Finset (Fin 5) := Finset.univ.image ι with hs
  have hscard : s.card = 4 := by
    rw [hs, Finset.card_image_of_injective _ ι.injective]
    simp
  have hys : y ∉ s := fun h => by
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp h
    exact hy ⟨i, hi⟩
  have hzs : z ∉ insert y s := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact hne h.symm
    · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp h
      exact hz ⟨i, hi⟩
  have : (insert z (insert y s)).card = 6 := by
    rw [Finset.card_insert_of_notMem hzs, Finset.card_insert_of_notMem hys, hscard]
  have h5 := Finset.card_le_univ (insert z (insert y s))
  rw [Fintype.card_fin] at h5
  omega

theorem exists_not_mem_range (ι : Fin 4 ↪ Fin 5) : ∃ p, p ∉ Set.range ι := by
  by_contra h
  push Not at h
  have hs : Function.Surjective ι := h
  have := Fintype.card_le_of_surjective ι hs
  simp at this

theorem comm_comp {n : ℕ} {w e : Wr n} (h : mkQ n (w * e) = mkQ n (e * w)) :
    (w * e).perm = (e * w).perm ∧ ∃ ε : ZMod 2, ∀ y, (e * w).vec y = (w * e).vec y + ε := by
  rcases mkQ_eq_iff.mp h with h1 | h1
  · have : e * w = w * e := by
      calc e * w = (w * e) * ((w * e)⁻¹ * (e * w)) := by group
        _ = w * e := by rw [h1, mul_one]
    refine ⟨by rw [this], 0, fun y => by rw [this, add_zero]⟩
  · have h2 : e * w = (w * e) * allOnes n := by
      calc e * w = (w * e) * ((w * e)⁻¹ * (e * w)) := by group
        _ = (w * e) * allOnes n := by rw [h1]
    refine ⟨by rw [h2]; rfl, 1, fun y => ?_⟩
    rw [h2, mul_vec]
    rfl

theorem zmod_two_cases (b : ZMod 2) : b = 0 ∨ b = 1 := by
  revert b
  decide

theorem mkQ_allOnes (n : ℕ) : mkQ n (allOnes n) = 1 :=
  (QuotientGroup.eq_one_iff _).mpr (Or.inr rfl)


theorem cent_pair (ι : Fin 4 ↪ Fin 5) {x : AEQ 5}
    (ht : ∀ a ∈ kList, x * mkQ 5 (embed ι a) = mkQ 5 (embed ι a) * x)
    (hs : ∀ a ∈ kStarList, x * mkQ 5 (embed ι a) = mkQ 5 (embed ι a) * x) :
    x = 1 ∨ x = mkQ 5 (zOf ι) := by
  classical
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (piSub 5) x
  have hcomm : ∀ a ∈ kList ++ kStarList,
      mkQ 5 (w * embed ι a) = mkQ 5 (embed ι a * w) := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · have := ht a ha
      rwa [← map_mul, ← map_mul] at this
    · have := hs a ha
      rwa [← map_mul, ← map_mul] at this
  have hdata := fun a (ha : a ∈ kList ++ kStarList) => comm_comp (hcomm a ha)
  have hpc : ∀ a ∈ kList ++ kStarList,
      w.perm * embedPerm ι a.perm = embedPerm ι a.perm * w.perm := by
    intro a ha
    have := (hdata a ha).1
    simpa only [mul_perm, embed_perm] using this
  obtain ⟨k₁, hk₁, hk₁p⟩ := exists_kList_d₁
  obtain ⟨k₂, hk₂, hk₂p⟩ := exists_kList_d₂
  obtain ⟨k₃, hk₃, hk₃p⟩ := exists_kList_d₃
  have hmap : ∀ i, w.perm (ι i) ∈ Set.range ι := by
    intro i
    by_contra hy
    have hc := hpc k₁ (List.mem_append_left _ hk₁)
    rw [hk₁p] at hc
    have e1 : w.perm (embedPerm ι d₁ (ι i)) = embedPerm ι d₁ (w.perm (ι i)) := by
      have := congrArg (fun f : Equiv.Perm (Fin 5) => f (ι i)) hc
      simpa using this
    rw [embedPerm_apply, embedPerm_of_not_mem ι d₁ hy] at e1
    exact d1_fixed_free i (ι.injective (w.perm.injective e1))
  set c := localPerm ι w.perm hmap with hcdef
  have hspec : ∀ i, w.perm (ι i) = ι (c i) := localPerm_spec ι w.perm hmap
  have hcomm_c : ∀ a ∈ kList ++ kStarList, c * a.perm = a.perm * c := by
    intro a ha
    refine Equiv.ext fun i => ι.injective ?_
    have hc := hpc a ha
    have e1 := congrArg (fun f : Equiv.Perm (Fin 5) => f (ι i)) hc
    simp only [Equiv.Perm.mul_apply, embedPerm_apply, hspec] at e1
    simpa [Equiv.Perm.mul_apply] using e1
  have hcV : c = 1 ∨ c = d₁ ∨ c = d₂ ∨ c = d₃ :=
    loc_perm c (by rw [← hk₁p]; exact hcomm_c k₁ (List.mem_append_left _ hk₁))
      (by rw [← hk₂p]; exact hcomm_c k₂ (List.mem_append_left _ hk₂))
      (by rw [← hk₃p]; exact hcomm_c k₃ (List.mem_append_left _ hk₃))
  have hsymm : ∀ i, w.perm.symm (ι i) = ι (c.symm i) := by
    intro i
    apply w.perm.injective
    rw [Equiv.apply_symm_apply, hspec, Equiv.apply_symm_apply]
  have hout : ∀ y, y ∉ Set.range ι → w.perm.symm y ∉ Set.range ι := by
    rintro y hy ⟨i, hi⟩
    apply hy
    refine ⟨c i, ?_⟩
    rw [← hspec, hi, Equiv.apply_symm_apply]
  obtain ⟨p, hp⟩ := exists_not_mem_range ι
  have hε0 : ∀ a ∈ kList ++ kStarList, ∀ ε : ZMod 2,
      (∀ y, (embed ι a * w).vec y = (w * embed ι a).vec y + ε) → ε = 0 := by
    intro a ha ε hε
    have h1 := hε p
    rw [mul_vec, mul_vec, embed_vec_of_not_mem ι a hp, embed_vec_of_not_mem ι a (hout p hp),
      embed_perm, embedPerm_symm_of_not_mem ι a.perm hp] at h1
    simpa using h1
  have hV := loc_vec c (by
    rcases hcV with h | h | h | h <;> simp [h]) (fun i => w.vec (ι i)) (by
    intro a ha i
    obtain ⟨-, ε, hε⟩ := hdata a ha
    have e0 := hε0 a ha ε hε
    have h1 := hε (ι i)
    rw [mul_vec, mul_vec, embed_vec, embedVec_apply, hsymm, embedVec_apply, embed_perm,
      embedPerm_symm_apply, e0, add_zero] at h1
    rw [h1])
  obtain ⟨hc1, hV⟩ := hV
  have hσid : ∀ y, w.perm y = y := by
    intro y
    have hfix : ∀ j, w.perm (ι j) = ι j := fun j => by rw [hspec, hc1]; rfl
    by_cases hy : y ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hy
      exact hfix i
    · have h1 : w.perm y ∉ Set.range ι := by
        rintro ⟨j, hj⟩
        apply hy
        refine ⟨j, ?_⟩
        have : w.perm y = w.perm (ι j) := by rw [← hj]; exact (hfix j).symm
        exact (w.perm.injective this).symm
      exact eq_of_not_mem_range ι h1 hy
  have hperm1 : w.perm = 1 := Equiv.ext hσid
  have hvother : ∀ y, y ∉ Set.range ι → w.vec y = w.vec p := fun y hy => by
    rw [eq_of_not_mem_range ι hy hp]
  have hw : w = ⟨w.vec, 1⟩ := by
    cases w
    simp only at hperm1
    subst hperm1
    rfl
  rcases hV with hV0 | hV1 <;> rcases zmod_two_cases (w.vec p) with hb | hb
  ·
    left
    have : w = 1 := by
      refine Wr.ext (funext fun y => ?_) hperm1
      by_cases hy : y ∈ Set.range ι
      · obtain ⟨i, rfl⟩ := hy
        exact congrFun hV0 i
      · rw [hvother y hy, hb]
        rfl
    rw [this, map_one]
  ·
    right
    have : w = zOf ι * allOnes 5 := by
      refine Wr.ext (funext fun y => ?_) (by rw [mul_perm, zOf_perm]; exact hperm1)
      rw [mul_vec, zOf_vec_apply]
      by_cases hy : y ∈ Set.range ι
      · obtain ⟨i, rfl⟩ := hy
        have h0 : w.vec (ι i) = 0 := congrFun hV0 i
        rw [h0, if_pos ⟨i, rfl⟩]
        show (0 : ZMod 2) = 1 + 1
        decide
      · rw [hvother y hy, hb, if_neg hy]
        show (1 : ZMod 2) = 0 + 1
        decide
    rw [this, map_mul, mkQ_allOnes, mul_one]
  ·
    right
    have : w = zOf ι := by
      refine Wr.ext (funext fun y => ?_) (by rw [zOf_perm]; exact hperm1)
      rw [zOf_vec_apply]
      by_cases hy : y ∈ Set.range ι
      · obtain ⟨i, rfl⟩ := hy
        rw [congrFun hV1 i]
        simp
      · rw [hvother y hy, hb]
        simp [hy]
    rw [this]
  ·
    left
    have : w = allOnes 5 := by
      refine Wr.ext (funext fun y => ?_) hperm1
      by_cases hy : y ∈ Set.range ι
      · obtain ⟨i, rfl⟩ := hy
        exact congrFun hV1 i
      · rw [hvother y hy, hb]
        rfl
    rw [this, mkQ_allOnes]

end AE5

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
