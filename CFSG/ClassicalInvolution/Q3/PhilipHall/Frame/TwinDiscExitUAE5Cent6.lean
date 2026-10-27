module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUAE5Cent

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

namespace TwinDisc

namespace AE5

theorem cent_core {n : ℕ} (ι : Fin 4 ↪ Fin n) {p : Fin n} (hp : p ∉ Set.range ι) {x : AEQ n}
    (ht : ∀ a ∈ kList, x * mkQ n (embed ι a) = mkQ n (embed ι a) * x)
    (hs : ∀ a ∈ kStarList, x * mkQ n (embed ι a) = mkQ n (embed ι a) * x) :
    ∃ w : Wr n, x = mkQ n w ∧ (∀ j, w.perm (ι j) = ι j) ∧
      ((fun i => w.vec (ι i)) = 0 ∨ (fun i => w.vec (ι i)) = fun _ => 1) ∧
      (∀ y, y ∉ Set.range ι → w.perm y ∉ Set.range ι) := by
  classical
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (piSub n) x
  have hcomm : ∀ a ∈ kList ++ kStarList,
      mkQ n (w * embed ι a) = mkQ n (embed ι a * w) := by
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
      have := congrArg (fun f : Equiv.Perm (Fin n) => f (ι i)) hc
      simpa using this
    rw [embedPerm_apply, embedPerm_of_not_mem ι d₁ hy] at e1
    exact d1_fixed_free i (ι.injective (w.perm.injective e1))
  set c := localPerm ι w.perm hmap with hcdef
  have hspec : ∀ i, w.perm (ι i) = ι (c i) := localPerm_spec ι w.perm hmap
  have hcomm_c : ∀ a ∈ kList ++ kStarList, c * a.perm = a.perm * c := by
    intro a ha
    refine Equiv.ext fun i => ι.injective ?_
    have hc := hpc a ha
    have e1 := congrArg (fun f : Equiv.Perm (Fin n) => f (ι i)) hc
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
  have hfix : ∀ j, w.perm (ι j) = ι j := fun j => by rw [hspec, hc1]; rfl
  refine ⟨w, rfl, hfix, hV, ?_⟩
  intro y hy ⟨j, hj⟩
  apply hy
  refine ⟨j, ?_⟩
  have : w.perm y = w.perm (ι j) := by rw [← hj]; exact (hfix j).symm
  exact (w.perm.injective this).symm

theorem outside_two (ι : Fin 4 ↪ Fin 6) : ∃ p q : Fin 6, p ≠ q ∧ ∀ y, y ∉ Set.range ι ↔ y = p ∨ y = q := by
  classical
  set s : Finset (Fin 6) := Finset.univ.image ι with hs
  have hscard : s.card = 4 := by
    rw [hs, Finset.card_image_of_injective _ ι.injective]
    simp
  have hc : sᶜ.card = 2 := by
    rw [Finset.card_compl, Fintype.card_fin, hscard]
  obtain ⟨p, q, hpq, hpqe⟩ := Finset.card_eq_two.mp hc
  refine ⟨p, q, hpq, fun y => ?_⟩
  have hy : y ∉ Set.range ι ↔ y ∈ sᶜ := by
    rw [Finset.mem_compl, hs, Finset.mem_image]
    simp [Set.mem_range]
  rw [hy, hpqe]
  simp

theorem cent_sq6 (ι : Fin 4 ↪ Fin 6) {x : AEQ 6}
    (ht : ∀ a ∈ kList, x * mkQ 6 (embed ι a) = mkQ 6 (embed ι a) * x)
    (hs : ∀ a ∈ kStarList, x * mkQ 6 (embed ι a) = mkQ 6 (embed ι a) * x) :
    x * x = 1 ∨ x * x = mkQ 6 (zOf ι) := by
  classical
  obtain ⟨p, q, hpq, hout⟩ := outside_two ι
  have hp : p ∉ Set.range ι := (hout p).mpr (Or.inl rfl)
  obtain ⟨w, rfl, hfix, hV, hpres⟩ := cent_core ι hp ht hs
  have key : ∀ a b c : Fin 6, (a = p ∨ a = q) → (b = p ∨ b = q) → (c = p ∨ c = q) →
      w.perm a = b → w.perm b = c → c = a := by
    intro a b c ha hb hc hab hbc
    by_cases heq : a = b
    · subst heq
      rw [hab] at hbc
      exact hbc.symm
    · have hcb : c ≠ b := by
        rintro rfl
        exact heq (w.perm.injective (hab.trans hbc.symm))
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
        first | rfl | exact absurd rfl heq | exact absurd rfl hcb | exact absurd rfl hpq |
          exact absurd rfl hpq.symm
  have hinv : ∀ y, y ∉ Set.range ι → w.perm (w.perm y) = y := by
    intro y hy
    have h1 := hpres y hy
    have h2 := hpres _ h1
    exact key y (w.perm y) _ ((hout y).mp hy) ((hout _).mp h1) ((hout _).mp h2) rfl rfl
  have hsymm : ∀ y, y ∉ Set.range ι → w.perm.symm y = w.perm y := by
    intro y hy
    apply w.perm.injective
    rw [Equiv.apply_symm_apply, hinv y hy]
  have hsymm' : ∀ j, w.perm.symm (ι j) = ι j := by
    intro j
    apply w.perm.injective
    rw [Equiv.apply_symm_apply, hfix]
  have hconst : ∃ c : ZMod 2, ∀ y, y ∉ Set.range ι → w.vec y + w.vec (w.perm y) = c := by
    by_cases hpp : w.perm p = p
    · have hqq : w.perm q = q := by
        have hq : q ∉ Set.range ι := (hout q).mpr (Or.inr rfl)
        have h1 := hpres q hq
        rw [hout] at h1
        rcases h1 with h1 | h1
        · exact absurd (w.perm.injective (h1.trans hpp.symm)) hpq.symm
        · exact h1
      refine ⟨0, fun y hy => ?_⟩
      rcases (hout y).mp hy with rfl | rfl
      · rw [hpp]; exact CharTwo.add_self_eq_zero _
      · rw [hqq]; exact CharTwo.add_self_eq_zero _
    · have hpq' : w.perm p = q := by
        have h1 := hpres p hp
        rw [hout] at h1
        rcases h1 with h1 | h1
        · exact absurd h1 hpp
        · exact h1
      have hqp : w.perm q = p := by
        have := hinv p hp
        rwa [hpq'] at this
      refine ⟨w.vec p + w.vec q, fun y hy => ?_⟩
      rcases (hout y).mp hy with rfl | rfl
      · rw [hpq']
      · rw [hqp, add_comm]
  obtain ⟨c, hc⟩ := hconst
  have hu : ∀ y, (w * w).vec y = if y ∈ Set.range ι then 0 else c := by
    intro y
    rw [mul_vec]
    by_cases hy : y ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hy
      rw [hsymm', if_pos ⟨i, rfl⟩]
      exact CharTwo.add_self_eq_zero _
    · rw [if_neg hy, hsymm y hy]
      exact hc y hy
  have hu1 : (w * w).perm = 1 := by
    rw [mul_perm]
    refine Equiv.ext fun y => ?_
    by_cases hy : y ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hy
      simp [hfix]
    · simpa using hinv y hy
  rcases zmod_two_cases c with hc0 | hc1
  · left
    have : w * w = 1 := by
      refine Wr.ext (funext fun y => ?_) hu1
      rw [hu]
      by_cases hy : y ∈ Set.range ι
      · rw [if_pos hy]; rfl
      · rw [if_neg hy, hc0]; rfl
    rw [← map_mul, this, map_one]
  · right
    have : w * w = zOf ι * allOnes 6 := by
      refine Wr.ext (funext fun y => ?_) (hu1.trans (by rw [mul_perm, zOf_perm, one_mul]; rfl))
      rw [hu, mul_vec, zOf_vec_apply]
      by_cases hy : y ∈ Set.range ι
      · rw [if_pos hy, if_pos hy]
        show (0 : ZMod 2) = 1 + 1
        decide
      · rw [if_neg hy, if_neg hy, hc1]
        show (1 : ZMod 2) = 0 + 1
        decide
    rw [← map_mul, this, map_mul, mkQ_allOnes, mul_one]

end AE5

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
