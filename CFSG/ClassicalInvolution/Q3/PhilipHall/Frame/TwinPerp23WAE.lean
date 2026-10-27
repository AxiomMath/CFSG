module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23WPerm
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUAE5Cent
public import CFSG.ClassicalInvolution.Q3.TL3T32

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.W

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc.AE5

theorem fpf_cases : ∀ d : Equiv.Perm (Fin 4), (d = 1 ∨ ∀ i, d i ≠ i ∧ d (d i) = i) →
    d = 1 ∨ d = d₁ ∨ d = d₂ ∨ d = d₃ := by
  decide +kernel

theorem d_fpf : ∀ d : Equiv.Perm (Fin 4), (d = d₁ ∨ d = d₂ ∨ d = d₃) → ∀ i, d i ≠ i ∧ d (d i) = i := by
  decide +kernel

theorem kList_perm : ∀ k ∈ kList, k.perm = 1 ∨ k.perm = d₁ ∨ k.perm = d₂ ∨ k.perm = d₃ := by
  decide +kernel

theorem kStarList_perm :
    ∀ k ∈ kStarList, k.perm = 1 ∨ k.perm = d₁ ∨ k.perm = d₂ ∨ k.perm = d₃ := by
  decide +kernel

theorem exists_kStarList_d₁ : ∃ k ∈ kStarList, k.perm = d₁ := by decide +kernel
theorem exists_kStarList_d₂ : ∃ k ∈ kStarList, k.perm = d₂ := by decide +kernel
theorem exists_kStarList_d₃ : ∃ k ∈ kStarList, k.perm = d₃ := by decide +kernel

theorem one_mem_kList : (1 : Wr 4) ∈ kList := by decide +kernel
theorem one_mem_kStarList : (1 : Wr 4) ∈ kStarList := by decide +kernel

theorem exists_kList_perm : ∀ c : Equiv.Perm (Fin 4), (c = 1 ∨ c = d₁ ∨ c = d₂ ∨ c = d₃) →
    ∃ k ∈ kList, k.perm = c := by
  rintro c (rfl | rfl | rfl | rfl)
  · exact ⟨1, one_mem_kList, rfl⟩
  · exact exists_kList_d₁
  · exact exists_kList_d₂
  · exact exists_kList_d₃

theorem exists_kStarList_perm : ∀ c : Equiv.Perm (Fin 4), (c = 1 ∨ c = d₁ ∨ c = d₂ ∨ c = d₃) →
    ∃ k ∈ kStarList, k.perm = c := by
  rintro c (rfl | rfl | rfl | rfl)
  · exact ⟨1, one_mem_kStarList, rfl⟩
  · exact exists_kStarList_d₁
  · exact exists_kStarList_d₂
  · exact exists_kStarList_d₃

theorem V4m_embedPerm (ι : Fin 4 ↪ Fin 5) {p : Fin 5} (hp : p ∉ Set.range ι) {d : Equiv.Perm (Fin 4)}
    (hd : d = 1 ∨ d = d₁ ∨ d = d₂ ∨ d = d₃) : V4m p (embedPerm ι d) := by
  refine ⟨embedPerm_of_not_mem ι d hp, ?_⟩
  rcases hd with rfl | hd
  · exact Or.inl (embedPerm_one ι)
  · refine Or.inr fun x hx => ?_
    have hxr : x ∈ Set.range ι := by
      by_contra h
      exact hx (eq_of_not_mem_range ι h hp)
    obtain ⟨i, rfl⟩ := hxr
    have h1 := d_fpf d hd i
    rw [embedPerm_apply, embedPerm_apply]
    exact ⟨fun h => h1.1 (ι.injective h), by rw [h1.2]⟩

theorem perm_memAt {α : Finset (Fin 5)} {h : α.card = 4} {b : Bool} {p : Fin 5} (hp : p ∉ α)
    {a : Wr 5} (ha : a ∈ memAt α h b) : V4m p a.perm := by
  have hpr : p ∉ Set.range (emb α h) := by rw [range_emb]; exact hp
  cases b
  · obtain ⟨k, hk, rfl⟩ := ha
    rw [embed_perm]
    exact V4m_embedPerm _ hpr (kStarList_perm k hk)
  · obtain ⟨k, hk, rfl⟩ := ha
    rw [embed_perm]
    exact V4m_embedPerm _ hpr (kList_perm k hk)

theorem exists_memAt_perm {α : Finset (Fin 5)} (h : α.card = 4) (b : Bool) {p : Fin 5} (hp : p ∉ α)
    {σ : Equiv.Perm (Fin 5)} (hσ : V4m p σ) : ∃ a ∈ memAt α h b, a.perm = σ := by
  classical
  set ι := emb α h with hι
  have hpr : p ∉ Set.range ι := by rw [hι, range_emb]; exact hp
  have hout : ∀ x, x ≠ p → x ∈ Set.range ι := fun x hx => by
    by_contra h'
    exact hx (eq_of_not_mem_range ι h' hpr)
  have hmap : ∀ i, σ (ι i) ∈ Set.range ι := by
    intro i
    apply hout
    intro hc
    have : σ (ι i) = σ p := by rw [hc, hσ.1]
    exact (fun hip => hpr ⟨i, hip⟩) (σ.injective this)
  set c := localPerm ι σ hmap with hc
  have hspec : ∀ i, σ (ι i) = ι (c i) := localPerm_spec ι σ hmap
  have hcases : c = 1 ∨ c = d₁ ∨ c = d₂ ∨ c = d₃ := by
    apply fpf_cases
    rcases hσ.2 with h1 | h1
    · left
      refine Equiv.ext fun i => ι.injective ?_
      rw [← hspec, h1]
      rfl
    · right
      intro i
      have hne : ι i ≠ p := fun hip => hpr ⟨i, hip⟩
      obtain ⟨h2, h3⟩ := h1 (ι i) hne
      refine ⟨fun hci => h2 ?_, ?_⟩
      · rw [hspec, hci]
      · apply ι.injective
        rw [← hspec, ← hspec, h3]
  have hσc : embedPerm ι c = σ := by
    refine Equiv.ext fun x => ?_
    by_cases hx : x ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hx
      rw [embedPerm_apply, hspec]
    · have : x = p := eq_of_not_mem_range ι hx hpr
      subst this
      rw [embedPerm_of_not_mem ι c hx, hσ.1]
  cases b
  · obtain ⟨k, hk, hkp⟩ := exists_kStarList_perm c hcases
    refine ⟨embed ι k, ⟨k, hk, rfl⟩, ?_⟩
    rw [embed_perm, hkp, hσc]
  · obtain ⟨k, hk, hkp⟩ := exists_kList_perm c hcases
    refine ⟨embed ι k, ⟨k, hk, rfl⟩, ?_⟩
    rw [embed_perm, hkp, hσc]

theorem permQ_fix_of_comm_zBar {α : Finset (Fin 5)} (h : α.card = 4) {p : Fin 5} (hp : p ∉ α)
    {g : AEQ 5} (hg : g * zBar α h = zBar α h * g) : TC.Thin.permQ 5 g p = p := by
  classical
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (piSub 5) g
  set ι := emb α h with hι
  have hpr : p ∉ Set.range ι := by rw [hι, range_emb]; exact hp
  have hcomm : mkQ 5 (a * zOf ι) = mkQ 5 (zOf ι * a) := by
    rw [map_mul, map_mul]
    exact hg
  obtain ⟨hperm, ε, hε⟩ := comm_comp hcomm
  have hv : ∀ y, (zOf ι).vec y = (zOf ι).vec (a.perm.symm y) + ε := by
    intro y
    have h1 := hε y
    rw [mul_vec, mul_vec, zOf_perm] at h1
    have h2 : (zOf ι).vec y + a.vec ((1 : Equiv.Perm (Fin 5)).symm y) =
        a.vec y + (zOf ι).vec (a.perm.symm y) + ε := h1
    have h3 : (1 : Equiv.Perm (Fin 5)).symm y = y := rfl
    rw [h3] at h2
    have h4 : a.vec y + (zOf ι).vec y = a.vec y + ((zOf ι).vec (a.perm.symm y) + ε) := by
      rw [add_comm (a.vec y) _, h2, add_assoc]
    exact add_left_cancel h4
  show a.perm p = p
  rcases zmod_two_cases ε with h0 | h1
  · have hp0 := hv p
    rw [zOf_vec_apply, zOf_vec_apply, if_neg hpr, h0, add_zero] at hp0
    have hnot : a.perm.symm p ∉ Set.range ι := by
      intro hmem
      rw [if_pos hmem] at hp0
      exact absurd hp0 (by decide)
    have : a.perm.symm p = p := eq_of_not_mem_range ι hnot hpr
    exact (Equiv.symm_apply_eq a.perm).mp this |>.symm
  · exfalso
    have hy : ∀ i : Fin 4, a.perm.symm (ι i) = p := by
      intro i
      have h5 := hv (ι i)
      rw [zOf_vec_apply, zOf_vec_apply, if_pos ⟨i, rfl⟩, h1] at h5
      have hnot : a.perm.symm (ι i) ∉ Set.range ι := by
        intro hmem
        rw [if_pos hmem] at h5
        exact absurd h5 (by decide)
      exact eq_of_not_mem_range ι hnot hpr
    have h0 := hy 0
    have h1' := hy 1
    have : ι 0 = ι 1 := a.perm.symm.injective (h0.trans h1'.symm)
    exact absurd (ι.injective this) (by decide)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.W
