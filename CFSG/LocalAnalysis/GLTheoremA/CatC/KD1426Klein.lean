module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

open Equiv

namespace CFSG.LocalAnalysis.GLTheoremA.KD1426Klein

structure Distinct4 (x y z f : Fin 7) : Prop where
  xy : x ≠ y
  xz : x ≠ z
  yz : y ≠ z
  xf : x ≠ f
  yf : y ≠ f
  zf : z ≠ f

abbrev kU1 (x y z f : Fin 7) : Perm (Fin 7) := swap x y * swap z f
abbrev kU2 (x y z f : Fin 7) : Perm (Fin 7) := swap y z * swap x f
abbrev kU3 (x y z f : Fin 7) : Perm (Fin 7) := swap x z * swap y f

theorem conj_swap (d : Perm (Fin 7)) (p q : Fin 7) : d * swap p q * d⁻¹ = swap (d p) (d q) :=
  (swap_apply_apply d p q).symm

section Identities

variable {x y z f : Fin 7}

theorem kU1_mul_kU1 (h : Distinct4 x y z f) : kU1 x y z f * kU1 x y z f = 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  ext i
  simp only [Perm.mul_apply, Perm.one_apply, swap_apply_def]
  split_ifs <;> simp_all <;> omega

theorem kU2_mul_kU2 (h : Distinct4 x y z f) : kU2 x y z f * kU2 x y z f = 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  ext i
  simp only [Perm.mul_apply, Perm.one_apply, swap_apply_def]
  split_ifs <;> simp_all <;> omega

theorem kU3_mul_kU3 (h : Distinct4 x y z f) : kU3 x y z f * kU3 x y z f = 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  ext i
  simp only [Perm.mul_apply, Perm.one_apply, swap_apply_def]
  split_ifs <;> simp_all <;> omega

theorem kU12 (h : Distinct4 x y z f) : kU1 x y z f * kU2 x y z f = kU3 x y z f := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  ext i
  simp only [Perm.mul_apply, swap_apply_def]
  split_ifs <;> simp_all <;> omega

theorem kU21 (h : Distinct4 x y z f) : kU2 x y z f * kU1 x y z f = kU3 x y z f := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  ext i
  simp only [Perm.mul_apply, swap_apply_def]
  split_ifs <;> simp_all <;> omega

theorem kU13 (h : Distinct4 x y z f) : kU1 x y z f * kU3 x y z f = kU2 x y z f := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  ext i
  simp only [Perm.mul_apply, swap_apply_def]
  split_ifs <;> simp_all <;> omega

theorem kU31 (h : Distinct4 x y z f) : kU3 x y z f * kU1 x y z f = kU2 x y z f := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  ext i
  simp only [Perm.mul_apply, swap_apply_def]
  split_ifs <;> simp_all <;> omega

theorem kU23 (h : Distinct4 x y z f) : kU2 x y z f * kU3 x y z f = kU1 x y z f := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  ext i
  simp only [Perm.mul_apply, swap_apply_def]
  split_ifs <;> simp_all <;> omega

theorem kU32 (h : Distinct4 x y z f) : kU3 x y z f * kU2 x y z f = kU1 x y z f := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  ext i
  simp only [Perm.mul_apply, swap_apply_def]
  split_ifs <;> simp_all <;> omega

end Identities


@[expose] def kleinCarrier (x y z f : Fin 7) : Set (Perm (Fin 7)) :=
  {1, kU1 x y z f, kU2 x y z f, kU3 x y z f}

theorem mem_kleinCarrier {x y z f : Fin 7} {σ : Perm (Fin 7)} :
    σ ∈ kleinCarrier x y z f ↔
      σ = 1 ∨ σ = kU1 x y z f ∨ σ = kU2 x y z f ∨ σ = kU3 x y z f := by
  simp [kleinCarrier]

theorem swap_mul_swap_mem_klein {x y z f p q r : Fin 7} (h : Distinct4 x y z f)
    (hp : p = x ∨ p = y ∨ p = z) (hq : q = x ∨ q = y ∨ q = z) (hr : r = x ∨ r = y ∨ r = z)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    swap p q * swap r f ∈ kleinCarrier x y z f := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  rw [mem_kleinCarrier]
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
    rcases hr with rfl | rfl | rfl <;> simp_all [kU1, kU2, kU3, Equiv.swap_comm]


@[expose] def kleinSub {x y z f : Fin 7} (h : Distinct4 x y z f) : Subgroup (Perm (Fin 7)) where
  carrier := kleinCarrier x y z f
  mul_mem' := by
    intro a b ha hb
    rw [mem_kleinCarrier] at ha hb ⊢
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
      simp [kU1_mul_kU1 h, kU2_mul_kU2 h, kU3_mul_kU3 h, kU12 h, kU21 h, kU13 h, kU31 h,
        kU23 h, kU32 h]
  one_mem' := by
    rw [mem_kleinCarrier]
    exact Or.inl rfl
  inv_mem' := by
    intro a ha
    rw [mem_kleinCarrier] at ha ⊢
    rcases ha with rfl | rfl | rfl | rfl
    · exact Or.inl (inv_one)
    · exact Or.inr (Or.inl (inv_eq_of_mul_eq_one_right (kU1_mul_kU1 h)))
    · exact Or.inr (Or.inr (Or.inl (inv_eq_of_mul_eq_one_right (kU2_mul_kU2 h))))
    · exact Or.inr (Or.inr (Or.inr (inv_eq_of_mul_eq_one_right (kU3_mul_kU3 h))))

theorem mem_kleinSub {x y z f : Fin 7} (h : Distinct4 x y z f) {σ : Perm (Fin 7)} :
    σ ∈ kleinSub h ↔ σ = 1 ∨ σ = kU1 x y z f ∨ σ = kU2 x y z f ∨ σ = kU3 x y z f :=
  mem_kleinCarrier

theorem kU1_x {x y z f : Fin 7} (h : Distinct4 x y z f) : kU1 x y z f x = y := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  simp only [kU1, Perm.mul_apply, swap_apply_of_ne_of_ne h2 h4, swap_apply_left]

theorem kU2_x {x y z f : Fin 7} (h : Distinct4 x y z f) : kU2 x y z f x = f := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  simp only [kU2, Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne h5.symm h6.symm]

theorem kU3_x {x y z f : Fin 7} (h : Distinct4 x y z f) : kU3 x y z f x = z := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  simp only [kU3, Perm.mul_apply, swap_apply_of_ne_of_ne h1 h4, swap_apply_left]

theorem card_kleinSub {x y z f : Fin 7} (h : Distinct4 x y z f) : Nat.card (kleinSub h) = 4 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hd : Distinct4 x y z f := ⟨h1, h2, h3, h4, h5, h6⟩
  have e1 : kU1 x y z f ≠ 1 := fun e => by
    have := congrArg (fun σ : Perm (Fin 7) => σ x) e
    simp only [Perm.one_apply, kU1_x hd] at this
    exact h1 this.symm
  have e2 : kU2 x y z f ≠ 1 := fun e => by
    have := congrArg (fun σ : Perm (Fin 7) => σ x) e
    simp only [Perm.one_apply, kU2_x hd] at this
    exact h4 this.symm
  have e3 : kU3 x y z f ≠ 1 := fun e => by
    have := congrArg (fun σ : Perm (Fin 7) => σ x) e
    simp only [Perm.one_apply, kU3_x hd] at this
    exact h2 this.symm
  have e12 : kU1 x y z f ≠ kU2 x y z f := fun e => by
    have := congrArg (fun σ : Perm (Fin 7) => σ x) e
    simp only [kU1_x hd, kU2_x hd] at this
    exact h5 this
  have e13 : kU1 x y z f ≠ kU3 x y z f := fun e => by
    have := congrArg (fun σ : Perm (Fin 7) => σ x) e
    simp only [kU1_x hd, kU3_x hd] at this
    exact h3 this
  have e23 : kU2 x y z f ≠ kU3 x y z f := fun e => by
    have := congrArg (fun σ : Perm (Fin 7) => σ x) e
    simp only [kU2_x hd, kU3_x hd] at this
    exact h6 this.symm
  have hcarr : Nat.card (kleinSub hd) = Set.ncard (kleinCarrier x y z f) :=
    Nat.card_coe_set_eq (kleinCarrier x y z f)
  rw [hcarr, kleinCarrier, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
    Set.ncard_pair e23]
  · simp [e12, e13]
  · simp [e1.symm, e2.symm, e3.symm]

theorem kU_mem_alt {x y z f : Fin 7} (h : Distinct4 x y z f) :
    ∀ σ ∈ kleinSub h, σ ∈ alternatingGroup (Fin 7) := by
  intro σ hσ
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  rw [mem_kleinSub] at hσ
  rcases hσ with rfl | rfl | rfl | rfl
  · exact Subgroup.one_mem _
  · rw [Perm.mem_alternatingGroup, kU1, Perm.sign_mul, Perm.sign_swap h1, Perm.sign_swap h6]
    norm_num
  · rw [Perm.mem_alternatingGroup, kU2, Perm.sign_mul, Perm.sign_swap h3, Perm.sign_swap h4]
    norm_num
  · rw [Perm.mem_alternatingGroup, kU3, Perm.sign_mul, Perm.sign_swap h2, Perm.sign_swap h5]
    norm_num

@[expose] def kleinA7 {x y z f : Fin 7} (h : Distinct4 x y z f) : Subgroup (alternatingGroup (Fin 7)) :=
  (kleinSub h).subgroupOf (alternatingGroup (Fin 7))

theorem card_kleinA7 {x y z f : Fin 7} (h : Distinct4 x y z f) :
    Nat.card (kleinA7 h) = 4 := by
  have hle : kleinSub h ≤ alternatingGroup (Fin 7) := fun σ hσ => kU_mem_alt h σ hσ
  have hmap : (kleinA7 h).map (alternatingGroup (Fin 7)).subtype = kleinSub h := by
    unfold kleinA7
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hle]
  rw [← Subgroup.card_map_of_injective (alternatingGroup (Fin 7)).subtype_injective, hmap,
    card_kleinSub h]

theorem cycle_orientation {σ : Perm (Fin 7)} {x y z : Fin 7}
    (h1 : x ≠ y) (h2 : x ≠ z) (h3 : y ≠ z)
    (hsupp : ∀ t, σ t ≠ t ↔ (t = x ∨ t = y ∨ t = z)) :
    (σ x = y ∧ σ y = z ∧ σ z = x) ∨ (σ x = z ∧ σ y = x ∧ σ z = y) := by
  have hmem : ∀ t, (t = x ∨ t = y ∨ t = z) → (σ t = x ∨ σ t = y ∨ σ t = z) := by
    intro t ht
    by_contra hc
    have hfix : σ (σ t) = σ t := by
      by_contra hne
      exact hc ((hsupp (σ t)).1 hne)
    have hst : σ t = t := by
      have := congrArg σ.symm hfix
      simpa using this
    exact ((hsupp t).2 ht) hst
  have hsx : σ x ≠ x := (hsupp x).2 (Or.inl rfl)
  have hsy : σ y ≠ y := (hsupp y).2 (Or.inr (Or.inl rfl))
  have hsz : σ z ≠ z := (hsupp z).2 (Or.inr (Or.inr rfl))
  have hi := σ.injective
  rcases hmem x (Or.inl rfl) with ex | ex | ex
  · exact absurd ex hsx
  · rcases hmem y (Or.inr (Or.inl rfl)) with ey | ey | ey
    · exfalso
      rcases hmem z (Or.inr (Or.inr rfl)) with ez | ez | ez
      · exact h3 (hi (ez.trans ey.symm)).symm
      · exact h2 (hi (ez.trans ex.symm)).symm
      · exact hsz ez
    · exact absurd ey hsy
    · rcases hmem z (Or.inr (Or.inr rfl)) with ez | ez | ez
      · exact Or.inl ⟨ex, ey, ez⟩
      · exact absurd (hi (ez.trans ex.symm)) (fun e => h2 e.symm)
      · exact absurd ez hsz
  · rcases hmem y (Or.inr (Or.inl rfl)) with ey | ey | ey
    · rcases hmem z (Or.inr (Or.inr rfl)) with ez | ez | ez
      · exact absurd (hi (ez.trans ey.symm)) (fun e => h3 e.symm)
      · exact Or.inr ⟨ex, ey, ez⟩
      · exact absurd ez hsz
    · exact absurd ey hsy
    · exact absurd (hi (ey.trans ex.symm)) (fun e => h1 e.symm)

end CFSG.LocalAnalysis.GLTheoremA.KD1426Klein

end
