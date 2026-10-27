module

public import CFSG.ClassicalInvolution.Q3.Sec13RecogS
public import CFSG.ClassicalInvolution.Q3.Sec13EndAE8J

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

namespace AE8End

variable {Ω : Set (Subgroup G)} {u : G}

@[expose] def ae8e_rep : Fin 6 → Equiv.Perm (Fin 6) :=
  ![1, Equiv.swap 1 0 * Equiv.swap 2 3, Equiv.swap 2 0 * Equiv.swap 1 3,
    Equiv.swap 3 0 * Equiv.swap 1 2, Equiv.swap 4 0 * Equiv.swap 1 2,
    Equiv.swap 5 0 * Equiv.swap 1 2]

theorem ae8e_rep_mem (x : Fin 6) : ae8e_rep x ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  fin_cases x <;> decide

theorem ae8e_rep_zero (x : Fin 6) : ae8e_rep x x = 0 := by
  fin_cases x <;> decide

theorem ae8e_hom_trivial {s : Finset (Fin 6)} (hs : 5 ≤ Nat.card s) {A : Type} [CommGroup A]
    (f : alternatingGroup s →* A) (x : alternatingGroup s) : f x = 1 := by
  have htop : ⁅(⊤ : Subgroup (alternatingGroup s)), ⊤⁆ = ⊤ :=
    commutator_alternatingGroup_eq_top hs
  have hmap := Subgroup.map_commutator (H₁ := ⊤) (H₂ := ⊤) f
  rw [htop] at hmap
  have hbot : Subgroup.map f (⊤ : Subgroup (alternatingGroup s)) = ⊥ := by
    rw [hmap, Subgroup.commutator_self_eq_bot_iff]
    infer_instance
  have hx : f x ∈ Subgroup.map f (⊤ : Subgroup (alternatingGroup s)) :=
    Subgroup.mem_map_of_mem f trivial
  rw [hbot] at hx
  exact (Subgroup.mem_bot).mp hx

theorem ae8e_zmod2_self (x : ZMod 2) (h : x = x + x) : x = 0 := by
  revert x; decide

theorem ae8e_zmod2_add_self (t : ZMod 2) : t + t = 0 := by
  revert t
  decide

theorem ae8e_zmod2_neg (t : ZMod 2) : -t = t := by
  revert t
  decide

theorem ae8e_zmod2_swap (a b c : ZMod 2) (h : a = b + c) : c = a + b := by
  revert a b c; decide

theorem H1_alt_six (c : alternatingGroup (Fin 6) → (Fin 6 → ZMod 2))
    (hc : ∀ σ τ : alternatingGroup (Fin 6), c (σ * τ) =
      c σ + fun i => c τ ((σ : Equiv.Perm (Fin 6)).symm i)) :
    ∃ v : Fin 6 → ZMod 2, ∀ σ : alternatingGroup (Fin 6),
      c σ = (fun i => v ((σ : Equiv.Perm (Fin 6)).symm i)) + v := by
  have hcp : ∀ (σ τ : alternatingGroup (Fin 6)) (p : Fin 6),
      c (σ * τ) p = c σ p + c τ ((σ : Equiv.Perm (Fin 6)).symm p) := fun σ τ p => by
    rw [hc σ τ]
    rfl
  have hc1 : ∀ p, c 1 p = 0 := fun p => by
    have h := hcp 1 1 p
    simp only [mul_one, OneMemClass.coe_one, Equiv.Perm.one_def, Equiv.refl_symm,
      Equiv.refl_apply] at h
    exact ae8e_zmod2_self _ h
  let s : Finset (Fin 6) := Finset.univ.erase 0
  have hs5 : 5 ≤ Nat.card s := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    decide
  have hfix : ∀ x : alternatingGroup s,
      ((alternatingGroup.ofSubtype s x : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) 0 = 0 :=
    fun x => by
      rw [alternatingGroup.coe_ofSubtype]
      exact Equiv.Perm.ofSubtype_apply_of_not_mem _ (by simp [s])
  let f : alternatingGroup s →* Multiplicative (ZMod 2) :=
    { toFun := fun x => Multiplicative.ofAdd (c (alternatingGroup.ofSubtype s x) 0)
      map_one' := by
        simp only [map_one]
        rw [hc1 0]
        rfl
      map_mul' := fun x y => by
        have h0 : ((alternatingGroup.ofSubtype s x : alternatingGroup (Fin 6)) :
            Equiv.Perm (Fin 6)).symm 0 = 0 := by
          rw [Equiv.symm_apply_eq]
          exact (hfix x).symm
        simp only [map_mul]
        rw [hcp, h0, ofAdd_add] }
  have hf1 : ∀ x : alternatingGroup s, c (alternatingGroup.ofSubtype s x) 0 = 0 := fun x => by
    have := ae8e_hom_trivial hs5 f x
    exact (ofAdd_eq_one.mp this)
  have hkey : ∀ h : alternatingGroup (Fin 6), (h : Equiv.Perm (Fin 6)) 0 = 0 → c h 0 = 0 := by
    intro h hh0
    have hz : ∀ x, (h : Equiv.Perm (Fin 6)) x = 0 ↔ x = 0 := fun x => by
      constructor
      · intro e
        apply (h : Equiv.Perm (Fin 6)).injective
        rw [e, hh0]
      · rintro rfl
        exact hh0
    have hp : ∀ x, (x ∈ s ↔ (h : Equiv.Perm (Fin 6)) x ∈ s) := fun x => by
      simp only [s, Finset.mem_erase, Finset.mem_univ, and_true]
      exact (not_congr (hz x)).symm
    have hmove : ∀ x, (h : Equiv.Perm (Fin 6)) x ≠ x → x ∈ s := fun x hx => by
      simp only [s, Finset.mem_erase, Finset.mem_univ, and_true]
      rintro rfl
      exact hx hh0
    have hk : alternatingGroup.ofSubtype s ⟨Equiv.Perm.subtypePerm (h : Equiv.Perm (Fin 6))
        (fun x => (hp x).symm), by
          rw [Equiv.Perm.mem_alternatingGroup, ← Equiv.Perm.sign_ofSubtype,
            Equiv.Perm.ofSubtype_subtypePerm _ hmove]
          exact Equiv.Perm.mem_alternatingGroup.mp h.2⟩ = h := by
      apply Subtype.ext
      rw [alternatingGroup.coe_ofSubtype, Equiv.Perm.ofSubtype_subtypePerm _ hmove]
    rw [← hk]
    exact hf1 _
  let r : Fin 6 → alternatingGroup (Fin 6) := fun x => ⟨ae8e_rep x, ae8e_rep_mem x⟩
  have hr : ∀ x, (r x : Equiv.Perm (Fin 6)) x = 0 := fun x => ae8e_rep_zero x
  have hwd : ∀ (g g' : alternatingGroup (Fin 6)) (x : Fin 6),
      (g : Equiv.Perm (Fin 6)) x = 0 → (g' : Equiv.Perm (Fin 6)) x = 0 → c g' 0 = c g 0 := by
    intro g g' x hg hg'
    have hginv : (g : Equiv.Perm (Fin 6))⁻¹ 0 = x := Equiv.Perm.inv_eq_iff_eq.mpr hg.symm
    have hh0 : ((g' * g⁻¹ : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) 0 = 0 := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply, hginv]
      exact hg'
    have hgg : g' = (g' * g⁻¹ : alternatingGroup (Fin 6)) * g := by group
    rw [hgg, hcp _ _ 0, hkey _ hh0, (Equiv.symm_apply_eq _).mpr hh0.symm, zero_add]
  let v : Fin 6 → ZMod 2 := fun x => c (r x) 0
  have hcob : ∀ (σ : alternatingGroup (Fin 6)) (x : Fin 6),
      c σ x = v ((σ : Equiv.Perm (Fin 6)).symm x) + v x := by
    intro σ x
    have h1 : ((r x * σ : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6))
        ((σ : Equiv.Perm (Fin 6)).symm x) = 0 := by
      rw [Subgroup.coe_mul, Equiv.Perm.mul_apply, Equiv.apply_symm_apply]
      exact hr x
    have h2 := hwd (r x * σ) (r ((σ : Equiv.Perm (Fin 6)).symm x)) _ h1 (hr _)
    have h3 := hcp (r x) σ 0
    have h4 : (r x : Equiv.Perm (Fin 6)).symm 0 = x := (Equiv.symm_apply_eq _).mpr (hr x).symm
    rw [h4] at h3
    have h5 : v ((σ : Equiv.Perm (Fin 6)).symm x) = v x + c σ x := by
      show c (r ((σ : Equiv.Perm (Fin 6)).symm x)) 0 = c (r x) 0 + c σ x
      rw [h2, h3]
    exact ae8e_zmod2_swap _ _ _ h5
  refine ⟨v, fun σ => ?_⟩
  funext x
  rw [Pi.add_apply]
  exact hcob σ x

section AERelabel

open CFSG.ClassicalInvolution.Q3.AE Wr

open Classical in
@[expose] noncomputable def ae8e_ext6 (ι : Fin 6 ↪ Fin 8) (v : Fin 6 → ZMod 2) : Fin 8 → ZMod 2 :=
  fun x => if h : x ∈ Set.range ι then v (ι.toEquivRange.symm ⟨x, h⟩) else 0

open Classical in
@[expose] noncomputable def ae8e_permExt6 (ι : Fin 6 ↪ Fin 8) (s : Equiv.Perm (Fin 6)) :
    Equiv.Perm (Fin 8) :=
  s.extendDomain ι.toEquivRange

theorem ae8e_ext6_apply (ι : Fin 6 ↪ Fin 8) (v : Fin 6 → ZMod 2) (i : Fin 6) :
    ae8e_ext6 ι v (ι i) = v i := by
  classical
  unfold ae8e_ext6
  split_ifs with h
  · congr 1
    apply ι.toEquivRange.injective
    rw [Equiv.apply_symm_apply]
    rfl
  · exact absurd (Set.mem_range_self i) h

theorem ae8e_ext6_of_not_mem (ι : Fin 6 ↪ Fin 8) (v : Fin 6 → ZMod 2) {x : Fin 8}
    (hx : x ∉ Set.range ι) : ae8e_ext6 ι v x = 0 := by
  classical
  simp [ae8e_ext6, hx]

theorem ae8e_permExt6_apply (ι : Fin 6 ↪ Fin 8) (s : Equiv.Perm (Fin 6)) (i : Fin 6) :
    ae8e_permExt6 ι s (ι i) = ι (s i) := by
  classical
  unfold ae8e_permExt6
  have := Equiv.Perm.extendDomain_apply_image s ι.toEquivRange i
  simpa using this

theorem ae8e_permExt6_of_not_mem (ι : Fin 6 ↪ Fin 8) (s : Equiv.Perm (Fin 6)) {x : Fin 8}
    (hx : x ∉ Set.range ι) : ae8e_permExt6 ι s x = x := by
  classical
  unfold ae8e_permExt6
  exact Equiv.Perm.extendDomain_apply_not_subtype s ι.toEquivRange hx

theorem ae8e_permExt6_mul (ι : Fin 6 ↪ Fin 8) (s t : Equiv.Perm (Fin 6)) :
    ae8e_permExt6 ι (s * t) = ae8e_permExt6 ι s * ae8e_permExt6 ι t := by
  classical
  unfold ae8e_permExt6
  rw [Equiv.Perm.extendDomain_mul]

theorem ae8e_permExt6_one (ι : Fin 6 ↪ Fin 8) : ae8e_permExt6 ι 1 = 1 := by
  classical
  unfold ae8e_permExt6
  exact Equiv.Perm.extendDomain_one ι.toEquivRange

@[expose] noncomputable def ae8e_relab6 (ι : Fin 6 ↪ Fin 8) : Wr 6 →* Wr 8 where
  toFun a := ⟨ae8e_ext6 ι a.vec, ae8e_permExt6 ι a.perm⟩
  map_one' := by
    refine Wr.ext (funext fun x => ?_) (ae8e_permExt6_one ι)
    show ae8e_ext6 ι (1 : Wr 6).vec x = (1 : Wr 8).vec x
    by_cases hx : x ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hx
      rw [ae8e_ext6_apply]
      rfl
    · rw [ae8e_ext6_of_not_mem ι _ hx]
      rfl
  map_mul' a b := by
    refine Wr.ext (funext fun x => ?_) (ae8e_permExt6_mul ι a.perm b.perm)
    show ae8e_ext6 ι (a * b).vec x =
      ae8e_ext6 ι a.vec x + ae8e_ext6 ι b.vec ((ae8e_permExt6 ι a.perm).symm x)
    by_cases hx : x ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hx
      have h1 : (ae8e_permExt6 ι a.perm).symm (ι i) = ι (a.perm.symm i) := by
        apply (ae8e_permExt6 ι a.perm).injective
        rw [Equiv.apply_symm_apply, ae8e_permExt6_apply, Equiv.apply_symm_apply]
      rw [h1, ae8e_ext6_apply, ae8e_ext6_apply, ae8e_ext6_apply, mul_vec]
    · have h1 : (ae8e_permExt6 ι a.perm).symm x = x := by
        apply (ae8e_permExt6 ι a.perm).injective
        rw [Equiv.apply_symm_apply, ae8e_permExt6_of_not_mem ι _ hx]
      rw [h1, ae8e_ext6_of_not_mem ι _ hx, ae8e_ext6_of_not_mem ι _ hx,
        ae8e_ext6_of_not_mem ι _ hx, add_zero]

theorem ae8e_relab6_vec (ι : Fin 6 ↪ Fin 8) (a : Wr 6) :
    (ae8e_relab6 ι a).vec = ae8e_ext6 ι a.vec := rfl

theorem ae8e_relab6_perm (ι : Fin 6 ↪ Fin 8) (a : Wr 6) :
    (ae8e_relab6 ι a).perm = ae8e_permExt6 ι a.perm := rfl


@[expose] def ae8e_relab4 (τ : Equiv.Perm (Fin 4)) (a : Wr 4) : Wr 4 :=
  ⟨fun i => a.vec (τ.symm i), τ * a.perm * τ⁻¹⟩

theorem ae8e_relab4_inv (τ : Equiv.Perm (Fin 4)) (x : Wr 4) :
    ae8e_relab4 τ (ae8e_relab4 τ⁻¹ x) = x := by
  refine Wr.ext (funext fun i => ?_) ?_
  · show x.vec (τ⁻¹.symm (τ.symm i)) = x.vec i
    congr 1
    simp [Equiv.Perm.inv_def]
  · show τ * (τ⁻¹ * x.perm * τ⁻¹⁻¹) * τ⁻¹ = x.perm
    group

theorem ae8e_relab4_kQ : ∀ τ : Equiv.Perm (Fin 4),
    ((∀ a ∈ kList, ae8e_relab4 τ a ∈ kList) ∧ (∀ a ∈ kList, ae8e_relab4 τ⁻¹ a ∈ kList)) ∨
    ((∀ a ∈ kList, ae8e_relab4 τ a ∈ kStarList) ∧
      (∀ a ∈ kStarList, ae8e_relab4 τ⁻¹ a ∈ kList)) := by
  decide +kernel

@[expose] def ae8e_relab4Hom (τ : Equiv.Perm (Fin 4)) : Wr 4 →* Wr 4 where
  toFun := ae8e_relab4 τ
  map_one' := by
    refine Wr.ext (funext fun i => ?_) ?_
    · show (1 : Wr 4).vec (τ.symm i) = (1 : Wr 4).vec i
      rfl
    · show τ * (1 : Wr 4).perm * τ⁻¹ = (1 : Wr 4).perm
      rw [one_perm, mul_one, mul_inv_cancel]
  map_mul' a b := by
    refine Wr.ext (funext fun i => ?_) ?_
    · show (a * b).vec (τ.symm i) = a.vec (τ.symm i) + b.vec (τ.symm ((τ * a.perm * τ⁻¹).symm i))
      rw [mul_vec]
      have hinv : ∀ j, (τ * a.perm * τ⁻¹).symm j = τ (a.perm.symm (τ.symm j)) := fun j => rfl
      congr 2
      rw [hinv, Equiv.symm_apply_apply]
    · show τ * (a * b).perm * τ⁻¹ = (τ * a.perm * τ⁻¹) * (τ * b.perm * τ⁻¹)
      rw [mul_perm]
      group

theorem ae8e_relab4_kQStar : ∀ τ : Equiv.Perm (Fin 4),
    ((∀ a ∈ kStarList, ae8e_relab4 τ a ∈ kList) ∧ (∀ a ∈ kList, ae8e_relab4 τ⁻¹ a ∈ kStarList)) ∨
    ((∀ a ∈ kStarList, ae8e_relab4 τ a ∈ kStarList) ∧
      (∀ a ∈ kStarList, ae8e_relab4 τ⁻¹ a ∈ kStarList)) := by
  decide +kernel

theorem ae8e_embed_trans_perm {n : ℕ} (κ : Fin 4 ↪ Fin n) (τ : Equiv.Perm (Fin 4)) (a : Wr 4) :
    embed (τ.toEmbedding.trans κ) a = embed κ (ae8e_relab4 τ a) := by
  refine Wr.ext (funext fun x => ?_) ?_
  · show embedVec (τ.toEmbedding.trans κ) a.vec x = embedVec κ (ae8e_relab4 τ a).vec x
    by_cases hx : x ∈ Set.range κ
    · obtain ⟨j, rfl⟩ := hx
      obtain ⟨i, rfl⟩ : ∃ i, τ i = j := ⟨τ.symm j, τ.apply_symm_apply j⟩
      have h1 : embedVec (τ.toEmbedding.trans κ) a.vec (κ (τ i)) = a.vec i :=
        embedVec_apply (τ.toEmbedding.trans κ) a.vec i
      have h2 : embedVec κ (ae8e_relab4 τ a).vec (κ (τ i)) = a.vec i := by
        rw [embedVec_apply κ (ae8e_relab4 τ a).vec (τ i)]
        show a.vec (τ.symm (τ i)) = a.vec i
        rw [Equiv.symm_apply_apply]
      rw [h1, h2]
    · have hx' : x ∉ Set.range (τ.toEmbedding.trans κ) := by
        rintro ⟨i, rfl⟩
        exact hx ⟨τ i, rfl⟩
      rw [embedVec_of_not_mem _ _ hx', embedVec_of_not_mem _ _ hx]
  · show embedPerm (τ.toEmbedding.trans κ) a.perm = embedPerm κ (τ * a.perm * τ⁻¹)
    refine Equiv.ext fun x => ?_
    show embedPerm (τ.toEmbedding.trans κ) a.perm x = embedPerm κ (τ * a.perm * τ⁻¹) x
    by_cases hx : x ∈ Set.range κ
    · obtain ⟨j, rfl⟩ := hx
      obtain ⟨i, rfl⟩ : ∃ i, τ i = j := ⟨τ.symm j, τ.apply_symm_apply j⟩
      have h1 : embedPerm (τ.toEmbedding.trans κ) a.perm (κ (τ i)) = κ (τ (a.perm i)) :=
        embedPerm_apply (τ.toEmbedding.trans κ) a.perm i
      have h2 : embedPerm κ (τ * a.perm * τ⁻¹) (κ (τ i)) = κ (τ (a.perm i)) := by
        rw [embedPerm_apply κ _ (τ i)]
        congr 1
        show τ (a.perm (τ.symm (τ i))) = τ (a.perm i)
        rw [Equiv.symm_apply_apply]
      rw [h1, h2]
    · have hx' : x ∉ Set.range (τ.toEmbedding.trans κ) := by
        rintro ⟨i, rfl⟩
        exact hx ⟨τ i, rfl⟩
      rw [embedPerm_of_not_mem _ _ hx', embedPerm_of_not_mem _ _ hx]

theorem ae8e_relab6_embed (ι : Fin 6 ↪ Fin 8) (κ : Fin 4 ↪ Fin 6) (a : Wr 4) :
    ae8e_relab6 ι (embed κ a) = embed (κ.trans ι) a := by
  refine Wr.ext (funext fun x => ?_) ?_
  · show ae8e_ext6 ι (embedVec κ a.vec) x = embedVec (κ.trans ι) a.vec x
    by_cases hx : x ∈ Set.range (κ.trans ι)
    · obtain ⟨i, rfl⟩ := hx
      have h1 : ae8e_ext6 ι (embedVec κ a.vec) (ι (κ i)) = a.vec i := by
        rw [ae8e_ext6_apply, embedVec_apply]
      have h2 : embedVec (κ.trans ι) a.vec ((κ.trans ι) i) = a.vec i :=
        embedVec_apply (κ.trans ι) a.vec i
      rw [h2]
      exact h1
    · by_cases hx' : x ∈ Set.range ι
      · obtain ⟨j, rfl⟩ := hx'
        have hj : j ∉ Set.range κ := by
          rintro ⟨i, rfl⟩
          exact hx ⟨i, rfl⟩
        rw [ae8e_ext6_apply, embedVec_of_not_mem κ _ hj, embedVec_of_not_mem _ _ hx]
      · rw [ae8e_ext6_of_not_mem ι _ hx', embedVec_of_not_mem _ _ hx]
  · show ae8e_permExt6 ι (embedPerm κ a.perm) = embedPerm (κ.trans ι) a.perm
    refine Equiv.ext fun x => ?_
    show ae8e_permExt6 ι (embedPerm κ a.perm) x = embedPerm (κ.trans ι) a.perm x
    by_cases hx : x ∈ Set.range (κ.trans ι)
    · obtain ⟨i, rfl⟩ := hx
      have h1 : ae8e_permExt6 ι (embedPerm κ a.perm) (ι (κ i)) = ι (κ (a.perm i)) := by
        rw [ae8e_permExt6_apply, embedPerm_apply]
      have h2 : embedPerm (κ.trans ι) a.perm ((κ.trans ι) i) = ι (κ (a.perm i)) :=
        embedPerm_apply (κ.trans ι) a.perm i
      rw [h2]
      exact h1
    · by_cases hx' : x ∈ Set.range ι
      · obtain ⟨j, rfl⟩ := hx'
        have hj : j ∉ Set.range κ := by
          rintro ⟨i, rfl⟩
          exact hx ⟨i, rfl⟩
        rw [ae8e_permExt6_apply, embedPerm_of_not_mem κ _ hj, embedPerm_of_not_mem _ _ hx]
      · rw [ae8e_permExt6_of_not_mem ι _ hx', embedPerm_of_not_mem _ _ hx]


theorem ae8e_relab6_memK (ι : Fin 6 ↪ Fin 8) (κ : Fin 4 ↪ Fin 6) :
    (memK κ).map (ae8e_relab6 ι) = memK (κ.trans ι) := by
  have hc : (ae8e_relab6 ι).comp (embed κ) = embed (κ.trans ι) :=
    MonoidHom.ext fun a => ae8e_relab6_embed ι κ a
  unfold memK
  rw [Subgroup.map_map, hc]

theorem ae8e_relab6_memKStar (ι : Fin 6 ↪ Fin 8) (κ : Fin 4 ↪ Fin 6) :
    (memKStar κ).map (ae8e_relab6 ι) = memKStar (κ.trans ι) := by
  have hc : (ae8e_relab6 ι).comp (embed κ) = embed (κ.trans ι) :=
    MonoidHom.ext fun a => ae8e_relab6_embed ι κ a
  unfold memKStar
  rw [Subgroup.map_map, hc]

theorem ae8e_kQ_map_relab (τ : Equiv.Perm (Fin 4)) :
    kQ.map (ae8e_relab4Hom τ) = kQ ∨ kQ.map (ae8e_relab4Hom τ) = kQStar := by
  rcases ae8e_relab4_kQ τ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact h1 a ha
    · intro hx
      exact ⟨ae8e_relab4 τ⁻¹ x, h2 x hx, ae8e_relab4_inv τ x⟩
  · right
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact h1 a ha
    · intro hx
      exact ⟨ae8e_relab4 τ⁻¹ x, h2 x hx, ae8e_relab4_inv τ x⟩

theorem ae8e_kQStar_map_relab (τ : Equiv.Perm (Fin 4)) :
    kQStar.map (ae8e_relab4Hom τ) = kQ ∨ kQStar.map (ae8e_relab4Hom τ) = kQStar := by
  rcases ae8e_relab4_kQStar τ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact h1 a ha
    · intro hx
      exact ⟨ae8e_relab4 τ⁻¹ x, h2 x hx, ae8e_relab4_inv τ x⟩
  · right
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact h1 a ha
    · intro hx
      exact ⟨ae8e_relab4 τ⁻¹ x, h2 x hx, ae8e_relab4_inv τ x⟩

theorem ae8e_memK_trans_perm {n : ℕ} (κ : Fin 4 ↪ Fin n) (τ : Equiv.Perm (Fin 4)) :
    memK (τ.toEmbedding.trans κ) = memK κ ∨ memK (τ.toEmbedding.trans κ) = memKStar κ := by
  have hc : (embed κ).comp (ae8e_relab4Hom τ) = embed (τ.toEmbedding.trans κ) :=
    MonoidHom.ext fun a => (ae8e_embed_trans_perm κ τ a).symm
  have key : memK (τ.toEmbedding.trans κ) = (kQ.map (ae8e_relab4Hom τ)).map (embed κ) := by
    unfold memK
    rw [Subgroup.map_map, hc]
  rw [key]
  rcases ae8e_kQ_map_relab τ with h | h
  · left
    rw [h]
    rfl
  · right
    rw [h]
    rfl

theorem ae8e_memKStar_trans_perm {n : ℕ} (κ : Fin 4 ↪ Fin n) (τ : Equiv.Perm (Fin 4)) :
    memKStar (τ.toEmbedding.trans κ) = memK κ ∨
      memKStar (τ.toEmbedding.trans κ) = memKStar κ := by
  have hc : (embed κ).comp (ae8e_relab4Hom τ) = embed (τ.toEmbedding.trans κ) :=
    MonoidHom.ext fun a => (ae8e_embed_trans_perm κ τ a).symm
  have key : memKStar (τ.toEmbedding.trans κ) = (kQStar.map (ae8e_relab4Hom τ)).map (embed κ) := by
    unfold memKStar
    rw [Subgroup.map_map, hc]
  rw [key]
  rcases ae8e_kQStar_map_relab τ with h | h
  · left
    rw [h]
    rfl
  · right
    rw [h]
    rfl

theorem ae8e_exists_perm_of_range_eq {n : ℕ} (κ κ' : Fin 4 ↪ Fin n)
    (h : Set.range κ = Set.range κ') : ∃ τ : Equiv.Perm (Fin 4), ∀ i, κ i = κ' (τ i) := by
  classical
  have hmem : ∀ i, κ i ∈ Set.range κ' := fun i => h ▸ Set.mem_range_self i
  let f : Fin 4 → Fin 4 := fun i => κ'.toEquivRange.symm ⟨κ i, hmem i⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply κ.injective
    have := congrArg (fun k => (κ'.toEquivRange k : Fin n)) hij
    simpa [f] using this
  have hb : Function.Bijective f := Finite.injective_iff_bijective.mp hf
  refine ⟨Equiv.ofBijective f hb, fun i => ?_⟩
  show κ i = κ' (f i)
  have h2 : κ'.toEquivRange (f i) = ⟨κ i, hmem i⟩ := Equiv.apply_symm_apply _ _
  have h3 : (κ'.toEquivRange (f i) : Fin n) = κ' (f i) := rfl
  rw [← h3, h2]


theorem ae8e_range_trans_emb (α : Finset (Fin 6)) (h : α.card = 4) (ι : Fin 6 ↪ Fin 8) :
    Set.range ((emb α h).trans ι) = ((α.image ι : Finset (Fin 8)) : Set (Fin 8)) := by
  ext x
  simp only [Set.mem_range, Function.Embedding.trans_apply, Finset.coe_image, Set.mem_image,
    Finset.mem_coe]
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨(emb α h) i, ?_, rfl⟩
    have := Set.mem_range_self (f := emb α h) i
    rw [range_emb] at this
    exact this
  · rintro ⟨a, ha, rfl⟩
    have : a ∈ Set.range (emb α h) := by rw [range_emb]; exact ha
    obtain ⟨i, rfl⟩ := this
    exact ⟨i, rfl⟩

theorem ae8e_relab6_memAt (ι : Fin 6 ↪ Fin 8) (α : Finset (Fin 6)) (h : α.card = 4) (b : Bool) :
    ∃ (β : Finset (Fin 8)) (hβ : β.card = 4) (b' : Bool),
      (memAt α h b).map (ae8e_relab6 ι) = memAt β hβ b' := by
  have hβ : (Finset.image (⇑ι) α).card = 4 := by
    rw [Finset.card_image_of_injective _ ι.injective, h]
  obtain ⟨τ, hτ⟩ := ae8e_exists_perm_of_range_eq ((emb α h).trans ι)
    (emb (Finset.image (⇑ι) α) hβ) (by rw [ae8e_range_trans_emb, range_emb])
  have hκ : (emb α h).trans ι = τ.toEmbedding.trans (emb (Finset.image (⇑ι) α) hβ) :=
    Function.Embedding.ext fun i => hτ i
  cases b
  · have h1 : (memKStar (emb α h)).map (ae8e_relab6 ι) =
        memKStar (τ.toEmbedding.trans (emb (Finset.image (⇑ι) α) hβ)) := by
      rw [ae8e_relab6_memKStar, hκ]
    rcases ae8e_memKStar_trans_perm (emb (Finset.image (⇑ι) α) hβ) τ with h2 | h2
    · exact ⟨Finset.image (⇑ι) α, hβ, true, h1.trans h2⟩
    · exact ⟨Finset.image (⇑ι) α, hβ, false, h1.trans h2⟩
  · have h1 : (memK (emb α h)).map (ae8e_relab6 ι) =
        memK (τ.toEmbedding.trans (emb (Finset.image (⇑ι) α) hβ)) := by
      rw [ae8e_relab6_memK, hκ]
    rcases ae8e_memK_trans_perm (emb (Finset.image (⇑ι) α) hβ) τ with h2 | h2
    · exact ⟨Finset.image (⇑ι) α, hβ, true, h1.trans h2⟩
    · exact ⟨Finset.image (⇑ι) α, hβ, false, h1.trans h2⟩


end AERelabel

@[expose] def ae8e_ext (w : Fin 6 → ZMod 2) : Fin 8 → ZMod 2 := fun i =>
  if h : i.val < 6 then w ⟨i.val, h⟩ else if i.val = 6 then ∑ j, w j else 0

@[expose] def ae8e_supp (v : Fin 8 → ZMod 2) : Finset (Fin 8) := Finset.univ.filter fun i => v i ≠ 0

@[expose] def ae8e_pair (w : Fin 6 → ZMod 2) : Finset (Fin 8) :=
  if (ae8e_supp (ae8e_ext w)).card = 2 then ae8e_supp (ae8e_ext w)
  else (ae8e_supp (ae8e_ext w))ᶜ

abbrev ae8e_inW (w : Fin 6 → ZMod 2) : Prop :=
  wt w = 1 ∨ wt w = 2 ∨ wt w = 5 ∨ wt w = 6

theorem ae8e_pair_card : ∀ w : Fin 6 → ZMod 2, ae8e_inW w → (ae8e_pair w).card = 2 := by
  decide +kernel

theorem ae8e_pair_inj : ∀ w w' : Fin 6 → ZMod 2, ae8e_inW w → ae8e_inW w' →
    ae8e_pair w = ae8e_pair w' → w = w' := by
  decide +kernel

theorem ae8e_pair_surj : ∀ s : Finset (Fin 8), s.card = 2 →
    ∃ w : Fin 6 → ZMod 2, ae8e_inW w ∧ ae8e_pair w = s := by
  decide +kernel

theorem ae8e_M2 : ∀ w w' : Fin 6 → ZMod 2, w ≠ w' → ae8e_inW w → ae8e_inW w' →
    (ae8e_inW (w + w') ↔ (ae8e_pair w ∩ ae8e_pair w').Nonempty) := by
  decide +kernel

theorem ae8e_M3 : ∀ w w' : Fin 6 → ZMod 2, w ≠ w' → ae8e_inW w → ae8e_inW w' →
    ae8e_inW (w + w') → ae8e_pair (w + w') = symmDiff (ae8e_pair w) (ae8e_pair w') := by
  decide +kernel

theorem ae8e_triple : ∀ i j k : Fin 8, i ≠ j → j ≠ k → i ≠ k →
    symmDiff ({i, j} : Finset (Fin 8)) {j, k} = {i, k} := by
  decide +kernel

@[expose] def ae8e_c6 (a : Fin 6) : Fin 8 := Fin.castLE (by norm_num) a

theorem ae8e_c6_injective : Function.Injective ae8e_c6 :=
  Fin.castLE_injective (by norm_num)

@[expose] def ae8e_e2 (a b : Fin 6) : Fin 6 → ZMod 2 := fun k => if k = a ∨ k = b then 1 else 0

theorem ae8e_e2_pair : ∀ a b : Fin 6, a ≠ b →
    ae8e_pair (ae8e_e2 a b) = {ae8e_c6 a, ae8e_c6 b} := by
  decide +kernel

theorem ae8e_e2_inW : ∀ a b : Fin 6, a ≠ b → ae8e_inW (ae8e_e2 a b) := by
  decide +kernel

theorem ae8e_e2_unique : ∀ (w : Fin 6 → ZMod 2) (a b : Fin 6), a ≠ b → ae8e_inW w →
    ae8e_pair w = {ae8e_c6 a, ae8e_c6 b} → w = ae8e_e2 a b := by
  decide +kernel

theorem ae8e_e2_eq_single : ∀ a b : Fin 6, a ≠ b →
    ae8e_e2 a b = (Pi.single a (1 : ZMod 2) : Fin 6 → ZMod 2) + Pi.single b 1 := by
  decide +kernel

theorem ae8e_e2_perm (τ : Equiv.Perm (Fin 6)) (a b : Fin 6) :
    (fun k => ae8e_e2 a b (τ.symm k)) = ae8e_e2 (τ a) (τ b) := by
  funext k
  simp [ae8e_e2, Equiv.symm_apply_eq]

theorem ae8e_zmod2_alg : ∀ x y p q : ZMod 2, x + y = p + q → x = p + (q + y) := by
  decide

theorem ae8e_zmod2_alg0 : ∀ t x : ZMod 2, x = t + (t + x) := by
  decide

theorem ae8e_three_points : ∀ a : Fin 6, ∃ b c : Fin 6, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  decide +kernel

theorem ae8e_lin (w : Fin 6 → Fin 6 → ZMod 2)
    (hw : ∀ a b : Fin 6, a ≠ b →
      w a + w b = (Pi.single a (1 : ZMod 2) : Fin 6 → ZMod 2) + Pi.single b 1)
    (v : Fin 6 → ZMod 2) (hv : ∑ i, v i = 0) : ∑ a, v a • w a = v := by
  set c : Fin 6 → ZMod 2 := (Pi.single 0 (1 : ZMod 2) : Fin 6 → ZMod 2) + w 0 with hc
  have hwc : ∀ a, w a = (Pi.single a (1 : ZMod 2) : Fin 6 → ZMod 2) + c := by
    intro a
    funext i
    rw [Pi.add_apply, hc, Pi.add_apply]
    by_cases ha : a = 0
    · subst ha
      exact ae8e_zmod2_alg0 _ _
    · have h := congrFun (hw a 0 ha) i
      rw [Pi.add_apply, Pi.add_apply] at h
      exact ae8e_zmod2_alg _ _ _ _ h
  funext i
  have h1 : ∀ a, w a i = (Pi.single a (1 : ZMod 2) : Fin 6 → ZMod 2) i + c i := fun a => by
    have := congrFun (hwc a) i
    rwa [Pi.add_apply] at this
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, h1, mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, hv, zero_mul, add_zero]
  simp [Pi.single_apply]

@[expose] def ae8e_iota (σ : Equiv.Perm (Fin 8)) : Fin 6 ↪ Fin 8 :=
  ⟨fun a => σ (ae8e_c6 a), fun a b h => ae8e_c6_injective (σ.injective h)⟩

theorem ae8e_iota_apply (σ : Equiv.Perm (Fin 8)) (a : Fin 6) :
    ae8e_iota σ a = σ (ae8e_c6 a) := rfl

theorem ae8e_sum_range {M : Type*} [AddCommMonoid M] (ι : Fin 6 ↪ Fin 8) (g : Fin 8 → M)
    (hg : ∀ k, k ∉ Set.range ι → g k = 0) : ∑ k, g k = ∑ a, g (ι a) := by
  classical
  rw [← Finset.sum_map Finset.univ ι g]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro k _ hk
  apply hg
  rintro ⟨a, rfl⟩
  exact hk (Finset.mem_map_of_mem _ (Finset.mem_univ a))

section Model

variable {c : Chart Ω u} {co : Coords c}

theorem ae8e_delta_mem (cl : Classes co) (x : ↥(Delta u)) : (x : G) ∈ zGroup Ω := by
  obtain ⟨hx, -⟩ := (cl.u_class (x : G)).mp x.2
  exact hx

@[expose] def ae8e_coord (cl : Classes co) (x : ↥(Delta u)) : Fin 6 → ZMod 2 :=
  (co.e ⟨(x : G), ae8e_delta_mem cl x⟩).toAdd

theorem ae8e_coord_inW (cl : Classes co) (x : ↥(Delta u)) : ae8e_inW (ae8e_coord cl x) := by
  obtain ⟨hx, h⟩ := (cl.u_class (x : G)).mp x.2
  exact h

theorem ae8e_coord_inj (cl : Classes co) {x y : ↥(Delta u)}
    (h : ae8e_coord cl x = ae8e_coord cl y) : x = y := by
  unfold ae8e_coord at h
  have h1 : co.e ⟨(x : G), ae8e_delta_mem cl x⟩ = co.e ⟨(y : G), ae8e_delta_mem cl y⟩ :=
    Multiplicative.toAdd.injective h
  have h2 : (⟨(x : G), ae8e_delta_mem cl x⟩ : ↥(zGroup Ω)) = ⟨(y : G), ae8e_delta_mem cl y⟩ :=
    co.e.injective h1
  have h3 : (x : G) = (y : G) := congrArg (fun d : ↥(zGroup Ω) => (d : G)) h2
  exact Subtype.ext h3

theorem ae8e_coord_surj (cl : Classes co) {w : Fin 6 → ZMod 2} (hw : ae8e_inW w) :
    ∃ x : ↥(Delta u), ae8e_coord cl x = w := by
  have hd : (co.e.symm (Multiplicative.ofAdd w) : G) ∈ Delta u := by
    refine (cl.u_class _).mpr ⟨(co.e.symm (Multiplicative.ofAdd w)).2, ?_⟩
    simpa using hw
  exact ⟨⟨_, hd⟩, by simp [ae8e_coord]⟩

theorem ae8e_coord_mul (cl : Classes co) {x y z : ↥(Delta u)} (h : (z : G) = (x : G) * y) :
    ae8e_coord cl z = ae8e_coord cl x + ae8e_coord cl y := by
  have h' : (⟨(z : G), ae8e_delta_mem cl z⟩ : ↥(zGroup Ω)) =
      ⟨(x : G), ae8e_delta_mem cl x⟩ * ⟨(y : G), ae8e_delta_mem cl y⟩ := Subtype.ext h
  unfold ae8e_coord
  rw [h', map_mul, toAdd_mul]

theorem ae8e_mul_mem_iff (cl : Classes co) {x y : ↥(Delta u)} (hxy : x ≠ y) :
    (x : G) * y ∈ Delta u ↔ ae8e_inW (ae8e_coord cl x + ae8e_coord cl y) := by
  constructor
  · intro hm
    have hD : (x : G) * y ∈ zGroup Ω :=
      (zGroup Ω).mul_mem (ae8e_delta_mem cl x) (ae8e_delta_mem cl y)
    have h1 := ae8e_coord_inW cl ⟨(x : G) * y, hm⟩
    rwa [ae8e_coord_mul cl (z := ⟨(x : G) * y, hm⟩) rfl] at h1
  · intro hw
    obtain ⟨z, hz⟩ := ae8e_coord_surj cl hw
    have h1 : co.e ⟨(z : G), ae8e_delta_mem cl z⟩ = co.e
        (⟨(x : G), ae8e_delta_mem cl x⟩ * ⟨(y : G), ae8e_delta_mem cl y⟩) := by
      apply Multiplicative.toAdd.injective
      rw [map_mul, toAdd_mul]
      exact hz
    have h2 : (⟨(z : G), ae8e_delta_mem cl z⟩ : ↥(zGroup Ω)) =
        ⟨(x : G), ae8e_delta_mem cl x⟩ * ⟨(y : G), ae8e_delta_mem cl y⟩ :=
      co.e.injective h1
    have hzxy : (z : G) = (x : G) * y := congrArg (fun d : ↥(zGroup Ω) => (d : G)) h2
    exact hzxy ▸ z.2

@[expose] noncomputable def ae8e_E0 (cl : Classes co) :
    ↥(Delta u) ≃ {s : Finset (Fin 8) // s.card = 2} :=
  Equiv.ofBijective
    (fun x => ⟨ae8e_pair (ae8e_coord cl x), ae8e_pair_card _ (ae8e_coord_inW cl x)⟩)
    (by
      refine ⟨fun x y h => ?_, fun ⟨s, hs⟩ => ?_⟩
      · apply ae8e_coord_inj cl
        apply ae8e_pair_inj _ _ (ae8e_coord_inW cl x) (ae8e_coord_inW cl y)
        exact congrArg Subtype.val h
      · obtain ⟨w, hw, hws⟩ := ae8e_pair_surj s hs
        obtain ⟨x, hx⟩ := ae8e_coord_surj cl hw
        exact ⟨x, Subtype.ext (by simp only [hx]; exact hws)⟩)

theorem ae8e_card_pos (s : {s : Finset (Fin 8) // s.card = 2}) :
    (s : Finset (Fin 8)).Nonempty :=
  Finset.card_pos.mp (by rw [s.2]; norm_num)

theorem ae8e_exists_perm (cl : Classes co) (pt : Points u) :
    ∃ σ : Equiv.Perm (Fin 8), ∀ x : ↥(Delta u),
      (pt.E x : Finset (Fin 8)) = (ae8e_pair (ae8e_coord cl x)).image σ := by
  let F : Equiv.Perm {s : Finset (Fin 8) // s.card = 2} := (ae8e_E0 cl).symm.trans pt.E
  have hF' : ∀ x : ↥(Delta u), F (ae8e_E0 cl x) = pt.E x := fun x => by
    simp [F]
  have hF : ∀ s t : {s : Finset (Fin 8) // s.card = 2},
      ((s : Finset (Fin 8)) ∩ (t : Finset (Fin 8))).Nonempty ↔
        (((F s : {s : Finset (Fin 8) // s.card = 2}) : Finset (Fin 8)) ∩
          ((F t : {s : Finset (Fin 8) // s.card = 2}) : Finset (Fin 8))).Nonempty := by
    intro s t
    obtain ⟨x, rfl⟩ := (ae8e_E0 cl).surjective s
    obtain ⟨y, rfl⟩ := (ae8e_E0 cl).surjective t
    rw [hF' x, hF' y]
    by_cases hxy : x = y
    · subst hxy
      rw [Finset.inter_self, Finset.inter_self]
      exact ⟨fun _ => ae8e_card_pos _, fun _ => ae8e_card_pos _⟩
    · have hcne : ae8e_coord cl x ≠ ae8e_coord cl y := fun h => hxy (ae8e_coord_inj cl h)
      have h1 : ((ae8e_pair (ae8e_coord cl x)) ∩ (ae8e_pair (ae8e_coord cl y))).Nonempty ↔
          (x : G) * y ∈ Delta u := by
        rw [ae8e_mul_mem_iff cl hxy]
        exact (ae8e_M2 _ _ hcne (ae8e_coord_inW cl x) (ae8e_coord_inW cl y)).symm
      have h2 : (x : G) * y ∈ Delta u ↔
          ((pt.E x : Finset (Fin 8)) ∩ (pt.E y : Finset (Fin 8))).Nonempty :=
        ⟨fun h => ((pt.adj x y).mp ⟨hxy, h⟩).2, fun h => ((pt.adj x y).mpr ⟨hxy, h⟩).2⟩
      exact h1.trans h2
  obtain ⟨σ, hσ, -⟩ := T8_exists_perm F hF
  refine ⟨σ, fun x => ?_⟩
  have h := hσ (ae8e_E0 cl x)
  rw [hF' x] at h
  exact h

end Model


namespace Points

variable {c : Chart Ω u} {co : Coords c}

theorem mul_eq (H : End18.Hyp Ω) (cl : Classes co) (pt : Points u) {x y z : ↥(Delta u)}
    {i j k : Fin 8} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hx : (pt.E x : Finset (Fin 8)) = {i, j}) (hy : (pt.E y : Finset (Fin 8)) = {j, k})
    (hz : (pt.E z : Finset (Fin 8)) = {i, k}) : (x : G) * y = z := by
  obtain ⟨σ, hσ⟩ := ae8e_exists_perm cl pt
  have hxy : x ≠ y := by
    intro h
    subst h
    have h1 : ({i, j} : Finset (Fin 8)) = {j, k} := hx.symm.trans hy
    have h2 : i ∈ ({j, k} : Finset (Fin 8)) := by
      rw [← h1]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at h2
    rcases h2 with h2 | h2
    · exact hij h2
    · exact hik h2
  have hmem : (x : G) * y ∈ Delta u :=
    ((pt.adj x y).mpr ⟨hxy, ⟨j, by simp [hx, hy]⟩⟩).2
  have hcne : ae8e_coord cl x ≠ ae8e_coord cl y := fun h => hxy (ae8e_coord_inj cl h)
  have hEw : (pt.E ⟨(x : G) * y, hmem⟩ : Finset (Fin 8)) = {i, k} := by
    rw [hσ ⟨(x : G) * y, hmem⟩, ae8e_coord_mul cl (z := ⟨(x : G) * y, hmem⟩) rfl,
      ae8e_M3 _ _ hcne (ae8e_coord_inW cl x) (ae8e_coord_inW cl y)
        ((ae8e_mul_mem_iff cl hxy).mp hmem), Finset.image_symmDiff _ _ σ.injective,
      ← hσ x, ← hσ y, hx, hy]
    exact ae8e_triple i j k hij hjk hik
  have hEq : pt.E ⟨(x : G) * y, hmem⟩ = pt.E z := Subtype.ext (hEw.trans hz.symm)
  exact congrArg Subtype.val (pt.E.injective hEq)

section Beta

variable {c : Chart Ω u} {co : Coords c}

@[expose] def ae8e_ind (s : Finset (Fin 8)) : Fin 8 → ZMod 2 := fun k => if k ∈ s then 1 else 0

theorem ae8e_ind_even : ∀ i j : Fin 8, i ≠ j → ∑ k, ae8e_ind {i, j} k = 0 := by
  decide +kernel

theorem ae8e_even_gen : ∀ f : Fin 8 → ZMod 2, ∑ k, f k = 0 →
    f = ∑ i ∈ (Finset.univ.erase 7).filter (fun i => f i ≠ 0), ae8e_ind {i, 7} := by
  decide +kernel

@[expose] noncomputable def ae8e_x (pt : Points u) (i j : Fin 8) (h : i ≠ j) : ↥(Delta u) :=
  pt.E.symm ⟨{i, j}, Finset.card_pair h⟩

theorem ae8e_x_E (pt : Points u) (i j : Fin 8) (h : i ≠ j) :
    (pt.E (ae8e_x pt i j h) : Finset (Fin 8)) = {i, j} := by
  simp [ae8e_x]

theorem ae8e_x_comm (pt : Points u) (i j : Fin 8) (h : i ≠ j) :
    ae8e_x pt i j h = ae8e_x pt j i h.symm := by
  simp only [ae8e_x]
  congr 1
  exact Subtype.ext (Finset.pair_comm i j)

@[expose] noncomputable def ae8e_vv (cl : Classes co) (pt : Points u) (i : Fin 8) :
    Fin 6 → ZMod 2 :=
  if h : i = 7 then 0 else ae8e_coord cl (ae8e_x pt i 7 h)

@[expose] noncomputable def ae8e_lam (cl : Classes co) (pt : Points u) :
    (Fin 8 → ZMod 2) →+ (Fin 6 → ZMod 2) :=
  AddMonoidHom.mk' (fun f => ∑ i, f i • ae8e_vv cl pt i)
    (fun f g => by simp [add_smul, Finset.sum_add_distrib])

theorem ae8e_lam_apply (cl : Classes co) (pt : Points u) (f : Fin 8 → ZMod 2) :
    ae8e_lam cl pt f = ∑ i, f i • ae8e_vv cl pt i := rfl

theorem ae8e_lam_ind (cl : Classes co) (pt : Points u) (s : Finset (Fin 8)) :
    ae8e_lam cl pt (ae8e_ind s) = ∑ k ∈ s, ae8e_vv cl pt k := by
  simp [ae8e_lam_apply, ae8e_ind, ite_smul, Finset.sum_ite_mem]

theorem ae8e_vv_seven (cl : Classes co) (pt : Points u) : ae8e_vv cl pt 7 = 0 := by
  simp [ae8e_vv]

theorem ae8e_vv_of_ne (cl : Classes co) (pt : Points u) {i : Fin 8} (h : i ≠ 7) :
    ae8e_vv cl pt i = ae8e_coord cl (ae8e_x pt i 7 h) := by
  simp [ae8e_vv, h]

theorem ae8e_vv_add (H : End18.Hyp Ω) (cl : Classes co) (pt : Points u) {i j : Fin 8}
    (hij : i ≠ j) :
    ae8e_vv cl pt i + ae8e_vv cl pt j = ae8e_coord cl (ae8e_x pt i j hij) := by
  by_cases hi : i = 7
  · subst hi
    have hj : j ≠ 7 := fun h => hij h.symm
    rw [ae8e_vv_seven, zero_add, ae8e_vv_of_ne cl pt hj, ae8e_x_comm pt 7 j hij]
  by_cases hj : j = 7
  · subst hj
    rw [ae8e_vv_seven, add_zero, ae8e_vv_of_ne cl pt hi]
  rw [ae8e_vv_of_ne cl pt hi, ae8e_vv_of_ne cl pt hj]
  have hmul := mul_eq H cl pt (i := i) (j := 7) (k := j) hi (Ne.symm hj) hij
    (ae8e_x_E pt i 7 hi) (by rw [ae8e_x_E pt j 7 hj, Finset.pair_comm]) (ae8e_x_E pt i j hij)
  exact (ae8e_coord_mul cl hmul.symm).symm

theorem ae8e_lam_pair (H : End18.Hyp Ω) (cl : Classes co) (pt : Points u) {i j : Fin 8}
    (hij : i ≠ j) :
    ae8e_lam cl pt (ae8e_ind {i, j}) = ae8e_coord cl (ae8e_x pt i j hij) := by
  rw [ae8e_lam_ind, Finset.sum_pair hij, ae8e_vv_add H cl pt hij]

theorem ae8e_coord_symm (cl : Classes co) (x : ↥(Delta u)) :
    ((co.e.symm (Multiplicative.ofAdd (ae8e_coord cl x)) : ↥(zGroup Ω)) : G) = (x : G) := by
  simp [ae8e_coord]

@[expose] noncomputable def ae8e_beta (cl : Classes co) (pt : Points u) :
    Multiplicative (Fin 8 → ZMod 2) →* G :=
  (zGroup Ω).subtype.comp
    ((co.e.symm.toMonoidHom).comp (AddMonoidHom.toMultiplicative (ae8e_lam cl pt)))

theorem ae8e_beta_ofAdd (cl : Classes co) (pt : Points u) (f : Fin 8 → ZMod 2) :
    ae8e_beta cl pt (Multiplicative.ofAdd f) =
      ((co.e.symm (Multiplicative.ofAdd (ae8e_lam cl pt f)) : ↥(zGroup Ω)) : G) := rfl

theorem ae8e_beta_pair (H : End18.Hyp Ω) (cl : Classes co) (pt : Points u) {i j : Fin 8}
    (hij : i ≠ j) :
    ae8e_beta cl pt (Multiplicative.ofAdd (ae8e_ind {i, j})) = (ae8e_x pt i j hij : G) := by
  rw [ae8e_beta_ofAdd, ae8e_lam_pair H cl pt hij, ae8e_coord_symm]

theorem ae8e_lam_surj (H : End18.Hyp Ω) (cl : Classes co) (pt : Points u)
    (w : Fin 6 → ZMod 2) :
    ∃ f : Fin 8 → ZMod 2, ∑ i, f i = 0 ∧ ae8e_lam cl pt f = w := by
  let P : (Fin 6 → ZMod 2) → Prop := fun w =>
    ∃ f : Fin 8 → ZMod 2, ∑ i, f i = 0 ∧ ae8e_lam cl pt f = w
  have hadd : ∀ a b, P a → P b → P (a + b) := by
    rintro a b ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, by simp [Finset.sum_add_distrib, hf, hg], by simp⟩
  have hzero : P 0 := ⟨0, by simp, by simp⟩
  have hsmul : ∀ (a : ZMod 2) (x : Fin 6 → ZMod 2), P x → P (a • x) := by
    intro a x hx
    rcases (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) a with rfl | rfl
    · rw [zero_smul]; exact hzero
    · rw [one_smul]; exact hx
  have hbase : ∀ d : Fin 6, P (fun j => if d = j then 1 else 0) := by
    intro d
    have hW : ae8e_inW (fun j => if d = j then 1 else 0) := by
      revert d; decide
    obtain ⟨x, hx⟩ := ae8e_coord_surj cl hW
    obtain ⟨i, j, hij, hE⟩ := Finset.card_eq_two.mp (pt.E x).2
    have hxe : x = ae8e_x pt i j hij := by
      have : pt.E x = ⟨{i, j}, Finset.card_pair hij⟩ := Subtype.ext hE
      rw [ae8e_x, ← this, Equiv.symm_apply_apply]
    refine ⟨ae8e_ind {i, j}, ae8e_ind_even i j hij, ?_⟩
    rw [ae8e_lam_pair H cl pt hij, ← hxe, hx]
  have hw : P w := by
    rw [pi_eq_sum_univ w]
    exact Finset.sum_induction _ P hadd hzero (fun d _ => hsmul _ _ (hbase d))
  exact hw

end Beta

theorem ae8e_star : ∀ q : Fin 8, ∑ w ∈ Finset.univ.filter
    (fun w : Fin 6 → ZMod 2 => ae8e_inW w ∧ q ∈ ae8e_pair w), w = 0 := by
  decide +kernel

theorem ae8e_eq_x (pt : Points u) {x : ↥(Delta u)} {i j : Fin 8} (h : i ≠ j)
    (hE : (pt.E x : Finset (Fin 8)) = {i, j}) : x = ae8e_x pt i j h := by
  apply pt.E.injective
  apply Subtype.ext
  rw [ae8e_x_E pt i j h, hE]

theorem ae8e_star_sum (cl : Classes co) (pt : Points u) (σ : Equiv.Perm (Fin 8))
    (hσ : ∀ x : ↥(Delta u), (pt.E x : Finset (Fin 8)) = (ae8e_pair (ae8e_coord cl x)).image σ) :
    ∑ i, ae8e_vv cl pt i = 0 := by
  set q : Fin 8 := σ.symm 7 with hq
  have hstar := ae8e_star q
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (7 : Fin 8)), ae8e_vv_seven, add_zero]
  refine (Finset.sum_nbij (fun i => ae8e_vv cl pt i) ?_ ?_ ?_ ?_).trans hstar
  ·
    intro i hi
    have hi7 : i ≠ 7 := Finset.ne_of_mem_erase hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [ae8e_vv_of_ne cl pt hi7]
    refine ⟨ae8e_coord_inW cl _, ?_⟩
    have h7 : (7 : Fin 8) ∈ (pt.E (ae8e_x pt i 7 hi7) : Finset (Fin 8)) := by
      rw [ae8e_x_E pt i 7 hi7]
      simp
    rw [hσ] at h7
    obtain ⟨p, hp, hpσ⟩ := Finset.mem_image.mp h7
    have hpq : p = q := by rw [hq, ← hpσ, Equiv.symm_apply_apply]
    rw [← hpq]
    exact hp
  ·
    intro i hi j hj hij
    have hi7 : i ≠ 7 := Finset.ne_of_mem_erase hi
    have hj7 : j ≠ 7 := Finset.ne_of_mem_erase hj
    dsimp only at hij
    rw [ae8e_vv_of_ne cl pt hi7, ae8e_vv_of_ne cl pt hj7] at hij
    have hxx := ae8e_coord_inj cl hij
    have hE : (pt.E (ae8e_x pt i 7 hi7) : Finset (Fin 8)) = {i, 7} := ae8e_x_E pt i 7 hi7
    have hE' : (pt.E (ae8e_x pt j 7 hj7) : Finset (Fin 8)) = {j, 7} := ae8e_x_E pt j 7 hj7
    rw [hxx, hE'] at hE
    have hmem : i ∈ ({j, 7} : Finset (Fin 8)) := by rw [hE]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · exact h
    · exact absurd h hi7
  ·
    intro w hw
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    obtain ⟨hwin, hwq⟩ := hw
    obtain ⟨x, hx⟩ := ae8e_coord_surj cl hwin
    have h7 : (7 : Fin 8) ∈ (pt.E x : Finset (Fin 8)) := by
      rw [hσ x, hx]
      exact Finset.mem_image.mpr ⟨q, hwq, by rw [hq, Equiv.apply_symm_apply]⟩
    obtain ⟨a, b, hab, hE⟩ := Finset.card_eq_two.mp (pt.E x).2
    rw [hE] at h7
    simp only [Finset.mem_insert, Finset.mem_singleton] at h7
    rcases h7 with h7 | h7
    · have hb : b ≠ 7 := fun hb => hab (h7.symm.trans hb.symm)
      refine ⟨b, ?_, ?_⟩
      · simp [Finset.mem_erase, hb]
      · have hEb : (pt.E x : Finset (Fin 8)) = {b, 7} := by
          rw [hE, ← h7, Finset.pair_comm]
        show ae8e_vv cl pt b = w
        rw [ae8e_vv_of_ne cl pt hb, ← ae8e_eq_x pt hb hEb]
        exact hx
    · have ha : a ≠ 7 := fun ha => hab (ha.trans h7)
      refine ⟨a, ?_, ?_⟩
      · simp [Finset.mem_erase, ha]
      · have hEa : (pt.E x : Finset (Fin 8)) = {a, 7} := by
          rw [hE, ← h7]
        show ae8e_vv cl pt a = w
        rw [ae8e_vv_of_ne cl pt ha, ← ae8e_eq_x pt ha hEa]
        exact hx
  · intro i _
    rfl

theorem ae8e_eq_of_card_two {K : Type*} (hK : Nat.card K = 2) {a b : K} (hab : a ≠ b) (x : K) :
    x = a ∨ x = b := by
  obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' a).mp hK
  by_cases hxa : x = a
  · exact Or.inl hxa
  · right
    exact (huniq x hxa).trans (huniq b (Ne.symm hab)).symm

@[expose] noncomputable def ae8e_sumH : (Fin 8 → ZMod 2) →+ ZMod 2 :=
  AddMonoidHom.mk' (fun f => ∑ i, f i) (fun f g => by simp [Finset.sum_add_distrib])

theorem ae8e_card_even : Nat.card ↥(ae8e_sumH.ker) = 128 := by
  have hsurj : Function.Surjective ae8e_sumH := fun a =>
    ⟨Pi.single 0 a, by simp [ae8e_sumH]⟩
  have h := AddSubgroup.card_ker_mul_card_of_surjective hsurj
  have h2 : Nat.card (ZMod 2) = 2 := by simp
  have h256 : Nat.card (Fin 8 → ZMod 2) = 256 := by simp [Nat.card_eq_fintype_card]
  rw [h2, h256] at h
  omega

theorem ae8e_kernel (H : End18.Hyp Ω) (cl : Classes co) (pt : Points u)
    (hstar : ∑ i, ae8e_vv cl pt i = 0) {f : Fin 8 → ZMod 2} (hf : ∑ i, f i = 0)
    (h0 : ae8e_lam cl pt f = 0) : f = 0 ∨ f = fun _ => 1 := by
  let lamEv : ae8e_sumH.ker →+ (Fin 6 → ZMod 2) := (ae8e_lam cl pt).comp ae8e_sumH.ker.subtype
  have hsurj : Function.Surjective lamEv := by
    intro w
    obtain ⟨g, hg, hgw⟩ := ae8e_lam_surj H cl pt w
    exact ⟨⟨g, hg⟩, hgw⟩
  have hcard1 := AddSubgroup.card_ker_mul_card_of_surjective hsurj
  have h64 : Nat.card (Fin 6 → ZMod 2) = 64 := by simp [Nat.card_eq_fintype_card]
  rw [h64, ae8e_card_even] at hcard1
  have hK : Nat.card lamEv.ker = 2 := by omega
  have hone : (fun _ : Fin 8 => (1 : ZMod 2)) ∈ ae8e_sumH.ker := by
    show ∑ i : Fin 8, (1 : ZMod 2) = 0
    decide
  let a : lamEv.ker := ⟨⟨0, ae8e_sumH.ker.zero_mem⟩, by simp [lamEv]⟩
  let b : lamEv.ker := ⟨⟨fun _ => 1, hone⟩, by
    show ae8e_lam cl pt (fun _ => 1) = 0
    simp [ae8e_lam_apply, hstar]⟩
  have hab : a ≠ b := by
    intro h
    have h' := congrArg (fun x : lamEv.ker => (x.1.1 : Fin 8 → ZMod 2) 0) h
    simp [a, b] at h'
  rcases ae8e_eq_of_card_two hK hab ⟨⟨f, hf⟩, h0⟩ with h | h
  · left
    exact congrArg (fun x : lamEv.ker => (x : Fin 8 → ZMod 2)) h
  · right
    exact congrArg (fun x : lamEv.ker => (x : Fin 8 → ZMod 2)) h

@[expose] noncomputable def ae8e_perm (s : Equiv.Perm (Fin 8)) :
    Multiplicative (Fin 8 → ZMod 2) →* Multiplicative (Fin 8 → ZMod 2) :=
  MonoidHom.mk' (fun f => Multiplicative.ofAdd (fun i => f.toAdd (s.symm i)))
    (fun a b => by
      simp only [toAdd_mul, ← ofAdd_add]
      rfl)

theorem ae8e_perm_ind (s : Equiv.Perm (Fin 8)) (i j : Fin 8) :
    ae8e_perm s (Multiplicative.ofAdd (ae8e_ind {i, j})) =
      Multiplicative.ofAdd (ae8e_ind {s i, s j}) := by
  simp only [ae8e_perm, MonoidHom.mk'_apply, toAdd_ofAdd]
  congr 1
  funext k
  simp [ae8e_ind, Equiv.symm_apply_eq]

theorem ae8e_conj_mem (g : G) (x : ↥(Delta u)) : g * (x : G) * g⁻¹ ∈ Delta u := by
  obtain ⟨h, hx⟩ := x.2
  exact ⟨g * h, by rw [hx]; group⟩

theorem ae8e_conj_x (pt : Points u) (g : G) {i j : Fin 8} (hij : i ≠ j) :
    g * (ae8e_x pt i j hij : G) * g⁻¹ =
      (ae8e_x pt (pt.π g i) (pt.π g j) ((pt.π g).injective.ne hij) : G) := by
  let y : ↥(Delta u) := ⟨g * (ae8e_x pt i j hij : G) * g⁻¹, ae8e_conj_mem g _⟩
  have hy : (pt.E y : Finset (Fin 8)) = {pt.π g i, pt.π g j} := by
    rw [pt.equivariant g (ae8e_x pt i j hij) y rfl, ae8e_x_E]
    simp
  have := ae8e_eq_x pt ((pt.π g).injective.ne hij) hy
  rw [← this]

theorem ae8e_beta_eq_one_iff (cl : Classes co) (pt : Points u) (f : Fin 8 → ZMod 2) :
    ae8e_beta cl pt (Multiplicative.ofAdd f) = 1 ↔ ae8e_lam cl pt f = 0 := by
  rw [ae8e_beta_ofAdd]
  constructor
  · intro h
    have h1 : (co.e.symm (Multiplicative.ofAdd (ae8e_lam cl pt f)) : ↥(zGroup Ω)) = 1 :=
      Subtype.ext h
    have h2 := congrArg co.e h1
    rw [MulEquiv.apply_symm_apply, map_one] at h2
    exact ofAdd_eq_one.mp h2
  · intro h
    rw [h, ofAdd_zero, map_one]
    rfl

theorem ae8e_conj (H : End18.Hyp Ω) (cl : Classes co) (pt : Points u) (g : G)
    (f : Multiplicative (Fin 8 → ZMod 2)) (hf : ∑ i, f.toAdd i = 0) :
    g * ae8e_beta cl pt f * g⁻¹ = ae8e_beta cl pt (ae8e_perm (pt.π g) f) := by
  let φ₁ : Multiplicative (Fin 8 → ZMod 2) →* G :=
    (MulAut.conj g).toMonoidHom.comp (ae8e_beta cl pt)
  let φ₂ : Multiplicative (Fin 8 → ZMod 2) →* G :=
    (ae8e_beta cl pt).comp (ae8e_perm (pt.π g))
  have hgen : Set.EqOn φ₁ φ₂
      {a | ∃ i : Fin 8, ∃ h : i ≠ 7, a = Multiplicative.ofAdd (ae8e_ind {i, 7})} := by
    rintro a ⟨i, hi, rfl⟩
    have hne : pt.π g i ≠ pt.π g 7 := (pt.π g).injective.ne hi
    show g * ae8e_beta cl pt (Multiplicative.ofAdd (ae8e_ind {i, 7})) * g⁻¹ =
      ae8e_beta cl pt (ae8e_perm (pt.π g) (Multiplicative.ofAdd (ae8e_ind {i, 7})))
    rw [ae8e_beta_pair H cl pt hi, ae8e_perm_ind, ae8e_beta_pair H cl pt hne, ae8e_conj_x]
  have hmem : Multiplicative.ofAdd f.toAdd ∈ Subgroup.closure
      {a | ∃ i : Fin 8, ∃ h : i ≠ 7, a = Multiplicative.ofAdd (ae8e_ind {i, 7})} := by
    rw [ae8e_even_gen f.toAdd hf, ofAdd_sum]
    apply Subgroup.prod_mem
    intro i hi
    have hi7 : i ≠ 7 := Finset.ne_of_mem_erase (Finset.mem_of_mem_filter i hi)
    exact Subgroup.subset_closure ⟨i, hi7, rfl⟩
  have key := MonoidHom.eqOn_closure hgen hmem
  rw [ofAdd_toAdd] at key
  exact key

theorem ae8e_move (a : Fin 6) :
    ∃ τ : Equiv.Perm (Fin 6), τ ∈ alternatingGroup (Fin 6) ∧ τ a ≠ a := by
  by_cases h : a = 0
  · refine ⟨ae8e_rep 1, ae8e_rep_mem 1, ?_⟩
    subst h
    decide
  · refine ⟨ae8e_rep a, ae8e_rep_mem a, ?_⟩
    rw [ae8e_rep_zero]
    exact fun e => h e.symm

theorem ae8e_range_iff (ι ι₀ : Fin 6 ↪ Fin 8)
    (hsub : ∀ x, x ∈ Set.range ι → x ∈ Set.range ι₀) : ∀ x, x ∈ Set.range ι₀ → x ∈ Set.range ι := by
  classical
  have hS : Finset.univ.image ι ⊆ Finset.univ.image ι₀ := by
    intro z hz
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨b, hb⟩ := hsub (ι a) ⟨a, rfl⟩
    exact Finset.mem_image.mpr ⟨b, Finset.mem_univ _, hb⟩
  have hcard : (Finset.univ.image ι₀).card ≤ (Finset.univ.image ι).card := by
    rw [Finset.card_image_of_injective _ ι₀.injective, Finset.card_image_of_injective _ ι.injective]
  intro x hx
  obtain ⟨i, rfl⟩ := hx
  have hi : ι₀ i ∈ Finset.univ.image ι₀ := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  rw [← Finset.eq_of_subset_of_card_le hS hcard] at hi
  obtain ⟨a, -, ha⟩ := Finset.mem_image.mp hi
  exact ⟨a, ha⟩

section Labels

variable {c : Chart Ω u} {co : Coords c}

theorem ae8e_coord_e2 (cl : Classes co) (pt : Points u) (σ : Equiv.Perm (Fin 8))
    (hσ : ∀ x : ↥(Delta u),
      (pt.E x : Finset (Fin 8)) = (ae8e_pair (ae8e_coord cl x)).image σ)
    {a b : Fin 6} (hab : a ≠ b) (h : ae8e_iota σ a ≠ ae8e_iota σ b) :
    ae8e_coord cl (ae8e_x pt (ae8e_iota σ a) (ae8e_iota σ b) h) = ae8e_e2 a b := by
  have hE : (pt.E (ae8e_x pt (ae8e_iota σ a) (ae8e_iota σ b) h) : Finset (Fin 8)) =
      {ae8e_iota σ a, ae8e_iota σ b} := ae8e_x_E pt _ _ h
  have h2 : Finset.image σ (ae8e_pair
      (ae8e_coord cl (ae8e_x pt (ae8e_iota σ a) (ae8e_iota σ b) h))) =
      Finset.image σ {ae8e_c6 a, ae8e_c6 b} := by
    rw [← hσ, hE]
    simp [ae8e_iota_apply, Finset.image_insert]
  exact ae8e_e2_unique _ a b hab (ae8e_coord_inW cl _) (Finset.image_injective σ.injective h2)

theorem ae8e_vv_e2 (H : End18.Hyp Ω) (cl : Classes co) (pt : Points u) (σ : Equiv.Perm (Fin 8))
    (hσ : ∀ x : ↥(Delta u),
      (pt.E x : Finset (Fin 8)) = (ae8e_pair (ae8e_coord cl x)).image σ)
    {a b : Fin 6} (hab : a ≠ b) :
    ae8e_vv cl pt (ae8e_iota σ a) + ae8e_vv cl pt (ae8e_iota σ b) = ae8e_e2 a b := by
  have h : ae8e_iota σ a ≠ ae8e_iota σ b := (ae8e_iota σ).injective.ne hab
  rw [ae8e_vv_add H cl pt h, ae8e_coord_e2 cl pt σ hσ hab h]

theorem ae8e_lam_ext6 (H : End18.Hyp Ω) (cl : Classes co) (pt : Points u)
    (σ : Equiv.Perm (Fin 8))
    (hσ : ∀ x : ↥(Delta u),
      (pt.E x : Finset (Fin 8)) = (ae8e_pair (ae8e_coord cl x)).image σ)
    (v : Fin 6 → ZMod 2) (hv : ∑ i, v i = 0) :
    ae8e_lam cl pt (ae8e_ext6 (ae8e_iota σ) v) = v := by
  rw [ae8e_lam_apply, ae8e_sum_range (ae8e_iota σ)
    (fun k => ae8e_ext6 (ae8e_iota σ) v k • ae8e_vv cl pt k) ?_]
  · simp only [ae8e_ext6_apply]
    exact ae8e_lin (fun a => ae8e_vv cl pt (ae8e_iota σ a)) (fun a b hab => by
      rw [ae8e_vv_e2 H cl pt σ hσ hab, ae8e_e2_eq_single a b hab]) v hv
  · intro k hk
    simp only [ae8e_ext6_of_not_mem _ _ hk, zero_smul]

theorem ae8e_beta_vec (H : End18.Hyp Ω) (cl : Classes co) (pt : Points u) (σ : Equiv.Perm (Fin 8))
    (hσ : ∀ x : ↥(Delta u),
      (pt.E x : Finset (Fin 8)) = (ae8e_pair (ae8e_coord cl x)).image σ)
    (y : ↥(pSpan (Generic.centMembers Ω u))) (hy : (y : G) ∈ zGroup Ω) :
    ae8e_beta cl pt (Multiplicative.ofAdd (ae8e_ext6 (ae8e_iota σ) (c.ψ y : AE.Wr 6).vec)) =
      (y : G) := by
  have hv : ∑ i, (c.ψ y : AE.Wr 6).vec i = 0 := by
    have h := (c.ψ y).2
    rw [AE.mem_aeSub] at h
    exact h.1
  have hco : (co.e ⟨(y : G), hy⟩).toAdd = (c.ψ y : AE.Wr 6).vec := co.vec ⟨(y : G), hy⟩ y rfl
  rw [ae8e_beta_ofAdd, ae8e_lam_ext6 H cl pt σ hσ _ hv, ← hco, ofAdd_toAdd,
    MulEquiv.symm_apply_apply]

end Labels

section Perm

variable {c : Chart Ω u} {co : Coords c}

theorem ae8e_perm_iota (H : End18.Hyp Ω) (cl : Classes co) (pt : Points u)
    (σ : Equiv.Perm (Fin 8))
    (hσ : ∀ x : ↥(Delta u),
      (pt.E x : Finset (Fin 8)) = (ae8e_pair (ae8e_coord cl x)).image σ)
    (y : ↥(pSpan (Generic.centMembers Ω u))) (a : Fin 6) :
    pt.π (y : G) (ae8e_iota σ a) = ae8e_iota σ ((c.ψ y : AE.Wr 6).perm a) := by
  have key : ∀ b : Fin 6, a ≠ b →
      Finset.image (pt.π (y : G)) {ae8e_iota σ a, ae8e_iota σ b} =
        {ae8e_iota σ ((c.ψ y : AE.Wr 6).perm a), ae8e_iota σ ((c.ψ y : AE.Wr 6).perm b)} := by
    intro b hab
    have hι : ae8e_iota σ a ≠ ae8e_iota σ b := (ae8e_iota σ).injective.ne hab
    set τ : Equiv.Perm (Fin 6) := (c.ψ y : AE.Wr 6).perm with hτ
    have hτab : τ a ≠ τ b := τ.injective.ne hab
    set x : ↥(Delta u) := ae8e_x pt (ae8e_iota σ a) (ae8e_iota σ b) hι with hxdef
    have hx2 : ae8e_coord cl x = ae8e_e2 a b := ae8e_coord_e2 cl pt σ hσ hab hι
    let d' : ↥(Delta u) := ⟨(y : G) * (x : G) * (y : G)⁻¹, ae8e_conj_mem _ x⟩
    have hE' : (pt.E d' : Finset (Fin 8)) = Finset.image (pt.π (y : G)) (pt.E x : Finset (Fin 8)) :=
      pt.equivariant (y : G) x d' rfl
    have h1 := co.act y ⟨(x : G), ae8e_delta_mem cl x⟩ ⟨(d' : G), ae8e_delta_mem cl d'⟩ rfl
    have hcoord : ae8e_coord cl d' = fun k => ae8e_e2 a b (τ.symm k) := by
      show (co.e ⟨(d' : G), ae8e_delta_mem cl d'⟩).toAdd = _
      rw [h1]
      show (fun i => ae8e_coord cl x (τ.symm i)) = _
      rw [hx2]
    have hEd : (pt.E d' : Finset (Fin 8)) = {ae8e_iota σ (τ a), ae8e_iota σ (τ b)} := by
      rw [hσ d', hcoord, ae8e_e2_perm τ a b, ae8e_e2_pair (τ a) (τ b) hτab]
      simp [ae8e_iota_apply, Finset.image_insert]
    rw [← ae8e_x_E pt _ _ hι, ← hE', hEd]
  obtain ⟨b, e, hab, hae, hbe⟩ := ae8e_three_points a
  have h1 : pt.π (y : G) (ae8e_iota σ a) ∈
      ({ae8e_iota σ ((c.ψ y : AE.Wr 6).perm a), ae8e_iota σ ((c.ψ y : AE.Wr 6).perm b)} :
        Finset (Fin 8)) := by
    rw [← key b hab]
    exact Finset.mem_image_of_mem _ (by simp)
  have h2 : pt.π (y : G) (ae8e_iota σ a) ∈
      ({ae8e_iota σ ((c.ψ y : AE.Wr 6).perm a), ae8e_iota σ ((c.ψ y : AE.Wr 6).perm e)} :
        Finset (Fin 8)) := by
    rw [← key e hae]
    exact Finset.mem_image_of_mem _ (by simp)
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  rcases h1 with h1 | h1
  · exact h1
  · rcases h2 with h2 | h2
    · exact absurd ((c.ψ y : AE.Wr 6).perm.injective
        ((ae8e_iota σ).injective (h1.symm.trans h2))).symm hab
    · exact absurd ((c.ψ y : AE.Wr 6).perm.injective
        ((ae8e_iota σ).injective (h1.symm.trans h2))) hbe

theorem ae8e_perm_Y (H : End18.Hyp Ω) (cl : Classes co) (pt : Points u)
    (σ : Equiv.Perm (Fin 8))
    (hσ : ∀ x : ↥(Delta u),
      (pt.E x : Finset (Fin 8)) = (ae8e_pair (ae8e_coord cl x)).image σ)
    (y : ↥(pSpan (Generic.centMembers Ω u))) :
    pt.π (y : G) = ae8e_permExt6 (ae8e_iota σ) (c.ψ y : AE.Wr 6).perm := by
  obtain ⟨ι₀, hι₀⟩ := exists_chartLines H cl pt
  have hsub : ∀ x, x ∈ Set.range (ae8e_iota σ) → x ∈ Set.range ι₀ := by
    rintro _ ⟨a, rfl⟩
    by_contra hx
    obtain ⟨τ, hτA, hτa⟩ := ae8e_move a
    have hmem : (AE.Wr.ofPerm τ : AE.Wr 6) ∈ AE.aeSub 6 := by
      rw [AE.mem_aeSub]
      refine ⟨?_, ?_⟩
      · simp [AE.Wr.wsum, AE.Wr.ofPerm]
      · exact Equiv.Perm.mem_alternatingGroup.mp hτA
    set y₀ : ↥(pSpan (Generic.centMembers Ω u)) := c.ψ.symm ⟨AE.Wr.ofPerm τ, hmem⟩ with hy₀
    have hψ : c.ψ y₀ = ⟨AE.Wr.ofPerm τ, hmem⟩ := c.ψ.apply_symm_apply _
    have hperm : (c.ψ y₀ : AE.Wr 6).perm = τ := by
      rw [hψ]
      rfl
    have hfix := (hι₀ y₀).2 (ae8e_iota σ a) hx
    have hact := ae8e_perm_iota H cl pt σ hσ y₀ a
    rw [hperm] at hact
    exact hτa ((ae8e_iota σ).injective (hact.symm.trans hfix))
  have hrange := ae8e_range_iff (ae8e_iota σ) ι₀ hsub
  refine Equiv.ext fun x => ?_
  by_cases hx : x ∈ Set.range (ae8e_iota σ)
  · obtain ⟨a, rfl⟩ := hx
    rw [ae8e_permExt6_apply]
    exact ae8e_perm_iota H cl pt σ hσ y a
  · rw [ae8e_permExt6_of_not_mem _ _ hx]
    have hx0 : x ∉ Set.range ι₀ := fun h => hx (hrange x h)
    exact (hι₀ y).2 x hx0

end Perm

section Assembly

variable {c : Chart Ω u} {co : Coords c}

@[expose] noncomputable def ae8e_permQ : AE.AEQ 8 →* Equiv.Perm (Fin 8) :=
  QuotientGroup.lift (AE.piSub 8) (AE.permHom 8) (fun x hx => by
    show AE.permHom 8 x = 1
    rcases AE.mem_piSub.mp hx with h | h
    · rw [h, map_one]
    · rw [h]
      rfl)

theorem ae8e_permQ_mk (w : AE.Wr 8) : ae8e_permQ (AE.mkQ 8 w) = AE.permHom 8 w := rfl

@[expose] noncomputable def ae8e_rho (c : Chart Ω u) (σ : Equiv.Perm (Fin 8)) :
    ↥(pSpan (Generic.centMembers Ω u)) →* AE.AEQ 8 :=
  (AE.mkQ 8).comp ((ae8e_relab6 (ae8e_iota σ)).comp
    ((AE.aeSub 6).subtype.comp c.ψ.toMonoidHom))

theorem ae8e_rho_apply (σ : Equiv.Perm (Fin 8)) (y : ↥(pSpan (Generic.centMembers Ω u))) :
    ae8e_rho c σ y = AE.mkQ 8 (ae8e_relab6 (ae8e_iota σ) (c.ψ y : AE.Wr 6)) := rfl

theorem ae8e_permQ_rho (σ : Equiv.Perm (Fin 8)) (y : ↥(pSpan (Generic.centMembers Ω u))) :
    ae8e_permQ (ae8e_rho c σ y) = ae8e_permExt6 (ae8e_iota σ) (c.ψ y : AE.Wr 6).perm := rfl

theorem ae8e_permQ_phi (pt : Points u) {H : Subgroup G} {β : Multiplicative (Fin 8 → ZMod 2) →* G}
    (hS : AESplitHyp (zGroup Ω) H (pt.π.comp H.subtype) β) (hker : pt.π.ker = zGroup Ω)
    {φ : G →* AE.AEQ 8}
    (hβφ : ∀ f : Multiplicative (Fin 8 → ZMod 2), ∑ i, f.toAdd i = 0 →
      φ (β f) = AE.mkQ 8 (AE.Wr.ofVec f.toAdd))
    (hHφ : ∀ x : H, φ x = AE.mkQ 8 (AE.Wr.ofPerm ((pt.π.comp H.subtype) x))) (g : G) :
    ae8e_permQ (φ g) = pt.π g := by
  obtain ⟨f, hf, x, hx⟩ := hS.exists_eq_mul g
  have hπβ : pt.π (β f) = 1 := by
    have hmem : β f ∈ pt.π.ker := by
      rw [hker]
      exact (hS.mem_iff _).mpr ⟨f, hf, rfl⟩
    exact hmem
  rw [← hx, map_mul, map_mul, hβφ f hf, hHφ x, map_mul, ae8e_permQ_mk, ae8e_permQ_mk,
    hπβ, one_mul]
  simp [AE.permHom, AE.Wr.ofVec, AE.Wr.ofPerm]

theorem ae8e_mkQ_ofVec_eq {β : Multiplicative (Fin 8 → ZMod 2) →* G}
    (hβ1 : ∀ f : Multiplicative (Fin 8 → ZMod 2), ∑ i, f.toAdd i = 0 →
      (β f = 1 ↔ f.toAdd = 0 ∨ f.toAdd = fun _ => 1))
    {f g : Fin 8 → ZMod 2} (hf : ∑ i, f i = 0) (hg : ∑ i, g i = 0)
    (h : β (Multiplicative.ofAdd f) = β (Multiplicative.ofAdd g)) :
    AE.mkQ 8 (AE.Wr.ofVec f) = AE.mkQ 8 (AE.Wr.ofVec g) := by
  have hsub : ∑ i, (f - g) i = 0 := by
    simp [Finset.sum_sub_distrib, hf, hg]
  have h1 : β (Multiplicative.ofAdd (f - g)) = 1 := by
    rw [ofAdd_sub, map_div, h, div_self']
  rcases (hβ1 _ hsub).mp h1 with h2 | h2
  · have hfg : f = g := by
      exact sub_eq_zero.mp h2
    rw [hfg]
  · have hfg : f = g + fun _ => 1 := by
      funext i
      have h3 : f i - g i = 1 := congrFun h2 i
      simp only [Pi.add_apply]
      linear_combination h3
    rw [hfg]
    have hprod : AE.Wr.ofVec (g + fun _ => 1) = AE.Wr.ofVec g * AE.Wr.allOnes 8 := by
      refine AE.Wr.ext ?_ ?_
      · funext i
        simp [AE.Wr.ofVec, AE.Wr.allOnes, AE.Wr.mul_vec]
      · simp [AE.Wr.ofVec, AE.Wr.allOnes, AE.Wr.mul_perm]
    rw [hprod, map_mul]
    have hone : AE.mkQ 8 (AE.Wr.allOnes 8) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (AE.mem_piSub.mpr (Or.inr rfl))
    rw [hone, mul_one]

theorem ae8e_ext6_zero (ι : Fin 6 ↪ Fin 8) : ae8e_ext6 ι 0 = 0 := by
  funext k
  simp [ae8e_ext6]

theorem ae8e_ext6_sum (ι : Fin 6 ↪ Fin 8) (v : Fin 6 → ZMod 2) (hv : ∑ i, v i = 0) :
    ∑ k, ae8e_ext6 ι v k = 0 := by
  rw [ae8e_sum_range ι (ae8e_ext6 ι v) (fun k hk => ae8e_ext6_of_not_mem ι v hk)]
  simp only [ae8e_ext6_apply]
  exact hv

theorem ae8e_relab6_ofVec (ι : Fin 6 ↪ Fin 8) (v : Fin 6 → ZMod 2) :
    ae8e_relab6 ι (AE.Wr.ofVec v) = AE.Wr.ofVec (ae8e_ext6 ι v) := by
  refine AE.Wr.ext rfl ?_
  show ae8e_permExt6 ι 1 = 1
  exact ae8e_permExt6_one ι

theorem ae8e_relab6_ofPerm (ι : Fin 6 ↪ Fin 8) (τ : Equiv.Perm (Fin 6)) :
    ae8e_relab6 ι (AE.Wr.ofPerm τ) = AE.Wr.ofPerm (ae8e_permExt6 ι τ) := by
  refine AE.Wr.ext ?_ rfl
  show ae8e_ext6 ι 0 = 0
  exact ae8e_ext6_zero ι

theorem ae8e_vec_of_perm_one (w : AE.Wr 6) (h : w.perm = 1) : w = AE.Wr.ofVec w.vec :=
  AE.Wr.ext rfl h

theorem ae8e_phi_eq_rho (H : End18.Hyp Ω) (cl : Classes co) (pt : Points u)
    (σ : Equiv.Perm (Fin 8))
    (hσ : ∀ x : ↥(Delta u),
      (pt.E x : Finset (Fin 8)) = (ae8e_pair (ae8e_coord cl x)).image σ)
    {H' : Subgroup G} (hS : AESplitHyp (zGroup Ω) H' (pt.π.comp H'.subtype) (ae8e_beta cl pt))
    {φ : G →* AE.AEQ 8}
    (hβφ : ∀ f : Multiplicative (Fin 8 → ZMod 2), ∑ i, f.toAdd i = 0 →
      φ (ae8e_beta cl pt f) = AE.mkQ 8 (AE.Wr.ofVec f.toAdd))
    (hHφ : ∀ x : H', φ x = AE.mkQ 8 (AE.Wr.ofPerm ((pt.π.comp H'.subtype) x)))
    (hH0 : c.H0 ≤ H')
    (y : ↥(pSpan (Generic.centMembers Ω u))) :
    φ (y : G) = ae8e_rho c σ y := by
  have hβ1 := hS.eq_one_iff
  have hmem := hS.mem_iff
  obtain ⟨τ, hτdef⟩ : ∃ τ : Equiv.Perm (Fin 6), τ = (c.ψ y : AE.Wr 6).perm := ⟨_, rfl⟩
  have hτA : τ ∈ alternatingGroup (Fin 6) := by
    have h := (c.ψ y).2
    rw [AE.mem_aeSub] at h
    rw [hτdef]
    exact Equiv.Perm.mem_alternatingGroup.mpr h.2
  have hmemA : (AE.Wr.ofPerm τ : AE.Wr 6) ∈ AE.aeSub 6 := by
    rw [AE.mem_aeSub]
    exact ⟨by simp [AE.Wr.wsum, AE.Wr.ofPerm], Equiv.Perm.mem_alternatingGroup.mp hτA⟩
  obtain ⟨h₀, hh₀⟩ : ∃ h₀ : ↥(pSpan (Generic.centMembers Ω u)),
      c.ψ h₀ = ⟨AE.Wr.ofPerm τ, hmemA⟩ := ⟨c.ψ.symm ⟨AE.Wr.ofPerm τ, hmemA⟩, c.ψ.apply_symm_apply _⟩
  have hψh₀ : (c.ψ h₀ : AE.Wr 6) = AE.Wr.ofPerm τ := congrArg Subtype.val hh₀
  have hh₀H0 : (h₀ : G) ∈ c.H0 := by
    rw [Chart.mem_H0]
    refine ⟨h₀.2, ?_, ?_⟩
    · rw [hψh₀]
      rfl
    · rw [hψh₀]
      exact hτA
  obtain ⟨d, hd⟩ : ∃ d : ↥(pSpan (Generic.centMembers Ω u)), d = y * h₀⁻¹ := ⟨_, rfl⟩
  have hψd : (c.ψ d : AE.Wr 6).perm = 1 := by
    have hc : ((c.ψ d : ↥(AE.aeSub 6)) : AE.Wr 6) =
        (c.ψ y : AE.Wr 6) * ((c.ψ h₀ : ↥(AE.aeSub 6)) : AE.Wr 6)⁻¹ := by
      rw [hd, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hc, AE.Wr.mul_perm, AE.Wr.inv_perm, hψh₀, AE.Wr.ofPerm, ← hτdef]
    simp
  have hdD : (d : G) ∈ zGroup Ω := (Chart.mem_zGroup_iff c H d).mpr hψd
  have hyd : y = d * h₀ := by
    rw [hd, inv_mul_cancel_right]
  have hφd : φ (d : G) = ae8e_rho c σ d := by
    obtain ⟨f, hf, hfd⟩ := (hmem (d : G)).mp hdD
    have h1 : φ (d : G) = AE.mkQ 8 (AE.Wr.ofVec f.toAdd) := by
      rw [← hfd]
      exact hβφ f hf
    have hv : ∑ i, (c.ψ d : AE.Wr 6).vec i = 0 := by
      have h := (c.ψ d).2
      rw [AE.mem_aeSub] at h
      exact h.1
    have hψd_ofVec : (c.ψ d : AE.Wr 6) = AE.Wr.ofVec (c.ψ d : AE.Wr 6).vec :=
      ae8e_vec_of_perm_one _ hψd
    have hρd : ae8e_rho c σ d =
        AE.mkQ 8 (AE.Wr.ofVec (ae8e_ext6 (ae8e_iota σ) (c.ψ d : AE.Wr 6).vec)) := by
      rw [ae8e_rho_apply]
      congr 1
      conv_lhs => rw [hψd_ofVec]
      exact ae8e_relab6_ofVec _ _
    have hβeq : ae8e_beta cl pt (Multiplicative.ofAdd f.toAdd) =
        ae8e_beta cl pt (Multiplicative.ofAdd (ae8e_ext6 (ae8e_iota σ) (c.ψ d : AE.Wr 6).vec)) := by
      rw [ofAdd_toAdd, hfd, ae8e_beta_vec H cl pt σ hσ d hdD]
    rw [h1, hρd]
    exact ae8e_mkQ_ofVec_eq hβ1 hf (ae8e_ext6_sum _ _ hv) hβeq
  have hφh : φ (h₀ : G) = ae8e_rho c σ h₀ := by
    have h1 : φ (h₀ : G) = AE.mkQ 8 (AE.Wr.ofPerm ((pt.π.comp H'.subtype) ⟨(h₀ : G), hH0 hh₀H0⟩)) :=
      hHφ ⟨(h₀ : G), hH0 hh₀H0⟩
    have hπ : pt.π (h₀ : G) = ae8e_permExt6 (ae8e_iota σ) τ := by
      rw [ae8e_perm_Y H cl pt σ hσ h₀, hψh₀]
      rfl
    have hρh : ae8e_rho c σ h₀ = AE.mkQ 8 (AE.Wr.ofPerm (ae8e_permExt6 (ae8e_iota σ) τ)) := by
      rw [ae8e_rho_apply, hψh₀, ae8e_relab6_ofPerm]
    rw [h1, hρh]
    congr 2
  rw [hyd, Subgroup.coe_mul, map_mul, hφd, hφh, ← map_mul]

end Assembly

theorem ae8e_beta_spec (H : End18.Hyp Ω) (cl : Classes co) (pt : Points u) :
    (∀ g : G, g ∈ zGroup Ω ↔
        ∃ f : Multiplicative (Fin 8 → ZMod 2), ∑ i, f.toAdd i = 0 ∧ ae8e_beta cl pt f = g) ∧
      (∀ f : Multiplicative (Fin 8 → ZMod 2), ∑ i, f.toAdd i = 0 →
        (ae8e_beta cl pt f = 1 ↔ f.toAdd = 0 ∨ f.toAdd = fun _ => 1)) ∧
      (∀ (g : G) (f : Multiplicative (Fin 8 → ZMod 2)), ∑ i, f.toAdd i = 0 →
        g * ae8e_beta cl pt f * g⁻¹ =
          ae8e_beta cl pt (Multiplicative.ofAdd fun i => f.toAdd ((pt.π g).symm i))) ∧
      ∀ x : ↥(Delta u),
        ae8e_beta cl pt (Multiplicative.ofAdd fun i =>
          if i ∈ (pt.E x : Finset (Fin 8)) then (1 : ZMod 2) else 0) = x := by
  obtain ⟨σ, hσ⟩ := ae8e_exists_perm cl pt
  have hstar := ae8e_star_sum cl pt σ hσ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g
    constructor
    · intro hg
      obtain ⟨f, hf, hfl⟩ := ae8e_lam_surj H cl pt (co.e ⟨g, hg⟩).toAdd
      refine ⟨Multiplicative.ofAdd f, hf, ?_⟩
      rw [ae8e_beta_ofAdd, hfl, ofAdd_toAdd, MulEquiv.symm_apply_apply]
    · rintro ⟨f, -, rfl⟩
      exact ((co.e.symm.toMonoidHom.comp (AddMonoidHom.toMultiplicative (ae8e_lam cl pt))) f).2
  · intro f hf
    have h1 := ae8e_beta_eq_one_iff cl pt f.toAdd
    rw [ofAdd_toAdd] at h1
    rw [h1]
    constructor
    · exact fun h => ae8e_kernel H cl pt hstar hf h
    · rintro (h | h)
      · rw [h]
        exact map_zero _
      · rw [h, ae8e_lam_apply]
        simp [hstar]
  · intro g f hf
    exact ae8e_conj H cl pt g f hf
  · intro x
    obtain ⟨i, j, hij, hE⟩ := Finset.card_eq_two.mp (pt.E x).2
    have hx : x = ae8e_x pt i j hij := ae8e_eq_x pt hij hE
    have hind : (fun k => if k ∈ (pt.E x : Finset (Fin 8)) then (1 : ZMod 2) else 0) =
        ae8e_ind {i, j} := by
      funext k
      simp only [ae8e_ind, hE]
    rw [hind, ae8e_beta_pair H cl pt hij, hx]

theorem exists_beta (H : End18.Hyp Ω) (cl : Classes co) (pt : Points u) :
    ∃ β : Multiplicative (Fin 8 → ZMod 2) →* G,
      (∀ g : G, g ∈ zGroup Ω ↔
        ∃ f : Multiplicative (Fin 8 → ZMod 2), ∑ i, f.toAdd i = 0 ∧ β f = g) ∧
      (∀ f : Multiplicative (Fin 8 → ZMod 2), ∑ i, f.toAdd i = 0 →
        (β f = 1 ↔ f.toAdd = 0 ∨ f.toAdd = fun _ => 1)) ∧
      (∀ (g : G) (f : Multiplicative (Fin 8 → ZMod 2)), ∑ i, f.toAdd i = 0 →
        g * β f * g⁻¹ = β (Multiplicative.ofAdd fun i => f.toAdd ((pt.π g).symm i))) ∧
      ∀ x : ↥(Delta u),
        β (Multiplicative.ofAdd fun i => if i ∈ (pt.E x : Finset (Fin 8)) then (1 : ZMod 2) else 0)
          = x :=
  ⟨ae8e_beta cl pt, ae8e_beta_spec H cl pt⟩

theorem ae8e_split (H : End18.Hyp Ω) (cl : Classes co) (pt : Points u) :
    ∃ Hc : Subgroup G,
      AESplitHyp (zGroup Ω) Hc (pt.π.comp Hc.subtype) (ae8e_beta cl pt) ∧
        (pt.π.comp Hc.subtype).range = alternatingGroup (Fin 8) ∧ c.H0 ≤ Hc := by
  obtain ⟨hV, hβ, hconj, -⟩ := ae8e_beta_spec H cl pt
  have hker : pt.π.ker = zGroup Ω := ker_eq_zGroup H cl pt
  have hnorm : (zGroup Ω).Normal := by
    rw [← hker]
    infer_instance
  have hrange : pt.π.range = alternatingGroup (Fin 8) := range_eq H cl pt
  obtain ⟨ι, hι⟩ := Points.map_H0_eq_altOn H cl pt
  obtain ⟨Hc, hcompl, hH0⟩ := splits_of_alt_eight_rel (zGroup Ω) pt.π hker hrange
    (ae8e_beta cl pt) hV hβ hconj ι c.H0 (Chart.H0_inf_zGroup H c) hι
  refine ⟨Hc, ⟨hcompl, ?_, hV, hβ, fun h f hf => hconj h f hf⟩, ?_, hH0⟩
  ·
    rw [injective_iff_map_eq_one]
    intro h hh
    have hmem : (h : G) ∈ zGroup Ω := by
      rw [← hker]
      exact hh
    have hbot : (h : G) ∈ (⊥ : Subgroup G) := by
      rw [← disjoint_iff.mp hcompl.disjoint]
      exact ⟨hmem, h.2⟩
    exact Subtype.ext ((Subgroup.mem_bot).mp hbot)
  · rw [← hrange]
    apply le_antisymm
    · rintro _ ⟨h, rfl⟩
      exact ⟨(h : G), rfl⟩
    rintro _ ⟨g, rfl⟩
    obtain ⟨⟨⟨v, hv⟩, ⟨x, hx⟩⟩, hvx⟩ := hcompl.2 g
    have hπv : pt.π v = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      exact hv
    refine ⟨⟨x, hx⟩, ?_⟩
    show pt.π x = pt.π g
    rw [← hvx]
    simp [map_mul, hπv]

theorem exists_splitHyp (H : End18.Hyp Ω) (cl : Classes co)
    (pt : Points u) :
    ∃ (Hc : Subgroup G) (σ : ↥Hc →* Equiv.Perm (Fin 8))
      (β : Multiplicative (Fin 8 → ZMod 2) →* G),
      AESplitHyp (zGroup Ω) Hc σ β ∧ σ.range = alternatingGroup (Fin 8) := by
  obtain ⟨Hc, hS, hr, -⟩ := ae8e_split H cl pt
  exact ⟨Hc, pt.π.comp Hc.subtype, ae8e_beta cl pt, hS, hr⟩

theorem ae8e_D_comm (cl : Classes co) {x y : G} (hx : x ∈ zGroup Ω) (hy : y ∈ zGroup Ω) :
    x * y = y * x := by
  have h : (⟨x, hx⟩ : ↥(zGroup Ω)) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ := by
    apply co.e.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  exact congrArg Subtype.val h

theorem ae8e_D_sq (cl : Classes co) {x : G} (hx : x ∈ zGroup Ω) : x * x = 1 := by
  have h : (⟨x, hx⟩ : ↥(zGroup Ω)) * ⟨x, hx⟩ = 1 := by
    apply co.e.injective
    rw [map_mul, map_one]
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_one]
    funext i
    simp [ae8e_zmod2_add_self]
  exact congrArg Subtype.val h

end Points

section FrameCert


theorem exists_hom_aeModel_eight (H : End18.Hyp Ω) :
    ∃ φ : G →* AE.AEQ 8, Function.Injective φ ∧ φ.range = TL4.aeModel 8 ∧
      ∃ K ∈ Ω, ∃ (α : Finset (Fin 8)) (hα : α.card = 4) (b : Bool),
        K.map φ = AE.memBar α hα b := by
  obtain ⟨u, hu⟩ := exists_sectFrame H
  obtain ⟨c⟩ := exists_chart H hu.toSectData
  obtain ⟨co⟩ := Chart.exists_coords H hu c
  have cl := exists_classes H hu.toSectData co
  obtain ⟨pt⟩ := exists_points H cl
  obtain ⟨σ, hσ⟩ := ae8e_exists_perm cl pt
  obtain ⟨H', hS, hr, hH0⟩ := Points.ae8e_split H cl pt
  obtain ⟨φ, hinj, hrange, hβφ, hHφ⟩ := hS.exists_hom_aeModel hr
  have hYρ : ∀ y : ↥(pSpan (Generic.centMembers Ω u)), φ (y : G) = Points.ae8e_rho c σ y :=
    fun y => Points.ae8e_phi_eq_rho H cl pt σ hσ hS hβφ hHφ hH0 y
  have hα6 : ({0, 1, 2, 3} : Finset (Fin 6)).card = 4 := by decide
  obtain ⟨L, hL, hLlab⟩ := c.label_surj {0, 1, 2, 3} hα6 true
  obtain ⟨β, hβcard, b', hmemβ⟩ :=
    ae8e_relab6_memAt (ae8e_iota σ) {0, 1, 2, 3} hα6 true
  refine ⟨φ, hinj, hrange, L, hL.1, β, hβcard, b', ?_⟩
  have hLY : L ≤ pSpan (Generic.centMembers Ω u) := le_pSpan hL
  have hcomp : Points.ae8e_rho c σ =
      φ.comp (pSpan (Generic.centMembers Ω u)).subtype :=
    MonoidHom.ext fun y => (hYρ y).symm
  have h1 : (L.subgroupOf (pSpan (Generic.centMembers Ω u))).map (Points.ae8e_rho c σ) =
      L.map φ := by
    rw [hcomp, ← Subgroup.map_map, Subgroup.subgroupOf_map_subtype, inf_of_le_left hLY]
  have h2 : (L.subgroupOf (pSpan (Generic.centMembers Ω u))).map (Points.ae8e_rho c σ) =
      AE.memBar β hβcard b' := by
    have h3 : (L.subgroupOf (pSpan (Generic.centMembers Ω u))).map (Points.ae8e_rho c σ) =
        (((((L.subgroupOf (pSpan (Generic.centMembers Ω u))).map c.ψ.toMonoidHom).map
          (AE.aeSub 6).subtype).map (ae8e_relab6 (ae8e_iota σ))).map (AE.mkQ 8)) := by
      rw [Points.ae8e_rho, Subgroup.map_map, Subgroup.map_map, Subgroup.map_map]
      rfl
    rw [h3, hLlab, hmemβ]
    rfl
  rw [← h1, h2]

end FrameCert

end AE8End

end CFSG.ClassicalInvolution.Q3.Sec13
