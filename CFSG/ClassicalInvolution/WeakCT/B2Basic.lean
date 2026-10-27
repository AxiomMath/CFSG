module

public import CFSG.ClassicalInvolution.WeakCT.WeylSigns

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Timmesfeld
  CFSG.Timmesfeld.LevisExtras
open scoped commutatorElement

@[expose] def zB2 : Finset (ℤ × ℤ) :=
  {(1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (-1, -1), (2, 1), (-2, -1)}

@[expose] def bS (z : ℤ × ℤ) : ℤ × ℤ := (-z.1 + 2 * z.2, z.2)

@[expose] def bL (z : ℤ × ℤ) : ℤ × ℤ := (z.1, z.1 - z.2)

@[expose] def eList (z w : ℤ × ℤ) : List (ℕ × ℕ) :=
  [(1, 1), (1, 2), (2, 1), (2, 2)].filter fun p => p.1 • z + p.2 • w ∈ zB2

theorem zB2_exp_le : ∀ z ∈ zB2, ∀ w ∈ zB2, z + w ≠ 0 → ∀ a b : ℕ, 0 < a → 0 < b →
    a • z + b • w ∈ zB2 → a ≤ 2 ∧ b ≤ 2 := by
  intro z hz w hw hzw a b ha hb h
  simp only [zB2, Finset.mem_insert, Finset.mem_singleton] at hz hw h
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Prod.ext_iff] at hzw h ⊢ <;> omega

theorem zB2_neg_mem : ∀ z ∈ zB2, -z ∈ zB2 := by decide

theorem bS_mem : ∀ z ∈ zB2, bS z ∈ zB2 := by decide

theorem bL_mem : ∀ z ∈ zB2, bL z ∈ zB2 := by decide

theorem mem_eList {z w : ℤ × ℤ} (hz : z ∈ zB2) (hw : w ∈ zB2) (hzw : z + w ≠ 0) (p : ℕ × ℕ) :
    p ∈ eList z w ↔ 0 < p.1 ∧ 0 < p.2 ∧ p.1 • z + p.2 • w ∈ zB2 := by
  constructor
  · intro h
    simp only [eList, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false,
      decide_eq_true_eq] at h
    obtain ⟨hp, hm⟩ := h
    rcases hp with rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide, hm⟩
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨h4, h5⟩ := zB2_exp_le z hz w hw hzw p.1 p.2 h1 h2 h3
    simp only [eList, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false,
      decide_eq_true_eq]
    refine ⟨?_, h3⟩
    obtain ⟨a, b⟩ := p
    simp only at h1 h2 h4 h5
    interval_cases a <;> interval_cases b <;> simp

theorem nodup_eList (z w : ℤ × ℤ) : (eList z w).Nodup :=
  List.Nodup.filter _ (by decide)

section Roots

variable {K : Type} [Group K] {D : UniversalRootDatum K} {s l : Fin D.rank}

theorem reflection_pair_bS (hcsl : D.cartan s l = -2) (z : ℤ × ℤ) :
    reflection D.cartan s (pair s l z) = pair s l (bS z) := by
  rw [reflection_pair_left l (D.isFiniteType.apply_self s), hcsl]
  congr 1
  simp [bS]

theorem reflection_pair_bL (hcls : D.cartan l s = -1) (z : ℤ × ℤ) :
    reflection D.cartan l (pair s l z) = pair s l (bL z) := by
  rw [reflection_pair_right s (D.isFiniteType.apply_self l), hcls]
  exact congrArg _ (Prod.ext (by simp [bL]) (by simp only [bL]; ring))

theorem pair_mem_roots_zB2 (hcsl : D.cartan s l = -2) (hcls : D.cartan l s = -1) :
    ∀ z ∈ zB2, pair s l z ∈ D.roots := by
  have h10 : pair s l (1, 0) ∈ D.roots := by rw [pair_one_zero]; exact single_mem_roots s
  have h01 : pair s l (0, 1) ∈ D.roots := by rw [pair_zero_one]; exact single_mem_roots l
  have hS : ∀ z, pair s l z ∈ D.roots → pair s l (bS z) ∈ D.roots := fun z h => by
    rw [← reflection_pair_bS hcsl]
    exact reflection_mem_roots s h
  have hL : ∀ z, pair s l z ∈ D.roots → pair s l (bL z) ∈ D.roots := fun z h => by
    rw [← reflection_pair_bL hcls]
    exact reflection_mem_roots l h
  simp only [zB2, Finset.mem_insert, Finset.mem_singleton]
  rintro z (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact h10
  · exact hS _ h10
  · exact h01
  · exact hL _ h01
  · exact hL _ h10
  · exact hL _ (hS _ h10)
  · exact hS _ h01
  · exact hS _ (hL _ h01)

theorem pairRoots_subset_zB2 (hdiv : D.divisible = ∅) (hcsl : D.cartan s l = -2)
    (hcls : D.cartan l s = -1) : pairRoots D s l ⊆ pair s l '' zB2 :=
  pairRoots_subset_pair hdiv (by decide) (by decide)
    (by rw [hcsl]; decide) (by rw [hcls]; decide)

end Roots

theorem eList_comm : ∀ z ∈ zB2, ∀ w ∈ zB2, z + w ≠ 0 → ∀ p ∈ eList z w, ∀ q ∈ eList z w,
    p ≠ q → (p.1 • z + p.2 • w) + (q.1 • z + q.2 • w) ≠ 0 ∧
      eList (p.1 • z + p.2 • w) (q.1 • z + q.2 • w) = [] := by decide

section Relations

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K}
  {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : Steinberg.CommOrder (Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
  {s l : Fin D.rank}

@[expose] def Cz {r : ℕ} (F : Type) [Field F] (C : (Fin r → ℤ) → (Fin r → ℤ) → ℕ × ℕ → ℤ)
    (s l : Fin r) (z w : ℤ × ℤ) (p : ℕ × ℕ) : F :=
  ((C (pair s l z) (pair s l w) p : ℤ) : F)

theorem ne_of_cartan_neg_two (hcsl : D.cartan s l = -2) : s ≠ l := by
  rintro rfl
  rw [D.isFiniteType.apply_self] at hcsl
  norm_num at hcsl

theorem mem_zB2_of_pair_mem (hdiv : D.divisible = ∅) (hcsl : D.cartan s l = -2)
    (hcls : D.cartan l s = -1) {z : ℤ × ℤ} (h : pair s l z ∈ D.roots) : z ∈ zB2 :=
  mem_of_pair_mem (ne_of_cartan_neg_two hcsl) (pairRoots_subset_zB2 hdiv hcsl hcls) h

theorem pair_add_ne_zero (hcsl : D.cartan s l = -2) {z w : ℤ × ℤ} (hzw : z + w ≠ 0) :
    pair s l z + pair s l w ≠ 0 := by
  rw [← map_add, ← map_zero (pair s l)]
  exact fun h => hzw (pair_injective (ne_of_cartan_neg_two hcsl) h)

theorem pair_nsmul_add (p : ℕ × ℕ) (z w : ℤ × ℤ) :
    p.1 • pair s l z + p.2 • pair s l w = pair s l (p.1 • z + p.2 • w) := by
  rw [map_add, map_nsmul, map_nsmul]

variable (hE : Steinberg.ChevalleyExtras D F x C O)
include hE

theorem comm_rel_nil (hdiv : D.divisible = ∅) (hcsl : D.cartan s l = -2)
    (hcls : D.cartan l s = -1) {z w : ℤ × ℤ} (hz : z ∈ zB2) (hw : w ∈ zB2) (hzw : z + w ≠ 0)
    (hnil : eList z w = []) (c d : F) : ⁅x (pair s l z) c, x (pair s l w) d⁆ = 1 := by
  have hα := pair_mem_roots_zB2 hcsl hcls z hz
  have hβ := pair_mem_roots_zB2 hcsl hcls w hw
  rw [hE.comm _ hα _ hβ (pair_add_ne_zero hcsl hzw) c d]
  have hl : O.list (pair s l z) (pair s l w) = [] := by
    refine List.eq_nil_iff_forall_not_mem.2 fun p hp => ?_
    rw [O.mem_iff _ hα _ hβ (pair_add_ne_zero hcsl hzw)] at hp
    obtain ⟨h1, h2, h3⟩ := hp
    have h3' : p.1 • pair s l z + p.2 • pair s l w ∈ D.roots := h3
    rw [pair_nsmul_add] at h3'
    have h4 := (mem_eList hz hw hzw p).2 ⟨h1, h2, mem_zB2_of_pair_mem hdiv hcsl hcls h3'⟩
    rw [hnil] at h4
    exact List.not_mem_nil h4
  rw [hl]
  rfl

theorem commute_of_nil (hdiv : D.divisible = ∅) (hcsl : D.cartan s l = -2)
    (hcls : D.cartan l s = -1) {z w : ℤ × ℤ} (hz : z ∈ zB2) (hw : w ∈ zB2) (hzw : z + w ≠ 0)
    (hnil : eList z w = []) (c d : F) : Commute (x (pair s l z) c) (x (pair s l w) d) :=
  commutatorElement_eq_one_iff_commute.1 (comm_rel_nil hE hdiv hcsl hcls hz hw hzw hnil c d)

theorem comm_rel (hdiv : D.divisible = ∅) (hcsl : D.cartan s l = -2)
    (hcls : D.cartan l s = -1) {z w : ℤ × ℤ} (hz : z ∈ zB2) (hw : w ∈ zB2) (hzw : z + w ≠ 0)
    (c d : F) : ⁅x (pair s l z) c, x (pair s l w) d⁆ = ((eList z w).map fun p =>
      x (pair s l (p.1 • z + p.2 • w)) (Cz F C s l z w p * c ^ p.1 * d ^ p.2)).prod := by
  have hα := pair_mem_roots_zB2 hcsl hcls z hz
  have hβ := pair_mem_roots_zB2 hcsl hcls w hw
  have hne := pair_add_ne_zero hcsl hzw
  rw [hE.comm _ hα _ hβ hne c d]
  have hperm : (O.list (pair s l z) (pair s l w)).Perm (eList z w) := by
    refine (List.perm_ext_iff_of_nodup (O.nodup _ _) (nodup_eList z w)).2 fun p => ?_
    rw [O.mem_iff _ hα _ hβ hne, mem_eList hz hw hzw]
    constructor
    · rintro ⟨h1, h2, h3⟩
      have h3' : p.1 • pair s l z + p.2 • pair s l w ∈ D.roots := h3
      rw [pair_nsmul_add] at h3'
      exact ⟨h1, h2, mem_zB2_of_pair_mem hdiv hcsl hcls h3'⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, ?_⟩
      change p.1 • pair s l z + p.2 • pair s l w ∈ D.roots
      rw [pair_nsmul_add]
      exact pair_mem_roots_zB2 hcsl hcls _ h3
  have hF : ∀ p : ℕ × ℕ, x (p.1 • pair s l z + p.2 • pair s l w)
      (((C (pair s l z) (pair s l w) p : ℤ) : F) * c ^ p.1 * d ^ p.2) =
      x (pair s l (p.1 • z + p.2 • w)) (Cz F C s l z w p * c ^ p.1 * d ^ p.2) := by
    intro p
    rw [pair_nsmul_add]
    rfl
  simp only [hF]
  symm
  refine (hperm.symm.map _).prod_eq' ?_
  rw [List.pairwise_map]
  refine List.Nodup.pairwise_of_forall_ne (nodup_eList z w) fun p hp q hq hpq => ?_
  have hp' := (mem_eList hz hw hzw p).1 hp
  have hq' := (mem_eList hz hw hzw q).1 hq
  obtain ⟨h1, h2⟩ := eList_comm z hz w hw hzw p hp q hq hpq
  exact commute_of_nil hE hdiv hcsl hcls hp'.2.2 hq'.2.2 h1 h2 _ _

theorem comm_rel_perm (hdiv : D.divisible = ∅) (hcsl : D.cartan s l = -2)
    (hcls : D.cartan l s = -1) {z w : ℤ × ℤ} (hz : z ∈ zB2) (hw : w ∈ zB2) (hzw : z + w ≠ 0)
    {L : List (ℕ × ℕ)} (hL : L.Perm (eList z w)) (c d : F) :
    ⁅x (pair s l z) c, x (pair s l w) d⁆ = (L.map fun p =>
      x (pair s l (p.1 • z + p.2 • w)) (Cz F C s l z w p * c ^ p.1 * d ^ p.2)).prod := by
  rw [comm_rel hE hdiv hcsl hcls hz hw hzw c d]
  refine ((hL.map _).prod_eq' ?_).symm
  rw [List.pairwise_map]
  refine hL.nodup_iff.2 (nodup_eList z w) |>.pairwise_of_forall_ne fun p hp q hq hpq => ?_
  have hp' := (mem_eList hz hw hzw p).1 (hL.mem_iff.1 hp)
  have hq' := (mem_eList hz hw hzw q).1 (hL.mem_iff.1 hq)
  obtain ⟨h1, h2⟩ := eList_comm z hz w hw hzw p (hL.mem_iff.1 hp) q (hL.mem_iff.1 hq) hpq
  exact commute_of_nil hE hdiv hcsl hcls hp'.2.2 hq'.2.2 h1 h2 _ _

end Relations

theorem eList_length_le : ∀ z ∈ zB2, ∀ w ∈ zB2, z + w ≠ 0 → (eList z w).length ≤ 2 := by decide

theorem eList_functional : ∀ z ∈ zB2, ∀ w ∈ zB2, z + w ≠ 0 → ∀ p ∈ eList z w, ∀ q ∈ eList z w,
    p ≠ q → p.1 • z + p.2 • w ≠ q.1 • z + q.2 • w ∧
      ∃ μ ∈ Finset.Icc (-2 : ℤ) 2 ×ˢ Finset.Icc (-2 : ℤ) 2,
        0 < μ.1 * (p.1 • z + p.2 • w).1 + μ.2 * (p.1 • z + p.2 • w).2 ∧
          0 < μ.1 * (q.1 • z + q.2 • w).1 + μ.2 * (q.1 • z + q.2 • w).2 := by decide

section Extraction

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K}
  {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : Steinberg.CommOrder (Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
  {s l : Fin D.rank}

variable (hE : Steinberg.ChevalleyExtras D F x C O)
include hE

theorem x_mem {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) (u : F) : x γ u ∈ D.rootGroup γ :=
  ((hE.param γ hγ).1 _).2 ⟨u, rfl⟩

theorem x_injective' {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) : Function.Injective (x γ) :=
  (hE.param γ hγ).2.2

theorem x_add' {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) (c d : F) :
    x γ (c + d) = x γ c * x γ d :=
  (hE.param γ hγ).2.1 c d

theorem x_neg' {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) (c : F) : x γ (-c) = (x γ c)⁻¹ := by
  have h := x_add' hE hγ c (-c)
  rw [add_neg_cancel, x_zero hE hγ] at h
  exact (eq_inv_of_mul_eq_one_right h.symm)

theorem conj_eq_comm {γ δ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) (t v : F) :
    x γ t * x δ v * x γ (-t) = ⁅x γ t, x δ v⁆ * x δ v := by
  rw [x_neg' hE hγ, commutatorElement_def]
  group

theorem ext2_aux {γ₁ γ₂ : Fin D.rank → ℤ} (h₁ : γ₁ ∈ D.roots) (h₂ : γ₂ ∈ D.roots)
    (hne : γ₁ ≠ γ₂) (f : (Fin D.rank → ℤ) →+ ℤ) (hf₁ : 0 < f γ₁) (hf₂ : 0 < f γ₂)
    (hle : f γ₁ ≤ f γ₂) {u₁ u₂ u₁' u₂' : F}
    (h : x γ₁ u₁ * x γ₂ u₂ = x γ₁ u₁' * x γ₂ u₂') : u₁ = u₁' ∧ u₂ = u₂' := by
  classical
  have key := hE.prodInjective f [γ₁, γ₂] (by simp [hne])
    (fun γ hγ => by
      rcases List.mem_pair.mp hγ with rfl | rfl
      · exact ⟨h₁, hf₁⟩
      · exact ⟨h₂, hf₂⟩)
    (List.pairwise_pair.mpr hle)
  let g : (Fin D.rank → ℤ) → K := fun γ => if γ = γ₁ then x γ₁ u₁ else x γ₂ u₂
  let g' : (Fin D.rank → ℤ) → K := fun γ => if γ = γ₁ then x γ₁ u₁' else x γ₂ u₂'
  have hmem : ∀ (w w' : F), ∀ γ ∈ [γ₁, γ₂],
      (if γ = γ₁ then x γ₁ w else x γ₂ w') ∈ D.rootGroup γ := by
    intro w w' γ hγ
    rcases List.mem_pair.mp hγ with rfl | rfl
    · rw [ite_eq_left rfl]
      exact x_mem hE h₁ w
    · rw [ite_eq_right (Ne.symm hne)]
      exact x_mem hE h₂ w'
  have hprod := key g g' (hmem u₁ u₂) (hmem u₁' u₂') (by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, g, g',
      ite_eq_right (Ne.symm hne)]
    exact h)
  have e1 := hprod γ₁ (by simp)
  have e2 := hprod γ₂ (by simp)
  simp only [g, g', ite_eq_left rfl, ite_eq_right (Ne.symm hne)] at e1 e2
  exact ⟨x_injective' hE h₁ e1, x_injective' hE h₂ e2⟩

theorem ext2 {γ₁ γ₂ : Fin D.rank → ℤ} (h₁ : γ₁ ∈ D.roots) (h₂ : γ₂ ∈ D.roots)
    (hne : γ₁ ≠ γ₂) (f : (Fin D.rank → ℤ) →+ ℤ) (hf₁ : 0 < f γ₁) (hf₂ : 0 < f γ₂)
    (hcomm : ∀ u v, Commute (x γ₁ u) (x γ₂ v)) {u₁ u₂ u₁' u₂' : F}
    (h : x γ₁ u₁ * x γ₂ u₂ = x γ₁ u₁' * x γ₂ u₂') : u₁ = u₁' ∧ u₂ = u₂' := by
  rcases le_total (f γ₁) (f γ₂) with hle | hle
  · exact ext2_aux hE h₁ h₂ hne f hf₁ hf₂ hle h
  · have h' : x γ₂ u₂ * x γ₁ u₁ = x γ₂ u₂' * x γ₁ u₁' := by
      rw [(hcomm u₁ u₂).eq.symm, (hcomm u₁' u₂').eq.symm]
      exact h
    have := ext2_aux hE h₂ h₁ hne.symm f hf₂ hf₁ hle h'
    exact ⟨this.2, this.1⟩

theorem ext3 {γ₁ γ₂ γ₃ : Fin D.rank → ℤ} (h₁ : γ₁ ∈ D.roots) (h₂ : γ₂ ∈ D.roots)
    (h₃ : γ₃ ∈ D.roots) (hne₁₂ : γ₁ ≠ γ₂) (hne₁₃ : γ₁ ≠ γ₃) (hne₂₃ : γ₂ ≠ γ₃)
    (f : (Fin D.rank → ℤ) →+ ℤ) (hf₁ : 0 < f γ₁) (hf₂ : 0 < f γ₂) (hf₃ : 0 < f γ₃)
    (hle₁₂ : f γ₁ ≤ f γ₂) (hle₂₃ : f γ₂ ≤ f γ₃) {u₁ u₂ u₃ u₁' u₂' u₃' : F}
    (h : x γ₁ u₁ * x γ₂ u₂ * x γ₃ u₃ = x γ₁ u₁' * x γ₂ u₂' * x γ₃ u₃') :
    u₁ = u₁' ∧ u₂ = u₂' ∧ u₃ = u₃' := by
  classical
  have key := hE.prodInjective f [γ₁, γ₂, γ₃] (by simp [hne₁₂, hne₁₃, hne₂₃])
    (fun γ hγ => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hγ
      rcases hγ with rfl | rfl | rfl
      · exact ⟨h₁, hf₁⟩
      · exact ⟨h₂, hf₂⟩
      · exact ⟨h₃, hf₃⟩)
    (List.pairwise_cons.2 ⟨fun b hb => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · exact hle₁₂
      · exact hle₁₂.trans hle₂₃, List.pairwise_pair.2 hle₂₃⟩)
  have hmem : ∀ (w₁ w₂ w₃ : F), ∀ γ ∈ [γ₁, γ₂, γ₃],
      (if γ = γ₁ then x γ₁ w₁ else if γ = γ₂ then x γ₂ w₂ else x γ₃ w₃) ∈ D.rootGroup γ := by
    intro w₁ w₂ w₃ γ hγ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hγ
    rcases hγ with rfl | rfl | rfl
    · rw [ite_eq_left rfl]
      exact x_mem hE h₁ w₁
    · rw [ite_eq_right (Ne.symm hne₁₂), ite_eq_left rfl]
      exact x_mem hE h₂ w₂
    · rw [ite_eq_right (Ne.symm hne₁₃), ite_eq_right (Ne.symm hne₂₃)]
      exact x_mem hE h₃ w₃
  have hprod := key
    (fun γ => if γ = γ₁ then x γ₁ u₁ else if γ = γ₂ then x γ₂ u₂ else x γ₃ u₃)
    (fun γ => if γ = γ₁ then x γ₁ u₁' else if γ = γ₂ then x γ₂ u₂' else x γ₃ u₃')
    (hmem u₁ u₂ u₃) (hmem u₁' u₂' u₃') (by
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        ite_eq_right (Ne.symm hne₁₂), ite_eq_right (Ne.symm hne₁₃), ite_eq_right (Ne.symm hne₂₃)]
      simpa [mul_assoc] using h)
  have e1 := hprod γ₁ (by simp)
  have e2 := hprod γ₂ (by simp)
  have e3 := hprod γ₃ (by simp)
  simp only [ite_eq_right (Ne.symm hne₁₂), ite_eq_right (Ne.symm hne₁₃),
    ite_eq_right (Ne.symm hne₂₃)] at e1 e2 e3
  exact ⟨x_injective' hE h₁ e1, x_injective' hE h₂ e2, x_injective' hE h₃ e3⟩

end Extraction

theorem eList_swap_perm {z w : ℤ × ℤ} (hz : z ∈ zB2) (hw : w ∈ zB2) (hzw : z + w ≠ 0) :
    (eList w z).Perm ((eList z w).map Prod.swap) := by
  have hwz : w + z ≠ 0 := by rwa [add_comm]
  refine (List.perm_ext_iff_of_nodup (nodup_eList w z)
    ((nodup_eList z w).map Prod.swap_injective)).2 fun p => ?_
  rw [mem_eList hw hz hwz, List.mem_map]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨p.swap, (mem_eList hz hw hzw _).2 ⟨h2, h1, ?_⟩, Prod.swap_swap p⟩
    simpa [add_comm] using h3
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨h1, h2, h3⟩ := (mem_eList hz hw hzw q).1 hq
    exact ⟨h2, h1, by simpa [add_comm] using h3⟩

theorem list_prod_inv_of_pairwise {G : Type*} [Group G] (L : List G) (h : L.Pairwise Commute) :
    L.prod⁻¹ = (L.map (·⁻¹)).prod := by
  rw [List.prod_inv_reverse]
  refine ((List.reverse_perm _).symm.prod_eq' ?_).symm
  rw [List.pairwise_map]
  exact h.imp fun hc => hc.inv_inv

@[expose] def bSh : ℤ × ℤ →+ ℤ × ℤ :=
  AddMonoidHom.mk' bS fun z w => Prod.ext (by simp only [bS, Prod.fst_add, Prod.snd_add]; ring)
    (by simp only [bS, Prod.snd_add])

@[expose] def bLh : ℤ × ℤ →+ ℤ × ℤ :=
  AddMonoidHom.mk' bL fun z w => Prod.ext (by simp only [bL, Prod.fst_add])
    (by simp only [bL, Prod.fst_add, Prod.snd_add]; ring)

theorem bSh_apply (z : ℤ × ℤ) : bSh z = bS z := rfl

theorem bLh_apply (z : ℤ × ℤ) : bLh z = bL z := rfl

theorem bS_bS (z : ℤ × ℤ) : bS (bS z) = z := Prod.ext (by simp only [bS]; ring) (by simp only [bS])

theorem bL_bL (z : ℤ × ℤ) : bL (bL z) = z := Prod.ext (by simp only [bL]) (by simp only [bL]; ring)

theorem eList_map {r : ℤ × ℤ →+ ℤ × ℤ} (hrmem : ∀ z ∈ zB2, r z ∈ zB2)
    (hrinv : ∀ z, r (r z) = z) (z w : ℤ × ℤ) : eList (r z) (r w) = eList z w := by
  unfold eList
  refine List.filter_congr fun p _ => ?_
  have h : p.1 • r z + p.2 • r w = r (p.1 • z + p.2 • w) := by
    rw [map_add, map_nsmul, map_nsmul]
  rw [h]
  have key : ∀ y, r y ∈ zB2 ↔ y ∈ zB2 := fun y =>
    ⟨fun hy => by simpa [hrinv] using hrmem _ hy, hrmem y⟩
  simp only [key]

section Coeff

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K}
  {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : Steinberg.CommOrder (Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
  {s l : Fin D.rank}

@[expose] def funcl {r : ℕ} (s l : Fin r) (μ : ℤ × ℤ) : (Fin r → ℤ) →+ ℤ :=
  AddMonoidHom.mk' (fun v => μ.1 * v s + μ.2 * v l) (fun a b => by simp only [Pi.add_apply]; ring)

theorem funcl_pair (hsl : s ≠ l) (μ : ℤ × ℤ) (z : ℤ × ℤ) :
    funcl s l μ (pair s l z) = μ.1 * z.1 + μ.2 * z.2 := by
  simp [funcl, pair_apply, hsl, hsl.symm]

variable (hE : Steinberg.ChevalleyExtras D F x C O)
include hE

theorem coeff_eq_of_prod_eq (hdiv : D.divisible = ∅) (hcsl : D.cartan s l = -2)
    (hcls : D.cartan l s = -1) {z w : ℤ × ℤ} (hz : z ∈ zB2) (hw : w ∈ zB2) (hzw : z + w ≠ 0)
    {u u' : ℕ × ℕ → F}
    (h : ((eList z w).map fun p => x (pair s l (p.1 • z + p.2 • w)) (u p)).prod =
      ((eList z w).map fun p => x (pair s l (p.1 • z + p.2 • w)) (u' p)).prod) :
    ∀ p ∈ eList z w, u p = u' p := by
  have hlen := eList_length_le z hz w hw hzw
  have hmem := mem_eList hz hw hzw
  have hcp := eList_comm z hz w hw hzw
  have hfn := eList_functional z hz w hw hzw
  have hnd := nodup_eList z w
  have hsl := ne_of_cartan_neg_two hcsl
  have hroot : ∀ p ∈ eList z w, pair s l (p.1 • z + p.2 • w) ∈ D.roots := fun p hp =>
    pair_mem_roots_zB2 hcsl hcls _ ((hmem p).1 hp).2.2
  generalize eList z w = L at *
  rcases L with _ | ⟨p, _ | ⟨q, _ | ⟨r, t⟩⟩⟩
  · simp
  · intro p' hp'
    obtain rfl : p' = p := by simpa using hp'
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
    exact x_injective' hE (hroot p' (by simp)) h
  · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
    have hpq : p ≠ q := by
      rintro rfl
      simp at hnd
    have hp : p ∈ [p, q] := by simp
    have hq : q ∈ [p, q] := by simp
    obtain ⟨hne, μ, -, hμp, hμq⟩ := hfn p hp q hq hpq
    obtain ⟨h1, h2⟩ := hcp p hp q hq hpq
    have hp' := (hmem p).1 hp
    have hq' := (hmem q).1 hq
    have key := ext2 hE (hroot p hp) (hroot q hq) (fun h => hne (pair_injective hsl h))
      (funcl s l μ) (by rw [funcl_pair hsl]; exact hμp) (by rw [funcl_pair hsl]; exact hμq)
      (fun u v => commute_of_nil hE hdiv hcsl hcls hp'.2.2 hq'.2.2 h1 h2 u v) h
    intro p' hp''
    rcases List.mem_pair.mp hp'' with rfl | rfl
    · exact key.1
    · exact key.2
  · simp at hlen

theorem const_transfer (hdiv : D.divisible = ∅) (hcsl : D.cartan s l = -2)
    (hcls : D.cartan l s = -1) {k : Fin D.rank} {r : ℤ × ℤ →+ ℤ × ℤ}
    (hr : ∀ z, reflection D.cartan k (pair s l z) = pair s l (r z))
    (hrmem : ∀ z ∈ zB2, r z ∈ zB2) (hrinv : ∀ z, r (r z) = z) {z w : ℤ × ℤ} (hz : z ∈ zB2)
    (hw : w ∈ zB2) (hzw : z + w ≠ 0) {p : ℕ × ℕ} (hp : p ∈ eList z w) :
    Cz F C s l (r z) (r w) p * wsign hE k (pair s l z) ^ p.1 * wsign hE k (pair s l w) ^ p.2 =
      wsign hE k (pair s l (p.1 • z + p.2 • w)) * Cz F C s l z w p := by
  have hrz := hrmem z hz
  have hrw := hrmem w hw
  have hrzw : r z + r w ≠ 0 := by
    rw [← map_add]
    intro h
    apply hzw
    have := congrArg r h
    rwa [hrinv, map_zero] at this
  have hmem := mem_eList hz hw hzw
  have hroot : ∀ q ∈ eList z w, pair s l (q.1 • z + q.2 • w) ∈ D.roots := fun q hq =>
    pair_mem_roots_zB2 hcsl hcls _ ((hmem q).1 hq).2.2
  have hzr : pair s l z ∈ D.roots := pair_mem_roots_zB2 hcsl hcls z hz
  have hwr : pair s l w ∈ D.roots := pair_mem_roots_zB2 hcsl hcls w hw
  set W := Steinberg.weylElement x k 1 with hW
  have h1 : W * ⁅x (pair s l z) 1, x (pair s l w) 1⁆ * W⁻¹ =
      ⁅W * x (pair s l z) 1 * W⁻¹, W * x (pair s l w) 1 * W⁻¹⁆ := by
    simp only [commutatorElement_def]
    group
  rw [weyl_conj_one hE hzr, weyl_conj_one hE hwr, hr, hr,
    comm_rel hE hdiv hcsl hcls hrz hrw hrzw, comm_rel hE hdiv hcsl hcls hz hw hzw] at h1
  have hLeq : eList (r z) (r w) = eList z w := eList_map hrmem hrinv z w
  have hmap : W * ((eList z w).map fun q =>
      x (pair s l (q.1 • z + q.2 • w)) (Cz F C s l z w q * (1 : F) ^ q.1 * (1 : F) ^ q.2)).prod *
        W⁻¹ = ((eList z w).map fun q =>
      x (pair s l (q.1 • r z + q.2 • r w)) (wsign hE k (pair s l (q.1 • z + q.2 • w)) *
        (Cz F C s l z w q * (1 : F) ^ q.1 * (1 : F) ^ q.2))).prod := by
    have := map_list_prod (MulAut.conj W) ((eList z w).map fun q =>
      x (pair s l (q.1 • z + q.2 • w)) (Cz F C s l z w q * (1 : F) ^ q.1 * (1 : F) ^ q.2))
    simp only [MulAut.conj_apply] at this
    rw [this, List.map_map]
    congr 1
    refine List.map_congr_left fun q hq => ?_
    simp only [Function.comp, MulAut.conj_apply]
    rw [weyl_conj_one hE (hroot q hq), hr, map_add, map_nsmul, map_nsmul]
  rw [hmap, hLeq] at h1
  have key := coeff_eq_of_prod_eq hE hdiv hcsl hcls hrz hrw hrzw
    (u := fun q => Cz F C s l (r z) (r w) q * (wsign hE k (pair s l z) * 1) ^ q.1 *
      (wsign hE k (pair s l w) * 1) ^ q.2)
    (u' := fun q => wsign hE k (pair s l (q.1 • z + q.2 • w)) *
      (Cz F C s l z w q * (1 : F) ^ q.1 * (1 : F) ^ q.2)) (by rw [hLeq]; exact h1.symm) p
    (by rw [hLeq]; exact hp)
  simpa using key

theorem const_transfer_s (hdiv : D.divisible = ∅) (hcsl : D.cartan s l = -2)
    (hcls : D.cartan l s = -1) {z w : ℤ × ℤ} (hz : z ∈ zB2) (hw : w ∈ zB2) (hzw : z + w ≠ 0)
    {p : ℕ × ℕ} (hp : p ∈ eList z w) :
    Cz F C s l (bS z) (bS w) p * wsign hE s (pair s l z) ^ p.1 * wsign hE s (pair s l w) ^ p.2 =
      wsign hE s (pair s l (p.1 • z + p.2 • w)) * Cz F C s l z w p :=
  const_transfer hE hdiv hcsl hcls (r := bSh) (fun z => reflection_pair_bS hcsl z)
    (fun z hz => bS_mem z hz) bS_bS hz hw hzw hp

theorem const_transfer_l (hdiv : D.divisible = ∅) (hcsl : D.cartan s l = -2)
    (hcls : D.cartan l s = -1) {z w : ℤ × ℤ} (hz : z ∈ zB2) (hw : w ∈ zB2) (hzw : z + w ≠ 0)
    {p : ℕ × ℕ} (hp : p ∈ eList z w) :
    Cz F C s l (bL z) (bL w) p * wsign hE l (pair s l z) ^ p.1 * wsign hE l (pair s l w) ^ p.2 =
      wsign hE l (pair s l (p.1 • z + p.2 • w)) * Cz F C s l z w p :=
  const_transfer hE hdiv hcsl hcls (r := bLh) (fun z => reflection_pair_bL hcls z)
    (fun z hz => bL_mem z hz) bL_bL hz hw hzw hp

theorem const_swap (hdiv : D.divisible = ∅) (hcsl : D.cartan s l = -2)
    (hcls : D.cartan l s = -1) {z w : ℤ × ℤ} (hz : z ∈ zB2) (hw : w ∈ zB2) (hzw : z + w ≠ 0)
    {p : ℕ × ℕ} (hp : p ∈ eList z w) :
    Cz F C s l w z p.swap = -Cz F C s l z w p := by
  have hwz : w + z ≠ 0 := by rwa [add_comm]
  have hmem := mem_eList hz hw hzw
  have hmem' := mem_eList hw hz hwz
  have hroot : ∀ q ∈ eList z w, pair s l (q.1 • z + q.2 • w) ∈ D.roots := fun q hq =>
    pair_mem_roots_zB2 hcsl hcls _ ((hmem q).1 hq).2.2
  have h1 := comm_rel hE hdiv hcsl hcls hw hz hwz (1 : F) 1
  have h2 := comm_rel hE hdiv hcsl hcls hz hw hzw (1 : F) 1
  have h3 : ⁅x (pair s l w) 1, x (pair s l z) 1⁆ = ⁅x (pair s l z) 1, x (pair s l w) 1⁆⁻¹ :=
    (commutatorElement_inv _ _).symm
  rw [h1, h2] at h3
  have hcommz : ((eList z w).map fun q => x (pair s l (q.1 • z + q.2 • w))
      (Cz F C s l z w q * (1 : F) ^ q.1 * (1 : F) ^ q.2)).Pairwise Commute := by
    rw [List.pairwise_map]
    refine List.Nodup.pairwise_of_forall_ne (nodup_eList z w) fun p hp q hq hpq => ?_
    have hp' := (hmem p).1 hp
    have hq' := (hmem q).1 hq
    obtain ⟨h1, h2⟩ := eList_comm z hz w hw hzw p hp q hq hpq
    exact commute_of_nil hE hdiv hcsl hcls hp'.2.2 hq'.2.2 h1 h2 _ _
  have hcommw : ((eList w z).map fun q => x (pair s l (q.1 • w + q.2 • z))
      (Cz F C s l w z q * (1 : F) ^ q.1 * (1 : F) ^ q.2)).Pairwise Commute := by
    rw [List.pairwise_map]
    refine List.Nodup.pairwise_of_forall_ne (nodup_eList w z) fun p hp q hq hpq => ?_
    have hp' := (hmem' p).1 hp
    have hq' := (hmem' q).1 hq
    obtain ⟨h1, h2⟩ := eList_comm w hw z hz hwz p hp q hq hpq
    exact commute_of_nil hE hdiv hcsl hcls hp'.2.2 hq'.2.2 h1 h2 _ _
  rw [list_prod_inv_of_pairwise _ hcommz] at h3
  have hperm := (eList_swap_perm hz hw hzw).map (fun q => x (pair s l (q.1 • w + q.2 • z))
      (Cz F C s l w z q * (1 : F) ^ q.1 * (1 : F) ^ q.2))
  have hL : ((eList w z).map fun q => x (pair s l (q.1 • w + q.2 • z))
      (Cz F C s l w z q * (1 : F) ^ q.1 * (1 : F) ^ q.2)).prod =
      ((eList z w).map fun p => x (pair s l (p.1 • z + p.2 • w))
        (Cz F C s l w z p.swap * (1 : F) ^ p.swap.1 * (1 : F) ^ p.swap.2)).prod := by
    rw [hperm.prod_eq' hcommw, List.map_map]
    congr 1
    refine List.map_congr_left fun p _ => ?_
    simp only [Function.comp, Prod.fst_swap, Prod.snd_swap]
    rw [add_comm (p.2 • w) (p.1 • z)]
  have hR : (((eList z w).map fun q => x (pair s l (q.1 • z + q.2 • w))
      (Cz F C s l z w q * (1 : F) ^ q.1 * (1 : F) ^ q.2)).map (·⁻¹)).prod =
      ((eList z w).map fun p => x (pair s l (p.1 • z + p.2 • w))
        (-(Cz F C s l z w p * (1 : F) ^ p.1 * (1 : F) ^ p.2))).prod := by
    rw [List.map_map]
    congr 1
    refine List.map_congr_left fun p hp => ?_
    simp only [Function.comp]
    rw [x_neg' hE (hroot p hp)]
  have key := coeff_eq_of_prod_eq hE hdiv hcsl hcls hz hw hzw
    (u := fun p => Cz F C s l w z p.swap * (1 : F) ^ p.swap.1 * (1 : F) ^ p.swap.2)
    (u' := fun p => -(Cz F C s l z w p * (1 : F) ^ p.1 * (1 : F) ^ p.2))
    (by rw [← hL, ← hR]; exact h3) p hp
  simpa using key

end Coeff

end CFSG.ClassicalInvolution.WeakCT
