module

public import CFSG.ClassicalInvolution.Models.Transfer.Basic
public import CFSG.ClassicalInvolution.Models.LinearPairs.Intrinsic

public section

namespace CFSG.ClassicalInvolution.Models.Transfer

open Module Matrix CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Models
open scoped MatrixGroups

variable {K : Type} [Field K] {n : ℕ}

theorem eq_one_or_coe_eq_neg_one {z : SL(n, K)} (hn : 1 ≤ n)
    (hz : z ∈ Subgroup.center SL(n, K)) (hz2 : z * z = 1) :
    z = 1 ∨ (z : Matrix (Fin n) (Fin n) K) = -1 := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  have hsq : Matrix.scalar (Fin n) (r * r) = 1 := by
    rw [map_mul, hr, ← Matrix.SpecialLinearGroup.coe_mul, hz2, Matrix.SpecialLinearGroup.coe_one]
  rw [← map_one (Matrix.scalar (Fin n)), Matrix.scalar_inj] at hsq
  rcases mul_self_eq_one_iff.mp hsq with h | h
  · left
    apply Subtype.ext
    rw [← hr, h, map_one, Matrix.SpecialLinearGroup.coe_one]
  · right
    rw [← hr, h, map_neg, map_one]

theorem eq_two_mul_of_finrank_eigSpace_neg (h2 : (2 : K) ≠ 0) {A : Matrix (Fin n) (Fin n) K}
    (hA : A * A = 1) {k : ℕ} (h₁ : finrank K (eigSpace A (-1)) = k)
    (h₂ : finrank K (eigSpace (-A) (-1)) = k) : n = 2 * k := by
  have e : eigSpace (-A) (-1) = eigSpace A 1 := by
    ext v
    rw [mem_eigSpace_neg_one, mem_eigSpace_one, Matrix.neg_mulVec, neg_inj]
  rw [e] at h₂
  have := Submodule.finrank_add_eq_of_isCompl (isCompl_eigSpace h2 hA)
  rw [h₁, h₂, Module.finrank_fin_fun] at this
  omega

section LongRoot

theorem not_mem_center_of_isLongRootSL2 (h2 : (2 : K) ≠ 0) {hn : 2 ≤ n} (hn3 : 3 ≤ n)
    {L : Subgroup SL(n, K)} {i : SL(n, K)} (h : IsLongRootSL2 hn L i) :
    i ∉ Subgroup.center SL(n, K) := by
  intro hc
  have hdim := h.finrank_minusSpace h2
  rcases eq_one_or_coe_eq_neg_one (by omega) hc h.mul_self with h1 | h1
  · have := (h.isClassicalSL2 h2).orderOf_eq_two
    rw [h1, orderOf_one] at this
    omega
  · have : minusSpace i = ⊤ := by
      rw [eq_top_iff]
      intro v _
      rw [mem_minusSpace, h1, Matrix.neg_mulVec, Matrix.one_mulVec]
    rw [this, finrank_top, Module.finrank_fin_fun] at hdim
    omega

theorem map_ne_one_of_isLongRootSL2 (h2 : (2 : K) ≠ 0) {hn : 2 ≤ n} (hn3 : 3 ≤ n)
    {X : Type*} [Group X] {θ : SL(n, K) →* X} (hker : θ.ker ≤ Subgroup.center SL(n, K))
    {L : Subgroup SL(n, K)} {i : SL(n, K)} (h : IsLongRootSL2 hn L i) : θ i ≠ 1 :=
  fun h1 => not_mem_center_of_isLongRootSL2 h2 hn3 h (hker (MonoidHom.mem_ker.mpr h1))

theorem eq_one_of_mem_ker_of_isLongRootSL2 [Finite K] (hodd : Odd (Nat.card K)) (hn3 : 3 ≤ n)
    {hn : 2 ≤ n} {L : Subgroup SL(n, K)} {i : SL(n, K)} (h : IsLongRootSL2 hn L i)
    {X : Type*} [Group X] {θ : SL(n, K) →* X} (hker : θ.ker ≤ Subgroup.center SL(n, K)) :
    ∀ z ∈ L, z ∈ θ.ker → z = 1 :=
  eq_one_of_mem_ker_of_isClassicalSL2 θ hodd hker
    (h.isClassicalSL2 (two_ne_zero_of_odd_natCard hodd))
    (map_ne_one_of_isLongRootSL2 (two_ne_zero_of_odd_natCard hodd) hn3 hker h)

theorem eq_of_map_eq_of_isLongRootSL2 (h2 : (2 : K) ≠ 0) {hn : 2 ≤ n}
    {L₁ L₂ : Subgroup SL(n, K)} {i₁ i₂ : SL(n, K)} (h₁ : IsLongRootSL2 hn L₁ i₁)
    (h₂ : IsLongRootSL2 hn L₂ i₂) {X : Type*} [Group X] {θ : SL(n, K) →* X}
    (hker : θ.ker ≤ Subgroup.center SL(n, K)) (hlift : n ≠ 4 ∨ KerInvolutionFree θ)
    (hθ : θ i₁ = θ i₂) : i₁ = i₂ := by
  have hz : i₁ * i₂⁻¹ ∈ θ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hθ, mul_inv_cancel]
  have hzi : i₁ = (i₁ * i₂⁻¹) * i₂ := by rw [inv_mul_cancel_right]
  have hzc := hker hz
  have hz2 : (i₁ * i₂⁻¹) * (i₁ * i₂⁻¹) = 1 :=
    sq_eq_one_of_mul_sq_eq_one h₂.mul_self hzc (by rw [← hzi]; exact h₁.mul_self)
  have hz1 : i₁ * i₂⁻¹ = 1 := by
    rcases hlift with hn4 | hfree
    · rcases eq_one_or_coe_eq_neg_one (by omega) hzc hz2 with h1 | h1
      · exact h1
      · exfalso
        apply hn4
        have hmat : (i₁ : Matrix (Fin n) (Fin n) K) = -(i₂ : Matrix (Fin n) (Fin n) K) := by
          rw [hzi, Matrix.SpecialLinearGroup.coe_mul, h1, neg_one_mul]
        have hconj := h₁.finrank_minusSpace h2
        rw [minusSpace, hmat] at hconj
        have := eq_two_mul_of_finrank_eigSpace_neg h2 h₂.coe_mul_self
          (h₂.finrank_minusSpace h2) hconj
        omega
    · exact hfree _ hz hz2
  exact mul_inv_eq_one.mp hz1

theorem kerConjFree_of_isLongRootSL2 (h2 : (2 : K) ≠ 0) {hn : 2 ≤ n} {L : Subgroup SL(n, K)}
    {i : SL(n, K)} (h : IsLongRootSL2 hn L i) {X : Type*} [Group X] {θ : SL(n, K) →* X}
    (hker : θ.ker ≤ Subgroup.center SL(n, K)) (hlift : n ≠ 4 ∨ KerInvolutionFree θ) :
    KerConjFree θ i := by
  intro g z hz hg
  have hθ : θ (g * i * g⁻¹) = θ i := by
    rw [hg, map_mul, MonoidHom.mem_ker.mp hz, one_mul]
  have hgi := eq_of_map_eq_of_isLongRootSL2 h2 (h.conj g) h hker hlift hθ
  rw [hg] at hgi
  exact mul_eq_right.mp hgi

theorem commute_and_ne_of_map (h2 : (2 : K) ≠ 0) {hn : 2 ≤ n} {L₂ : Subgroup SL(n, K)}
    {i₂ : SL(n, K)} (h₂ : IsLongRootSL2 hn L₂ i₂) {X : Type*} [Group X] {θ : SL(n, K) →* X}
    (hker : θ.ker ≤ Subgroup.center SL(n, K)) (hlift : n ≠ 4 ∨ KerInvolutionFree θ)
    {i₁ : SL(n, K)} (hc : Commute (θ i₁) (θ i₂)) (hne : θ i₁ ≠ θ i₂) :
    Commute i₁ i₂ ∧ i₁ ≠ i₂ :=
  ⟨commute_of_commute_map θ (kerConjFree_of_isLongRootSL2 h2 h₂ hker hlift) hc,
    fun e => hne (congrArg θ e)⟩

end LongRoot

@[expose] def IsLongRootImage {X : Type*} [Group X] (θ : SL(n, K) →* X) (hn : 2 ≤ n)
    (L' : Subgroup X) (i' : X) : Prop :=
  ∃ (L : Subgroup SL(n, K)) (i : SL(n, K)), IsLongRootSL2 hn L i ∧ L.map θ = L' ∧ θ i = i'

section Image

variable [Finite K] {X : Type} [Group X] {θ : SL(n, K) →* X} {hn : 2 ≤ n}

theorem IsLongRootImage.nonempty_mulEquiv (hodd : Odd (Nat.card K)) (hn3 : 3 ≤ n)
    (hker : θ.ker ≤ Subgroup.center SL(n, K)) {L' : Subgroup X} {i' : X}
    (h : IsLongRootImage θ hn L' i') : Nonempty (L' ≃* SL(2, K)) := by
  obtain ⟨L, i, hL, rfl, rfl⟩ := h
  obtain ⟨e⟩ := (hL.isClassicalSL2 (two_ne_zero_of_odd_natCard hodd)).nonempty_mulEquiv
  exact ⟨(mulEquivMap (eq_one_of_mem_ker_of_isLongRootSL2 hodd hn3 hL hker)).symm.trans e⟩

theorem IsLongRootImage.orderOf_eq_two (hodd : Odd (Nat.card K)) (hn3 : 3 ≤ n)
    (hker : θ.ker ≤ Subgroup.center SL(n, K)) {L' : Subgroup X} {i' : X}
    (h : IsLongRootImage θ hn L' i') : orderOf i' = 2 := by
  obtain ⟨L, i, hL, rfl, rfl⟩ := h
  have hc := hL.isClassicalSL2 (two_ne_zero_of_odd_natCard hodd)
  exact orderOf_map_eq_two (eq_one_of_mem_ker_of_isLongRootSL2 hodd hn3 hL hker) hc.mem
    hc.orderOf_eq_two

omit [Finite K] in
theorem IsLongRootImage.mem {L' : Subgroup X} {i' : X} (h : IsLongRootImage θ hn L' i') :
    i' ∈ L' := by
  obtain ⟨L, i, hL, rfl, rfl⟩ := h
  exact ⟨i, hL.mem, rfl⟩

theorem IsLongRootImage.eq_of_orderOf_eq_two (hodd : Odd (Nat.card K)) (hn3 : 3 ≤ n)
    (hker : θ.ker ≤ Subgroup.center SL(n, K)) {L' : Subgroup X} {i' : X}
    (h : IsLongRootImage θ hn L' i') {t : X} (ht : t ∈ L') (h2 : orderOf t = 2) : t = i' := by
  obtain ⟨L, i, hL, rfl, rfl⟩ := h
  exact eq_map_of_orderOf_eq_two (eq_one_of_mem_ker_of_isLongRootSL2 hodd hn3 hL hker)
    (fun _ htL ht2 => hL.eq_of_orderOf_eq_two (two_ne_zero_of_odd_natCard hodd) htL ht2) ht h2

omit [Finite K] in
theorem IsLongRootImage.eq_of_involution_eq (h2 : (2 : K) ≠ 0)
    (hker : θ.ker ≤ Subgroup.center SL(n, K)) (hlift : n ≠ 4 ∨ KerInvolutionFree θ)
    {L₁' L₂' : Subgroup X} {i' : X} (h₁ : IsLongRootImage θ hn L₁' i')
    (h₂ : IsLongRootImage θ hn L₂' i') : L₁' = L₂' := by
  obtain ⟨L₁, i₁, h₁, rfl, hθ₁⟩ := h₁
  obtain ⟨L₂, i₂, h₂, rfl, hθ₂⟩ := h₂
  have := eq_of_map_eq_of_isLongRootSL2 h2 h₁ h₂ hker hlift (hθ₁.trans hθ₂.symm)
  subst this
  exact congrArg (Subgroup.map θ) ((h₁.eq_longRootGroup h2).trans (h₂.eq_longRootGroup h2).symm)

theorem IsLongRootImage.isClassicalSL2 (hodd : Odd (Nat.card K)) (hn3 : 3 ≤ n)
    (hsurj : Function.Surjective θ) (hker : θ.ker ≤ Subgroup.center SL(n, K))
    (hlift : n ≠ 4 ∨ KerInvolutionFree θ) {L' : Subgroup X} {i' : X}
    (h : IsLongRootImage θ hn L' i') : IsClassicalSL2 K L' i' := by
  obtain ⟨L, i, hL, rfl, rfl⟩ := h
  have h2 := two_ne_zero_of_odd_natCard hodd
  exact isClassicalSL2_map θ hsurj (hL.isClassicalSL2 h2)
    (eq_one_of_mem_ker_of_isLongRootSL2 hodd hn3 hL hker)
    (kerConjFree_of_isLongRootSL2 h2 hL hker hlift)

omit [Finite K] in
theorem centralizer_map_eq_of_isLongRootSL2 (h2 : (2 : K) ≠ 0)
    (hsurj : Function.Surjective θ) (hker : θ.ker ≤ Subgroup.center SL(n, K))
    (hlift : n ≠ 4 ∨ KerInvolutionFree θ) {L : Subgroup SL(n, K)} {i : SL(n, K)}
    (h : IsLongRootSL2 hn L i) :
    Subgroup.centralizer ({θ i} : Set X) = (Subgroup.centralizer ({i} : Set SL(n, K))).map θ :=
  centralizer_map_eq θ hsurj (kerConjFree_of_isLongRootSL2 h2 h hker hlift)

omit [Finite K] in
theorem map_mem_normalizer_of_isLongRootSL2 (h2 : (2 : K) ≠ 0) {L : Subgroup SL(n, K)}
    {i : SL(n, K)} (h : IsLongRootSL2 hn L i) {g : SL(n, K)}
    (hg : g ∈ Subgroup.centralizer ({i} : Set SL(n, K))) :
    θ g ∈ Subgroup.normalizer ((L.map θ : Subgroup X) : Set X) :=
  map_mem_normalizer θ ((h.isClassicalSL2 h2).centralizer_le_normalizer hg)

omit [Finite K] in
theorem IsLongRootImage.conj (hsurj : Function.Surjective θ) {L' : Subgroup X} {i' : X}
    (h : IsLongRootImage θ hn L' i') (x : X) :
    IsLongRootImage θ hn (L'.map (MulAut.conj x).toMonoidHom) (x * i' * x⁻¹) := by
  obtain ⟨L, i, hL, rfl, rfl⟩ := h
  obtain ⟨g, rfl⟩ := hsurj x
  refine ⟨_, _, hL.conj g, ?_, by simp⟩
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext y
  simp

end Image

section Lemma65

variable [Finite K] {X : Type} [Group X] {θ : SL(n, K) →* X} {hn : 2 ≤ n}

theorem lemma_6_5_map_of_commute (hodd : Odd (Nat.card K)) (h5 : 5 ≤ Nat.card K) (hn3 : 3 ≤ n)
    (hker : θ.ker ≤ Subgroup.center SL(n, K)) {L₁ L₂ : Subgroup SL(n, K)}
    {i₁ i₂ : SL(n, K)} (h₁ : IsLongRootSL2 hn L₁ i₁) (h₂ : IsLongRootSL2 hn L₂ i₂)
    (hc : Commute i₁ i₂) (hne : i₁ ≠ i₂) :
    (∀ x ∈ L₁.map θ, ∀ y ∈ L₂.map θ, x * y = y * x) ∨
      (θ i₂ ∉ Subgroup.centralizer ((L₁.map θ : Subgroup X) : Set X) ∧
        LinearBlockStandardPair K (L₁.map θ ⊔ L₂.map θ) (L₁.map θ) (L₂.map θ)) := by
  have h2 := two_ne_zero_of_odd_natCard hodd
  have hperf : ⁅L₁, L₁⁆ = L₁ :=
    Subgroup.isPerfect_iff.mp ((h₁.isClassicalSL2 h2).isPerfect (by omega))
  have key := dichotomy_map hker hperf (B12 K) (B23 K)
    ((lemma_6_5 h2 hn3 h₁ h₂ hc hne).imp (fun h => h.1) id)
  rcases key with hcomm | ⟨hnot, ρ, hker', hrange, hU, hV⟩
  · exact Or.inl hcomm
  · exact Or.inr ⟨hnot, linearBlockStandardPair_of_normalized hker' hrange hU hV⟩

theorem lemma_6_5_map (hodd : Odd (Nat.card K)) (h5 : 5 ≤ Nat.card K) (hn3 : 3 ≤ n)
    (hker : θ.ker ≤ Subgroup.center SL(n, K)) (hlift : n ≠ 4 ∨ KerInvolutionFree θ)
    {L₁ L₂ : Subgroup SL(n, K)} {i₁ i₂ : SL(n, K)} (h₁ : IsLongRootSL2 hn L₁ i₁)
    (h₂ : IsLongRootSL2 hn L₂ i₂) (hc : Commute (θ i₁) (θ i₂)) (hne : θ i₁ ≠ θ i₂) :
    (∀ x ∈ L₁.map θ, ∀ y ∈ L₂.map θ, x * y = y * x) ∨
      (θ i₂ ∉ Subgroup.centralizer ((L₁.map θ : Subgroup X) : Set X) ∧
        LinearBlockStandardPair K (L₁.map θ ⊔ L₂.map θ) (L₁.map θ) (L₂.map θ)) := by
  obtain ⟨hc', hne'⟩ :=
    commute_and_ne_of_map (two_ne_zero_of_odd_natCard hodd) h₂ hker hlift hc hne
  exact lemma_6_5_map_of_commute hodd h5 hn3 hker h₁ h₂ hc' hne'

theorem mem_centralizer_map_iff_forall_comm_of_commute (hodd : Odd (Nat.card K))
    (h5 : 5 ≤ Nat.card K) (hn3 : 3 ≤ n) (hker : θ.ker ≤ Subgroup.center SL(n, K))
    {L₁ L₂ : Subgroup SL(n, K)} {i₁ i₂ : SL(n, K)} (h₁ : IsLongRootSL2 hn L₁ i₁)
    (h₂ : IsLongRootSL2 hn L₂ i₂) (hc : Commute i₁ i₂) (hne : i₁ ≠ i₂) :
    θ i₂ ∈ Subgroup.centralizer ((L₁.map θ : Subgroup X) : Set X) ↔
      ∀ x ∈ L₁.map θ, ∀ y ∈ L₂.map θ, x * y = y * x := by
  have h2 := two_ne_zero_of_odd_natCard hodd
  have hperf : ⁅L₁, L₁⁆ = L₁ :=
    Subgroup.isPerfect_iff.mp ((h₁.isClassicalSL2 h2).isPerfect (by omega))
  exact mem_centralizer_map_iff hker hperf h₂.mem
    (mem_centralizer_iff_forall_comm h2 hn3 h₁ h₂ hc hne)

theorem mem_centralizer_map_iff_forall_comm (hodd : Odd (Nat.card K)) (h5 : 5 ≤ Nat.card K)
    (hn3 : 3 ≤ n) (hker : θ.ker ≤ Subgroup.center SL(n, K))
    (hlift : n ≠ 4 ∨ KerInvolutionFree θ) {L₁ L₂ : Subgroup SL(n, K)} {i₁ i₂ : SL(n, K)}
    (h₁ : IsLongRootSL2 hn L₁ i₁) (h₂ : IsLongRootSL2 hn L₂ i₂)
    (hc : Commute (θ i₁) (θ i₂)) (hne : θ i₁ ≠ θ i₂) :
    θ i₂ ∈ Subgroup.centralizer ((L₁.map θ : Subgroup X) : Set X) ↔
      ∀ x ∈ L₁.map θ, ∀ y ∈ L₂.map θ, x * y = y * x := by
  obtain ⟨hc', hne'⟩ :=
    commute_and_ne_of_map (two_ne_zero_of_odd_natCard hodd) h₂ hker hlift hc hne
  exact mem_centralizer_map_iff_forall_comm_of_commute hodd h5 hn3 hker h₁ h₂ hc' hne'

theorem lemma_6_5_image (hodd : Odd (Nat.card K)) (h5 : 5 ≤ Nat.card K) (hn3 : 3 ≤ n)
    (hker : θ.ker ≤ Subgroup.center SL(n, K)) (hlift : n ≠ 4 ∨ KerInvolutionFree θ)
    {L₁' L₂' : Subgroup X} {i₁' i₂' : X} (h₁ : IsLongRootImage θ hn L₁' i₁')
    (h₂ : IsLongRootImage θ hn L₂' i₂') (hc : Commute i₁' i₂') (hne : i₁' ≠ i₂') :
    (∀ x ∈ L₁', ∀ y ∈ L₂', x * y = y * x) ∨
      (i₂' ∉ Subgroup.centralizer (L₁' : Set X) ∧
        LinearBlockStandardPair K (L₁' ⊔ L₂') L₁' L₂') := by
  obtain ⟨L₁, i₁, h₁, rfl, rfl⟩ := h₁
  obtain ⟨L₂, i₂, h₂, rfl, rfl⟩ := h₂
  exact lemma_6_5_map hodd h5 hn3 hker hlift h₁ h₂ hc hne

theorem mem_centralizer_iff_forall_comm_image (hodd : Odd (Nat.card K)) (h5 : 5 ≤ Nat.card K)
    (hn3 : 3 ≤ n) (hker : θ.ker ≤ Subgroup.center SL(n, K))
    (hlift : n ≠ 4 ∨ KerInvolutionFree θ) {L₁' L₂' : Subgroup X} {i₁' i₂' : X}
    (h₁ : IsLongRootImage θ hn L₁' i₁') (h₂ : IsLongRootImage θ hn L₂' i₂')
    (hc : Commute i₁' i₂') (hne : i₁' ≠ i₂') :
    i₂' ∈ Subgroup.centralizer (L₁' : Set X) ↔ ∀ x ∈ L₁', ∀ y ∈ L₂', x * y = y * x := by
  obtain ⟨L₁, i₁, h₁, rfl, rfl⟩ := h₁
  obtain ⟨L₂, i₂, h₂, rfl, rfl⟩ := h₂
  exact mem_centralizer_map_iff_forall_comm hodd h5 hn3 hker hlift h₁ h₂ hc hne

end Lemma65

end CFSG.ClassicalInvolution.Models.Transfer
