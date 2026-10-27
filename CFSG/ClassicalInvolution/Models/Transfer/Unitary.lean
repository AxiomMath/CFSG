module

public import CFSG.ClassicalInvolution.Models.Transfer.Linear
public import CFSG.ClassicalInvolution.Models.UnitaryPairs.Pairs

public section

namespace CFSG.ClassicalInvolution.Models.Transfer

open Matrix CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
  CFSG.ClassicalGroups.Unitary CFSG.LieType.Steinberg CFSG.LieType.BorelTits
  CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Models CFSG.Assembly.LowTwoRank Module
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ}

section Center

theorem pair_ne_three_two_of_five_le {q : ℕ} (hq : 5 ≤ q) {m : ℕ} : (m, q) ≠ (3, 2) := by
  intro h
  have := congrArg Prod.snd h
  simp only at this
  omega

theorem exists_scalar_of_mem_center_su (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f)
    (hn3 : 3 ≤ n) {z : Su K p f n} (hz : z ∈ Subgroup.center (Su K p f n)) :
    ∃ c : K, suMat z = Matrix.scalar (Fin n) c := by
  have hZ := (isQuasisimple_statedSU_of_card (F := K) (p := p) (f := f) hK hn3
    (pair_ne_three_two_of_five_le hq)).2
  let e := MulEquiv.subgroupCongr (SUid_eq_statedSU hK n)
  have hz' : e z ∈ Subgroup.center (StatedSU n (p ^ f) K) := by
    rw [← map_center_mulEquiv e]
    exact ⟨z, hz, rfl⟩
  rw [hZ, Subgroup.mem_subgroupOf] at hz'
  obtain ⟨c, hc⟩ := hz'
  refine ⟨(c : K), ?_⟩
  have : ((e z : StatedSU n (p ^ f) K) : GL (Fin n) K) = (z : GL (Fin n) K) := rfl
  rw [← GeneralLinearGroup.coe_scalar]
  exact (congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) (hc.trans this)).symm

theorem eq_one_or_suMat_eq_neg_one (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f)
    (hn3 : 3 ≤ n) {z : Su K p f n} (hz : z ∈ Subgroup.center (Su K p f n)) (hz2 : z * z = 1) :
    z = 1 ∨ suMat z = -1 := by
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨c, hc⟩ := exists_scalar_of_mem_center_su hK hq hn3 hz
  have hsq : Matrix.scalar (Fin n) (c * c) = 1 := by
    rw [map_mul, ← hc, ← suMat_mul, hz2, suMat_one]
  rw [← map_one (Matrix.scalar (Fin n)), Matrix.scalar_inj] at hsq
  rcases mul_self_eq_one_iff.mp hsq with h | h
  · left
    apply suMat_injective
    rw [hc, h, map_one, suMat_one]
  · right
    rw [hc, h, map_neg, map_one]

end Center

section LongRoot

variable (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)

include hK hp hq

theorem not_mem_center_of_isLongRootSU2 (hn3 : 3 ≤ n) {hn : 2 ≤ n}
    {L : Subgroup (Su K p f n)} {i : Su K p f n} (h : IsLongRootSU2 K p f hn L i) :
    i ∉ Subgroup.center (Su K p f n) := by
  intro hc
  have h2 := two_ne_zero_of_charP_ne_two (K := K) hp
  have hdim := h.finrank_minusSpaceSU h2
  rcases eq_one_or_suMat_eq_neg_one hK hq hn3 hc h.mul_self with h1 | h1
  · have := (h.isClassicalSL2 hK hp).orderOf_eq_two
    rw [h1, orderOf_one] at this
    omega
  · have : minusSpaceSU i = ⊤ := by
      rw [eq_top_iff]
      intro v _
      rw [mem_minusSpaceSU, h1, Matrix.neg_mulVec, Matrix.one_mulVec]
    rw [this, finrank_top, Module.finrank_fin_fun] at hdim
    omega

theorem map_ne_one_of_isLongRootSU2 (hn3 : 3 ≤ n) {hn : 2 ≤ n} {X : Type*} [Group X]
    {θ : Su K p f n →* X} (hker : θ.ker ≤ Subgroup.center (Su K p f n))
    {L : Subgroup (Su K p f n)} {i : Su K p f n} (h : IsLongRootSU2 K p f hn L i) : θ i ≠ 1 :=
  fun h1 => not_mem_center_of_isLongRootSU2 hK hp hq hn3 h (hker (MonoidHom.mem_ker.mpr h1))

theorem eq_one_of_mem_ker_of_isLongRootSU2 (hn3 : 3 ≤ n) {hn : 2 ≤ n}
    {L : Subgroup (Su K p f n)} {i : Su K p f n} (h : IsLongRootSU2 K p f hn L i)
    {X : Type*} [Group X] {θ : Su K p f n →* X} (hker : θ.ker ≤ Subgroup.center (Su K p f n)) :
    ∀ z ∈ L, z ∈ θ.ker → z = 1 :=
  eq_one_of_mem_ker_of_isClassicalSL2 θ (odd_natCard_fixedSubfield hK hp) hker
    (h.isClassicalSL2 hK hp) (map_ne_one_of_isLongRootSU2 hK hp hq hn3 hker h)

theorem eq_of_map_eq_of_isLongRootSU2 (hn3 : 3 ≤ n) {hn : 2 ≤ n}
    {L₁ L₂ : Subgroup (Su K p f n)} {i₁ i₂ : Su K p f n} (h₁ : IsLongRootSU2 K p f hn L₁ i₁)
    (h₂ : IsLongRootSU2 K p f hn L₂ i₂) {X : Type*} [Group X] {θ : Su K p f n →* X}
    (hker : θ.ker ≤ Subgroup.center (Su K p f n)) (hlift : n ≠ 4 ∨ KerInvolutionFree θ)
    (hθ : θ i₁ = θ i₂) : i₁ = i₂ := by
  have h2 := two_ne_zero_of_charP_ne_two (K := K) hp
  have hz : i₁ * i₂⁻¹ ∈ θ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hθ, mul_inv_cancel]
  have hzi : i₁ = (i₁ * i₂⁻¹) * i₂ := by rw [inv_mul_cancel_right]
  have hzc := hker hz
  have hz2 : (i₁ * i₂⁻¹) * (i₁ * i₂⁻¹) = 1 :=
    sq_eq_one_of_mul_sq_eq_one h₂.mul_self hzc (by rw [← hzi]; exact h₁.mul_self)
  have hz1 : i₁ * i₂⁻¹ = 1 := by
    rcases hlift with hn4 | hfree
    · rcases eq_one_or_suMat_eq_neg_one hK hq hn3 hzc hz2 with h1 | h1
      · exact h1
      · exfalso
        apply hn4
        have hmat : suMat i₁ = -suMat i₂ := by
          rw [hzi, suMat_mul, h1, neg_one_mul]
        have hconj := h₁.finrank_minusSpaceSU h2
        rw [minusSpaceSU, hmat] at hconj
        have := eq_two_mul_of_finrank_eigSpace_neg h2 h₂.coe_mul_self
          (h₂.finrank_minusSpaceSU h2) hconj
        omega
    · exact hfree _ hz hz2
  exact mul_inv_eq_one.mp hz1

theorem kerConjFree_of_isLongRootSU2 (hn3 : 3 ≤ n) {hn : 2 ≤ n} {L : Subgroup (Su K p f n)}
    {i : Su K p f n} (h : IsLongRootSU2 K p f hn L i) {X : Type*} [Group X]
    {θ : Su K p f n →* X} (hker : θ.ker ≤ Subgroup.center (Su K p f n))
    (hlift : n ≠ 4 ∨ KerInvolutionFree θ) : KerConjFree θ i := by
  intro g z hz hg
  have hθ : θ (g * i * g⁻¹) = θ i := by
    rw [hg, map_mul, MonoidHom.mem_ker.mp hz, one_mul]
  have hgi := eq_of_map_eq_of_isLongRootSU2 hK hp hq hn3 (h.conj g) h hker hlift hθ
  rw [hg] at hgi
  exact mul_eq_right.mp hgi

theorem commute_and_ne_of_map_su (hn3 : 3 ≤ n) {hn : 2 ≤ n} {L₂ : Subgroup (Su K p f n)}
    {i₂ : Su K p f n} (h₂ : IsLongRootSU2 K p f hn L₂ i₂) {X : Type*} [Group X]
    {θ : Su K p f n →* X} (hker : θ.ker ≤ Subgroup.center (Su K p f n))
    (hlift : n ≠ 4 ∨ KerInvolutionFree θ) {i₁ : Su K p f n} (hc : Commute (θ i₁) (θ i₂))
    (hne : θ i₁ ≠ θ i₂) : Commute i₁ i₂ ∧ i₁ ≠ i₂ :=
  ⟨commute_of_commute_map θ (kerConjFree_of_isLongRootSU2 hK hp hq hn3 h₂ hker hlift) hc,
    fun e => hne (congrArg θ e)⟩

end LongRoot

@[expose] def IsLongRootSU2Image {X : Type*} [Group X] (θ : Su K p f n →* X) (hn : 2 ≤ n)
    (L' : Subgroup X) (i' : X) : Prop :=
  ∃ (L : Subgroup (Su K p f n)) (i : Su K p f n), IsLongRootSU2 K p f hn L i ∧ L.map θ = L' ∧
    θ i = i'

section Image

variable {X : Type} [Group X] {θ : Su K p f n →* X} {hn : 2 ≤ n}
variable (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)

include hK hp hq

theorem IsLongRootSU2Image.nonempty_mulEquiv (hn3 : 3 ≤ n)
    (hker : θ.ker ≤ Subgroup.center (Su K p f n)) {L' : Subgroup X} {i' : X}
    (h : IsLongRootSU2Image θ hn L' i') : Nonempty (L' ≃* SL(2, fixedSubfield K p f)) := by
  obtain ⟨L, i, hL, rfl, rfl⟩ := h
  obtain ⟨e⟩ := (hL.isClassicalSL2 hK hp).nonempty_mulEquiv
  exact ⟨(mulEquivMap (eq_one_of_mem_ker_of_isLongRootSU2 hK hp hq hn3 hL hker)).symm.trans e⟩

theorem IsLongRootSU2Image.orderOf_eq_two (hn3 : 3 ≤ n)
    (hker : θ.ker ≤ Subgroup.center (Su K p f n)) {L' : Subgroup X} {i' : X}
    (h : IsLongRootSU2Image θ hn L' i') : orderOf i' = 2 := by
  obtain ⟨L, i, hL, rfl, rfl⟩ := h
  have hc := hL.isClassicalSL2 hK hp
  exact orderOf_map_eq_two (eq_one_of_mem_ker_of_isLongRootSU2 hK hp hq hn3 hL hker) hc.mem
    hc.orderOf_eq_two

theorem IsLongRootSU2Image.eq_of_orderOf_eq_two (hn3 : 3 ≤ n)
    (hker : θ.ker ≤ Subgroup.center (Su K p f n)) {L' : Subgroup X} {i' : X}
    (h : IsLongRootSU2Image θ hn L' i') {t : X} (ht : t ∈ L') (h2 : orderOf t = 2) : t = i' := by
  obtain ⟨L, i, hL, rfl, rfl⟩ := h
  exact eq_map_of_orderOf_eq_two (eq_one_of_mem_ker_of_isLongRootSU2 hK hp hq hn3 hL hker)
    (fun _ htL ht2 => hL.eq_of_orderOf_eq_two hK hp htL ht2) ht h2

theorem IsLongRootSU2Image.eq_of_involution_eq (hn3 : 3 ≤ n)
    (hker : θ.ker ≤ Subgroup.center (Su K p f n)) (hlift : n ≠ 4 ∨ KerInvolutionFree θ)
    {L₁' L₂' : Subgroup X} {i' : X} (h₁ : IsLongRootSU2Image θ hn L₁' i')
    (h₂ : IsLongRootSU2Image θ hn L₂' i') : L₁' = L₂' := by
  obtain ⟨L₁, i₁, h₁, rfl, hθ₁⟩ := h₁
  obtain ⟨L₂, i₂, h₂, rfl, hθ₂⟩ := h₂
  have := eq_of_map_eq_of_isLongRootSU2 hK hp hq hn3 h₁ h₂ hker hlift (hθ₁.trans hθ₂.symm)
  subst this
  have h2 := two_ne_zero_of_charP_ne_two (K := K) hp
  exact congrArg (Subgroup.map θ)
    ((h₁.eq_longRootGroupSU h2).trans (h₂.eq_longRootGroupSU h2).symm)

theorem IsLongRootSU2Image.isClassicalSL2 (hn3 : 3 ≤ n) (hsurj : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center (Su K p f n)) (hlift : n ≠ 4 ∨ KerInvolutionFree θ)
    {L' : Subgroup X} {i' : X} (h : IsLongRootSU2Image θ hn L' i') :
    IsClassicalSL2 (fixedSubfield K p f) L' i' := by
  obtain ⟨L, i, hL, rfl, rfl⟩ := h
  exact isClassicalSL2_map θ hsurj (hL.isClassicalSL2 hK hp)
    (eq_one_of_mem_ker_of_isLongRootSU2 hK hp hq hn3 hL hker)
    (kerConjFree_of_isLongRootSU2 hK hp hq hn3 hL hker hlift)

omit hK hp hq in
theorem IsLongRootSU2Image.mem {L' : Subgroup X} {i' : X} (h : IsLongRootSU2Image θ hn L' i') :
    i' ∈ L' := by
  obtain ⟨L, i, hL, rfl, rfl⟩ := h
  exact ⟨i, hL.mem, rfl⟩

theorem centralizer_map_eq_of_isLongRootSU2 (hn3 : 3 ≤ n) (hsurj : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center (Su K p f n)) (hlift : n ≠ 4 ∨ KerInvolutionFree θ)
    {L : Subgroup (Su K p f n)} {i : Su K p f n} (h : IsLongRootSU2 K p f hn L i) :
    Subgroup.centralizer ({θ i} : Set X) = (Subgroup.centralizer ({i} : Set (Su K p f n))).map θ :=
  centralizer_map_eq θ hsurj (kerConjFree_of_isLongRootSU2 hK hp hq hn3 h hker hlift)

omit hq in
theorem map_mem_normalizer_of_isLongRootSU2 {L : Subgroup (Su K p f n)} {i : Su K p f n}
    (h : IsLongRootSU2 K p f hn L i) {g : Su K p f n}
    (hg : g ∈ Subgroup.centralizer ({i} : Set (Su K p f n))) :
    θ g ∈ Subgroup.normalizer ((L.map θ : Subgroup X) : Set X) :=
  map_mem_normalizer θ ((h.isClassicalSL2 hK hp).centralizer_le_normalizer hg)

omit hK hp hq in
theorem IsLongRootSU2Image.conj (hsurj : Function.Surjective θ) {L' : Subgroup X} {i' : X}
    (h : IsLongRootSU2Image θ hn L' i') (x : X) :
    IsLongRootSU2Image θ hn (L'.map (MulAut.conj x).toMonoidHom) (x * i' * x⁻¹) := by
  obtain ⟨L, i, hL, rfl, rfl⟩ := h
  obtain ⟨g, rfl⟩ := hsurj x
  refine ⟨_, _, hL.conj g, ?_, by simp⟩
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext y
  simp

end Image

section Lemma65

variable {X : Type} [Group X] {θ : Su K p f n →* X} {hn : 2 ≤ n}
variable (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)

include hK hp hq

theorem lemma_6_5_su_map_of_commute (hn3 : 3 ≤ n) (hker : θ.ker ≤ Subgroup.center (Su K p f n))
    {L₁ L₂ : Subgroup (Su K p f n)} {i₁ i₂ : Su K p f n}
    (h₁ : IsLongRootSU2 K p f hn L₁ i₁) (h₂ : IsLongRootSU2 K p f hn L₂ i₂)
    (hc : Commute i₁ i₂) (hne : i₁ ≠ i₂) :
    (∀ x ∈ L₁.map θ, ∀ y ∈ L₂.map θ, x * y = y * x) ∨
      (θ i₂ ∉ Subgroup.centralizer ((L₁.map θ : Subgroup X) : Set X) ∧
        UnitaryBlockStandardPair K p f (L₁.map θ ⊔ L₂.map θ) (L₁.map θ) (L₂.map θ)) := by
  have hperf : ⁅L₁, L₁⁆ = L₁ :=
    Subgroup.isPerfect_iff.mp ((h₁.isClassicalSL2 hK hp).isPerfect
      (by rw [card_fixedSubfield hK]; omega))
  have key := dichotomy_map hker hperf (B12 K p f) (B23 K p f)
    ((lemma_6_5_su hK hp hn3 h₁ h₂ hc hne).imp (fun h => h.1) id)
  rcases key with hcomm | ⟨hnot, ρ, hker', hrange, hU, hV⟩
  · exact Or.inl hcomm
  · exact Or.inr ⟨hnot, unitaryBlockStandardPair_of_normalized hker' hrange hU hV⟩

theorem lemma_6_5_su_map (hn3 : 3 ≤ n) (hker : θ.ker ≤ Subgroup.center (Su K p f n))
    (hlift : n ≠ 4 ∨ KerInvolutionFree θ) {L₁ L₂ : Subgroup (Su K p f n)}
    {i₁ i₂ : Su K p f n} (h₁ : IsLongRootSU2 K p f hn L₁ i₁) (h₂ : IsLongRootSU2 K p f hn L₂ i₂)
    (hc : Commute (θ i₁) (θ i₂)) (hne : θ i₁ ≠ θ i₂) :
    (∀ x ∈ L₁.map θ, ∀ y ∈ L₂.map θ, x * y = y * x) ∨
      (θ i₂ ∉ Subgroup.centralizer ((L₁.map θ : Subgroup X) : Set X) ∧
        UnitaryBlockStandardPair K p f (L₁.map θ ⊔ L₂.map θ) (L₁.map θ) (L₂.map θ)) := by
  obtain ⟨hc', hne'⟩ := commute_and_ne_of_map_su hK hp hq hn3 h₂ hker hlift hc hne
  exact lemma_6_5_su_map_of_commute hK hp hq hn3 hker h₁ h₂ hc' hne'

theorem mem_centralizer_map_iff_forall_comm_su_of_commute (hn3 : 3 ≤ n)
    (hker : θ.ker ≤ Subgroup.center (Su K p f n)) {L₁ L₂ : Subgroup (Su K p f n)}
    {i₁ i₂ : Su K p f n} (h₁ : IsLongRootSU2 K p f hn L₁ i₁) (h₂ : IsLongRootSU2 K p f hn L₂ i₂)
    (hc : Commute i₁ i₂) (hne : i₁ ≠ i₂) :
    θ i₂ ∈ Subgroup.centralizer ((L₁.map θ : Subgroup X) : Set X) ↔
      ∀ x ∈ L₁.map θ, ∀ y ∈ L₂.map θ, x * y = y * x := by
  have hperf : ⁅L₁, L₁⁆ = L₁ :=
    Subgroup.isPerfect_iff.mp ((h₁.isClassicalSL2 hK hp).isPerfect
      (by rw [card_fixedSubfield hK]; omega))
  exact mem_centralizer_map_iff hker hperf h₂.mem
    (mem_centralizer_iff_forall_comm_su hK hp hn3 h₁ h₂ hc hne)

theorem mem_centralizer_map_iff_forall_comm_su (hn3 : 3 ≤ n)
    (hker : θ.ker ≤ Subgroup.center (Su K p f n)) (hlift : n ≠ 4 ∨ KerInvolutionFree θ)
    {L₁ L₂ : Subgroup (Su K p f n)} {i₁ i₂ : Su K p f n} (h₁ : IsLongRootSU2 K p f hn L₁ i₁)
    (h₂ : IsLongRootSU2 K p f hn L₂ i₂) (hc : Commute (θ i₁) (θ i₂)) (hne : θ i₁ ≠ θ i₂) :
    θ i₂ ∈ Subgroup.centralizer ((L₁.map θ : Subgroup X) : Set X) ↔
      ∀ x ∈ L₁.map θ, ∀ y ∈ L₂.map θ, x * y = y * x := by
  obtain ⟨hc', hne'⟩ := commute_and_ne_of_map_su hK hp hq hn3 h₂ hker hlift hc hne
  exact mem_centralizer_map_iff_forall_comm_su_of_commute hK hp hq hn3 hker h₁ h₂ hc' hne'

theorem lemma_6_5_su_image (hn3 : 3 ≤ n) (hker : θ.ker ≤ Subgroup.center (Su K p f n))
    (hlift : n ≠ 4 ∨ KerInvolutionFree θ) {L₁' L₂' : Subgroup X} {i₁' i₂' : X}
    (h₁ : IsLongRootSU2Image θ hn L₁' i₁') (h₂ : IsLongRootSU2Image θ hn L₂' i₂')
    (hc : Commute i₁' i₂') (hne : i₁' ≠ i₂') :
    (∀ x ∈ L₁', ∀ y ∈ L₂', x * y = y * x) ∨
      (i₂' ∉ Subgroup.centralizer (L₁' : Set X) ∧
        UnitaryBlockStandardPair K p f (L₁' ⊔ L₂') L₁' L₂') := by
  obtain ⟨L₁, i₁, h₁, rfl, rfl⟩ := h₁
  obtain ⟨L₂, i₂, h₂, rfl, rfl⟩ := h₂
  exact lemma_6_5_su_map hK hp hq hn3 hker hlift h₁ h₂ hc hne

theorem mem_centralizer_iff_forall_comm_su_image (hn3 : 3 ≤ n)
    (hker : θ.ker ≤ Subgroup.center (Su K p f n)) (hlift : n ≠ 4 ∨ KerInvolutionFree θ)
    {L₁' L₂' : Subgroup X} {i₁' i₂' : X} (h₁ : IsLongRootSU2Image θ hn L₁' i₁')
    (h₂ : IsLongRootSU2Image θ hn L₂' i₂') (hc : Commute i₁' i₂') (hne : i₁' ≠ i₂') :
    i₂' ∈ Subgroup.centralizer (L₁' : Set X) ↔ ∀ x ∈ L₁', ∀ y ∈ L₂', x * y = y * x := by
  obtain ⟨L₁, i₁, h₁, rfl, rfl⟩ := h₁
  obtain ⟨L₂, i₂, h₂, rfl, rfl⟩ := h₂
  exact mem_centralizer_map_iff_forall_comm_su hK hp hq hn3 hker hlift h₁ h₂ hc hne

end Lemma65

end CFSG.ClassicalInvolution.Models.Transfer
