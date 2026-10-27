module

public import CFSG.RankThree.PartOne.KGD.D4T36Torus

public section

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Lattice
  CFSG.RankThree.Chevalley.TrialityFold CFSG.RankThree.PartOne.KGD
open scoped Matrix Pointwise

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem sign_mul_zeta_pow_eq_one {R : Type*} [Field R] (h2 : (2 : R) ≠ 0) (h3 : (3 : R) ≠ 0)
    {ζ : R} (hζ : ζ ^ 2 + ζ + 1 = 0) {s : ℤ} (hs : s = 1 ∨ s = -1) {n : ℕ} (hn : n < 3)
    (h : (s : R) * ζ ^ n = 1) : s = 1 ∧ n = 0 := by
  interval_cases n
  · rcases hs with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · exfalso
      apply h2
      simp at h
      linear_combination -h
  · rcases hs with rfl | rfl
    · exfalso
      apply h3
      simp at h
      linear_combination hζ - (ζ + 2) * h
    · exfalso
      simp at h
      apply one_ne_zero (α := R)
      have hz : ζ = -1 := by linear_combination -h
      rw [hz] at hζ
      linear_combination hζ
  · rcases hs with rfl | rfl
    · exfalso
      apply h3
      rw [Int.cast_one, one_mul] at h
      have hζ' : ζ + 2 = 0 := by linear_combination hζ - h
      linear_combination (-(ζ - 2)) * hζ' + h
    · exfalso
      simp at h
      have hz : ζ ^ 2 = -1 := by linear_combination -h
      have hz0 : ζ = 0 := by linear_combination hζ - hz
      apply one_ne_zero (α := R)
      rw [hz0] at hζ
      linear_combination hζ

section Rigid

variable {L : Type} [Field L] {Fr : L →+* L} {q : ℕ}

theorem rootChar_powA_zpow (hFr : ∀ c, Fr c = c ^ q) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    {a : Fin TwistTag.D4.tag.rank → Lˣ} (ha : a ∈ fixedCharTuples (d4T36M ε) Fr)
    (u : Fin TwistTag.D4.tag.rank → ℤ) (n : ℕ) :
    rootChar a ((d4T36A ^ n) *ᵥ u) = rootChar a u ^ ((ε * q) ^ n) := by
  have hεn : ε ^ n * ε ^ n = 1 := by
    rw [← mul_pow]
    rcases hε with rfl | rfl <;> simp
  have h1 : (d4T36A ^ n) *ᵥ u = (ε ^ n) • ((d4T36M ε ^ n) *ᵥ u) := by
    rw [d4T36M, smul_pow, Matrix.smul_mulVec, smul_smul, hεn, one_smul]
  rw [h1, rootChar_zsmul, rootChar_pow_mulVec_of_mem_fixedCharTuples hFr ha n u,
    ← zpow_natCast, ← _root_.zpow_mul]
  congr 1
  push_cast
  ring

theorem fix_on_sigma (hFr : ∀ c, Fr c = c ^ q) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hrq : (r : ℤ) ∣ (q : ℤ) ^ 2 + ε * q + 1)
    {a₁ a₂ : Fin TwistTag.D4.tag.rank → Lˣ} (h₂ : a₂ ∈ fixedCharTuples (d4T36M ε) Fr)
    (hr₂ : ∀ β, rootChar a₂ β ^ r = 1) {i₁ i₂ : Fin 4} (hi : i₁ ≠ i₂)
    (hk₁ : rootCharKernel a₁ = trialitySigma i₁) (hk₂ : rootCharKernel a₂ = trialitySigma i₂)
    (y : (Fin TwistTag.D4.tag.rank → ℤ) →+ (Fin TwistTag.D4.tag.rank → ℤ))
    (hy : ∀ α, IsRoot TwistTag.D4.tag α → IsRoot TwistTag.D4.tag (y α))
    (hy₁ : ∀ β, rootChar a₁ (y β) = rootChar a₁ β)
    (hy₂ : ∀ β, rootChar a₂ (y β) = rootChar a₂ β) :
    ∀ α : Fin TwistTag.D4.tag.rank → ℤ, α ∈ trialitySigma i₁ → y α = α := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  intro α hα
  have hαroot : IsRoot TwistTag.D4.tag α :=
    isRoot_of_mem_trialitySigmaList (mem_trialitySigma.1 hα)
  have hyα : y α ∈ trialitySigma i₁ := by
    rw [← hk₁] at hα ⊢
    exact ⟨hy α hαroot, by rw [hy₁]; exact hα.2⟩
  obtain ⟨n, hn, horb⟩ := d4T36_sigma_orbit i₁ α (mem_trialitySigma.1 hα) (y α)
    (mem_trialitySigma.1 hyα)
  set z := rootChar a₂ α with hz
  have hz1 : z ≠ 1 := by
    intro h1
    have : α ∈ trialitySigma i₂ := by
      rw [← hk₂]
      exact ⟨hαroot, h1⟩
    exact Set.disjoint_left.1 (pairwise_disjoint_trialitySigma hi) hα this
  have hzord : orderOf z = r := orderOf_eq_prime (hr₂ α) hz1
  have hexp : ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ z ^ (s * (ε * q) ^ n) = z ∧
      ((s = 1 ∧ y α = (d4T36A ^ n) *ᵥ α) ∨ (s = -1 ∧ y α = -((d4T36A ^ n) *ᵥ α))) := by
    rcases horb with h | h
    · have h' : y α = (d4T36A ^ n) *ᵥ α := h
      refine ⟨1, Or.inl rfl, ?_, Or.inl ⟨rfl, h'⟩⟩
      have h1 := hy₂ α
      rw [h', rootChar_powA_zpow hFr hε h₂] at h1
      simpa using h1
    · have h' : y α = -((d4T36A ^ n) *ᵥ α) := h
      refine ⟨-1, Or.inr rfl, ?_, Or.inr ⟨rfl, h'⟩⟩
      have h1 := hy₂ α
      rw [h', d4Q_rootChar_neg, rootChar_powA_zpow hFr hε h₂] at h1
      calc z ^ (-1 * (ε * q) ^ n) = (z ^ (ε * q) ^ n)⁻¹ := by rw [neg_one_mul, _root_.zpow_neg]
        _ = z := h1
  obtain ⟨s, hs, hsz, hyα'⟩ := hexp
  have hdvd : (r : ℤ) ∣ s * (ε * q) ^ n - 1 := by
    have h1 : z ^ (s * (ε * q) ^ n - 1) = 1 := by
      rw [_root_.zpow_sub_one, hsz, mul_inv_cancel]
    have := orderOf_dvd_iff_zpow_eq_one.2 h1
    rwa [hzord] at this
  have hz0 : ((s * (ε * q) ^ n - 1 : ℤ) : ZMod r) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hdvd
  set ζ : ZMod r := ((ε * q : ℤ) : ZMod r) with hζdef
  have hs1 : (s : ZMod r) * ζ ^ n = 1 := by
    have : ((s * (ε * q) ^ n - 1 : ℤ) : ZMod r) = (s : ZMod r) * ζ ^ n - 1 := by
      push_cast
      rw [hζdef]
      push_cast
      ring
    rw [this] at hz0
    exact sub_eq_zero.1 hz0
  have hζ : ζ ^ 2 + ζ + 1 = 0 := by
    have h1 : (((q : ℤ) ^ 2 + ε * q + 1 : ℤ) : ZMod r) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact hrq
    have hε2 : (ε : ZMod r) ^ 2 = 1 := by rcases hε with rfl | rfl <;> simp
    rw [hζdef]
    push_cast at h1 ⊢
    linear_combination h1 + (q : ZMod r) ^ 2 * hε2
  have h2 : (2 : ZMod r) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod r) = 0 := by exact_mod_cast h
    exact absurd (Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff 2 r).1 h')) (by omega)
  have h3 : (3 : ZMod r) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : ZMod r) = 0 := by exact_mod_cast h
    exact absurd (Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff 3 r).1 h')) (by omega)
  obtain ⟨hs', hn'⟩ := sign_mul_zeta_pow_eq_one h2 h3 hζ hs hn hs1
  rcases hyα' with ⟨-, h⟩ | ⟨hs1', -⟩
  · rw [h, hn', pow_zero, Matrix.one_mulVec]
  · rw [hs'] at hs1'
    exact absurd hs1' (by norm_num)

theorem eq_id_of_fixes_cols_det
    (y : (Fin TwistTag.D4.tag.rank → ℤ) →+ (Fin TwistTag.D4.tag.rank → ℤ))
    (x₁ x₂ x₃ x₄ : Fin TwistTag.D4.tag.rank → ℤ) (hdet : (d4T36Col x₁ x₂ x₃ x₄).det = -1)
    (h₁ : y x₁ = x₁) (h₂ : y x₂ = x₂) (h₃ : y x₃ = x₃) (h₄ : y x₄ = x₄)
    (β : Fin TwistTag.D4.tag.rank → ℤ) : y β = β := by
  set N := d4T36Col x₁ x₂ x₃ x₄ with hN
  have hv : N *ᵥ (-(N.adjugate *ᵥ β)) = β := by
    rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec, Matrix.mul_adjugate, hdet]
    simp [Matrix.neg_mulVec]
  have hcol : N *ᵥ (-(N.adjugate *ᵥ β)) =
      ∑ k, (-(N.adjugate *ᵥ β)) k •
        (![x₁, x₂, x₃, x₄] : Fin 4 → Fin TwistTag.D4.tag.rank → ℤ) k := by
    funext r
    simp [hN, d4T36Col, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hk : ∀ k : Fin 4, y ((![x₁, x₂, x₃, x₄] : Fin 4 → Fin TwistTag.D4.tag.rank → ℤ) k) =
      (![x₁, x₂, x₃, x₄] : Fin 4 → Fin TwistTag.D4.tag.rank → ℤ) k := by
    intro k
    match k with
    | 0 => exact h₁
    | 1 => exact h₂
    | 2 => exact h₃
    | 3 => exact h₄
  calc y β = y (N *ᵥ (-(N.adjugate *ᵥ β))) := by rw [hv]
    _ = ∑ k, y ((-(N.adjugate *ᵥ β)) k •
        (![x₁, x₂, x₃, x₄] : Fin 4 → Fin TwistTag.D4.tag.rank → ℤ) k) := by rw [hcol, map_sum]
    _ = ∑ k, (-(N.adjugate *ᵥ β)) k •
        (![x₁, x₂, x₃, x₄] : Fin 4 → Fin TwistTag.D4.tag.rank → ℤ) k :=
      Finset.sum_congr rfl fun k _ => by rw [map_zsmul, hk k]
    _ = β := by rw [← hcol, hv]

theorem trialityU_mem_sigma (i : Fin 4) : trialityU i ∈ trialitySigma i :=
  mem_trialitySigma.2 (by simp [trialitySigmaList])

theorem d4T36M_trialityU_mem_sigma {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (i : Fin 4) :
    d4T36M ε *ᵥ trialityU i ∈ trialitySigma i := by
  refine mem_trialitySigma.2 ?_
  rcases hε with rfl | rfl
  · have h1 : d4T36M 1 *ᵥ trialityU i = trialityAMat *ᵥ trialityU i := by
      rw [d4T36M, one_smul]
      rfl
    rw [h1]
    simp [trialitySigmaList]
  · have h2 : d4T36M (-1) *ᵥ trialityU i = -(trialityAMat *ᵥ trialityU i) := by
      rw [d4T36M, neg_one_smul]
      exact Matrix.neg_mulVec _ _
    rw [h2]
    simp [trialitySigmaList]

theorem eq_id_of_two_characters (hFr : ∀ c, Fr c = c ^ q) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hrq : (r : ℤ) ∣ (q : ℤ) ^ 2 + ε * q + 1) {a₁ a₂ : Fin TwistTag.D4.tag.rank → Lˣ}
    (h₁ : a₁ ∈ fixedCharTuples (d4T36M ε) Fr) (h₂ : a₂ ∈ fixedCharTuples (d4T36M ε) Fr)
    (hr₁ : ∀ β, rootChar a₁ β ^ r = 1) (hr₂ : ∀ β, rootChar a₂ β ^ r = 1) {i₁ i₂ : Fin 4}
    (hi : i₁ ≠ i₂) (hk₁ : rootCharKernel a₁ = trialitySigma i₁)
    (hk₂ : rootCharKernel a₂ = trialitySigma i₂)
    (y : (Fin TwistTag.D4.tag.rank → ℤ) →+ (Fin TwistTag.D4.tag.rank → ℤ))
    (hy : ∀ α, IsRoot TwistTag.D4.tag α → IsRoot TwistTag.D4.tag (y α))
    (hy₁ : ∀ β, rootChar a₁ (y β) = rootChar a₁ β)
    (hy₂ : ∀ β, rootChar a₂ (y β) = rootChar a₂ β) (β : Fin TwistTag.D4.tag.rank → ℤ) :
    y β = β := by
  have f₁ := fix_on_sigma hFr hε hr hr5 hrq h₂ hr₂ hi hk₁ hk₂ y hy hy₁ hy₂
  have f₂ := fix_on_sigma hFr hε hr hr5 hrq h₁ hr₁ hi.symm hk₂ hk₁ y hy hy₂ hy₁
  have hu₁ := trialityU_mem_sigma i₁
  have hu₂ := trialityU_mem_sigma i₂
  have hroot₁ : IsRoot TwistTag.D4.tag (trialityU i₁) :=
    isRoot_of_mem_trialitySigmaList (mem_trialitySigma.1 hu₁)
  have hroot₂ : IsRoot TwistTag.D4.tag (trialityU i₂) :=
    isRoot_of_mem_trialitySigmaList (mem_trialitySigma.1 hu₂)
  have hdet : (d4T36Col (trialityU i₁) (d4T36M ε *ᵥ trialityU i₁) (trialityU i₂)
      (d4T36M ε *ᵥ trialityU i₂)).det = -1 := by
    have hnot : ¬∃ k, trialityU i₁ ∈ trialitySigma k ∧ trialityU i₂ ∈ trialitySigma k := by
      rintro ⟨k, hk1, hk2⟩
      have e1 : k = i₁ := by
        by_contra hki
        exact (Set.disjoint_left.1 (pairwise_disjoint_trialitySigma hki)) hk1 hu₁
      have e2 : k = i₂ := by
        by_contra hki
        exact (Set.disjoint_left.1 (pairwise_disjoint_trialitySigma hki)) hk2 hu₂
      exact hi (e1.symm.trans e2)
    have h := (trialityColMat_det hε hroot₁ hroot₂).2 hnot
    have e : d4T36Col (trialityU i₁) (d4T36M ε *ᵥ trialityU i₁) (trialityU i₂)
        (d4T36M ε *ᵥ trialityU i₂) = trialityColMat (trialityU i₁)
        ((ε • trialityA) *ᵥ trialityU i₁) (trialityU i₂) ((ε • trialityA) *ᵥ trialityU i₂) := by
      rw [d4T36M_eq]
      rfl
    exact (congrArg Matrix.det e).trans h
  exact eq_id_of_fixes_cols_det y _ _ _ _ hdet (f₁ _ hu₁) (f₁ _ (d4T36M_trialityU_mem_sigma hε i₁))
    (f₂ _ hu₂) (f₂ _ (d4T36M_trialityU_mem_sigma hε i₂)) β

def sigmaTrivialSubgroup {E : Type*} [Group E] (β : E →* (Fin TwistTag.D4.tag.rank → Lˣ))
    (i : Fin 4) : Subgroup E where
  carrier := {e | ∀ α : Fin TwistTag.D4.tag.rank → ℤ, α ∈ trialitySigma i → rootChar (β e) α = 1}
  one_mem' := fun α _ => by rw [map_one]; exact CTTorus.rootChar_one α
  mul_mem' := fun {a b} ha hb α hα => by
    rw [map_mul, CTTorus.rootChar_mul, ha α hα, hb α hα, one_mul]
  inv_mem' := fun {a} ha α hα => by
    rw [map_inv, rootChar_inv_apply, ha α hα, inv_one]

theorem sigmaTrivialSubgroup_card_le {E : Type*} [Group E] [Finite E] {r : ℕ} (hr : r.Prime)
    (hcard : Nat.card E = r ^ 2) (β : E →* (Fin TwistTag.D4.tag.rank → Lˣ)) (i : Fin 4)
    (hne : sigmaTrivialSubgroup β i ≠ ⊤) : Nat.card (sigmaTrivialSubgroup β i) ≤ r := by
  have hdvd : Nat.card (sigmaTrivialSubgroup β i) ∣ r ^ 2 :=
    hcard ▸ Subgroup.card_subgroup_dvd_card _
  obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow hr).1 hdvd
  by_contra hlt'
  have hlt := not_le.1 hlt'
  have hr2 := hr.two_le
  have hk2 : k = 2 := by
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with h | h | h
    · rw [h, pow_zero] at hkeq
      omega
    · rw [h, pow_one] at hkeq
      omega
    · exact h
  apply hne
  exact (Subgroup.card_eq_iff_eq_top _).1 (by rw [hkeq, hk2, hcard])

theorem exists_regular_of_two_singular {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) {E : Type*} [Group E] [Finite E] {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hcard : Nat.card E = r ^ 2) (β : E →* (Fin TwistTag.D4.tag.rank → Lˣ))
    (hβ : ∀ e, β e ∈ fixedCharTuples (d4T36M ε) Fr) {q₁ q₂ : E} {i₁ i₂ : Fin 4}
    (hi : i₁ ≠ i₂) (h₁ : rootCharKernel (β q₁) = trialitySigma i₁)
    (h₂ : rootCharKernel (β q₂) = trialitySigma i₂) :
    ∃ e : E, rootCharKernel (β e) = ∅ := by
  classical
  have : Fintype E := Fintype.ofFinite E
  have hS : ∀ i, sigmaTrivialSubgroup β i ≠ ⊤ := by
    intro i hi'
    have hq₁ : q₁ ∈ sigmaTrivialSubgroup β i := hi' ▸ Subgroup.mem_top _
    have hq₂ : q₂ ∈ sigmaTrivialSubgroup β i := hi' ▸ Subgroup.mem_top _
    have hU := trialityU_mem_sigma i
    have hroot : IsRoot TwistTag.D4.tag (trialityU i) :=
      isRoot_of_mem_trialitySigmaList (mem_trialitySigma.1 hU)
    have e1 : trialityU i ∈ trialitySigma i₁ := by
      rw [← h₁]
      exact ⟨hroot, hq₁ _ hU⟩
    have e2 : trialityU i ∈ trialitySigma i₂ := by
      rw [← h₂]
      exact ⟨hroot, hq₂ _ hU⟩
    have c1 : i = i₁ := by
      by_contra hne
      exact Set.disjoint_left.1 (pairwise_disjoint_trialitySigma hne) hU e1
    have c2 : i = i₂ := by
      by_contra hne
      exact Set.disjoint_left.1 (pairwise_disjoint_trialitySigma hne) hU e2
    exact hi (c1.symm.trans c2)
  have hcardS : ∀ i, Nat.card (sigmaTrivialSubgroup β i) ≤ r := fun i =>
    sigmaTrivialSubgroup_card_le hr hcard β i (hS i)
  by_contra hno'
  have hno : ∀ e, rootCharKernel (β e) ≠ ∅ := fun e he => hno' ⟨e, he⟩
  have hcover : ∀ e : E, ∃ i, e ∈ sigmaTrivialSubgroup β i := by
    intro e
    by_cases h1 : β e = 1
    · exact ⟨0, fun α _ => by rw [h1]; exact CTTorus.rootChar_one α⟩
    · rcases d4T36_rootCharKernel_cases hε (hβ e) h1 with h | ⟨i, hi⟩
      · exact absurd h (hno e)
      · exact ⟨i, fun α hα => by
          have : α ∈ rootCharKernel (β e) := hi ▸ hα
          exact this.2⟩
  have hsum : Nat.card E ≤ ∑ i : Fin 4, Nat.card (sigmaTrivialSubgroup β i) := by
    calc Nat.card E = (Finset.univ : Finset E).card := Nat.card_eq_fintype_card
      _ ≤ (Finset.univ.biUnion fun i : Fin 4 =>
            (Finset.univ.filter fun e => e ∈ sigmaTrivialSubgroup β i)).card := by
          apply Finset.card_le_card
          intro e _
          obtain ⟨i, hi⟩ := hcover e
          exact Finset.mem_biUnion.2
            ⟨i, Finset.mem_univ _, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩
      _ ≤ ∑ i : Fin 4, (Finset.univ.filter fun e => e ∈ sigmaTrivialSubgroup β i).card :=
          Finset.card_biUnion_le
      _ = ∑ i : Fin 4, Nat.card (sigmaTrivialSubgroup β i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h4 : ∑ i : Fin 4, Nat.card (sigmaTrivialSubgroup β i) ≤ 4 * r := by
    calc ∑ i : Fin 4, Nat.card (sigmaTrivialSubgroup β i) ≤ ∑ _i : Fin 4, r :=
          Finset.sum_le_sum fun i _ => hcardS i
      _ = 4 * r := by simp
  rw [hcard] at hsum
  nlinarith

end Rigid

end CFSG.GH74.GLS.Stage2.Bender.Thm1
