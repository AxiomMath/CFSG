module

public import CFSG.HardMathSupport.C14IdxA2Hom
public import CFSG.LieType.AlgebraicGroups.ToralTwistPinningRoots

public section

namespace CFSG.HardMathSupport.C14Idx

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint

private theorem injective_four_of_nodup {τ : Tag} {α β α' β' : Fin τ.rank → ℤ}
    (hne : [α, β, α', β'].Nodup) :
    Function.Injective (![α, β, α', β'] : Fin 4 → Fin τ.rank → ℤ) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

private noncomputable def imageCoeff {τ : Tag} {s : ℕ} (ν : Fin s → Fin τ.rank → ℤ)
    (a : Fin s → ℤ) : (Fin τ.rank → ℤ) → ℤ :=
  fun x => if h : ∃ i, ν i = x then a (Classical.choose h) else 0

private theorem imageCoeff_apply {τ : Tag} {s : ℕ} {ν : Fin s → Fin τ.rank → ℤ}
    (hν : Function.Injective ν) (a : Fin s → ℤ) (i : Fin s) :
    imageCoeff ν a (ν i) = a i := by
  classical
  have hex : ∃ j, ν j = ν i := ⟨i, rfl⟩
  rw [imageCoeff, dif_pos hex]
  congr 1
  exact hν (Classical.choose_spec hex)

private theorem imageCoeff_of_notMem {τ : Tag} {s : ℕ} {ν : Fin s → Fin τ.rank → ℤ}
    (a : Fin s → ℤ) {x : Fin τ.rank → ℤ} (hx : ∀ i, ν i ≠ x) :
    imageCoeff ν a x = 0 := by
  classical
  rw [imageCoeff]
  split_ifs with h
  · obtain ⟨i, hi⟩ := h
    exact absurd hi (hx i)
  · rfl

private theorem sum_imageCoeff {τ : Tag} {s : ℕ} {ν : Fin s → Fin τ.rank → ℤ}
    {Δ : Finset (Fin τ.rank → ℤ)} (hν : Function.Injective ν)
    (hνΔ : ∀ i, ν i ∈ Δ) (a : Fin s → ℤ) :
    ∑ x ∈ Δ, imageCoeff ν a x • x = ∑ i, a i • ν i := by
  classical
  set S := Finset.univ.image ν with hS
  have hSsub : S ⊆ Δ := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
    exact hνΔ i
  have hsupp : ∀ x ∈ Δ, x ∉ S → imageCoeff ν a x = 0 := by
    intro x _ hx
    exact imageCoeff_of_notMem a (fun i hi =>
      hx (Finset.mem_image.2 ⟨i, Finset.mem_univ i, hi⟩))
  have hsupp' : ∀ x ∈ Δ, x ∉ S → imageCoeff ν a x • x = 0 := by
    intro x hx hxS
    rw [hsupp x hx hxS, zero_smul]
  rw [← Finset.sum_subset hSsub hsupp', hS, Finset.sum_image]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [imageCoeff_apply hν]
  · intro i _ j _ hij
    rw [hν hij]

private theorem sum_four {τ : Tag} {a b c d : ℤ} {α β γ δ : Fin τ.rank → ℤ} :
    ∑ i : Fin 4,
        (![a, b, c, d] : Fin 4 → ℤ) i •
          (![α, β, γ, δ] : Fin 4 → Fin τ.rank → ℤ) i =
      a • α + b • β + c • γ + d • δ := by
  rw [Fin.sum_univ_four]
  simp [add_assoc]

private theorem sum_imageCoeff_four {τ : Tag} {α β α' β' : Fin τ.rank → ℤ}
    {Δ : Finset (Fin τ.rank → ℤ)} (hν : Function.Injective
      (![α, β, α', β'] : Fin 4 → Fin τ.rank → ℤ))
    (hα : α ∈ Δ) (hβ : β ∈ Δ) (hα' : α' ∈ Δ) (hβ' : β' ∈ Δ) (a b a' b' : ℤ) :
    ∑ x ∈ Δ, imageCoeff (![α, β, α', β'] : Fin 4 → Fin τ.rank → ℤ)
        ![a, b, a', b'] x • x = a • α + b • β + a' • α' + b' • β' := by
  rw [sum_imageCoeff hν (fun i => by fin_cases i <;> simp [hα, hβ, hα', hβ'])
    (![a, b, a', b'] : Fin 4 → ℤ)]
  exact sum_four

private theorem mem_a2PairRoots_iff {τ : Tag} {α β γ : Fin τ.rank → ℤ} :
    γ ∈ a2PairRoots α β ↔
      γ = α ∨ γ = β ∨ γ = α + β ∨ γ = -α ∨ γ = -β ∨ γ = -(α + β) := by
  simp [a2PairRoots]

private theorem exists_coeffs_of_mem_a2PairRoots {τ : Tag} {α β γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ a2PairRoots α β) :
    ∃ a b : ℤ, (a ≠ 0 ∨ b ≠ 0) ∧ γ = a • α + b • β := by
  rcases mem_a2PairRoots_iff.1 hγ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, 0, Or.inl one_ne_zero, by simp⟩
  · exact ⟨0, 1, Or.inr one_ne_zero, by simp⟩
  · exact ⟨1, 1, Or.inl one_ne_zero, by simp⟩
  · exact ⟨-1, 0, Or.inl (by norm_num), by simp⟩
  · exact ⟨0, -1, Or.inr (by norm_num), by simp⟩
  · exact ⟨-1, -1, Or.inl (by norm_num), by simp [neg_add_rev, add_comm]⟩

theorem mem_kernelRoots_of_mem_a2PairRoots {τ : Tag} {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {α β : Fin τ.rank → ℤ}
    (hα : α ∈ kernelRoots χ) (hβ : β ∈ kernelRoots χ)
    (hsum : α + β ∈ kernelRoots χ) {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ a2PairRoots α β) : γ ∈ kernelRoots χ := by
  rcases mem_a2PairRoots_iff.1 hγ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hα
  · exact hβ
  · exact hsum
  · exact ⟨IsRoot.neg hα.1, chi_neg hα.2⟩
  · exact ⟨IsRoot.neg hβ.1, chi_neg hβ.2⟩
  · exact ⟨IsRoot.neg hsum.1, chi_neg hsum.2⟩

private theorem coords_unique_kernel
    {τ : Tag} {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    {c c' : (Fin τ.rank → ℤ) → ℤ}
    (h : ∑ β ∈ simpleRoots (kernelRoots χ), c β • β =
      ∑ β ∈ simpleRoots (kernelRoots χ), c' β • β) :
    ∀ β ∈ simpleRoots (kernelRoots χ), c β = c' β := by
  have h1 := congrArg toReal h
  rw [toReal_sum_smul, toReal_sum_smul] at h1
  have h2 : ∑ β ∈ simpleRoots (kernelRoots χ), ((c β : ℝ) - c' β) • toReal β = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, h1, sub_self]
  intro β hβ
  have hzero := eq_zero_of_sum_smul_toReal_eq_zero
    (fun _ hμ => simpleRoots_height_pos hμ)
    (fun _ hμ _ hν hne => iform_nonpos_of_mem_simpleRoots_kernelRoots hμ hν hne)
    h2 β hβ
  exact_mod_cast sub_eq_zero.1 hzero

private theorem coords_nonneg_of_mem_posRoots_kernel
    {τ : Tag} {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    {η : Fin τ.rank → ℤ} (hη : η ∈ posRoots (kernelRoots χ))
    {c : (Fin τ.rank → ℤ) → ℤ}
    (hc : η = ∑ β ∈ simpleRoots (kernelRoots χ), c β • β) :
    ∀ β ∈ simpleRoots (kernelRoots χ), 0 ≤ c β := by
  obtain ⟨d, hd, he⟩ := exists_nonneg_coords_kernel hη
  have hcu := coords_unique_kernel (h := hc.symm.trans he)
  intro β hβ
  rw [hcu β hβ]
  exact hd β hβ

private theorem coords_nonpos_of_mem_negRoots_kernel
    {τ : Tag} {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    {η : Fin τ.rank → ℤ} (hη : η ∈ negRoots (kernelRoots χ))
    {c : (Fin τ.rank → ℤ) → ℤ}
    (hc : η = ∑ β ∈ simpleRoots (kernelRoots χ), c β • β) :
    ∀ β ∈ simpleRoots (kernelRoots χ), c β ≤ 0 := by
  have hpos : -η ∈ posRoots (kernelRoots χ) := hη
  have hc' : -η = ∑ β ∈ simpleRoots (kernelRoots χ), (-c) β • β := by
    rw [hc, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun β _ => by rw [Pi.neg_apply, neg_smul]
  have hnn := coords_nonneg_of_mem_posRoots_kernel hpos hc'
  intro β hβ
  have := hnn β hβ
  simp only [Pi.neg_apply] at this
  omega

theorem not_isRoot_add_of_mem_a2PairRoots
    {τ : Tag} {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {α β α' β' : Fin τ.rank → ℤ}
    (hα : α ∈ simpleRoots (kernelRoots χ)) (hβ : β ∈ simpleRoots (kernelRoots χ))
    (hα' : α' ∈ simpleRoots (kernelRoots χ)) (hβ' : β' ∈ simpleRoots (kernelRoots χ))
    (hne : [α, β, α', β'].Nodup) (hsum : IsRoot τ (α + β)) (hsum' : IsRoot τ (α' + β'))
    (horth : ∀ x ∈ ({α, β} : Set (Fin τ.rank → ℤ)), ∀ y ∈ ({α', β'} : Set (Fin τ.rank → ℤ)),
      iform x y = 0)
    {γ δ : Fin τ.rank → ℤ} (hγ : γ ∈ a2PairRoots α β) (hδ : δ ∈ a2PairRoots α' β') :
    ¬IsRoot τ (γ + δ) ∧ γ ≠ -δ := by
  classical
  have hαk : α ∈ kernelRoots χ := simpleRoots_subset hα
  have hβk : β ∈ kernelRoots χ := simpleRoots_subset hβ
  have hα'k : α' ∈ kernelRoots χ := simpleRoots_subset hα'
  have hβ'k : β' ∈ kernelRoots χ := simpleRoots_subset hβ'
  have hsumk : α + β ∈ kernelRoots χ := ⟨hsum, by
    rw [ofAdd_add, map_mul, hαk.2, hβk.2, one_mul]⟩
  have hsum'k : α' + β' ∈ kernelRoots χ := ⟨hsum', by
    rw [ofAdd_add, map_mul, hα'k.2, hβ'k.2, one_mul]⟩
  have hγk : γ ∈ kernelRoots χ := mem_kernelRoots_of_mem_a2PairRoots hαk hβk hsumk hγ
  have hδk : δ ∈ kernelRoots χ := mem_kernelRoots_of_mem_a2PairRoots hα'k hβ'k hsum'k hδ
  obtain ⟨a, b, hab, hγab⟩ := exists_coeffs_of_mem_a2PairRoots hγ
  obtain ⟨a', b', ha'b', hδab⟩ := exists_coeffs_of_mem_a2PairRoots hδ
  have hν : Function.Injective (![α, β, α', β'] : Fin 4 → Fin τ.rank → ℤ) :=
    injective_four_of_nodup hne
  have hαα' : iform α α' = 0 := horth α (by simp) α' (by simp)
  have hαβ' : iform α β' = 0 := horth α (by simp) β' (by simp)
  have hβα' : iform β α' = 0 := horth β (by simp) α' (by simp)
  have hββ' : iform β β' = 0 := horth β (by simp) β' (by simp)
  have horthγδ : iform γ δ = 0 := by
    rw [hγab, hδab]
    simp only [iform_add_left, iform_add_right, iform_smul_left, iform_smul_right,
      hαα', hαβ', hβα', hββ']
    ring
  have hsumγδ : γ + δ = a • α + b • β + a' • α' + b' • β' := by
    rw [hγab, hδab]
    abel
  have hsumγδ' : γ - δ = a • α + b • β + (-a') • α' + (-b') • β' := by
    rw [hγab, hδab]
    simp only [neg_smul]
    abel
  have hγδexp : γ + δ = ∑ x ∈ simpleRoots (kernelRoots χ),
      imageCoeff (![α, β, α', β'] : Fin 4 → Fin τ.rank → ℤ) ![a, b, a', b'] x • x := by
    rw [sum_imageCoeff_four hν hα hβ hα' hβ' a b a' b']
    exact hsumγδ
  have hγδ'exp : γ - δ = ∑ x ∈ simpleRoots (kernelRoots χ),
      imageCoeff (![α, β, α', β'] : Fin 4 → Fin τ.rank → ℤ) ![a, b, -a', -b'] x • x := by
    rw [sum_imageCoeff_four hν hα hβ hα' hβ' a b (-a') (-b')]
    exact hsumγδ'
  have e0 : imageCoeff (![α, β, α', β'] : Fin 4 → Fin τ.rank → ℤ) ![a, b, a', b'] α = a := by
    simpa using imageCoeff_apply hν ![a, b, a', b'] (0 : Fin 4)
  have e1 : imageCoeff (![α, β, α', β'] : Fin 4 → Fin τ.rank → ℤ) ![a, b, a', b'] β = b := by
    simpa using imageCoeff_apply hν ![a, b, a', b'] (1 : Fin 4)
  have e2 : imageCoeff (![α, β, α', β'] : Fin 4 → Fin τ.rank → ℤ) ![a, b, a', b'] α' = a' := by
    simpa using imageCoeff_apply hν ![a, b, a', b'] (2 : Fin 4)
  have e3 : imageCoeff (![α, β, α', β'] : Fin 4 → Fin τ.rank → ℤ) ![a, b, a', b'] β' = b' := by
    simpa using imageCoeff_apply hν ![a, b, a', b'] (3 : Fin 4)
  have f0 : imageCoeff (![α, β, α', β'] : Fin 4 → Fin τ.rank → ℤ) ![a, b, -a', -b'] α = a := by
    simpa using imageCoeff_apply hν ![a, b, -a', -b'] (0 : Fin 4)
  have f1 : imageCoeff (![α, β, α', β'] : Fin 4 → Fin τ.rank → ℤ) ![a, b, -a', -b'] β = b := by
    simpa using imageCoeff_apply hν ![a, b, -a', -b'] (1 : Fin 4)
  have f2 : imageCoeff (![α, β, α', β'] : Fin 4 → Fin τ.rank → ℤ) ![a, b, -a', -b'] α' = -a' := by
    simpa using imageCoeff_apply hν ![a, b, -a', -b'] (2 : Fin 4)
  have f3 : imageCoeff (![α, β, α', β'] : Fin 4 → Fin τ.rank → ℤ) ![a, b, -a', -b'] β' = -b' := by
    simpa using imageCoeff_apply hν ![a, b, -a', -b'] (3 : Fin 4)
  constructor
  · intro hroot
    have hηk : γ + δ ∈ kernelRoots χ := ⟨hroot, by
      rw [ofAdd_add, map_mul, hγk.2, hδk.2, one_mul]⟩
    have hfix : rootReflection δ • γ = γ :=
      rootReflection_smul_of_iform_eq_zero hδk.1 (by rw [iform_comm]; exact horthγδ)
    have hnegδ : rootReflection δ • δ = -δ := rootReflection_smul_self hδk.1
    have hη'k : γ - δ ∈ kernelRoots χ := by
      have hmap : rootReflection δ • (γ + δ) = γ - δ := by
        rw [smul_add, hfix, hnegδ, sub_eq_add_neg]
      rw [← hmap]
      exact smul_mem_kernelRoots (rootReflection_mem_charStabilizer hδk) hηk
    have hsign1 : (0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ a' ∧ 0 ≤ b') ∨
        (a ≤ 0 ∧ b ≤ 0 ∧ a' ≤ 0 ∧ b' ≤ 0) := by
      rcases IsRoot.height_pos_or_neg hroot with hpos | hneg
      · left
        have hc := coords_nonneg_of_mem_posRoots_kernel
          (η := γ + δ) ⟨hηk, hpos⟩ hγδexp
        have h0 := hc α hα
        have h1 := hc β hβ
        have h2 := hc α' hα'
        have h3 := hc β' hβ'
        rw [e0] at h0
        rw [e1] at h1
        rw [e2] at h2
        rw [e3] at h3
        exact ⟨h0, h1, h2, h3⟩
      · right
        have hneg' : γ + δ ∈ negRoots (kernelRoots χ) :=
          ⟨⟨IsRoot.neg hηk.1, chi_neg hηk.2⟩, by rw [height_neg]; omega⟩
        have hc := coords_nonpos_of_mem_negRoots_kernel hneg' hγδexp
        have h0 := hc α hα
        have h1 := hc β hβ
        have h2 := hc α' hα'
        have h3 := hc β' hβ'
        rw [e0] at h0
        rw [e1] at h1
        rw [e2] at h2
        rw [e3] at h3
        exact ⟨h0, h1, h2, h3⟩
    have hsign2 : (0 ≤ a ∧ 0 ≤ b ∧ a' ≤ 0 ∧ b' ≤ 0) ∨
        (a ≤ 0 ∧ b ≤ 0 ∧ 0 ≤ a' ∧ 0 ≤ b') := by
      rcases IsRoot.height_pos_or_neg hη'k.1 with hpos | hneg
      · left
        have hc := coords_nonneg_of_mem_posRoots_kernel
          (η := γ - δ) ⟨hη'k, hpos⟩ hγδ'exp
        have h0 := hc α hα
        have h1 := hc β hβ
        have h2 := hc α' hα'
        have h3 := hc β' hβ'
        rw [f0] at h0
        rw [f1] at h1
        rw [f2] at h2
        rw [f3] at h3
        exact ⟨h0, h1, by omega, by omega⟩
      · right
        have hneg' : γ - δ ∈ negRoots (kernelRoots χ) :=
          ⟨⟨IsRoot.neg hη'k.1, chi_neg hη'k.2⟩, by rw [height_neg]; omega⟩
        have hc := coords_nonpos_of_mem_negRoots_kernel hneg' hγδ'exp
        have h0 := hc α hα
        have h1 := hc β hβ
        have h2 := hc α' hα'
        have h3 := hc β' hβ'
        rw [f0] at h0
        rw [f1] at h1
        rw [f2] at h2
        rw [f3] at h3
        exact ⟨h0, h1, by omega, by omega⟩
    have hzero : (a = 0 ∧ b = 0) ∨ (a' = 0 ∧ b' = 0) := by
      rcases hsign1 with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ <;>
        rcases hsign2 with ⟨k1, k2, k3, k4⟩ | ⟨k1, k2, k3, k4⟩ <;> omega
    rcases hzero with ⟨ha0, hb0⟩ | ⟨ha'0, hb'0⟩
    · rcases hab with h | h
      · exact h ha0
      · exact h hb0
    · rcases ha'b' with h | h
      · exact h ha'0
      · exact h hb'0
  · intro heq
    have hzero : γ + δ = 0 := by rw [heq]; abel
    have hsumc : ∑ x ∈ simpleRoots (kernelRoots χ),
        imageCoeff (![α, β, α', β'] : Fin 4 → Fin τ.rank → ℤ) ![a, b, a', b'] x • x =
        ∑ x ∈ simpleRoots (kernelRoots χ),
        (0 : (Fin τ.rank → ℤ) → ℤ) x • x := by
      rw [← hγδexp, hzero]
      simp
    have hcu := coords_unique_kernel hsumc
    have ha0 : a = 0 := by
      have h := hcu α hα
      rwa [e0, show (0 : (Fin τ.rank → ℤ) → ℤ) α = 0 from rfl] at h
    exact hab.elim (fun h => h ha0) (fun h => h (by
      have h' := hcu β hβ
      rwa [e1, show (0 : (Fin τ.rank → ℤ) → ℤ) β = 0 from rfl] at h'))

end CFSG.HardMathSupport.C14Idx
