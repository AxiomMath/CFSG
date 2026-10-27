module

public import CFSG.LieType.HighestRoot.CentChevalleyThree
public import CFSG.LieType.HighestRoot.CentChevalleyPerm
public import CFSG.LieType.Steinberg.TwistedD4.Defs

public section

namespace CFSG.LieType.HighestRoot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.TwistedD4 CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

abbrev t4c : Fin d4.rank → ℤ := Pi.single (nd 2) 1

abbrev t4b0 : Fin d4.rank → ℤ := ![0, 1, 1, 1]

abbrev t4b1 : Fin d4.rank → ℤ := ![1, 0, 1, 1]

abbrev t4b3 : Fin d4.rank → ℤ := ![1, 1, 1, 0]

abbrev IsT4Outer (β : Fin d4.rank → ℤ) : Prop := β = t4b0 ∨ β = t4b1 ∨ β = t4b3

abbrev IsT4Frame (β : Fin d4.rank → ℤ) : Prop := β = t4c ∨ IsT4Outer β

theorem isRoot_t4b0 : IsRoot d4 t4b0 :=
  (RootCertificate.isRoot_iff (Tag.rootCertificate_check d4)).2 ⟨15, by decide, by decide⟩

theorem isRoot_t4b1 : IsRoot d4 t4b1 :=
  (RootCertificate.isRoot_iff (Tag.rootCertificate_check d4)).2 ⟨13, by decide, by decide⟩

theorem isRoot_t4b3 : IsRoot d4 t4b3 :=
  (RootCertificate.isRoot_iff (Tag.rootCertificate_check d4)).2 ⟨12, by decide, by decide⟩

theorem isRoot_of_isT4Frame
    {β : Fin d4.rank → ℤ} (hβ : IsT4Frame β) : IsRoot d4 β := by
  rcases hβ with rfl | rfl | rfl | rfl
  exacts [isRoot_single _ _, isRoot_t4b0, isRoot_t4b1, isRoot_t4b3]

theorem rho_t4c : rho t4c = t4c := by rw [rho_single, rhoPerm_two]

theorem rho_t4b0 : rho t4b0 = t4b1 := by decide

theorem rho_t4b1 : rho t4b1 = t4b3 := by decide

theorem rho_t4b3 : rho t4b3 = t4b0 := by decide

theorem isT4Outer_rho {β : Fin d4.rank → ℤ} (hβ : IsT4Outer β) : IsT4Outer (rho β) := by
  rcases hβ with rfl | rfl | rfl
  · exact Or.inr (Or.inl rho_t4b0)
  · exact Or.inr (Or.inr rho_t4b1)
  · exact Or.inl rho_t4b3

theorem rho_ne_of_isT4Outer {β : Fin d4.rank → ℤ} (hβ : IsT4Outer β) : rho β ≠ β := by
  rcases hβ with rfl | rfl | rfl
  · rw [rho_t4b0]; decide
  · rw [rho_t4b1]; decide
  · rw [rho_t4b3]; decide

theorem rho_rho_ne_of_isT4Outer {β : Fin d4.rank → ℤ} (hβ : IsT4Outer β) : rho (rho β) ≠ β := by
  rcases hβ with rfl | rfl | rfl
  · rw [rho_t4b0, rho_t4b1]; decide
  · rw [rho_t4b1, rho_t4b3]; decide
  · rw [rho_t4b3, rho_t4b0]; decide

theorem t4_kernel_check : ∀ γ ∈ rootFinset d4, corootPair d4 (nd 2) γ % 2 = 0 →
    γ = t4c ∨ γ = -t4c ∨ γ = t4b0 ∨ γ = -t4b0 ∨ γ = t4b1 ∨ γ = -t4b1 ∨ γ = t4b3 ∨
      γ = -t4b3 := by
  decide +kernel

variable {K : Type} [Field K]

theorem t4_mem_kernel_iff
    (hK : ringChar K ≠ 2) (α : Fin d4.rank → ℤ) :
    α ∈ rootCharKernel (signTuple d4 K (nd 2)) ↔ ∃ β, IsT4Frame β ∧ (α = β ∨ α = -β) := by
  rw [mem_rootCharKernel_signTuple hK]
  constructor
  · rintro ⟨hα, hev⟩
    rcases t4_kernel_check α (mem_rootFinset.2 hα) (Int.even_iff.1 hev) with
      h | h | h | h | h | h | h | h
    · exact ⟨t4c, Or.inl rfl, Or.inl h⟩
    · exact ⟨t4c, Or.inl rfl, Or.inr h⟩
    · exact ⟨t4b0, Or.inr (Or.inl rfl), Or.inl h⟩
    · exact ⟨t4b0, Or.inr (Or.inl rfl), Or.inr h⟩
    · exact ⟨t4b1, Or.inr (Or.inr (Or.inl rfl)), Or.inl h⟩
    · exact ⟨t4b1, Or.inr (Or.inr (Or.inl rfl)), Or.inr h⟩
    · exact ⟨t4b3, Or.inr (Or.inr (Or.inr rfl)), Or.inl h⟩
    · exact ⟨t4b3, Or.inr (Or.inr (Or.inr rfl)), Or.inr h⟩
  · rintro ⟨β, hβ, h | h⟩ <;> subst h
    · refine ⟨isRoot_of_isT4Frame hβ, Int.even_iff.2 ?_⟩
      rcases hβ with rfl | rfl | rfl | rfl <;> decide
    · refine ⟨IsRoot.neg (isRoot_of_isT4Frame hβ), Int.even_iff.2 ?_⟩
      rcases hβ with rfl | rfl | rfl | rfl <;> decide

theorem iform_t4_eq_zero {β β' : Fin d4.rank → ℤ} (hβ : IsT4Frame β) (hβ' : IsT4Frame β')
    (hne : β ≠ β') : iform β β' = 0 := by
  rcases hβ with rfl | rfl | rfl | rfl <;> rcases hβ' with rfl | rfl | rfl | rfl <;>
    first | exact absurd rfl hne | decide

theorem t4_ne_neg {β β' : Fin d4.rank → ℤ} (hβ : IsT4Frame β) (hβ' : IsT4Frame β') :
    β ≠ -β' := by
  rcases hβ with rfl | rfl | rfl | rfl <;> rcases hβ' with rfl | rfl | rfl | rfl <;> decide

theorem iform_self_d4
    {ε : Fin d4.rank → ℤ} (hε : IsRoot d4 ε) : iform ε ε = 2 := by
  obtain ⟨k, hk⟩ := iform_self_of_isRoot hε
  rw [hk, symmetrizer_d4, mul_one]

theorem commute_rootSubgroup_t4
    {β β' : Fin d4.rank → ℤ} (hβ : IsT4Frame β)
    (hβ' : IsT4Frame β') (hne : β' ≠ β) {s : ℤ} (hs : s = 1 ∨ s = -1) :
    ∀ x ∈ rootSubgroup d4 K (s • β'),
      (∀ y ∈ rootSubgroup d4 K β, Commute x y) ∧ ∀ y ∈ rootSubgroup d4 K (-β), Commute x y := by
  have hr' : IsRoot d4 (s • β') := by
    rcases hs with rfl | rfl
    · rw [one_smul]; exact isRoot_of_isT4Frame hβ'
    · rw [neg_one_smul]; exact IsRoot.neg (isRoot_of_isT4Frame hβ')
  have hlong : ∀ ε, IsRoot d4 ε → iform ε ε ≤ iform β β := fun ε hε => by
    rw [iform_self_d4 hε, iform_self_d4 (isRoot_of_isT4Frame hβ)]
  have h0 : iform (s • β') β = 0 := by
    rw [iform_smul_left, iform_t4_eq_zero hβ' hβ hne, mul_zero]
  have hne1 : s • β' ≠ β := by
    rcases hs with rfl | rfl
    · rw [one_smul]; exact hne
    · rw [neg_one_smul]; exact fun h => t4_ne_neg hβ hβ' h.symm
  have hne2 : s • β' ≠ -β := by
    rcases hs with rfl | rfl
    · rw [one_smul]; exact t4_ne_neg hβ' hβ
    · rw [neg_one_smul]; exact fun h => hne (neg_injective h)
  exact commute_pair_of_iform_eq_zero noG2_D4 hr' (isRoot_of_isT4Frame hβ) hlong h0 hne1 hne2

theorem commute_t4
    {β β' : Fin d4.rank → ℤ} (hβ : IsT4Frame β) (hβ' : IsT4Frame β')
    (hne : β' ≠ β) {x y : ModGL d4 K} (hx : x ∈ pairGroup d4 K β') (hy : y ∈ pairGroup d4 K β) :
    Commute x y := by
  have key : ∀ {s : ℤ}, (s = 1 ∨ s = -1) → ∀ u ∈ rootSubgroup d4 K (s • β'), Commute u y := by
    intro s hs u hu
    obtain ⟨h1, h2⟩ := commute_rootSubgroup_t4 hβ hβ' hne hs u hu
    have hle : pairGroup d4 K β ≤ Subgroup.centralizer ({u} : Set (ModGL d4 K)) :=
      sup_le (fun v hv => Subgroup.mem_centralizer_singleton_iff.2 (h1 v hv).eq.symm)
        (fun v hv => Subgroup.mem_centralizer_singleton_iff.2 (h2 v hv).eq.symm)
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hy)).symm
  have hle : pairGroup d4 K β' ≤ Subgroup.centralizer ({y} : Set (ModGL d4 K)) := by
    refine sup_le (fun u hu => Subgroup.mem_centralizer_singleton_iff.2 ?_)
      (fun u hu => Subgroup.mem_centralizer_singleton_iff.2 ?_)
    · exact (key (Or.inl rfl) u (by rwa [one_smul])).eq
    · exact (key (Or.inr rfl) u (by rwa [neg_one_smul])).eq
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hx)

theorem mem_kernelRoots_t4
    (hK : ringChar K ≠ 2) {β : Fin d4.rank → ℤ} (hβ : IsT4Frame β) :
    β ∈ kernelRoots (signChar d4 K (nd 2)) := by
  rw [← rootCharKernel_signTuple_eq hK, t4_mem_kernel_iff hK]
  exact ⟨β, hβ, Or.inl rfl⟩

theorem neg_mem_kernelRoots_t4
    (hK : ringChar K ≠ 2) {β : Fin d4.rank → ℤ} (hβ : IsT4Frame β) :
    -β ∈ kernelRoots (signChar d4 K (nd 2)) := by
  rw [← rootCharKernel_signTuple_eq hK, t4_mem_kernel_iff hK]
  exact ⟨β, hβ, Or.inr rfl⟩

theorem iform_eq_zero_of_mem_kernelRoots_t4
    (hK : ringChar K ≠ 2) {β : Fin d4.rank → ℤ}
    (hβ : IsT4Frame β) {α : Fin d4.rank → ℤ} (hα : α ∈ kernelRoots (signChar d4 K (nd 2)))
    (hne : α ≠ β) (hne' : α ≠ -β) : iform α β = 0 := by
  rw [← rootCharKernel_signTuple_eq hK, t4_mem_kernel_iff hK] at hα
  obtain ⟨β', hβ', rfl | rfl⟩ := hα
  · exact iform_t4_eq_zero hβ' hβ hne
  · have hne'' : β' ≠ β := fun h => hne' (by rw [h])
    rw [← neg_one_smul ℤ β', iform_smul_left, iform_t4_eq_zero hβ' hβ hne'', mul_zero]

theorem componentRootSpan_t4
    (hK : ringChar K ≠ 2) {β : Fin d4.rank → ℤ} (hβ : IsT4Frame β) :
    componentRootSpan K (signChar d4 K (nd 2)) ⟦⟨β, mem_kernelRoots_t4 hK hβ⟩⟧ =
      pairGroup d4 K β := by
  rw [pairGroup, ← rootSpan_pair_eq]
  change rootSpan d4 K (componentRoots (signChar d4 K (nd 2)) _) = _
  congr 1
  ext α
  constructor
  · rintro ⟨hα, hαk⟩
    exact (mem_pair_iff_of_mk_eq_of_iform
      (fun α hα hne hne' => iform_eq_zero_of_mem_kernelRoots_t4 hK hβ hα hne hne') hαk).2
      (Or.inl rfl)
  · rintro (rfl | rfl)
    · exact ⟨mem_kernelRoots_t4 hK hβ, rfl⟩
    · exact ⟨neg_mem_kernelRoots_t4 hK hβ,
        mk_eq_of_iform_ne_zero (iform_neg_self_ne_zero (isRoot_of_isT4Frame hβ))⟩

theorem exists_t4_of_class
    (hK : ringChar K ≠ 2) (k : KernelComponent (signChar d4 K (nd 2))) :
    ∃ β, ∃ hβ : IsT4Frame β, k = ⟦⟨β, mem_kernelRoots_t4 hK hβ⟩⟧ := by
  induction k using Quotient.inductionOn with
  | h α =>
  obtain ⟨α, hα⟩ := α
  have hα' := hα
  rw [← rootCharKernel_signTuple_eq hK, t4_mem_kernel_iff hK] at hα'
  obtain ⟨β, hβ, rfl | rfl⟩ := hα'
  · exact ⟨α, hβ, rfl⟩
  · refine ⟨β, hβ, mk_eq_of_iform_ne_zero ?_⟩
    exact iform_neg_self_ne_zero (isRoot_of_isT4Frame hβ)

end CFSG.LieType.HighestRoot
