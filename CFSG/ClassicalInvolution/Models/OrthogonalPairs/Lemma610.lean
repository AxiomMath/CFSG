module

public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Triple
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Pairs
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Planes

public section

namespace CFSG.ClassicalInvolution.Models.OrthogonalPairs

open QuadraticMap Matrix CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] def negSpace (i : V ≃ₗ[K] V) : Submodule K V :=
  Module.End.eigenspace (i : Module.End K V) (-1)

@[expose] def posSpace (i : V ≃ₗ[K] V) : Submodule K V :=
  Module.End.eigenspace (i : Module.End K V) 1

theorem negSpace_La_neg_one (h2 : (2 : K) ≠ 0) (F : Frame Q) :
    negSpace (F.La (-1)) = F.span :=
  Frame.eigenspace_neg_one_La_neg_one h2 F

theorem posSpace_La_neg_one (h2 : (2 : K) ≠ 0) (F : Frame Q) :
    posSpace (F.La (-1)) = F.perp :=
  Frame.eigenspace_one_La_neg_one h2 F

namespace Frame

variable [FiniteDimensional K V] {F₁ F₂ : Frame Q}

theorem finrank_sup_of_disjoint {A B : Submodule K V} (hd : Disjoint A B) :
    Module.finrank K ↥(A ⊔ B) = Module.finrank K A + Module.finrank K B := by
  have := Submodule.finrank_sup_add_finrank_inf_eq A B
  rw [hd.eq_bot, finrank_bot] at this
  omega

theorem finrank_span_inf_perp (h2 : (2 : K) ≠ 0)
    (hc : F₂.La (-1) * F₁.La (-1) = F₁.La (-1) * F₂.La (-1))
    (h : Module.finrank K ↥(F₁.span ⊓ F₂.span) = 2) :
    Module.finrank K ↥(F₁.span ⊓ F₂.perp) = 2 := by
  have hd : Disjoint (F₁.span ⊓ F₂.perp) (F₁.span ⊓ F₂.span) := by
    rw [Submodule.disjoint_def]
    rintro x ⟨-, hx1⟩ ⟨-, hx2⟩
    exact Submodule.disjoint_def.mp (isCompl_span_perp F₂).disjoint x hx2 hx1
  have h3 := finrank_sup_of_disjoint hd
  rw [← span_eq_sup h2 hc, finrank_span, h] at h3
  omega

theorem finrank_perp_inf_span (h2 : (2 : K) ≠ 0)
    (hc : F₂.La (-1) * F₁.La (-1) = F₁.La (-1) * F₂.La (-1))
    (h : Module.finrank K ↥(F₁.span ⊓ F₂.span) = 2) :
    Module.finrank K ↥(F₁.perp ⊓ F₂.span) = 2 := by
  have hd : Disjoint (F₁.span ⊓ F₂.span) (F₁.perp ⊓ F₂.span) := by
    rw [Submodule.disjoint_def]
    rintro x ⟨hx1, -⟩ ⟨hx2, -⟩
    exact Submodule.disjoint_def.mp (isCompl_span_perp F₁).disjoint x hx1 hx2
  have h3 := finrank_sup_of_disjoint hd
  rw [← span_eq_sup' h2 hc, finrank_span, h] at h3
  omega

omit [FiniteDimensional K V] in
theorem polar_eq_zero_of_mem_perp {F : Frame Q} {x y : V} (hx : x ∈ F.span) (hy : y ∈ F.perp) :
    polar Q x y = 0 := by
  obtain ⟨X, rfl⟩ := hx
  rw [polar_comm]
  exact (mem_perp_iff_forall_incl F).mp hy X

omit [FiniteDimensional K V] in
theorem horth₁₂ : ∀ x ∈ F₁.span ⊓ F₂.perp, ∀ y ∈ F₁.span ⊓ F₂.span, polar Q x y = 0 := by
  intro x hx y hy
  rw [polar_comm]
  exact polar_eq_zero_of_mem_perp hy.2 hx.2

omit [FiniteDimensional K V] in
theorem horth₁₃ : ∀ x ∈ F₁.span ⊓ F₂.perp, ∀ y ∈ F₁.perp ⊓ F₂.span, polar Q x y = 0 := by
  intro x hx y hy
  exact polar_eq_zero_of_mem_perp hx.1 hy.1

omit [FiniteDimensional K V] in
theorem horth₂₃ : ∀ x ∈ F₁.span ⊓ F₂.span, ∀ y ∈ F₁.perp ⊓ F₂.span, polar Q x y = 0 := by
  intro x hx y hy
  exact polar_eq_zero_of_mem_perp hx.1 hy.1

omit [FiniteDimensional K V] in
theorem hasSingularVector_iff_of_decomp {F : Frame Q} {U U' : Submodule K V}
    (hspan : F.span = U ⊔ U') (horth : ∀ x ∈ U, ∀ y ∈ U', polar Q x y = 0)
    (hU : Module.finrank K U = 2) (hU' : Module.finrank K U' = 2) :
    HasSingularVector Q U ↔ HasSingularVector Q U' := by
  have horth' : ∀ x ∈ U', ∀ y ∈ U, polar Q x y = 0 := fun x hx y hy => by
    rw [polar_comm]
    exact horth y hy x hx
  have hspan' : F.span = U' ⊔ U := by rw [hspan, sup_comm]
  have hnd : PolarNondegOn Q U := polarNondegOn_of_orth hspan horth
  have hnd' : PolarNondegOn Q U' := polarNondegOn_of_orth hspan' horth'
  exact ⟨hasSingularVector_of_complement hspan' horth' hnd hU,
    hasSingularVector_of_complement hspan horth hnd' hU'⟩

omit [FiniteDimensional K V] in
theorem polarNondegOn_U₁ (h2 : (2 : K) ≠ 0)
    (hc : F₂.La (-1) * F₁.La (-1) = F₁.La (-1) * F₂.La (-1)) :
    PolarNondegOn Q (F₁.span ⊓ F₂.perp) :=
  polarNondegOn_of_orth (span_eq_sup h2 hc) horth₁₂

omit [FiniteDimensional K V] in
theorem polarNondegOn_U₂ (h2 : (2 : K) ≠ 0)
    (hc : F₂.La (-1) * F₁.La (-1) = F₁.La (-1) * F₂.La (-1)) :
    PolarNondegOn Q (F₁.span ⊓ F₂.span) :=
  polarNondegOn_of_orth ((span_eq_sup h2 hc).trans (sup_comm _ _)) fun x hx y hy => by
    rw [polar_comm]
    exact horth₁₂ y hy x hx

omit [FiniteDimensional K V] in
theorem polarNondegOn_U₃ (h2 : (2 : K) ≠ 0)
    (hc : F₂.La (-1) * F₁.La (-1) = F₁.La (-1) * F₂.La (-1)) :
    PolarNondegOn Q (F₁.perp ⊓ F₂.span) :=
  polarNondegOn_of_orth ((span_eq_sup' h2 hc).trans (sup_comm _ _)) fun x hx y hy => by
    rw [polar_comm]
    exact horth₂₃ y hy x hx

omit [FiniteDimensional K V] in
theorem orth_of_mem {U U' : Submodule K V} (horth : ∀ x ∈ U, ∀ y ∈ U', polar Q x y = 0)
    {P P' : HypPair Q} (he : P.e ∈ U) (hf : P.f ∈ U) (he' : P'.e ∈ U') (hf' : P'.f ∈ U') :
    P.Orth P' :=
  ⟨horth _ he _ he', horth _ he _ hf', horth _ hf _ he', horth _ hf _ hf'⟩

theorem frame_span_eq {F : Frame Q} {U : Submodule K V} (hle : F.span ≤ U)
    (hfin : Module.finrank K U = 4) : F.span = U := by
  have : FiniteDimensional K U := Module.finite_of_finrank_pos (by omega)
  exact Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_span, hfin])

theorem exists_triple (h2 : (2 : K) ≠ 0)
    (hc : F₂.La (-1) * F₁.La (-1) = F₁.La (-1) * F₂.La (-1))
    (h : Module.finrank K ↥(F₁.span ⊓ F₂.span) = 2)
    (hs : HasSingularVector Q (F₁.span ⊓ F₂.span)) :
    ∃ T : Triple Q, T.frame01.span = F₁.span ∧ T.frame12.span = F₂.span := by
  have h₁ := finrank_span_inf_perp h2 hc h
  have h₃ := finrank_perp_inf_span h2 hc h
  have hsp₁ := span_eq_sup h2 hc
  have hsp₂ := span_eq_sup' h2 hc
  have hs₁ : HasSingularVector Q (F₁.span ⊓ F₂.perp) :=
    (hasSingularVector_iff_of_decomp hsp₁ horth₁₂ h₁ h).mpr hs
  have hs₃ : HasSingularVector Q (F₁.perp ⊓ F₂.span) :=
    (hasSingularVector_iff_of_decomp hsp₂ horth₂₃ h h₃).mp hs
  have nd₁ := polarNondegOn_U₁ h2 hc
  have nd₂ := polarNondegOn_U₂ h2 hc
  have nd₃ := polarNondegOn_U₃ h2 hc
  obtain ⟨Pa, hae, haf, -⟩ := exists_hypPair_of_hasSingularVector nd₁ h₁ hs₁
  obtain ⟨Pb, hbe, hbf, -⟩ := exists_hypPair_of_hasSingularVector nd₂ h hs
  obtain ⟨Pc, hce, hcf, -⟩ := exists_hypPair_of_hasSingularVector nd₃ h₃ hs₃
  refine ⟨⟨Pa, Pb, Pc, orth_of_mem horth₁₂ hae haf hbe hbf, orth_of_mem horth₁₃ hae haf hce hcf,
    orth_of_mem horth₂₃ hbe hbf hce hcf⟩, ?_, ?_⟩
  · refine frame_span_eq ?_ (finrank_span F₁)
    rintro _ ⟨X, rfl⟩
    simp only [Triple.frame01, Frame.incl_apply]
    exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.smul_mem _ _ hae.1) (Submodule.smul_mem _ _ haf.1))
      (Submodule.smul_mem _ _ hbe.1)) (Submodule.smul_mem _ _ hbf.1)
  · refine frame_span_eq ?_ (finrank_span F₂)
    rintro _ ⟨X, rfl⟩
    simp only [Triple.frame12, Frame.incl_apply]
    exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.smul_mem _ _ hbe.2) (Submodule.smul_mem _ _ hbf.2))
      (Submodule.smul_mem _ _ hce.2)) (Submodule.smul_mem _ _ hcf.2)

theorem exists_hom_of_hasSingularVector (h2 : (2 : K) ≠ 0)
    (hc : F₂.La (-1) * F₁.La (-1) = F₁.La (-1) * F₂.La (-1))
    (h : Module.finrank K ↥(F₁.span ⊓ F₂.span) = 2)
    (hs : HasSingularVector Q (F₁.span ⊓ F₂.span)) :
    ∃ θ : SL(3, K) →* (V ≃ₗ[K] V), Function.Injective θ ∧
      θ.range = F₁.La.range ⊔ F₂.La.range ∧
      (B12 K).map θ = F₁.La.range ∧ (B23 K).map θ = F₂.La.range := by
  obtain ⟨T, hT₁, hT₂⟩ := exists_triple h2 hc h hs
  exact T.exists_theta (La_range_eq_or_eq_swap h2 (La_neg_one_eq_of_span_eq hT₁.symm))
    (La_range_eq_or_eq_swap h2 (La_neg_one_eq_of_span_eq hT₂.symm))

theorem hasSingularVector_iff_of_orth {F₃ : Frame Q} (h2 : (2 : K) ≠ 0)
    (hc₁₂ : F₂.La (-1) * F₁.La (-1) = F₁.La (-1) * F₂.La (-1))
    (horth : ∀ X Y, polar Q (F₁.incl X) (F₃.incl Y) = 0)
    (h₁₂ : Module.finrank K ↥(F₁.span ⊓ F₂.span) = 2)
    (h₃₂ : Module.finrank K ↥(F₃.span ⊓ F₂.span) = 2) :
    HasSingularVector Q (F₁.span ⊓ F₂.span) ↔ HasSingularVector Q (F₃.span ⊓ F₂.span) := by
  have hAB : ∀ x ∈ F₁.span ⊓ F₂.span, ∀ y ∈ F₃.span ⊓ F₂.span, polar Q x y = 0 := by
    rintro x ⟨⟨X, rfl⟩, -⟩ y ⟨⟨Y, rfl⟩, -⟩
    exact horth X Y
  have ndA : PolarNondegOn Q (F₁.span ⊓ F₂.span) := polarNondegOn_U₂ h2 hc₁₂
  have hd : Disjoint (F₁.span ⊓ F₂.span) (F₃.span ⊓ F₂.span) := by
    rw [Submodule.disjoint_def]
    intro x hxA hxB
    refine ndA x hxA fun y hy => ?_
    rw [polar_comm]
    exact hAB y hy x hxB
  have hle : (F₁.span ⊓ F₂.span) ⊔ (F₃.span ⊓ F₂.span) ≤ F₂.span :=
    sup_le inf_le_right inf_le_right
  have heq : F₂.span = (F₁.span ⊓ F₂.span) ⊔ (F₃.span ⊓ F₂.span) := by
    refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
    rw [finrank_sup_of_disjoint hd, h₁₂, h₃₂, finrank_span]
  exact hasSingularVector_iff_of_decomp heq hAB h₁₂ h₃₂

end Frame

section Lemma610

variable [Finite K] [FiniteDimensional K V] {L₁ L₂ : Subgroup (V ≃ₗ[K] V)}
  {i₁ i₂ : V ≃ₗ[K] V}

theorem conjSubgroup_eq_of_mem_normalizer {G : Type*} [Group G] {g : G} {N : Subgroup G}
    (hg : g ∈ Subgroup.normalizer (N : Set G)) : conjSubgroup g N = N := by
  ext x
  rw [mem_conjSubgroup]
  exact ((Subgroup.mem_normalizer_iff''.mp hg) x).symm

theorem mem_normalizer_of_conjSubgroup_eq {G : Type*} [Group G] {g : G} {N : Subgroup G}
    (h : conjSubgroup g N = N) : g ∈ Subgroup.normalizer (N : Set G) := by
  rw [Subgroup.mem_normalizer_iff'']
  intro x
  rw [← mem_conjSubgroup, h]

omit [Finite K] [FiniteDimensional K V] in
theorem exists_ne_of_not_mem_centralizer {F : Frame Q} {g : V ≃ₗ[K] V}
    (hg : g ∉ Subgroup.centralizer (F.La.range : Set (V ≃ₗ[K] V))) :
    ∃ A : SL(2, K), g * F.La A ≠ F.La A * g := by
  by_contra hcon
  apply hg
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨A, rfl⟩
  by_contra hne
  exact hcon ⟨A, fun h => hne h.symm⟩

theorem lemma_6_10_third (hodd : Odd (Nat.card K)) (h₁ : IsFundamental Q L₁ i₁)
    (h₂ : IsFundamental Q L₂ i₂) (hc : i₁ * i₂ = i₂ * i₁)
    (hN : i₂ ∈ Subgroup.normalizer (L₁ : Set (V ≃ₗ[K] V)))
    (hC : i₂ ∉ Subgroup.centralizer (L₁ : Set (V ≃ₗ[K] V)))
    (hs : HasSingularVector Q (negSpace i₁ ⊓ negSpace i₂)) :
    ∃ L₃ : Subgroup (V ≃ₗ[K] V), IsFundamental Q L₃ (i₁ * i₂) ∧ L₃ ≤ L₁ ⊔ L₂ := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  have h₁' := h₁
  have h₂' := h₂
  obtain ⟨F₁, rfl, rfl⟩ := h₁
  obtain ⟨F₂, rfl, rfl⟩ := h₂
  have hdim := Frame.finrank_inf_span_eq_two h2 hc.symm (conjSubgroup_eq_of_mem_normalizer hN)
    (exists_ne_of_not_mem_centralizer hC)
  rw [negSpace_La_neg_one h2, negSpace_La_neg_one h2] at hs
  obtain ⟨T, hT₁, hT₂⟩ := Frame.exists_triple h2 hc.symm hdim hs
  obtain ⟨T', e1, e2⟩ := T.exists_triple_theta
    (Frame.La_range_eq_or_eq_swap h2 (Frame.La_neg_one_eq_of_span_eq hT₁.symm))
    (Frame.La_range_eq_or_eq_swap h2 (Frame.La_neg_one_eq_of_span_eq hT₂.symm))
  rw [T'.map_B12] at e1
  rw [T'.map_B23] at e2
  have hi₁ : F₁.La (-1) = T'.frame01.swap.La (-1) :=
    IsFundamental.involution_unique hodd h₁' (e1 ▸ IsFundamental.of_frame T'.frame01.swap)
  have hi₂ : F₂.La (-1) = T'.frame12.swap.La (-1) :=
    IsFundamental.involution_unique hodd h₂' (e2 ▸ IsFundamental.of_frame T'.frame12.swap)
  refine ⟨T'.frame02.swap.La.range, ⟨T'.frame02.swap, rfl, ?_⟩, ?_⟩
  · rw [hi₁, hi₂, T'.La_neg_one_mul_eq]
  · rw [← e1, ← e2, ← T'.range_theta]
    exact T'.La_range_le_range_theta

omit [FiniteDimensional K V] in
theorem mem_normalizer_iff_even (hodd : Odd (Nat.card K)) (h₁ : IsFundamental Q L₁ i₁)
    (h₂ : IsFundamental Q L₂ i₂) (hc : i₁ * i₂ = i₂ * i₁) :
    i₂ ∈ Subgroup.normalizer (L₁ : Set (V ≃ₗ[K] V)) ↔
      Even (Module.finrank K ↥(negSpace i₁ ⊓ negSpace i₂)) := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  obtain ⟨F₁, rfl, rfl⟩ := h₁
  obtain ⟨F₂, rfl, rfl⟩ := h₂
  rw [negSpace_La_neg_one h2, negSpace_La_neg_one h2, ← Frame.conjSubgroup_eq_iff_even h2 hc.symm]
  exact ⟨conjSubgroup_eq_of_mem_normalizer, mem_normalizer_of_conjSubgroup_eq⟩

omit [FiniteDimensional K V] in
theorem finrank_inf_negSpace (hodd : Odd (Nat.card K)) (h₁ : IsFundamental Q L₁ i₁)
    (h₂ : IsFundamental Q L₂ i₂) (hc : i₁ * i₂ = i₂ * i₁)
    (hN : i₂ ∈ Subgroup.normalizer (L₁ : Set (V ≃ₗ[K] V)))
    (hC : i₂ ∉ Subgroup.centralizer (L₁ : Set (V ≃ₗ[K] V))) :
    Module.finrank K ↥(negSpace i₁ ⊓ negSpace i₂) = 2 := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  obtain ⟨F₁, rfl, rfl⟩ := h₁
  obtain ⟨F₂, rfl, rfl⟩ := h₂
  rw [negSpace_La_neg_one h2, negSpace_La_neg_one h2]
  exact Frame.finrank_inf_span_eq_two h2 hc.symm (conjSubgroup_eq_of_mem_normalizer hN)
    (exists_ne_of_not_mem_centralizer hC)

variable (Q) in
structure PairDecomposition (i₁ i₂ : V ≃ₗ[K] V) : Prop where
  finrank_U₁ : Module.finrank K ↥(negSpace i₁ ⊓ posSpace i₂) = 2
  finrank_U₂ : Module.finrank K ↥(negSpace i₁ ⊓ negSpace i₂) = 2
  finrank_U₃ : Module.finrank K ↥(posSpace i₁ ⊓ negSpace i₂) = 2
  negSpace_i₁ : negSpace i₁ = (negSpace i₁ ⊓ posSpace i₂) ⊔ (negSpace i₁ ⊓ negSpace i₂)
  negSpace_i₂ : negSpace i₂ = (negSpace i₁ ⊓ negSpace i₂) ⊔ (posSpace i₁ ⊓ negSpace i₂)
  orth₁₂ : ∀ x ∈ negSpace i₁ ⊓ posSpace i₂, ∀ y ∈ negSpace i₁ ⊓ negSpace i₂, polar Q x y = 0
  orth₁₃ : ∀ x ∈ negSpace i₁ ⊓ posSpace i₂, ∀ y ∈ posSpace i₁ ⊓ negSpace i₂, polar Q x y = 0
  orth₂₃ : ∀ x ∈ negSpace i₁ ⊓ negSpace i₂, ∀ y ∈ posSpace i₁ ⊓ negSpace i₂, polar Q x y = 0
  nondeg₁ : PolarNondegOn Q (negSpace i₁ ⊓ posSpace i₂)
  nondeg₂ : PolarNondegOn Q (negSpace i₁ ⊓ negSpace i₂)
  nondeg₃ : PolarNondegOn Q (posSpace i₁ ⊓ negSpace i₂)
  type₁₂ : HasSingularVector Q (negSpace i₁ ⊓ posSpace i₂) ↔
    HasSingularVector Q (negSpace i₁ ⊓ negSpace i₂)
  type₂₃ : HasSingularVector Q (negSpace i₁ ⊓ negSpace i₂) ↔
    HasSingularVector Q (posSpace i₁ ⊓ negSpace i₂)

omit [Finite K] in
theorem Frame.pairDecomposition (h2 : (2 : K) ≠ 0) {F₁ F₂ : Frame Q}
    (hc : F₂.La (-1) * F₁.La (-1) = F₁.La (-1) * F₂.La (-1))
    (h : Module.finrank K ↥(F₁.span ⊓ F₂.span) = 2) :
    PairDecomposition Q (F₁.La (-1)) (F₂.La (-1)) := by
  have h₁ := Frame.finrank_span_inf_perp h2 hc h
  have h₃ := Frame.finrank_perp_inf_span h2 hc h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  try simp only [negSpace_La_neg_one h2, posSpace_La_neg_one h2]
  · rw [negSpace_La_neg_one h2, posSpace_La_neg_one h2]
    exact h₁
  · rw [negSpace_La_neg_one h2, negSpace_La_neg_one h2]
    exact h
  · rw [posSpace_La_neg_one h2, negSpace_La_neg_one h2]
    exact h₃
  · exact Frame.span_eq_sup h2 hc
  · exact Frame.span_eq_sup' h2 hc
  · exact Frame.horth₁₂
  · exact Frame.horth₁₃
  · exact Frame.horth₂₃
  · exact Frame.polarNondegOn_U₁ h2 hc
  · exact Frame.polarNondegOn_U₂ h2 hc
  · exact Frame.polarNondegOn_U₃ h2 hc
  · exact Frame.hasSingularVector_iff_of_decomp (Frame.span_eq_sup h2 hc) Frame.horth₁₂ h₁ h
  · exact Frame.hasSingularVector_iff_of_decomp (Frame.span_eq_sup' h2 hc) Frame.horth₂₃ h h₃

theorem lemma_6_10 (hodd : Odd (Nat.card K)) (h₁ : IsFundamental Q L₁ i₁)
    (h₂ : IsFundamental Q L₂ i₂) (hc : i₁ * i₂ = i₂ * i₁)
    (hN : i₂ ∈ Subgroup.normalizer (L₁ : Set (V ≃ₗ[K] V)))
    (hC : i₂ ∉ Subgroup.centralizer (L₁ : Set (V ≃ₗ[K] V))) :
    PairDecomposition Q i₁ i₂ ∧
      (HasSingularVector Q (negSpace i₁ ⊓ negSpace i₂) →
        LinearBlockStandardPair K (L₁ ⊔ L₂) L₁ L₂) := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  obtain ⟨F₁, rfl, rfl⟩ := h₁
  obtain ⟨F₂, rfl, rfl⟩ := h₂
  have hdim := Frame.finrank_inf_span_eq_two h2 hc.symm (conjSubgroup_eq_of_mem_normalizer hN)
    (exists_ne_of_not_mem_centralizer hC)
  refine ⟨Frame.pairDecomposition h2 hc.symm hdim, fun hs => ?_⟩
  rw [negSpace_La_neg_one h2, negSpace_La_neg_one h2] at hs
  obtain ⟨θ, hinj, hrange, hU, hV⟩ := Frame.exists_hom_of_hasSingularVector h2 hc.symm hdim hs
  exact linearBlockStandardPair_of_normalized
    (by rw [(MonoidHom.ker_eq_bot_iff θ).mpr hinj]; exact bot_le) hrange hU hV

theorem lemma_6_11 {L₃ : Subgroup (V ≃ₗ[K] V)} {i₃ : V ≃ₗ[K] V} (hodd : Odd (Nat.card K))
    (h₁ : IsFundamental Q L₁ i₁) (h₂ : IsFundamental Q L₂ i₂) (h₃ : IsFundamental Q L₃ i₃)
    (h₁₂ : i₁ * i₂ = i₂ * i₁) (h₃₂ : i₃ * i₂ = i₂ * i₃) (h₁₃ : i₁ * i₃ = i₃ * i₁)
    (hK : ∀ x ∈ L₁, ∀ y ∈ L₃, x * y = y * x)
    (hN₁ : i₂ ∈ Subgroup.normalizer (L₁ : Set (V ≃ₗ[K] V)))
    (hN₃ : i₂ ∈ Subgroup.normalizer (L₃ : Set (V ≃ₗ[K] V)))
    (hC₁ : i₂ ∉ Subgroup.centralizer (L₁ : Set (V ≃ₗ[K] V)))
    (hC₃ : i₂ ∉ Subgroup.centralizer (L₃ : Set (V ≃ₗ[K] V))) :
    HasSingularVector Q (negSpace i₁ ⊓ negSpace i₂) ↔
      HasSingularVector Q (negSpace i₂ ⊓ negSpace i₃) := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  have hd₁ := finrank_inf_negSpace hodd h₁ h₂ h₁₂ hN₁ hC₁
  have hd₃ := finrank_inf_negSpace hodd h₃ h₂ h₃₂ hN₃ hC₃
  by_cases hi : i₃ = i₁
  · subst hi
    rw [inf_comm]
  · obtain ⟨F₁, rfl, rfl⟩ := h₁
    obtain ⟨F₂, rfl, rfl⟩ := h₂
    obtain ⟨F₃, rfl, rfl⟩ := h₃
    rw [negSpace_La_neg_one h2, negSpace_La_neg_one h2] at hd₁ hd₃
    rw [negSpace_La_neg_one h2, negSpace_La_neg_one h2, negSpace_La_neg_one h2,
      inf_comm F₂.span F₃.span]
    have hcent : ∀ A : SL(2, K), F₃.La (-1) * F₁.La A = F₁.La A * F₃.La (-1) := fun A =>
      (hK _ ⟨A, rfl⟩ _ ⟨-1, rfl⟩).symm
    have horth := (Frame.orth_or_eq h2 h₁₃.symm hcent).resolve_right hi
    exact Frame.hasSingularVector_iff_of_orth h2 h₁₂.symm horth hd₁ hd₃

omit [Finite K] in
theorem linearBlockStandardPair_subgroupOf {X : Type} [Group X] {W U V : Subgroup X}
    (H : Subgroup X) (hW : W ≤ H) (h : LinearBlockStandardPair K W U V) :
    LinearBlockStandardPair K (W.subgroupOf H) (U.subgroupOf H) (V.subgroupOf H) := by
  obtain ⟨θ, c, hrange, hker, h'⟩ := h
  have hθ : ∀ g, θ g ∈ H := fun g => hW (hrange ▸ ⟨g, rfl⟩)
  let θ' : SL(3, K) →* H := θ.codRestrict H hθ
  have hsub : ∀ S : Subgroup SL(3, K), S.map θ ≤ W := fun S => by
    rintro _ ⟨g, -, rfl⟩
    exact hrange ▸ ⟨g, rfl⟩
  have hmap : ∀ (S : Subgroup SL(3, K)) (T : Subgroup X), S.map θ = T → S.map θ' = T.subgroupOf H :=
    fun S T hST => by
      have hTH : T ≤ H := hST ▸ (hsub S).trans hW
      refine Subgroup.map_injective (f := H.subtype) Subtype.val_injective ?_
      rw [Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hTH, ← hST]
      rfl
  refine ⟨θ', c, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_eq_map]
    exact hmap ⊤ W (by rw [← MonoidHom.range_eq_map]; exact hrange)
  · rwa [MonoidHom.ker_codRestrict]
  · rcases h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨hmap _ _ h1, hmap _ _ h2⟩
    · exact Or.inr ⟨hmap _ _ h1, hmap _ _ h2⟩

theorem lemma_6_10_subgroupOf (hodd : Odd (Nat.card K)) (h₁ : IsFundamental Q L₁ i₁)
    (h₂ : IsFundamental Q L₂ i₂) (hc : i₁ * i₂ = i₂ * i₁)
    (hN : i₂ ∈ Subgroup.normalizer (L₁ : Set (V ≃ₗ[K] V)))
    (hC : i₂ ∉ Subgroup.centralizer (L₁ : Set (V ≃ₗ[K] V)))
    (hs : HasSingularVector Q (negSpace i₁ ⊓ negSpace i₂)) :
    LinearBlockStandardPair K ((L₁ ⊔ L₂).subgroupOf (elementaryGroup Q))
      (L₁.subgroupOf (elementaryGroup Q)) (L₂.subgroupOf (elementaryGroup Q)) :=
  linearBlockStandardPair_subgroupOf (elementaryGroup Q)
    (sup_le h₁.le_elementaryGroup h₂.le_elementaryGroup)
    ((lemma_6_10 hodd h₁ h₂ hc hN hC).2 hs)

omit [Finite K] [FiniteDimensional K V] in
theorem PairDecomposition.not_hasSingularVector {i₁ i₂ : V ≃ₗ[K] V}
    (hP : PairDecomposition Q i₁ i₂) (hs : ¬ HasSingularVector Q (negSpace i₁ ⊓ negSpace i₂)) :
    ¬ HasSingularVector Q (negSpace i₁ ⊓ posSpace i₂) ∧
      ¬ HasSingularVector Q (posSpace i₁ ⊓ negSpace i₂) :=
  ⟨fun h => hs (hP.type₁₂.mp h), fun h => hs (hP.type₂₃.mpr h)⟩

omit [FiniteDimensional K V] in
theorem sup_fixes_posSpace {i₁ i₂ : V ≃ₗ[K] V} (hodd : Odd (Nat.card K))
    (h₁ : IsFundamental Q L₁ i₁) (h₂ : IsFundamental Q L₂ i₂) {g : V ≃ₗ[K] V}
    (hg : g ∈ L₁ ⊔ L₂) {x : V} (hx : x ∈ posSpace i₁ ⊓ posSpace i₂) : g x = x := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  obtain ⟨F₁, rfl, rfl⟩ := h₁
  obtain ⟨F₂, rfl, rfl⟩ := h₂
  rw [posSpace_La_neg_one h2, posSpace_La_neg_one h2] at hx
  have hfix : ∀ F : Frame Q, x ∈ F.perp → F.La.range ≤ MulAction.stabilizer (V ≃ₗ[K] V) x := by
    intro F hF
    rintro _ ⟨A, rfl⟩
    rw [MulAction.mem_stabilizer_iff]
    exact F.La_apply_of_coords_eq_zero A ((Frame.mem_perp_iff F).mp hF)
  have := sup_le (hfix F₁ hx.1) (hfix F₂ hx.2) hg
  rwa [MulAction.mem_stabilizer_iff] at this

omit [Finite K] [FiniteDimensional K V] in
theorem negSpace_neg_mul (i : V ≃ₗ[K] V) : negSpace (LinearEquiv.neg K * i) = posSpace i := by
  ext x
  simp only [negSpace, posSpace, Module.End.mem_eigenspace_iff, neg_smul, one_smul]
  exact neg_inj

omit [FiniteDimensional K V] in
theorem ncard_isFundamental_le_two (hodd : Odd (Nat.card K)) (j : V ≃ₗ[K] V) :
    {L' : Subgroup (V ≃ₗ[K] V) | IsFundamental Q L' j}.ncard ≤ 2 := by
  by_cases h : ∃ L, IsFundamental Q L j
  · obtain ⟨L, hL⟩ := h
    exact (IsFundamental.ncard_eq_two hodd hL).le
  · have : {L' : Subgroup (V ≃ₗ[K] V) | IsFundamental Q L' j} = ∅ := by
      ext L'
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h' => h ⟨L', h'⟩
    rw [this]
    simp

omit [FiniteDimensional K V] in
theorem ncard_isFundamental_pm_le_four (hodd : Odd (Nat.card K)) (i : V ≃ₗ[K] V) :
    {L' : Subgroup (V ≃ₗ[K] V) |
      IsFundamental Q L' i ∨ IsFundamental Q L' (LinearEquiv.neg K * i)}.ncard ≤ 4 := by
  have h := Set.ncard_union_le {L' : Subgroup (V ≃ₗ[K] V) | IsFundamental Q L' i}
    {L' : Subgroup (V ≃ₗ[K] V) | IsFundamental Q L' (LinearEquiv.neg K * i)}
  have h1 := ncard_isFundamental_le_two (Q := Q) hodd i
  have h2 := ncard_isFundamental_le_two (Q := Q) hodd (LinearEquiv.neg K * i)
  have e : {L' : Subgroup (V ≃ₗ[K] V) |
      IsFundamental Q L' i ∨ IsFundamental Q L' (LinearEquiv.neg K * i)} =
      {L' : Subgroup (V ≃ₗ[K] V) | IsFundamental Q L' i} ∪
        {L' : Subgroup (V ≃ₗ[K] V) | IsFundamental Q L' (LinearEquiv.neg K * i)} := rfl
  rw [e]
  omega

theorem ncard_isFundamental_pm_eq_two (hodd : Odd (Nat.card K)) {L : Subgroup (V ≃ₗ[K] V)}
    {i : V ≃ₗ[K] V} (h : IsFundamental Q L i) (hdim : Module.finrank K V ≠ 8) :
    {L' : Subgroup (V ≃ₗ[K] V) |
      IsFundamental Q L' i ∨ IsFundamental Q L' (LinearEquiv.neg K * i)}.ncard = 2 := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  have hno : ∀ L', ¬ IsFundamental Q L' (LinearEquiv.neg K * i) := by
    rintro L' ⟨F', -, hF'⟩
    obtain ⟨F, rfl, rfl⟩ := h
    have h1 : F.perp = F'.span := by
      rw [← posSpace_La_neg_one h2, ← negSpace_neg_mul, hF', negSpace_La_neg_one h2]
    have h3 := Submodule.finrank_add_eq_of_isCompl (Frame.isCompl_span_perp F)
    rw [h1, Frame.finrank_span, Frame.finrank_span] at h3
    exact hdim (by omega)
  have e : {L' : Subgroup (V ≃ₗ[K] V) |
      IsFundamental Q L' i ∨ IsFundamental Q L' (LinearEquiv.neg K * i)} =
      {L' : Subgroup (V ≃ₗ[K] V) | IsFundamental Q L' i} := by
    ext L'
    simp only [Set.mem_ofPred_eq]
    exact ⟨fun h' => h'.resolve_right (hno L'), Or.inl⟩
  rw [e]
  exact IsFundamental.ncard_eq_two hodd h

end Lemma610

end CFSG.ClassicalInvolution.Models.OrthogonalPairs
