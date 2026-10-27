module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7C22E

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Balance

section Const


variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
  {K₀ : Subgroup G} {z : G}

@[expose] def AllFrame3Hyp51 (Ω : Set (Subgroup G)) (z : G) : Prop :=
  ∀ (K₁ K₂ K₃ R₁ R₂ R₃ : Subgroup G) (u₁ u₂ u₃ : G),
    Frame3 Ω z K₁ K₂ K₃ R₁ R₂ R₃ u₁ u₂ u₃ →
      Hyp51 (Subgroup.closure ({z, u₁ * u₂, u₂ * u₃} : Set G))

theorem sup_le_centralizer_of_twins {K K' : Subgroup G} (hz : IsUniqueInvolution K z)
    (hz' : IsUniqueInvolution K' z) :
    K ⊔ K' ≤ Subgroup.centralizer ({z} : Set G) :=
  sup_le (fun _ hk => Subgroup.mem_centralizer_singleton_iff.mpr
      (Hat2A7S8.comm_of_mem_isUniqueInvolution hz hk))
    (fun _ hk => Subgroup.mem_centralizer_singleton_iff.mpr
      (Hat2A7S8.comm_of_mem_isUniqueInvolution hz' hk))

theorem alpha_eq_of_same_members (hs : Pre2A7 Ω K₀) (hall : AllFrame3Hyp51 Ω z)
    {K₁ K₂ K₃ R₁ R₂ R₃ R₁' R₂' R₃' : Subgroup G} {u₁ u₂ u₃ u₁' u₂' u₃' : G}
    (F : Frame3 Ω z K₁ K₂ K₃ R₁ R₂ R₃ u₁ u₂ u₃)
    (F' : Frame3 Ω z K₁ K₂ K₃ R₁' R₂' R₃' u₁' u₂' u₃') :
    alphaOf (Subgroup.closure ({z, u₁ * u₂} : Set G)) =
      alphaOf (Subgroup.closure ({z, u₁' * u₂'} : Set G)) := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  obtain ⟨g, hgK, hg1, hg2⟩ := T7X.exists_conj_sylow_pair hΩ F.mem₁ F.mem₂ F.ne₁₂ F.hz₁ F.hz₂
    F'.syl₁ F'.syl₂ F'.comm₁₂ F.syl₁ F.syl₂ F.comm₁₂
  have hgz : g * z * g⁻¹ = z := by
    have h := Subgroup.mem_centralizer_singleton_iff.mp
      (sup_le_centralizer_of_twins F.hz₁ F.hz₂ hgK)
    rw [h]
    group
  have hgN : g ∈ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({z, u₁ * u₂} : Set G)) : Set G) :=
    (sup_le (F.le_normalizer_alpha₁ hs (hall _ _ _ _ _ _ _ _ _ F))
      (F.le_normalizer_alpha₂ hs (hall _ _ _ _ _ _ _ _ _ F))) hgK
  have hα : alphaOf (Subgroup.closure ({z, (g * u₁ * g⁻¹) * (g * u₂ * g⁻¹)} : Set G)) =
      alphaOf (Subgroup.closure ({z, u₁ * u₂} : Set G)) := by
    have e : (g * u₁ * g⁻¹) * (g * u₂ * g⁻¹) = g * (u₁ * u₂) * g⁻¹ := by group
    rw [e, alphaOf_closure_conj hgz]
    exact mem_normalizer_iff_conjSub_eq.mp hgN
  have hv₁ : g * u₁ * g⁻¹ ∈ R₁' := by
    rw [← hg1]
    exact conj_mem_conjSub F.mem_u₁
  have hv₂ : g * u₂ * g⁻¹ ∈ R₂' := by
    rw [← hg2]
    exact conj_mem_conjSub F.mem_u₂
  have ho₁ : orderOf (g * u₁ * g⁻¹) = 4 := by rw [orderOf_conj_mul_inv_eq]; exact F.ord₁
  have ho₂ : orderOf (g * u₂ * g⁻¹) = 4 := by rw [orderOf_conj_mul_inv_eq]; exact F.ord₂
  have F₂ := F'.withElems hv₁ hv₂ F'.mem_u₃ ho₁ ho₂ F'.ord₃
  have F₃ := F'.withElems F'.mem_u₁ hv₂ F'.mem_u₃ F'.ord₁ ho₂ F'.ord₃
  have e1 := F'.alphaOf_pair₁₃ hΩ (hall _ _ _ _ _ _ _ _ _ F')
  have e2 := F₃.alphaOf_pair₁₃ hΩ (hall _ _ _ _ _ _ _ _ _ F₃)
  have e3 := F₃.alphaOf_pair₂₃ hΩ (hall _ _ _ _ _ _ _ _ _ F₃)
  have e4 := F₂.alphaOf_pair₂₃ hΩ (hall _ _ _ _ _ _ _ _ _ F₂)
  rw [← hα, ← e4, e3, ← e2, e1]

@[expose] def Pr (Ω : Set (Subgroup G)) (z : G) (L L' α : Subgroup G) : Prop :=
  ∃ (M R R' R'' : Subgroup G) (x y w : G), Frame3 Ω z L L' M R R' R'' x y w ∧
    alphaOf (Subgroup.closure ({z, x * y} : Set G)) = α

theorem Pr.mem₁ {L L' α : Subgroup G} (h : Pr Ω z L L' α) : L ∈ Ω := by
  obtain ⟨_, _, _, _, _, _, _, F, _⟩ := h
  exact F.mem₁

theorem Pr.mem₂ {L L' α : Subgroup G} (h : Pr Ω z L L' α) : L' ∈ Ω := by
  obtain ⟨_, _, _, _, _, _, _, F, _⟩ := h
  exact F.mem₂

theorem Pr.hz₁ {L L' α : Subgroup G} (h : Pr Ω z L L' α) : IsUniqueInvolution L z := by
  obtain ⟨_, _, _, _, _, _, _, F, _⟩ := h
  exact F.hz₁

theorem Pr.hz₂ {L L' α : Subgroup G} (h : Pr Ω z L L' α) : IsUniqueInvolution L' z := by
  obtain ⟨_, _, _, _, _, _, _, F, _⟩ := h
  exact F.hz₂

theorem Pr.ne {L L' α : Subgroup G} (h : Pr Ω z L L' α) : L' ≠ L := by
  obtain ⟨_, _, _, _, _, _, _, F, _⟩ := h
  exact F.ne₁₂

theorem Pr.unique (hs : Pre2A7 Ω K₀) (hall : AllFrame3Hyp51 Ω z) {L L' α α' : Subgroup G}
    (h : Pr Ω z L L' α) (h' : Pr Ω z L L' α') : α = α' := by
  obtain ⟨M, R, R', R'', x, y, w, F, rfl⟩ := h
  obtain ⟨M', S, S', S'', x', y', w', F', rfl⟩ := h'
  obtain ⟨T, v, F''⟩ := exists_frame3_extend hs.hyp F.mem₁ F.mem₂ F'.mem₃ F.hz₁ F.hz₂ F'.hz₃
    F.ne₁₂ F'.ne₁₃ F'.ne₂₃ F.syl₁ F.syl₂ F.comm₁₂ F.mem_u₁ F.ord₁ F.mem_u₂ F.ord₂
  exact alpha_eq_of_same_members hs hall F'' F'

theorem Pr.symm {L L' α : Subgroup G} (h : Pr Ω z L L' α) : Pr Ω z L' L α := by
  obtain ⟨M, R, R', R'', x, y, w, F, rfl⟩ := h
  refine ⟨M, R', R, R'', y, x, w, F.swap₁₂, ?_⟩
  rw [F.comm₁₂']

theorem Pr.extend (hs : Pre2A7 Ω K₀) (hall : AllFrame3Hyp51 Ω z) {L L' α M : Subgroup G}
    (h : Pr Ω z L L' α) (hM : M ∈ Ω) (hzM : IsUniqueInvolution M z) (hML : M ≠ L)
    (hML' : M ≠ L') : Pr Ω z L M α := by
  obtain ⟨N, R, R', R'', x, y, w, F, rfl⟩ := h
  obtain ⟨T, v, F''⟩ := exists_frame3_extend hs.hyp F.mem₁ F.mem₂ hM F.hz₁ F.hz₂ hzM F.ne₁₂ hML
    hML' F.syl₁ F.syl₂ F.comm₁₂ F.mem_u₁ F.ord₁ F.mem_u₂ F.ord₂
  exact ⟨L', R, T, R', x, v, y, F''.swap₂₃, F''.alphaOf_pair₁₃ hs.hyp (hall _ _ _ _ _ _ _ _ _ F'')⟩

theorem Pr.global (hs : Pre2A7 Ω K₀) (hall : AllFrame3Hyp51 Ω z) {L₁ L₂ M₁ M₂ α α' : Subgroup G}
    (h : Pr Ω z L₁ L₂ α) (h' : Pr Ω z M₁ M₂ α') : α = α' := by
  by_cases e11 : L₁ = M₁
  · subst e11
    by_cases e22 : L₂ = M₂
    · subst e22
      exact h.unique hs hall h'
    · have h3 := h.extend hs hall h'.mem₂ h'.hz₂ h'.ne (fun e => e22 e.symm)
      exact h3.unique hs hall h'
  · by_cases e12 : L₁ = M₂
    · subst e12
      by_cases e21 : L₂ = M₁
      · subst e21
        exact h.unique hs hall h'.symm
      · have h3 := h.extend hs hall h'.mem₁ h'.hz₁ (fun e => h'.ne e.symm) (fun e => e21 e.symm)
        exact h3.unique hs hall h'.symm
    · by_cases e21 : L₂ = M₁
      · subst e21
        have h3 := h.symm.extend hs hall h'.mem₂ h'.hz₂ h'.ne (fun e => e12 e.symm)
        exact h3.unique hs hall h'
      · by_cases e22 : L₂ = M₂
        · subst e22
          have h3 := h.symm.extend hs hall h'.mem₁ h'.hz₁ (fun e => h'.ne e.symm)
            (fun e => e11 e.symm)
          exact h3.unique hs hall h'.symm
        · have h3 := h.extend hs hall h'.mem₁ h'.hz₁ (fun e => e11 e.symm) (fun e => e21 e.symm)
          have h4 := h3.symm.extend hs hall h'.mem₂ h'.hz₂ h'.ne (fun e => e12 e.symm)
          exact h4.unique hs hall h'

theorem alpha_const (hs : Pre2A7 Ω K₀) (hall : AllFrame3Hyp51 Ω z)
    {K₁ K₂ K₃ R₁ R₂ R₃ K₁' K₂' K₃' R₁' R₂' R₃' : Subgroup G} {u₁ u₂ u₃ u₁' u₂' u₃' : G}
    (F : Frame3 Ω z K₁ K₂ K₃ R₁ R₂ R₃ u₁ u₂ u₃)
    (F' : Frame3 Ω z K₁' K₂' K₃' R₁' R₂' R₃' u₁' u₂' u₃') :
    alphaOf (Subgroup.closure ({z, u₁ * u₂} : Set G)) =
      alphaOf (Subgroup.closure ({z, u₁' * u₂'} : Set G)) :=
  Pr.global hs hall ⟨K₃, R₁, R₂, R₃, u₁, u₂, u₃, F, rfl⟩
    ⟨K₃', R₁', R₂', R₃', u₁', u₂', u₃', F', rfl⟩

end Const

end CFSG.ClassicalInvolution.Hat2A7S
