module

public import CFSG.GroupTheory.SubnormalFamilyNormalizer

public section

namespace CFSG.GroupTheory

open Subgroup

universe u

variable {G : Type u} [Group G]

abbrev familyJoin (T : Set (Subgroup G)) : Subgroup G :=
  Subgroup.closure (⋃ B ∈ T, (B : Set G))

theorem mem_normalizer_familyJoin {T : Set (Subgroup G)} {g : G}
    (hg : ∀ B ∈ T, CFSG.conjugate B g ∈ T) (hg' : ∀ B ∈ T, CFSG.conjugate B g⁻¹ ∈ T) :
    g ∈ Subgroup.normalizer (familyJoin T : Set G) := by
  have hmap : ∀ k : G, (∀ B ∈ T, CFSG.conjugate B k⁻¹ ∈ T) →
      (familyJoin T).map (MulAut.conj k).toMonoidHom ≤ familyJoin T := by
    intro k hk
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨a, ha, rfl⟩
    simp only [Set.mem_iUnion] at ha
    obtain ⟨B, hB, haB⟩ := ha
    apply Subgroup.subset_closure
    simp only [Set.mem_iUnion]
    refine ⟨CFSG.conjugate B k⁻¹, hk B hB, ?_⟩
    change _ ∈ B.map (MulAut.conj k⁻¹⁻¹).toMonoidHom
    rw [inv_inv]
    exact ⟨a, haB, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact hmap g hg' ⟨h, hh, rfl⟩
  · intro hh
    have h1 := hmap g⁻¹ (by simpa using hg) ⟨g * h * g⁻¹, hh, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using h1

variable [Finite G]

theorem exists_mem_normalizer_of_ssubset (K : Subgroup G) (Sig : Set (Subgroup G))
    (hle : ∀ B ∈ Sig, B ≤ K) (hsub : ∀ B ∈ Sig, (B.subgroupOf K).IsSubnormal)
    (hinv : ∀ B ∈ Sig, ∀ g ∈ K, CFSG.conjugate B g ∈ Sig) (Sig₀ : Set (Subgroup G))
    (hSig₀ : Sig₀ ⊂ Sig) :
    ∃ X ∈ Sig \ Sig₀, X ≤ Subgroup.normalizer (familyJoin Sig₀ : Set G) := by
  classical
  let f : Subgroup G → Subgroup K := fun A => A.subgroupOf K
  have hfinv : ∀ A : Subgroup G, A ≤ K → (f A).map K.subtype = A := fun A hA =>
    Subgroup.map_subgroupOf_eq_of_le hA
  set Sig' := f '' Sig with hSig'
  set Sig₀' := f '' Sig₀ with hSig₀'
  have hsub' : ∀ B ∈ Sig', B.IsSubnormal := by
    rintro _ ⟨A, hA, rfl⟩
    exact hsub A hA
  have hinv' : ∀ B ∈ Sig', ∀ g : K, CFSG.conjugate B g ∈ Sig' := by
    rintro _ ⟨A, hA, rfl⟩ g
    have hconj : CFSG.conjugate A g ∈ Sig := hinv A hA g g.2
    have hle' : CFSG.conjugate A g ≤ K := hle _ hconj
    refine ⟨CFSG.conjugate A g, hconj, ?_⟩
    apply Subgroup.map_injective K.subtype_injective
    rw [hfinv _ hle']
    ext z
    simp only [CFSG.conjugate, Subgroup.mem_map, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, Subgroup.coe_subtype]
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨g⁻¹ * ⟨a, hle A hA ha⟩ * g⁻¹⁻¹, ⟨⟨a, hle A hA ha⟩, ?_, rfl⟩, by simp⟩
      simpa [f, Subgroup.mem_subgroupOf] using ha
    · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
      refine ⟨(b : G), ?_, by simp⟩
      simpa [f, Subgroup.mem_subgroupOf] using hb
  have hfinj : Set.InjOn f Sig := by
    intro A hA B hB hAB
    rw [← hfinv A (hle A hA), ← hfinv B (hle B hB), hAB]
  have hproper' : Sig₀' ⊂ Sig' := by
    refine ⟨Set.image_mono hSig₀.1, ?_⟩
    intro hrev
    apply hSig₀.2
    intro A hA
    obtain ⟨B, hB, hBA⟩ := hrev ⟨A, hA, rfl⟩
    rwa [← hfinj (hSig₀.1 hB) hA hBA]
  obtain ⟨X', ⟨hX'S, hX'not⟩, hX'⟩ :=
    invariant_subnormal_family_normalizer_extension Sig' hsub' hinv' Sig₀' hproper'
  obtain ⟨X, hXS, rfl⟩ := hX'S
  refine ⟨X, ⟨hXS, fun hX => hX'not ⟨X, hX, rfl⟩⟩, ?_⟩
  have hLmap : (Subgroup.closure (⋃ B ∈ Sig₀', (B : Set K))).map K.subtype =
      familyJoin Sig₀ := by
    rw [MonoidHom.map_closure]
    congr 1
    ext z
    simp only [Set.mem_image, Set.mem_iUnion, Subgroup.coe_subtype]
    constructor
    · rintro ⟨w, ⟨_, ⟨A, hA, rfl⟩, hw⟩, rfl⟩
      exact ⟨A, hA, by simpa [f, Subgroup.mem_subgroupOf] using hw⟩
    · rintro ⟨A, hA, hz⟩
      have hzK : z ∈ K := hle A (hSig₀.1 hA) hz
      exact ⟨⟨z, hzK⟩, ⟨f A, ⟨A, hA, rfl⟩, by simpa [f, Subgroup.mem_subgroupOf] using hz⟩,
        rfl⟩
  have h := map_subtype_le_normalizer hX'
  rw [hLmap, hfinv X (hle X hXS)] at h
  exact h

theorem subnormal_family_normalizer_unique_maximal_overgroup (𝒰 : Set (Subgroup G))
    (hne : 𝒰.Nonempty) (Sig : Subgroup G → Set (Subgroup G))
    (hle : ∀ U ∈ 𝒰, ∀ B ∈ Sig U, B ≤ U)
    (hsub : ∀ U ∈ 𝒰, ∀ B ∈ Sig U, (B.subgroupOf U).IsSubnormal)
    (hinv : ∀ U ∈ 𝒰, ∀ B ∈ Sig U, ∀ g ∈ U, CFSG.conjugate B g ∈ Sig U)
    (hcompat : ∀ U ∈ 𝒰, ∀ V ∈ 𝒰, ∀ B ∈ Sig V, B ≤ U → B ∈ Sig U)
    (hnorm : ∀ U ∈ 𝒰, ∀ V ∈ 𝒰, ∃ W ∈ 𝒰,
      Subgroup.normalizer
        ((Subgroup.closure (⋃ B ∈ Sig U ∩ Sig V, (B : Set G)) : Subgroup G) : Set G) ≤ W) :
    (∃ M ∈ 𝒰, (∀ U ∈ 𝒰, M ≤ U → U = M) ∧
      (∀ M' ∈ 𝒰, (∀ U ∈ 𝒰, M' ≤ U → U = M') → M' = M) ∧ ∀ U ∈ 𝒰, U ≤ M) ∧
    Subgroup.closure (⋃ B ∈ (∅ : Set (Subgroup G)), (B : Set G)) = ⊥ := by
  classical
  refine ⟨?_, by simp⟩
  have hfin : 𝒰.Finite := Set.toFinite 𝒰
  have hUnorm : ∀ U ∈ 𝒰, U ≤ Subgroup.normalizer (familyJoin (Sig U) : Set G) := fun U hU g hg =>
    mem_normalizer_familyJoin (fun B hB => hinv U hU B hB g hg)
      (fun B hB => hinv U hU B hB g⁻¹ (U.inv_mem hg))
  let IsMax : Subgroup G → Prop := fun U => U ∈ 𝒰 ∧ ∀ V ∈ 𝒰, U ≤ V → V = U
  have hexmax : ∀ U ∈ 𝒰, ∃ M, IsMax M ∧ U ≤ M := by
    intro U hU
    obtain ⟨M, hUM, hM⟩ := hfin.exists_le_maximal hU
    exact ⟨M, ⟨hM.prop, fun V hV hMV => (hM.eq_of_le hV hMV).symm⟩, hUM⟩
  have hmaxnorm : ∀ U, IsMax U → Subgroup.normalizer (familyJoin (Sig U) : Set G) = U := by
    intro U hU
    obtain ⟨W, hW, hNW⟩ := hnorm U hU.1 U hU.1
    rw [Set.inter_self] at hNW
    have hUW : U ≤ W := le_trans (hUnorm U hU.1) hNW
    rw [hU.2 W hW hUW] at hNW
    exact le_antisymm hNW (hUnorm U hU.1)
  have huniq : ∀ U₁ U₂, IsMax U₁ → IsMax U₂ → U₁ = U₂ := by
    by_contra hcon
    push Not at hcon
    set P : Set (Subgroup G × Subgroup G) :=
      {pr | IsMax pr.1 ∧ IsMax pr.2 ∧ pr.1 ≠ pr.2} with hP
    have hPne : P.Nonempty := by
      obtain ⟨U₁, U₂, h1, h2, h12⟩ := hcon
      exact ⟨(U₁, U₂), h1, h2, h12⟩
    have hPfin : P.Finite := Set.toFinite P
    obtain ⟨⟨U₁, U₂⟩, ⟨h1, h2, h12⟩, hmaxpair⟩ :=
      Set.Finite.exists_maximalFor (fun pr => Sig pr.1 ∩ Sig pr.2) P hPfin hPne
    set Sig₀ := Sig U₁ ∩ Sig U₂ with hSig₀
    obtain ⟨W, hW, hNW⟩ := hnorm U₁ h1.1 U₂ h2.1
    obtain ⟨U₃, h3, hWU₃⟩ := hexmax W hW
    have hNU₃ : Subgroup.normalizer (familyJoin Sig₀ : Set G) ≤ U₃ := le_trans hNW hWU₃
    have hjoin_le : familyJoin Sig₀ ≤ Subgroup.normalizer (familyJoin Sig₀ : Set G) :=
      Subgroup.le_normalizer
    have hSig₀U₃ : Sig₀ ⊆ Sig U₃ := by
      intro B hB
      refine hcompat U₃ h3.1 U₁ h1.1 B hB.1 ?_
      refine le_trans ?_ (le_trans hjoin_le hNU₃)
      intro b hb
      apply Subgroup.subset_closure
      simp only [Set.mem_iUnion]
      exact ⟨B, hB, hb⟩
    have hforce : ∀ U, IsMax U → Sig₀ ⊆ Sig U → Sig₀ ⊂ Sig U → U = U₃ := by
      intro U hU _ hproper
      obtain ⟨X, ⟨hXU, hX0⟩, hXN⟩ := exists_mem_normalizer_of_ssubset U (Sig U) (hle U hU.1)
        (hsub U hU.1) (hinv U hU.1) Sig₀ hproper
      have hXU₃ : X ∈ Sig U₃ := hcompat U₃ h3.1 U hU.1 X hXU (le_trans hXN hNU₃)
      by_contra hne
      have hbig : Sig₀ ⊂ Sig U ∩ Sig U₃ :=
        ⟨fun B hB => ⟨hproper.1 hB, hSig₀U₃ hB⟩, fun h => hX0 (h ⟨hXU, hXU₃⟩)⟩
      have hpair : (U, U₃) ∈ P := ⟨hU, h3, hne⟩
      exact hbig.2 (hmaxpair hpair hbig.1)
    have hdistinct : Sig U₁ ≠ Sig U₂ := by
      intro h
      apply h12
      rw [← hmaxnorm U₁ h1, ← hmaxnorm U₂ h2, h]
    by_cases hp1 : Sig₀ ⊂ Sig U₁
    · have hU₁ := hforce U₁ h1 hp1.1 hp1
      by_cases hp2 : Sig₀ ⊂ Sig U₂
      · exact h12 (hU₁.trans (hforce U₂ h2 hp2.1 hp2).symm)
      · have heq : Sig₀ = Sig U₂ := by
          by_contra hne
          exact hp2 ⟨Set.inter_subset_right, fun h => hne (Set.Subset.antisymm
            Set.inter_subset_right h)⟩
        have hle2 : U₂ ≤ U₁ := by
          rw [← hmaxnorm U₂ h2, ← heq, hU₁]
          exact hNU₃
        exact h12 (h2.2 U₁ h1.1 hle2)
    · have heq : Sig₀ = Sig U₁ := by
        by_contra hne
        exact hp1 ⟨Set.inter_subset_left, fun h => hne (Set.Subset.antisymm
          Set.inter_subset_left h)⟩
      have hp2 : Sig₀ ⊂ Sig U₂ := by
        refine ⟨Set.inter_subset_right, fun h => hdistinct ?_⟩
        apply Set.Subset.antisymm
        · rw [← heq]
          exact Set.inter_subset_right
        · exact fun B hB => (h hB).1
      have hU₂ := hforce U₂ h2 hp2.1 hp2
      have hle1 : U₁ ≤ U₂ := by
        rw [← hmaxnorm U₁ h1, ← heq, hU₂]
        exact hNU₃
      exact h12 (h1.2 U₂ h2.1 hle1).symm
  obtain ⟨U₀, hU₀⟩ := hne
  obtain ⟨M, hM, -⟩ := hexmax U₀ hU₀
  refine ⟨M, hM.1, hM.2, fun M' hM' hmax' => huniq M' M ⟨hM', hmax'⟩ hM, ?_⟩
  intro U hU
  obtain ⟨M', hM', hUM'⟩ := hexmax U hU
  rw [← huniq M' M hM' hM]
  exact hUM'

end CFSG.GroupTheory
