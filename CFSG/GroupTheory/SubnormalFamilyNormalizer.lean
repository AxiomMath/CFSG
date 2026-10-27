module

public import CFSG.GroupTheory.SubnormalJoin
public import CFSG.Foundations.Basic

public section

namespace CFSG.GroupTheory

open Subgroup

universe u

theorem closure_iUnion_normal_of_conj_mem {G : Type u} [Group G] (Sig₀ : Set (Subgroup G))
    (hinv : ∀ A ∈ Sig₀, ∀ g : G, CFSG.conjugate A g ∈ Sig₀) :
    (Subgroup.closure (⋃ A ∈ Sig₀, (A : Set G))).Normal := by
  refine ⟨fun l hl g => ?_⟩
  have hle : (Subgroup.closure (⋃ A ∈ Sig₀, (A : Set G))).map (MulAut.conj g).toMonoidHom ≤
      Subgroup.closure (⋃ A ∈ Sig₀, (A : Set G)) := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨a, ha, rfl⟩
    simp only [Set.mem_iUnion] at ha
    obtain ⟨A, hA, haA⟩ := ha
    have hconj : CFSG.conjugate A g⁻¹ ∈ Sig₀ := hinv A hA g⁻¹
    apply Subgroup.subset_closure
    simp only [Set.mem_iUnion]
    refine ⟨CFSG.conjugate A g⁻¹, hconj, ?_⟩
    change _ ∈ A.map (MulAut.conj g⁻¹⁻¹).toMonoidHom
    rw [inv_inv]
    exact ⟨a, haA, rfl⟩
  exact hle ⟨l, hl, rfl⟩

theorem map_subtype_le_normalizer {G : Type u} [Group G] {K : Subgroup G} {X L : Subgroup K}
    (h : X ≤ Subgroup.normalizer (L : Set K)) :
    X.map K.subtype ≤ Subgroup.normalizer ((L.map K.subtype : Subgroup G) : Set G) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro g
  have hx' := Subgroup.mem_normalizer_iff.mp (h hx)
  constructor
  · rintro ⟨l, hl, rfl⟩
    refine ⟨x * l * x⁻¹, (hx' l).mp hl, ?_⟩
    simp
  · rintro ⟨l, hl, hgl⟩
    have hmem : x⁻¹ * l * x ∈ L := by
      have h2 := (hx' (x⁻¹ * l * x)).mpr (by
        rw [show x * (x⁻¹ * l * x) * x⁻¹ = l by group]
        exact hl)
      exact h2
    refine ⟨x⁻¹ * l * x, hmem, ?_⟩
    have hgl' : (l : G) = (x : G) * g * (x : G)⁻¹ := hgl
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hgl']
    group

theorem invariant_subnormal_family_normalizer_extension {G : Type u} [Group G] [Finite G]
    (Sig : Set (Subgroup G)) (hsub : ∀ A ∈ Sig, A.IsSubnormal)
    (hinv : ∀ A ∈ Sig, ∀ g : G, CFSG.conjugate A g ∈ Sig) (Sig₀ : Set (Subgroup G))
    (hSig₀ : Sig₀ ⊂ Sig) :
    ∃ X ∈ Sig \ Sig₀,
      X ≤ Subgroup.normalizer
        ((Subgroup.closure (⋃ A ∈ Sig₀, (A : Set G)) : Subgroup G) : Set G) := by
  classical
  induction hcard : Nat.card G using Nat.strong_induction_on generalizing G with
  | _ N ih =>
  set L := Subgroup.closure (⋃ A ∈ Sig₀, (A : Set G)) with hL
  have hLsub : L.IsSubnormal :=
    (subnormal_subgroups_generated_join Sig₀ fun A hA => hsub A (hSig₀.1 hA)).1
  obtain ⟨X₀, hX₀S, hX₀⟩ := Set.exists_of_ssubset hSig₀
  rcases hLsub.lt_normal with htop | ⟨G₁, hG₁, hLG₁, hG₁top⟩
  ·
    refine ⟨X₀, ⟨hX₀S, hX₀⟩, ?_⟩
    rw [htop]
    have : (⊤ : Subgroup G).Normal := inferInstance
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  ·
    set Sig₁ := {A ∈ Sig | A ≤ G₁} with hSig₁
    have hSig₀₁ : Sig₀ ⊆ Sig₁ := by
      intro A hA
      refine ⟨hSig₀.1 hA, le_trans ?_ hLG₁⟩
      rw [hL]
      intro a ha
      apply Subgroup.subset_closure
      simp only [Set.mem_iUnion]
      exact ⟨A, hA, ha⟩
    by_cases hproper : Sig₀ ⊂ Sig₁
    ·
      have hlt : Nat.card G₁ < N := by
        rw [← hcard]
        have h := Subgroup.card_lt_of_lt hG₁top
        rwa [Subgroup.card_top] at h
      let f : Subgroup G → Subgroup G₁ := fun A => A.subgroupOf G₁
      have hfinv : ∀ A : Subgroup G, A ≤ G₁ → (f A).map G₁.subtype = A := fun A hA =>
        Subgroup.map_subgroupOf_eq_of_le hA
      set Sig₁' := f '' Sig₁ with hSig₁'
      set Sig₀' := f '' Sig₀ with hSig₀'
      have hsub' : ∀ B ∈ Sig₁', B.IsSubnormal := by
        rintro _ ⟨A, hA, rfl⟩
        exact (hsub A hA.1).subgroupOf
      have hinv' : ∀ B ∈ Sig₁', ∀ g : G₁, CFSG.conjugate B g ∈ Sig₁' := by
        rintro _ ⟨A, hA, rfl⟩ g
        have hconj : CFSG.conjugate A g ∈ Sig := hinv A hA.1 g
        have hle : CFSG.conjugate A g ≤ G₁ := by
          rintro _ ⟨a, ha, rfl⟩
          have haG : a ∈ G₁ := hA.2 ha
          change (g : G)⁻¹ * a * (g : G)⁻¹⁻¹ ∈ G₁
          exact G₁.mul_mem (G₁.mul_mem (G₁.inv_mem g.2) haG) (G₁.inv_mem (G₁.inv_mem g.2))
        refine ⟨CFSG.conjugate A g, ⟨hconj, hle⟩, ?_⟩
        apply Subgroup.map_injective G₁.subtype_injective
        rw [hfinv _ hle]
        ext z
        simp only [CFSG.conjugate, Subgroup.mem_map, MulEquiv.coe_toMonoidHom,
          MulAut.conj_apply, Subgroup.coe_subtype]
        constructor
        · rintro ⟨a, ha, rfl⟩
          refine ⟨g⁻¹ * ⟨a, hA.2 ha⟩ * g⁻¹⁻¹, ⟨⟨a, hA.2 ha⟩, ?_, rfl⟩, by simp⟩
          simpa [f, Subgroup.mem_subgroupOf] using ha
        · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
          refine ⟨(b : G), ?_, by simp⟩
          simpa [f, Subgroup.mem_subgroupOf] using hb
      have hfinj : Set.InjOn f Sig₁ := by
        intro A hA B hB hAB
        rw [← hfinv A hA.2, ← hfinv B hB.2, hAB]
      have hproper' : Sig₀' ⊂ Sig₁' := by
        refine ⟨Set.image_mono hproper.1, ?_⟩
        intro hrev
        apply hproper.2
        intro A hA
        obtain ⟨B, hB, hBA⟩ := hrev ⟨A, hA, rfl⟩
        rwa [← hfinj (hSig₀₁ hB) hA hBA]
      obtain ⟨X', ⟨hX'S, hX'not⟩, hX'⟩ := ih (Nat.card G₁) hlt Sig₁' hsub' hinv' Sig₀' hproper' rfl
      obtain ⟨X, hXS, rfl⟩ := hX'S
      refine ⟨X, ⟨hXS.1, fun hX => hX'not ⟨X, hX, rfl⟩⟩, ?_⟩
      have hLmap : (Subgroup.closure (⋃ B ∈ Sig₀', (B : Set G₁))).map G₁.subtype = L := by
        rw [MonoidHom.map_closure, hL]
        congr 1
        ext z
        simp only [Set.mem_image, Set.mem_iUnion, Subgroup.coe_subtype]
        constructor
        · rintro ⟨w, ⟨_, ⟨A, hA, rfl⟩, hw⟩, rfl⟩
          exact ⟨A, hA, by simpa [f, Subgroup.mem_subgroupOf] using hw⟩
        · rintro ⟨A, hA, hz⟩
          have hzG : z ∈ G₁ := (hSig₀₁ hA).2 hz
          exact ⟨⟨z, hzG⟩, ⟨f A, ⟨A, hA, rfl⟩, by simpa [f, Subgroup.mem_subgroupOf] using hz⟩,
            rfl⟩
      have h := map_subtype_le_normalizer hX'
      rw [hLmap, hfinv X hXS.2] at h
      exact h
    ·
      have heq : Sig₀ = Sig₁ := by
        by_contra hne
        exact hproper ⟨hSig₀₁, fun h => hne (Set.Subset.antisymm hSig₀₁ h)⟩
      have hinv₀ : ∀ A ∈ Sig₀, ∀ g : G, CFSG.conjugate A g ∈ Sig₀ := by
        intro A hA g
        rw [heq] at hA ⊢
        refine ⟨hinv A hA.1 g, ?_⟩
        rintro _ ⟨a, ha, rfl⟩
        have haG : a ∈ G₁ := hA.2 ha
        change g⁻¹ * a * g⁻¹⁻¹ ∈ G₁
        exact hG₁.conj_mem a haG g⁻¹
      have hLnormal : L.Normal := closure_iUnion_normal_of_conj_mem Sig₀ hinv₀
      refine ⟨X₀, ⟨hX₀S, hX₀⟩, ?_⟩
      rw [Subgroup.normalizer_eq_top]
      exact le_top

end CFSG.GroupTheory
