module

public import CFSG.Quasithin.Background.A3Structure312Transport
public import CFSG.Quasithin.Background.A3Structure312Quotient
public import CFSG.Quasithin.Vol2.Ch1Comm

public section

namespace CFSG.QuasithinUnique.Vol2Native.A312L

open CFSG.Open CFSG.SectionRank CFSG.Assembly.LowTwoRank
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

@[expose] def A312For (X : Type) [Group X] [Finite X] : Prop :=
  ∀ T : Subgroup X, CFSG.QuasithinUnique.IsSylowTwoOf T ⊤ → ∀ B ∈ lFamily T, B ≠ ⊤ →
    A312Case B ⊤

section Transport

variable {X Y : Type} [Group X] [Group Y]

theorem map_map_symm (e : X ≃* Y) (B : Subgroup X) :
    (B.map e.toMonoidHom).map e.symm.toMonoidHom = B := by
  rw [Subgroup.map_map]
  have h : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id X := by
    ext x
    simp
  rw [h, Subgroup.map_id]

noncomputable def mapEquiv (e : X ≃* Y) (B : Subgroup X) : ↥(B.map e.toMonoidHom) ≃* ↥B :=
  (B.equivMapOfInjective e.toMonoidHom e.injective).symm

noncomputable def topMapEquiv (e : X ≃* Y) : ↥(⊤ : Subgroup Y) ≃* ↥(⊤ : Subgroup X) :=
  Subgroup.topEquiv.trans (e.symm.trans Subgroup.topEquiv.symm)

theorem normalizer_map_mulEquiv (e : X ≃* Y) (S : Subgroup X) :
    Subgroup.normalizer ((S.map e.toMonoidHom : Subgroup Y) : Set Y) =
      (Subgroup.normalizer (S : Set X)).map e.toMonoidHom := by
  apply le_antisymm
  · intro y hy
    refine ⟨e.symm y, ?_, by simp⟩
    change e.symm y ∈ Subgroup.normalizer (S : Set X)
    rw [Subgroup.mem_normalizer_iff] at hy ⊢
    intro h
    have h1 := hy (e h)
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv] at h1
    simpa only [MulEquiv.symm_apply_apply, map_mul, map_inv] using h1
  · exact Subgroup.le_normalizer_map e.toMonoidHom

variable [Finite X] [Finite Y]

omit [Finite Y] in
theorem isParabolic2_top_map_equiv (e : X ≃* Y) {P : Subgroup X}
    (h : IsParabolic2 (⊤ : Subgroup X) P) :
    IsParabolic2 (⊤ : Subgroup Y) (P.map e.toMonoidHom) := by
  obtain ⟨-, S, hS, hN⟩ := h
  refine ⟨le_top, S.map e.toMonoidHom,
    A312.isSylowTwoOf_top_map e.toMonoidHom e.surjective hS, ?_⟩
  intro y hy
  have hy' : y ∈ Subgroup.normalizer ((S.map e.toMonoidHom : Subgroup Y) : Set Y) := hy.2
  rw [normalizer_map_mulEquiv] at hy'
  obtain ⟨x, hx, rfl⟩ := hy'
  exact ⟨x, hN ⟨Subgroup.mem_top x, hx⟩, rfl⟩

theorem isMaxParabolic2_top_map_equiv (e : X ≃* Y) {P : Subgroup X}
    (h : IsMaxParabolic2 (⊤ : Subgroup X) P) :
    IsMaxParabolic2 (⊤ : Subgroup Y) (P.map e.toMonoidHom) := by
  obtain ⟨hpar, hne, hmax⟩ := h
  refine ⟨isParabolic2_top_map_equiv e hpar, ?_, ?_⟩
  · intro htop
    apply hne
    have := congrArg (Subgroup.map e.symm.toMonoidHom) htop
    rw [map_map_symm, Subgroup.map_top_of_surjective _ e.symm.surjective] at this
    exact this
  · intro Q hQ hQne hPQ
    have hQ' : IsParabolic2 (⊤ : Subgroup X) (Q.map e.symm.toMonoidHom) :=
      isParabolic2_top_map_equiv e.symm hQ
    have hne' : Q.map e.symm.toMonoidHom ≠ ⊤ := by
      intro htop
      apply hQne
      have := congrArg (Subgroup.map e.toMonoidHom) htop
      rw [Subgroup.map_map] at this
      have h' : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id Y := by
        ext y
        simp
      rw [h', Subgroup.map_id, Subgroup.map_top_of_surjective _ e.surjective] at this
      exact this
    have hPQ' : P ≤ Q.map e.symm.toMonoidHom := by
      have := Subgroup.map_mono (f := e.symm.toMonoidHom) hPQ
      rwa [map_map_symm] at this
    have hQP := hmax _ hQ' hne' hPQ'
    have := congrArg (Subgroup.map e.toMonoidHom) hQP
    rw [Subgroup.map_map] at this
    have h' : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id Y := by
      ext y
      simp
    rw [h', Subgroup.map_id] at this
    exact this

theorem eq_perfectCore_map_equiv (e : X ≃* Y) {B : Subgroup X} {P : Subgroup Y}
    (h : B.map e.toMonoidHom = perfectCore P) :
    B = perfectCore (P.map e.symm.toMonoidHom) := by
  rw [← map_perfectCore e.symm.toMonoidHom P, ← h, map_map_symm]

theorem A312C2.of_mulEquiv (e : X ≃* Y) {B : Subgroup X}
    (h : A312C2 (B.map e.toMonoidHom) (⊤ : Subgroup Y)) : A312C2 B (⊤ : Subgroup X) := by
  obtain ⟨⟨n, hn⟩, hY, P, hP, hBP⟩ := h
  exact ⟨⟨n, IsPSL.of_mulEquiv (A312.modO2Equiv (mapEquiv e B)) hn⟩,
    IsRank2LieChar2.of_mulEquiv (topMapEquiv e) hY, P.map e.symm.toMonoidHom,
    isMaxParabolic2_top_map_equiv e.symm hP, eq_perfectCore_map_equiv e hBP⟩

theorem A312C3.of_mulEquiv (e : X ≃* Y) {B : Subgroup X}
    (h : A312C3 (B.map e.toMonoidHom) (⊤ : Subgroup Y)) : A312C3 B (⊤ : Subgroup X) := by
  obtain ⟨f, h1, h2, P, hP, hBP⟩ := h
  exact ⟨f, IsSz.of_mulEquiv (A312.modO2Equiv (mapEquiv e B)) h1,
    Is2F4.of_mulEquiv (topMapEquiv e) h2, P.map e.symm.toMonoidHom,
    isParabolic2_top_map_equiv e.symm hP, eq_perfectCore_map_equiv e hBP⟩

theorem A312C4.of_mulEquiv (e : X ≃* Y) {B : Subgroup X}
    (h : A312C4 (B.map e.toMonoidHom) (⊤ : Subgroup Y)) : A312C4 B (⊤ : Subgroup X) := by
  obtain ⟨h1, h2, P, hP, hBP⟩ := h
  refine ⟨IsPSL.of_mulEquiv (A312.modO2Equiv (mapEquiv e B)) h1, ?_, P.map e.symm.toMonoidHom,
    isParabolic2_top_map_equiv e.symm hP, eq_perfectCore_map_equiv e hBP⟩
  rcases h2 with h2 | h2
  · exact Or.inl (IsPSL.of_mulEquiv (topMapEquiv e) h2)
  · exact Or.inr (IsPSL.of_mulEquiv (topMapEquiv e) h2)

theorem A312C5.of_mulEquiv (e : X ≃* Y) {B : Subgroup X}
    (h : A312C5 (B.map e.toMonoidHom) (⊤ : Subgroup Y)) : A312C5 B (⊤ : Subgroup X) := by
  obtain ⟨h1, h2, P, hP, hBP⟩ := h
  exact ⟨IsPSL.of_mulEquiv (A312.modO2Equiv (mapEquiv e B)) h1,
    IsPSL.of_mulEquiv (topMapEquiv e) h2, P.map e.symm.toMonoidHom,
    isParabolic2_top_map_equiv e.symm hP, eq_perfectCore_map_equiv e hBP⟩

theorem A312Case.of_mulEquiv (e : X ≃* Y) {B : Subgroup X}
    (h : A312Case (B.map e.toMonoidHom) (⊤ : Subgroup Y)) : A312Case B (⊤ : Subgroup X) := by
  have eB := mapEquiv e B
  have eL := topMapEquiv e
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · left
    exact A312C2.of_mulEquiv e h
  · right
    left
    exact A312C3.of_mulEquiv e h
  · iterate 2 right
    left
    exact A312C4.of_mulEquiv e h
  · iterate 3 right
    left
    exact A312C5.of_mulEquiv e h
  · iterate 4 right
    left
    exact A312C6.of_equiv eB eL h
  · iterate 5 right
    left
    exact A312C7.of_equiv eB eL h
  · iterate 6 right
    left
    exact A312C8.of_equiv eB eL h
  · iterate 7 right
    left
    exact A312C9.of_equiv eB eL h
  · iterate 8 right
    left
    exact A312C10.of_equiv eB eL h
  · iterate 9 right
    left
    exact A312C11.of_equiv eB eL h
  · iterate 10 right
    left
    exact A312C12.of_equiv eB eL h
  · iterate 11 right
    left
    exact A312C13.of_equiv eB eL h
  · iterate 12 right
    left
    exact A312C14.of_equiv eB eL h
  · iterate 13 right
    left
    exact A312C15.of_equiv eB eL h
  · iterate 14 right
    left
    exact A312C16.of_equiv eB eL h
  · iterate 15 right
    left
    exact A312C17.of_equiv eB eL h
  · iterate 16 right
    left
    exact A312C18.of_equiv eB eL h
  · iterate 17 right
    left
    exact A312C19.of_equiv eB eL h
  · iterate 18 right
    exact A312C20.of_equiv eB eL h

theorem A312For.of_mulEquiv (e : X ≃* Y) (h : A312For Y) : A312For X := by
  intro T hT B hB hBtop
  have hT' : CFSG.QuasithinUnique.IsSylowTwoOf (T.map e.toMonoidHom) ⊤ :=
    A312.isSylowTwoOf_top_map e.toMonoidHom e.surjective hT
  have hB' : B.map e.toMonoidHom ∈ lFamily (T.map e.toMonoidHom) := by
    have h1 := cComp_map_mulEquiv e (show B ∈ cComp (B ⊔ T) from hB)
    rw [Subgroup.map_sup] at h1
    exact h1
  have hne : B.map e.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hBtop
    have := congrArg (Subgroup.map e.symm.toMonoidHom) htop
    rw [map_map_symm, Subgroup.map_top_of_surjective _ e.symm.surjective] at this
    exact this
  exact A312Case.of_mulEquiv e (h _ hT' _ hB' hne)

end Transport

end CFSG.QuasithinUnique.Vol2Native.A312L
