module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Exc3CoreRankChkS
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Exc3CoreRankChkE8
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExc

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem exc3core_nb_of_eqvGen {α : Type} {R : α → α → Prop} {a b : α}
    (h : Relation.EqvGen R a b) : a = b ∨ ((∃ z, R a z ∨ R z a) ∧ ∃ z, R b z ∨ R z b) := by
  induction h with
  | rel x y hxy => exact Or.inr ⟨⟨y, Or.inl hxy⟩, ⟨x, Or.inr hxy⟩⟩
  | refl x => exact Or.inl rfl
  | symm x y _ ih =>
    rcases ih with h | ⟨h1, h2⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨h2, h1⟩
  | trans x y z _ _ ih1 ih2 =>
    rcases ih1 with h1 | ⟨h1, h1'⟩
    · subst h1
      exact ih2
    · rcases ih2 with h2 | ⟨h2, h2'⟩
      · subst h2
        exact Or.inr ⟨h1, h1'⟩
      · exact Or.inr ⟨h1, h2'⟩


theorem exc3core_noIso_of_comp {τ : Tag} (K : KacData τ) {p : ℕ} {μ : Fin τ.rank → ℤ}
    {x : Option (Fin τ.rank)} {C : Finset (Option (Fin τ.rank))} (h : K.comp p μ x = ↑C) :
    exc3core_noIso τ K.θ C := by
  intro y hy
  by_cases hC : C = {y}
  · exact Or.inl hC
  · right
    have hz : ∃ z ∈ C, z ≠ y := by
      by_contra hno
      push Not at hno
      exact hC (Finset.eq_singleton_iff_unique_mem.2 ⟨hy, hno⟩)
    obtain ⟨z0, hz0, hz0y⟩ := hz
    have hyc : y ∈ K.comp p μ x := by rw [h]; exact hy
    have hz0c : z0 ∈ K.comp p μ x := by rw [h]; exact hz0
    obtain ⟨hyZ, hyE⟩ := hyc
    obtain ⟨hz0Z, hz0E⟩ := hz0c
    have hE : Relation.EqvGen (K.ZRel p μ) y z0 := (hyE.symm).trans _ _ _ hz0E
    rcases exc3core_nb_of_eqvGen hE with he | ⟨⟨z, hz⟩, -⟩
    · exact absurd he.symm hz0y
    · have hrel : K.ZRel p μ y z ∨ K.ZRel p μ z y := hz
      have hzc : z ∈ K.comp p μ x := by
        rcases hrel with hr | hr
        · exact ⟨hr.2.1, hyE.trans _ _ _ (Relation.EqvGen.rel _ _ hr)⟩
        · exact ⟨hr.1, hyE.trans _ _ _ (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hr))⟩
      have hzC : z ∈ C := by
        have : z ∈ (↑C : Set (Option (Fin τ.rank))) := h ▸ hzc
        exact_mod_cast this
      refine ⟨z, hzC, ?_⟩
      have hadj : K.Adj y z := by
        rcases hrel with hr | hr
        · exact hr.2.2
        · refine ⟨Ne.symm hr.2.2.1, ?_⟩
          rw [iform_comm]
          exact hr.2.2.2
      refine ⟨hadj.1, ?_⟩
      have e : ∀ u, K.extRoot u = exc3core_extVec K.θ u := fun u => by cases u <;> rfl
      have := hadj.2
      rw [e, e] at this
      exact this

theorem exc3core_compRank_of_kac {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (SL : LangSetup τ L 5) {K : KacData τ} (hK : K.Facts) {a : Fin τ.rank → Lˣ}
    (hap : ∀ m, a m ^ 3 = 1) (i : KernelComponent (rootCharHom a)) {P : ℕ → ℕ → Prop}
    (hchk : ∀ C : Finset (Option (Fin τ.rank)), (∃ y, y ∉ C) → exc3core_noIso τ K.θ C →
      P (kacCount τ K.θ C) C.card) :
    P (componentRoots (rootCharHom a) i).ncard (compRank (componentRoots (rootCharHom a) i)) := by
  have hTp : rootDiagUnit τ a ^ 3 = 1 := by
    have e : rootDiagUnit τ (a ^ 3) = rootDiagUnit τ a ^ 3 := map_pow (rootDiagUnitHom τ L) a 3
    have h1 : a ^ 3 = 1 := funext fun m => by simpa using hap m
    rw [← e, h1]
    exact rootDiagUnit_one
  have h3 : ((3 : ℕ) : L) ≠ 0 := by
    intro h
    have h2 : ((2 : ℕ) : L) = 0 := CharP.cast_eq_zero L 2
    have : (1 : L) = 0 := by
      have h' : ((3 : ℕ) : L) - ((2 : ℕ) : L) = 0 := by rw [h, h2, sub_zero]
      push_cast at h'
      linear_combination h'
    exact one_ne_zero this
  obtain ⟨v, μ, -, hpin⟩ := SL.exists_pinnedT_of_prime Nat.prime_three h3 hK hTp
  obtain ⟨x, C, hxC, hC, -, hr, hc⟩ := hpin i
  rw [hr, hc]
  exact hchk C hC (exc3core_noIso_of_comp K hxC)

theorem exc3core_rank_F4 {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] (SL : LangSetup Tag.F4 L 5)
    {a : Fin Tag.F4.rank → Lˣ} (hap : ∀ m, a m ^ 3 = 1) (i : KernelComponent (rootCharHom a)) :
    exc3core_rankTabF4 (componentRoots (rootCharHom a) i).ncard
      (compRank (componentRoots (rootCharHom a) i)) :=
  exc3core_compRank_of_kac SL facts_F4 hap i exc3core_rankChk_F4

theorem exc3core_rank_E6 {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] (SL : LangSetup Tag.E6 L 5)
    {a : Fin Tag.E6.rank → Lˣ} (hap : ∀ m, a m ^ 3 = 1) (i : KernelComponent (rootCharHom a)) :
    exc3core_rankTabE6 (componentRoots (rootCharHom a) i).ncard
      (compRank (componentRoots (rootCharHom a) i)) :=
  exc3core_compRank_of_kac SL facts_E6 hap i exc3core_rankChk_E6

theorem exc3core_rank_E7 {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] (SL : LangSetup Tag.E7 L 5)
    {a : Fin Tag.E7.rank → Lˣ} (hap : ∀ m, a m ^ 3 = 1) (i : KernelComponent (rootCharHom a)) :
    exc3core_rankTabE7 (componentRoots (rootCharHom a) i).ncard
      (compRank (componentRoots (rootCharHom a) i)) :=
  exc3core_compRank_of_kac SL facts_E7 hap i exc3core_rankChk_E7

theorem exc3core_rank_E8 {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] (SL : LangSetup Tag.E8 L 5)
    {a : Fin Tag.E8.rank → Lˣ} (hap : ∀ m, a m ^ 3 = 1) (i : KernelComponent (rootCharHom a)) :
    exc3core_rankTabE8 (componentRoots (rootCharHom a) i).ncard
      (compRank (componentRoots (rootCharHom a) i)) :=
  exc3core_compRank_of_kac SL facts_E8 hap i exc3core_rankChk_E8

end CFSG.LocalAnalysis.GLTheoremA.I167

end
