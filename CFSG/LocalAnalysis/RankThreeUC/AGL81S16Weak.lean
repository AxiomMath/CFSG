module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.RankThreeUC.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def weakClosureIn (V T : Subgroup G) : Subgroup G :=
  ⨆ g : {g : G // V.map (MulAut.conj g).toMonoidHom ≤ T},
    V.map (MulAut.conj (g : G)).toMonoidHom

omit [Finite G] in
theorem weakClosureIn_le (V T : Subgroup G) : weakClosureIn V T ≤ T :=
  iSup_le fun g => g.2

omit [Finite G] in
theorem map_conj_le_weakClosureIn {V T : Subgroup G} {g : G}
    (hg : V.map (MulAut.conj g).toMonoidHom ≤ T) :
    V.map (MulAut.conj g).toMonoidHom ≤ weakClosureIn V T :=
  le_iSup (fun g : {g : G // V.map (MulAut.conj g).toMonoidHom ≤ T} =>
    V.map (MulAut.conj (g : G)).toMonoidHom) ⟨g, hg⟩

omit [Finite G] in
theorem le_weakClosureIn {V T : Subgroup G} (hVT : V ≤ T) : V ≤ weakClosureIn V T := by
  have h1 : V.map (MulAut.conj (1 : G)).toMonoidHom = V := by
    ext x
    simp
  have := map_conj_le_weakClosureIn (V := V) (T := T) (g := 1) (by rw [h1]; exact hVT)
  rwa [h1] at this

omit [Finite G] in
private theorem conj_mem_weakClosureIn {V T : Subgroup G} {n : G} (hn : n ∈ normalizer (T : Set G))
    {y : G} (hy : y ∈ weakClosureIn V T) : n * y * n⁻¹ ∈ weakClosureIn V T := by
  refine Subgroup.iSup_induction _ (C := fun y => n * y * n⁻¹ ∈ weakClosureIn V T) hy
    (fun g x hx => ?_) ?_ (fun x y hx hy => ?_)
  · obtain ⟨x₀, hx₀, rfl⟩ := hx
    have hng : V.map (MulAut.conj (n * (g : G))).toMonoidHom ≤ T := by
      rintro _ ⟨v, hv, rfl⟩
      have h1 : (g : G) * v * (g : G)⁻¹ ∈ T := g.2 ⟨v, hv, rfl⟩
      have h2 := (mem_normalizer_iff.mp hn _).mp h1
      simpa [mul_assoc] using h2
    exact map_conj_le_weakClosureIn hng ⟨x₀, hx₀, by simp [mul_assoc]⟩
  · simp
  · simpa [mul_assoc] using mul_mem hx hy

omit [Finite G] in
theorem normalizer_le_normalizer_weakClosureIn (V T : Subgroup G) :
    normalizer (T : Set G) ≤ normalizer (weakClosureIn V T : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro y
  exact ⟨fun hy => conj_mem_weakClosureIn hn hy, fun hy => by
    simpa [mul_assoc] using conj_mem_weakClosureIn ((normalizer (T : Set G)).inv_mem hn) hy⟩

theorem IsWitness.normalizer_le_of_normalized {p : ℕ} {P : Sylow p G} {M : Subgroup G}
    (hw : IsWitness p P M) {T X : Subgroup G} (hX2 : IsPGroup 2 X) (hX1 : X ≠ ⊥)
    (hTX : normalizer (T : Set G) ≤ normalizer (X : Set G))
    (h2 : 2 ≤ CFSG.Open.pRank p (M ⊓ normalizer (X : Set G))) : normalizer (T : Set G) ≤ M :=
  hTX.trans (hw.u2 _ ⟨X, hX1, hX2, rfl⟩ (by rwa [inf_comm]))

theorem IsWitness.normalizer_le_of_weakClosure {p : ℕ} {P : Sylow p G} {M : Subgroup G}
    (hw : IsWitness p P M) {T V : Subgroup G} (hT : IsPGroup 2 T) (hVT : V ≤ T) (hV1 : V ≠ ⊥)
    (h2 : 2 ≤ CFSG.Open.pRank p (M ⊓ normalizer (weakClosureIn V T : Set G))) :
    normalizer (T : Set G) ≤ M :=
  hw.normalizer_le_of_normalized (hT.to_le (weakClosureIn_le V T))
    (ne_bot_of_le_ne_bot hV1 (le_weakClosureIn hVT)) (normalizer_le_normalizer_weakClosureIn V T) h2

end CFSG.LocalAnalysis.RankThreeUC
