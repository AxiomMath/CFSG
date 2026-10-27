module

public import CFSG.ClassicalInvolution.ModelFacts.Models
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.RankOne
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCFrame

public section

namespace CFSG.ClassicalInvolution.Models.SymplecticPairs

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.ClassicalInvolution.ModelFacts

variable {p : ℕ} [hp : Fact p.Prime]

theorem modelUniv_PSp_K (m f : ℕ) :
    (modelUniv .PSp m p f hp.out).K = StatedSp m (GaloisField p f) := rfl

theorem mem_fundamentalSubgroups_PSp_iff {m f : ℕ}
    (hadm : StatedLieAdmissible .PSp m p f) (R : Subgroup (StatedSp m (GaloisField p f))) :
    R ∈ fundamentalSubgroups .PSp (modelUniv .PSp m p f hp.out).D ↔
      ∃ P, IsHyperbolicPlane P ∧ R = planeGroup P := by
  have hm : 1 ≤ m := by
    have := hadm.2.2.1
    omega
  let k₀ : Fin m := ⟨m - 1, by omega⟩
  have hk₀ : ¬ k₀.val + 1 < m := by
    simp only [k₀]
    omega
  have hlong : IsLongestRoot (modelUniv .PSp m p f hp.out).D (Pi.single k₀ 1) :=
    isLongestRoot_single .PSp m p f hp.out trivial hadm k₀ (by
      simp only [IsLongNode, k₀]
      omega)
  have e0 : (modelUniv .PSp m p f hp.out).D.rootGroup (Pi.single k₀ 1) ⊔
      (modelUniv .PSp m p f hp.out).D.rootGroup (-Pi.single k₀ 1) =
      (longBlock (GaloisField p f) m k₀).range := (range_longBlock_eq_rankOne hk₀).symm
  constructor
  · rintro ⟨g, γ, hγ, rfl⟩
    have hγ' : IsLongestRoot (modelUniv .PSp m p f hp.out).D γ := by
      rcases hγ with h | ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h (by decide)
      · exact absurd h (by decide)
    obtain ⟨h, hh⟩ := exists_conj_of_isLongestRoot .PSp m p f hp.out trivial hadm hlong hγ'
    have key := (congrArg (fun H => H.map (MulAut.conj g).toMonoidHom) hh.symm).trans
      ((map_conj_map_conj _ _ _).trans
        (congrArg (fun H => H.map (MulAut.conj (g * h)).toMonoidHom) e0))
    exact (exists_conj_longBlock_iff k₀ _).1 ⟨g * h, key⟩
  · intro hP
    obtain ⟨g, hg⟩ := (exists_conj_longBlock_iff k₀ R).2 hP
    exact ⟨g, Pi.single k₀ 1, Or.inl hlong,
      hg.trans (congrArg (fun H => H.map (MulAut.conj g).toMonoidHom) e0.symm)⟩

end CFSG.ClassicalInvolution.Models.SymplecticPairs
