module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcRoots

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

variable
  {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem excTri_D4_twistInner_of_untwisted (S : LangSetup .D4 L p) {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr)) :
    twistInner {v : Fin Tag.D4.rank → ℤ | IsRoot .D4 v}
      (S.ρ : (Fin Tag.D4.rank → ℤ) → (Fin Tag.D4.rank → ℤ)) := by
  obtain ⟨w, hn⟩ := S.D.n_weyl
  refine ⟨w, ?_, fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ hn hγ⟩
  have htop : Subgroup.closure {s : WeylGroup .D4 |
      ∃ γ ∈ {v : Fin Tag.D4.rank → ℤ | IsRoot .D4 v}, s = rootReflection γ} = ⊤ := by
    rw [eq_top_iff, ← (coxeterSystem .D4).subgroup_closure_range_simple, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    refine Subgroup.subset_closure ⟨Pi.single i 1, isRoot_single .D4 i, ?_⟩
    rw [rootReflection_eq_conj (w := 1) (j := i) (one_smul _ _), one_mul, inv_one, mul_one]
  rw [htop]
  exact Subgroup.mem_top w

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
