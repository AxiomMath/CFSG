module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreLang
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentrePerm
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreKac
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreScalar
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreRank

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSConn

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE CFSG.LieType.Steinberg.Adjoint
open scoped MatrixGroups

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

section Class


variable {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}

theorem conn_class_unitary (S : LangSetup Tag.E6 L p₀) {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = twistHom TwistTag.E6 L Fr)
    (h3 : ((3 : ℕ) : L) ≠ 0) {a : Fin Tag.E6.rank → Lˣ}
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (hap : ∀ i, a i ^ 3 = 1) (h3q : 3 ∣ S.D.q + 1)
    (hk : (kernelRoots (rootCharHom a)).ncard = 22 ∨ (kernelRoots (rootCharHom a)).ncard = 30)
    (i : KernelComponent (rootCharHom a)) :
    ∃ m : ℕ, (m = 1 ∨ m = 4 ∨ m = 5) ∧ ∃ (ψ : SL(m + 1, L) →* ModGL Tag.E6 L)
      (σ : Fin (m + 1) → Fin (m + 1) → Fin Tag.E6.rank → ℤ) (π : Equiv.Perm (Fin (m + 1))),
      IsSLFrame ψ σ ∧ componentRoots (rootCharHom a) i = frameRoots σ ∧
        (∀ x y, x ≠ y → S.ρ (σ x y) = σ (π y) (π x)) ∧
        componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 ∧
        (m = 5 → ∀ A ∈ Subgroup.center SL(m + 1, L), A ^ 3 = 1 → ψ A = 1) ∧
        (m = 1 → compRank (componentRoots (rootCharHom a) i) = 1 ∧
          (componentRoots (rootCharHom a) i).ncard = 2 ∧
            (kernelRoots (rootCharHom a)).ncard = 22) := by
  classical
  obtain ⟨u, hu, hρ⟩ := exists_rho_neg_weyl_of_conn S hFr hΦ hT hap h3q
    (by rcases hk with h | h <;> simp [h])
  obtain ⟨m, hm, v, ψ₀, σ₀, hψ₀, hn₀, hΨ, hS5, hS1⟩ := conn_class_data h3 hap hk i
  have hψ := hψ₀.transport v
  have hnorm : ∀ x y, x ≠ y → iform (v • σ₀ x y) (v • σ₀ x y) = 2 := fun x y hxy => by
    rw [iform_smul]
    exact hn₀ x y hxy
  have hΨ' : componentRoots (rootCharHom a) i = frameRoots (fun x y => v • σ₀ x y) := by
    rw [hΨ, IsSLFrame.frameRoots_smul]
  obtain ⟨π, hπ1⟩ := exists_unitary_perm_of_rho_eq_neg i hψ hnorm hΨ' S.ρ hu hρ
  have hstab : ∀ γ ∈ componentRoots (rootCharHom a) i,
      S.ρ γ ∈ componentRoots (rootCharHom a) i := by
    intro γ hγ
    rw [hΨ'] at hγ ⊢
    obtain ⟨x, y, hxy, rfl⟩ := hγ
    exact ⟨π y, π x, fun h => hxy (π.injective h).symm, hπ1 x y hxy⟩
  have hfin : (componentRoots (rootCharHom a) i).Finite :=
    (CFSG.Blueprint.Chevalley.finite_setOf_isRoot Tag.E6).subset fun γ hγ => hγ.1.1
  refine ⟨m, hm, _, fun x y => v • σ₀ x y, π, hψ, hΨ', hπ1,
    componentOrbitLength_eq_one hfin hstab, fun h5 A hA hA3 => ?_, hS1⟩
  subst h5
  obtain ⟨S5, hS5', hr5⟩ := hS5 rfl
  have h1 : ψ₀ A = 1 := frame_A5_center_cube_eq_one h3 hS5' hψ₀ hr5 hA hA3
  change (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) L v)).toMonoidHom (ψ₀ A) = 1
  rw [h1, map_one]

theorem not_three_dvd_center_of_conn_class (S : LangSetup Tag.E6 L p₀) {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = twistHom TwistTag.E6 L Fr)
    (h3 : ((3 : ℕ) : L) ≠ 0) {a : Fin Tag.E6.rank → Lˣ}
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (hap : ∀ i, a i ^ 3 = 1) (h3q : 3 ∣ S.D.q + 1)
    (hk : (kernelRoots (rootCharHom a)).ncard = 22 ∨ (kernelRoots (rootCharHom a)).ncard = 30)
    (i : KernelComponent (rootCharHom a))
    (hQS : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
    [Finite ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)] :
    ¬ 3 ∣ Nat.card (Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  classical
  obtain ⟨m, hm, ψ, σ, π, hψ, hΨ, hπ1, hs1, hψ6, hS1⟩ :=
    conn_class_unitary S hFr hΦ h3 hT hap h3q hk i
  have hπ : ∀ x y, x ≠ y → (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom a) i)] (σ x y) = σ (π y) (π x) := fun x y hxy => by
    rw [hs1, Function.iterate_one]
    exact hπ1 x y hxy
  obtain ⟨r, e, hr, hchar, he, hq⟩ := S.exists_char_pow
  rcases hm with rfl | rfl | rfl
  · exact not_three_dvd_center_of_rankOne S hT i (hS1 rfl).1 (hS1 rfl).2.1 hQS hr hchar he hq
  · exact not_three_dvd_center_of_suN S hT i (ν := 4 + 1) (Or.inl rfl) hψ hΨ π hπ hr hchar he hq
      hs1 (fun h => absurd h (by norm_num))
  · exact not_three_dvd_center_of_suN S hT i (ν := 5 + 1) (Or.inr rfl) hψ hΨ π hπ hr hchar he hq
      hs1 (fun _ => hψ6 rfl)

end Class

end KSConn

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
