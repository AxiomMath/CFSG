module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShE6Defs
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24A2CubeClass
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleOrbit

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6UniqAbs
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24

theorem e6_rho_swap_of_stable
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.E6 L p₀) (h3 : ((3 : ℕ) : L) ≠ 0) {a : Fin Tag.E6.rank → Lˣ}
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (hap : ∀ k, a k ^ 3 = 1)
    (h18 : (kernelRoots (rootCharHom a)).ncard = 18) {i j : KernelComponent (rootCharHom a)}
    (hj : (S.ρ : (Fin Tag.E6.rank → ℤ) → _) '' componentRoots (rootCharHom a) j =
      componentRoots (rootCharHom a) j)
    (hi : (S.ρ : (Fin Tag.E6.rank → ℤ) → _) '' componentRoots (rootCharHom a) i ≠
      componentRoots (rootCharHom a) i) :
    ∃ m : KernelComponent (rootCharHom a),
      (S.ρ : (Fin Tag.E6.rank → ℤ) → _) '' componentRoots (rootCharHom a) i =
          componentRoots (rootCharHom a) m ∧
        (S.ρ : (Fin Tag.E6.rank → ℤ) → _) '' componentRoots (rootCharHom a) m =
          componentRoots (rootCharHom a) i ∧
        m ≠ i ∧ m ≠ j ∧ i ≠ j ∧ ∀ k, k = i ∨ k = m ∨ k = j := by
  obtain ⟨c, hc, -⟩ := kernel_classes_of_ncard_eighteen h3 hap h18
  have hinj : ∀ {X Y : Set (Fin Tag.E6.rank → ℤ)}, (S.ρ : (Fin Tag.E6.rank → ℤ) → _) '' X =
      (S.ρ : (Fin Tag.E6.rank → ℤ) → _) '' Y → X = Y :=
    fun h => Set.image_injective.2 S.ρ.injective h
  obtain ⟨m, hm⟩ := outer_exists_image_component S hT i
  obtain ⟨m', hm'⟩ := outer_exists_image_component S hT m
  have hij : i ≠ j := by
    rintro rfl
    exact hi hj
  have hmi : m ≠ i := by
    rintro rfl
    exact hi hm
  have hmj : m ≠ j := by
    rintro rfl
    exact hij (eq_of_componentRoots_eq (hinj (hm.trans hj.symm)))
  have hall : ∀ k, k = i ∨ k = m ∨ k = j := by
    obtain ⟨x, rfl⟩ := hc.2 i
    obtain ⟨y, rfl⟩ := hc.2 m
    obtain ⟨z, rfl⟩ := hc.2 j
    intro k
    obtain ⟨t, rfl⟩ := hc.2 k
    have key : ∀ x y z t : Fin 3, y ≠ x → z ≠ x → z ≠ y → t = x ∨ t = y ∨ t = z := by decide
    rcases key x y z t (fun h => hmi (by rw [h])) (fun h => hij (by rw [h]))
        (fun h => hmj (by rw [h])) with h | h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (Or.inl (by rw [h]))
    · exact Or.inr (Or.inr (by rw [h]))
  have hm'm : m' ≠ m := by
    intro h
    rw [h] at hm'
    exact hmi (eq_of_componentRoots_eq (hinj (hm'.trans hm.symm)))
  have hm'j : m' ≠ j := by
    intro h
    rw [h] at hm'
    exact hmj (eq_of_componentRoots_eq (hinj (hm'.trans hj.symm)))
  rcases hall m' with h | h | h
  · rw [h] at hm'
    exact ⟨m, hm, hm', hmi, hmj, hij, hall⟩
  · exact absurd h hm'm
  · exact absurd h hm'j

theorem e6OrbitThreeUnique_holds :
    E6OrbitThreeUnique := by
  intro L _ _ _ p₀ S a hT hap h18 i hi3 j
  have h3L : ((3 : ℕ) : L) ≠ 0 := by
    have h2 : ((2 : ℕ) : L) = 0 := CharP.cast_eq_zero L 2
    have h3 : ((3 : ℕ) : L) = 1 := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, Nat.cast_add, h2, zero_add, Nat.cast_one]
    rw [h3]
    exact one_ne_zero
  obtain ⟨c, hc, -⟩ := kernel_classes_of_ncard_eighteen h3L hap h18
  rcases orbit_dichotomy S hT hc with ⟨j₀, hj₀⟩ | hall
  · exfalso
    have hj₀s : (S.ρ : (Fin Tag.E6.rank → ℤ) → _) '' componentRoots (rootCharHom a) j₀ =
        componentRoots (rootCharHom a) j₀ := by
      have h := (outer_componentOrbitLength_spec S hT j₀).2.1
      rwa [hj₀, Function.iterate_one] at h
    have his : (S.ρ : (Fin Tag.E6.rank → ℤ) → _) '' componentRoots (rootCharHom a) i ≠
        componentRoots (rootCharHom a) i := by
      intro h
      have : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) ≤ 1 :=
        Nat.sInf_le ⟨one_pos, by rw [Function.iterate_one]; exact h⟩
      omega
    obtain ⟨m, hm, hm', -⟩ := e6_rho_swap_of_stable S h3L hT hap h18 hj₀s his
    have h2 : (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2] '' componentRoots (rootCharHom a) i =
        componentRoots (rootCharHom a) i := by
      rw [show (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2] = S.ρ ∘ S.ρ from rfl, Set.image_comp, hm, hm']
    have : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) ≤ 2 :=
      Nat.sInf_le ⟨two_pos, h2⟩
    omega
  · unfold rationalComponent rationalSpan
    rw [(hall j).2, (hall i).2]

end CFSG.LocalAnalysis.GLTheoremA.T158

end
