module

public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.ExactGL2OrderAlternatives
public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.SevenCharacterClassicalRecognition

public section

open scoped Classical

namespace CFSG.Semidihedral.GL2Recognition

open CFSG.TwoRankLowerBound.Helpers CFSG.BlockSectionOrthogonality.Helpers
  CFSG.Semidihedral.Principal CFSG.Semidihedral.Principal.GL2ThreeCharacters

theorem even_orderOf_of_mem_sylow_two {G : Type*} [Group G] (S : Sylow 2 G) {s : G}
    (hs : s ∈ (S : Subgroup G)) (hs1 : s ≠ 1) : Even (orderOf s) := by
  obtain ⟨k, hk⟩ := S.isPGroup' ⟨s, hs⟩
  have hord : orderOf s ∣ 2 ^ k := by
    rw [← Subgroup.orderOf_mk s hs]
    exact orderOf_dvd_of_pow_eq_one hk
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
  rcases m with _ | m
  · rw [pow_zero, orderOf_eq_one_iff] at hm
    exact absurd hm hs1
  · rw [hm, pow_succ]
    exact even_two.mul_left _

theorem exact_GL2_centralizer_produces_order_alternatives {G : Type} [Group G] [Fintype G]
    (hinv : ∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v) (t : G)
    (ht : orderOf t = 2)
    (π : Subgroup.centralizer ({t} : Set G) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (a p b : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) (ha : orderOf a = 8)
    (hp : orderOf p = 3) (hb : orderOf b = 2)
    (hbz : b ∉ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)))
    (φ : Fin 8 → Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) → ℂ)
    (hφirr : ∀ i, φ i ∈ CFSG.BlocksIrr (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)))
    (hφ : let ξ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 8)
      let ω : ℂ := ξ + ξ ^ 3
      let rep : Fin 8 → Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) :=
        ![1, -1, a ^ 2, p, -1 * p, b, a, a⁻¹]
      let table : Fin 8 → Fin 8 → ℂ := ![![1, 1, 1, 1, 1, 1, 1, 1],
        ![1, 1, 1, 1, 1, -1, -1, -1], ![2, 2, 2, -1, -1, 0, 0, 0], ![3, 3, -1, 0, 0, -1, 1, 1],
        ![3, 3, -1, 0, 0, 1, -1, -1], ![4, -4, 0, 1, -1, 0, 0, 0], ![2, -2, 0, -1, 1, 0, ω, -ω],
        ![2, -2, 0, -1, 1, 0, -ω, ω]]
      ∀ i j, φ i (rep j) = table i j) :
    let C := Subgroup.centralizer ({t} : Set G)
    let Φ : Fin 5 → Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) → ℂ :=
      ![φ 0 + φ 2 - φ 4, φ 2 - φ 6, φ 6 - φ 7, φ 1 + φ 4 - φ 5, φ 1 + φ 2 - φ 3]
    let β : Fin 5 → G → ℂ := fun i => inducedFunction C (fun c => Φ i (π c))
    let identities : CFSG.BlocksIrr G → CFSG.BlocksIrr G → CFSG.BlocksIrr G →
        CFSG.BlocksIrr G → CFSG.BlocksIrr G → CFSG.BlocksIrr G → CFSG.BlocksIrr G → Prop :=
      fun χ₁ χ₂ χ₃ χ₄ χ₅ χ₆ χ₇ =>
        [χ₁, χ₂, χ₃, χ₄, χ₅, χ₆, χ₇].Nodup ∧
        (χ₁ : G → ℂ) ≠ 1 ∧ (χ₂ : G → ℂ) ≠ 1 ∧ (χ₃ : G → ℂ) ≠ 1 ∧ (χ₄ : G → ℂ) ≠ 1 ∧
        (χ₅ : G → ℂ) ≠ 1 ∧ (χ₆ : G → ℂ) ≠ 1 ∧ (χ₇ : G → ℂ) ≠ 1 ∧
        β 0 = 1 + ((χ₁ : G → ℂ) - χ₂) ∧ β 1 = (χ₁ : G → ℂ) - χ₃ ∧
        β 2 = (χ₃ : G → ℂ) - χ₄ ∧ β 3 = (χ₂ : G → ℂ) - χ₅ + χ₆ ∧
        β 4 = (χ₁ : G → ℂ) - χ₅ + χ₇ ∧
        ∀ ψ ∈ CFSG.BlocksIrr G, ψ ≠ 1 → ψ ≠ (χ₁ : G → ℂ) → ψ ≠ (χ₂ : G → ℂ) →
          ψ ≠ (χ₃ : G → ℂ) → ψ ≠ (χ₄ : G → ℂ) → ψ ≠ (χ₅ : G → ℂ) → ψ ≠ (χ₆ : G → ℂ) →
          ψ ≠ (χ₇ : G → ℂ) → ∀ g : G, Even (orderOf g) → ψ g = 0
    commutator G = ⊤ ∧
    Xor
      (Nat.card G = 7920 ∧
        ∃ χ₁ χ₂ χ₃ χ₄ χ₅ χ₆ χ₇ : CFSG.BlocksIrr G, identities χ₁ χ₂ χ₃ χ₄ χ₅ χ₆ χ₇ ∧
          ![(χ₁ : G → ℂ) 1, (χ₂ : G → ℂ) 1, (χ₃ : G → ℂ) 1, (χ₄ : G → ℂ) 1, (χ₅ : G → ℂ) 1,
            (χ₆ : G → ℂ) 1, (χ₇ : G → ℂ) 1] = ![10, 11, 10, 10, 55, 44, 45] ∧
          (∃ ψ₁ ∈ CFSG.BlocksIrr G, ∃ ψ₂ ∈ CFSG.BlocksIrr G, ψ₁ ≠ ψ₂ ∧ ψ₁ 1 = 16 ∧ ψ₂ 1 = 16 ∧
            ∀ ψ ∈ CFSG.BlocksIrr G, ψ = 1 ∨ ψ = (χ₁ : G → ℂ) ∨ ψ = (χ₂ : G → ℂ) ∨
              ψ = (χ₃ : G → ℂ) ∨ ψ = (χ₄ : G → ℂ) ∨ ψ = (χ₅ : G → ℂ) ∨ ψ = (χ₆ : G → ℂ) ∨
              ψ = (χ₇ : G → ℂ) ∨ ψ = ψ₁ ∨ ψ = ψ₂) ∧
          (irreducibles_finite G).toFinset.val.map (fun ψ => ψ 1) =
            ({1, 10, 10, 10, 11, 16, 16, 44, 45, 55} : Multiset ℂ) ∧
          Nat.card (ConjClasses G) = 10)
      (Nat.card G = 5616 ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSL 3 3 1 ∧
        ∃ χ₁ χ₂ χ₃ χ₄ χ₅ χ₆ χ₇ : CFSG.BlocksIrr G, identities χ₁ χ₂ χ₃ χ₄ χ₅ χ₆ χ₇ ∧
          ![(χ₁ : G → ℂ) 1, (χ₂ : G → ℂ) 1, (χ₃ : G → ℂ) 1, (χ₄ : G → ℂ) 1, (χ₅ : G → ℂ) 1,
            (χ₆ : G → ℂ) 1, (χ₇ : G → ℂ) 1] = ![26, 27, 26, 26, 39, 12, 13] ∧
          (irreducibles_finite G).toFinset.val.map (fun ψ => ψ 1) =
            ({1, 12, 13, 16, 16, 16, 16, 26, 26, 26, 27, 39} : Multiset ℂ) ∧
          Nat.card (ConjClasses G) = 12) := by
  intro C Φ β identities
  obtain ⟨hperf, hxor⟩ :=
    exact_GL2_centralizer_order_alternatives_core hinv t ht π a p b ha hp hb hbz φ hφirr hφ
  refine ⟨hperf, ?_⟩
  rcases hxor with ⟨hA, hnB⟩ | ⟨hB, hnA⟩
  · exact Or.inl ⟨hA, fun hB => hnB ⟨hB.1, hB.2.2⟩⟩
  · obtain ⟨hG, χ₁, χ₂, χ₃, χ₄, χ₅, χ₆, χ₇, hids, hdeg, hmset, hcls⟩ := hB
    obtain ⟨hnd, h1, h2, h3, h4, h5, h6, h7, -, -, -, -, -, hvanish⟩ := id hids
    obtain ⟨S⟩ := Sylow.nonempty (p := 2) (G := G)
    have hvanS : ∀ ψ ∈ CFSG.BlocksIrr G, ψ ≠ 1 → ψ ≠ (χ₁ : G → ℂ) → ψ ≠ (χ₂ : G → ℂ) →
        ψ ≠ (χ₃ : G → ℂ) → ψ ≠ (χ₄ : G → ℂ) → ψ ≠ (χ₅ : G → ℂ) → ψ ≠ (χ₆ : G → ℂ) →
        ψ ≠ (χ₇ : G → ℂ) → ∀ s ∈ (S : Subgroup G), s ≠ 1 → ψ s = 0 :=
      fun ψ hψ e0 e1 e2 e3 e4 e5 e6 e7 s hs hs1 =>
        hvanish ψ hψ e0 e1 e2 e3 e4 e5 e6 e7 s (even_orderOf_of_mem_sylow_two S hs hs1)
    obtain ⟨-, -, -, -, -, hmodel⟩ := seven_character_sylow_support_classical_recognition hG S
      χ₁ χ₂ χ₃ χ₄ χ₅ χ₆ χ₇ hnd h1 h2 h3 h4 h5 h6 h7 hdeg hvanS
    exact Or.inr ⟨⟨hG, (hmodel hinv t ht ⟨π⟩).1, χ₁, χ₂, χ₃, χ₄, χ₅, χ₆, χ₇, hids, hdeg,
      hmset, hcls⟩, hnA⟩

end CFSG.Semidihedral.GL2Recognition
