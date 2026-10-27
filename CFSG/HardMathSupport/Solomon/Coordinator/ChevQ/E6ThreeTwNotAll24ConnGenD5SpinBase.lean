module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenD5Pos
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTwoDBase
public import CFSG.RankThree.Lattice.SteinbergBIE6QplusFold

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.LieType.Universal.Spin

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000


section Transport

theorem d5_base_form_of_enum {Ψ : Set (Fin Tag.E6.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    {v : WeylGroup Tag.E6} {Jf : Finset (Fin Tag.E6.rank)} (n : Fin 5 → Fin Tag.E6.rank)
    (hJn : ∀ j, j ∈ Jf ↔ ∃ i, n i = j)
    (hcart : ∀ i j, Tag.E6.cartan (n i) (n j) = cartanD 5 i j)
    (hΨv : Ψ = (fun α => v • α) '' parabolicRoots Tag.E6 (↑Jf : Set (Fin Tag.E6.rank)))
    (ε : simpleRoots Ψ ≃ Fin 5)
    (hε : ∀ β γ : simpleRoots Ψ, corootPair (β : Fin Tag.E6.rank → ℤ) γ =
      cartanD 5 (ε β) (ε γ)) :
    ∃ w : WeylGroup Tag.E6,
      Ψ = (fun α => w • α) '' parabolicRoots Tag.E6 (↑Jf : Set (Fin Tag.E6.rank)) ∧
      simpleRoots Ψ = Jf.image fun j => w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) := by
  have hsl : ∀ β ∈ Ψ, iform β β = 2 := fun β hβ => by
    rw [← dotProduct_mulVec_eq_iform]
    exact rootForm_self (Or.inr (Or.inl rfl)) (hΨ.isRoot β hβ)
  have hbΨ : ∀ i, v • (Pi.single (n i) 1 : Fin Tag.E6.rank → ℤ) ∈ Ψ := fun i => by
    rw [hΨv]
    exact ⟨Pi.single (n i) 1, single_mem_parabolicRoots (Finset.mem_coe.2 ((hJn _).2 ⟨i, rfl⟩)),
      rfl⟩
  have hbM : ∀ i j, iform (v • (Pi.single (n i) 1 : Fin Tag.E6.rank → ℤ))
      (v • (Pi.single (n j) 1 : Fin Tag.E6.rank → ℤ)) = cartanD 5 i j := fun i j => by
    rw [iform_smul, CFSG.RankThree.Lattice.iform_single_single_E6', hcart]
  have hdiag : ∀ i : Fin 5, cartanD 5 i i = 2 := by decide
  have hoff : ∀ i j : Fin 5, i ≠ j → cartanD 5 i j ≠ 2 := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  obtain ⟨u, hu, π, -, hub⟩ := CompsPTwoDBase.exists_weyl_base_transport hΨ ε hsl
    (M := cartanD 5) hε hdiag hoff (fun i => v • (Pi.single (n i) 1 : Fin Tag.E6.rank → ℤ))
    hbΨ hbM
  refine ⟨u * v, ?_, ?_⟩
  · ext γ
    constructor
    · intro hγ
      have hinv : u⁻¹ • γ ∈ Ψ := smul_mem_of_mem_componentWeylGroup hΨ (inv_mem hu) γ hγ
      rw [hΨv] at hinv
      obtain ⟨α, hα, hαγ⟩ := hinv
      refine ⟨α, hα, ?_⟩
      show (u * v) • α = γ
      rw [mul_smul]
      have hαγ' : v • α = u⁻¹ • γ := hαγ
      rw [hαγ', smul_inv_smul]
    · rintro ⟨α, hα, hαγ⟩
      have hαγ' : (u * v) • α = γ := hαγ
      have h : v • α ∈ Ψ := by
        rw [hΨv]
        exact ⟨α, hα, rfl⟩
      rw [← hαγ', mul_smul]
      exact smul_mem_of_mem_componentWeylGroup hΨ hu _ h
  · ext β
    simp only [Finset.mem_image]
    constructor
    · intro hβ
      refine ⟨n (π.symm (ε ⟨β, hβ⟩)), (hJn _).2 ⟨_, rfl⟩, ?_⟩
      have h1 : u • (v • (Pi.single (n (π.symm (ε ⟨β, hβ⟩))) 1 : Fin Tag.E6.rank → ℤ)) =
          (ε.symm (π (π.symm (ε ⟨β, hβ⟩))) : Fin Tag.E6.rank → ℤ) := hub _
      rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply] at h1
      rw [mul_smul]
      exact h1
    · rintro ⟨j, hj, rfl⟩
      obtain ⟨i, rfl⟩ := (hJn j).1 hj
      have h1 : u • (v • (Pi.single (n i) 1 : Fin Tag.E6.rank → ℤ)) =
          (ε.symm (π i) : Fin Tag.E6.rank → ℤ) := hub i
      rw [mul_smul, h1]
      exact (ε.symm (π i)).2

end Transport

section Native

theorem d5_rightInverse_A : ∃ ν : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ,
    ∀ j₀ j : Fin Tag.E6.rank, 1 ≤ j₀.val → 1 ≤ j.val →
      ∑ k, Tag.E6.cartan j k * ν j₀ k = if j = j₀ then 1 else 0 :=
  ⟨![![0, 0, 0, 0, 0, 0], ![1, 2, 2, 3, 2, 1], ![-1, 0, 0, 0, 0, 0], ![-2, 0, -1, 0, 0, 0],
    ![0, 1, 1, 2, 2, 1], ![-2, -1, -2, -2, -1, 0]], by decide⟩

theorem d5_rightInverse_B : ∃ ν : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ,
    ∀ j₀ j : Fin Tag.E6.rank, j₀.val ≤ 4 → j.val ≤ 4 →
      ∑ k, Tag.E6.cartan j k * ν j₀ k = if j = j₀ then 1 else 0 :=
  ⟨![![0, -1, -1, -2, -2, -2], ![1, 2, 2, 3, 2, 1], ![1, 1, 2, 2, 1, 0], ![0, 0, 0, 0, -1, -2],
    ![0, 0, 0, 0, 0, -1], ![0, 0, 0, 0, 0, 0]], by decide⟩

theorem d5_base_form {Ψ : Set (Fin Tag.E6.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    {v : WeylGroup Tag.E6} {J : Set (Fin Tag.E6.rank)} (hJ : J = d5NodesA ∨ J = d5NodesB)
    (hΨv : Ψ = (fun α => v • α) '' parabolicRoots Tag.E6 J)
    (ε : simpleRoots Ψ ≃ Fin 5)
    (hε : ∀ β γ : simpleRoots Ψ, corootPair (β : Fin Tag.E6.rank → ℤ) γ =
      cartanD 5 (ε β) (ε γ)) :
    ∃ (w : WeylGroup Tag.E6) (Jf : Finset (Fin Tag.E6.rank)),
      Ψ = (fun α => w • α) '' parabolicRoots Tag.E6 (↑Jf : Set (Fin Tag.E6.rank)) ∧
      simpleRoots Ψ = Jf.image (fun j => w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) ∧
      ∀ j₀ ∈ Jf, ∃ ν : Fin Tag.E6.rank → ℤ, ∀ j ∈ Jf,
        ∑ k, Tag.E6.cartan j k * ν k = if j = j₀ then 1 else 0 := by
  rcases hJ with rfl | rfl
  · obtain ⟨ν, hν⟩ := d5_rightInverse_A
    have hcoe : (↑(Finset.univ.filter fun j : Fin Tag.E6.rank => 1 ≤ j.val) :
        Set (Fin Tag.E6.rank)) = d5NodesA := by
      ext j
      simp [d5NodesA]
    obtain ⟨w, hw1, hw2⟩ := d5_base_form_of_enum hΨ
      (Jf := Finset.univ.filter fun j : Fin Tag.E6.rank => 1 ≤ j.val)
      (![5, 4, 3, 1, 2] : Fin 5 → Fin Tag.E6.rank) (by decide)
      (by intro i j; fin_cases i <;> fin_cases j <;> decide)
      (by rw [hcoe]; exact hΨv) ε hε
    refine ⟨w, _, hw1, hw2, fun j₀ hj₀ => ⟨ν j₀, fun j hj => ?_⟩⟩
    exact hν j₀ j (by simpa using hj₀) (by simpa using hj)
  · obtain ⟨ν, hν⟩ := d5_rightInverse_B
    have hcoe : (↑(Finset.univ.filter fun j : Fin Tag.E6.rank => j.val ≤ 4) :
        Set (Fin Tag.E6.rank)) = d5NodesB := by
      ext j
      simp [d5NodesB]
    obtain ⟨w, hw1, hw2⟩ := d5_base_form_of_enum hΨ
      (Jf := Finset.univ.filter fun j : Fin Tag.E6.rank => j.val ≤ 4)
      (![0, 2, 3, 1, 4] : Fin 5 → Fin Tag.E6.rank) (by decide)
      (by intro i j; fin_cases i <;> fin_cases j <;> decide)
      (by rw [hcoe]; exact hΨv) ε hε
    refine ⟨w, _, hw1, hw2, fun j₀ hj₀ => ⟨ν j₀, fun j hj => ?_⟩⟩
    exact hν j₀ j (by simpa using hj₀) (by simpa using hj)

end Native

end KSGen

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
