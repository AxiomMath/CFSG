module

public import CFSG.Quasithin.Background.GoldschmidtRankOneUnitaryTwo

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open

theorem l514c_center_eq_bot_of_two_trans {G Ω : Type*} [Group G] [Finite Ω] (rho : G →* Equiv.Perm Ω)
    (hinj : Function.Injective rho) (h3 : 3 ≤ Nat.card Ω)
    (h2 : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ g : G, rho g a = c ∧ rho g b = d) :
    Subgroup.center G = ⊥ := by
  classical
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  apply hinj
  rw [map_one]
  ext a
  by_contra hne
  have hne' : rho z a ≠ a := fun h => hne (by simpa using h)
  obtain ⟨c, hca, hcz⟩ : ∃ c : Ω, c ≠ a ∧ c ≠ rho z a := by
    by_contra hall
    push_neg at hall
    have := Fintype.ofFinite Ω
    have hsub : (Finset.univ : Finset Ω) ⊆ {a, rho z a} := fun c _ => by
      by_cases hc : c = a
      · simp [hc]
      · simp [hall c hc]
    have h1 := (Finset.card_le_card hsub).trans Finset.card_le_two
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at h1
    omega
  obtain ⟨g, hg1, hg2⟩ := h2 a (rho z a) a c (Ne.symm hne') (Ne.symm hca)
  have hcomm : g * z = z * g := (Subgroup.mem_center_iff.1 hz g)
  have := congrArg (fun f => rho f a) hcomm
  simp only [map_mul, Equiv.Perm.mul_apply, hg1, hg2] at this
  exact hcz this

theorem l514c_center_statedProj_su_two {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ 1) ^ 2) :
    Subgroup.center (StatedProj (StatedSU 3 (2 ^ 1) F)) = ⊥ := by
  obtain ⟨σ, hσ, hfix, ⟨e⟩⟩ := CFSG.Quasithin.exists_statedProj_equiv_psu (n := 1) one_ne_zero hF
  have H := CFSG.BenderSuzuki.External.huppert_II_10_12
    (RankTwoShapes.antidiagonalHermitianForm σ hσ) (2 ^ 1) hF hfix rfl
  dsimp only at H
  obtain ⟨hΩ, rho, pinf, hinj, -, -, -, h2t, -, -⟩ := H
  have hc := l514c_center_eq_bot_of_two_trans rho hinj (by rw [hΩ]; norm_num) h2t
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have : e z ∈ Subgroup.center _ := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    apply e.symm.injective
    simp [hz (e.symm g)]
  rw [hc, Subgroup.mem_bot] at this
  simpa using this

end CFSG.HardMathSupport.Solomon.Coordinator
