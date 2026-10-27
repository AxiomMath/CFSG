module

public import CFSG.ClassicalInvolution.Q3.Q3EXOrth
public import CFSG.ClassicalInvolution.Uniform.U8Shape
public import CFSG.ClassicalInvolution.RouteD.ExoticD4Model

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W.EX

open CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
  CFSG.ClassicalInvolution.ModelFacts.TG3 CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

local notation "𝔽₃" => GaloisField 3 1


section Geometry

variable {V : Type} [AddCommGroup V] [Module 𝔽₃ V] {Q : QuadraticForm 𝔽₃ V}

theorem not_commutes_self3 {L : Subgroup (V ≃ₗ[𝔽₃] V)} {i : V ≃ₗ[𝔽₃] V}
    (h : IsFundamental Q L i) : ¬ Commutes L L := by
  intro hc
  obtain ⟨e⟩ := h.nonempty_mulEquiv
  apply Uniform.sl2_exists_not_comm (GaloisField 3 1)
  intro A B
  apply e.injective
  rw [map_mul, map_mul]
  exact Subtype.ext (hc _ (e A).2 _ (e B).2)

end Geometry

section Central

variable {X Y : Type} [Group X] [Finite X] [Group Y]

theorem eq_of_map_eq_gen3 (π : X →* Y) (hker : π.ker ≤ Subgroup.center X)
    (hk3 : ∀ x ∈ π.ker, x ^ 3 = 1 → x = 1) {A B : Subgroup X} (hA : ModelFacts.Gen3 A)
    (hB : ModelFacts.Gen3 B) (h : A.map π = B.map π) : A = B :=
  Uniform.eq_of_map_eq_of_gen3 π hker hk3 hA hB h

theorem commutes_map_iff_gen3 (π : X →* Y) (hker : π.ker ≤ Subgroup.center X)
    (hk3 : ∀ x ∈ π.ker, x ^ 3 = 1 → x = 1) {A B : Subgroup X} (hA : ModelFacts.Gen3 A) :
    Commutes (A.map π) (B.map π) ↔ Commutes A B := by
  constructor
  · intro h a ha b hb
    have h1 : ∀ a' ∈ A, π a' * π b = π b * π a' := fun a' ha' =>
      h (π a') ⟨a', ha', rfl⟩ (π b) ⟨b, hb, rfl⟩
    exact ModelFacts.commute_of_map_commute_of_gen3 π hker hk3 hA h1 a ha
  · rintro h _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, h x hx y hy]

end Central

section Ctx

variable {ι : Type} [Fintype ι] {Q : QuadraticForm 𝔽₃ (ι → 𝔽₃)}
  {𝓕 : Set (Subgroup (spinGroup Q))}

theorem cliqueFour_of_ctx3 [Finite (spinGroup Q)] (c : SpinCtx3 Q 𝓕)
    (hconj : ∀ R ∈ 𝓕, ∀ g : spinGroup Q, conjSub g R ∈ 𝓕)
    (hsingle : ∀ R ∈ 𝓕, ∀ R' ∈ 𝓕, ∃ g : spinGroup Q, R' = conjSub g R)
    (hdim : Module.finrank 𝔽₃ (ι → 𝔽₃) = 8) :
    CliqueFour (fun R R' : ↥𝓕 => Commutes R.1 R'.1) := by
  intro F₁ F₂ F₃ n12 n13 n23 c12 c13 c23
  have hodd := odd_natCard_galoisField_three
  have hR₀ : F₁.1 ∈ 𝓕 := F₁.2
  obtain ⟨fr₀, himg⟩ := c.hframe _ hR₀
  have hperp : 2 ≤ Module.finrank 𝔽₃ fr₀.perp := by
    have h1 := ModelFacts.finrank_perp_add_four fr₀
    omega
  have hpos : 0 < Module.finrank 𝔽₃ (ι → 𝔽₃) := by omega
  have : Nontrivial (ι → 𝔽₃) := Module.finrank_pos_iff.mp hpos
  have hcorr := spin_fund_correspondence hodd c.hQ hR₀ hconj (fun R hR => hsingle _ hR₀ R hR)
    fr₀ himg hperp
  have hker := ker_spinAction_le_center Q
  have hk3 : ∀ x ∈ (spinAction Q).ker, x ^ 3 = 1 → x = 1 := by
    intro x hx h3
    have h2 : x * x = 1 := c.hker2 x hx
    have h : x ^ 3 = x ^ 2 * x := pow_succ x 2
    rw [h, pow_two, h2, one_mul] at h3
    exact h3
  have hc : ∀ {A B : ↥𝓕}, Commutes A.1 B.1 →
      Commutes (A.1.map (spinAction Q)) (B.1.map (spinAction Q)) := fun {A B} h =>
    (commutes_map_iff_gen3 _ hker hk3 (c.hG3 _ A.2)).mpr h
  have hne : ∀ {A B : ↥𝓕}, A ≠ B →
      A.1.map (spinAction Q) ≠ B.1.map (spinAction Q) := fun {A B} h e =>
    h (Subtype.ext (eq_of_map_eq_gen3 _ hker hk3 (c.hG3 _ A.2) (c.hG3 _ B.2) e))
  obtain ⟨R₄', ⟨i₄, h₄⟩, d1, d2, d3, k1, k2, k3', hall⟩ := exists_k4_of_three hodd c.hQ hdim
    (hcorr.1 _ F₁.2) (hcorr.1 _ F₂.2) (hcorr.1 _ F₃.2) (hne n12) (hne n13) (hne n23) (hc c12)
    (hc c13) (hc c23)
  obtain ⟨R₄, hR₄, hR₄π⟩ := hcorr.2 R₄' ⟨i₄, h₄⟩
  have hfin : ∀ {A : ↥𝓕}, Commutes (A.1.map (spinAction Q)) R₄' → Commutes A.1 R₄ :=
    fun {A} h => (commutes_map_iff_gen3 _ hker hk3 (c.hG3 _ A.2)).mp (hR₄π ▸ h)
  refine ⟨⟨R₄, hR₄⟩, ?_, ?_, ?_, hfin k1, hfin k2, hfin k3', ?_⟩
  · intro h
    exact d1 (hR₄π.symm.trans (by rw [← h]))
  · intro h
    exact d2 (hR₄π.symm.trans (by rw [← h]))
  · intro h
    exact d3 (hR₄π.symm.trans (by rw [← h]))
  · rintro ⟨R', hR'⟩ hcom
    have hcom' := (commutes_map_iff_gen3 _ hker hk3 (c.hG3 _ F₁.2)).mpr hcom
    rcases hall (R'.map (spinAction Q)) (hcorr.1 R' hR') (Or.inl hcom') with e | e | e | e
    · exact absurd (e ▸ hcom') (not_commutes_self3 (hcorr.1 _ F₁.2).choose_spec)
    · exact Or.inl (Subtype.ext (eq_of_map_eq_gen3 _ hker hk3 (c.hG3 _ hR') (c.hG3 _ F₂.2) e))
    · exact Or.inr (Or.inl (Subtype.ext
        (eq_of_map_eq_gen3 _ hker hk3 (c.hG3 _ hR') (c.hG3 _ F₃.2) e)))
    · exact Or.inr (Or.inr (Subtype.ext
        (eq_of_map_eq_gen3 _ hker hk3 (c.hG3 _ hR') (c.hG3 _ hR₄) (e.trans hR₄π.symm))))

end Ctx

section Model

theorem cliqueFour_fund_plus_four3 (hadm : StatedLieAdmissible .POmegaPlus 4 3 1) :
    CliqueFour (fun R R' : ↥(fundamentalSubgroups .POmegaPlus
      (modelUniv .POmegaPlus 4 3 1 Fact.out).D) => Commutes R.1 R'.1) := by
  have hn3 : 3 ≤ 4 := by norm_num
  have h3 : (3 : ℕ) ^ 1 = 3 := by norm_num
  have hM : modelUniv .POmegaPlus 4 3 1 Fact.out =
      ⟨spinGroup (quadPlus 4 (GaloisField 3 1)), plusDatum 4 (GaloisField 3 1) hn3⟩ :=
    (rfl : modelUniv .POmegaPlus 4 3 1 Fact.out =
      ModelFacts.modelUniv .POmegaPlus 4 3 1 Fact.out).trans (ModelFacts.modelUniv_POmegaPlus hn3)
  have hsingle : FundamentalSingleClass .POmegaPlus
      (modelUniv .POmegaPlus 4 3 1 Fact.out).D :=
    ModelFacts.fundamentalSingleClass .POmegaPlus 4 3 1 Fact.out trivial hadm (by decide)
      (by decide)
  have hG3 : ∀ R ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 4 3 1 Fact.out).D,
      ModelFacts.Gen3 R := fun R hR =>
    ModelFacts.gen3_of_mem_longestFundamental3 (t := .POmegaPlus) h3 trivial hadm (by decide)
      (by decide)
      (ModelFacts.fundamentalSubgroups_subset_longest (by decide) (by decide) _ hR)
  have hlong : ∀ k : Fin (modelUniv .POmegaPlus 4 3 1 Fact.out).D.rank,
      IsLongestRoot (modelUniv .POmegaPlus 4 3 1 Fact.out).D (Pi.single k 1) :=
    fun k => ModelFacts.isLongestRoot_single .POmegaPlus 4 3 1 Fact.out trivial hadm k trivial
  have hsl2 : ∀ R ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 4 3 1 Fact.out).D,
      Nonempty (R ≃* SL(2, GaloisField 3 1)) := fun R hR =>
    ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups (by norm_num) (t := .POmegaPlus)
      trivial hadm (by decide) (by decide) hR
  have hfin : Finite (modelUniv .POmegaPlus 4 3 1 Fact.out).K :=
    ModelFacts.finite_modelUniv (t := .POmegaPlus) (by norm_num) Nat.prime_three trivial hadm
  generalize modelUniv .POmegaPlus 4 3 1 Fact.out = M at hM hsingle hG3 hlong hsl2 hfin ⊢
  subst hM
  have : Finite (spinGroup (quadPlus 4 (GaloisField 3 1))) := hfin
  have ctx := spinCtx3_plus hn3 (le_refl 4) hsingle hlong hG3 hsl2
  have hdim : Module.finrank (GaloisField 3 1) (Fin 4 ⊕ Fin 4 → GaloisField 3 1) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  exact cliqueFour_of_ctx3 ctx (fun R hR g => conjSub_mem_fundamentalSubgroups hR g)
    (fun R hR R' hR' => hsingle _ hR R' hR') hdim

theorem cliqueFour_of_kind {c : CompData} (hc : c = CompData.model .POmegaPlus 4) :
    CliqueFour (fun R R' : ↥c.fund => Commutes R.1 R'.1) := by
  subst hc
  exact cliqueFour_fund_plus_four3 ⟨Nat.prime_three, le_rfl, le_rfl⟩

end Model

end CFSG.ClassicalInvolution.Q3.Q3W.EX
