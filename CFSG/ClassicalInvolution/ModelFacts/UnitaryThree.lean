module

public import CFSG.ClassicalInvolution.ModelFacts.Models

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.RootSystem CFSG.LieType.BorelTits Matrix

section Three

variable {F : Type*} [Field F] {σ : F ≃+* F}

@[expose] def fixMid (σ : F ≃+* F) : Subgroup (SU σ 3) where
  carrier := {g | ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ (Pi.single 1 1 : Fin 3 → F) =
    Pi.single 1 1}
  mul_mem' := by
    intro a b ha hb
    change (((a : GL (Fin 3) F) * (b : GL (Fin 3) F) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
      *ᵥ (Pi.single 1 1 : Fin 3 → F) = Pi.single 1 1
    rw [Units.val_mul, ← Matrix.mulVec_mulVec]
    have hb' : ((b : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ (Pi.single 1 1 : Fin 3 → F) =
      Pi.single 1 1 := hb
    rw [hb']
    exact ha
  one_mem' := by
    show (((1 : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ (Pi.single 1 1 : Fin 3 → F) =
      Pi.single 1 1
    rw [Units.val_one, Matrix.one_mulVec]
  inv_mem' := by
    intro a ha
    have ha' : ((a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ (Pi.single 1 1 : Fin 3 → F) =
      Pi.single 1 1 := ha
    show ((((a : GL (Fin 3) F))⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
      (Pi.single 1 1 : Fin 3 → F) = Pi.single 1 1
    conv_lhs => rw [← ha']
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem longRootHom_range_le_fixMid {i : Fin 3} (hi : i ≠ Fin.rev i) :
    (longRootHom σ hi).range ≤ fixMid σ := by
  rintro _ ⟨c, rfl⟩
  change (longRootMatrix i (c.toAdd : F)) *ᵥ (Pi.single 1 1 : Fin 3 → F) = Pi.single 1 1
  rw [longRootMatrix, Matrix.add_mulVec, Matrix.one_mulVec]
  have : Fin.rev i ≠ 1 := by
    intro h
    apply hi
    rw [h]
    fin_cases i <;> simp_all [Fin.rev]
  ext a
  simp [Pi.single_apply, this]

variable (hσ : ∀ c, σ (σ c) = c)

theorem rootGroup_le_fixMid {γ : Fin (3 / 2) → ℤ}
    (hγ : ∀ i : Fin 3, i ≠ Fin.rev i → weight 3 i ≠ toStd 3 γ) :
    rootGroup σ hσ 3 γ ≤ fixMid σ := by
  unfold rootGroup
  refine sup_le (sup_le ?_ ?_) ?_
  · refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => iSup_le fun hi =>
      iSup_le fun hj => iSup_le fun hji => iSup_le fun _ => ?_
    exfalso
    fin_cases i <;> fin_cases j <;> simp_all [Fin.rev]
  · exact iSup_le fun i => iSup_le fun hi => iSup_le fun _ => longRootHom_range_le_fixMid hi
  · refine iSup_le fun i => iSup_le fun k => iSup_le fun hi => iSup_le fun hik =>
      iSup_le fun hk => iSup_le fun hw => ?_
    exact absurd hw (hγ i hi)

@[expose] noncomputable def heisSU (a b : F) (hab : b + σ b + σ a * a = 0) : SU σ 3 :=
  ⟨⟨heisenbergMatrix σ 0 1 a b, heisenbergMatrix σ 0 1 (-a) (-b - a * σ a),
    by
      rw [heisenbergMatrix_mul σ (by decide) (by decide) (by decide), map_neg, add_neg_cancel,
        show b + (-b - a * σ a) - a * -σ a = 0 by ring, heisenbergMatrix_zero],
    by
      rw [heisenbergMatrix_mul σ (by decide) (by decide) (by decide), neg_add_cancel,
        show -b - a * σ a + b - -a * σ a = 0 by ring, heisenbergMatrix_zero]⟩,
    det_heisenbergMatrix σ (by decide) (by decide) (by decide) a b,
    heisenbergMatrix_isometry σ hσ (by decide) (by decide) (by decide) hab⟩

theorem heisSU_not_mem_fixMid (a b : F) (hab : b + σ b + σ a * a = 0) (ha : a ≠ 0) :
    heisSU hσ a b hab ∉ fixMid σ := by
  intro h
  have h' : (heisenbergMatrix σ 0 1 a b) *ᵥ (Pi.single 1 1 : Fin 3 → F) = Pi.single 1 1 := h
  have := congrFun h' 0
  simp [heisenbergMatrix] at this
  exact ha this

theorem not_even_three : ¬ Even 3 := by decide

theorem weight_ne_toStd_pos :
    ∀ i : Fin 3, i ≠ Fin.rev i →
      weight 3 i ≠ toStd 3 (2 • (Pi.single (⟨0, by decide⟩ : Fin (3 / 2)) 1 :
        Fin (3 / 2) → ℤ)) := by
  intro i hi h
  have := congrFun h ⟨0, by decide⟩
  fin_cases i <;> simp [weight, toStd, not_even_three] at this hi

theorem weight_ne_toStd_neg :
    ∀ i : Fin 3, i ≠ Fin.rev i →
      weight 3 i ≠ toStd 3 (-(2 • (Pi.single (⟨0, by decide⟩ : Fin (3 / 2)) 1 :
        Fin (3 / 2) → ℤ))) := by
  intro i hi h
  have := congrFun h ⟨0, by decide⟩
  fin_cases i <;> simp [weight, toStd, not_even_three] at this hi

end Three

section Datum

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

theorem map_conj_ne_top_of_isLongestRoot_three (hF : Nat.card F = (p ^ f) ^ 2)
    (hlong : IsLongestRoot (rootDatum hF 3)
      (2 • Pi.single (⟨0, by show 0 < 3 / 2; decide⟩ : Fin (rootDatum hF 3).rank) 1))
    {γ : Fin (rootDatum hF 3).rank → ℤ} (hγ : IsLongestRoot (rootDatum hF 3) γ)
    (g : SU (unitaryInvolution F p f) 3) :
    ((rootDatum hF 3).rootGroup γ ⊔ (rootDatum hF 3).rootGroup (-γ)).map
      (MulAut.conj g).toMonoidHom ≠ ⊤ := by
  have hσ := unitaryInvolution_involutive hF
  let i₀ : Fin (rootDatum hF 3).rank := ⟨0, by show 0 < 3 / 2; decide⟩
  have hsub : ∀ i j : Fin (rootDatum hF 3).rank, i = j := fun i j =>
    Fin.ext (by
      have hi : i.val < 3 / 2 := i.2
      have hj : j.val < 3 / 2 := j.2
      omega)
  have hcases : γ = 2 • Pi.single i₀ 1 ∨ γ = -(2 • Pi.single i₀ 1) := by
    have hl := hγ.lenSq_eq hlong
    rcases hγ.mem with ⟨w, i, rfl⟩ | ⟨w, i, hi, rfl⟩
    · exfalso
      rw [lenSq_weylAction, lenSq_single, lenSq_two_nsmul, lenSq_single, hsub i i₀] at hl
      have := symmetrizer_pos (rootDatum hF 3).isFiniteType i₀
      linarith
    · rw [hsub i i₀]
      rcases weylAction_single_eq_or_neg (rootDatum hF 3).isFiniteType hsub i₀ w with h | h
      · left
        rw [h]
      · right
        rw [h, smul_neg]
  have hle : (rootDatum hF 3).rootGroup γ ⊔ (rootDatum hF 3).rootGroup (-γ) ≤
      fixMid (unitaryInvolution F p f) := by
    have h1 := rootGroup_le_fixMid (σ := unitaryInvolution F p f) hσ
      weight_ne_toStd_pos
    have h2 := rootGroup_le_fixMid (σ := unitaryInvolution F p f) hσ
      weight_ne_toStd_neg
    rcases hcases with rfl | rfl
    · exact sup_le h1 h2
    · rw [neg_neg]
      exact sup_le h2 h1
  intro htop
  have h1 : (fixMid (unitaryInvolution F p f)).map
      (MulAut.conj g).toMonoidHom = ⊤ :=
    eq_top_iff.2 (htop ▸ Subgroup.map_mono hle)
  have h2 := eq_top_of_map_conj_eq_top h1
  obtain ⟨b, hb⟩ := exists_add_unitaryInvolution_eq hF
    (a := -1) (by rw [map_neg, map_one])
  have hab : b + unitaryInvolution F p f b +
      unitaryInvolution F p f 1 * 1 = 0 := by
    rw [hb, map_one]
    ring
  exact heisSU_not_mem_fixMid hσ 1 b hab one_ne_zero (h2 ▸ Subgroup.mem_top _)

end Datum

theorem fundamentalSubgroups_ne_top_PSU_three (p f : ℕ) (hp : p.Prime)
    (hadm : StatedLieAdmissible .PSU 3 p f) :
    ∀ R ∈ fundamentalSubgroups .PSU (modelUniv .PSU 3 p f hp).D, R ≠ ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  have hf : 1 ≤ f := hadm.2.1
  have hF := card_galoisField_two_mul p f hf
  have hlong := isLongestRoot_two_nsmul_single_PSU 3 p f hp hadm (by decide)
  revert hlong
  rw [modelUniv_PSU hf]
  intro hlong R hR
  obtain ⟨g, γ, hγ, rfl⟩ := hR
  rcases hγ with hγ | ⟨h, -⟩ | ⟨h, -⟩
  · exact map_conj_ne_top_of_isLongestRoot_three hF
      (hlong ⟨0, by show 0 < 3 / 2; decide⟩ (by show 0 + 1 = 3 / 2; decide)) hγ g
  · exact absurd h (by decide)
  · exact absurd h (by decide)

theorem fundamentalIsWhole_modelUniv (t : StatedLieTag) (n p f : ℕ) (hp : p.Prime)
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p f) :
    ((t = .PSL ∧ n = 2) → ∀ R ∈ fundamentalSubgroups t (modelUniv t n p f hp).D, R = ⊤) ∧
      (¬ (t = .PSL ∧ n = 2) →
        ∀ R ∈ fundamentalSubgroups t (modelUniv t n p f hp).D, R ≠ ⊤) := by
  refine ⟨?_, fun h1 => ?_⟩
  · rintro ⟨rfl, rfl⟩
    exact fundamentalSubgroups_eq_top_PSL_two p f hp hadm
  · by_cases h2 : t = .PSU ∧ n = 3
    · obtain ⟨rfl, rfl⟩ := h2
      exact fundamentalSubgroups_ne_top_PSU_three p f hp hadm
    · exact fundamentalSubgroups_ne_top t n p f hp hfund hadm h1 h2

@[expose] def FundamentalIsWhole : Prop :=
  ∀ (t : StatedLieTag) (n p f : ℕ) (hp : p.Prime), IsFundTag t → StatedLieAdmissible t n p f →
    ((t = .PSL ∧ n = 2) → ∀ R ∈ fundamentalSubgroups t (modelUniv t n p f hp).D, R = ⊤) ∧
      (¬ (t = .PSL ∧ n = 2) →
        ∀ R ∈ fundamentalSubgroups t (modelUniv t n p f hp).D, R ≠ ⊤)

theorem fundamentalIsWhole : FundamentalIsWhole := fun t n p f hp hfund hadm =>
  fundamentalIsWhole_modelUniv t n p f hp hfund hadm

end CFSG.ClassicalInvolution.ModelFacts
