module

public import CFSG.LocalAnalysis.ComponentClassification.FiveCatC5OmegaBasic
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatC5PSLBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinRow

public section

namespace CFSG.ComponentClassification.SolMax.FiveCat.C5Omega

open CFSG Subgroup CFSG.Open
open CFSG.ComponentClassification.CatLeafProof.X10Lin
open CFSG.ComponentClassification.SolMax.FiveCat.C5PSL (eq_psl_two_one_of_a5)

theorem le_four_of_mem_orthTuples_psl_two_one {d e : ℕ}
    (h : ((.PSL : StatedLieTag), 2, 1) ∈ orthTuples d e) : d ≤ 4 ∧ e = 1 := by
  rcases h with ⟨hd, h⟩ | ⟨hd, h | h⟩ | ⟨hd, h⟩ | ⟨hd, h | h⟩ | ⟨hd, -, h⟩ | ⟨hd, -, h | h⟩
  · have := (Prod.mk.inj (Prod.mk.inj h).2).2
    exact ⟨by omega, by omega⟩
  · have := (Prod.mk.inj (Prod.mk.inj h).2).2
    exact ⟨by omega, by omega⟩
  · have := (Prod.mk.inj (Prod.mk.inj h).2).2
    omega
  · exact absurd (Prod.mk.inj h).1 (by decide)
  · have := (Prod.mk.inj (Prod.mk.inj h).2).1
    omega
  · exact absurd (Prod.mk.inj h).1 (by decide)
  · exact absurd (Prod.mk.inj h).1 (by decide)
  · exact absurd (Prod.mk.inj h).1 (by decide)
  · exact absurd (Prod.mk.inj h).1 (by decide)

theorem le_four_of_modelIn_orthTuples {d e : ℕ} {L : Type} [Group L]
    (h : ModelIn 5 (orthTuples d e) L)
    (hA : Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 5))) : d ≤ 4 ∧ e = 1 := by
  obtain ⟨t, m, e', hT, hadm, hm⟩ := h
  obtain ⟨rfl, rfl, rfl⟩ :=
    eq_psl_two_one_of_a5 (isClassicalTag_of_mem_orthTuples hT) hadm hm hA
  exact le_four_of_mem_orthTuples_psl_two_one hT

section Exists

variable {K W : Type} [Field K] [Finite K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]

theorem exists_component_orthogonal (hodd : Odd (Nat.card K)) (hK3 : Nat.card K ≠ 3)
    (Q : QuadraticForm K W) (hQ : Q.polarBilin.Nondegenerate) (h3 : 3 ≤ Module.finrank K W) :
    ∃ M : Subgroup ↥(TauCeti.QuadraticMap.orthogonalGroup Q), IsComponent M := by
  have hK2 : Nat.card K ≠ 2 := fun h => absurd (h ▸ hodd) (by decide)
  by_cases h5 : 5 ≤ Module.finrank K W
  · exact ⟨commutator _, ComponentClassification.OddSelector.commutator_orthogonalGroup_quasisimple
      hodd Q hQ h5, Subgroup.Normal.isSubnormal inferInstance⟩
  · rcases (show Module.finrank K W = 3 ∨ Module.finrank K W = 4 by omega) with h | h
    · obtain ⟨-, -, -, -, -, -, hq, -⟩ :=
        LocalAnalysis.ComponentInitial.orthogonal_three_derived hodd hK3 Q hQ h
      exact ⟨commutator _, hq, Subgroup.Normal.isSubnormal inferInstance⟩
    · by_cases hS : ∃ S : Submodule K W, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0
      · obtain ⟨-, e, -, -, hsup, hq₁, -, hn₁, -⟩ :=
          LocalAnalysis.ComponentInitial.orthogonal_split_four_derived hK2 hK3 Q hQ h hS
        refine ⟨_, hq₁, ?_⟩
        exact Subgroup.IsSubnormal.trans (hsup ▸ le_sup_left) hn₁.isSubnormal
          (Subgroup.Normal.isSubnormal inferInstance)
      · obtain ⟨-, -, -, -, -, -, -, -, hq, -⟩ :=
          LocalAnalysis.ComponentInitial.orthogonal_nonsplit_four_derived hodd Q hQ h hS
        exact ⟨commutator _, hq, Subgroup.Normal.isSubnormal inferInstance⟩

end Exists

section Prod

variable {K : Type} [Field K] [Finite K] {W₁ W₂ : Type} [AddCommGroup W₁] [Module K W₁]
  [FiniteDimensional K W₁] [AddCommGroup W₂] [Module K W₂] [FiniteDimensional K W₂]

theorem orth_prod_left {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 5 ^ f)
    (Q₁ : QuadraticForm K W₁) (hQ₁ : Q₁.polarBilin.Nondegenerate)
    (Q₂ : QuadraticForm K W₂) (hQ₂ : Q₂.polarBilin.Nondegenerate)
    (hd : 7 ≤ Module.finrank K W₁ + Module.finrank K W₂)
    {M : Subgroup (↥(TauCeti.QuadraticMap.orthogonalGroup Q₁) ×
      ↥(TauCeti.QuadraticMap.orthogonalGroup Q₂))}
    (hM : IsComponent M) (hA : Nonempty (↥M ⧸ center ↥M ≃* alternatingGroup (Fin 5)))
    (h2 : ∀ x ∈ M, x.2 = 1) :
    ∃ M' : Subgroup (↥(TauCeti.QuadraticMap.orthogonalGroup Q₁) ×
      ↥(TauCeti.QuadraticMap.orthogonalGroup Q₂)), IsComponent M' ∧ M' ≠ M := by
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (Nat.prime_five.odd_of_ne_two (by norm_num)).pow
  have hK3 : Nat.card K ≠ 3 := by
    intro h3
    have h5 : 5 ∣ Nat.card K := by
      rw [hK]
      exact dvd_pow_self 5 (by omega)
    rw [h3] at h5
    omega
  obtain ⟨ρ, hρi, hρc, -⟩ := OddClassSelector.restrict_component (MulEquiv.refl _) hM h2
  let eρ : ↥M ≃* ↥ρ.range := MonoidHom.ofInjective hρi
  have hA₁ : Nonempty (↥ρ.range ⧸ center ↥ρ.range ≃* alternatingGroup (Fin 5)) :=
    ⟨(QuotientGroup.congr _ _ eρ (Subgroup.map_center_eq eρ)).symm.trans hA.some⟩
  have h3 : 3 ≤ Module.finrank K W₁ := by
    by_contra hlt
    have hsol : Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup Q₁) :=
      ((CatalogueBOrthogonalAssembly.odd_orthogonal_all_dimensional_isometry_p_components hodd Q₁
        hQ₁).2 (by omega)).1
    exact LocalAnalysis.ComponentInitial.not_isComponent_of_isSolvable _ hρc
  have hmodel := orthogonal_component_models Nat.prime_five (by norm_num) hf hK Q₁ hQ₁ h3 hρc
  obtain ⟨hd4, -⟩ := le_four_of_modelIn_orthTuples hmodel hA₁
  have h3₂ : 3 ≤ Module.finrank K W₂ := by omega
  obtain ⟨C₂, hC₂⟩ := exists_component_orthogonal hodd hK3 Q₂ hQ₂ h3₂
  refine ⟨C₂.map (MonoidHom.inr _ _), isComponent_map_inr hC₂, fun heq => ?_⟩
  apply CatLeafProof.ne_bot_of_isQuasisimple hM.1
  rw [eq_bot_iff]
  intro x hx
  have h1 : x.1 = 1 := by
    have hx' : x ∈ C₂.map (MonoidHom.inr _ _) := heq ▸ hx
    obtain ⟨y, -, rfl⟩ := hx'
    rfl
  exact Subgroup.mem_bot.2 (Prod.ext h1 (h2 x hx))

theorem notOnlyA5_orth_prod {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 5 ^ f)
    (Q₁ : QuadraticForm K W₁) (hQ₁ : Q₁.polarBilin.Nondegenerate)
    (Q₂ : QuadraticForm K W₂) (hQ₂ : Q₂.polarBilin.Nondegenerate)
    (hd : 7 ≤ Module.finrank K W₁ + Module.finrank K W₂) :
    NotOnlyA5 (↥(TauCeti.QuadraticMap.orthogonalGroup Q₁) ×
      ↥(TauCeti.QuadraticMap.orthogonalGroup Q₂)) := by
  intro M hM hA
  rcases LocalAnalysis.ComponentInitial.CentralQuotientLift.fst_eq_or_snd_eq_of_isComponent_prod
      hM with h2 | h1
  · exact orth_prod_left hf hK Q₁ hQ₁ Q₂ hQ₂ hd hM hA h2
  · let e := MulEquiv.prodComm (M := ↥(TauCeti.QuadraticMap.orthogonalGroup Q₁))
      (N := ↥(TauCeti.QuadraticMap.orthogonalGroup Q₂))
    have hM' := LocalCores.isComponent_map_mulEquiv e hM
    have hA' := nonempty_a5_map e hA
    have h2' : ∀ x ∈ M.map e.toMonoidHom, x.2 = 1 := by
      rintro _ ⟨y, hy, rfl⟩
      exact h1 y hy
    obtain ⟨M', hM'c, hne⟩ := orth_prod_left (W₁ := W₂) (W₂ := W₁) hf hK Q₂ hQ₂ Q₁ hQ₁
      (by omega) hM' hA' h2'
    exact exists_component_ne_of_mulEquiv e ⟨M', hM'c, hne⟩

end Prod

end CFSG.ComponentClassification.SolMax.FiveCat.C5Omega
