module

public import CFSG.ClassicalInvolution.Q3.Q3T8AFZ01
public import CFSG.ClassicalInvolution.Uniform.U7Cent

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.G2D4Models
open CFSG.ClassicalInvolution.Asc77.T3Typed (isUniqueInvolution_of_map)
open scoped MatrixGroups commutatorElement


section G2

theorem zLink3_g2_false {Z : Type} [Group Z] [Finite Z] {Ψ : Set (Subgroup Z)} {ι : Type}
    (D : Q3.LieSystemData3 ι Z Ψ) (hΩ : HypOmegaModU (.sl2 3 1) Ψ)
    (hnt : ∀ M ∈ Ψ, ∀ M' ∈ twinSet Ψ M, M' = M) {i : ι}
    (hc : D.kind i = compModel 3 1 .G2 0) {M₁ M₂ : Subgroup Z} (hM₁ : M₁ ∈ Ψ)
    (hM₂ : M₂ ∈ omegaNbr Ψ M₁) {R₁ R₂ : Subgroup (D.kind i).G} (hR₁ : R₁ ∈ (D.kind i).fund)
    (hR₂ : R₂ ∈ (D.kind i).fund) (h1 : M₁ = R₁.map (D.hom i)) (h2 : M₂ = R₂.map (D.hom i)) :
    False := by
  have hker := castHom_ker_le_center hc (D.hom i) (D.ker_le_center i)
  have hinj : Function.Injective (castHom hc (D.hom i)) :=
    RouteD.G2D4.injective_of_ker_le_center (p := 3) (e := 1) (by norm_num) (Or.inl rfl) 0
      le_rfl _ hker
  obtain ⟨R₁', hR₁', e₁⟩ := exists_map_castHom hc (D.hom i) hR₁
  obtain ⟨R₂', hR₂', e₂⟩ := exists_map_castHom hc (D.hom i) hR₂
  let C : G2Comp Ψ :=
    { ψ := castHom hc (D.hom i)
      inj := hinj
      cover := by
        intro L hL
        obtain ⟨l, T, hT, hLT⟩ := D.fundamental L hL
        by_cases hli : l = i
        · subst hli
          obtain ⟨T', hT', hTT'⟩ := exists_map_castHom hc (D.hom l) hT
          exact Or.inl ⟨T', hT', hLT.trans hTT'.symm⟩
        · right
          intro x hx y hy
          rw [hLT] at hx
          obtain ⟨x', -, rfl⟩ := hx
          rw [range_castHom hc] at hy
          obtain ⟨y', rfl⟩ := hy
          exact D.commute l i hli x' y' }
  have hex : ExactMembers Ψ := zLink3_exact hΩ D.card_eq
  have hK : M₁ ∈ C.members := ⟨hM₁, R₁', hR₁', by rw [h1]; exact e₁.symm⟩
  have hM : M₂ ∈ C.members := ⟨hM₂.1, R₂', hR₂', by rw [h2]; exact e₂.symm⟩
  have htw := twin_of_mem_omegaNbr_g2 g2CentralizerInvolution3_proved hΩ hex C hK hM hM₂
  exact hM₂.2.1 (hnt M₁ hM₁ M₂ htw)

end G2

section TD4

variable {X : Type} [Group X] [Finite X]

theorem zLink3_td4_range (hadm : StatedLieAdmissible .trialityD4 0 3 1)
    (ψ : (compModel 3 1 .trialityD4 0).G →* X)
    (hker : ψ.ker ≤ Subgroup.center (compModel 3 1 .trialityD4 0).G)
    {R₁ R₂ : Subgroup (compModel 3 1 .trialityD4 0).G}
    (hQex : ∃ Q : Subgroup X, Q ≤ R₂.map ψ ∧ Nat.card Q = 8 ∧
      Q ≤ Subgroup.normalizer ((R₁.map ψ : Subgroup X) : Set X))
    {z w : X} (hz : IsUniqueInvolution (R₁.map ψ) z) (hw : IsUniqueInvolution (R₂.map ψ) w)
    (hzw : z ≠ w) :
    ψ.range ≤ Subgroup.centralizer ({z} : Set X) ⊔ Subgroup.centralizer ({w} : Set X) ⊔
      Subgroup.centralizer ({z * w} : Set X) := by
  obtain ⟨Q, hQJ, hQ8, hQN⟩ := hQex
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hinj : Function.Injective ψ :=
    RouteD.G2D4.injective_of_ker_le_center hp2 (Or.inr rfl) 0 (le_refl 1) ψ hker
  obtain ⟨c₁, hc₁z, hc₁⟩ := isUniqueInvolution_of_map hinj hz
  obtain ⟨c₂, hc₂w, hc₂⟩ := isUniqueInvolution_of_map hinj hw
  have hcomm : z * w = w * z := zLink3_comm_of_sylow hQJ hQ8 hQN hz hw
  have h12 : c₁ * c₂ = c₂ * c₁ := hinj (by rw [map_mul, map_mul, hc₁z, hc₂w]; exact hcomm)
  have hne : c₁ ≠ c₂ := fun h => hzw (by rw [← hc₁z, ← hc₂w, h])
  have htop := sup_centralizer_eq_top_model_td4 hp2 hadm hc₁.sq hc₂.sq hc₁.ne_one hc₂.ne_one
    hne h12
  have hmap : ∀ (c : (compModel 3 1 .trialityD4 0).G) (a : X), ψ c = a →
      (Subgroup.centralizer ({c} : Set (compModel 3 1 .trialityD4 0).G)).map ψ ≤
        Subgroup.centralizer ({a} : Set X) := by
    rintro c a rfl _ ⟨g, hg, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp hg]
  rw [MonoidHom.range_eq_map, ← htop, Subgroup.map_sup]
  exact le_sup_of_le_left (sup_le_sup (hmap c₁ z hc₁z) (hmap c₂ w hc₂w))

theorem zLink3_td4_class (hadm : StatedLieAdmissible .trialityD4 0 3 1)
    (ψ : (compModel 3 1 .trialityD4 0).G →* X)
    (hker : ψ.ker ≤ Subgroup.center (compModel 3 1 .trialityD4 0).G)
    {R₁ R : Subgroup (compModel 3 1 .trialityD4 0).G}
    (hR₁ : R₁ ∈ (compModel 3 1 .trialityD4 0).fund)
    (hR : R ∈ (compModel 3 1 .trialityD4 0).fund) (h₁ : Nat.card (R₁.map ψ) = 24)
    (h : Nat.card (R.map ψ) = 24) : ∃ g : X, R.map ψ = conjSub g (R₁.map ψ) := by
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hinj : Function.Injective ψ :=
    RouteD.G2D4.injective_of_ker_le_center hp2 (Or.inr rfl) 0 (le_refl 1) ψ hker
  have hcard₁ : Nat.card R₁ = 24 := by
    rw [← Subgroup.card_map_of_injective hinj]
    exact h₁
  have hcard : Nat.card R = 24 := by
    rw [← Subgroup.card_map_of_injective hinj]
    exact h
  by_cases hconj : ∃ g, R = R₁.map (MulAut.conj g).toMonoidHom
  · obtain ⟨g, hg⟩ := hconj
    refine ⟨ψ g, ?_⟩
    have hg' : R = conjSub g R₁ := hg
    rw [hg']
    exact AscQuot.map_conjSub ψ g R₁
  · exact absurd (hcard₁.trans hcard.symm)
      (d4OrdersDiffer 3 .trialityD4 0 1 rfl hadm R₁ hR₁ R hR hconj)

end TD4

section M11

theorem zLink3_m11_false {X : Type} [Group X] [Finite X] (ψ : Q3.CompData.m11.G →* X)
    (hker : ψ.ker ≤ Subgroup.center Q3.CompData.m11.G) {R₁ R₂ : Subgroup Q3.CompData.m11.G}
    (h24₁ : Nat.card (R₁.map ψ) = 24)
    (hQex : ∃ Q : Subgroup X, Q ≤ R₂.map ψ ∧ Nat.card Q = 8 ∧
      Q ≤ Subgroup.normalizer ((R₁.map ψ : Subgroup X) : Set X))
    (hv : padicValNat 2 (Nat.card ↥(R₁.map ψ ⊓ R₂.map ψ)) ≤ 1) : False := by
  obtain ⟨Q, hQJ, hQ8, hQN⟩ := hQex
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans (Q3.center_m11_eq_bot Q3.m11Facts).le
  have hrange : Nat.card ψ.range = 7920 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact Q3.card_m11_kernel
  have hKr : R₁.map ψ ≤ ψ.range := Subgroup.map_le_range ψ R₁
  have hJr : R₂.map ψ ≤ ψ.range := Subgroup.map_le_range ψ R₂
  have hle : Q ⊔ R₁.map ψ ≤ ψ.range := sup_le (hQJ.trans hJr) hKr
  have hdvd : Nat.card ↥(Q ⊔ R₁.map ψ) ∣ 7920 := hrange ▸ Subgroup.card_dvd_of_le hle
  rcases card_sup_of_sylow_normalizes h24₁ hQ8 hQJ hQN hv with ⟨h, -⟩ | ⟨h, -⟩ <;>
    rw [h] at hdvd <;> norm_num at hdvd

end M11

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
