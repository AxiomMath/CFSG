module

public import CFSG.ClassicalInvolution.Asc77.AscE189Bar
import CFSG.ClassicalInvolution.Asc77.AscIH8Model
import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofExcLayerTwisted

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
  CFSG.ClassicalInvolution.Generic.CoreAssembly
open scoped commutatorElement MatrixGroups

@[expose] def TwinShape (t : StatedLieTag) (n : ℕ) : Prop :=
  (t = .POmegaOdd ∧ 3 ≤ n) ∨ (t = .POmegaPlus ∧ 4 ≤ n) ∨ (t = .POmegaMinus ∧ 4 ≤ n) ∨
    (t = .PSp ∧ n = 2) ∨ (t = .PSL ∧ n = 4) ∨ (t = .PSU ∧ n = 4)

section ModelClass

variable {p : ℕ} [Fact p.Prime]

theorem modelTwinClass_two_of_twin (t : StatedLieTag) (n e : ℕ)
    {R R' : Subgroup (modelUniv t n p e Fact.out).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D)
    (hR' : R' ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D) (hne : R ≠ R')
    (hcomm : Commutes R R')
    (h5 : ∀ S ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D,
      ((S = R ∨ Commutes S R) ↔ (S = R' ∨ Commutes S R'))) :
    ModelTwinClass p t n e 2 := by
  refine ⟨![R, R'], ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hR
    · exact hR'
  · intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd (by simpa using hij) hne
    · exact absurd (by simpa using hij) hne.symm
    · rfl
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hcomm
    · exact fun x hx y hy => (hcomm y hy x hx).symm
    · exact absurd rfl hij
  · intro i j S hS
    have h6 := h5 S hS
    fin_cases i <;> fin_cases j
    · exact Iff.rfl
    · exact h6
    · exact h6.symm
    · exact Iff.rfl

theorem twinShape_of_twinClass (hp2 : p ≠ 2) {e : ℕ} (hq : 5 ≤ p ^ e) {t : StatedLieTag} {n : ℕ}
    (hfund : IsFundTag t) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    (hadm : StatedLieAdmissible t n p e) (hnA1 : ¬ (t = .PSL ∧ n = 2))
    (hT : ModelTwinClass p t n e 2) : TwinShape t n := by
  rcases mfTwin (p := p) (f := e) hp2 hq t n 2 hfund hG2 hD4 hadm hnA1 le_rfl hT with
    h | ⟨ht, hn, -⟩
  · simp only [ShapeTable, ShapeSL7, ShapeSL6, ShapeSLs, ShapeSU7, ShapeSU6, ShapeSUs, ShapeSp4,
      ShapeSp3, ShapeE7, ShapeE8, ShapeTwinD, ShapeTwinSL4, ShapeTwinB, ShapeTwinSp2, ShapeTwinTD,
      ShapeTwinSU4] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact absurd h.1 (by norm_num)
    · exact absurd h.1 (by norm_num)
    · exact absurd h.1 (by norm_num)
    · exact absurd h.1 (by norm_num)
    · exact absurd h.1 (by norm_num)
    · exact absurd h.1 (by norm_num)
    · exact absurd h.1 (by norm_num)
    · exact absurd h.1 (by norm_num)
    · exact absurd h.1 (by norm_num)
    · exact absurd h.1 (by norm_num)
    · exact Or.inr (Or.inl ⟨h.2.1, h.2.2⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.2.1, h.2.2⟩))))
    · exact Or.inl ⟨h.2.1, h.2.2⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h.2.1, h.2.2⟩)))
    · exact Or.inr (Or.inr (Or.inl ⟨h.2.1, h.2.2⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h.2.1, h.2.2⟩))))
  · exact Or.inr (Or.inl ⟨ht, by omega⟩)

end ModelClass


section Component

variable {p f : ℕ} [Fact p.Prime] {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

omit [Fact p.Prime] [Finite X] in
theorem commutes_map_of_commutes {K : Type} [Group K] (ψ : K →* X) {A B : Subgroup K}
    (h : Commutes A B) : Commutes (A.map ψ) (B.map ψ) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul, h a ha b hb]

theorem twinShape_of_twin (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΦ : HypOmega p f Φ) (D : OmegaLie p f Φ)
    (i : Fin D.card) (hG2 : D.tag i ≠ .G2) (hD4 : D.tag i ≠ .trialityD4)
    {R R' : Subgroup (D.model i).K} (hR : R ∈ fundamentalSubgroups (D.tag i) (D.model i).D)
    (hR' : R' ∈ fundamentalSubgroups (D.tag i) (D.model i).D) (hK : R.map (D.hom i) ∈ Φ)
    (hK'Φ : R'.map (D.hom i) ∈ Φ) {z : X} (hzK : IsUniqueInvolution (R.map (D.hom i)) z)
    (hzK' : IsUniqueInvolution (R'.map (D.hom i)) z)
    (hne : R.map (D.hom i) ≠ R'.map (D.hom i)) :
    TwinShape (D.tag i) (D.rank i) ∧ R ≠ R' ∧ Commutes R R' ∧
      ∃ x ∈ R, ∃ x' ∈ R', x * x = 1 ∧ x ≠ 1 ∧ x' * x' = 1 ∧ x' ≠ 1 ∧ D.hom i x = z ∧
        D.hom i x' = z := by
  have hnA1 : ¬ (D.tag i = .PSL ∧ D.rank i = 2) := by
    intro hA1
    apply hne
    rw [D.map_fund_eq_comp_of_A1 i hA1 hR, D.map_fund_eq_comp_of_A1 i hA1 hR']
  have hexp : D.exp i = f := (D.exp_eq i).resolve_right fun h => hD4 h.1
  have hq' : 5 ≤ p ^ D.exp i := by rw [hexp]; exact hq
  have hperf := Gaps.fundPerfect_modelUniv hp (D.isFundTag i) (D.admissible i) (by omega)
  have hRp : R ≤ ⁅R, R⁆ := hperf R hR
  have hR'p : R' ≤ ⁅R', R'⁆ := hperf R' hR'
  have hker := D.ker_le_center i
  have hex : oddCoreOf (R.map (D.hom i)) = ⊥ := oddCoreOf_eq_bot_of_exact hΦ.exact hK
  have hK' : R'.map (D.hom i) ∈ twinSet Φ (R.map (D.hom i)) := ⟨hK'Φ, z, hzK, hzK'⟩
  have hneR : R ≠ R' := fun h => hne (by rw [h])
  obtain ⟨hcomm, x, hx, x', hx', hψx, hψx', hx'1, -⟩ := ih8_twin_data hΦ.toMod hker hRp hK hK'Φ
    hne hzK hzK' hex
  have hinj := D.injOn_fund i hnA1 hR
  have hinj' := D.injOn_fund i hnA1 hR'
  have hx2 : x * x = 1 := hinj _ (R.mul_mem hx hx) (by rw [map_mul, hψx, hzK.sq])
  have hx'2 : x' * x' = 1 := hinj' _ (R'.mul_mem hx' hx') (by rw [map_mul, hψx', hzK'.sq])
  have hx1 : x ≠ 1 := fun h => hzK.ne_one (by rw [← hψx, h, map_one])
  have hKP : KPerp Φ (R.map (D.hom i)) = KPerp Φ (R'.map (D.hom i)) :=
    (l6_3 p f hp hq X Φ hΦ.toMod _ hK _ hK').1
  have hperp : ∀ L ∈ Φ, ((L = R.map (D.hom i) ∨ Commutes L (R.map (D.hom i))) ↔
      (L = R'.map (D.hom i) ∨ Commutes L (R'.map (D.hom i)))) := by
    intro L hL
    rw [← mem_kPerp_iff_commutes hp hq hΦ hK hL hzK,
      ← mem_kPerp_iff_commutes hp hq hΦ hK'.1 hL hzK', hKP]
  have hsc := ModelFacts.fundamentalSingleClass (D.tag i) (D.rank i) p (D.exp i) Fact.out
    (ih8_isFundTag_mf (D.isFundTag i)) (D.admissible i) hG2 hD4
  have h5 : ∀ S ∈ fundamentalSubgroups (D.tag i) (D.model i).D,
      ((S = R ∨ Commutes S R) ↔ (S = R' ∨ Commutes S R')) := by
    intro S hS
    obtain ⟨y, hy⟩ := hsc R hR S hS
    have hy' : S = conjSub y R := hy
    have hSΦ : S.map (D.hom i) ∈ Φ := by
      have h1 := hΦ.conjInvariant (D.hom i y) _ hK
      rw [conjSub_map (D.hom i) y R] at h1
      rw [hy']
      exact h1
    have hpS : S ≤ ⁅S, S⁆ := hperf S hS
    have hto : ∀ {T : Subgroup (D.model i).K}, T ≤ ⁅T, T⁆ →
        ((S = T ∨ Commutes S T) ↔
          (S.map (D.hom i) = T.map (D.hom i) ∨
            Commutes (S.map (D.hom i)) (T.map (D.hom i)))) := by
      intro T hpT
      constructor
      · rintro (rfl | h)
        · exact Or.inl rfl
        · exact Or.inr (commutes_map_of_commutes _ h)
      · rintro (h | h)
        · exact Or.inl (ih8_eq_of_map_eq _ hker hpS hpT h)
        · exact Or.inr (ih8_commutes_of_commutes_map _ hker hpS h)
    rw [hto hRp, hto hR'p]
    exact hperp _ hSΦ
  have hT := modelTwinClass_two_of_twin (p := p) (D.tag i) (D.rank i) (D.exp i) hR hR' hneR hcomm
    h5
  have hshape := twinShape_of_twinClass hp hq' (D.isFundTag i) hG2 hD4 (D.admissible i) hnA1 hT
  exact ⟨hshape, hneR, hcomm, x, hx, x', hx', hx2, hx1, hx'2, hx'1, hψx, hψx'⟩

end Component

end CFSG.ClassicalInvolution.Asc77
