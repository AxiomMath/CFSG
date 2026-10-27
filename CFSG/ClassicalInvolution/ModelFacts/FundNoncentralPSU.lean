module

public import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralSimple
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalPSU

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.RootSystem

section Center

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p] {n : ℕ}

theorem eq_one_of_mem_center_of_mem_fixCols (hF : Nat.card F = (p ^ f) ^ 2) (hn : 3 ≤ n)
    (hnq : (n, p ^ f) ≠ (3, 2)) {m : ℕ} (hm : m < n) {e : Fin m → Fin n}
    {r : SU (unitaryInvolution F p f) n}
    (hrc : r ∈ Subgroup.center (SU (unitaryInvolution F p f) n))
    (hr : r ∈ fixCols (unitaryInvolution F p f) n e) : r = 1 := by
  obtain ⟨-, hZ⟩ := isQuasisimple_statedSU_of_card hF hn hnq
  set P : GL (Fin n) F := (exists_wittMatrix hF n).choose with hP
  let φ : SU (unitaryInvolution F p f) n ≃* StatedSU n (p ^ f) F :=
    (conjEquiv P (exists_wittMatrix hF n).choose_spec).trans
      (MulEquiv.subgroupCongr (SUid_eq_statedSU hF n))
  have hconj : ((φ r : StatedSU n (p ^ f) F) : GL (Fin n) F) =
      P * (r : GL (Fin n) F) * P⁻¹ := rfl
  have h1 : φ r ∈ Subgroup.center (StatedSU n (p ^ f) F) := by
    rw [← map_center_mulEquiv φ]
    exact ⟨r, hrc, rfl⟩
  rw [hZ] at h1
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp h1
  have hr1 : (r : GL (Fin n) F) = Matrix.GeneralLinearGroup.scalar (Fin n) c := by
    rw [hconj] at hc
    calc (r : GL (Fin n) F) = P⁻¹ * (P * (r : GL (Fin n) F) * P⁻¹) * P := by group
      _ = P⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin n) c * P) := by rw [← hc]; group
      _ = Matrix.GeneralLinearGroup.scalar (Fin n) c := by
        rw [Matrix.GeneralLinearGroup.scalar_commute c P]
        group
  obtain ⟨a, ha⟩ : ∃ a : Fin n, a ∉ Set.range e := by
    by_contra hcon
    push Not at hcon
    have := Fintype.card_le_of_surjective e hcon
    simp only [Fintype.card_fin] at this
    omega
  have h2 : mat (unitaryInvolution F p f) n r a a = (1 : Matrix (Fin n) (Fin n) F) a a :=
    hr a ha a
  have h3 : mat (unitaryInvolution F p f) n r a a = (c : F) := by
    rw [mat_apply, hr1, Matrix.GeneralLinearGroup.coe_scalar]
    simp
  have hc1 : c = 1 := Units.ext (by rw [← h3, h2]; simp)
  apply Subtype.ext
  rw [hr1, hc1, map_one]
  rfl

end Center

section Model

variable {p : ℕ} [hp : Fact p.Prime]

theorem eq_one_of_mem_center_PSU (n e : ℕ) (hfund : IsFundTag .PSU)
    (hadm : StatedLieAdmissible .PSU n p e) :
    ∀ R ∈ fundamentalSubgroups .PSU (modelUniv .PSU n p e hp.out).D,
      ∀ r ∈ R, r ∈ Subgroup.center (modelUniv .PSU n p e hp.out).K → r = 1 := by
  have hf : 1 ≤ e := hadm.2.1
  have hM := modelUniv_PSU (n := n) (p := p) (f := e) hf
  have hconj : ∀ γ γ' : Fin (modelUniv .PSU n p e hp.out).D.rank → ℤ,
      IsLongestRoot (modelUniv .PSU n p e hp.out).D γ →
      IsLongestRoot (modelUniv .PSU n p e hp.out).D γ' →
      ∃ g : (modelUniv .PSU n p e hp.out).K,
        ((modelUniv .PSU n p e hp.out).D.rootGroup γ ⊔
          (modelUniv .PSU n p e hp.out).D.rootGroup (-γ)).map (MulAut.conj g).toMonoidHom =
        (modelUniv .PSU n p e hp.out).D.rootGroup γ' ⊔
          (modelUniv .PSU n p e hp.out).D.rootGroup (-γ') :=
    fun γ γ' h h' => exists_conj_of_isLongestRoot .PSU n p e hp.out hfund hadm h h'
  rw [hM] at hconj ⊢
  intro R hR r hrR hrc
  have hF : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 := card_galoisField_two_mul p e hf
  obtain ⟨k, γ₀, h₀, hγ, hγ'⟩ := exists_longest_root_psu hp.out hadm
  obtain ⟨g, γ, hγl, rfl⟩ := hR
  have hγl' : IsLongestRoot (Unitary.rootDatum hF n) γ := by
    rcases hγl with h | ⟨ht, -⟩ | ⟨ht, -⟩
    · exact h
    · exact absurd ht (by simp)
    · exact absurd ht (by simp)
  refine eq_one_of_mem_center_of_conj (D := Unitary.rootDatum hF n) hconj h₀ ?_ hγl' hrR hrc
  intro r' hr' hmem
  have heq := rankOne_eq_fixCols (p := p) (f := e) hF hγ hγ'
  have hmem' : r' ∈ fixCols (unitaryInvolution (GaloisField p (2 * e)) p e) n
      (CFSG.LieType.Steinberg.lastIdxEven k) := by
    rw [← heq]
    exact hmem
  exact eq_one_of_mem_center_of_mem_fixCols hF hadm.2.2.1 hadm.2.2.2 (m := 2)
    (by have := hadm.2.2.1; omega) hr' hmem'

end Model

end CFSG.ClassicalInvolution.ModelFacts
