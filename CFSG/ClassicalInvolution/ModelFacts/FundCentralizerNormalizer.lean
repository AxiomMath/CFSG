module

public import CFSG.ClassicalInvolution.ModelFacts.FundamentalSL2All
public import CFSG.LieType.HighestRoot.Defs
import CFSG.ClassicalInvolution.ModelFacts.G2D4TD4Model
import CFSG.LieType.HighestRoot.CentChevalleyModels
import CFSG.LieType.HighestRoot.CentLinearModels
import CFSG.LieType.HighestRoot.CentSpinModels
import CFSG.LieType.HighestRoot.CentTwistedE6Three
public import CFSG.ClassicalInvolution.AschTight.S19MFund

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

variable {p e : ℕ} [Fact p.Prime]


theorem exists_isUniqueInvolution_of_mem_fundamentalSubgroups (hp2 : p ≠ 2) {t : StatedLieTag}
    {n : ℕ} (hfund : Generic.IsFundTag t) (hadm : StatedLieAdmissible t n p e)
    {R : Subgroup (Generic.modelUniv t n p e Fact.out).K}
    (hR : R ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t n p e Fact.out).D) :
    ∃ z, Generic.IsUniqueInvolution R z := by
  have he : 1 ≤ e := hadm.2.1
  rcases nonempty_equiv_sl2_galoisField_of_mem_fundamentalSubgroups hp2 hfund hadm hR with
    h | ⟨-, h⟩
  · exact Disconnected.AschTight.S19M.exists_isUniqueInvolution_of_equiv_sl2
      (Disconnected.AschTight.S19M.odd_natCard_galoisField hp2 he) (Classical.choice h)
  · exact Disconnected.AschTight.S19M.exists_isUniqueInvolution_of_equiv_sl2
      (Disconnected.AschTight.S19M.odd_natCard_galoisField hp2 (by omega)) (Classical.choice h)

open CFSG.LieType.HighestRoot in
theorem centralizer_le_normalizer_of_highestRootCZ {t : StatedLieTag} {n : ℕ}
    (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4) (hfund : Generic.IsFundTag t)
    (hadm : StatedLieAdmissible t n p e)
    (hCZ : HighestRootCZ (Generic.modelUniv t n p e Fact.out).D (GaloisField p e))
    {R : Subgroup (Generic.modelUniv t n p e Fact.out).K}
    (hR : R ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t n p e Fact.out).D)
    {z : (Generic.modelUniv t n p e Fact.out).K} (hz : Generic.IsUniqueInvolution R z) :
    Subgroup.centralizer ({z} : Set (Generic.modelUniv t n p e Fact.out).K) ≤
      Subgroup.normalizer (R : Set (Generic.modelUniv t n p e Fact.out).K) := by
  obtain ⟨γ, hγroot, hγmax, hcc⟩ := hCZ
  have hγ : Generic.IsLongestRoot (Generic.modelUniv t n p e Fact.out).D γ := ⟨hγroot, hγmax⟩
  obtain ⟨g, γ', hγ'cond, hRg⟩ := hR
  have hγ' : Generic.IsLongestRoot (Generic.modelUniv t n p e Fact.out).D γ' := by
    rcases hγ'cond with h | ⟨ht, -⟩ | ⟨ht, -⟩
    · exact h
    · exact absurd ht hG2
    · exact absurd ht hD4
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : (Generic.modelUniv t n p e Fact.out).K,
      Generic.conjSub g₀ (rankOneGroup (Generic.modelUniv t n p e Fact.out).D γ) =
        rankOneGroup (Generic.modelUniv t n p e Fact.out).D γ' :=
    exists_conj_of_isLongestRoot t n p e Fact.out hfund hadm hγ hγ'
  have hcc₁ : CentralizerCondition (GaloisField p e)
      (Generic.conjSub g₀ (rankOneGroup (Generic.modelUniv t n p e Fact.out).D γ)) :=
    centralizerCondition_map (MulAut.conj g₀) hcc
  have hcc₂ : CentralizerCondition (GaloisField p e)
      (Generic.conjSub g
        (Generic.conjSub g₀ (rankOneGroup (Generic.modelUniv t n p e Fact.out).D γ))) :=
    centralizerCondition_map (MulAut.conj g) hcc₁
  have hRcc : CentralizerCondition (GaloisField p e) R := by
    rw [hRg]
    have h := hcc₂
    rw [hg₀] at h
    exact h
  have hz2 : orderOf z = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using hz.sq) hz.ne_one
  exact (hRcc z hz.mem hz2).1


theorem centralizer_le_normalizer_of_mem_fundamentalSubgroups (hp2 : p ≠ 2) {t : StatedLieTag}
    {n : ℕ} (hfund : Generic.IsFundTag t) (hadm : StatedLieAdmissible t n p e)
    {R : Subgroup (Generic.modelUniv t n p e Fact.out).K}
    (hR : R ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t n p e Fact.out).D)
    {z : (Generic.modelUniv t n p e Fact.out).K} (hz : Generic.IsUniqueInvolution R z) :
    Subgroup.centralizer ({z} : Set (Generic.modelUniv t n p e Fact.out).K) ≤
      Subgroup.normalizer (R : Set (Generic.modelUniv t n p e Fact.out).K) := by
  cases t with
  | G2 =>
    exact CFSG.ClassicalInvolution.Asc77.T3Typed.centralizer_le_normalizer_of_g2
      (t := .G2) hp2 rfl hadm hR hz
  | trialityD4 =>
    have hn : n = 0 := hadm.2.2
    subst hn
    intro g hg
    have hgz : g * z = z * g := Subgroup.mem_centralizer_singleton_iff.mp hg
    have hgc : g * z * g⁻¹ = z := by rw [hgz]; group
    have h1 : Generic.IsUniqueInvolution (Generic.conjSub g R) z := by
      have h := hz.conj g
      rwa [hgc] at h
    exact (CFSG.ClassicalInvolution.G2D4Models.normalizer_iff_conjSub_eq).mpr
      (CFSG.ClassicalInvolution.G2D4Models.noTwinsFund_td4 hp2 hadm R hR z hz g h1)
  | PSL =>
    exact centralizer_le_normalizer_of_highestRootCZ (t := .PSL) (n := n)
      (by decide) (by decide) hfund hadm
      (CFSG.LieType.HighestRoot.highestRootCZ_genericModelUniv_PSL hp2 hadm) hR hz
  | PSU =>
    exact centralizer_le_normalizer_of_highestRootCZ (t := .PSU) (n := n)
      (by decide) (by decide) hfund hadm
      (CFSG.LieType.HighestRoot.highestRootCZ_genericModelUniv_PSU hp2 hadm) hR hz
  | PSp =>
    exact centralizer_le_normalizer_of_highestRootCZ (t := .PSp) (n := n)
      (by decide) (by decide) hfund hadm
      (CFSG.LieType.HighestRoot.highestRootCZ_genericModelUniv_PSp hp2 hadm) hR hz
  | POmegaOdd =>
    exact centralizer_le_normalizer_of_highestRootCZ (t := .POmegaOdd) (n := n)
      (by decide) (by decide) hfund hadm
      (CFSG.LieType.HighestRoot.highestRootCZ_genericModelUniv_POmegaOdd hp2 hadm) hR hz
  | POmegaPlus =>
    exact centralizer_le_normalizer_of_highestRootCZ (t := .POmegaPlus) (n := n)
      (by decide) (by decide) hfund hadm
      (CFSG.LieType.HighestRoot.highestRootCZ_genericModelUniv_POmegaPlus hp2 hadm) hR hz
  | POmegaMinus =>
    exact centralizer_le_normalizer_of_highestRootCZ (t := .POmegaMinus) (n := n)
      (by decide) (by decide) hfund hadm
      (CFSG.LieType.HighestRoot.highestRootCZ_genericModelUniv_POmegaMinus hp2 hadm) hR hz
  | F4 =>
    exact centralizer_le_normalizer_of_highestRootCZ (t := .F4) (n := n)
      (by decide) (by decide) hfund hadm
      (CFSG.LieType.HighestRoot.highestRootCZ_modelUniv_F4 n p e hp2) hR hz
  | E6 =>
    exact centralizer_le_normalizer_of_highestRootCZ (t := .E6) (n := n)
      (by decide) (by decide) hfund hadm
      (CFSG.LieType.HighestRoot.highestRootCZ_modelUniv_E6 n p e hp2) hR hz
  | E7 =>
    exact centralizer_le_normalizer_of_highestRootCZ (t := .E7) (n := n)
      (by decide) (by decide) hfund hadm
      (CFSG.LieType.HighestRoot.highestRootCZ_modelUniv_E7 n p e hp2) hR hz
  | E8 =>
    exact centralizer_le_normalizer_of_highestRootCZ (t := .E8) (n := n)
      (by decide) (by decide) hfund hadm
      (CFSG.LieType.HighestRoot.highestRootCZ_modelUniv_E8 n p e hp2) hR hz
  | twistedE6 =>
    exact centralizer_le_normalizer_of_highestRootCZ (t := .twistedE6) (n := n)
      (by decide) (by decide) hfund hadm
      (CFSG.LieType.HighestRoot.highestRootCZ_modelUniv_twistedE6_full (p := p) (f := e) n
        hp2 hadm.2.1) hR hz
  | twistedB2 => exact hfund.elim
  | twistedG2 => exact hfund.elim
  | twistedF4 => exact hfund.elim
  | Tits => exact hfund.elim

end CFSG.ClassicalInvolution.ModelFacts
