module

public import CFSG.ClassicalInvolution.Asc77.AscIHTwin
public import CFSG.ClassicalInvolution.Asc77.AscT3Basic
public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2NC

public section

namespace CFSG.ClassicalInvolution.Asc77.T3Typed

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3 CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.G2D4Models CFSG.ClassicalInvolution.Balance.Bootstrap

variable {p : ℕ} [Fact p.Prime]

theorem exists_fund_uniqueInvolution_g2 (hp2 : p ≠ 2) {e : ℕ} (he : 1 ≤ e) :
    ∃ R ∈ fundamentalSubgroups StatedLieTag.G2 (modelUniv StatedLieTag.G2 0 p e Fact.out).D,
      ∃ c : (modelUniv StatedLieTag.G2 0 p e Fact.out).K, IsUniqueInvolution R c := by
  change ∃ R ∈ fundamentalSubgroups StatedLieTag.G2
      (CFSG.LieType.Steinberg.Adjoint.g2Datum (GaloisField p e)),
    ∃ c : ↥(adjointGroup Tag.G2 (GaloisField p e)), IsUniqueInvolution R c
  set F := GaloisField p e with hF
  have hodd : Odd (Nat.card F) := by
    rw [GaloisField.card p e (by omega)]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have hK2 : ringChar F ≠ 2 := ringChar_ne_two_of_odd_nat_card hodd
  set γ : Fin Tag.G2.rank → ℤ := Pi.single ⟨0, by decide⟩ 1 with hγdef
  have hγ : IsRoot Tag.G2 γ := isRoot_single Tag.G2 ⟨0, by decide⟩
  set ι : ↥(adjointGroup Tag.G2 F) →* ModGL Tag.G2 F := (adjointGroup Tag.G2 F).subtype with hι
  have hιinj : Function.Injective ι := Subtype.val_injective
  set Q : Subgroup ↥(adjointGroup Tag.G2 F) :=
    rootGroup (rootOperatorFamily Tag.G2) F γ ⊔ rootGroup (rootOperatorFamily Tag.G2) F (-γ)
    with hQ
  have hQmap : Q.map ι = rootPair Tag.G2 F γ := by
    rw [hQ, ← ModelFacts.subgroupOf_rootSubgroup_sup_eq (rootOperatorFamily Tag.G2) hγ, hι,
      Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.2 (sup_le (rootSubgroup_le_adjointGroup γ)
      (rootSubgroup_le_adjointGroup (-γ)))
  obtain ⟨a, ha, hne1, hγa⟩ := exists_signKernel_g2 hK2 hγ
  obtain ⟨w, i, φ, hw, hφinj, hφrange, hφneg⟩ := exists_hom_of_isRoot hK2 hγ
  have hφa : φ (-1) = rootDiagUnit Tag.G2 a :=
    hφneg.trans (torusElt_neg_one_conj_eq_rootDiagUnit hodd ha hne1 hγa hw)
  have hmod : IsUniqueInvolution (rootPair Tag.G2 F γ) (rootDiagUnit Tag.G2 a) := by
    have := isUniqueInvolution_range_sl2 hodd hφinj
    rwa [hφa, hφrange] at this
  have hz : IsUniqueInvolution (Q.map ι) (rootDiagUnit Tag.G2 a) := by
    rw [hQmap]
    exact hmod
  obtain ⟨c, -, hc⟩ := isUniqueInvolution_comap hιinj hz
  exact ⟨Q, ⟨1, γ, Or.inr (Or.inl ⟨rfl, mem_adjDatum_roots.2 hγ⟩), by rw [conjSub_one]⟩, c, hc⟩

theorem exists_fund_of_involution_g2 (hp2 : p ≠ 2) {e : ℕ} (hadm : StatedLieAdmissible .G2 0 p e)
    {u : (modelUniv .G2 0 p e Fact.out).K} (hu : u * u = 1) (hu1 : u ≠ 1) :
    ∃ R ∈ fundamentalSubgroups .G2 (modelUniv .G2 0 p e Fact.out).D, IsUniqueInvolution R u := by
  obtain ⟨R₀, hR₀, c₀, hc₀⟩ := exists_fund_uniqueInvolution_g2 (p := p) hp2 hadm.2.1
  obtain ⟨g, hg⟩ := g2_model_involutions_conj (t := .G2) rfl hp2 hadm hc₀.sq hu hc₀.ne_one hu1
  refine ⟨conjSub g R₀, RouteD.conjSub_mem_fundamentalSubgroups hR₀ g, ?_⟩
  have := hc₀.conj g
  rwa [hg] at this

end CFSG.ClassicalInvolution.Asc77.T3Typed
