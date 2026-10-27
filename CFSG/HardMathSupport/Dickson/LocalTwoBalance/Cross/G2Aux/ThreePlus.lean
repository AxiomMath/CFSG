module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.G2Aux.Centralizers
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.G2Aux.Arith
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding.G2PlusEven
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.RankThree.PartOne.SEITZ6.G2MaxDone
public import CFSG.Goldschmidt.Final
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossOrthBase

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.G2Aux

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false

section Frame


variable {K K₂ : Type} [Field K] [Finite K] [Field K₂] [Algebra K K₂] [Finite K₂]
  {σ : K₂ ≃+* K₂}

theorem R_isPerfect (M : QPlusModel K σ) (hdeg : Module.finrank K K₂ = 2)
    (hσ : ∀ c, σ c = c ^ Nat.card K) (hK4 : 4 ≤ Nat.card K) {β : Fin Tag.G2.rank → ℤ}
    (hβ : IsRoot .G2 β) : Group.IsPerfect ↥(M.R β) := by
  by_cases hodd : Odd (Nat.card K)
  · obtain ⟨P, hP, -⟩ := rootSL2_comap_fixed_eq hodd hdeg σ hσ M.hg M.hzdef M.hz M.hw hβ
    exact (isQuasisimple_of_rootSL2_comap_eq hK4 inf_le_left hP).1
  · haveI := charP_two_of_even_natCard K (Nat.not_odd_iff_even.1 hodd)
    haveI : CharP K₂ 2 := charP_of_injective_algebraMap (algebraMap K K₂).injective 2
    obtain ⟨P, hP, -⟩ := EvenG2.rootSL2_comap_fixed_eq_of_charTwo hdeg σ hσ M.hg M.hzdef M.hz M.hw hβ
    exact (EvenG2.isSimpleGroup_of_rootSL2_comap_eq hK4 inf_le_left hP).2.1

theorem plane_conj_into_torsion (M : QPlusModel K σ) (hdeg : Module.finrank K K₂ = 2)
    (hσ : ∀ c, σ c = c ^ Nat.card K) (h3 : 3 ∣ Nat.card K + 1)
    {F : Subgroup (ModGL .G2 K₂)} (hFΓ : F ≤ M.gamma) (hF3 : ∀ x ∈ F, x ^ 3 = 1)
    (hFc : Nat.card F = 3 ^ 2) :
    ∃ h ∈ M.gamma, F.map (MulAut.conj h).toMonoidHom ≤ torusTorsion K₂ 3 := by
  set ψ := twistEmb (K := K) M.g
  have hψinj : Function.Injective ψ := twistEmb_injective (K := K) M.g
  have hrange : ψ.range = M.gamma := by
    rw [MonoidHom.range_eq_map]
    exact map_twistEmb_top M.g
  set EG := F.comap ψ
  have hmap : EG.map ψ = F := Subgroup.map_comap_eq_self (by rwa [hrange])
  have hcard : Nat.card EG = 3 ^ 2 := by
    rw [← hFc, ← hmap, Subgroup.card_map_of_injective hψinj]
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm : IsMulCommutative EG := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hcard
  have hexp : ∀ x ∈ EG, x ^ 3 = 1 := fun x hx =>
    hψinj (by rw [map_pow, map_one]; exact hF3 _ hx)
  haveI : CFSG.IsElementaryAbelian 3 EG :=
    { toIsMulCommutative := hcomm
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
        Subtype.ext (by simpa using hexp g g.2) }
  obtain ⟨y, hy, hyE⟩ := M.exists_conj_plane_to_torsion hdeg hσ h3 EG hcard
  exact ⟨y, hy, by rw [← hmap]; exact hyE.le⟩

theorem generation_of_X_eq (M : QPlusModel K σ) (hX : M.X = M.gamma) :
    ⨆ β : {β : Fin Tag.G2.rank → ℤ // IsRoot .G2 β}, rootRankOneGroup .G2 K₂ β.1 ⊓ M.gamma =
      M.gamma := by
  refine Eq.trans ?_ hX
  simp only [QPlusModel.X, QPlusModel.R]
  rw [iSup_subtype']

theorem component_three (M : QPlusModel K σ) (hdeg : Module.finrank K K₂ = 2)
    (hσ : ∀ c, σ c = c ^ Nat.card K) (hK3 : ringChar K ≠ 3) (hK4 : 4 ≤ Nat.card K)
    (h3 : 3 ∣ Nat.card K + 1) {β : Fin Tag.G2.rank → ℤ} (hβ : IsRoot .G2 β)
    {a : Fin Tag.G2.rank → K₂ˣ} (hdE : rootDiagUnit .G2 a ∈ torusTorsion K₂ 3)
    (hd1 : rootDiagUnit .G2 a ≠ 1) (hχ : rootChar a β = 1) :
    ∃ L : Subgroup (ModGL .G2 K₂), rootRankOneGroup .G2 K₂ β ⊓ M.gamma ≤ L ∧
      L ≤ M.gamma ⊓ Subgroup.centralizer {rootDiagUnit .G2 a} ∧ CFSG.IsQuasisimple L ∧
      (L.subgroupOf (M.gamma ⊓ Subgroup.centralizer {rootDiagUnit .G2 a})).IsSubnormal ∧
      ¬ Nat.Coprime 3 (Nat.card L) := by
  set d := rootDiagUnit .G2 a
  set ψ := twistEmb (K := K) M.g
  have hψinj : Function.Injective ψ := twistEmb_injective (K := K) M.g
  have hrange : ψ.range = M.gamma := by
    rw [MonoidHom.range_eq_map]
    exact map_twistEmb_top M.g
  have hdΓ : d ∈ M.gamma := M.torusTorsion_three_le_gamma hσ h3 hdE
  obtain ⟨x, hx⟩ := M.exists_twistEmb_eq hdΓ
  have hd3 : d ^ 3 = 1 := (mem_torusTorsion_iff.1 hdE).2
  have hx3 : x ^ 3 = 1 := hψinj (by rw [map_pow, hx, hd3, map_one])
  have hx1 : x ≠ 1 := fun h => hd1 (by rw [← hx, h, map_one])
  set D := M.gamma ⊓ Subgroup.centralizer ({d} : Set (ModGL .G2 K₂))
  have hDC : D = (Subgroup.centralizer ({x} : Set (adjointGroup .G2 K))).map ψ := by
    ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨hyΓ, hyc⟩
      rw [← hrange] at hyΓ
      obtain ⟨y₀, rfl⟩ := hyΓ
      refine ⟨y₀, ?_, rfl⟩
      have hyc' : ψ y₀ ∈ Subgroup.centralizer ({d} : Set (ModGL .G2 K₂)) := hyc
      rw [Subgroup.mem_centralizer_singleton_iff] at hyc' ⊢
      apply hψinj
      rw [map_mul, map_mul, hx]
      exact hyc'
    · rintro ⟨y₀, hy₀, rfl⟩
      refine ⟨hrange ▸ MonoidHom.mem_range.2 ⟨y₀, rfl⟩, ?_⟩
      show ψ y₀ ∈ Subgroup.centralizer ({d} : Set (ModGL .G2 K₂))
      rw [Subgroup.mem_centralizer_singleton_iff] at hy₀ ⊢
      rw [← hx, ← map_mul, ← map_mul, hy₀]
  have hLeq : ⁅D, D⁆ = (⁅Subgroup.centralizer ({x} : Set (adjointGroup .G2 K)),
      Subgroup.centralizer ({x} : Set (adjointGroup .G2 K))⁆).map ψ := by
    rw [hDC, Subgroup.map_commutator]
  obtain ⟨hq, h3d⟩ := commutator_centralizer_isQuasisimple hK3 hK4 h3 hx3 hx1
  refine ⟨⁅D, D⁆, ?_, commutator_self_le D, ?_, isSubnormal_commutator_subgroupOf D, ?_⟩
  · exact le_commutator_of_isPerfect (R_isPerfect M hdeg hσ hK4 hβ) (M.R_le_centralizer hβ hχ)
  · rw [hLeq]
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.equivMapOfInjective _ ψ hψinj) hq
  · rw [hLeq, Subgroup.card_map_of_injective hψinj, ← Nat.Prime.dvd_iff_not_coprime Nat.prime_three]
    exact h3d

theorem X_eq_gamma_of_generation (M : QPlusModel K σ)
    (h : ⨆ β : {β : Fin Tag.G2.rank → ℤ // IsRoot .G2 β}, rootRankOneGroup .G2 K₂ β.1 ⊓ M.gamma =
      M.gamma) : M.X = M.gamma :=
  le_antisymm M.X_le_gamma (h.symm.le.trans (iSup_le fun β => M.R_le_X β.2))

theorem isLangFrame_three (M : QPlusModel K σ) (hdeg : Module.finrank K K₂ = 2)
    (hσ : ∀ c, σ c = c ^ Nat.card K) (hK3 : ringChar K ≠ 3) (hK4 : 4 ≤ Nat.card K)
    (h3 : 3 ∣ Nat.card K + 1) (hX : M.X = M.gamma) :
    IsLangFrame .G2 K₂ 3 M.gamma (torusTorsion K₂ 3) where
  E_le_torus := torusTorsion_le_torusGroup 3
  E_le_Γ := M.torusTorsion_three_le_gamma hσ h3
  sylow := fun _ hFΓ hF3 hFc => plane_conj_into_torsion M hdeg hσ h3 hFΓ hF3 hFc
  generation := generation_of_X_eq M hX
  component := fun _ hβ _ hdE hd1 hχ => component_three M hdeg hσ hK3 hK4 h3 hβ hdE hd1 hχ

end Frame

section Main


theorem innerPlaneBalance_three_of_dvd_add_one (K : Type) [Field K] [Finite K]
    (h4 : 4 ≤ Nat.card K) (hq : 3 ∣ Nat.card K + 1) :
    InnerPlaneBalance 3 (adjointGroup Tag.G2 K) := by
  have hK3 := ringChar_ne_three_of_dvd_add_one K hq
  obtain ⟨K₂, _, _, hdeg, σ, hσ⟩ := exists_quadratic_frobenius_all K
  have : Module.Finite K K₂ := Module.finite_of_finrank_pos (by omega)
  have : Finite K₂ := Module.finite_of_finite K
  obtain ⟨M⟩ : Nonempty (QPlusModel K σ) := by
    by_cases hodd : Odd (Nat.card K)
    · exact QPlusModel.nonempty_of_odd hodd hdeg hσ
    · haveI := charP_two_of_even_natCard K (Nat.not_odd_iff_even.1 hodd)
      exact QPlusModel.nonempty_of_charTwo hdeg hσ
  have hX : M.X = M.gamma := by
    by_cases hodd : Odd (Nat.card K)
    · have hq5 : 5 ≤ Nat.card K := by
        obtain ⟨m, hm⟩ := hodd
        omega
      have := CFSG.RankThree.PartOne.SEITZ11.G2Seven.g2_qplus_generation hodd hq5 K₂ hdeg σ hσ
        M.hg M.hzdef M.hz M.hw
      exact X_eq_gamma_of_generation M this
    · haveI := charP_two_of_even_natCard K (Nat.not_odd_iff_even.1 hodd)
      exact QPlusModel.X_eq_gamma_of_charTwo'
        (RankThree.PartOne.SEITZ6.maxSL2SL2G2_of_top CFSG.Goldschmidt.topStatement) M hdeg hσ h4
  have hF := isLangFrame_three M hdeg hσ hK3 h4 hq hX
  let ε : adjointGroup Tag.G2 K ≃* ↥M.gamma :=
    Subgroup.equivMapOfInjective (adjointGroup Tag.G2 K) M.phi M.phi_injective
  have hinj := conj_injective_of_mulEquiv ε
    (mulAut_conj_injective_adjointGroup (τ := Tag.G2) (K := K))
  exact InnerPlaneBalance.of_mulEquiv ε (innerPlaneBalance_of_langFrame Nat.prime_three hF hinj)

end Main

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.G2Aux
