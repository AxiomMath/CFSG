module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6AdaptChart
public import CFSG.ClassicalInvolution.RouteD.TypeUPatternPartner
public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutAmbient
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate123
public import CFSG.ClassicalInvolution.LBalance.Main
public import CFSG.ClassicalInvolution.ModelFacts.OddCover
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.ClassicalInvolution.Models.Transfer
public import CFSG.ClassicalInvolution.Models.UnitaryFrames
public import CFSG.ClassicalInvolution.Models.UnitaryPairs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.PrimeComplementQuotientComponents
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Phan CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.BorelTits
open scoped MatrixGroups
open Matrix

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

local notation "FF" => GaloisField p (2 * f)

theorem UCtx.conj_perm {m : ℕ} (c : UCtx p f m Ω K z) {t : G} (htz : t * z * t⁻¹ = z) :
    (∀ L ∈ centralizingMembers Ω {z}, conjSub t L ∈ centralizingMembers Ω {z}) ∧
      conjSub t K = K := by
  have hconj := c.hΩ.conjInvariant
  have hconj_t : centralizingMembers Ω {z} = conjSub t '' centralizingMembers Ω {z} := by
    have := centralizingMembers_conj hconj t z
    rwa [htz] at this
  have hmemΩz : ∀ L ∈ centralizingMembers Ω {z}, conjSub t L ∈ centralizingMembers Ω {z} := by
    intro L hL
    have : conjSub t L ∈ conjSub t '' centralizingMembers Ω {z} := ⟨L, hL, rfl⟩
    rwa [← hconj_t] at this
  refine ⟨hmemΩz, ?_⟩
  have hcK : IsClassicalMember p f (conjSub t K) z := by
    have := c.hz.conj t
    rwa [htz] at this
  have hmem : conjSub t K ∈ centralizingMembers Ω {z} :=
    ⟨hconj t K c.hK, le_centralizer_of_isClassicalMember hcK⟩
  exact typeU_eq_of_locImg_le_Q₀ c.hp2 c.hq c.hm c.hΩ c.hex c.hK c.hz c.hP1 c.d hmem
    (typeU_locImg_self_le_Q₀ c.hp2 c.hq c.hm (hconj t K c.hK) hcK c.d)

namespace TE6Chart

variable {c : UCtx p f 5 Ω K z} {nd : UNodes c}
  {Θ : Su (GaloisField p (2 * f)) p f 6 →* G}

theorem conj_mem_range (hΘ : TE6Chart c nd Θ) {t : G} (htz : t * z * t⁻¹ = z) {y : G}
    (hy : y ∈ Θ.range) : t * y * t⁻¹ ∈ Θ.range := by
  obtain ⟨hperm, hK⟩ := c.conj_perm htz
  have hK' : conjSub t⁻¹ K = K := by
    have := congrArg (conjSub t⁻¹) hK
    rw [conjSub_inv_conjSub] at this
    exact this.symm
  have hj : ∀ i : Fin 5, ∀ y ∈ nd.j i.val, t * y * t⁻¹ ∈ Θ.range := by
    intro i y hy
    have hmem := hperm _ (nd.mem i.val (by omega))
    have hne : conjSub t (nd.j i.val) ≠ K := by
      intro h
      apply nd.ne_K i.val (by omega)
      have := congrArg (conjSub t⁻¹) h
      rwa [conjSub_inv_conjSub, hK'] at this
    obtain ⟨R, -, hRe⟩ := hΘ.cover _ hmem hne
    have : t * y * t⁻¹ ∈ conjSub t (nd.j i.val) := conj_mem_conjSub hy
    rw [hRe] at this
    exact Subgroup.map_le_range Θ R this
  have hle : (⨆ i : Fin 5, nd.j i.val) ≤ Θ.range.comap (MulAut.conj t).toMonoidHom :=
    iSup_le fun i y hy => hj i y hy
  rw [← hΘ.range_eq] at hle
  exact hle hy

theorem exists_alpha (hΘ : TE6Chart c nd Θ) {t : G} (htz : t * z * t⁻¹ = z) (ht2 : t * t = 1) :
    ∃ (α : Su FF p f 6 →* Su FF p f 6) (g : GL (Fin 6) FF) (φ : FF ≃+* FF),
      (∀ x, Θ (α x) = t * Θ x * t⁻¹) ∧
      (∀ x, ((α x : GL (Fin 6) FF) : Matrix (Fin 6) (Fin 6) FF) =
        (g : Matrix (Fin 6) (Fin 6) FF) *
          φ.mapMatrix ((x : GL (Fin 6) FF) : Matrix (Fin 6) (Fin 6) FF) *
            ((g⁻¹ : GL (Fin 6) FF) : Matrix (Fin 6) (Fin 6) FF)) ∧
      ((g : Matrix (Fin 6) (Fin 6) FF).map (unitaryInvolution FF p f))ᵀ *
        (g : Matrix (Fin 6) (Fin 6) FF) = 1 ∧
      (φ = RingEquiv.refl FF ∨ φ = unitaryInvolution FF p f) ∧ α.comp α = MonoidHom.id _ := by
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hσ : ∀ y : G, (MulAut.conj t) ((MulAut.conj t) y) = y := fun y => by
    simp only [MulAut.conj_apply, ht']
    calc t * (t * y * t) * t = (t * t) * y * (t * t) := by group
      _ = y := by rw [ht2]; group
  have hstab : ∀ x, (MulAut.conj t) (Θ x) ∈ Θ.range := fun x =>
    hΘ.conj_mem_range htz ⟨x, rfl⟩
  obtain ⟨α, g, φ, h1, h2, h3, h4, h5⟩ :=
    ModelFacts.UnitaryAut.unitaryAutClassification_ambient c.card_eq c.hp2 c.hq
      (by norm_num : 3 ≤ 6) Θ hΘ.ker_le (MulAut.conj t) hσ hstab
  exact ⟨α, g, φ, fun x => by rw [h1 x]; rfl, h2, h3, h4, h5⟩

omit [Finite G] in
theorem centralizes_of_fixed {α : Su FF p f 6 →* Su FF p f 6} {t : G}
    (hα : ∀ x, Θ (α x) = t * Θ x * t⁻¹) {x : Su FF p f 6} (hx : α x = x) :
    t * Θ x = Θ x * t := by
  have := hα x
  rw [hx] at this
  rw [eq_mul_inv_iff_mul_eq] at this
  exact this.symm

end TE6Chart

end CFSG.ClassicalInvolution.RouteD
