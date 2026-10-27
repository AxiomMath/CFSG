module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndRank
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415PBase
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415Tools
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitBlowup
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.TwoA.Census.PermClasses

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd

variable {X : Type} [Group X] [Finite X]
  {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X} {w z : X} {V : Subgroup X}
  {i j : ℕ} {z₁ τ α : X} {K₂ W 𝒱 : Subgroup X}

namespace Data415B

theorem oddCore_fusionZStar_component {M : Subgroup (MBar z₁)} (hM : IsComponent M) :
    pPrimeCore 2 ↥M = ⊥ ∧ Open.fusionZStar ↥M = center ↥M := by
  have hO : pPrimeCore 2 ↥M = ⊥ :=
    pPrimeCore_eq_bot_of_isSubnormal (pPrimeCore_quotient_pPrimeCore_eq_bot 2) hM.2
  refine ⟨hO, ?_⟩
  ext l
  rw [GSThmB.OddQuot.mem_fusionZStar_iff, hO, mem_center_iff]
  constructor
  · intro h m
    have := h m
    rw [mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this.symm
  · intro h m
    rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (h m).symm

theorem lift_component {M : Subgroup (MBar z₁)} (hM : IsComponent M) :
    ∃ J : Subgroup ↥(centralizer ({z₁} : Set X)), IsPComponent 2 J ∧
      J.map (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({z₁} : Set X)))) = M ∧
      IsTwoQuasisimple ↥J ∧ Nonempty (↥J ⧸ Open.fusionZStar ↥J ≃* ↥M ⧸ center ↥M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hOM, hZM⟩ := oddCore_fusionZStar_component hM
  obtain ⟨J, hJ, hJM⟩ := LocalAnalysis.ComponentInitial.exists_isPComponent_of_isComponent 2 hM
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({z₁} : Set X))) with hπ
  have hker : ¬ 2 ∣ Nat.card π.ker := GSThmB.OddQuot.not_two_dvd_card_ker
  have hk1 : ¬ 2 ∣ Nat.card (MulEquiv.subgroupCongr hJM).toMonoidHom.ker := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr (MulEquiv.subgroupCongr hJM).injective, card_bot]
    norm_num
  obtain ⟨eZ⟩ := GSThmB.OddQuot.nonempty_quotient_fusionZStar_equiv π hker J
  obtain ⟨eZ₂⟩ := GSThmB.OddQuot.nonempty_fusionZStar_equiv_of_surjective
    (MulEquiv.subgroupCongr hJM).toMonoidHom (MulEquiv.subgroupCongr hJM).surjective hk1
  obtain ⟨eO⟩ := GSThmB.OddQuot.nonempty_pPrimeCore_equiv_of_surjective (π.subgroupMap J)
    (π.subgroupMap_surjective J) (GSThmB.OddQuot.not_two_dvd_card_ker_subgroupMap π hker J)
  obtain ⟨eO₂⟩ := GSThmB.OddQuot.nonempty_pPrimeCore_equiv_of_surjective
    (MulEquiv.subgroupCongr hJM).toMonoidHom (MulEquiv.subgroupCongr hJM).surjective hk1
  have eO' : ↥J ⧸ pPrimeCore 2 ↥J ≃* ↥M :=
    eO.trans (eO₂.trans ((QuotientGroup.quotientMulEquivOfEq hOM).trans QuotientGroup.quotientBot))
  refine ⟨J, hJ, hJM, ⟨ClassicalInvolution.LBalanceProof.isPerfect_of_isPComponent hJ,
    LocalCores.isQuasisimple_of_mulEquiv eO'.symm hM.1⟩, ⟨eZ.trans (eZ₂.trans
      (QuotientGroup.quotientMulEquivOfEq hZM))⟩⟩

variable (hD : Data415B t L p f S w z V i j z₁ τ α K₂ W 𝒱)
include hD

theorem t_mul_beta : t * (w ^ (orderOf w / 2) * t ^ i * z ^ j) =
    w ^ (orderOf w / 2) * t ^ (i + 1) * z ^ j := by
  have htu : t * w ^ (orderOf w / 2) = w ^ (orderOf w / 2) * t :=
    hD.hs.setup.X_comm (subset_closure (by simp)) (subset_closure (by simp))
  calc t * (w ^ (orderOf w / 2) * t ^ i * z ^ j) =
      (t * w ^ (orderOf w / 2)) * t ^ i * z ^ j := by group
    _ = (w ^ (orderOf w / 2) * t) * t ^ i * z ^ j := by rw [htu]
    _ = w ^ (orderOf w / 2) * t ^ (i + 1) * z ^ j := by rw [pow_succ']; group

theorem not_lieModel_L4U4
    (hnβ : ∀ g : X, g * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * g⁻¹ ≠ z₁)
    {M : Subgroup (MBar z₁)} (hM : IsComponent M) :
    ∀ k : ℕ, 1 ≤ k → ¬ Blueprint.LieModel (↥M ⧸ center ↥M) .PSL 4 p k ∧
      ¬ Blueprint.LieModel (↥M ⧸ center ↥M) .PSU 4 p k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨g, hg⟩, -⟩ := hD.fd.fusion hnβ
  have h47 := hD.h47 (i + 1) j
  rw [← hD.t_mul_beta] at h47
  have hCC : (centralizer ({t * (w ^ (orderOf w / 2) * t ^ i * z ^ j)} : Set X)).map
      (MulAut.conj g).toMonoidHom = centralizer ({z₁} : Set X) := by
    rw [L415.map_conj_centralizer, hg]
  obtain ⟨φ⟩ : Nonempty (↥(centralizer ({t * (w ^ (orderOf w / 2) * t ^ i * z ^ j)} : Set X)) ≃*
      ↥(centralizer ({z₁} : Set X))) :=
    ⟨((centralizer ({t * (w ^ (orderOf w / 2) * t ^ i * z ^ j)} : Set X)).equivMapOfInjective _
      (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr hCC)⟩
  obtain ⟨J, hJ, -, h2q, ⟨eZ⟩⟩ := lift_component hM
  set J' := J.map φ.symm.toMonoidHom with hJ'def
  have hJ' : IsPComponent 2 J' := isPComponent_map_mulEquiv φ.symm hJ
  let eJ : ↥J ≃* ↥J' := J.equivMapOfInjective _ φ.symm.injective
  have hk1 : ¬ 2 ∣ Nat.card eJ.symm.toMonoidHom.ker := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr eJ.symm.injective, card_bot]
    norm_num
  obtain ⟨eZ'⟩ := GSThmB.OddQuot.nonempty_fusionZStar_equiv_of_surjective eJ.symm.toMonoidHom
    eJ.symm.surjective hk1
  have h2q' : IsTwoQuasisimple ↥J' := isTwoQuasisimple_of_mulEquiv eJ h2q
  intro k hk
  have hno := h47 J' hJ' k hk
  exact ⟨fun hL => hno ⟨h2q', ↥M ⧸ center ↥M, inferInstance, Or.inl hL, ⟨eZ'.trans eZ⟩⟩,
    fun hU => hno ⟨h2q', ↥M ⧸ center ↥M, inferInstance, Or.inr hU, ⟨eZ'.trans eZ⟩⟩⟩

end Data415B

end CFSG.ComponentClassification.HarrisLit
