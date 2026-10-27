module

public import CFSG.ClassicalInvolution.Q3.TL4SecIdLie
public import CFSG.ClassicalInvolution.Q3.Q3T6CoreSec
public import CFSG.LieType.Steinberg.CentralExt.TrialityCoprime
public import CFSG.LieType.HighestRoot.ModelCenter

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open scoped MatrixGroups

section Center

open CFSG CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

theorem center_unitary_three {F : Type} [Field F] [Finite F] [CharP F 3]
    (hF : Nat.card F = (3 ^ 1) ^ 2) :
    Subgroup.center (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 3 1) 3) = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  set e := Unitary.equivStatedSU (p := 3) (f := 1) hF 3 with he
  have hz' : e z ∈ Subgroup.center (StatedSU 3 (3 ^ 1) F) := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, hz x]
  rw [(Unitary.isQuasisimple_statedSU_of_card hF (by norm_num) (by decide)).2] at hz'
  have hsc : ((e z : StatedSU 3 (3 ^ 1) F) : GL (Fin 3) F) ∈ StatedScalars (Fin 3) F :=
    Subgroup.mem_subgroupOf.mp hz'
  have hdet := Unitary.det_eq_one_of_mem_statedSU (e z).2
  have h3 : ((e z : StatedSU 3 (3 ^ 1) F) : GL (Fin 3) F) ^ 3 = 1 := by
    obtain ⟨u, hu⟩ := hsc
    rw [← hu] at hdet ⊢
    have hu3 : u ^ 3 = 1 := by
      have h1 : ((Matrix.GeneralLinearGroup.scalar (Fin 3) u : GL (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F).det = (u : F) ^ 3 := by
        simp [Matrix.GeneralLinearGroup.scalar]
      rw [h1] at hdet
      exact Units.ext (by rw [Units.val_pow_eq_pow_val, hdet, Units.val_one])
    rw [← map_pow, hu3, map_one]
  have h1 := CFSG.ComponentClassification.RankTwoOddLie.eq_one_of_mem_statedScalars hsc h3
  have h2 : e z = 1 := Subtype.ext h1
  rw [map_eq_one_iff e e.injective] at h2
  exact h2


theorem center_modelUniv_psl_three (hp : Nat.Prime 3) :
    Subgroup.center (modelUniv .PSL 3 3 1 hp).K = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  show Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 3 1)) = ⊥
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨r, hr, hz'⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  rw [Fintype.card_fin] at hr
  have h1 : r = 1 := CFSG.ComponentClassification.RankTwoOddLie.eq_one_of_pow_eq_one_of_charP hr
  rw [h1, map_one] at hz'
  rw [Subgroup.mem_bot]
  exact Subtype.ext hz'.symm

theorem center_modelUniv_g2_three (hp : Nat.Prime 3) :
    Subgroup.center (modelUniv .G2 0 3 1 hp).K = ⊥ :=
  CFSG.LieType.Chevalley.center_adjointGroup_eq_bot

theorem center_modelUniv_d4_three (hp : Nat.Prime 3) :
    Subgroup.center (modelUniv .trialityD4 0 3 1 hp).K = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  exact CFSG.LieType.Steinberg.CentralExt.TrialityClosed.twistedGroup_center_eq_bot_of_card
    (q := 3) (by norm_num) (by rw [GaloisField.card 3 (3 * 1) (by norm_num)])
    (fun c => by simp [frobenius_def])

theorem center_modelUniv_psu_three (hp : Nat.Prime 3) :
    Subgroup.center (modelUniv .PSU 3 3 1 hp).K = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hF : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 3 1 le_rfl
  have hU : modelUniv .PSU 3 3 1 hp =
      ⟨Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 3 (2 * 1)) 3 1) 3,
        Unitary.rootDatum hF 3⟩ := by
    simp only [modelUniv, CFSG.LieType.Universal.lieUniversal, le_refl, ↓reduceDIte]
  rw [hU]
  exact center_unitary_three hF

end Center

section Lie

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DEdgeless dAdj)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Uniform
open CFSG.Blueprint


@[expose] def SecIdLieEdgeless3Below (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < n → ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightDatum R S t → TightCls Y R S t → SecIdLie3 R t → TightEdgeless R →
      LieModel Y .PSL 3 3 1 ∨ LieModel Y .PSU 3 3 1 ∨ LieModel Y .G2 0 3 1 ∨
        LieModel Y .trialityD4 0 3 1 ∨ NativeSporadic.IsSporadic Y .M11


theorem secIdLieEdgeless3Below_of {n : ℕ} (hCIT : CITBelowT (.sl2 3 1) n) :
    SecIdLieEdgeless3Below n := by
  intro Y _ _ hn R S t hd hc hl hE
  set Δ := CoreAssembly.conjClass (tightCore R) with hΔ
  have hΩ : HypOmegaGen Δ := hd.hypOmegaGen
  have h2 : ∀ J ∈ Δ, IsPGroup 2 ↥J := hl.isPGroup_members hc.2.2
  have hlift : HasLifts Δ := hl.hasLifts hd
  have hex : ExactSylow Δ := hl.exactSylow hc.2.2
  obtain ⟨hΛ, hgΛ, -⟩ := hl.liftFam_hyp hd hc
  have hO : classicalInvolutionOddCore Y = ⊥ := hc.2.2
  have hDE : DEdgeless (liftFam Δ) := by
    intro M hM M' hM' hadj
    obtain ⟨J, hJ, hJM⟩ := exists_core_of_mem_liftFam hM
    obtain ⟨J', hJ', hJM'⟩ := exists_core_of_mem_liftFam hM'
    exact hE J hJ J' hJ' ((dAdj_liftFam_iff hΩ h2 hlift hex hM hJ hJM hM' hJ' hJM').mp hadj)
  have hne : (liftFam Δ).Nonempty := by
    obtain ⟨L, u, h⟩ := hlift _ (CoreAssembly.mem_conjClass_self (tightCore R))
    exact ⟨_, satU_mem_liftFam (CoreAssembly.mem_conjClass_self _) h⟩
  set ω := omegaGen (liftFam Δ) with hω
  have eω : ↥ω ≃* Y := (MulEquiv.subgroupCongr hgΛ).trans Subgroup.topEquiv
  have hOω : classicalInvolutionOddCore ↥ω = ⊥ := by
    have h1 := CFSG.ComponentClassification.OddCore.equiv_invariant eω.symm
    have h2 : componentClassificationOddCore Y = ⊥ := hO
    rw [h2, Subgroup.map_bot] at h1
    exact h1.symm
  let eG : (↥ω ⧸ classicalInvolutionOddCore ↥ω) ≃* Y :=
    ((QuotientGroup.quotientMulEquivOfEq hOω).trans QuotientGroup.quotientBot).trans eω
  have hTop : (⊤ : Subgroup (↥ω ⧸ classicalInvolutionOddCore ↥ω)) ∉
      oddQuotientFamily (restrictFamily (liftFam Δ) ω) := by
    rintro ⟨L', ⟨M, hM, hMω, rfl⟩, hL'⟩
    have hinj : Function.Injective (QuotientGroup.mk' (classicalInvolutionOddCore ↥ω)) := by
      rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hOω]
    have hMtop : M.subgroupOf ω = ⊤ := by
      apply Subgroup.map_injective hinj
      rw [hL', Subgroup.map_top, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
    have hMY : M = ⊤ := by
      rw [Subgroup.subgroupOf_eq_top, hgΛ] at hMtop
      exact top_le_iff.mp hMtop
    obtain ⟨J, hJ, hJM⟩ := exists_core_of_mem_liftFam hM
    have hall : ∀ J' ∈ Δ, J' = J := fun J' hJ' =>
      hex.core_unique hΩ h2 hM hJ' hJ (hMY ▸ le_top) hJM
    have hJtop : J = ⊤ := by
      have h1 : (⨆ g : Y, conjSub g (tightCore R)) = ⊤ := hc.2.1
      rw [eq_top_iff, ← h1]
      exact iSup_le fun g => (hall _ ⟨g, rfl⟩).le
    obtain ⟨z, hz⟩ := liftFam_mem3 hM
    have hm : IsClassicalMember3 M z := hz.member.toQ3 (by norm_num)
    have h8 := natCard_of_isSylow2In_classicalMember3 hm
      (isSylow2In_of_le_liftFam hΩ hJ (h2 J hJ) hM hJM)
    have h24 := hm.card_ge
    rw [hMY, ← hJtop, h8] at h24
    omega
  rcases Q3T6.sectionThm6U_datum hCIT hn hΛ hne hDE hTop with ⟨t', k, e', M, htag⟩ | ⟨D, hD⟩
  ·
    have he1 : e' = 1 := by
      rcases M.exp_eq with h | ⟨-, h⟩ <;> omega
    subst he1
    have hZ : Subgroup.center (modelUniv t' k 3 1 Nat.prime_three).K = ⊥ := by
      rcases htag with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact center_modelUniv_psl_three _
      · exact center_modelUniv_psu_three _
      · exact center_modelUniv_g2_three _
      · exact center_modelUniv_d4_three _
    have hinj : Function.Injective M.ψ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      exact M.ker_le_center.trans hZ.le
    let eK := MulEquiv.ofBijective M.ψ ⟨hinj, M.surj⟩
    obtain ⟨-, hLie⟩ := ModelFacts.modelClauseZero t' k 3 1 Nat.prime_three M.isFundTag
      M.admissible
    have hLK : LieModel (modelUniv t' k 3 1 Nat.prime_three).K t' k 3 1 :=
      CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
        ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) hLie
    have hLY : LieModel Y t' k 3 1 := CFSG.LieType.CurtisTits.lieModel_of_mulEquiv (eK.trans eG) hLK
    rcases htag with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl hLY
    · exact Or.inr (Or.inl hLY)
    · exact Or.inr (Or.inr (Or.inl hLY))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hLY)))
  ·
    refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
    let φ := castHom hD (D.hom 0)
    have hsurj : Function.Surjective φ := by
      rw [← MonoidHom.range_eq_top, range_castHom, MonoidHom.range_eq_top]
      exact Q3T6.lieSystemDataU_surjective_hom D 0
    have hinj : Function.Injective φ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      exact (castHom_ker_le_center hD (D.hom 0) (D.ker_le_center 0)).trans
        Q3W.center_m11_eq_bot.le
    exact ⟨((MulEquiv.ofBijective φ ⟨hinj, hsurj⟩).trans eG).symm⟩

end Lie

end CFSG.ClassicalInvolution.Q3.TL4
