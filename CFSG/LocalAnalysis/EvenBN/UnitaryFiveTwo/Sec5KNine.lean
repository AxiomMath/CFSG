module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec5KSeven
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour
import all CFSG.Fischer.F4

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup Matrix CFSG.Open CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaInputs SL44
open scoped MatrixGroups

@[expose] noncomputable def stabHom :
    StabSub →* slUnitary (bar : F4 →+* F4) (revGL 4 F4 : Matrix (Fin 4) (Fin 4) F4) where
  toFun g := ⟨⟨subMat (mat g), (subMat_mem g.2).2⟩, (subMat_mem g.2).1⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    change subMat (mat 1) = 1
    rw [mat_one]
    decide
  map_mul' g h := by
    apply Subtype.ext
    apply Subtype.ext
    change subMat (mat ((g : SU52) * h)) = subMat (mat g) * subMat (mat h)
    rw [mat_mul, mem_StabSub.1 g.2, mem_StabSub.1 h.2, ← extMat_mul, subMat_extMat,
      subMat_extMat, subMat_extMat]

theorem stabHom_injective : Function.Injective stabHom := fun g g' h => by
  have h1 : subMat (mat g) = subMat (mat g') :=
    congrArg (fun z : slUnitary (bar : F4 →+* F4) (revGL 4 F4 : Matrix (Fin 4) (Fin 4) F4) =>
      ((z : SpecialLinearGroup (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4)) h
  apply Subtype.ext
  apply ext_mat
  rw [mem_StabSub.1 g.2, mem_StabSub.1 g'.2, h1]

theorem card_StabSub_dvd : Nat.card StabSub ∣ 25920 := by
  rw [← card_slUnitary_four (F := F4) (by rw [Nat.card_eq_fintype_card, F4.card]) bar_apply,
    Nat.card_congr (MonoidHom.ofInjective stabHom_injective).toEquiv]
  exact Subgroup.card_subgroup_dvd_card _

theorem card_K₃sub_dvd : Nat.card K₃sub ∣ 25920 :=
  (Subgroup.card_dvd_of_le K₃sub_le_StabSub).trans card_StabSub_dvd

theorem exists_mulEquiv_SL_F4 {X : Type} [Group X]
    (h : CFSG.Blueprint.LieModel X .PSL 4 2 2) : Nonempty (SL(4, F4) ≃* X) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel h
  have : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by norm_num) hF
  have : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = Fintype.card F4 := by
    rw [F4.card, ← Nat.card_eq_fintype_card, hF]
    norm_num
  set ι₄ : F ≃+* F4 := FiniteField.ringEquivOfCardEq hcard
  let ΦSL : SL(4, F) ≃* SL(4, F4) :=
    { toFun := Matrix.SpecialLinearGroup.map ι₄.toRingHom
      invFun := Matrix.SpecialLinearGroup.map ι₄.symm.toRingHom
      left_inv := fun M => by
        ext i j
        simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
      right_inv := fun M => by
        ext i j
        simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
      map_mul' := fun M N => map_mul _ M N }
  exact ⟨((e.trans
    (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSLFourEquivSL F)).trans ΦSL).symm⟩

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem kLinear_of_lieModel (h : d.Hyp) (hC : d.K ⊓ d.H = d.K₃)
    (hm : CFSG.Blueprint.LieModel d.K .PSL 4 2 2) : d.KLinear := by
  classical
  obtain ⟨ψ⟩ := exists_mulEquiv_SL_F4 hm
  have hF : Nat.card F4 = 4 := card_F4
  have hker := ker_le_center (d := d) ψ
  obtain ⟨A, σ, ε, hε, hA⟩ := exists_actsOn_stdSL ψ h.t_mem_normalizer_K
  have hCt : d.K ⊓ centralizer ({d.t} : Set G) = d.K₃ := hC
  have hK₃ : Nat.card d.K₃ ∣ 25920 := by rw [Data.K₃, d.card_pull]; exact card_K₃sub_dvd
  have hsmall : ∀ Q ≤ d.K ⊓ centralizer ({d.t} : Set G), IsPGroup 2 Q →
      Nat.card Q < Nat.card F4 ^ (2 * 2) := by
    intro Q hQ hQ2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := hQ2.exists_card_eq
    have hdvd : 2 ^ k ∣ 25920 := hk ▸ (Subgroup.card_dvd_of_le (hCt ▸ hQ)).trans hK₃
    have hk6 : k ≤ 6 := by
      by_contra hk7
      have h7 : 2 ^ 7 ∣ 25920 := (pow_dvd_pow 2 (by omega)).trans hdvd
      exact absurd h7 (by norm_num)
    rw [hk, hF]
    calc 2 ^ k ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hk6
      _ < 4 ^ (2 * 2) := by norm_num
  have hσ1 : σ ≠ 1 := field_ne_one_of_small hF (r := 2) (Or.inl rfl) rfl ψ.toMonoidHom hker
    h.t_mul_t hε hA hsmall
  rcases cases_of_lift (n := 4) (by norm_num) hF ψ.toMonoidHom hker h.t_mul_t hε hA with
    ⟨hσ, -⟩ | ⟨-, hσx, H, hH⟩
  · exact absurd hσ hσ1
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  ·
    exfalso
    obtain ⟨θ, hθ, hrange⟩ := exists_field_centralizer (n := 4) (by norm_num) ψ.toMonoidHom
      ψ.surjective hker hσx hH
    have hcard : Nat.card d.K₃ = 20160 := by
      rw [← hCt, ← hrange, ← Nat.card_congr (MonoidHom.ofInjective hθ).toEquiv,
        card_SL_four_two]
    have hL : Nat.card d.K₃ ∣ 13685760 := by
      rw [← card_SU52.1, ← Nat.card_congr d.η.toEquiv]
      exact Subgroup.card_dvd_of_le (d.pull_le_L _)
    rw [hcard] at hL
    exact absurd hL (by norm_num)
  ·
    obtain ⟨φ, hφ, hφker, hact⟩ := exists_std_graphField hF ψ.toMonoidHom ψ.surjective hker hσx hH
    have hσf : σ = frobeniusEquiv F4 2 := RingEquiv.ext fun c => by
      rw [hσx, frobeniusEquiv_apply, frobenius_def]
    subst hσf
    have hinj : Function.Injective φ := by
      rw [← MonoidHom.ker_eq_bot_iff, hφker]
      exact (MonoidHom.ker_eq_bot_iff _).mpr ψ.injective
    refine ⟨hC, MulEquiv.ofBijective φ ⟨hinj, hφ⟩, fun x => ?_⟩
    rw [sigmaSL_eq_stdSL]
    exact hact x

end Data.Hyp

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
