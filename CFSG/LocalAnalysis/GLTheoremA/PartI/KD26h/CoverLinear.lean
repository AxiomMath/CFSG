module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.KD26h.Cover
public import CFSG.LieType.SeitzGeneration.HyperCoverLinear
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Cover
public import CFSG.Assembly.OrderReductions.LinearOrders
public import CFSG.LieType.Multipliers.L34Upper

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open Matrix

theorem exists_mulEquiv_sl_of_cover {K : Type} [Group K] [Finite K]
    (hK : CFSG.Open.IsQuasisimple K) {m : ℕ} (hm : 2 ≤ m) {F : Type} [Field F] [Finite F]
    (hp : (m + 1).Prime) (hpF : (m + 1) ∣ Nat.card F - 1) (hF : ¬ (m = 2 ∧ Nat.card F = 4))
    (e : K ⧸ Subgroup.center K ≃* ProjectiveSpecialLinearGroup (Fin (m + 1)) F)
    (hZ : Nat.card (Subgroup.center K) = m + 1) :
    ∃ φ : SpecialLinearGroup (Fin (m + 1)) F ≃* K,
      ∀ g : SpecialLinearGroup (Fin (m + 1)) F,
        e (QuotientGroup.mk (φ g)) =
          (QuotientGroup.mk g : ProjectiveSpecialLinearGroup (Fin (m + 1)) F) := by
  have hperf : Group.IsPerfect K := Group.isPerfect_def.2 hK.1
  set ρ : K →* ProjectiveSpecialLinearGroup (Fin (m + 1)) F :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)) with hρdef
  have hρ : Function.Surjective ρ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ρ.ker = Subgroup.center K := by
    ext g
    rw [MonoidHom.mem_ker, hρdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff e e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hF2' : Nat.card F ≠ 2 := by
    intro h2
    rw [h2] at hpF
    have := Nat.le_of_dvd (by norm_num) hpF
    omega
  have hm3 : ¬ (m = 3 ∧ Nat.card F = 3) := by
    rintro ⟨rfl, -⟩
    norm_num at hp
  have hsep := CFSG.LieType.Steinberg.CentralExt.SLClosed.separating_of_card hm hF2' hF hm3
  obtain ⟨φ, hφs, hφρ⟩ :=
    CFSG.LieType.SeitzGeneration.exists_sl_cover_hom hm hsep ρ hρ hker.le
  have hcenter : Nat.card (Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F)) = m + 1 := by
    rw [CFSG.OrderReductions.LinearOrders.card_specialLinear_center F (m + 1) (by omega)]
    exact Nat.gcd_eq_left hpF
  have hbij : Function.Bijective φ := by
    refine bijective_of_cover
      (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F)))
      (QuotientGroup.mk'_surjective _) ρ hρ φ hφs hφρ ?_
    rw [QuotientGroup.ker_mk', hcenter, hker, hZ]
  exact ⟨MulEquiv.ofBijective φ hbij, fun g => hφρ g⟩

theorem exists_mulEquiv_sl_of_cover_three_four
    {K : Type} [Group K] [Finite K]
    (hK : CFSG.Open.IsQuasisimple K) {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4)
    (e : K ⧸ Subgroup.center K ≃* ProjectiveSpecialLinearGroup (Fin 3) F)
    (hZ : Nat.card (Subgroup.center K) = 3) :
    ∃ φ : SpecialLinearGroup (Fin 3) F ≃* K,
      ∀ g : SpecialLinearGroup (Fin 3) F,
        e (QuotientGroup.mk (φ g)) =
          (QuotientGroup.mk g : ProjectiveSpecialLinearGroup (Fin 3) F) := by
  have hperf : Group.IsPerfect K := Group.isPerfect_def.2 hK.1
  set ρ : K →* ProjectiveSpecialLinearGroup (Fin 3) F :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)) with hρdef
  have hρ : Function.Surjective ρ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ρ.ker = Subgroup.center K := by
    ext g
    rw [MonoidHom.mem_ker, hρdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff e e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hF' : Nat.card F = 2 ^ 2 := by rw [hF]; norm_num
  have hLie : CFSG.Blueprint.LieModel (ProjectiveSpecialLinearGroup (Fin 3) F) .PSL 3 2 2 :=
    Or.inl ⟨by decide, ⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩,
      F, inferInstance, inferInstance, hF',
      ⟨CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F⟩⟩
  obtain ⟨-, ⟨eM⟩⟩ :=
    CFSG.LieType.Multipliers.L34Upper.multiplier_PSL_three_four _ hLie
  have hcard : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
      (ProjectiveSpecialLinearGroup (Fin 3) F)) = 48 := by
    rw [← Nat.card_congr
      (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess
        (ProjectiveSpecialLinearGroup (Fin 3) F)).toEquiv, Nat.card_congr eM.toEquiv]
    simp [Nat.card_prod]
  haveI : Finite (CFSG.RankThree.PerfectCover.hopfMultiplier
      (ProjectiveSpecialLinearGroup (Fin 3) F)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hSLperf : Group.IsPerfect (SpecialLinearGroup (Fin 3) F) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (by norm_num)
  have hcenter : Nat.card (Subgroup.center (SpecialLinearGroup (Fin 3) F)) = 3 := by
    rw [CFSG.OrderReductions.LinearOrders.card_specialLinear_center F 3 (by norm_num), hF]
    norm_num
  set α : SpecialLinearGroup (Fin 3) F →* ProjectiveSpecialLinearGroup (Fin 3) F :=
    QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 3) F))
  have hαs : Function.Surjective α := QuotientGroup.mk'_surjective _
  have hαker : α.ker = Subgroup.center (SpecialLinearGroup (Fin 3) F) := QuotientGroup.ker_mk' _
  have hβp : IsPGroup 3 ρ.ker := by
    rw [hker]
    exact IsPGroup.of_card (n := 1) (by rw [hZ]; norm_num)
  have hM : (Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
      (ProjectiveSpecialLinearGroup (Fin 3) F))).factorization 3 ≤
        (Nat.card α.ker).factorization 3 := by
    rw [hcard, hαker, hcenter]
    norm_num [Nat.factorization]
  obtain ⟨φ, hφs, hφ⟩ := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.exists_hom_of_cover
    hSLperf hperf α hαs hαker.le ρ hρ hker.le Nat.prime_three hβp hM
  have hφρ : ∀ g, ρ (φ g) = α g := fun g => DFunLike.congr_fun hφ g
  have hbij : Function.Bijective φ := by
    refine bijective_of_cover α hαs ρ hρ φ hφs hφρ ?_
    rw [hαker, hcenter, hker, hZ]
  exact ⟨MulEquiv.ofBijective φ hbij, fun g => hφρ g⟩

end CFSG.LocalAnalysis.GLTheoremA
