module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2SU
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Lift
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87MultMilestone
public import CFSG.Foundations.SteinbergCADefinitionNodes
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.StandardType.Marking

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.SectionRank.OddCover
open CFSG.LocalAnalysis.ComponentInitial


theorem rk2_model_of_isLabel {X : Type} [Group X] [Finite X] {lab : GLALabel} (h : Rk2IsLabel X lab) :
    CFSG.Open.IsQuasisimple X ∧ LargeEvenInLambda2 lab ∧
      CFSG.StandardType.MarkedModel lab (X ⧸ Subgroup.center X) := by
  obtain ⟨hL, lab', hlab', hraw⟩ := CFSG.StandardType.Canonical.largeEvenMarking_markedModel h
  obtain ⟨R, _, I, F, hQ⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  obtain ⟨hs, -, θ, hP, hm⟩ := hQ
  have hP' : lab' = lab := hP
  subst hP'
  exact ⟨⟨hL, (θ.isSimpleGroup_congr).2 hs⟩, hlab', CFSG.StandardType.MarkedModel.of_mulEquiv θ.symm hm⟩

theorem rk2_card_griess_twA {S : Type} [Group S] {ℓ n : ℕ}
    (hS : CFSG.Blueprint.LieModel S .PSU (ℓ + 1) 2 n)
    (hex : Multiplier.exceptionalOrders .PSU (ℓ + 1) 2 n = (1, 1)) :
    Nat.card (CFSG.Open.griessHopfMultiplier S) = Nat.gcd (ℓ + 1) (2 ^ n + 1) := by
  obtain ⟨-, ⟨eG⟩⟩ := CFSG.Milestones.cl_lit_griess_schur_multipliers_all_native_models
    S .PSU (ℓ + 1) 2 n hS
  have hcard : Nat.card (CFSG.Open.griessHopfMultiplier S) =
      ((Multiplier.genericOrders .PSU (ℓ + 1) 2 n).1 * (Multiplier.genericOrders .PSU (ℓ + 1) 2 n).2) *
        ((Multiplier.exceptionalOrders .PSU (ℓ + 1) 2 n).1 *
          (Multiplier.exceptionalOrders .PSU (ℓ + 1) 2 n).2) := by
    rw [Nat.card_congr eG.toEquiv, CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_generic_exceptional']
  have hg : Multiplier.genericOrders .PSU (ℓ + 1) 2 n = (Nat.gcd (ℓ + 1) (2 ^ n + 1), 1) := rfl
  rw [hex, hg] at hcard
  simpa using hcard

theorem rk2_card_center_dvd_twA {X : Type} [Group X] [Finite X] {ℓ n : ℕ}
    (hX : Rk2IsLabel X ⟨.twA, ℓ, n⟩)
    (hex : Multiplier.exceptionalOrders .PSU (ℓ + 1) 2 n = (1, 1)) :
    Nat.card (Subgroup.center X) ∣ Nat.gcd (ℓ + 1) (2 ^ n + 1) := by
  obtain ⟨hQ, -, hM⟩ := rk2_model_of_isLabel hX
  have hM' : CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) .PSU (ℓ + 1) 2 n := hM
  have hQ' : CFSG.IsQuasisimple X := (CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1.2 hQ
  have hcard := rk2_card_griess_twA hM' hex
  have hgpos : Nat.gcd (ℓ + 1) (2 ^ n + 1) ≠ 0 := (Nat.gcd_pos_of_pos_right _ (by positivity)).ne'
  haveI : Finite (CFSG.Open.griessHopfMultiplier (X ⧸ Subgroup.center X)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact hgpos)
  have h1 := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_hopf hQ' (MulEquiv.refl _)
  rwa [hcard] at h1

theorem rk2_inf_center_eq_bot {X : Type} [Group X] [Finite X] {q k : ℕ} (hq : q.Prime) {A : Subgroup X}
    (hA : Nat.card A = q ^ k) (hZ : ¬ q ∣ Nat.card (Subgroup.center X)) :
    A ⊓ Subgroup.center X = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have h1 : orderOf x ∣ q ^ k := hA ▸ Subgroup.orderOf_dvd_natCard A hx.1
  have h2 : orderOf x ∣ Nat.card (Subgroup.center X) := Subgroup.orderOf_dvd_natCard _ hx.2
  have hcop : Nat.Coprime (q ^ k) (Nat.card (Subgroup.center X)) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hq).2 hZ)
  rw [Subgroup.mem_bot]
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem rk2_twA_pRank_le {X : Type} [Group X] [Finite X] {ℓ n q : ℕ}
    (hX : Rk2IsLabel X ⟨.twA, ℓ, n⟩) (hex : Multiplier.exceptionalOrders .PSU (ℓ + 1) 2 n = (1, 1))
    (hq : q.Prime) (hq2 : q ≠ 2) (hqQ : ¬ q ∣ 2 ^ n + 1) :
    CFSG.Open.pRank q (⊤ : Subgroup X) ≤ (ℓ + 1) / 2 := by
  obtain ⟨hQ, hl, hM⟩ := rk2_model_of_isLabel hX
  have hM' : CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) .PSU (ℓ + 1) 2 n := hM
  obtain ⟨-, F, hF, hFin, hcard, ⟨e⟩⟩ := hM'.statedClassicalModel (by decide)
  have hn1 : 1 ≤ n := hl.1
  have hFD : UnitaryFieldData 2 n F :=
    ⟨Nat.prime_two, hn1, by rw [hcard, ← pow_mul, mul_comm]⟩
  haveI : CharP F 2 := hFD.charP
  haveI : Fact q.Prime := ⟨hq⟩
  have hZ : ¬ q ∣ Nat.card (Subgroup.center X) := fun hd =>
    hqQ ((hd.trans (rk2_card_center_dvd_twA hX hex)).trans (Nat.gcd_dvd_right _ _))
  set H : Subgroup (GL (Fin (ℓ + 1)) F) := StatedSU (ℓ + 1) (2 ^ n) F with hH
  set D : Subgroup H := (StatedScalars (Fin (ℓ + 1)) F).subgroupOf H with hD
  have hDq : ¬ q ∣ Nat.card D := by
    have hDe : Nat.card D ∣ 2 ^ n + 1 := card_scalars_dvd (by omega) H fun x c hc => by
      have hu := unitary_of_mem_statedSU (p := 2) (f := n) hcard x.1.2
      rw [hc, Matrix.GeneralLinearGroup.coe_scalar] at hu
      have h00 := congrFun (congrFun hu ⟨0, by omega⟩) ⟨0, by omega⟩
      rw [Matrix.scalar_apply, Matrix.diagonal_map (by simp), Matrix.diagonal_transpose,
        Matrix.diagonal_mul_diagonal, Matrix.one_apply_eq, Matrix.diagonal_apply_eq] at h00
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, pow_succ, Units.val_one]
      exact h00
    exact fun hd => hqQ (hd.trans hDe)
  let α : H →* StatedProj H := QuotientGroup.mk' D
  have hα : Function.Surjective α := QuotientGroup.mk'_surjective D
  have hαk : α.ker = D := QuotientGroup.ker_mk' D
  obtain ⟨A, -, hA, hAcard⟩ := CFSG.SectionRank.exists_pRank hq.one_lt (⊤ : Subgroup X)
  let φ : X →* StatedProj H := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  have hφx : ∀ x, φ x = e (QuotientGroup.mk x) := fun x => rfl
  have hφk : ∀ x, φ x = 1 → x ∈ Subgroup.center X := by
    intro x hx
    rw [hφx] at hx
    exact (QuotientGroup.eq_one_iff x).1 ((MulEquiv.map_eq_one_iff e).1 hx)
  have hinf := rk2_inf_center_eq_bot hq hAcard hZ
  have hφA : ∀ a b : A, φ a = φ b → a = b := by
    intro a b hab
    have h1 : φ ((a : X)⁻¹ * b) = 1 := by rw [map_mul, map_inv, hab, inv_mul_cancel]
    have h2 : (a : X)⁻¹ * b ∈ A ⊓ Subgroup.center X :=
      ⟨A.mul_mem (A.inv_mem a.2) b.2, hφk _ h1⟩
    rw [hinf, Subgroup.mem_bot, inv_mul_eq_one] at h2
    exact Subtype.ext h2
  have hAmap : Nat.card (A.map φ) = Nat.card A := by
    refine (Nat.card_congr (Equiv.ofBijective
      (fun a : A => (⟨φ a, Subgroup.mem_map_of_mem φ a.2⟩ : A.map φ)) ⟨fun a b hab => hφA a b
        (congrArg Subtype.val hab), ?_⟩)).symm
    rintro ⟨_, ⟨a, ha, rfl⟩⟩
    exact ⟨⟨a, ha⟩, rfl⟩
  have hĀ : IsElemAbelian q (A.map φ) := CFSG.SectionRank.isElemAbelian_map hA φ
  obtain ⟨B, hB, hBcard⟩ := rk2_lift_elemAbelian hq α hα (by rw [hαk]; exact hDq) hĀ
  set B' : Subgroup (GL (Fin (ℓ + 1)) F) := B.map H.subtype with hB'
  have hB'el : IsElemAbelian q B' := CFSG.SectionRank.isElemAbelian_map hB H.subtype
  have hB'card : Nat.card B' = Nat.card B := Subgroup.card_map_of_injective H.subtype_injective
  have hB'H : ∀ g ∈ B', g ∈ H := by
    rintro _ ⟨b, -, rfl⟩
    exact b.2
  have hrK : (q : F) ≠ 0 := CFSG.RankThree.PartOne.LIT.natCast_ne_zero_of_charTwo hq hq2
  have hσ : ∀ c : F, c ^ q = 1 → c * hFD.bar c = 1 → c = 1 := by
    intro c hc1 hc2
    rw [hFD.bar_apply, ← pow_succ'] at hc2
    have hg : c ^ Nat.gcd q (2 ^ n + 1) = 1 := pow_gcd_eq_one.mpr ⟨hc1, hc2⟩
    rwa [Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd hq).2 hqQ), pow_one] at hg
  have hbound := rk2_card_le_unitary hFD.bar hFD.bar_bar hq hrK hσ B'
    (fun g hg k hk => isElemAbelian_commute hB'el hg hk) (fun g hg => hB'el.2 g hg) (fun g hg => by
      have := (CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff hFD).1 (hB'H g hg)
      exact this.2)
  have hk : q ^ CFSG.Open.pRank q (⊤ : Subgroup X) ≤ q ^ ((ℓ + 1) / 2) := by
    rw [← hAcard, ← hAmap, ← hBcard, ← hB'card]
    exact hbound
  exact (Nat.pow_le_pow_iff_right hq.one_lt).1 hk

end CFSG.LocalAnalysis.GLTheoremA
