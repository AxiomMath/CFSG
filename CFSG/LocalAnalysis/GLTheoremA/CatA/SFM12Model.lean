module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.KU6L2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM12Unit
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FU6Center

public section

namespace CFSG.LocalAnalysis.GLTheoremA.SFM12

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.Y10F


theorem charP_two_of_card {F : Type} [Field F] [Finite F] (h : Nat.card F = (2 ^ 2) ^ 2) :
    CharP F 2 := by
  haveI := Fintype.ofFinite F
  obtain ⟨p, hp, n, hpr, hcard⟩ := FiniteField.card' F
  have h16 : Fintype.card F = 16 := by
    rw [← Nat.card_eq_fintype_card, h]
    norm_num
  rw [h16] at hcard
  have hdvd : p ∣ 2 ^ 4 := by
    rw [show (2 : ℕ) ^ 4 = 16 by norm_num, hcard]
    exact dvd_pow_self p (PNat.ne_zero n)
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hpr Nat.prime_two).1 (hpr.dvd_of_dvd_pow hdvd)
  rw [← hp2]
  exact hp

theorem psu5_of_marked {X : Type} [Group X] (h : CFSG.StandardType.MarkedModel ⟨.twA, 4, 2⟩ X) :
    CFSG.Blueprint.LieModel X .PSU 5 2 2 := h

theorem forty_one_dvd_of_label {X : Type} [Group X] [Finite X]
    (hX : HasLabel X (fun l : GLALabel => l = ⟨.twA, 4, 2⟩)) :
    CFSG.Open.IsQuasisimple X ∧ 41 ∣ Nat.card X := by
  obtain ⟨-, hQ, hM⟩ := hasLabel_model hX
  have hLM := psu5_of_marked hM
  have hsc : CFSG.Open.StatedClassicalModel (X ⧸ Subgroup.center X) .PSU 5 2 2 := by
    rcases hLM with ⟨-, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact h
    all_goals omega
  obtain ⟨-, F5, hFi5, hFf5, hF5, ⟨e5⟩⟩ := hsc
  have hcardQ : Nat.card (X ⧸ Subgroup.center X) =
      Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSU 5 (2 ^ 2) F5)) :=
    Nat.card_congr e5.toEquiv
  have hform := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU (K := F5) Nat.prime_two
    (by norm_num) hF5 (by norm_num : 2 ≤ 5)
  have h41q : 41 ∣ Nat.card (X ⧸ Subgroup.center X) := by
    rw [hcardQ, hform]
    norm_num [Finset.prod_Icc_succ_top]
  refine ⟨hQ, ?_⟩
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X)]
  exact Dvd.dvd.mul_right h41q _

theorem U6Mem_of_unitaryDiag (hR : UnitaryDiagFact) : U6Mem := by
  classical
  unfold UnitaryDiagFact at hR
  intro L _ _ hL y J hord hlay hJlab
  have hZ : Subgroup.center L = ⊥ := u6Center_holds L hL
  obtain ⟨-, -, hM6⟩ := hasLabel_model hL
  have hLM6 := i61_model_psu hM6 (lab := ⟨.twA, 5, 2⟩) rfl rfl
  have hsc6 : CFSG.Open.StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 6 2 2 := by
    rcases hLM6 with ⟨-, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact h
    all_goals omega
  obtain ⟨-, F, hFi, hFf, hF, ⟨e⟩⟩ := hsc6
  have hF' : Nat.card F = (2 ^ 2) ^ 2 := hF
  haveI : CharP F 2 := charP_two_of_card hF'
  have hscal : (CFSG.Open.StatedScalars (Fin 6) F).subgroupOf (CFSG.Open.StatedSU 6 (2 ^ 2) F) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨c, hc⟩ := (MonoidHom.mem_range).1 hx
    have hcSU : Matrix.GeneralLinearGroup.scalar (Fin 6) c ∈ CFSG.Open.StatedSU 6 (2 ^ 2) F := by
      rw [hc]
      exact x.2
    have hkey := ((CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hF' (n := 6)
      (by norm_num)).2.1 c).1 hcSU
    have h6 : c ^ 6 = 1 := hkey.1
    have h5 : c ^ 5 = 1 := by simpa using hkey.2
    have hc1 : c = 1 := by
      have key : c = c ^ 6 * (c ^ 5)⁻¹ := by group
      rw [h6, h5] at key
      simpa using key
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    rw [← hc, hc1, map_one]
    rfl
  let Φ1 : CFSG.Open.StatedProj (CFSG.Open.StatedSU 6 (2 ^ 2) F) ≃*
      ↥(CFSG.Open.StatedSU 6 (2 ^ 2) F) :=
    (QuotientGroup.quotientMulEquivOfEq hscal).trans QuotientGroup.quotientBot
  let Φ0 : L ≃* L ⧸ Subgroup.center L :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  let Φ : L ≃* ↥(CFSG.Open.StatedSU 6 (2 ^ 2) F) := Φ0.trans (e.trans Φ1)
  have hgord : orderOf (Φ y) = 5 := (orderOf_injective Φ.toMonoidHom Φ.injective y).trans hord
  have hg5 : (Φ y) ^ 5 = 1 := by
    rw [← hgord]
    exact pow_orderOf_eq_one _
  have hg1 : Φ y ≠ 1 := by
    intro h
    have hy1 : y = 1 := Φ.injective (h.trans (map_one Φ).symm)
    rw [hy1, orderOf_one] at hord
    norm_num at hord
  have hCy : Subgroup.centralizer ({Φ y} : Set ↥(CFSG.Open.StatedSU 6 (2 ^ 2) F)) =
      (Subgroup.centralizer ({y} : Set L)).map Φ.toMonoidHom := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · intro hx
      rw [Subgroup.mem_centralizer_iff] at hx
      have hx' : Φ y * x = x * Φ y := hx _ (Set.mem_singleton _)
      refine ⟨Φ.symm x, ?_, by simp⟩
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      apply Φ.injective
      simp only [map_mul, MulEquiv.apply_symm_apply]
      exact hx'
    · rintro ⟨c, hc, rfl⟩
      rw [Subgroup.mem_centralizer_iff] at hc ⊢
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      show Φ y * Φ c = Φ c * Φ y
      rw [← map_mul, ← map_mul, hc y (Set.mem_singleton _)]
  have hJsub : J ≤ Subgroup.centralizer ({y} : Set L) := by
    rw [← hlay]
    exact glaLayer_le _
  have hlay' : GLALayer (Subgroup.centralizer ({Φ y} : Set ↥(CFSG.Open.StatedSU 6 (2 ^ 2) F))) =
      J.map Φ.toMonoidHom := by
    rw [hCy, glaLayer_map (ι := Φ.toMonoidHom) Φ.injective, hlay]
  have hJ'lab : HasLabel ↥(J.map Φ.toMonoidHom) (fun lab : GLALabel => lab = ⟨.twA, 4, 2⟩) :=
    (hasLabel_congr (Subgroup.equivMapOfInjective J Φ.toMonoidHom Φ.injective) _).1 hJlab
  obtain ⟨hJ'q, h41⟩ := forty_one_dvd_of_label hJ'lab
  have hJC : J.map Φ.toMonoidHom ≤ Subgroup.centralizer ({Φ y} : Set ↥(CFSG.Open.StatedSU 6 (2 ^ 2) F)) := by
    rw [hCy]
    exact Subgroup.map_mono hJsub
  have hnorm : ∀ c ∈ Subgroup.centralizer ({Φ y} : Set ↥(CFSG.Open.StatedSU 6 (2 ^ 2) F)),
      ∀ j ∈ J.map Φ.toMonoidHom, c * j * c⁻¹ ∈ J.map Φ.toMonoidHom := by
    intro c hc j hj
    rw [hCy, Subgroup.mem_map] at hc
    obtain ⟨c0, hc0, rfl⟩ := hc
    obtain ⟨j0, hj0, rfl⟩ := Subgroup.mem_map.1 hj
    have hmem : (MulAut.conj c0).toMonoidHom j0 ∈ J := by
      rw [← hlay]
      exact glaLayer_conj_le _ hc0 (Subgroup.mem_map_of_mem _ (hlay ▸ hj0))
    have e : Φ.toMonoidHom c0 * Φ.toMonoidHom j0 * (Φ.toMonoidHom c0)⁻¹ =
        Φ.toMonoidHom ((MulAut.conj c0).toMonoidHom j0) := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
    rw [e]
    exact Subgroup.mem_map_of_mem _ hmem
  have hmemK := core_general (F := F) hF' (fun g hg => hR F hF' g hg) hg5 hg1 hJ'q hJC hnorm h41
  obtain ⟨j, hj, hjy⟩ := Subgroup.mem_map.1 hmemK
  have hjy' : j = y := Φ.injective hjy
  rw [← hjy']
  exact hj

theorem U6Mem_holds : U6Mem := U6Mem_of_unitaryDiag unitaryDiagFact_holds

end CFSG.LocalAnalysis.GLTheoremA.SFM12
