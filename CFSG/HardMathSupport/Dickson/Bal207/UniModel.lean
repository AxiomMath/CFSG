module

public import CFSG.HardMathSupport.Dickson.Bal207.FCInner
public import CFSG.Open.GriessAllModelsStatement
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder
import CFSG.HardMathSupport.Dickson.Bal207.Center
import CFSG.HardMathSupport.Dickson.Bal207.UniFrame
import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Models
import CFSG.Adapters.TauCetiLieModels
import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield
import CFSG.RankThree.PartOne.KC.UnitaryRegularUnipotentLift
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.Uni

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207Aux CFSG.Blueprint.Multiplier
  CFSG.HardMathSupport.Dickson.Bal207.FirstClaim

theorem uni_model (hGA : GriessAllModelsStatement) {p : ℕ} {K : Type} [Group K] [Finite K]
    (hK : CFSG.Open.IsQuasisimple K) (hL : IsLieQuot K (FamUni p)) :
    p = 3 ∧ Nat.Coprime 3 (Nat.card (Subgroup.center K)) ∧
      ∃ (f : ℕ) (F : Type) (_ : Field F) (h : UnitaryFieldData 2 f F) (n : ℕ),
        (f = 1 ∨ f = 3) ∧ 4 ≤ n ∧ ¬ 3 ∣ n ∧
          Nonempty ((K ⧸ Subgroup.center K) ≃* primeFormP h (oneGram F n)) := by
  obtain ⟨⟨dd, hv⟩, hd, ⟨e⟩⟩ := hL
  cases dd with
  | twistedA r q =>
    obtain ⟨⟨rfl, -⟩, h3, hq⟩ := hd
    have hp2 : q.p = 2 := by rcases hq with ⟨h, -⟩ | ⟨h, -⟩ <;> exact h
    have hf : q.exponent = 1 ∨ q.exponent = 3 := by
      rcases hq with ⟨-, h⟩ | ⟨-, h⟩
      · exact Or.inl h
      · exact Or.inr h
    refine ⟨rfl, ?_, ?_⟩
    · have hL := CFSG.Models.lieModel_twistedA r q hv (MulEquiv.refl _)
      have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩ = 2 := by
        rw [← hp2]
        exact TauCeti.LieTypeIndex.characteristic_twistedA r q
      rw [hc] at hL
      have hg : ¬ 3 ∣ (genericOrders .PSU (r + 1) 2
          (TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA r q, hv⟩)).1 := by
        simp only [genericOrders]
        intro h
        exact h3 (Nat.dvd_trans h (Nat.gcd_dvd_left _ _))
      exact centerAux_coprime_of_card_le_one Nat.prime_three
        ((CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.center_torsion_le hGA hK e hL
          Nat.prime_three).trans (centerAux_torsBound_eq_one (Or.inl rfl) hg).le)
    · have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
      rw [hp2] at hm
      obtain ⟨⟨hℓ, hm1, hn3, hne⟩, F, _, _, hF, ⟨e'⟩⟩ := hm
      have hU : UnitaryFieldData 2 q.exponent F := ⟨hℓ, hm1, by rw [hF, ← pow_mul, mul_comm]⟩
      have hq' : ¬(r + 1 = 3 ∧ 2 ^ q.exponent = 2) := fun ⟨h1, h2⟩ => hne (by rw [h1, h2])
      obtain ⟨⟨eT⟩, -⟩ := unitary_prime_form_full_semilinear_realization hU
        (isPrimeFormGram_one (n := r + 1)) hn3 hq'
      exact ⟨q.exponent, F, inferInstance, hU, r + 1, hf, by omega, h3,
        ⟨(e'.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hU (by omega)).symm).trans
          eT.symm⟩⟩
  | _ => exact (hd.2 : False).elim

section Field

variable {f n : ℕ} {F : Type} [Field F] (h : UnitaryFieldData 2 f F)

theorem uni_three_dvd (hf : f = 1 ∨ f = 3) : 3 ∣ 2 ^ f + 1 := by
  rcases hf with rfl | rfl <;> norm_num

theorem uni_gcd_eq_one (hf : f = 1 ∨ f = 3) (h3 : ¬ 3 ∣ n) : Nat.gcd n (2 ^ f + 1) = 1 := by
  have hc : Nat.Coprime n 3 :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3)
  rcases hf with rfl | rfl
  · exact hc
  · exact Nat.Coprime.pow_right 2 hc

theorem uni_units_eq_one (hf : f = 1 ∨ f = 3) (h3 : ¬ 3 ∣ n) {c : Fˣ} (hcn : (c : F) ^ n = 1)
    (hN : h.norm (c : F) = 1) : c = 1 := by
  have h1 : c ^ n = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hcn, Units.val_one])
  have h2 : c ^ (2 ^ f + 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, ← hN, UnitaryFieldData.norm, h.bar_apply,
      pow_succ, mul_comm]
  have hd : orderOf c ∣ Nat.gcd n (2 ^ f + 1) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
  rw [uni_gcd_eq_one hf h3, Nat.dvd_one, orderOf_eq_one_iff] at hd
  exact hd

theorem uni_ne_three (h3 : ¬ 3 ∣ n) : ¬(n = 3 ∧ 2 ^ f = 2) := by
  rintro ⟨rfl, -⟩
  exact h3 (dvd_refl 3)

theorem uni_normOneScalars_eq_bot (hf : f = 1 ∨ f = 3) (h3 : ¬ 3 ∣ n) (hn : 1 ≤ n) :
    normOneScalars h (gramSU h (oneGram F n)) n = ⊥ := by
  have hc := CFSG.RankThree.Classical.card_normOneScalars_one h hn
  rw [uni_gcd_eq_one hf h3] at hc
  exact Subgroup.eq_bot_of_card_eq _ hc

theorem uni_center_eq_bot (hn : 3 ≤ n) (h3 : ¬ 3 ∣ n) :
    Subgroup.center (primeFormP h (oneGram F n)) = ⊥ :=
  CFSG.RankThree.PartOne.KCUnitaryRegular.center_primeFormP_eq_bot h (C := 1)
    isPrimeFormGram_one hn (uni_ne_three h3)

theorem uni_eq_one_of_conjHom_eq_one (hf : f = 1 ∨ f = 3) (hn : 3 ≤ n) (h3 : ¬ 3 ∣ n)
    (t : primeFormUnitary h (oneGram F n))
    (hdet : ((t : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1)
    (h1 : primeFormConjHom h (oneGram F n) t = 1) : (t : GL (Fin n) F) = 1 := by
  have hC : IsPrimeFormGram (1 : GL (Fin n) F) := isPrimeFormGram_one
  have hpsi : primeFormPsi h hC ⟨t, 1⟩ = 1 := by
    rw [primeFormPsi_apply, map_one, mul_one]
    exact h1
  obtain ⟨-, c, hcN, hc⟩ := (primeFormPsi_eq_one_iff h hC hn _).1 hpsi
  have hc' : (t : GL (Fin n) F) = GeneralLinearGroup.scalar (Fin n) c := hc
  have hcn : (c : F) ^ n = 1 := by
    have e := congrArg Units.val (GeneralLinearGroup.det_scalar (n := Fin n) c)
    rw [Units.val_pow_eq_pow_val, Fintype.card_fin] at e
    rw [← e, ← hdet, hc']
    rfl
  rw [hc', uni_units_eq_one h hf h3 hcn hcN, map_one]

theorem uni_exists_conjHom_eq (hf : f = 1 ∨ f = 3) (hn : 3 ≤ n) (h3 : ¬ 3 ∣ n)
    (A : primeFormUnitary h (oneGram F n)) :
    ∃ s : gramSU h (oneGram F n),
      primeFormConjHom h (oneGram F n) A = primeFormConjHom h (oneGram F n) ⟨s, s.2.1⟩ := by
  obtain ⟨-, -, hcard, -⟩ := unitary_full_diagonal_outer_order h hn (uni_ne_three h3)
  rw [uni_gcd_eq_one hf h3] at hcard
  have htop := Subgroup.index_eq_one.1 hcard
  have hmem : (⟨primeFormConjHom h (oneGram F n) A, ⟨A, rfl⟩⟩ :
      primeFormD h (oneGram F n)) ∈
        (CFSG.ComponentClassification.OuterAutomorphisms.inner
          (primeFormP h (oneGram F n))).subgroupOf (primeFormD h (oneGram F n)) := by
    rw [htop]
    exact Subgroup.mem_top _
  exact (mem_inner_primeFormP h _ _).1 hmem

theorem uni_fix_cube_root {σ : F ≃+* F} (hσ : σ ^ 3 = 1) {ω : F} (hω : ω ^ 3 = 1) : σ ω = ω := by
  by_cases h1 : ω = 1
  · rw [h1, map_one]
  have hs := frame_one_add_add_sq hω h1
  have hu3 : (σ ω) ^ 3 = 1 := by rw [← map_pow, hω, map_one]
  have hfac : (σ ω - 1) * ((σ ω - ω) * (σ ω - ω ^ 2)) = 0 := by
    linear_combination hu3 - (σ ω - 1) * σ ω * hs + (σ ω - 1) * hω
  have hσ1 : σ ω - 1 ≠ 0 := by
    rw [sub_ne_zero]
    intro he
    exact h1 (σ.injective (by rw [he, map_one]))
  rcases mul_eq_zero.1 ((mul_eq_zero.1 hfac).resolve_left hσ1) with he | he
  · exact sub_eq_zero.1 he
  · exfalso
    have hu : σ ω = ω ^ 2 := sub_eq_zero.1 he
    have h2 : σ (ω ^ 2) = ω := by
      rw [map_pow, hu, ← pow_mul]
      linear_combination ω * hω
    have h3' : (σ ^ 3) ω = ω ^ 2 := by
      rw [RingAut.coe_pow]
      show σ (σ (σ ω)) = ω ^ 2
      rw [hu, h2, hu]
    rw [hσ, RingAut.one_apply] at h3'
    have : ω * (ω - 1) = 0 := by linear_combination -h3'
    rcases mul_eq_zero.1 this with h0 | h0
    · rw [h0] at hω
      norm_num at hω
    · exact h1 (sub_eq_zero.1 h0)

end Field

end CFSG.HardMathSupport.Dickson.Bal207.Uni

end
