module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigInvPt
public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigInvA9
public import CFSG.GH74.GLS.Stage2.Local.P34Sp4OddM
public import CFSG.GH74.GLS.Stage2.Local.P34Sp4OddN
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KASp4Q3U1

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.CatFactsSp4
open SymplecticHigher SymplecticFlag

variable {F : Type} [Field F] [Finite F]

theorem odd_natCard_of_ringChar_ne_two (hodd : ringChar F ≠ 2) : Odd (Nat.card F) := by
  classical
  have := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card]
  exact Nat.odd_iff.mpr (FiniteField.odd_card_of_char_ne_two hodd)

omit [Finite F] in
theorem even_natCard_psp4 (h2 : (2 : F) ≠ 0) : Even (Nat.card (StatedProj (StatedSp 2 F))) := by
  have hn : (negOneSL : Matrix.SpecialLinearGroup (Fin 2) F) * negOneSL = 1 := by
    have h := pow_orderOf_eq_one (negOneSL : Matrix.SpecialLinearGroup (Fin 2) F)
    rw [orderOf_negOneSL h2] at h
    exact (pow_two _).symm.trans h
  have hu : u1 F ^ 2 = 1 := by
    rw [pow_two, u1_eq_proj_blkSL, ← map_mul, ← map_mul, Prod.mk_mul_mk, mul_one, hn]
    show proj 2 F (blkSL F 1) = 1
    rw [map_one, map_one]
  have ho : orderOf (u1 F) = 2 := orderOf_eq_prime hu (u1_ne_one h2)
  have hd : orderOf (u1 F) ∣ Nat.card (StatedProj (StatedSp 2 F)) := orderOf_dvd_natCard _
  rw [ho] at hd
  exact even_iff_two_dvd.mpr hd

theorem oddNormal_u1_eq_bot (h2 : (2 : F) ≠ 0) (hc1 : pPrimeCore 2 ↥(E1 F) = ⊥)
    (hc2 : pPrimeCore 2 ↥(E2 F) = ⊥) {R : Subgroup (StatedProj (StatedSp 2 F))}
    (hRD : R ≤ centralizer {u1 F}) (hnorm : ∀ d ∈ centralizer {u1 F}, ∀ r ∈ R, d * r * d⁻¹ ∈ R)
    (hodd' : ∀ r ∈ R, Odd (orderOf r)) : R = ⊥ := by
  have hE1 : R ⊓ E1 F = ⊥ := GH74.GLS.Stage2.Local.P34.inf_eq_bot_of_pPrimeCore hnorm hodd'
    ((E1_le_X0 h2).trans X0_le_centralizer) hc1
  have hE2 : R ⊓ E2 F = ⊥ := GH74.GLS.Stage2.Local.P34.inf_eq_bot_of_pPrimeCore hnorm hodd'
    ((E2_le_X0 h2).trans X0_le_centralizer) hc2
  have hX0 : ∀ m ∈ R, m ∈ X0 F → m = 1 := by
    intro m hmR hmX
    have hc : ∀ y ∈ E2 F, m * y = y * m := by
      intro y hy
      have hyD : y ∈ centralizer {u1 F} := (E2_le_X0 h2).trans X0_le_centralizer hy
      have h1 : y * m⁻¹ * y⁻¹ ∈ R := hnorm y hyD m⁻¹ (R.inv_mem hmR)
      have h2' : m * y * m⁻¹ ∈ E2 F := conj_mem_E2 h2 hmX hy
      have e : m * (y * m⁻¹ * y⁻¹) = (m * y * m⁻¹) * y⁻¹ := by group
      have h3 : m * (y * m⁻¹ * y⁻¹) ∈ R ⊓ E2 F := by
        refine ⟨R.mul_mem hmR h1, ?_⟩
        rw [e]
        exact (E2 F).mul_mem h2' ((E2 F).inv_mem hy)
      rw [hE2, Subgroup.mem_bot, e] at h3
      have h4 : m * y * m⁻¹ = y := mul_inv_eq_one.mp h3
      calc m * y = (m * y * m⁻¹) * m := by group
        _ = y * m := by rw [h4]
    have : m ∈ R ⊓ E1 F := ⟨hmR, mem_E1_of_commute_E2 h2 hmX hc⟩
    rw [hE1, Subgroup.mem_bot] at this
    exact this
  rw [eq_bot_iff]
  intro r hr
  have hsq : r * r = 1 :=
    hX0 _ (R.mul_mem hr hr) (GH74.GLS.Stage2.Local.P34.sq_mem_X0 (hRD hr))
  have hdvd : orderOf r ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
  · exact (Subgroup.mem_bot).mpr (orderOf_eq_one_iff.mp h1)
  · exact absurd (h1 ▸ hodd' r hr) (by decide)

theorem involutionOddCore_u1_eq_bot (hodd : ringChar F ≠ 2) :
    Assembly.Dichotomy.involutionOddCore (u1 F) = ⊥ := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hodd
  have hoddF := odd_natCard_of_ringChar_ne_two hodd
  obtain ⟨hc1, hc2⟩ : pPrimeCore 2 ↥(E1 F) = ⊥ ∧ pPrimeCore 2 ↥(E2 F) = ⊥ := by
    by_cases h3 : Nat.card F = 3
    · exact ⟨GH74.GLS.Stage2.Signalizer.Ivk8.kaQ3_pPrimeCore_E1 h3,
        GH74.GLS.Stage2.Signalizer.Ivk8.kaQ3_pPrimeCore_E2 h3⟩
    · have h1 : 1 < Nat.card F := Finite.one_lt_card
      have h4 : 4 ≤ Nat.card F := by
        obtain ⟨k, hk⟩ := hoddF
        omega
      exact ⟨pPrimeCore_E1 h2 h4, pPrimeCore_E2 h2 h4⟩
  have hA : Odd (Nat.card (Assembly.Dichotomy.involutionOddCore (u1 F))) := by
    rw [ClassicalInvolution.Balance.involutionOddCore_eq_oddCoreCentralizer]
    exact ClassicalInvolution.Balance.odd_card_oddCoreCentralizer _
  refine oddNormal_u1_eq_bot h2 hc1 hc2 ?_
    (fun d hd r hr => ClassicalInvolution.Balance.conj_mem_involutionOddCore hd hr)
    (fun r hr => Odd.of_dvd_nat hA (Subgroup.orderOf_dvd_natCard _ hr))
  rw [Assembly.Dichotomy.involutionOddCore]
  exact map_subtype_le _

theorem rigid_u1 (hodd : ringChar F ≠ 2) {β : MulAut (StatedProj (StatedSp 2 F))}
    (hβ : Odd (orderOf β))
    (hβC : ∀ c ∈ centralizer ({u1 F} : Set (StatedProj (StatedSp 2 F))), β c = c) : β = 1 :=
  GH74.GLS.Stage2.Local.P34.odd_aut_fix_trivial (odd_natCard_of_ringChar_ne_two hodd) hβ
    (fun x hx => hβC x (X0_le_centralizer (E1_le_X0 (Ring.two_ne_zero hodd) hx)))
    (fun x hx => hβC x (X0_le_centralizer (E2_le_X0 (Ring.two_ne_zero hodd) hx)))

theorem rigidAt_proj (hodd : ringChar F ≠ 2) {y : StatedSp 2 F} (hy : y * y = 1) :
    Assembly.Dichotomy.involutionOddCore (proj 2 F y) = ⊥ ∧
      ∀ β : MulAut (StatedProj (StatedSp 2 F)), Odd (orderOf β) →
        (∀ c ∈ centralizer ({proj 2 F y} : Set (StatedProj (StatedSp 2 F))), β c = c) →
          β = 1 := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hodd
  by_cases hy1 : proj 2 F y = 1
  · rw [hy1]
    have := GH74.GLS.Stage2.Signalizer.Odd87.isSimpleGroup_psp4_of_odd hodd
    refine ⟨involutionOddCore_one_eq_bot_of_simple (even_natCard_psp4 h2),
      fun β _ hβ => MulEquiv.ext fun g => hβ g ?_⟩
    rw [mem_centralizer_singleton_iff, one_mul, mul_one]
  · have hy1' : y ≠ 1 := fun h => hy1 (by rw [h, map_one])
    have hyn : y ≠ negS F := by
      rintro rfl
      apply hy1
      rw [← MonoidHom.mem_ker, ker_proj, mem_spScalars_iff]
      exact Or.inr rfl
    obtain ⟨g, hg⟩ := exists_conj_T1_of_sq h2 hy hy1' hyn
    have hα : MulAut.conj (proj 2 F g)⁻¹ (proj 2 F y) = u1 F := by
      rw [MulAut.conj_apply, inv_inv, ← map_inv, ← map_mul, ← map_mul, hg]
      rfl
    have hx2 : proj 2 F y * proj 2 F y = 1 := by rw [← map_mul, hy, map_one]
    refine rigidAt_of_mulAut (MulAut.conj (proj 2 F g)⁻¹) hx2 ?_ ?_
    · rw [hα]
      exact involutionOddCore_u1_eq_bot hodd
    · rw [hα]
      exact fun β hβ hβC => rigid_u1 hodd hβ hβC

theorem involutionOddCore_conj_proj_eq_bot (hodd : ringChar F ≠ 2) {y : StatedSp 2 F}
    (hy : y * y = 1) (H : Subgroup (MulAut (StatedProj (StatedSp 2 F))))
    (hH : (MulAut.conj : StatedProj (StatedSp 2 F) →* MulAut (StatedProj (StatedSp 2 F))).range ≤
      H) :
    Assembly.Dichotomy.involutionOddCore (⟨MulAut.conj (proj 2 F y), hH ⟨_, rfl⟩⟩ : H) = ⊥ := by
  obtain ⟨hO, hR⟩ := rigidAt_proj hodd hy
  exact involutionOddCore_eq_bot_of_rigidAt
    (GH74.GLS.Stage2.Signalizer.Odd87.center_psp4_eq_bot hodd) hO hR H hH

theorem isInvolutionCoreFreeInv_statedSp_two (hodd : ringChar F ≠ 2) :
    IsInvolutionCoreFreeInv ↥(StatedSp 2 F) := by
  intro H hH y hy
  have hZ : center ↥(StatedSp 2 F) = spScalars 2 F :=
    CFSG.LieType.Universal.Symplectic.center_eq 2 F
  set e : (↥(StatedSp 2 F) ⧸ center ↥(StatedSp 2 F)) ≃* StatedProj (StatedSp 2 F) :=
    QuotientGroup.quotientMulEquivOfEq hZ with he
  have hy2 : (QuotientGroup.mk y : ↥(StatedSp 2 F) ⧸ center ↥(StatedSp 2 F)) *
      QuotientGroup.mk y = 1 := by
    rw [← QuotientGroup.mk_mul, hy, QuotientGroup.mk_one]
  refine involutionOddCore_conj_eq_bot_of_mulEquiv e.symm hy2 (fun H' hH' => ?_) H hH
  have hey : e.symm.symm (QuotientGroup.mk y) = proj 2 F y := by
    rw [MulEquiv.symm_symm, he, QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  have key : ∀ (p : StatedProj (StatedSp 2 F)) (_ : p = proj 2 F y),
      Assembly.Dichotomy.involutionOddCore (⟨MulAut.conj p, hH' ⟨p, rfl⟩⟩ : H') = ⊥ := by
    rintro p rfl
    exact involutionOddCore_conj_proj_eq_bot hodd hy H' hH'
  exact key _ hey

end CFSG.ComponentClassification.Sol76.Sig
