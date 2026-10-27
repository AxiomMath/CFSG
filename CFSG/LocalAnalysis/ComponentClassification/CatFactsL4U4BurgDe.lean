module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4BurgDd
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4BurgDc
public import CFSG.RankThree.PartOne.AUTSL.Interface

public section

namespace CFSG.ComponentClassification.CatFactsL4U4.BurgD

open Matrix CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification CFSG.ComponentClassification.Burgoyne
open CFSG.ComponentClassification.Burgoyne.PSL CFSG.ComponentClassification.Burgoyne.B
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.UnbalancingLocal
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem descendAut_std (B : GL (Fin 4) F) (τ : F ≃+* F) (ε : ℕ) :
    descendAut 4 F (CatalogueBHigherLinearAction.slConjugation 4 F B *
      CatalogueBHigherLinearField.slFieldAut (Fin 4) F τ * CatalogueBGraphForm.slGraphAut 4 F ^ ε) =
      conjAut 4 F B * fieldAut 4 F τ * dualAut 4 F ^ ε := by
  rw [map_mul, map_mul, map_pow]
  rfl

theorem exists_mem_not_mem {J₀ : Finset (Fin 4)} (hJ : Odd J₀.card) :
    ∃ a b : Fin 4, a ∈ J₀ ∧ b ∉ J₀ := by
  have hle : J₀.card ≤ 4 := by simpa using J₀.card_le_univ
  obtain ⟨a, ha⟩ := Finset.card_pos.1 (show 0 < J₀.card by obtain ⟨m, hm⟩ := hJ; omega)
  have hc : J₀ᶜ.Nonempty := by
    rw [← Finset.card_pos, Finset.card_compl, Fintype.card_fin]
    obtain ⟨m, hm⟩ := hJ
    omega
  obtain ⟨b, hb⟩ := hc
  exact ⟨a, b, ha, Finset.mem_compl.1 hb⟩

theorem burgoynePropBSL4ExcInput : BurgoynePropBSL4ExcInput := by
  intro J _ _ K _ t Y c hH F _ _ hF θ A hA H J₀ μ hodd hHA
  obtain ⟨hq, hM4, ht, -, hY2, s, hs2, hst, hsY, Q, hQs, hQc, hQiso, -, hcQ, -, hprop⟩ := id hH
  obtain ⟨hsimple, hnab, -, -, -⟩ := hM4
  obtain ⟨p₁, n₁, _, hp₁, -, ⟨e₁⟩⟩ := hQiso
  have h2F₁ : (2 : GaloisField p₁ n₁) ≠ 0 :=
    Ring.two_ne_zero (by rw [ringChar.eq (GaloisField p₁ n₁) p₁]; exact hp₁)
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hinj := conj_injective_of_mulEquiv hsimple hnab θ
  obtain ⟨e, ψ', hψ', hInn', hψ't, hec, hdesc⟩ := exists_sl4_transport hH hF θ hA hHA
  have hcQ' : e negOneSL ∈ Q := hec ▸ hcQ
  set tr := MulAut.congr e.symm with htr
  have htr_apply : ∀ (γ : MulAut (K ⧸ pPrimeCore 2 K)) (g : SL(4, F)),
      e (tr γ g) = γ (e g) := fun γ g => e.apply_symm_apply _
  have ht' : tr (phiO K t) = CatalogueBHigherLinearAction.slConjugation 4 F (signGL F J₀) :=
    RankThree.PartOne.AUTSL.descendAut_injective (by norm_num) (by rw [hdesc, hψ't]; rfl)
  have hγ : ∀ g, phiO K t (e g) =
      e (CatalogueBHigherLinearAction.slConjugation 4 F (signGL F J₀) g) := fun g => by
    rw [← htr_apply, ht']
  have htmem : t ∈ closure (insert t (Y : Set J)) := subset_closure (Set.mem_insert t _)
  have hγQ : ∀ a ∈ Q, phiO K t a ∈ Q := fun a ha => by
    have := (hprop.1 t htmem).1
    rw [← this]
    exact mem_map_of_mem _ ha
  have hmemcore : ∀ y ∈ Y, ψ' ((rhoZ K).rangeRestrict y) ∈
      oddCoreIn ψ'.range (ψ' ((rhoZ K).rangeRestrict t)) := by
    intro y hy
    rw [← map_oddCentralizerCore_of_injective hψ']
    exact mem_map_of_mem _ (hY2 (mem_map_of_mem _ hy))
  have hρodd : ∀ y ∈ Y, Odd (orderOf ((rhoZ K).rangeRestrict y)) := fun y hy => by
    rw [← orderOf_injective ψ' hψ']
    exact odd_orderOf_of_mem_oddCoreIn (hmemcore y hy)
  have hφ1 : ∀ y : J, (rhoZ K).rangeRestrict y = 1 → phiO K y = 1 := fun y h =>
    phiO_eq_one_of_rhoZ_eq_one K hq (congrArg Subtype.val h)
  have hφodd : ∀ y ∈ Y, Odd (orderOf (phiO K y)) := by
    intro y hy
    have h1 := pow_orderOf_eq_one ((rhoZ K).rangeRestrict y)
    rw [← map_pow] at h1
    have h2' := hφ1 _ h1
    rw [map_pow] at h2'
    exact Odd.of_dvd_nat (hρodd y hy) (orderOf_dvd_of_pow_eq_one h2')
  have hnt : ¬ ∀ a ∈ Q, phiO K t a * a⁻¹ ∈ (pPrimeCore 2 Q).map Q.subtype := by
    intro hall
    obtain ⟨y, hy, hty⟩ := hprop.2.1 t htmem hall
    have h1 := hφodd y hy
    change Odd (orderOf (phiO K y)) at h1
    rw [← hty, ht] at h1
    exact (by decide : ¬ Odd 2) h1
  have hsE : ∀ g, s (e g) = e (tr s g) := fun g => (htr_apply s g).symm
  have hsQ : ∀ a ∈ Q, tr s (e.symm a) = e.symm a := fun a ha => by
    apply e.injective
    rw [htr_apply, e.apply_symm_apply]
    exact hQs ha
  have hs'2 : tr s ^ 2 = 1 := by
    have h := pow_orderOf_eq_one s
    rw [hs2] at h
    rw [← map_pow, h, map_one]
  have hs'1 : tr s ≠ 1 := by
    intro h
    have : s = 1 := tr.injective (by rw [h, map_one])
    rw [this, orderOf_one] at hs2
    exact absurd hs2 (by norm_num)
  have hcomm : ∀ g : J, s * phiO K g = phiO K g * s →
      descendAut 4 F (tr s) * ψ' ((rhoZ K).rangeRestrict g) =
        ψ' ((rhoZ K).rangeRestrict g) * descendAut 4 F (tr s) := fun g h => by
    rw [← hdesc, ← map_mul, ← map_mul, ← map_mul, ← map_mul, h]
  obtain ⟨Bs, τ, ε, hε, hs'⟩ :=
    RankThree.PartOne.AUTSL.exists_eq_std_of_mulAut_sl (by norm_num : 3 ≤ 4) (tr s)
  have hds : descendAut 4 F (tr s) = conjAut 4 F Bs * fieldAut 4 F τ * dualAut 4 F ^ ε := by
    rw [hs', descendAut_std]
  have hdsq : (conjAut 4 F Bs * fieldAut 4 F τ * dualAut 4 F ^ ε) ^ 2 = 1 := by
    rw [← hds, ← map_pow, hs'2, map_one]
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨p, hpF, n, hp, hcardF⟩ := FiniteField.card' F
  have hp2 : p ≠ 2 := by rw [← ringChar.eq F p]; exact hF
  have : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card F = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcardF]
  have hn1 : 1 ≤ (n : ℕ) := n.pos
  interval_cases ε
  · rw [pow_zero, mul_one] at hds hdsq
    by_cases hτ : τ = 1
    ·
      subst hτ
      rw [map_one, mul_one] at hds hdsq
      have hs'' : tr s = CatalogueBHigherLinearAction.slConjugation 4 F Bs := by
        rw [hs', map_one, pow_zero, mul_one, mul_one]
      have h1 : conjAut 4 F (Bs * Bs) * fieldAut 4 F 1 = 1 := by
        rw [map_one, mul_one, map_mul, ← pow_two, hdsq]
      obtain ⟨-, l, hl⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (by norm_num) _ 1 h1
      have hl' : (Bs : Matrix (Fin 4) (Fin 4) F) * Bs = (l : F) • 1 := by
        have := congrArg (fun M : GL (Fin 4) F => (M : Matrix (Fin 4) (Fin 4) F)) hl
        simp only [Units.val_mul, GeneralLinearGroup.coe_scalar] at this
        rw [← this, scalar_apply, smul_one_eq_diagonal]
      have hns : ∀ c : F, (Bs : Matrix (Fin 4) (Fin 4) F) ≠ c • 1 := by
        intro c hc
        have hc0 : c ≠ 0 := by
          rintro rfl
          rw [zero_smul] at hc
          have := (Matrix.isUnit_iff_isUnit_det _).1 Bs.isUnit
          rw [hc, Matrix.det_zero] at this
          exact not_isUnit_zero this
        apply hs'1
        rw [hs'']
        have : Bs = GeneralLinearGroup.scalar (Fin 4) (Units.mk0 c hc0) := by
          apply Units.ext
          rw [hc, GeneralLinearGroup.coe_scalar, Units.val_mk0, scalar_apply,
            smul_one_eq_diagonal]
        rw [this, CatalogueBHigherLinearAction.slConjugation_scalar]
      have hBS : (Bs : Matrix (Fin 4) (Fin 4) F) * signMat F J₀ = signMat F J₀ * Bs := by
        have h3 := hcomm t hst
        rw [hds, hψ't] at h3
        refine commute_of_conjAut_conj h2 hodd Bs ?_
        rw [map_mul, map_mul, h3, map_inv, mul_inv_cancel_right]
      have hQB : ∀ a ∈ Q, ((e.symm a : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * Bs =
          Bs * ((e.symm a : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) := by
        intro a ha
        have h4 := congrArg (fun x : SL(4, F) => (x : Matrix (Fin 4) (Fin 4) F)) (hsQ a ha)
        simp only [hs'', coe_slConj] at h4
        calc ((e.symm a : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * Bs
            = (Bs : Matrix (Fin 4) (Fin 4) F) * (e.symm a : SL(4, F)) *
                ((Bs⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * Bs := by rw [h4]
          _ = Bs * ((e.symm a : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) := by
              rw [Matrix.mul_assoc _ _ (Bs : Matrix (Fin 4) (Fin 4) F), ← Units.val_mul,
                inv_mul_cancel, Units.val_one, Matrix.mul_one]
      exact hnt (inner_trivial e h2 hodd h2F₁ e₁ hγ hγQ Bs hBS hl' hns hQB coe_negOneSL hcQ')
    ·
      obtain ⟨H', hH'⟩ := LocalAnalysis.ComponentInitial.OddHigherLinear.field_involution_conjugacy
        hp hp2 hn1 hcard (by norm_num) Bs τ hτ hdsq
      have hs'' : tr s = CatalogueBHigherLinearAction.slConjugation 4 F H' *
          CatalogueBHigherLinearField.slFieldAut (Fin 4) F τ *
            (CatalogueBHigherLinearAction.slConjugation 4 F H')⁻¹ :=
        RankThree.PartOne.AUTSL.descendAut_injective (by norm_num)
          (by rw [hds, hH', map_mul, map_mul, map_inv]; rfl)
      exact false_of_field e h2 τ (fun g => by rw [hsE, hs'']) hQs hQc h2F₁ e₁ coe_negOneSL hcQ'
  · rw [pow_one] at hds hdsq
    by_cases hτ : τ = 1
    ·
      subst hτ
      rw [map_one, mul_one] at hds
      obtain ⟨y, hy, a, ha, hya⟩ := hprop.2.2
      have hφy : phiO K y ≠ 1 := by
        intro h1
        apply hya
        rw [h1, MulAut.one_apply, mul_inv_cancel]
        exact one_mem _
      obtain ⟨i₁, i₂, hi₁, hi₂⟩ := exists_mem_not_mem hodd
      obtain ⟨α', β', hD⟩ := split_oddCoreIn hF (by norm_num) hinj hInn' hi₁ hi₂
        (hψ't ▸ hmemcore y hy)
      have hρ1 : ψ' ((rhoZ K).rangeRestrict y) ^ 2 = 1 → False := by
        intro hsq
        rw [← map_pow] at hsq
        have hsq' : (rhoZ K).rangeRestrict y ^ 2 = 1 := hψ' (by rw [hsq, map_one])
        have hdvd := orderOf_dvd_of_pow_eq_one hsq'
        have h1 : orderOf ((rhoZ K).rangeRestrict y) = 1 := by
          rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
          · exact h
          · exact absurd (h ▸ hρodd y hy) (by decide)
        exact hφy (hφ1 _ (orderOf_eq_one_iff.1 h1))
      apply hρ1
      by_cases hαβ : (α' : F) = β'
      · have hsc : blockScalarGL J₀ α' β' = GeneralLinearGroup.scalar (Fin 4) α' := by
          apply Units.ext
          rw [coe_blockScalarGL, GeneralLinearGroup.coe_scalar, scalar_apply, ← hαβ]
          congr 1
          funext i
          split_ifs <;> rfl
        rw [hD, hsc, conjAut_scalar, one_pow]
      · have h3 := hcomm y (hsY y hy)
        rw [hds, hD] at h3
        have hsq := sq_eq_sq_of_commute_dual h2 hodd Bs α' β' hαβ h3
        have hsc : blockScalarGL J₀ α' β' ^ 2 = GeneralLinearGroup.scalar (Fin 4) (α' ^ 2) := by
          apply Units.ext
          rw [Units.val_pow_eq_pow_val, coe_blockScalarGL, GeneralLinearGroup.coe_scalar,
            scalar_apply, pow_two, diagonal_mul_diagonal, Units.val_pow_eq_pow_val, pow_two]
          congr 1
          funext i
          split_ifs
          · rfl
          · exact hsq.symm
        rw [hD, ← map_pow, hsc, conjAut_scalar]
    ·
      obtain ⟨hfe, hτpow, H', hH'⟩ :=
        LocalAnalysis.ComponentInitial.LinearFlag.odd_linear_graph_field_involution_conjugacy
          hp hn1 hcard (by norm_num) Bs τ hτ hdsq
      have hpF' : CharP F p := hpF
      have hτu : τ = LieType.BorelTits.unitaryInvolution F p ((n : ℕ) / 2) := by
        ext x
        rw [hτpow, LieType.BorelTits.unitaryInvolution_apply]
      have hKf : Nat.card F = (p ^ ((n : ℕ) / 2)) ^ 2 := by
        rw [hcard, ← pow_mul]
        congr 1
        obtain ⟨k, hk⟩ := hfe
        omega
      have hs'' : tr s = CatalogueBHigherLinearAction.slConjugation 4 F H' *
          (CatalogueBHigherLinearField.slFieldAut (Fin 4) F τ *
            CatalogueBGraphForm.slGraphAut 4 F) *
            (CatalogueBHigherLinearAction.slConjugation 4 F H')⁻¹ :=
        RankThree.PartOne.AUTSL.descendAut_injective (by norm_num) (by
          rw [hds, hH', map_mul, map_mul, map_mul, map_inv]
          rfl)
      rw [hτu] at hs''
      exact false_of_graphField hp2 hKf e (fun g => by rw [hsE, hs'']) hQs hQc h2F₁ e₁
        coe_negOneSL hcQ'

end CFSG.ComponentClassification.CatFactsL4U4.BurgD
