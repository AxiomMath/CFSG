module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4BurgDUb
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4BurgDUa

public section

namespace CFSG.ComponentClassification.CatFactsL4U4.BurgD

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification CFSG.ComponentClassification.Burgoyne
open CFSG.ComponentClassification.Burgoyne.B CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.U
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.UnbalancingLocal
open scoped MatrixGroups

variable {p f : ℕ} {F : Type} [Field F]

theorem uDescend_mul [Finite F] [Fact p.Prime] (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    (a b : MulAut (StatedSU 4 (p ^ f) F)) :
    uDescend hF hp2 (a * b) = uDescend hF hp2 a * uDescend hF hp2 b := by
  ext x
  obtain ⟨g, rfl⟩ := projH_surjective x
  change uDescend hF hp2 (a * b) (projH _ g) = uDescend hF hp2 a (uDescend hF hp2 b (projH _ g))
  rw [uDescend_proj, uDescend_proj, uDescend_proj]
  rfl

theorem coe_uLift_one (h : UnitaryFieldData p f F) (A : uU h 4) (g : StatedSU 4 (p ^ f) F) :
    (((uLift h A 1 g : StatedSU 4 (p ^ f) F) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
        ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
        (((A : GL (Fin 4) F)⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
  rw [coe_uLift]
  rfl

theorem exists_in_out {J₀ : Finset (Fin 4)} (hJ : Odd J₀.card) :
    ∃ a b : Fin 4, a ∈ J₀ ∧ b ∉ J₀ := by
  have hle : J₀.card ≤ 4 := by simpa using J₀.card_le_univ
  obtain ⟨a, ha⟩ := Finset.card_pos.1 (show 0 < J₀.card by obtain ⟨m, hm⟩ := hJ; omega)
  have hc : J₀ᶜ.Nonempty := by
    rw [← Finset.card_pos, Finset.card_compl, Fintype.card_fin]
    obtain ⟨m, hm⟩ := hJ
    omega
  obtain ⟨b, hb⟩ := hc
  exact ⟨a, b, ha, Finset.mem_compl.1 hb⟩

theorem orderOf_negOneSU (h : UnitaryFieldData p f F) (h2 : (2 : F) ≠ 0) :
    orderOf (negOneSU h) = 2 := by
  refine orderOf_eq_prime ?_ ?_
  · apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, coe_negOneSU, neg_one_sq]
    rfl
  · intro h1
    have := congrArg (fun x : StatedSU 4 (p ^ f) F =>
      ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 0 0) h1
    simp only [coe_negOneSU, Matrix.neg_apply, one_apply_eq] at this
    change -1 = (1 : Matrix (Fin 4) (Fin 4) F) 0 0 at this
    rw [one_apply_eq] at this
    exact h2 (by linear_combination -this)

theorem burgoynePropBSU4ExcInput : BurgoynePropBSU4ExcInput := by
  intro J _ _ K _ t Y c hH p f F _ h hp2 θ A hA H J₀ l hl0 hodd hHA
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.charP
  have h2 : (2 : F) ≠ 0 := utwo_ne_zero h hp2
  have hF : Nat.card F = (p ^ f) ^ 2 := h.card_eq_sq
  obtain ⟨hq, hM4, ht, -, hY2, s, hs2, hst, hsY, Q, hQs, hQc, hQiso, -, hcQ, -, hprop⟩ := id hH
  obtain ⟨hsimple, hnab, -, -, -⟩ := hM4
  obtain ⟨p₁, n₁, _, hp₁, -, ⟨e₁⟩⟩ := hQiso
  have h2F₁ : (2 : GaloisField p₁ n₁) ≠ 0 :=
    Ring.two_ne_zero (by rw [ringChar.eq (GaloisField p₁ n₁) p₁]; exact hp₁)
  have hinj := PSL.conj_injective_of_mulEquiv hsimple hnab θ
  obtain ⟨e, ψ', hψ', hInn', hψ't, hec, hT⟩ := exists_su4_transport h hH hp2 θ hA hl0 hHA
  have hcQ' : e (negOneSU h) ∈ Q := hec ▸ hcQ
  set tr := MulAut.congr e.symm with htr
  have htr_apply : ∀ (γ : MulAut (K ⧸ pPrimeCore 2 K)) (g : StatedSU 4 (p ^ f) F),
      e (tr γ g) = γ (e g) := fun γ g => e.apply_symm_apply _
  have hdesc : ∀ j : J, uDescend hF hp2 (tr (phiO K j)) = ψ' ((rhoZ K).rangeRestrict j) := by
    intro j
    ext x
    obtain ⟨g, rfl⟩ := projH_surjective x
    rw [uDescend_proj]
    exact hT j g
  set ι₀ : StatedSU 4 (p ^ f) F →* Matrix (Fin 4) (Fin 4) F :=
    (Units.coeHom (Matrix (Fin 4) (Fin 4) F)).comp (StatedSU 4 (p ^ f) F).subtype with hι₀
  have hι₀g : ∀ g : StatedSU 4 (p ^ f) F,
      ι₀ g = ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := fun g => rfl
  have hSinv : (((uSign h J₀ : uU h 4) : GL (Fin 4) F)⁻¹ : GL (Fin 4) F) =
      PSL.signGL F J₀ := signGL_inv J₀
  have ht' : ∀ g, tr (phiO K t) g = uLift h (uSign h J₀) 1 g :=
    eq_uLift h hp2 (tr (phiO K t)) (by rw [hdesc, hψ't, map_one, mul_one])
  have hγ : ∀ g, ι₀ (e.symm (phiO K t (e g))) =
      PSL.signMat F J₀ * ι₀ g * PSL.signMat F J₀ := fun g => by
    change ι₀ (tr (phiO K t) g) = _
    rw [ht', hι₀g, coe_uLift_one, hSinv, PSL.coe_signGL, hι₀g, coe_uSign]
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
  have hφ1 : ∀ y : J, (rhoZ K).rangeRestrict y = 1 → phiO K y = 1 := fun y h' =>
    phiO_eq_one_of_rhoZ_eq_one K hq (congrArg Subtype.val h')
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
  have hsQ : ∀ a ∈ Q, tr s (e.symm a) = e.symm a := fun a ha => by
    apply e.injective
    rw [htr_apply, e.apply_symm_apply]
    exact hQs ha
  have hs'2 : tr s ^ 2 = 1 := by
    have h1 := pow_orderOf_eq_one s
    rw [hs2] at h1
    rw [← map_pow, h1, map_one]
  have hs'1 : tr s ≠ 1 := by
    intro h1
    have : s = 1 := tr.injective (by rw [h1, map_one])
    rw [this, orderOf_one] at hs2
    exact absurd hs2 (by norm_num)
  have hcomm : ∀ j : J, s * phiO K j = phiO K j * s →
      uDescend hF hp2 (tr s) * ψ' ((rhoZ K).rangeRestrict j) =
        ψ' ((rhoZ K).rangeRestrict j) * uDescend hF hp2 (tr s) := fun j h' => by
    rw [← hdesc, ← uDescend_mul, ← uDescend_mul, ← map_mul, ← map_mul, h']
  have hq' : ¬(4 = 3 ∧ p ^ f = 2) := fun h' => by omega
  obtain ⟨Bs, φ, hBs⟩ := exists_uConjAut_mul_uFieldAut h (by norm_num) hq' (uDescend hF hp2 (tr s))
  have hs'eq : ∀ g, tr s g = uLift h Bs φ g := eq_uLift h hp2 (tr s) hBs
  have hsq : (uConjAut h (by norm_num) Bs * uFieldAut h (by norm_num) φ) ^ 2 = 1 := by
    rw [← hBs, pow_two, ← uDescend_mul, ← pow_two, hs'2]
    ext x
    obtain ⟨g, rfl⟩ := projH_surjective x
    rw [uDescend_proj]
    rfl
  rcases uFieldAut_eq_or_of_sq h (by norm_num) hq' hsq with rfl | hφ
  ·
    rw [map_one, mul_one] at hBs hsq
    have hs1 : ∀ g, ι₀ (tr s g) = ((Bs : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * ι₀ g *
        (((Bs : GL (Fin 4) F)⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := fun g => by
      rw [hs'eq, hι₀g, coe_uLift_one, hι₀g]
    have h1 : uConjAut h (by norm_num) (Bs * Bs) = 1 := by rw [map_mul, ← pow_two, hsq]
    obtain ⟨l', hl'⟩ := (uConjAut_eq_one_iff h (by norm_num) _).1 h1
    have hl : ((Bs : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (Bs : GL (Fin 4) F) =
        (l' : F) • 1 := by
      have := congrArg (fun M : GL (Fin 4) F => (M : Matrix (Fin 4) (Fin 4) F)) hl'
      simp only [Subgroup.coe_mul, Units.val_mul, GeneralLinearGroup.coe_scalar] at this
      rw [this, scalar_apply, smul_one_eq_diagonal]
    have hns : ∀ c' : F, ((Bs : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) ≠ c' • 1 := by
      intro c' hc'
      apply hs'1
      ext g : 1
      apply Subtype.ext
      apply Units.ext
      change ι₀ (tr s g) = ι₀ g
      rw [hs1]
      have hBi : ((Bs : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
          (((Bs : GL (Fin 4) F)⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      have hcB : c' • (((Bs : GL (Fin 4) F)⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := by
        rw [← hBi, hc', Matrix.smul_mul, Matrix.one_mul]
      rw [hc', Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, ← Matrix.mul_smul, hcB,
        Matrix.mul_one]
    have hBS : ((Bs : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * PSL.signMat F J₀ =
        PSL.signMat F J₀ * (Bs : GL (Fin 4) F) := by
      have h3 := hcomm t hst
      rw [hBs, hψ't] at h3
      have h4 : uConjAut h (by norm_num) (Bs * uSign h J₀ * Bs⁻¹ * (uSign h J₀)⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, h3, map_inv, map_inv, mul_inv_cancel_right, mul_inv_cancel]
      obtain ⟨c', hc'⟩ := (uConjAut_eq_one_iff h (by norm_num) _).1 h4
      have h5 : (Bs : GL (Fin 4) F) * PSL.signGL F J₀ * (Bs : GL (Fin 4) F)⁻¹ =
          GeneralLinearGroup.scalar (Fin 4) c' * PSL.signGL F J₀ := by
        have := congrArg (· * PSL.signGL F J₀) hc'
        simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
        rw [← this]
        change _ = (Bs : GL (Fin 4) F) * PSL.signGL F J₀ * (Bs : GL (Fin 4) F)⁻¹ *
          (PSL.signGL F J₀)⁻¹ * PSL.signGL F J₀
        rw [inv_mul_cancel_right]
      have h6 : ((Bs : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * PSL.signMat F J₀ *
          (((Bs : GL (Fin 4) F)⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
            (c' : F) • PSL.signMat F J₀ := by
        have := congrArg (fun M : GL (Fin 4) F => (M : Matrix (Fin 4) (Fin 4) F)) h5
        simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, PSL.coe_signGL] at this
        rw [this, scalar_apply, ← smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul]
      have hc1 := eq_one_of_conj_signMat h2 hodd (Bs : GL (Fin 4) F) h6
      rw [hc1, one_smul] at h6
      calc ((Bs : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * PSL.signMat F J₀
          = ((Bs : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * PSL.signMat F J₀ *
              ((((Bs : GL (Fin 4) F)⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
                (Bs : GL (Fin 4) F)) := by
            rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
        _ = PSL.signMat F J₀ * (Bs : GL (Fin 4) F) := by rw [← Matrix.mul_assoc, h6]
    have hQB : ∀ a ∈ Q, ι₀ (e.symm a) * (Bs : GL (Fin 4) F) =
        ((Bs : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * ι₀ (e.symm a) := by
      intro a ha
      have h4 := congrArg ι₀ (hsQ a ha)
      rw [hs1] at h4
      calc ι₀ (e.symm a) * (Bs : GL (Fin 4) F)
          = ((Bs : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * ι₀ (e.symm a) *
              (((Bs : GL (Fin 4) F)⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
                (Bs : GL (Fin 4) F) := by rw [h4]
        _ = ((Bs : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * ι₀ (e.symm a) := by
            rw [Matrix.mul_assoc _ _ ((Bs : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F),
              ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
    exact hnt (inner_trivial_gen e ι₀ h2 hodd h2F₁ e₁ hγ hγQ (Bs : GL (Fin 4) F) hBS hl hns hQB
      (show ι₀ (negOneSU h) = -1 from coe_negOneSU h) (orderOf_negOneSU h h2) hcQ')
  ·
    have hφe : φ = barEq h := RingEquiv.ext hφ
    subst hφe
    obtain ⟨y, hy, a, ha, hya⟩ := hprop.2.2
    have hφy : phiO K y ≠ 1 := by
      intro h1
      apply hya
      rw [h1, MulAut.one_apply, mul_inv_cancel]
      exact one_mem _
    obtain ⟨i₁, i₂, hi₁, hi₂⟩ := exists_in_out hodd
    obtain ⟨α', β', hα', hβ', hD⟩ := split_oddCoreIn h hp2 (by norm_num) hinj hInn' hi₁ hi₂
      (hψ't ▸ hmemcore y hy)
    have hρ1 : ψ' ((rhoZ K).rangeRestrict y) ^ 2 = 1 → False := by
      intro hsq'
      rw [← map_pow] at hsq'
      have hsq'' : (rhoZ K).rangeRestrict y ^ 2 = 1 := hψ' (by rw [hsq', map_one])
      have hdvd := orderOf_dvd_of_pow_eq_one hsq''
      have h1 : orderOf ((rhoZ K).rangeRestrict y) = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h' | h'
        · exact h'
        · exact absurd (h' ▸ hρodd y hy) (by decide)
      exact hφy (hφ1 _ (orderOf_eq_one_iff.1 h1))
    apply hρ1
    by_cases hαβ : (α' : F) = β'
    · have hsc : ((uDiagJ h J₀ α' β' hα' hβ' : uU h 4) : GL (Fin 4) F) =
          GeneralLinearGroup.scalar (Fin 4) α' := by
        apply Units.ext
        rw [coe_uDiagJ, GeneralLinearGroup.coe_scalar, scalar_apply, ← hαβ]
        congr 1
        funext i
        split_ifs <;> rfl
      rw [hD, (uConjAut_eq_one_iff h (by norm_num) _).2 ⟨α', hsc⟩, one_pow]
    · have h3 := hcomm y (hsY y hy)
      rw [hBs, hD] at h3
      have hsq' := sq_eq_sq_of_commute_graph h h2 hodd Bs α' β' hα' hβ' hαβ h3.symm
      have hsc : ((uDiagJ h J₀ α' β' hα' hβ' ^ 2 : uU h 4) : GL (Fin 4) F) =
          GeneralLinearGroup.scalar (Fin 4) (α' ^ 2) := by
        apply Units.ext
        rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, coe_uDiagJ,
          GeneralLinearGroup.coe_scalar, scalar_apply, pow_two, diagonal_mul_diagonal,
          Units.val_pow_eq_pow_val, pow_two]
        congr 1
        funext i
        split_ifs
        · rfl
        · exact hsq'.symm
      rw [hD, ← map_pow, (uConjAut_eq_one_iff h (by norm_num) _).2 ⟨_, hsc⟩]

end CFSG.ComponentClassification.CatFactsL4U4.BurgD
