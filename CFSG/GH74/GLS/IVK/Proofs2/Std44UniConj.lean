module

public import CFSG.GH74.GLS.IVK.Proofs2.Std44
public import CFSG.RankThree.Classical.SteinbergBJUnitaryThreeInvolutions

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Matrix CFSG.Assembly.LowTwoRank CFSG.RankThree.CentralCover CFSG.RankThree.Classical
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

namespace Std44UniConj

abbrev D3 (F : Type) [Field F] : Matrix (Fin 3) (Fin 3) F := !![-1, 0, 0; 0, -1, 0; 0, 0, 1]

abbrev D2 (F : Type) [Field F] : Matrix (Fin 3) (Fin 3) F := !![-1, 0, 0; 0, 1, 0; 0, 0, -1]

section Matrices

variable {F : Type} [Field F]

theorem exists_unitary_conj_to_diag (bar : F →+* F) (hbb : ∀ x, bar (bar x) = x) (h2 : (2 : F) ≠ 0)
    {c M : Matrix (Fin 3) (Fin 3) F} (hc : (c.map bar)ᵀ * c = 1)
    (hM : M = c * D3 F * (c.map bar)ᵀ) (hcomm : M * D3 F = D3 F * M) (hne : M ≠ D3 F) :
    ∃ u : Matrix (Fin 3) (Fin 3) F, (u.map bar)ᵀ * u = 1 ∧ u.det = 1 ∧ M * u = u * D2 F ∧
      D3 F * u = u * D3 F := by
  have hcc : c * (c.map bar)ᵀ = 1 := mul_eq_one_comm.mp hc
  have hMij : ∀ i j, M i j = 2 * c i 2 * bar (c j 2) - (1 : Matrix (Fin 3) (Fin 3) F) i j := by
    intro i j
    have h := congrFun (congrFun hcc i) j
    rw [hM]
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply,
      Matrix.map_apply] at h ⊢
    fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> linear_combination (-1 : F) * h
  have hn : bar (c 0 2) * c 0 2 + bar (c 1 2) * c 1 2 + bar (c 2 2) * c 2 2 = 1 := by
    have h := congrFun (congrFun hc 2) 2
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using h
  have h4 : (4 : F) ≠ 0 := by
    have : (4 : F) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2
  have h02 : c 0 2 * bar (c 2 2) = 0 := by
    have h := congrFun (congrFun hcomm 0) 2
    simp [Matrix.mul_apply, Fin.sum_univ_three, hMij] at h
    have : (4 : F) * (c 0 2 * bar (c 2 2)) = 0 := by linear_combination h
    exact (mul_eq_zero.mp this).resolve_left h4
  have h12 : c 1 2 * bar (c 2 2) = 0 := by
    have h := congrFun (congrFun hcomm 1) 2
    simp [Matrix.mul_apply, Fin.sum_univ_three, hMij] at h
    have : (4 : F) * (c 1 2 * bar (c 2 2)) = 0 := by linear_combination h
    exact (mul_eq_zero.mp this).resolve_left h4
  by_cases hf2 : c 2 2 = 0
  · have hn' : bar (c 0 2) * c 0 2 + bar (c 1 2) * c 1 2 = 1 := by
      rw [hf2] at hn
      simpa using hn
    have hMlit : M = !![2 * c 0 2 * bar (c 0 2) - 1, 2 * c 0 2 * bar (c 1 2), 0;
        2 * c 1 2 * bar (c 0 2), 2 * c 1 2 * bar (c 1 2) - 1, 0; 0, 0, -1] := by
      ext i j
      rw [hMij]
      fin_cases i <;> fin_cases j <;> simp [hf2]
    refine ⟨!![bar (c 1 2), c 0 2, 0; -bar (c 0 2), c 1 2, 0; 0, 0, 1], ?_, ?_, ?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three, hbb] <;>
        first | ring1 | linear_combination hn'
    · simp [Matrix.det_fin_three]
      linear_combination hn'
    · rw [hMlit]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;>
        first | ring1 | linear_combination 2 * c 0 2 * hn' | linear_combination 2 * c 1 2 * hn'
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  · exfalso
    have hb2 : bar (c 2 2) ≠ 0 := (map_ne_zero bar).mpr hf2
    have hf0 : c 0 2 = 0 := (mul_eq_zero.mp h02).resolve_right hb2
    have hf1 : c 1 2 = 0 := (mul_eq_zero.mp h12).resolve_right hb2
    apply hne
    rw [hf0, hf1] at hn
    simp at hn
    ext i j
    rw [hMij]
    fin_cases i <;> fin_cases j <;> simp [hf0, hf1]
    linear_combination 2 * hn

end Matrices

section Bridge

variable {p f : ℕ} {F : Type} [Field F]

theorem coe_inv_unitary (h : UnitaryFieldData p f F) (c : unitarySU p f F 3) :
    (((c⁻¹ : unitarySU p f F 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((((c : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)).map h.bar)ᵀ := by
  have hB := ((mem_unitarySU_iff h).mp c.2).2
  rw [Subgroup.coe_inv, Matrix.coe_units_inv]
  exact Matrix.inv_eq_left_inv hB

theorem negNegOneDiag_eq : negNegOneDiag F = D3 F := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [negNegOneDiag]

theorem coe_unitaryInvT_eq (h : UnitaryFieldData p f F) :
    ((unitaryInvT h : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = D3 F := by
  rw [coe_unitaryInvT, negNegOneDiag_eq]

end Bridge

section Main

variable {p f : ℕ} {F : Type} [Field F]

theorem uniConj_aux (h : UnitaryFieldData p f F) (hp2 : p ≠ 2) (hq : Odd (p ^ f)) :
    UniConj F hq := by
  classical
  have hfin : Finite F := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP F p := h.charP
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq F p]; exact hp2)
  intro v v' hv hv' hne hcomm
  set ρ : ↥(StatedSU 3 (p ^ f) F) →* StatedProj (StatedSU 3 (p ^ f) F) :=
    statedProjMk (StatedSU 3 (p ^ f) F) with hρ
  have hsurj : Function.Surjective ρ := statedProjMk_surjective _
  have hC : ρ.ker ≤ Subgroup.center ↥(StatedSU 3 (p ^ f) F) := ker_statedProjMk_le_center _
  have hker : Nat.card ρ.ker = Nat.gcd 3 (p ^ f + 1) := by
    have := (CFSG.LinearGroups.unitary_scalar_kernel h.prime h.card_eq_sq (n := 3)
      (by norm_num)).2.2
    rw [← this, hρ, statedProjMk, QuotientGroup.ker_mk']
  have hodd : Odd (Nat.card ρ.ker) := by
    rw [hker]
    exact Odd.of_dvd_nat (by decide) (Nat.gcd_dvd_left 3 _)
  have hv2 : v ^ 2 = 1 := by rw [← hv]; exact pow_orderOf_eq_one v
  have hv'2 : v' ^ 2 = 1 := by rw [← hv']; exact pow_orderOf_eq_one v'
  have hv1 : v ≠ 1 := fun e => by rw [e, orderOf_one] at hv; exact absurd hv (by norm_num)
  have hv1' : v' ≠ 1 := fun e => by rw [e, orderOf_one] at hv'; exact absurd hv' (by norm_num)
  obtain ⟨a, ⟨ha2, hav⟩, -⟩ :=
    CFSG.SectionRank.OddCover.existsUnique_involution_lift hsurj hC hodd hv2
  obtain ⟨a', ⟨ha'2, hav'⟩, hu'⟩ :=
    CFSG.SectionRank.OddCover.existsUnique_involution_lift hsurj hC hodd hv'2
  have ha1 : a ≠ 1 := fun e => hv1 (by rw [← hav, e, map_one])
  have ha'1 : a' ≠ 1 := fun e => hv1' (by rw [← hav', e, map_one])
  have haa' : a ≠ a' := fun e => hne (by rw [← hav, ← hav', e])
  have hcommG : a * a' = a' * a := by
    have hconj2 : (a * a' * a⁻¹) ^ 2 = 1 := by
      rw [conj_pow, ha'2, mul_one, mul_inv_cancel]
    have hρconj : ρ (a * a' * a⁻¹) = v' := by
      rw [map_mul, map_mul, map_inv, hav, hav', hcomm]
      group
    have hcomm' : a * a' * a⁻¹ = a' := hu' _ ⟨hconj2, hρconj⟩
    calc a * a' = a * a' * a⁻¹ * a := by group
      _ = a' * a := by rw [hcomm']
  obtain ⟨t, ht⟩ : ∃ t : ↥(StatedSU 3 (p ^ f) F), t = unitaryInvT h := ⟨_, rfl⟩
  have ha_ord : orderOf a = 2 := orderOf_eq_prime ha2 ha1
  obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_unitaryInvT_of_orderOf h hp2 ha_ord)
  rw [← ht] at hc
  have hta : t = c⁻¹ * a * c := by rw [← hc]; group
  obtain ⟨a'', ha''⟩ : ∃ a'' : ↥(StatedSU 3 (p ^ f) F), a'' = c⁻¹ * a' * c := ⟨_, rfl⟩
  have ha''2 : a'' ^ 2 = 1 := by
    rw [ha'', sq]
    calc c⁻¹ * a' * c * (c⁻¹ * a' * c) = c⁻¹ * (a' * a') * c := by group
      _ = 1 := by rw [← sq, ha'2]; group
  have ha''1 : a'' ≠ 1 := fun e => ha'1 (by
    have : a' = c * a'' * c⁻¹ := by rw [ha'']; group
    rw [this, e]
    group)
  have ha''_ord : orderOf a'' = 2 := orderOf_eq_prime ha''2 ha''1
  have hcommt : a'' * t = t * a'' := by
    calc a'' * t = c⁻¹ * (a' * a) * c := by rw [ha'', hta]; group
      _ = c⁻¹ * (a * a') * c := by rw [hcommG]
      _ = t * a'' := by rw [ha'', hta]; group
  have hnet : a'' ≠ t := fun e => haa' (by
    have h1 : c⁻¹ * a' * c = c⁻¹ * a * c := by rw [← ha'', e, hta]
    have h2 : c⁻¹ * a' = c⁻¹ * a := mul_right_cancel h1
    exact (mul_left_cancel h2).symm)
  obtain ⟨c'', hc''⟩ := isConj_iff.mp (isConj_unitaryInvT_of_orderOf h hp2 ha''_ord)
  rw [← ht] at hc''
  have hc''mat : ((((c'' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)).map h.bar)ᵀ *
      ((c'' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 :=
    ((mem_unitarySU_iff h).mp c''.2).2
  have hMeq : ((a'' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((c'' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * D3 F *
        ((((c'' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)).map h.bar)ᵀ := by
    have := congrArg (fun x : ↥(StatedSU 3 (p ^ f) F) =>
      ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) hc''
    simp only [Subgroup.coe_mul, Units.val_mul, coe_inv_unitary h c'', ht] at this
    rw [← this, coe_unitaryInvT_eq]
  have hcommmat : ((a'' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * D3 F =
      D3 F * ((a'' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    have := congrArg (fun x : ↥(StatedSU 3 (p ^ f) F) =>
      ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) hcommt
    simpa [Subgroup.coe_mul, Units.val_mul, ht, coe_unitaryInvT_eq] using this
  have hnemat : ((a'' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ≠ D3 F := by
    intro e
    apply hnet
    apply Subtype.ext
    apply Units.ext
    rw [e]
    simp [ht, coe_unitaryInvT_eq]
  obtain ⟨u, hu1, hudet, hMu, hD3u⟩ :=
    exists_unitary_conj_to_diag h.bar h.bar_bar h2 hc''mat hMeq hcommmat hnemat
  have hdetne : u.det ≠ 0 := by rw [hudet]; exact one_ne_zero
  have hUmem : GeneralLinearGroup.mkOfDetNeZero u hdetne ∈ unitarySU p f F 3 :=
    (mem_unitarySU_iff h).mpr ⟨hudet, hu1⟩
  obtain ⟨U, hU⟩ : ∃ U : ↥(StatedSU 3 (p ^ f) F),
      U = ⟨GeneralLinearGroup.mkOfDetNeZero u hdetne, hUmem⟩ := ⟨_, rfl⟩
  have hUmat : ((U : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = u := by rw [hU]; rfl
  obtain ⟨t₂, ht₂⟩ : ∃ t₂ : ↥(StatedSU 3 (p ^ f) F), t₂ = ⟨oddDiag₂ F, Subgroup.subset_closure
      ⟨det_oddDiag₂ F, unitary_oddDiag₂ hq⟩⟩ := ⟨_, rfl⟩
  have ht₂mat : ((t₂ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = D2 F := by rw [ht₂]; rfl
  have htmat : ((t : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = D3 F := by
    rw [ht, coe_unitaryInvT_eq]
  have hrel1 : a'' * U = U * t₂ := by
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, hUmat, ht₂mat]
    exact hMu
  have hrel2 : t * U = U * t := by
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, hUmat, htmat]
    exact hD3u
  have hUt : U * t * U⁻¹ = t := by rw [← hrel2]; group
  have hUt₂ : U * t₂ * U⁻¹ = a'' := by rw [← hrel1]; group
  have hw1 : (c * U) * t * (c * U)⁻¹ = a := by
    calc (c * U) * t * (c * U)⁻¹ = c * (U * t * U⁻¹) * c⁻¹ := by group
      _ = a := by rw [hUt, hc]
  have hw2 : (c * U) * t₂ * (c * U)⁻¹ = a' := by
    calc (c * U) * t₂ * (c * U)⁻¹ = c * (U * t₂ * U⁻¹) * c⁻¹ := by group
      _ = a' := by rw [hUt₂, ha'']; group
  have ht3 : t = ⟨oddDiag₃ F, Subgroup.subset_closure
      ⟨det_oddDiag₃ F, unitary_oddDiag₃ hq⟩⟩ := by
    apply Subtype.ext
    apply Units.ext
    rw [htmat]
    rfl
  have hρconj : ∀ x y : ↥(StatedSU 3 (p ^ f) F), ρ (x * y * x⁻¹) = ρ x * ρ y * (ρ x)⁻¹ :=
    fun x y => by simp
  refine ⟨ρ (c * U)⁻¹, ?_, ?_⟩
  · have e1 : (c * U)⁻¹ * a * ((c * U)⁻¹)⁻¹ = t := by rw [← hw1]; group
    calc ρ (c * U)⁻¹ * v * (ρ (c * U)⁻¹)⁻¹ = ρ ((c * U)⁻¹ * a * ((c * U)⁻¹)⁻¹) := by
          rw [hρconj, hav]
      _ = ρ t := by rw [e1]
      _ = uniU₀ F hq := by rw [ht3]; rfl
  · have e1 : (c * U)⁻¹ * a' * ((c * U)⁻¹)⁻¹ = t₂ := by rw [← hw2]; group
    calc ρ (c * U)⁻¹ * v' * (ρ (c * U)⁻¹)⁻¹ = ρ ((c * U)⁻¹ * a' * ((c * U)⁻¹)⁻¹) := by
          rw [hρconj, hav']
      _ = ρ t₂ := by rw [e1]
      _ = uniU₀' F hq := by rw [ht₂]; rfl

theorem exists_unitaryFieldData [Finite F] {q : ℕ} (hq : Odd q) (hF : Nat.card F = q ^ 2) :
    ∃ p f : ℕ, UnitaryFieldData p f F ∧ q = p ^ f ∧ p ≠ 2 := by
  obtain ⟨p, hp⟩ := CharP.exists F
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hpp, hcard⟩ := FiniteField.card (K := F) p
  have hqd : q ∣ p ^ (n : ℕ) := by
    rw [← hcard, ← Nat.card_eq_fintype_card, hF]
    exact Dvd.intro q (sq q).symm
  obtain ⟨f, -, hf⟩ := (Nat.dvd_prime_pow hpp).1 hqd
  have hf0 : f ≠ 0 := by
    rintro rfl
    have h1 : Nat.card F = 1 := by rw [hF, hf]; norm_num
    have := Finite.one_lt_card (α := F)
    omega
  have hpodd : Odd p := by
    rw [hf] at hq
    exact (Nat.odd_pow_iff hf0).mp hq
  refine ⟨p, f, ⟨hpp, Nat.one_le_iff_ne_zero.mpr hf0, ?_⟩, hf, ?_⟩
  · rw [hF, hf, ← pow_mul, mul_comm]
  · rintro rfl
    exact absurd hpodd (by decide)

end Main

end Std44UniConj

theorem uniConj (F : Type) [Field F] [Finite F] {q : ℕ} (hq : Odd q) (hF : Nat.card F = q ^ 2) :
    UniConj F hq := by
  obtain ⟨p, f, h, rfl, hp2⟩ := Std44UniConj.exists_unitaryFieldData hq hF
  exact Std44UniConj.uniConj_aux h hp2 hq

end CFSG.GH74.GLS.IVK.Proofs2
