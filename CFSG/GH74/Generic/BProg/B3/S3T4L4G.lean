module

public import CFSG.GH74.Generic.BProg.B2.PuL4GraphUni
public import CFSG.GH74.Generic.BProg.B2.GenLocL4OutGraph

public section

namespace CFSG.GH74.Generic.BProg.B3

open Subgroup Matrix CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.Generic.BProg.B2.PuL4GraphLin

namespace S3T4

theorem rhoOf_eq_congr {N : Type} [Group N] {H : Subgroup N} [H.Normal]
    (hfaith : ∀ n : N, (∀ h ∈ H, n * h = h * n) → n = 1) {P : Type} [Group P] (e : ↥H ≃* P)
    (n : N) : rhoOf e n = MulAut.congr e (MulAut.conjNormal n : MulAut ↥H) := by
  have hinj : ∀ a b : P, MulAut.conj a = MulAut.conj b → a = b := by
    intro a b hab
    have hc : ∀ h ∈ H, ((e.symm (b⁻¹ * a) : ↥H) : N) * h = h * (e.symm (b⁻¹ * a) : ↥H) := by
      intro h hh
      have h1 := congrArg (fun φ : MulAut P => φ (e ⟨h, hh⟩)) hab
      simp only [MulAut.conj_apply] at h1
      have h2 : (b⁻¹ * a) * e ⟨h, hh⟩ = e ⟨h, hh⟩ * (b⁻¹ * a) := by
        calc (b⁻¹ * a) * e ⟨h, hh⟩ = b⁻¹ * (a * e ⟨h, hh⟩ * a⁻¹) * a := by group
          _ = b⁻¹ * (b * e ⟨h, hh⟩ * b⁻¹) * a := by rw [h1]
          _ = e ⟨h, hh⟩ * (b⁻¹ * a) := by group
      have h3 := congrArg (fun z => ((e.symm z : ↥H) : N)) h2
      simpa only [map_mul, MulEquiv.symm_apply_apply, Subgroup.coe_mul] using h3
    have h4 : e.symm (b⁻¹ * a) = 1 := Subtype.ext (hfaith _ hc)
    have h5 : b⁻¹ * a = 1 := by simpa using congrArg e h4
    exact (inv_mul_eq_one.1 h5).symm
  ext x
  set y : ↥H := e.symm x with hy
  have hm : n * (y : N) * n⁻¹ ∈ H := Subgroup.Normal.conj_mem inferInstance _ y.2 n
  have h1 : rhoOf e (n * (y : N) * n⁻¹) = MulAut.conj (e ⟨_, hm⟩) := rhoOf_mem e ⟨_, hm⟩
  have h2 : rhoOf e (n * (y : N) * n⁻¹) = MulAut.conj (rhoOf e n x) := by
    rw [map_mul, map_mul, map_inv, rhoOf_mem e y, hy, MulEquiv.apply_symm_apply]
    ext z
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply]
  have h3 : MulAut.congr e (MulAut.conjNormal n : MulAut ↥H) x = e ⟨_, hm⟩ := by
    rw [MulAut.congr_apply]
    exact congrArg e (Subtype.ext (MulAut.conjNormal_apply n y))
  exact hinj _ _ ((h2.symm.trans h1).trans (congrArg MulAut.conj h3.symm))

open Matrix in
theorem graph_form_of_not_diag4 {F : Type} [Field F] [Finite F] (hF : Nat.card F % 4 = 3)
    (τ : MulAut (LinearFlag.projectiveSL 4 F)) (hτ : τ ^ 2 = 1)
    (hnd : ∀ A : GL (Fin 4) F, τ ≠ LinearFlag.conjAut 4 F A) :
    ∃ A : GL (Fin 4) F, τ = LinearFlag.conjAut 4 F A * LinearFlag.dualAut 4 F ∧
      (((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ = (A : Matrix (Fin 4) (Fin 4) F) ∨
        ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ = -(A : Matrix (Fin 4) (Fin 4) F)) := by
  obtain ⟨-, hgen⟩ := LinearFlag.automorphism_generation (K := F) (n := 4) (by norm_num)
  obtain ⟨A, σ, ε, hε, hτA⟩ := hgen τ
  obtain ⟨-, -, hfc, hδδ, hδc, hδf, -⟩ :=
    LinearFlag.standard_automorphism_transport (K := F) (n := 4)
  have hsq : τ * τ = 1 := by rw [← pow_two]; exact hτ
  rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
  ·
    rw [pow_zero, mul_one] at hτA
    rw [hτA, LinearFlag.conjAut_mul_fieldAut_mul] at hsq
    obtain ⟨hσ, -⟩ :=
      LinearFlag.eq_one_of_conjAut_mul_fieldAut_eq_one (by norm_num : 3 ≤ 4) _ _ hsq
    have hσ1 : σ = 1 := B2.GenLocL4Out.eq_one_of_mul_self hF σ hσ
    exact (hnd A (by rw [hτA, hσ1, map_one, mul_one])).elim
  ·
    rw [pow_one] at hτA
    set A' := GeneralLinearGroup.inverseTranspose A with hA'
    have hδ : LinearFlag.dualAut 4 F * (LinearFlag.conjAut 4 F A * LinearFlag.fieldAut 4 F σ) *
        LinearFlag.dualAut 4 F = LinearFlag.conjAut 4 F A' * LinearFlag.fieldAut 4 F σ := by
      have := hδc A
      have h2 := hδf σ
      calc LinearFlag.dualAut 4 F * (LinearFlag.conjAut 4 F A * LinearFlag.fieldAut 4 F σ) *
          LinearFlag.dualAut 4 F
          = (LinearFlag.dualAut 4 F * LinearFlag.conjAut 4 F A * LinearFlag.dualAut 4 F) *
            (LinearFlag.dualAut 4 F * LinearFlag.fieldAut 4 F σ * LinearFlag.dualAut 4 F) := by
            calc _ = LinearFlag.dualAut 4 F * LinearFlag.conjAut 4 F A *
                  (LinearFlag.dualAut 4 F * LinearFlag.dualAut 4 F) * LinearFlag.fieldAut 4 F σ *
                  LinearFlag.dualAut 4 F := by rw [hδδ]; group
              _ = _ := by group
        _ = _ := by rw [this, h2]
    have h1 : τ * τ = LinearFlag.conjAut 4 F (A * GeneralLinearGroup.map (σ : F →+* F) A') *
        LinearFlag.fieldAut 4 F (σ * σ) := by
      rw [hτA, ← LinearFlag.conjAut_mul_fieldAut_mul, ← hδ]
      group
    rw [h1] at hsq
    obtain ⟨hσ, c, hc⟩ :=
      LinearFlag.eq_one_of_conjAut_mul_fieldAut_eq_one (by norm_num : 3 ≤ 4) _ _ hsq
    have hσ1 : σ = 1 := B2.GenLocL4Out.eq_one_of_mul_self hF σ hσ
    subst hσ1
    refine ⟨A, by rw [hτA, map_one, mul_one], ?_⟩
    have hAc : ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        (c : F) • ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ := by
      have h3 : (A * GeneralLinearGroup.map ((1 : F ≃+* F) : F →+* F) A' : GL (Fin 4) F) =
          GeneralLinearGroup.scalar (Fin 4) c := hc.symm
      have h4 : ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
          (((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ) =
            (c : F) • (1 : Matrix (Fin 4) (Fin 4) F) := by
        have := congrArg (fun u : GL (Fin 4) F => (u : Matrix (Fin 4) (Fin 4) F)) h3
        simpa [hA', GeneralLinearGroup.coe_inverseTranspose, Matrix.smul_eq_diagonal_mul,
          GeneralLinearGroup.coe_scalar] using this
      have h5 : ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ *
          ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ = 1 := by
        rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
      calc ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
          = ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
              (((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ *
                ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ) := by rw [h5, Matrix.mul_one]
        _ = ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
              (((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ) *
                ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ := by rw [Matrix.mul_assoc]
        _ = (c : F) • ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ := by
          rw [h4, Matrix.smul_mul, Matrix.one_mul]
    have hAT : ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ =
        (c : F) • ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
      have := congrArg Matrix.transpose hAc
      rwa [Matrix.transpose_smul, Matrix.transpose_transpose] at this
    have hc2 : (c : F) * c = 1 := by
      have h6 : ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
          ((c : F) * c) • ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
        calc ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
            = (c : F) • ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ := hAc
          _ = (c : F) • ((c : F) • ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) := by
            rw [hAT]
          _ = ((c : F) * c) • ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := smul_smul _ _ _
      have hA0 : ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) ≠ 0 := by
        intro h0
        have h7 := Units.mul_inv A
        rw [h0, Matrix.zero_mul] at h7
        exact zero_ne_one h7
      by_contra hne
      apply hA0
      have h8 : ((c : F) * c - 1) • ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 0 := by
        rw [sub_smul, one_smul, ← h6, sub_self]
      exact (smul_eq_zero.1 h8).resolve_left (sub_ne_zero.2 hne)
    rcases mul_self_eq_one_iff.1 hc2 with h | h
    · left; rw [hAT, h, one_smul]
    · right; rw [hAT, h, neg_smul, one_smul]

section Alt

open CFSG.GH74.Generic.BProg.B2.GenLocL4Gen4

theorem false_of_graph_alt4 {N : Type} [Group N] [Finite N] (H : Subgroup N) [H.Normal] {t : N}
    {L : Subgroup N} (hs : B2.ShapeInCent H t L) (htH : t ∉ H) {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (e : ↥H ≃* LinearFlag.projectiveSL 4 F) (A : GL (Fin 4) F)
    (hA : ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ = -(A : Matrix (Fin 4) (Fin 4) F))
    (hτ : MulAut.congr e (MulAut.conjNormal t : MulAut ↥H) =
      LinearFlag.conjAut 4 F A * LinearFlag.dualAut 4 F) (hN : SectionalTwoRankLE N 4) :
    False := by
  have hk2 : ringChar F ≠ 2 :=
    CFSG.ComponentClassification.CatalogueBOddQuadratic.char_ne_two_of_odd_card hodd
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hk2
  obtain ⟨r, hmr, σ, hker⟩ := exists_sp_cover (A := N) (a := t) (L := L) (m := 4) le_rfl hk2
    hodd (rhoOf_injective hs.faithful e) (isComponentOf_map_rho hs e) (B := A)
    ((rhoOf_eq_congr hs.faithful e t).trans hτ) hA
  have hr : r = 2 := by omega
  subst hr
  obtain ⟨φ, hφc⟩ := exists_q8q8_sp h2
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [hs.inv, pow_two] at this
  have hLC : L ≤ H ⊓ centralizer ({t} : Set N) := hs.comp.1
  let g₁ : QuaternionGroup 2 × QuaternionGroup 2 →* N := L.subtype.comp (σ.comp φ)
  let g₂ : Multiplicative (ZMod 2) →* N :=
    { toFun := fun x => if x = 1 then 1 else t
      map_one' := by simp
      map_mul' := by
        have hc : ∀ x : Multiplicative (ZMod 2), x = 1 ∨ x = Multiplicative.ofAdd 1 := by decide
        have hs11 : Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1 = 1 := by decide
        have hne : Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 := by decide
        intro x y
        rcases hc x with rfl | rfl <;> rcases hc y with rfl | rfl
        · simp
        · simp
        · simp
        · simp [hs11, hne, ht2] }
  have hcomm : ∀ m n, Commute (g₁ m) (g₂ n) := by
    intro m n
    have hm : ((σ (φ m) : L) : N) * t = t * ((σ (φ m) : L) : N) :=
      Subgroup.mem_centralizer_singleton_iff.1 (hLC (σ (φ m)).2).2
    by_cases hn : n = 1
    · simp [g₂, hn]
    · simp only [g₂, MonoidHom.coe_mk, OneHom.coe_mk, hn, ite_false]
      exact hm
  let f := g₁.noncommCoprod g₂ hcomm
  have hT : SectionalTwoRankLE ↥(⊤ : Subgroup N) 4 := SectionalTwoRankLE.subgroup ⊤ hN
  refine not_sectionalTwoRankLE_of_char (⊤ : Subgroup N) f (fun _ => Subgroup.mem_top _) psi5
    psi5_sq ?_ (r := 4) (by have := two_pow_le_card_psi5; omega) hT
  rintro ⟨⟨a, b⟩, ε⟩ hk
  have hc : ∀ x : Multiplicative (ZMod 2), x = 1 ∨ x = Multiplicative.ofAdd 1 := by decide
  have hfk : f ((a, b), ε) = g₁ (a, b) * g₂ ε := by
    simp only [f, MonoidHom.noncommCoprod_apply]
  rcases hc ε with rfl | rfl
  · have h1 : ((σ (φ (a, b)) : L) : N) = 1 := by
      have h0 : g₂ 1 = 1 := map_one g₂
      rw [hfk, h0, mul_one] at hk
      exact hk
    have h2 : σ (φ (a, b)) = 1 := Subtype.ext h1
    have h4 := hker (show φ (a, b) ∈ σ.ker from h2)
    rcases hφc _ h4 with h5 | h5
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h5
      exact psi5_eq_one_of (Or.inl rfl) (Or.inl rfl) rfl
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h5
      exact psi5_eq_one_of (Or.inr rfl) (Or.inr rfl) rfl
  · exfalso
    have hne : Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 := by decide
    have h0 : g₂ (Multiplicative.ofAdd 1) = t := by simp [g₂, hne]
    rw [hfk, h0] at hk
    have ht' : t = (g₁ (a, b))⁻¹ := eq_inv_of_mul_eq_one_right hk
    have hmem : t ∈ L := by
      rw [ht']
      exact L.inv_mem (σ (φ (a, b))).2
    exact htH (hLC hmem).1

end Alt

section Certified


theorem false_of_graph_nonsplit4 {N : Type} [Group N] [Finite N] (H : Subgroup N) [H.Normal]
    {t : N} {L : Subgroup N} (hs : B2.ShapeInCent H t L) {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F) (e : ↥H ≃* LinearFlag.projectiveSL 4 F)
    (A : GL (Fin 4) F)
    (hA : ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ = (A : Matrix (Fin 4) (Fin 4) F))
    (hns : ¬ ∃ S : Submodule F (Fin 4 → F), Module.finrank F S = 2 ∧
      ∀ x ∈ S, CFSG.ComponentClassification.CatalogueBLinearHigherB.matrixQuadraticForm
        (A⁻¹ : GL (Fin 4) F) x = 0)
    (hτ : MulAut.congr e (MulAut.conjNormal t : MulAut ↥H) =
      LinearFlag.conjAut 4 F A * LinearFlag.dualAut 4 F) : False := by
  have hchar : ringChar F ≠ 2 :=
    CFSG.ComponentClassification.CatalogueBOddQuadratic.char_ne_two_of_odd_card hodd
  obtain ⟨-, E, _, _, hE, ⟨eL⟩⟩ :=
    CFSG.ComponentClassification.OddSelector.selectorRowO_of_nonsplit
      (W := H) (a := t) (L := L) hodd (rhoOf_injective hs.faithful e)
      (map_centralizer_rho hs.faithful e t) (map_inf_centralizer_rho hs.faithful e t)
      (isComponentOf_map_rho hs e) (B := A) ((rhoOf_eq_congr hs.faithful e t).trans hτ) hA hns
  obtain ⟨p, f, hp, hpodd, hf, hF⟩ :=
    CFSG.ComponentClassification.CatalogueBLinearHigherB.exists_odd_prime_pow_card F hchar
  have hp2 : p ≠ 2 := by rintro rfl; exact (Nat.not_odd_iff_even.mpr even_two) hpodd
  have hE' : Nat.card E = p ^ (2 * f) := by rw [hE, hF, ← pow_mul, mul_comm]
  have h4 : 4 ≤ p ^ (2 * f) := by
    have h5' : 5 ≤ p ^ f := by rw [← hF]; exact h5
    calc 4 ≤ 5 * 5 := by norm_num
      _ ≤ p ^ f * p ^ f := Nat.mul_le_mul h5' h5'
      _ = p ^ (2 * f) := by rw [← pow_add]; ring_nf
  exact B2.PumpupTableOmega3.false_of_psl2_component hs hp hp2
    (B2.PumpupTableOmega3.lieModel_psl2_of_equiv hp (by omega) h4 hE'
      (eL.trans (LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 E).symm))

theorem false_of_graph_split4 {N : Type} [Group N] [Finite N] (H : Subgroup N) [H.Normal]
    {t : N} {L : Subgroup N} (hs : B2.ShapeInCent H t L) {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F) (e : ↥H ≃* LinearFlag.projectiveSL 4 F)
    (A : GL (Fin 4) F)
    (hA : ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ = (A : Matrix (Fin 4) (Fin 4) F))
    (hsp : ∃ S : Submodule F (Fin 4 → F), Module.finrank F S = 2 ∧
      ∀ x ∈ S, CFSG.ComponentClassification.CatalogueBLinearHigherB.matrixQuadraticForm
        (A⁻¹ : GL (Fin 4) F) x = 0)
    (hτ : MulAut.congr e (MulAut.conjNormal t : MulAut ↥H) =
      LinearFlag.conjAut 4 F A * LinearFlag.dualAut 4 F) : False := by
  have hchar : ringChar F ≠ 2 :=
    CFSG.ComponentClassification.CatalogueBOddQuadratic.char_ne_two_of_odd_card hodd
  obtain ⟨p, f, hp, hpodd, hf, hF⟩ :=
    CFSG.ComponentClassification.CatalogueBLinearHigherB.exists_odd_prime_pow_card F hchar
  have hp2 : p ≠ 2 := by rintro rfl; exact (Nat.not_odd_iff_even.mpr even_two) hpodd
  obtain ⟨-, ⟨eL⟩⟩ := CFSG.ComponentClassification.OddSelector.Catalog7L4E.split_component_iso
    (A := N) (a := t) (L := L) hp hp2 hf hF (rhoOf_injective hs.faithful e)
    (isComponentOf_map_rho hs e) (B := A) ((rhoOf_eq_congr hs.faithful e t).trans hτ) hA hsp
  have h4 : 4 ≤ p ^ f := by rw [← hF]; omega
  exact B2.PumpupTableOmega3.false_of_psl2_component hs hp hp2
    (B2.PumpupTableOmega3.lieModel_psl2_of_equiv hp hf h4 hF eL)

theorem outGraph_lin4 {N : Type} [Group N] [Finite N] (H : Subgroup N) [H.Normal] {t : N}
    {L : Subgroup N} {F : Type} [Field F] [Finite F] (hs : B2.ShapeInCent H t L)
    (hF4 : Nat.card F % 4 = 3) (h5 : 5 ≤ Nat.card F) (e : ↥H ≃* LinearFlag.projectiveSL 4 F)
    (hnd : ∀ A : GL (Fin 4) F, MulAut.congr e (MulAut.conjNormal t : MulAut ↥H) ≠
      LinearFlag.conjAut 4 F A) (h4 : SectionalTwoRankLE N 4) : False := by
  have hodd : Odd (Nat.card F) := Nat.odd_iff.mpr (by omega)
  have htH : t ∉ H := by
    intro ht
    obtain ⟨g, hg⟩ := LinearFlag.proj_surjective 4 F (e ⟨t, ht⟩)
    apply hnd (Matrix.SpecialLinearGroup.toGL g)
    rw [LinearFlag.conjAut_toGL, hg, ← rhoOf_eq_congr hs.faithful e]
    exact rhoOf_mem e ⟨t, ht⟩
  have ht2 : t ^ 2 = 1 := by
    have := pow_orderOf_eq_one t
    rwa [hs.inv] at this
  have hτ2 : (MulAut.congr e (MulAut.conjNormal t : MulAut ↥H)) ^ 2 = 1 := by
    rw [← map_pow, ← map_pow, ht2, map_one, map_one]
  obtain ⟨A, hτA, hform⟩ := graph_form_of_not_diag4 hF4 _ hτ2 hnd
  rcases hform with hsym | halt
  · by_cases hsp : ∃ S : Submodule F (Fin 4 → F), Module.finrank F S = 2 ∧
        ∀ x ∈ S, CFSG.ComponentClassification.CatalogueBLinearHigherB.matrixQuadraticForm
          (A⁻¹ : GL (Fin 4) F) x = 0
    · exact false_of_graph_split4 H hs hodd h5 e A hsym hsp hτA
    · exact false_of_graph_nonsplit4 H hs hodd h5 e A hsym hsp hτA
  · exact false_of_graph_alt4 H hs htH hodd e A halt hτA h4

end Certified

section Unitary

open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.CatFactsL4U4


theorem false_of_uni_not_diag {N : Type} [Group N] [Finite N] (H : Subgroup N) [H.Normal] {t : N}
    {L : Subgroup N} {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hs : B2.ShapeInCent H t L) (hq3 : 3 < p ^ f) (hp2 : p ≠ 2)
    (e : ↥H ≃* primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))
    (hnd : ∀ A : primeFormUnitary h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K),
      MulAut.congr e (MulAut.conjNormal t : MulAut ↥H) ≠
        primeFormConjHom h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) A)
    (h4 : SectionalTwoRankLE N 4) : False := by
  have : Finite K := h.finite
  obtain ⟨Φ, hΦ⟩ := B2.PuL4GraphUni.exists_stated_equiv h
  set τ := MulAut.congr e (MulAut.conjNormal t : MulAut ↥H) with hτ
  have ht2 : t ^ 2 = 1 := by
    have := pow_orderOf_eq_one t
    rwa [hs.inv] at this
  have hτ2 : τ ^ 2 = 1 := by rw [hτ, ← map_pow, ← map_pow, ht2, map_one, map_one]
  have htH : t ∉ H := by
    intro ht
    obtain ⟨s, hs'⟩ := QuotientGroup.mk_surjective (e ⟨t, ht⟩)
    apply hnd ⟨s, s.2.1⟩
    rw [primeFormConjHom_eq_conj, hs']
    ext x
    apply e.symm.injective
    apply Subtype.ext
    simp [hτ, MulAut.congr_apply, MulAut.conj_apply, MulAut.conjNormal_apply]
  set φ := MulAut.congr Φ τ with hφdef
  have hφ2 : φ ^ 2 = 1 := by rw [hφdef, ← map_pow, hτ2, map_one]
  have hφ : φ ∉ DiagU.InnU p f K h := B2.PuL4GraphUni.congr_not_mem_InnU h hΦ τ hnd
  obtain ⟨A, ψ, hAu, hψ, hψA, c, hAA⟩ := OIU.exists_anti_form h hp2 hφ2 hφ
  have he' : MulAut.congr (e.trans Φ) (MulAut.conjNormal t : MulAut ↥H) = φ := by
    ext x
    simp [hφdef, hτ, MulAut.congr_apply]
  obtain ⟨hJφ, hJ⟩ := B2.PuL4GraphUni.component_transport hs (e.trans Φ)
  rw [he'] at hJφ hJ
  obtain ⟨Y, hY, σ, hσs, hσk, -⟩ := OIU.exists_lift_component h hAu hψ hψA hAA hJφ hJ
  obtain ⟨eLX⟩ := B2.PuL4GraphUni.exists_equiv_image (hs.comp.1.trans inf_le_left) (e.trans Φ)
    (CFSG.ComponentClassification.GSThmB.Catalog7L4EU.ιU h)
    (CFSG.ComponentClassification.GSThmB.Catalog7L4EU.ιU_injective h)
  rcases B2.PuL4GraphUniForm.uni_anti_cases h hp2 hAu hAA hY σ hσs hσk with
    ⟨-, ⟨eY⟩⟩ | ⟨E', _, _, hE', ⟨e2⟩⟩ | ⟨ρ, hρk⟩
  · exact B2.PuL4GraphUniSplit.false_of_uni_split hs h.prime hp2 h.one_le h.card_fixedField hq3
      eY σ hσs hσk eLX
  · exact B2.PuL4GraphUniNonsplit.false_of_uni_nonsplit hs h.prime hp2 h.one_le hq3
      (by rw [hE', h.card_fixedField]) e2 eLX
  · have h2 : (2 : h.fixedField) ≠ 0 := fun h0 => by
      have h1 := congrArg h.fixedField.subtype h0
      rw [map_ofNat, map_zero] at h1
      exact two_ne_zero_of_odd h hp2 h1
    exact B2.PuL4GraphUniAlt.false_of_sp_cover hs htH h2 (eLX.symm.toMonoidHom.comp ρ)
      (fun x hx => hρk (MonoidHom.mem_ker.mpr
        ((MulEquiv.map_eq_one_iff eLX.symm).mp
          (show eLX.symm (ρ x) = 1 from MonoidHom.mem_ker.mp hx)))) h4

end Unitary

end S3T4

end CFSG.GH74.Generic.BProg.B3
