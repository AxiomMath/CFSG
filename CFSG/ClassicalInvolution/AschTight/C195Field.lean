module

public import CFSG.ClassicalInvolution.Asc77.AscL62Aut

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.ABGLocalTools CFSG.GorensteinWalter Matrix CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.AscL62 CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups Pointwise

section General

variable {F : Type} [Field F]

theorem psl2MulAutOf_mul (α β : MulAut SL(2, F)) :
    psl2MulAutOf (α * β) = psl2MulAutOf α * psl2MulAutOf β := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H b => rfl

theorem toGL_semilinHom (G : GL (Fin 2) F) (σ : F ≃+* F) (b : SL(2, F)) :
    SpecialLinearGroup.toGL (semilinHom G σ b) =
      G * GeneralLinearGroup.map σ.toRingHom (SpecialLinearGroup.toGL b) * G⁻¹ :=
  Units.ext rfl

theorem semilinHom_conj (G : GL (Fin 2) F) (σ : F ≃+* F) (h x : SL(2, F))
    (hx : semilinHom G σ x = x) :
    semilinHom (SpecialLinearGroup.toGL h * G *
        (GeneralLinearGroup.map σ.toRingHom (SpecialLinearGroup.toGL h))⁻¹) σ (h * x * h⁻¹) =
      h * x * h⁻¹ := by
  apply SpecialLinearGroup.toGL_injective
  have hx' := congrArg SpecialLinearGroup.toGL hx
  rw [toGL_semilinHom] at hx'
  rw [toGL_semilinHom]
  simp only [map_mul, map_inv]
  conv_rhs => rw [← hx']
  group

theorem exists_eq_semilinHom [Finite F] (hK : IsOddPrimePower (Nat.card F)) (h3 : 3 < Nat.card F)
    {γ : PGammaL2 F} {α : MulAut SL(2, F)}
    (hγ : pGammaL2ToMulAutPSL2 F hK h3 γ = psl2MulAutOf α) :
    ∃ G : GL (Fin 2) F, ∀ b, α b = semilinHom G γ.right b := by
  obtain ⟨G, hG⟩ := Matrix.ProjGenLinGroup.mk_surjective γ.left
  refine ⟨G, eq_semilinHom_of_smul (by omega) α G γ.right fun b => ?_⟩
  obtain ⟨u, hu, h⟩ := coe_mulAut_eq_smul_conj hK h3 α γ hγ G hG b
  exact ⟨u, hu, by rw [coe_semilinHom]; exact h⟩

theorem eq_one_of_semilinHom_eq_conj (G : GL (Fin 2) F) (σ : F ≃+* F) (s : SL(2, F))
    (h : ∀ b, semilinHom G σ b = s * b * s⁻¹) : σ = 1 := by
  ext t
  let b : SL(2, F) := ⟨!![t, -1; 1, 0], by simp [Matrix.det_fin_two]⟩
  have h1 := congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F).trace) (h b)
  simp only [coe_semilinHom, Matrix.SpecialLinearGroup.coe_mul] at h1
  rw [Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul,
    Matrix.trace_mul_cycle, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul] at h1
  simp only [Matrix.trace_fin_two, Matrix.map_apply, b, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    map_zero, add_zero] at h1
  exact h1

theorem diagHom_injective : Function.Injective (diagHom : Fˣ →* SL(2, F)) := by
  intro μ ν h
  have h1 := congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp only [coe_diagHom, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.empty_val', Matrix.cons_val_fin_one] at h1
  exact Units.ext h1

end General

variable {p f : ℕ} [Fact p.Prime]

theorem eight_le_two_pow_padicValNat (hp : p ≠ 2) (hf : Even f) (hf0 : f ≠ 0) :
    8 ≤ 2 ^ padicValNat 2 (p ^ f - 1) := by
  obtain ⟨k, rfl⟩ := hf
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  obtain ⟨m, hm⟩ : Odd (p ^ k) := hpodd.pow
  have hq : p ^ (k + k) = 4 * (m * (m + 1)) + 1 := by rw [pow_add, hm]; ring
  have h8 : 2 ^ 3 ∣ p ^ (k + k) - 1 := by
    rw [hq, Nat.add_sub_cancel]
    obtain ⟨c, hc⟩ := (Nat.even_mul_succ_self m).two_dvd
    exact ⟨c, by rw [hc]; ring⟩
  have hpos : p ^ (k + k) - 1 ≠ 0 := by
    have : 2 ≤ p ^ (k + k) := by
      calc 2 ≤ p := (Fact.out : p.Prime).two_le
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ (k + k) := Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega)
    omega
  have h3 := (padicValNat_dvd_iff_le hpos).mp h8
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ padicValNat 2 (p ^ (k + k) - 1) := Nat.pow_le_pow_right (by norm_num) h3

theorem exists_units_orderOf_two_pow (hf0 : f ≠ 0) :
    ∃ μ : (GaloisField p f)ˣ, orderOf μ = 2 ^ padicValNat 2 (p ^ f - 1) := by
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf0
  have hN0 : p ^ f - 1 ≠ 0 := by
    have : 2 ≤ p ^ f := by
      calc 2 ≤ p := (Fact.out : p.Prime).two_le
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ f := Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega)
    omega
  have hcardU : Nat.card (GaloisField p f)ˣ = p ^ f - 1 := by rw [Nat.card_units, hcard]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (GaloisField p f)ˣ)
  have hgord : orderOf g = p ^ f - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcardU]
  have hM : 2 ^ padicValNat 2 (p ^ f - 1) ∣ p ^ f - 1 := pow_padicValNat_dvd
  have hdvd : (p ^ f - 1) / 2 ^ padicValNat 2 (p ^ f - 1) ∣ orderOf g := by
    rw [hgord]
    exact Nat.div_dvd_of_dvd hM
  have hq0 : (p ^ f - 1) / 2 ^ padicValNat 2 (p ^ f - 1) ≠ 0 := by
    intro h0
    have := Nat.div_eq_zero_iff.mp h0
    have := Nat.le_of_dvd (by omega) hM
    omega
  refine ⟨g ^ ((p ^ f - 1) / 2 ^ padicValNat 2 (p ^ f - 1)), ?_⟩
  rw [orderOf_pow_of_dvd hq0 hdvd, hgord, Nat.div_div_self hM hN0]

theorem false_of_semilinHom_fixes_index_two (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hf : Even f)
    {G : GL (Fin 2) (GaloisField p f)} {σ : GaloisField p f ≃+* GaloisField p f}
    (hσ2 : σ * σ = 1) (hσ : σ ≠ 1) (P₁ : Sylow 2 SL(2, GaloisField p f))
    {D₁ : Subgroup SL(2, GaloisField p f)} (hD₁P : D₁ ≤ P₁)
    (hD₁ab : ∀ x ∈ D₁, ∀ y ∈ D₁, x * y = y * x) (hD₁card : Nat.card P₁ ≤ 2 * Nat.card D₁)
    (hfix : ∀ x ∈ D₁, semilinHom G σ x = x) : False := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hodd : Odd (Nat.card (GaloisField p f)) := odd_natCard_galoisField hp hq
  have hF2 : ringChar (GaloisField p f) ≠ 2 := by
    rw [ringChar.eq (GaloisField p f) p]
    exact hp
  obtain ⟨μ, hμ⟩ := exists_units_orderOf_two_pow (p := p) hf0
  have hM8 := eight_le_two_pow_padicValNat hp hf hf0
  set M := 2 ^ padicValNat 2 (p ^ f - 1) with hMdef
  set x₀ : SL(2, GaloisField p f) := diagHom μ with hx₀
  have hx₀ord : orderOf x₀ = M := by
    rw [hx₀, orderOf_injective diagHom diagHom_injective μ, hμ]
  have hx₀2 : IsPGroup 2 ↥(Subgroup.zpowers x₀) :=
    IsPGroup.of_card (n := padicValNat 2 (p ^ f - 1)) (by rw [Nat.card_zpowers, hx₀ord])
  obtain ⟨P₀, hP₀⟩ := hx₀2.exists_le_sylow
  have hx₀P₀ : x₀ ∈ (P₀ : Subgroup SL(2, GaloisField p f)) := hP₀ (Subgroup.mem_zpowers x₀)
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq SL(2, GaloisField p f) P₁ P₀
  set D : Subgroup SL(2, GaloisField p f) := D₁.map (MulAut.conj h).toMonoidHom with hD
  have hDP₀ : D ≤ P₀ := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 : (MulAut.conj h) • y ∈ (MulAut.conj h) • (P₁ : Subgroup SL(2, GaloisField p f)) :=
      Subgroup.smul_mem_pointwise_smul y (MulAut.conj h) _ (hD₁P hy)
    rw [← Sylow.coe_subgroup_smul, hh] at h1
    exact h1
  have hDcard : Nat.card D = Nat.card D₁ :=
    Subgroup.card_map_of_injective (MulAut.conj h).injective
  have hP₀P₁ : Nat.card P₀ = Nat.card P₁ := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  have hDab : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hD₁ab x hx y hy]
  obtain ⟨k, hk, ⟨e⟩⟩ := specialLinearGroup_sylow_quaternion (GaloisField p f) hF2 P₀
  have hquat : IsQuatSub (P₀ : Subgroup SL(2, GaloisField p f)) := ⟨k, hk, ⟨e⟩⟩
  have hz := isUniqueInvolution_top_neg_one hodd
  have hzP₀ : (-1 : SL(2, GaloisField p f)) ∈ (P₀ : Subgroup SL(2, GaloisField p f)) :=
    mem_of_uniqueInvolution_of_pGroup hz le_top P₀.isPGroup' (by have := hquat.eight_le; omega)
  have hzP' := isUniqueInvolution_of_le hz le_top hzP₀
  obtain ⟨C₀, hC₀P, hC₀c, hC₀card, hC₀mem⟩ := hquat.exists_cyclic_max
  have hx₀C₀ : x₀ ∈ C₀ := hC₀mem x₀ hx₀P₀ (by rw [hx₀ord]; omega)
  have hMC₀ : M ≤ Nat.card C₀ := by
    rw [← hx₀ord]
    exact Nat.le_of_dvd Nat.card_pos (Subgroup.orderOf_dvd_natCard C₀ hx₀C₀)
  have hDC₀ : D ≤ C₀ := by
    by_contra hDC
    obtain ⟨g, hgD, hgC⟩ := IsConcreteLE.not_le_iff_exists.mp hDC
    have hsmall : C₀ ⊓ D ≤ Subgroup.zpowers (-1 : SL(2, GaloisField p f)) := by
      intro c ⟨hcC, hcD⟩
      have h1 := conj_eq_inv_of_not_mem hquat hzP' hC₀P hC₀c hC₀card (hDP₀ hgD) hgC hcC
      rw [hDab g hgD c hcD, mul_inv_cancel_right] at h1
      have hcc : c * c = 1 := by
        calc c * c = c * c⁻¹ := by rw [← h1]
          _ = 1 := mul_inv_cancel c
      rcases hz.unique c (Subgroup.mem_top c) hcc with rfl | rfl
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers _
    have h2 : Nat.card ↥(C₀ ⊓ D) ≤ 2 := by
      refine (Subgroup.card_le_of_le hsmall).trans ?_
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hz.sq))
    have hidx : C₀.relIndex P₀ = 2 := by
      have h5 := Subgroup.relIndex_mul_card (H := C₀) (K := (P₀ : Subgroup SL(2, GaloisField p f)))
      rw [inf_eq_left.mpr hC₀P, hC₀card] at h5
      exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h5
    have hle := Subgroup.relIndex_le_of_le_right (H := C₀) hDP₀ (by rw [hidx]; norm_num)
    have h3 := Subgroup.relIndex_mul_card (H := C₀) (K := D)
    rw [hidx] at hle
    have h4 : Nat.card D ≤ 4 := by nlinarith
    omega
  have hDeq : D = C₀ := Subgroup.eq_of_le_of_card_ge hDC₀ (by omega)
  have hx₀D : x₀ ∈ D := hDeq ▸ hx₀C₀
  obtain ⟨d, hdD, hdx⟩ := hx₀D
  have hdx' : h * d * h⁻¹ = x₀ := by
    rw [← hdx]
    simp [MulAut.conj_apply]
  have h1 := semilinHom_conj G σ h d (hfix d hdD)
  rw [hdx'] at h1
  exact false_of_fixes_diag hp hq hσ2 hσ hμ h1

theorem right_eq_one_of_fixes_index_two (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hf : Even f)
    (hK : IsOddPrimePower (Nat.card (GaloisField p f))) (h3 : 3 < Nat.card (GaloisField p f))
    (P₁ : Sylow 2 SL(2, GaloisField p f)) {D₁ : Subgroup SL(2, GaloisField p f)}
    (hD₁P : D₁ ≤ P₁) (hD₁ab : ∀ x ∈ D₁, ∀ y ∈ D₁, x * y = y * x)
    (hD₁card : Nat.card P₁ ≤ 2 * Nat.card D₁) (n : ℕ) :
    ∀ (γ : PGammaL2 (GaloisField p f)) (α : MulAut SL(2, GaloisField p f)),
      pGammaL2ToMulAutPSL2 _ hK h3 γ = psl2MulAutOf α → γ ^ 2 ^ n = 1 →
        (∀ x ∈ D₁, α x = x) → γ.right = 1 := by
  induction n with
  | zero =>
    intro γ α _ hγn _
    rw [pow_zero, pow_one] at hγn
    rw [hγn]
    rfl
  | succ n ih =>
    intro γ α hγ hγn hfix
    have h2 := ih (γ ^ 2) (α ^ 2)
      (by rw [map_pow, hγ, pow_two, pow_two, psl2MulAutOf_mul])
      (by rw [← pow_mul, ← pow_succ']; exact hγn)
      (fun x hx => by rw [pow_two, MulAut.mul_apply, hfix x hx, hfix x hx])
    rw [pGammaL2_pow_right, pow_two] at h2
    by_contra hσ
    obtain ⟨G, hG⟩ := exists_eq_semilinHom hK h3 hγ
    exact false_of_semilinHom_fixes_index_two hp hq hf h2 hσ P₁ hD₁P hD₁ab hD₁card
      (fun x hx => by rw [← hG]; exact hfix x hx)

end CFSG.ClassicalInvolution.Disconnected.AschTight
