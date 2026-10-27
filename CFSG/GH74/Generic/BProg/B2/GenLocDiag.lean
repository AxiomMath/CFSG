module

public import CFSG.GH74.Generic.BProg.B2.GenLocBasicRed
public import CFSG.GH74.Generic.BProg.B2.WeakSigDiag
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification Subgroup Matrix

namespace GenLocDiag

variable {A : Type} [Group A]

theorem adm_comap_of_card_le [Finite A] (hA : CFSG.IsElementaryAbelian 2 A) {G : Type} [Group G]
    (ρ : A →* G) (E' : Subgroup G) (hE' : E' ≤ ρ.range) (hcard : Nat.card ρ.range ≤ 2 * Nat.card E') :
    pRank 2 A - 1 ≤ pRank 2 ↥(E'.comap ρ) := by
  rw [GenLocBasic.adm_iff_index hA, Subgroup.index_comap]
  have hR : Finite ↥ρ.range := Finite.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  have : Finite ↥E' := Finite.of_injective _ (Subgroup.inclusion_injective hE')
  have h1 : Nat.card ↥(E'.subgroupOf ρ.range) = Nat.card E' :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE').toEquiv
  have h2 := Subgroup.card_mul_index (E'.subgroupOf ρ.range)
  rw [h1] at h2
  have hpos : 0 < Nat.card E' := Nat.card_pos
  unfold Subgroup.relIndex
  by_contra hlt
  have hlt := not_le.mp hlt
  have : Nat.card E' * 3 ≤ Nat.card E' * (E'.subgroupOf ρ.range).index := Nat.mul_le_mul_left _ hlt
  omega

theorem map_gammaAct_le {J J' : Type} [Group J] [Group J'] (α : A →* MulAut J) (α' : A →* MulAut J')
    (π : J →* J') (hπ : ∀ (a : A) (x : J), π (α a x) = α' a (π x)) :
    (gammaAct α).map π ≤ gammaAct α' := by
  rw [gammaAct, Subgroup.map_iSup]
  refine iSup_le fun E => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hE => ?_
  rintro _ ⟨x, hx, rfl⟩
  refine le_gammaAct α' hE ?_
  rw [GenLocBasic.mem_fixedIn_map]
  intro a ha
  rw [← hπ, (GenLocBasic.mem_fixedIn_map _ _ _).1 hx a ha]

theorem gammaAct_eq_top_of_surj {J J' : Type} [Group J] [Group J'] (α : A →* MulAut J)
    (α' : A →* MulAut J') (π : J →* J') (hπs : Function.Surjective π)
    (hπ : ∀ (a : A) (x : J), π (α a x) = α' a (π x)) (h : gammaAct α = ⊤) : gammaAct α' = ⊤ := by
  have := map_gammaAct_le α α' π hπ
  rw [h, Subgroup.map_top_of_surjective π hπs] at this
  exact eq_top_iff.2 this

theorem pow_eq_one_of_mem_scalars {n : ℕ} {F : Type} [Field F] {z : SpecialLinearGroup (Fin n) F}
    (hz : z ∈ LinearFlag.scalars n F) : z ^ n = 1 := by
  obtain ⟨c, hc, hzc⟩ := LinearFlag.mem_scalars.1 hz
  apply Subtype.ext
  show ((z ^ n : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) =
    ((1 : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F)
  rw [Matrix.SpecialLinearGroup.coe_pow, hzc, ← map_pow, ← Units.val_pow_eq_pow_val, hc]
  simp

theorem not_two_dvd_card_scalars {n : ℕ} (hn : Odd n) {F : Type} [Field F] [Finite F] :
    ¬ 2 ∣ Nat.card (LinearFlag.scalars n F) := by
  intro h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := LinearFlag.scalars n F) 2 h
  have h1 : orderOf z ∣ n := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    simpa using pow_eq_one_of_mem_scalars z.2
  rw [hz] at h1
  exact (Nat.not_even_iff_odd.2 hn) (even_iff_two_dvd.2 h1)

theorem exists_involutive_section {n : ℕ} (hn : Odd n) {F : Type} [Field F] [Finite F]
    (D : Subgroup (LinearFlag.projectiveSL n F)) (hD : CFSG.IsElementaryAbelian 2 ↥D) :
    ∃ σ : ↥D →* SpecialLinearGroup (Fin n) F,
      (∀ d, LinearFlag.proj n F (σ d) = d) ∧ ∀ d, σ d * σ d = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfin : Finite (SpecialLinearGroup (Fin n) F) :=
    Finite.of_injective (Subtype.val : SpecialLinearGroup (Fin n) F → Matrix (Fin n) (Fin n) F)
      Subtype.val_injective
  obtain ⟨T, hTmap, hTdis⟩ := CFSG.RankThree.PartOne.CTP.SeitzToral.exists_lift_of_coprime_ker
    (LinearFlag.proj n F) (LinearFlag.proj_surjective n F) (p := 2)
    (by rw [LinearFlag.ker_proj]; exact not_two_dvd_card_scalars hn) D
    (CFSG.IsElementaryAbelian.isPGroup 2 ↥D)
  have hTmem : ∀ x ∈ T, LinearFlag.proj n F x ∈ D := fun x hx => hTmap ▸ ⟨x, hx, rfl⟩
  let fπ : T →* D := ((LinearFlag.proj n F).comp T.subtype).codRestrict D (fun x => hTmem x.1 x.2)
  have hsurj : Function.Surjective fπ := by
    intro d
    have : (d : LinearFlag.projectiveSL n F) ∈ T.map (LinearFlag.proj n F) := hTmap ▸ d.2
    obtain ⟨x, hx, hxd⟩ := this
    exact ⟨⟨x, hx⟩, Subtype.ext hxd⟩
  have hinj : Function.Injective fπ := by
    intro x y hxy
    have h1 : LinearFlag.proj n F x.1 = LinearFlag.proj n F y.1 := congrArg Subtype.val hxy
    have h2 : x.1⁻¹ * y.1 ∈ (LinearFlag.proj n F).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
    have h3 : x.1⁻¹ * y.1 = 1 :=
      Subgroup.disjoint_def.mp hTdis (T.mul_mem (T.inv_mem x.2) y.2) h2
    exact Subtype.ext (inv_mul_eq_one.mp h3)
  let e : T ≃* D := MulEquiv.ofBijective fπ ⟨hinj, hsurj⟩
  have hπe : ∀ d : D, LinearFlag.proj n F (e.symm d : T) = d := fun d =>
    congrArg Subtype.val (e.apply_symm_apply d)
  refine ⟨T.subtype.comp e.symm.toMonoidHom, hπe, fun d => ?_⟩
  have hk : ((e.symm d : T) : SpecialLinearGroup (Fin n) F) * (e.symm d : T) ∈
      (LinearFlag.proj n F).ker := by
    rw [MonoidHom.mem_ker, map_mul, hπe]
    exact Subtype.ext_iff.1 (WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hD d)
  exact Subgroup.disjoint_def.mp hTdis (T.mul_mem (e.symm d).2 (e.symm d).2) hk

theorem slConjugation_toGL {n : ℕ} {F : Type} [Field F] (u g : SpecialLinearGroup (Fin n) F) :
    CatalogueBHigherLinearAction.slConjugation n F (SpecialLinearGroup.toGL u) g = u * g * u⁻¹ := by
  apply Subtype.ext
  rw [LinearFlag.coe_slConjugation, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    ← map_inv]
  rfl

end GenLocDiag

section Diag

variable {A : Type} [Group A] [Finite A]

theorem gammaAct_sl_of_diag {n : ℕ} {F : Type} [Field F] [Finite F]
    (hA : CFSG.IsElementaryAbelian 2 A) (α : A →* MulAut (Matrix.SpecialLinearGroup (Fin n) F))
    (ρ : A →* GL (Fin n) F) (hdiag : ∀ a, ((ρ a : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).IsDiag)
    (hsq : ∀ a, ρ a * ρ a = 1)
    (hρ : ∀ (a : A) (g : Matrix.SpecialLinearGroup (Fin n) F),
      ((α a g : Matrix.SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        (ρ a : Matrix (Fin n) (Fin n) F) * (g : Matrix (Fin n) (Fin n) F) *
          ((ρ a)⁻¹ : GL (Fin n) F)) :
    gammaAct α = ⊤ := by
  have hfin : Finite ↥ρ.range := Finite.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  have key := closure_centralizer_hyperplane_diag_eq_top ρ.range
    (fun x hx i j hij => by obtain ⟨a, rfl⟩ := hx; exact hdiag a hij)
    (fun x hx => by obtain ⟨a, rfl⟩ := hx; exact hsq a)
  rw [eq_top_iff, ← key, Subgroup.closure_le]
  rintro g ⟨E', hE'D, hcard, hcomm⟩
  have hadm := GenLocDiag.adm_comap_of_card_le hA ρ E' hE'D hcard
  refine le_gammaAct α hadm ?_
  rw [GenLocBasic.mem_fixedIn_map]
  intro a ha
  apply Subtype.ext
  rw [hρ, ← hcomm (ρ a) ha, mul_assoc, Units.mul_inv, mul_one]

theorem gammaAct_projectiveSL_of_diag {n : ℕ} {F : Type} [Field F] [Finite F]
    (hA : CFSG.IsElementaryAbelian 2 A) (α : A →* MulAut (LinearFlag.projectiveSL n F))
    (ρ : A →* GL (Fin n) F) (hdiag : ∀ a, ((ρ a : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).IsDiag)
    (hsq : ∀ a, ρ a * ρ a = 1) (hρ : ∀ a, α a = LinearFlag.conjAut n F (ρ a)) :
    gammaAct α = ⊤ := by
  let α' : A →* MulAut (SpecialLinearGroup (Fin n) F) :=
    (CatalogueBHigherLinearAction.slConjugation n F).comp ρ
  have h1 : gammaAct α' = ⊤ :=
    gammaAct_sl_of_diag hA α' ρ hdiag hsq fun a g => LinearFlag.coe_slConjugation (ρ a) g
  refine GenLocDiag.gammaAct_eq_top_of_surj α' α (LinearFlag.proj n F) (LinearFlag.proj_surjective n F)
    (fun a g => ?_) h1
  rw [hρ a, LinearFlag.conjAut_proj]
  rfl

theorem exists_diag_lift_of_odd {n : ℕ} (hn : Odd n) {F : Type} [Field F] [Finite F]
    (hF : ringChar F ≠ 2) (D : Subgroup (LinearFlag.projectiveSL n F)) (hD : CFSG.IsElementaryAbelian 2 ↥D) :
    ∃ (B : GL (Fin n) F) (ρ : ↥D →* GL (Fin n) F),
      (∀ d, ((B⁻¹ * ρ d * B : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).IsDiag ∧ ρ d * ρ d = 1) ∧
      ∀ d, LinearFlag.conjAut n F (ρ d) = MulAut.conj (d : LinearFlag.projectiveSL n F) := by
  have := hD
  obtain ⟨σ, hσπ, hσsq⟩ := GenLocDiag.exists_involutive_section hn D hD
  let ρ : ↥D →* GL (Fin n) F := SpecialLinearGroup.toGL.comp σ
  have hρsq : ∀ d, ρ d * ρ d = 1 := fun d => by
    show SpecialLinearGroup.toGL (σ d) * SpecialLinearGroup.toGL (σ d) = 1
    rw [← map_mul, hσsq, map_one]
  have hcomm : ∀ x ∈ ρ.range, ∀ y ∈ ρ.range, x * y = y * x := by
    rintro _ ⟨d, rfl⟩ _ ⟨d', rfl⟩
    rw [← map_mul, ← map_mul, mul_comm' d d']
  have hexp : ∀ x ∈ ρ.range, x ^ 2 = 1 := by
    rintro _ ⟨d, rfl⟩
    rw [pow_two]
    exact hρsq d
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F (ringChar F) := ringChar.charP F
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartOne.CTP.exists_conj_diagonal_of_exponent_prime
    ⟨-1, IsPrimitiveRoot.neg_one (ringChar F) hF⟩ ρ.range hcomm hexp
  refine ⟨g⁻¹, ρ, fun d => ⟨?_, hρsq d⟩, fun d => ?_⟩
  · rw [inv_inv]
    intro i j hij
    exact hg (ρ d) ⟨d, rfl⟩ i j hij
  · ext y
    obtain ⟨h, rfl⟩ := LinearFlag.proj_surjective n F y
    change LinearFlag.conjAut n F (SpecialLinearGroup.toGL (σ d)) (LinearFlag.proj n F h) = _
    rw [LinearFlag.conjAut_proj, GenLocDiag.slConjugation_toGL, MulAut.conj_apply, map_mul, map_mul,
      map_inv, hσπ]

end Diag

section Inner

variable {A : Type} [Group A] [Finite A]

theorem gammaAct_projectiveSL_of_inner_odd {n : ℕ} (hn : Odd n) {F : Type} [Field F] [Finite F]
    (hF : ringChar F ≠ 2) (hA : CFSG.IsElementaryAbelian 2 A)
    (α : A →* MulAut (LinearFlag.projectiveSL n F)) (δ : A →* LinearFlag.projectiveSL n F)
    (hδ : ∀ a, α a = MulAut.conj (δ a)) : gammaAct α = ⊤ := by
  have hD : CFSG.IsElementaryAbelian 2 ↥δ.range :=
    GenLocBasic.isEA_of_surjective hA δ.rangeRestrict δ.rangeRestrict_surjective
  obtain ⟨B, ρ, hρ, hconj⟩ := exists_diag_lift_of_odd hn hF δ.range hD
  let ρ₁ : A →* GL (Fin n) F := ρ.comp δ.rangeRestrict
  let ρ₂ : A →* GL (Fin n) F := (MulAut.conj B⁻¹).toMonoidHom.comp ρ₁
  have h2 : ∀ a, ρ₂ a = B⁻¹ * ρ₁ a * B := fun a => by
    simp [ρ₂]
  have hα₁ : ∀ a, α a = LinearFlag.conjAut n F (ρ₁ a) := fun a => by
    rw [hδ a]
    exact (hconj (δ.rangeRestrict a)).symm
  let α₂ : A →* MulAut (LinearFlag.projectiveSL n F) := (LinearFlag.conjAut n F).comp ρ₂
  have h := gammaAct_projectiveSL_of_diag hA α₂ ρ₂ (fun a => by rw [h2]; exact (hρ _).1)
    (fun a => by
      have h3 : ρ₁ a * ρ₁ a = 1 := (hρ (δ.rangeRestrict a)).2
      calc ρ₂ a * ρ₂ a = B⁻¹ * (ρ₁ a * ρ₁ a) * B := by rw [h2]; group
        _ = 1 := by rw [h3]; group) fun a => rfl
  refine GenLocDiag.gammaAct_eq_top_of_surj α₂ α (LinearFlag.conjAut n F B).toMonoidHom
    (LinearFlag.conjAut n F B).surjective (fun a x => ?_) h
  show LinearFlag.conjAut n F B (LinearFlag.conjAut n F (ρ₂ a) x) = α a (LinearFlag.conjAut n F B x)
  rw [hα₁ a]
  have e1 : B * ρ₂ a = ρ₁ a * B := by rw [h2]; group
  have := congrArg (fun m => LinearFlag.conjAut n F m x) e1
  simpa only [map_mul, MulAut.mul_apply] using this

theorem gammaAct_projectiveSL_of_inner_odd' {n : ℕ} (hn : Odd n) {F : Type} [Field F] [Finite F]
    (hF : ringChar F ≠ 2)
    (hinj : Function.Injective
      (MulAut.conj : LinearFlag.projectiveSL n F →* MulAut (LinearFlag.projectiveSL n F)))
    (hA : CFSG.IsElementaryAbelian 2 A) (α : A →* MulAut (LinearFlag.projectiveSL n F))
    (hα : ∀ a, α a ∈
      (MulAut.conj : LinearFlag.projectiveSL n F →* MulAut (LinearFlag.projectiveSL n F)).range) :
    gammaAct α = ⊤ := by
  let e := MonoidHom.ofInjective hinj
  refine gammaAct_projectiveSL_of_inner_odd hn hF hA α
    (e.symm.toMonoidHom.comp (α.codRestrict _ hα)) fun a => ?_
  have h := congrArg Subtype.val (e.apply_symm_apply ⟨α a, hα a⟩)
  exact h.symm

end Inner

end CFSG.GH74.Generic.BProg.B2
