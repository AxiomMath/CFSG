module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73ClSp4Inv
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73ClSp4Field
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Comp
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73ClBridge
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Main

public section

namespace CFSG.GH74.GLS.IVK

open CFSG Subgroup Module Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.RestrictedStd
open CFSG.ComponentClassification.CatFactsSp4
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.ComponentClassification.CatalogueBSymplecticRepresentation
open CFSG.ComponentClassification.OddClassSelector CFSG.ComponentClassification.OddSelector
open CFSG.ComponentClassification.OutcomeLocal
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section Sp4Glue

variable {F : Type} [Field F] [Finite F]

theorem isSquare_mul_of_not_isSquare' {a b : F} (ha : ¬ IsSquare a) (hb : ¬ IsSquare b) :
    IsSquare (a * b) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have ha0 : a ≠ 0 := fun h => ha ⟨0, by rw [h, mul_zero]⟩
  have hb0 : b ≠ 0 := fun h => hb ⟨0, by rw [h, mul_zero]⟩
  have h1 : quadraticChar F a = -1 := quadraticChar_neg_one_iff_not_isSquare.2 ha
  have h2 : quadraticChar F b = -1 := quadraticChar_neg_one_iff_not_isSquare.2 hb
  have hab : quadraticChar F (a * b) = 1 := by
    rw [map_mul, h1, h2]
    norm_num
  exact (quadraticChar_one_iff_isSquare (mul_ne_zero ha0 hb0)).1 hab

omit [Finite F] in
theorem psp4_inner_of_square_multiplier (Am : gsp 2 F)
    (hsq : ∃ l : F, l ^ 2 = (multiplierUnit Am : F)) :
    ∃ g : StatedProj (StatedSp 2 F), conjAut 2 F Am = MulAut.conj g := by
  obtain ⟨l, hl⟩ := hsq
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero] at hl
    exact (multiplierUnit Am).ne_zero hl.symm
  have hμ := multiplierUnit_spec Am
  set Mm : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
    ((Am : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) with hMm
  have hA'sp : (l⁻¹ • Mm)ᵀ * formJ 2 F * (l⁻¹ • Mm) = formJ 2 F := by
    rw [transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, hμ, smul_smul,
      smul_smul, ← hl]
    rw [show l⁻¹ * l⁻¹ * l ^ 2 = 1 by field_simp, one_smul]
  set A' : StatedSp 2 F := toSp (l⁻¹ • Mm) hA'sp with hA'def
  have hAz : (Am : GL (Fin 2 ⊕ Fin 2) F) =
      GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) (Units.mk0 l hl0) *
        (A' : GL (Fin 2 ⊕ Fin 2) F) := by
    apply Units.ext
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar, hA'def, coe_toSp, Units.val_mk0,
      Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul,
      smul_smul, mul_inv_cancel₀ hl0, one_smul]
  exact ⟨proj 2 F A', conjAut_eq_conj_of_scalar_mul Am _ A' hAz⟩

omit [Finite F] in
theorem psp4_mem_of_square {A : Type} [Group A] {W : Subgroup A}
    (θ : W ≃* StatedProj (StatedSp 2 F))
    {ρ : A →* MulAut (StatedProj (StatedSp 2 F))} (hinj : Function.Injective ρ)
    (hρW : ∀ w : W, ρ w = MulAut.conj (θ w)) {u : A} {Au : gsp 2 F}
    (hρ : ρ u = conjAut 2 F Au) (hsq : ∃ l : F, l ^ 2 = (multiplierUnit Au : F)) : u ∈ W := by
  obtain ⟨g, hg⟩ := psp4_inner_of_square_multiplier Au hsq
  have h1 : ρ ((θ.symm g : W) : A) = ρ u := by
    rw [hρW, MulEquiv.apply_symm_apply, ← hg, hρ]
  have := hinj h1
  rw [← this]
  exact (θ.symm g).2

end Sp4Glue

section Sp4Core

variable {A : Type} [Group A] [Finite A] {W K : Subgroup A}

theorem psp4_hterm_W (hKW : K ≤ W) (hev : 2 ∣ Nat.card K)
    (hterm : ∀ u : A, orderOf u = 2 → u ∈ centralizer (K : Set A) →
      IsCompIn (centralizer ({u} : Set A)) K)
    (w : W) (hw : orderOf w = 2) (hwK : w ∈ centralizer ((K.subgroupOf W : Subgroup W) : Set W)) :
    K.subgroupOf W ≤ centralizer ({w} : Set W) ∧
      CFSG.IsPComponent 2 ((K.subgroupOf W).subgroupOf (centralizer ({w} : Set W))) := by
  have hwA : orderOf (w : A) = 2 := by rwa [Subgroup.orderOf_coe]
  have huC : (w : A) ∈ centralizer (K : Set A) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have := Subgroup.mem_centralizer_iff.1 hwK ⟨k, hKW hk⟩ hk
    exact congrArg Subtype.val this
  have hterm' := hterm (w : A) hwA huC
  have hKM : K ≤ centralizer ({(w : A)} : Set A) ⊓ W := le_inf hterm'.1 hKW
  have hM : IsCompIn (centralizer ({(w : A)} : Set A) ⊓ W) K :=
    LU.Local.isCompIn_mono' hterm' hKM inf_le_left
  have hB : IsCompIn (centralizer ({w} : Set W)) (K.subgroupOf W) := by
    have := subgroupOf_centralizer_inf_eq (L := W) (w : A) w.2
    rw [Subtype.coe_eta] at this
    rw [← this]
    exact ⟨Subgroup.subgroupOf_mono W hKM,
      (LU.Local.isComponent_subgroupOf_iff' (K := K)
        (M := centralizer ({(w : A)} : Set A) ⊓ W) (H := W) inf_le_right).2 hM.2⟩
  have hev' : 2 ∣ Nat.card ↥(K.subgroupOf W) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKW).toEquiv]
    exact hev
  exact C3.Layer1.Bk.isPCompIn_two_of_isCompIn_of_even hB hev'

end Sp4Core

section Sp4Main

variable {A : Type} [Group A] [Finite A] {W K : Subgroup A}

theorem psp4_core [W.Normal] (hCW : centralizer (W : Set A) = ⊥) (hKW : K ≤ W)
    (hWnab : ∃ a b : W, a * b ≠ b * a) (hWs : IsSimpleGroup W) {ℓ e : ℕ} {F : Type} [Field F]
    [Finite F] (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e) (hF : Nat.card F = ℓ ^ e)
    (hs : SmallSource K) (hodd : Odd (Nat.card (center K))) (hev : 2 ∣ Nat.card K)
    (θ : W ≃* StatedProj (StatedSp 2 F))
    {x y : A} (hx : orderOf x = 2) (hy : orderOf y = 2) (hxy : x ≠ y) (hcomm : x * y = y * x)
    (hxK : x ∈ centralizer (K : Set A)) (hyK : y ∈ centralizer (K : Set A))
    (hterm : ∀ u : A, orderOf u = 2 → u ∈ centralizer (K : Set A) →
      IsCompIn (centralizer ({u} : Set A)) K) : False := by
  classical
  have hodd' : Odd (Nat.card F) := by rw [hF]; exact (hℓ.odd_of_ne_two hℓ2).pow
  have : CharP F ℓ := finite_field_prime_power_characteristic hℓ he hF
  have hchar : ringChar F ≠ 2 := by rw [ringChar.eq F ℓ]; exact hℓ2
  have : IsSimpleGroup (StatedProj (StatedSp 2 F)) := θ.symm.isSimpleGroup
  have hnabP : ∃ a b : StatedProj (StatedSp 2 F), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hWnab
    exact ⟨θ a, θ b, fun h => hab (θ.injective (by rw [map_mul, map_mul, h]))⟩
  have hZ := OutcomeLocal.center_eq_bot_of_isSimpleGroup hnabP
  have hcj := conj_injective hZ
  obtain ⟨ρ, hinj, hρW, -, -⟩ := socle_extension hCW θ hZ
  have hKu : ∀ u : A, orderOf u = 2 → u ∈ centralizer (K : Set A) →
      CFSG.Assembly.IsComponentOf K (centralizer ({u} : Set A)) := fun u hu huK =>
    (isComponentOf_iff_isComponent_subgroupOf (hterm u hu huK).1).2 (hterm u hu huK).2
  have htype : ∀ u : A, orderOf u = 2 → u ∈ centralizer (K : Set A) →
      ∃ Au : gsp 2 F, ρ u = conjAut 2 F Au := by
    intro u hu huK
    have hL₁ := (socle_images θ hinj hρW hKW (hKu u hu huK)).2.2.2
    have hαα : ρ u * ρ u = 1 := by
      have hu2 : u * u = 1 := by
        have := pow_orderOf_eq_one u
        rwa [hu, pow_two] at this
      rw [← map_mul, hu2, map_one]
    have hα1 : ρ u ≠ 1 := by
      intro h
      have h1 : u = 1 := hinj (by rw [h, map_one])
      rw [h1, orderOf_one] at hu
      omega
    obtain ⟨Am, σ, hα, hσ2, ⟨dd, hdd⟩, -, -⟩ :=
      (odd_symplectic_automorphism_semilinear_representation hchar (le_refl 2)).2.2 (ρ u) hαα hα1
    by_cases hσ : σ = 1
    · subst hσ
      exact ⟨Am, by rw [hα, map_one, mul_one]⟩
    · exact (psp4_field_false hℓ hℓ2 he hF hs hinj hcj hL₁ hα hσ2 hdd hσ).elim
  have hinner : ∀ v : A, v ∈ W → orderOf v = 2 → v ∈ centralizer (K : Set A) → False := by
    intro v hvW hv hvK
    refine psp4_inner_false hodd' (W := W) θ (K₀ := K.subgroupOf W) ?_ ?_ (v := ⟨v, hvW⟩) ?_ ?_
    · have e := (Subgroup.subgroupOfEquivOfLe hKW)
      rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
      exact hodd
    · intro w hw hwK
      exact psp4_hterm_W hKW hev hterm w hw hwK
    · rwa [← Subgroup.orderOf_coe]
    · rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have := Subgroup.mem_centralizer_iff.1 hvK k.1 hk
      exact Subtype.ext this
  obtain ⟨Ax, hAx⟩ := htype x hx hxK
  obtain ⟨Ay, hAy⟩ := htype y hy hyK
  by_cases hx2 : ∃ l : F, l ^ 2 = (multiplierUnit Ax : F)
  · exact hinner x (psp4_mem_of_square θ hinj hρW hAx hx2) hx hxK
  by_cases hy2 : ∃ l : F, l ^ 2 = (multiplierUnit Ay : F)
  · exact hinner y (psp4_mem_of_square θ hinj hρW hAy hy2) hy hyK
  have hz1 : x * y ≠ 1 := by
    intro h1
    have : y = x⁻¹ := eq_inv_of_mul_eq_one_right h1
    have hxx : x⁻¹ = x := by
      rw [inv_eq_iff_mul_eq_one, ← pow_two, ← hx]
      exact pow_orderOf_eq_one x
    exact hxy (this.trans hxx).symm
  have hz2 : orderOf (x * y) = 2 := by
    refine orderOf_eq_prime ?_ hz1
    have hx2' : x * x = 1 := by rw [← pow_two, ← hx]; exact pow_orderOf_eq_one x
    have hy2' : y * y = 1 := by rw [← pow_two, ← hy]; exact pow_orderOf_eq_one y
    calc (x * y) ^ 2 = x * y * (x * y) := pow_two _
      _ = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hcomm]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hx2', hy2', mul_one]
  have hρz : ρ (x * y) = conjAut 2 F (Ax * Ay) := by rw [map_mul, hAx, hAy, map_mul]
  have hmul : (multiplierUnit (Ax * Ay) : F) = (multiplierUnit Ax : F) * (multiplierUnit Ay : F) := by
    have := congrArg (fun z : Fˣ => (z : F)) ((multiplier 2 F).map_mul Ax Ay)
    exact this
  have hsq : ∃ l : F, l ^ 2 = (multiplierUnit (Ax * Ay) : F) := by
    have h := isSquare_mul_of_not_isSquare' (a := (multiplierUnit Ax : F))
      (b := (multiplierUnit Ay : F)) (fun ⟨l, hl⟩ => hx2 ⟨l, by rw [hl, sq]⟩)
      (fun ⟨l, hl⟩ => hy2 ⟨l, by rw [hl, sq]⟩)
    obtain ⟨l, hl⟩ := h
    exact ⟨l, by rw [hmul, hl, sq]⟩
  exact hinner (x * y) (psp4_mem_of_square θ hinj hρW hρz hsq) hz2
    (Subgroup.mul_mem _ hxK hyK)

end Sp4Main

theorem stated_of_lieModel_PSp {S : Type} [Group S] {n p f : ℕ} (h : LieModel S .PSp n p f) :
    StatedClassicalModel S .PSp n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)

variable {N : Type} [Group N] [Finite N] {L K Q : Subgroup N}

theorem ivk73_sp4 (p f : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    Ivk73Empty (fun X _ => LieModel X .PSp 2 p f) := by
  intro N _ _ L K Q h hm
  obtain ⟨x, hxQ, y, hyQ, hx, hy, hxy, hcomm⟩ :=
    C3.Layer1.U1a.exists_commuting_involutions h.Q_rank
  have := h.normal
  have hodd := odd_center_K h.kbar_cases
  obtain ⟨-, F, _, _, hF, ⟨e₀⟩⟩ := stated_of_lieModel_PSp hm
  obtain ⟨V, hVK, -, hVc⟩ := h.exists_V hodd
  have hev : 2 ∣ Nat.card K :=
    (show 2 ∣ 4 by norm_num).trans (hVc ▸ Subgroup.card_dvd_of_le hVK)
  exact psp4_core h.centralizer_eq_bot h.K_le h.exists_noncomm h.simple hp hp2 hf hF
    h.smallSource hodd hev e₀ hx hy hxy hcomm (h.Q_sylow.le hxQ) (h.Q_sylow.le hyQ) h.terminal

end CFSG.GH74.GLS.IVK
