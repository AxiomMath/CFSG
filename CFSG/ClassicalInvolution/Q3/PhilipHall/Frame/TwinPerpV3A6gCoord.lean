module

public import CFSG.ClassicalInvolution.Q3.TL3T34

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6g

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TC.Thin
open scoped Matrix

@[expose] def sh (b : Fin 3 → ZMod 2) (f : Fin 8 → ZMod 2) : Fin 8 → ZMod 2 :=
  fun i => f (binIdx (bin i + b))

theorem sh_apply (b f i) : sh b f i = f (binIdx (bin i + b)) := rfl

@[expose] noncomputable def tl (b : Fin 3 → ZMod 2) : AEQ 8 := mkQ 8 (ofPerm (aperm 1 b))

theorem permBar_tl (b) : permBar 8 (tl b) = aperm 1 b := permBar_mkQ _

theorem aperm_one_mul (b c : Fin 3 → ZMod 2) : aperm 1 b * aperm 1 c = aperm 1 (b + c) := by
  rw [aperm_mul, mul_one, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec, add_comm]

theorem tl_mul (b c) : tl b * tl c = tl (b + c) := by
  unfold tl
  rw [← map_mul, ofPerm_mul, aperm_one_mul]

theorem tl_zero : tl 0 = 1 := by
  unfold tl
  rw [aperm_one_zero, ofPerm_one, map_one]

theorem actV_aperm_one (b f) : actV (aperm 1 b) f = sh b f := by
  funext i
  show f ((aperm 1 b).symm i) = _
  rw [aperm_one_symm_apply]
  rfl

theorem tl_conj_vbar (b g) : tl b * vbar 8 g * (tl b)⁻¹ = vbar 8 (sh b g) := by
  rw [conj_vbar (permBar_tl b), actV_aperm_one]

theorem tl_inv (b) : (tl b)⁻¹ = tl b := by
  apply inv_eq_of_mul_eq_one_right
  rw [tl_mul, two_smul_zero, tl_zero]

theorem vbar_inv (f) : (vbar 8 f)⁻¹ = vbar 8 f := by
  apply inv_eq_of_mul_eq_one_right
  rw [← vbar_add]
  have : f + f = 0 := by funext i; exact zmod_two_add_self _
  rw [this, vbar_zero]

@[expose] noncomputable def E8 (f : Fin 8 → ZMod 2) (b : Fin 3 → ZMod 2) : AEQ 8 := vbar 8 f * tl b

theorem E8_mul (f g b c) : E8 f b * E8 g c = E8 (f + sh b g) (b + c) := by
  unfold E8
  calc vbar 8 f * tl b * (vbar 8 g * tl c)
      = vbar 8 f * (tl b * vbar 8 g * (tl b)⁻¹) * (tl b * tl c) := by group
    _ = vbar 8 f * vbar 8 (sh b g) * tl (b + c) := by rw [tl_conj_vbar, tl_mul]
    _ = vbar 8 (f + sh b g) * tl (b + c) := by rw [← vbar_add]

theorem E8_zero : E8 0 0 = 1 := by
  unfold E8
  rw [vbar_zero, tl_zero, one_mul]

theorem E8_inv (f b) : (E8 f b)⁻¹ = E8 (sh b f) b := by
  unfold E8
  rw [mul_inv_rev, tl_inv, vbar_inv]
  calc tl b * vbar 8 f = tl b * vbar 8 f * (tl b)⁻¹ * tl b := by group
    _ = vbar 8 (sh b f) * tl b := by rw [tl_conj_vbar]

theorem permBar_E8 (f b) : permBar 8 (E8 f b) = aperm 1 b := by
  unfold E8
  rw [map_mul, permBar_vbar, permBar_tl, one_mul]

theorem E8_eq_iff (f g b c) : E8 f b = E8 g c ↔ b = c ∧ ModPi f g := by
  constructor
  · intro h
    have hb : aperm 1 b = aperm 1 c := by
      rw [← permBar_E8 f b, h, permBar_E8]
    obtain ⟨-, hbc⟩ := aperm_inj hb
    subst hbc
    refine ⟨rfl, ?_⟩
    unfold E8 at h
    exact vbar_eq_iff.mp (mul_right_cancel h)
  · rintro ⟨rfl, h⟩
    unfold E8
    rw [vbar_eq_iff.mpr h]

theorem E8_sq_iff (f b) : E8 f b * E8 f b = 1 ↔ ModPi (f + sh b f) 0 := by
  rw [E8_mul, ← E8_zero, E8_eq_iff]
  constructor
  · rintro ⟨-, h⟩; exact h
  · intro h; exact ⟨by rw [two_smul_zero], h⟩

@[expose] def aff (a : Fin 3 → ZMod 2) (c : ZMod 2) : Fin 8 → ZMod 2 := fun i => a ⬝ᵥ bin i + c

@[expose] def dd (b : Fin 3 → ZMod 2) : Fin 8 → ZMod 2 :=
  fun i => (if i = 0 then 1 else 0) + (if i = binIdx b then 1 else 0)

@[expose] def AffP (f : Fin 8 → ZMod 2) : Prop := ∃ a c, f = aff a c

@[expose] def EvF (f : Fin 8 → ZMod 2) : Prop := ∑ i, f i = 0

instance (f : Fin 8 → ZMod 2) : Decidable (AffP f) := inferInstanceAs (Decidable (∃ a c, f = aff a c))
instance (f : Fin 8 → ZMod 2) : Decidable (EvF f) := inferInstanceAs (Decidable (∑ i, f i = 0))
instance (f g : Fin 8 → ZMod 2) : Decidable (ModPi f g) := inferInstanceAs (Decidable (_ ∨ _))

theorem aff_even : ∀ a c, EvF (aff a c) := by decide +kernel
theorem dd_even : ∀ b, EvF (dd b) := by decide +kernel
theorem affP_add_aux : ∀ a c a' c', AffP (aff a c + aff a' c') := by decide +kernel
theorem affP_sh_aux : ∀ a c b, AffP (sh b (aff a c)) := by decide +kernel
theorem dd_cocycle : ∀ b c i, dd (b + c) i = dd b i + dd c (binIdx (bin i + b)) := by decide +kernel
theorem dd_sh_self : ∀ b i, dd b (binIdx (bin i + b)) = dd b i := by decide +kernel
theorem modPi_affP_aux : ∀ a c f, ModPi f (aff a c) → AffP f := by decide +kernel
theorem dd_affP : ∀ b, AffP (dd b) → b = 0 := by decide +kernel
theorem dd_zero : dd 0 = 0 := by decide +kernel
theorem aff_zero : aff 0 0 = 0 := by decide +kernel

theorem AffP.zero : AffP 0 := ⟨0, 0, aff_zero.symm⟩

theorem AffP.add {f g : Fin 8 → ZMod 2} (hf : AffP f) (hg : AffP g) : AffP (f + g) := by
  obtain ⟨a, c, rfl⟩ := hf
  obtain ⟨a', c', rfl⟩ := hg
  exact affP_add_aux a c a' c'

theorem AffP.sh {f : Fin 8 → ZMod 2} (hf : AffP f) (b : Fin 3 → ZMod 2) : AffP (sh b f) := by
  obtain ⟨a, c, rfl⟩ := hf
  exact affP_sh_aux a c b

theorem AffP.even {f : Fin 8 → ZMod 2} (hf : AffP f) : EvF f := by
  obtain ⟨a, c, rfl⟩ := hf
  exact aff_even a c

theorem AffP.of_modPi {f g : Fin 8 → ZMod 2} (hg : AffP g) (h : ModPi f g) : AffP f := by
  obtain ⟨a, c, rfl⟩ := hg
  exact modPi_affP_aux a c f h

theorem EvF.add {f g : Fin 8 → ZMod 2} (hf : EvF f) (hg : EvF g) : EvF (f + g) := by
  unfold EvF at *
  simp only [Pi.add_apply]
  rw [Finset.sum_add_distrib, hf, hg, add_zero]

theorem EvF.sh {f : Fin 8 → ZMod 2} (hf : EvF f) (b : Fin 3 → ZMod 2) : EvF (sh b f) := by
  unfold EvF at *
  have := sum_perm_apply (aperm 1 b).symm f
  rw [← hf]
  convert this using 2 with i
  show f (binIdx (bin i + b)) = f ((aperm 1 b).symm.symm i)
  rw [Equiv.symm_symm, aperm_apply]
  unfold aapply
  rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

theorem EvF.zero : EvF 0 := by decide +kernel

theorem inv_class : ∀ f : Fin 8 → ZMod 2, EvF f → ∀ b : Fin 3 → ZMod 2, ModPi (f + sh b f) 0 →
    (b = 0 ∨ AffP f ∨ AffP (f + dd b)) := by
  decide +kernel

theorem AffP.const (c : ZMod 2) : AffP (fun _ => c) := ⟨0, c, by funext i; simp [aff]⟩

theorem AffP.cancel {f g : Fin 8 → ZMod 2} (hf : AffP f) (hfg : AffP (f + g)) : AffP g := by
  have : g = f + (f + g) := by
    funext i
    simp only [Pi.add_apply]
    rw [← add_assoc, zmod_two_add_self, zero_add]
  rw [this]
  exact hf.add hfg

@[expose] def mkSub (P : (Fin 8 → ZMod 2) → (Fin 3 → ZMod 2) → Prop) (h0 : P 0 0)
    (hmul : ∀ f g b c, EvF f → EvF g → P f b → P g c → P (f + sh b g) (b + c))
    (hinv : ∀ f b, EvF f → P f b → P (sh b f) b) : Subgroup (AEQ 8) where
  carrier := {x | ∃ f b, EvF f ∧ P f b ∧ x = E8 f b}
  mul_mem' := by
    rintro _ _ ⟨f, b, hf, hP, rfl⟩ ⟨g, c, hg, hQ, rfl⟩
    exact ⟨f + sh b g, b + c, hf.add (hg.sh b), hmul f g b c hf hg hP hQ, E8_mul f g b c⟩
  one_mem' := ⟨0, 0, EvF.zero, h0, E8_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨f, b, hf, hP, rfl⟩
    exact ⟨sh b f, b, hf.sh b, hinv f b hf hP, E8_inv f b⟩

theorem sh_dd_self (b f) : sh b f + dd b = sh b (f + dd b) := by
  funext i
  simp only [Pi.add_apply, sh_apply]
  rw [dd_sh_self]

@[expose] def AE : Subgroup (AEQ 8) :=
  mkSub (fun _ b => b = 0) rfl (fun _ _ _ _ _ _ hb hc => by rw [hb, hc, add_zero])
    (fun _ _ _ hb => hb)

@[expose] def AT : Subgroup (AEQ 8) :=
  mkSub (fun f _ => AffP f) AffP.zero (fun f g b c _ _ hf hg => hf.add (hg.sh b))
    (fun f b _ hf => hf.sh b)

theorem PD_mul {f g : Fin 8 → ZMod 2} {b c : Fin 3 → ZMod 2} (hf : AffP (f + dd b))
    (hg : AffP (g + dd c)) : AffP ((f + sh b g) + dd (b + c)) := by
  have e : (f + sh b g) + dd (b + c) = (f + dd b) + sh b (g + dd c) := by
    funext i
    simp only [Pi.add_apply, sh_apply]
    rw [dd_cocycle b c i]
    ring
  rw [e]
  exact hf.add (hg.sh b)

theorem PD_inv {f : Fin 8 → ZMod 2} {b : Fin 3 → ZMod 2} (hf : AffP (f + dd b)) :
    AffP (sh b f + dd b) := by
  rw [sh_dd_self]
  exact hf.sh b

@[expose] def AD : Subgroup (AEQ 8) :=
  mkSub (fun f b => AffP (f + dd b)) (by rw [dd_zero, add_zero]; exact AffP.zero)
    (fun f g b c _ _ hf hg => PD_mul hf hg) (fun f b _ hf => PD_inv hf)

@[expose] def E3p : Subgroup (AEQ 8) :=
  mkSub (fun f b => b = 0 ∧ AffP f) ⟨rfl, AffP.zero⟩
    (fun f g b c _ _ hf hg => ⟨by rw [hf.1, hg.1, add_zero], hf.2.add (hg.2.sh b)⟩)
    (fun f b _ hf => ⟨hf.1, hf.2.sh b⟩)

theorem mem_AE {x : AEQ 8} : x ∈ AE ↔ ∃ f, EvF f ∧ x = E8 f 0 := by
  constructor
  · rintro ⟨f, b, hf, hb, rfl⟩
    exact ⟨f, hf, by rw [show b = 0 from hb]⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f, 0, hf, rfl, rfl⟩

theorem mem_AT {x : AEQ 8} : x ∈ AT ↔ ∃ f b, AffP f ∧ x = E8 f b := by
  constructor
  · rintro ⟨f, b, hf, hP, rfl⟩
    exact ⟨f, b, hP, rfl⟩
  · rintro ⟨f, b, hP, rfl⟩
    exact ⟨f, b, hP.even, hP, rfl⟩

theorem mem_AD {x : AEQ 8} : x ∈ AD ↔ ∃ f b, AffP (f + dd b) ∧ x = E8 f b := by
  constructor
  · rintro ⟨f, b, hf, hP, rfl⟩
    exact ⟨f, b, hP, rfl⟩
  · rintro ⟨f, b, hP, rfl⟩
    refine ⟨f, b, ?_, hP, rfl⟩
    have h1 := hP.even
    have h2 := (dd_even b)
    unfold EvF at *
    simp only [Pi.add_apply, Finset.sum_add_distrib] at h1
    rw [h2, add_zero] at h1
    exact h1

theorem mem_E3p {x : AEQ 8} : x ∈ E3p ↔ ∃ f, AffP f ∧ x = E8 f 0 := by
  constructor
  · rintro ⟨f, b, hf, hP, rfl⟩
    exact ⟨f, hP.2, by rw [hP.1]⟩
  · rintro ⟨f, hP, rfl⟩
    exact ⟨f, 0, hP.even, ⟨rfl, hP⟩, rfl⟩

theorem E3p_le_AT : E3p ≤ AT := by
  rintro x hx
  obtain ⟨f, hf, rfl⟩ := mem_E3p.mp hx
  exact mem_AT.mpr ⟨f, 0, hf, rfl⟩

theorem E3p_le_AD : E3p ≤ AD := by
  rintro x hx
  obtain ⟨f, hf, rfl⟩ := mem_E3p.mp hx
  refine mem_AD.mpr ⟨f, 0, ?_, rfl⟩
  rw [dd_zero, add_zero]
  exact hf

theorem AE_inf_AT_le : AE ⊓ AT ≤ E3p := by
  rintro x ⟨hE, hT⟩
  obtain ⟨f, hf, rfl⟩ := mem_AE.mp hE
  obtain ⟨g, c, hg, he⟩ := mem_AT.mp hT
  obtain ⟨-, hm⟩ := (E8_eq_iff _ _ _ _).mp he
  exact mem_E3p.mpr ⟨f, hg.of_modPi hm, rfl⟩

theorem AE_inf_AD_le : AE ⊓ AD ≤ E3p := by
  rintro x ⟨hE, hD⟩
  obtain ⟨f, hf, rfl⟩ := mem_AE.mp hE
  obtain ⟨g, c, hg, he⟩ := mem_AD.mp hD
  obtain ⟨hc, hm⟩ := (E8_eq_iff _ _ _ _).mp he
  rw [← hc, dd_zero, add_zero] at hg
  exact mem_E3p.mpr ⟨f, hg.of_modPi hm, rfl⟩

theorem AT_inf_AD_le : AT ⊓ AD ≤ E3p := by
  rintro x ⟨hT, hD⟩
  obtain ⟨f, b, hf, rfl⟩ := mem_AT.mp hT
  obtain ⟨g, c, hg, he⟩ := mem_AD.mp hD
  obtain ⟨hc, hm⟩ := (E8_eq_iff _ _ _ _).mp he
  subst hc
  have hfb : AffP (f + dd b) := by
    rcases hm with rfl | rfl
    · exact hg
    · have : (g + 1) + dd b = (g + dd b) + fun _ => (1 : ZMod 2) := by
        funext i
        simp only [Pi.add_apply, Pi.one_apply]
        ring
      rw [this]
      exact hg.add (AffP.const 1)
  have hdd := hf.cancel hfb
  have hb := dd_affP b hdd
  subst hb
  exact mem_E3p.mpr ⟨f, hf, rfl⟩

theorem affP_ind : ∀ δ ∈ affinePlanes, AffP (ind δ) := by decide +kernel

theorem zBar_mem_E3p {δ : Finset (Fin 8)} (hδ : δ ∈ affinePlanes) (h : δ.card = 4) :
    zBar δ h ∈ E3p := by
  rw [zBar_eq_vbar]
  have : vbar 8 (ind δ) = E8 (ind δ) 0 := by
    unfold E8
    rw [tl_zero, mul_one]
  rw [this]
  exact mem_E3p.mpr ⟨_, affP_ind δ hδ, rfl⟩

theorem card_of_param {S : Subgroup (AEQ 8)} {α : Type} [Fintype α] (par : α → AEQ 8)
    (hmem : ∀ a, par a ∈ S) (hinj : Function.Injective par) (hsurj : ∀ x ∈ S, ∃ a, par a = x) :
    Nat.card S = Fintype.card α := by
  have hb : Function.Bijective (fun a => (⟨par a, hmem a⟩ : S)) := by
    refine ⟨fun a b h => hinj (congrArg Subtype.val h), fun ⟨x, hx⟩ => ?_⟩
    obtain ⟨a, ha⟩ := hsurj x hx
    exact ⟨a, Subtype.ext ha⟩
  rw [← Nat.card_eq_fintype_card]
  exact (Nat.card_congr (Equiv.ofBijective _ hb)).symm

theorem aff_modPi_inj : ∀ a a' : Fin 3 → ZMod 2, ModPi (aff a 0) (aff a' 0) → a = a' := by
  decide +kernel
theorem aff_modPi_zero : ∀ (a : Fin 3 → ZMod 2) (c : ZMod 2), ModPi (aff a c) (aff a 0) := by
  decide +kernel
theorem dd_aff_affP : ∀ (a b : Fin 3 → ZMod 2) (c : ZMod 2), AffP ((dd b + aff a c) + dd b) := by
  decide +kernel
theorem dd_aff_modPi_inj : ∀ (a a' b : Fin 3 → ZMod 2),
    ModPi (dd b + aff a 0) (dd b + aff a' 0) → a = a' := by decide +kernel
theorem dd_aff_modPi_zero : ∀ (a b : Fin 3 → ZMod 2) (c : ZMod 2),
    ModPi (dd b + aff a c) (dd b + aff a 0) := by decide +kernel

theorem card_E3p : Nat.card E3p = 8 := by
  rw [card_of_param (S := E3p) (fun a : Fin 3 → ZMod 2 => E8 (aff a 0) 0)
    (fun a => mem_E3p.mpr ⟨_, ⟨a, 0, rfl⟩, rfl⟩)
    (fun a a' h => aff_modPi_inj a a' ((E8_eq_iff _ _ _ _).mp h).2)
    (fun x hx => by
      obtain ⟨f, ⟨a, c, rfl⟩, rfl⟩ := mem_E3p.mp hx
      exact ⟨a, ((E8_eq_iff _ _ _ _).mpr ⟨rfl, aff_modPi_zero a c⟩).symm⟩)]
  simp [Fintype.card_fun]

theorem card_AT : Nat.card AT = 64 := by
  rw [card_of_param (S := AT) (fun p : (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2) => E8 (aff p.1 0) p.2)
    (fun p => mem_AT.mpr ⟨_, p.2, ⟨p.1, 0, rfl⟩, rfl⟩)
    (fun p q h => by
      obtain ⟨hb, hm⟩ := (E8_eq_iff _ _ _ _).mp h
      exact Prod.ext (aff_modPi_inj _ _ hm) hb)
    (fun x hx => by
      obtain ⟨f, b, ⟨a, c, rfl⟩, rfl⟩ := mem_AT.mp hx
      exact ⟨(a, b), ((E8_eq_iff _ _ _ _).mpr ⟨rfl, aff_modPi_zero a c⟩).symm⟩)]
  simp [Fintype.card_fun, Fintype.card_prod]

theorem card_AD : Nat.card AD = 64 := by
  rw [card_of_param (S := AD)
    (fun p : (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2) => E8 (dd p.2 + aff p.1 0) p.2)
    (fun p => mem_AD.mpr ⟨_, p.2, dd_aff_affP p.1 p.2 0, rfl⟩)
    (fun p q h => by
      obtain ⟨hb, hm⟩ := (E8_eq_iff _ _ _ _).mp h
      obtain ⟨p1, p2⟩ := p
      obtain ⟨q1, q2⟩ := q
      simp only at hb hm
      subst hb
      exact Prod.ext (dd_aff_modPi_inj _ _ _ hm) rfl)
    (fun x hx => by
      obtain ⟨f, b, ⟨a, c, hac⟩, rfl⟩ := mem_AD.mp hx
      have hf : f = dd b + aff a c := by
        have : f = (f + dd b) + dd b := by
          funext i
          simp only [Pi.add_apply]
          rw [add_assoc, zmod_two_add_self, add_zero]
        rw [this, hac, add_comm]
      refine ⟨(a, b), ?_⟩
      show E8 (dd b + aff a 0) b = E8 f b
      rw [hf]
      exact ((E8_eq_iff _ _ _ _).mpr ⟨rfl, dd_aff_modPi_zero a b c⟩).symm)]
  simp [Fintype.card_fun, Fintype.card_prod]

@[expose] def repE (c : Fin 6 → ZMod 2) : Fin 8 → ZMod 2 :=
  ![0, c 0, c 1, c 2, c 3, c 4, c 5, c 0 + c 1 + c 2 + c 3 + c 4 + c 5]

theorem repE_even : ∀ c, EvF (repE c) := by decide +kernel
theorem repE_inj : ∀ c c', ModPi (repE c) (repE c') → c = c' := by decide +kernel
theorem repE_surj : ∀ f : Fin 8 → ZMod 2, EvF f →
    ModPi f (repE ![f 1 + f 0, f 2 + f 0, f 3 + f 0, f 4 + f 0, f 5 + f 0, f 6 + f 0]) := by
  decide +kernel

theorem card_AE : Nat.card AE = 64 := by
  rw [card_of_param (S := AE) (fun c : Fin 6 → ZMod 2 => E8 (repE c) 0)
    (fun c => mem_AE.mpr ⟨_, repE_even c, rfl⟩)
    (fun c c' h => repE_inj c c' ((E8_eq_iff _ _ _ _).mp h).2)
    (fun x hx => by
      obtain ⟨f, hf, rfl⟩ := mem_AE.mp hx
      exact ⟨![f 1 + f 0, f 2 + f 0, f 3 + f 0, f 4 + f 0, f 5 + f 0, f 6 + f 0],
        ((E8_eq_iff _ _ _ _).mpr ⟨rfl, repE_surj f hf⟩).symm⟩)]
  simp [Fintype.card_fun]

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6g
