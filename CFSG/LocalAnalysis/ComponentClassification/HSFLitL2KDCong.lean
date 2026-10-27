module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2KDFix
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2KCong

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit.L2KD

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer GorensteinWalter
open CFSG.ComponentClassification.AutL2Facts CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open L2K

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
variable {F : Type} [Field F] [Finite F]

theorem card_conj_z_modEq_kd (C : A.CaseKD) (S : Gens A) {κ : X} (Fr : Frame A F κ)
    (hzt : ∀ g ∈ centralizer ({t} : Set X), g * S.z * g⁻¹ ≠ t * S.z) :
    {b | ∃ g ∈ centralizer ({t} : Set X), g * S.z * g⁻¹ = b}.ncard ≡ 1 [MOD 4] := by
  classical
  set CX : Subgroup X := centralizer ({t} : Set X) with hCX
  set e := Fr.e with he
  have hzC : S.z ∈ CX := A.T_le_centralizer S.z_mem.1
  set a : PGammaL2 F := act A e S.z with ha
  set Y₀ : Subgroup CX := (centralizer ({a} : Set (PGammaL2 F))).comap (actC A e) with hY₀
  set Y : Subgroup X := Y₀.map CX.subtype with hY
  have hmemY : ∀ g, g ∈ Y ↔ g ∈ CX ∧ act A e g * a = a * act A e g := by
    intro g
    constructor
    · rintro ⟨h, hh, rfl⟩
      refine ⟨h.2, ?_⟩
      change act A e (h : X) * a = a * act A e (h : X)
      rw [act_of_mem e h.2]
      exact mem_centralizer_singleton_iff.mp hh
    · rintro ⟨hg, hcomm⟩
      refine ⟨⟨g, hg⟩, ?_, rfl⟩
      change actC A e ⟨g, hg⟩ ∈ centralizer ({a} : Set (PGammaL2 F))
      rw [mem_centralizer_singleton_iff, ← act_of_mem e hg]
      exact hcomm
  have hYC : Y ≤ CX := map_subtype_le _
  have hCzY : CX ⊓ centralizer ({S.z} : Set X) ≤ Y := by
    intro g hg
    obtain ⟨hgC, hgz⟩ := mem_inf.mp hg
    rw [hmemY]
    refine ⟨hgC, ?_⟩
    rw [ha, ← act_mul e hgC hzC, ← act_mul e hzC hgC, mem_centralizer_singleton_iff.mp hgz]
  set w₀ := rho e S.z with hw₀
  have haw₀ : a = incl F w₀ := act_of_mem_L e S.z_mem.2
  have hw₀I : BenderSuzuki.PFAppendixIII.IsInvolution w₀ :=
    ⟨fun h => S.z_ne_one (rho_eq_one e S.z_mem h), by
      rw [hw₀, ← rho_pow e S.z_mem.2, S.z_sq, rho_one]⟩
  have hset : {y | ∃ g ∈ (actC A e).range, g * a * g⁻¹ = y} =
      incl F '' {w : PSL2 F | BenderSuzuki.PFAppendixIII.IsInvolution w} := by
    ext y
    constructor
    · rintro ⟨g, -, rfl⟩
      refine ⟨semilinearAction F g w₀, ⟨fun h => hw₀I.1 ?_, ?_⟩, ?_⟩
      · exact (semilinearAction F g).injective (h.trans (map_one _).symm)
      · rw [← map_pow, hw₀I.2, map_one]
      · rw [haw₀, conj_incl]
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨c, hc⟩ := psl2_involutions_conjugate_of_odd_prime_power F Fr.odd w₀ w hw₀I hw
      obtain ⟨⟨l, hl⟩, hlc⟩ := QuotientGroup.mk_surjective (e.symm c)
      have hrl : rho e l = c := by rw [rho_of_mem e hl, hlc, MulEquiv.apply_symm_apply]
      refine ⟨actC A e ⟨l, L_le_C (A := A) hl⟩, ⟨_, rfl⟩, ?_⟩
      rw [← act_of_mem e (L_le_C (A := A) hl), act_of_mem_L e hl, hrl, haw₀, ← map_inv,
        ← map_mul, ← map_mul, hc]
  have hYidx : Y.relIndex CX =
      {w : PSL2 F | BenderSuzuki.PFAppendixIII.IsInvolution w}.ncard := by
    rw [relIndex, hY]
    change ((Y₀.map CX.subtype).comap CX.subtype).index = _
    rw [comap_map_eq_self_of_injective (subtype_injective CX), hY₀, Subgroup.index_comap,
      ← inf_relIndex_right, inf_comm, relIndex_inf_centralizer_eq_ncard, hset,
      Set.ncard_image_of_injective _ (incl_injective F)]
  have hK₀ := Fr.K₀_odd
  have hr : Odd (Nat.card Fr.K₀) := by
    obtain ⟨p, n, -, hpodd, -, hc⟩ := hK₀
    rw [hc]
    exact hpodd.pow
  have hr3 : 3 ≤ Nat.card Fr.K₀ := by
    obtain ⟨p, n, hp, hpodd, hn, hc⟩ := hK₀
    have h2 := hp.two_le
    have hp2 : p ≠ 2 := fun h => by rw [h] at hpodd; exact absurd hpodd (by decide)
    rw [hc]
    calc 3 ≤ p := by omega
      _ ≤ p ^ n := Nat.le_self_pow (by omega) p
  have hYmod : Y.relIndex CX ≡ 1 [MOD 4] := by
    rw [hYidx]
    exact ncard_involutions_modEq Fr.odd hr Fr.card_F hr3
  have hmul := relIndex_mul_relIndex (CX ⊓ centralizer ({S.z} : Set X)) Y CX hCzY hYC
  have hinf : (CX ⊓ centralizer ({S.z} : Set X)).relIndex Y =
      (Y ⊓ centralizer ({S.z} : Set X)).relIndex Y := by
    rw [← inf_relIndex_right (CX ⊓ centralizer ({S.z} : Set X)) Y,
      ← inf_relIndex_right (Y ⊓ centralizer ({S.z} : Set X)) Y]
    congr 1
    apply le_antisymm
    · exact le_inf (le_inf inf_le_right (inf_le_left.trans inf_le_right)) inf_le_right
    · exact le_inf (le_inf (inf_le_left.trans (inf_le_left.trans hYC))
        (inf_le_left.trans inf_le_right)) inf_le_right
  rw [relIndex_inf_centralizer_eq_ncard, hinf, relIndex_inf_centralizer_eq_ncard] at hmul
  rw [← hmul]
  set Fz : Set X := {y | ∃ g ∈ Y, g * S.z * g⁻¹ = y} with hFz
  have hxC := A.T_le_centralizer S.x₀_mem.1
  have hxY : S.x₀ ∈ Y := by
    rw [hmemY]
    refine ⟨hxC, ?_⟩
    rw [ha, Gens.z, act_pow e hxC]
    exact (Commute.self_pow _ 2).eq
  have hFx : ∀ f ∈ Fz, S.x₀ * f * S.x₀⁻¹ ∈ Fz := by
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨S.x₀ * g, mul_mem hxY hg, by group⟩
  have hFx' : ∀ f ∈ Fz, S.x₀⁻¹ * f * S.x₀ ∈ Fz := by
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨S.x₀⁻¹ * g, mul_mem (inv_mem hxY) hg, by group⟩
  have : Fintype Fz := Fintype.ofFinite Fz
  let π : Perm Fz :=
    { toFun := fun f => ⟨S.x₀ * f * S.x₀⁻¹, hFx f f.2⟩
      invFun := fun f => ⟨S.x₀⁻¹ * f * S.x₀, hFx' f f.2⟩
      left_inv := fun f => Subtype.ext (by simp [mul_assoc])
      right_inv := fun f => Subtype.ext (by simp [mul_assoc]) }
  have hπpow : ∀ (n : ℕ) (f : Fz), ((π ^ n) f : X) = S.x₀ ^ n * f * (S.x₀ ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro f; simp
    | succ n ih =>
      intro f
      rw [pow_succ', Perm.mul_apply]
      change S.x₀ * ((π ^ n) f : X) * S.x₀⁻¹ = _
      rw [ih, pow_succ']
      group
  have hπ4 : π ^ 4 = 1 := by
    ext f
    rw [hπpow, S.x₀_pow_four]
    simp
  have hfix : Fintype.card (Function.fixedPoints ⇑(π ^ 2)) = 1 := by
    rw [Fintype.card_eq_one_iff]
    have hzF : S.z ∈ Fz := ⟨1, one_mem _, by group⟩
    have hzfix : (π ^ 2) ⟨S.z, hzF⟩ = ⟨S.z, hzF⟩ := by
      apply Subtype.ext
      rw [hπpow]
      change S.x₀ ^ 2 * S.x₀ ^ 2 * (S.x₀ ^ 2)⁻¹ = S.x₀ ^ 2
      group
    refine ⟨⟨⟨S.z, hzF⟩, hzfix⟩, fun f => ?_⟩
    obtain ⟨⟨f, ⟨g, hg, rfl⟩⟩, hf⟩ := f
    apply Subtype.ext
    apply Subtype.ext
    change g * S.z * g⁻¹ = S.z
    have hf' := congrArg Subtype.val (show (π ^ 2) _ = _ from hf)
    rw [hπpow] at hf'
    change S.z * (g * S.z * g⁻¹) * S.z⁻¹ = g * S.z * g⁻¹ at hf'
    obtain ⟨hgC, hgcomm⟩ := (hmemY g).mp hg
    set f := g * S.z * g⁻¹ with hfdef
    have hfC : f ∈ CX := mul_mem (mul_mem hgC hzC) (inv_mem hgC)
    have hz2 : S.z ^ 2 = 1 := S.z_sq
    have hzinv : S.z⁻¹ = S.z := by rw [inv_eq_iff_mul_eq_one, ← pow_two, hz2]
    have hfz : S.z * f = f * S.z := by
      calc S.z * f = S.z * f * S.z⁻¹ * S.z := by group
        _ = f * S.z := by rw [hf']
    have hf2 : f ^ 2 = 1 := by rw [hfdef, conj_pow, hz2]; group
    have hact : act A e (S.z * f) = 1 := by
      rw [act_mul e hzC hfC, hfdef, act_conj e hgC hzC, ← ha, ← mul_assoc, ← mul_assoc,
        ← hgcomm]
      calc act A e g * a * a * (act A e g)⁻¹ = act A e g * (a * a) * (act A e g)⁻¹ := by
            group
        _ = 1 := by
          rw [ha, ← act_mul e hzC hzC, ← pow_two, hz2, act_one]
          group
    have hsq : (S.z * f) ^ 2 = 1 := by
      rw [(show Commute S.z f from hfz).mul_pow, hz2, hf2, one_mul]
    rcases eq_one_or_eq_t_of_sq C (mul_mem hzC hfC) ((act_eq_one_iff e (mul_mem hzC hfC)).mp hact)
      hsq with h | h
    · calc f = S.z⁻¹ * (S.z * f) := by group
        _ = S.z := by rw [h, mul_one, hzinv]
    · exfalso
      apply hzt g hgC
      calc g * S.z * g⁻¹ = S.z⁻¹ * (S.z * f) := by rw [hfdef]; group
        _ = t * S.z := by
          rw [h, hzinv]
          exact (commute_t_of_mem_C hzC)
  have hF1 := card_modEq_card_fixedPoints_sq π hπ4
  rw [hfix] at hF1
  have hFc : Fz.ncard = Fintype.card Fz := by
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  rw [hFc]
  calc Fintype.card Fz * Y.relIndex CX ≡ 1 * 1 [MOD 4] := Nat.ModEq.mul hF1.symm hYmod
    _ = 1 := by norm_num


variable (C : A.CaseKD)

theorem act_d_sq (e : L ⧸ pPrimeCore 2 L ≃* PSL2 F) : act A e C.d ^ 2 = 1 := by
  have hd2T : C.d ^ 2 ∈ A.T := pow_mem C.d_mem 2
  have hK : C.d ^ 2 ∈ A.K := by
    rw [← ψX_eq_one_iff hd2T, ψX_pow C.d_mem, ψX_d C, d8_sq]
  rw [← act_pow e (d_mem_C C), (act_eq_one_iff e (pow_mem (d_mem_C C) 2)).mpr hK.2]

theorem act_d_ne_one (e : L ⧸ pPrimeCore 2 L ≃* PSL2 F) : act A e C.d ≠ 1 := by
  intro h
  have hK : C.d ∈ A.K := Subgroup.mem_inf.mpr ⟨C.d_mem, (act_eq_one_iff e (d_mem_C C)).mp h⟩
  rw [← ψX_eq_one_iff C.d_mem, ψX_d C] at hK
  exact d8_ne_one hK

theorem not_sqLeft_act_d (S : Gens A) (Fr : Frame A F C.k) (e : L ⧸ pPrimeCore 2 L ≃* PSL2 F) :
    ¬ SqLeft (act A e C.d) := by
  intro hS
  rw [sqLeft_act_iff Fr.e e] at hS
  obtain ⟨c, -, hdk⟩ := d_conj_k C S
  exact S.z_ne_one (Frame.eq_one_of_conj_sq Fr (d_mem_C C) hS (Fr.z_mem_V S) c hdk)

theorem right_act_d (S : Gens A) (Fr : Frame A F C.k) (e : L ⧸ pPrimeCore 2 L ≃* PSL2 F) :
    (act A e C.d).right = 1 := by
  by_contra h
  exact not_sqLeft_act_d C S Fr e
    (sqLeft_of_involution Fr.odd (orderOf_eq_prime (act_d_sq C e) (act_d_ne_one C e)) h)

theorem inl_mem_range (S : Gens A) (Fr : Frame A F C.k) (e : L ⧸ pPrimeCore 2 L ≃* PSL2 F)
    (p : PGL2 F) : (SemidirectProduct.inl p : PGammaL2 F) ∈ (actC A e).range := by
  have hpsl : ∀ y : PGammaL2 F, y.right = 1 → SqLeft y → y ∈ (actC A e).range := by
    intro y hy1 hyS
    obtain ⟨s, hs⟩ := (mem_pslRange_iff y).mpr ⟨hy1, hyS⟩
    obtain ⟨⟨l, hl⟩, hlc⟩ := QuotientGroup.mk_surjective (e.symm s)
    have hrl : rho e l = s := by rw [rho_of_mem e hl, hlc, MulEquiv.apply_symm_apply]
    refine ⟨⟨l, L_le_C (A := A) hl⟩, ?_⟩
    rw [← act_of_mem e (L_le_C (A := A) hl), act_of_mem_L e hl, hrl, ← hs]
    rfl
  by_cases hp : SqLeft (SemidirectProduct.inl p : PGammaL2 F)
  · exact hpsl _ (by simp) hp
  · have hdC := d_mem_C C
    have h1 : (SemidirectProduct.inl p : PGammaL2 F) * (act A e C.d)⁻¹ ∈ (actC A e).range := by
      refine hpsl _ ?_ ?_
      · rw [SemidirectProduct.mul_right, SemidirectProduct.inv_right, right_act_d C S Fr e]
        simp
      · rw [sqLeft_mul, sqLeft_inv]
        exact iff_of_false hp (not_sqLeft_act_d C S Fr e)
    have h2 : act A e C.d ∈ (actC A e).range := ⟨⟨C.d, hdC⟩, (act_of_mem e hdC).symm⟩
    have := mul_mem h1 h2
    rwa [inv_mul_cancel_right] at this

@[expose] def fstHom : Multiplicative (ZMod 2 × ZMod 2) →* Multiplicative (ZMod 2) where
  toFun x := Multiplicative.ofAdd (Multiplicative.toAdd x).1
  map_one' := rfl
  map_mul' _ _ := rfl

omit [Finite X] in
variable (A) in
@[expose] def dbitT : A.T →* Multiplicative (ZMod 2) := fstHom.comp (type8.comp (L2Data.ψH A))

omit [Finite X] in
theorem dbitT_apply {g : X} (hg : g ∈ A.T) {u : (ZMod 8)ˣ} {b : ZMod 8}
    (hψ : ψX A g = aff8 u b) : dbitT A ⟨g, hg⟩ = Multiplicative.ofAdd (dbit8 b) := by
  have e1 : (L2Data.ψH A ⟨g, hg⟩) = ⟨aff8 u b, aff8_mem_H8 u b⟩ := by
    apply Subtype.ext
    rw [L2Data.ψH_coe, ← ψX_of_mem hg, hψ]
  change fstHom (type8 (L2Data.ψH A ⟨g, hg⟩)) = _
  rw [e1, type8_aff8]
  rfl

variable (A) in
@[expose] def TE : Subgroup X := (dbitT A).ker.map A.T.subtype

omit [Finite X] in
theorem mem_TE {g : X} : g ∈ TE A ↔ ∃ hg : g ∈ A.T, dbitT A ⟨g, hg⟩ = 1 := by
  constructor
  · rintro ⟨g', hg', rfl⟩
    exact ⟨g'.2, hg'⟩
  · rintro ⟨hg, h1⟩
    exact ⟨⟨g, hg⟩, h1, rfl⟩

omit [Finite X] in
include C in
theorem card_T_eq_two_mul_card_TE : Nat.card A.T = 2 * Nat.card (TE A) := by
  have hd : dbitT A ⟨C.d, C.d_mem⟩ = Multiplicative.ofAdd 1 := by
    rw [dbitT_apply C.d_mem (ψX_d C)]
    rfl
  have hrange : (dbitT A).range = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : ∀ y : Multiplicative (ZMod 2), y = 1 ∨ y = Multiplicative.ofAdd 1 := by decide
    rcases hx x with rfl | rfl
    · exact one_mem _
    · exact ⟨_, hd⟩
  have hidx : (dbitT A).ker.index = 2 := by
    rw [Subgroup.index_ker, hrange, card_top, Nat.card_eq_fintype_card]
    rfl
  have h := (dbitT A).ker.card_mul_index
  rw [hidx] at h
  have hTE : Nat.card (TE A) = Nat.card (dbitT A).ker :=
    card_map_of_injective (subtype_injective _)
  rw [hTE, ← h, mul_comm]

theorem eq_of_mem_TE {g : X} (hg : g ∈ TE A) :
    ∃ r ∈ A.R, ∃ a e : ℕ, a < 2 ∧ e < 2 ∧ g = r * t ^ a * C.k ^ e := by
  obtain ⟨hgT, h1⟩ := mem_TE.mp hg
  obtain ⟨u, b, hub⟩ := ψX_mem_H8 hgT
  rw [dbitT_apply hgT hub.symm] at h1
  have hb : dbit8 b = 0 := by
    have := congrArg Multiplicative.toAdd h1
    simpa using this
  obtain ⟨r, hr, a, e, ha, he, hg', -⟩ := exists_eq_of_mem_T C hgT hub.symm hb
  exact ⟨r, hr, a, e, ha, he, hg'⟩

theorem index_k_eq {r N : ℕ} (hr : Odd r) (hr3 : 3 ≤ r)
    (h : N * (r * (r ^ 2 - 1)) = r ^ 2 * ((r ^ 2) ^ 2 - 1)) : ∃ m, Odd m ∧ N = 2 * m := by
  obtain ⟨s, rfl⟩ := hr
  have hs : 1 ≤ s := by omega
  have h1 : (2 * s + 1) ^ 2 - 1 = 4 * s * (s + 1) := by
    rw [Nat.sub_eq_iff_eq_add (by nlinarith)]
    ring
  have h2 : ((2 * s + 1) ^ 2) ^ 2 - 1 = 4 * s * (s + 1) * ((2 * s + 1) ^ 2 + 1) := by
    rw [Nat.sub_eq_iff_eq_add (by nlinarith)]
    ring
  rw [h1, h2] at h
  have hpos : 0 < (2 * s + 1) * (4 * s * (s + 1)) := by positivity
  have hN : N = (2 * s + 1) * ((2 * s + 1) ^ 2 + 1) := by
    have : N * ((2 * s + 1) * (4 * s * (s + 1))) =
        ((2 * s + 1) * ((2 * s + 1) ^ 2 + 1)) * ((2 * s + 1) * (4 * s * (s + 1))) := by
      rw [h]
      ring
    exact Nat.eq_of_mul_eq_mul_right hpos this
  refine ⟨(2 * s + 1) * (2 * (s * s + s) + 1), ?_, ?_⟩
  · exact Odd.mul ⟨s, rfl⟩ ⟨s * s + s, rfl⟩
  · rw [hN]
    ring

theorem relIndex_inl_centralizer_mul {κ : X} (Fr : Frame A F κ) :
    ((SemidirectProduct.inl : PGL2 F →* PGammaL2 F).range ⊓
      centralizer ({(SemidirectProduct.inr Fr.σ : PGammaL2 F)} : Set (PGammaL2 F))).relIndex
        (SemidirectProduct.inl : PGL2 F →* PGammaL2 F).range * Nat.card (PGL2 Fr.K₀) =
      Nat.card (PGL2 F) := by
  set I := (SemidirectProduct.inl : PGL2 F →* PGammaL2 F).range with hI
  set H := I ⊓ centralizer ({(SemidirectProduct.inr Fr.σ : PGammaL2 F)} : Set (PGammaL2 F))
    with hH
  have hHeq : H = (Glauberman.Dickson.h826_pglMap Fr.K₀.subtype).range.map
      (SemidirectProduct.inl : PGL2 F →* PGammaL2 F) := by
    ext x
    constructor
    · intro hx
      obtain ⟨⟨p, rfl⟩, hx⟩ := Subgroup.mem_inf.mp hx
      rw [mem_centralizer_singleton_iff] at hx
      refine ⟨p, mem_range_of_pgl2FieldAut_fixed Fr.mem_K₀ Fr.h90 Fr.σσ ?_, rfl⟩
      have h1 := SemidirectProduct.inl_aut (φ := pgl2FieldAut F) Fr.σ p
      rw [map_inv] at h1
      apply (SemidirectProduct.inl_injective (φ := pgl2FieldAut F))
      rw [h1, ← hx, mul_inv_cancel_right]
    · rintro ⟨p, ⟨y, rfl⟩, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨⟨_, rfl⟩, ?_⟩
      rw [mem_centralizer_singleton_iff]
      have h1 := SemidirectProduct.inl_aut (φ := pgl2FieldAut F) Fr.σ
        (Glauberman.Dickson.h826_pglMap Fr.K₀.subtype y)
      rw [pgl2FieldAut_pglMap Fr.mem_K₀, map_inv] at h1
      calc (SemidirectProduct.inl (Glauberman.Dickson.h826_pglMap Fr.K₀.subtype y) : PGammaL2 F) *
            SemidirectProduct.inr Fr.σ
          = SemidirectProduct.inr Fr.σ * SemidirectProduct.inl
              (Glauberman.Dickson.h826_pglMap Fr.K₀.subtype y) * (SemidirectProduct.inr Fr.σ)⁻¹ *
            SemidirectProduct.inr Fr.σ := by rw [← h1]
        _ = _ := by group
  have hcardH : Nat.card H = Nat.card (PGL2 Fr.K₀) := by
    rw [hHeq, card_map_of_injective SemidirectProduct.inl_injective,
      ← Nat.card_congr (MonoidHom.ofInjective
        (Glauberman.Dickson.h826_pglMap_injective _ Fr.K₀.subtype_injective)).toEquiv]
  have hcardI : Nat.card I = Nat.card (PGL2 F) :=
    (Nat.card_congr (MonoidHom.ofInjective SemidirectProduct.inl_injective).toEquiv).symm
  have h := relIndex_mul_card H I
  rw [inf_of_le_left (inf_le_left : H ≤ I), hcardH, hcardI] at h
  exact h

theorem factorization_eq_of_sandwich {P H N : ℕ} (hP : P = 2 ^ N.factorization 2) (hPH : P ∣ H)
    (hHN : H ∣ N) (hN : N ≠ 0) : P = 2 ^ H.factorization 2 := by
  have hH : H ≠ 0 := fun h => hN (Nat.eq_zero_of_zero_dvd (h ▸ hHN))
  have h3 : H.factorization 2 ≤ N.factorization 2 :=
    (Nat.factorization_le_iff_dvd hH hN).mpr hHN 2
  have h4 : N.factorization 2 ≤ H.factorization 2 := by
    rw [hP] at hPH
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hH).mp hPH
  rw [hP, le_antisymm h3 h4]

theorem card_conj_k_modEq (S : Gens A) (Fr : Frame A F C.k) :
    {b | ∃ g ∈ centralizer ({t} : Set X), g * C.k * g⁻¹ = b}.ncard ≡ 2 [MOD 4] := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set CX : Subgroup X := centralizer ({t} : Set X) with hCX
  set e := Fr.e with he
  set a : PGammaL2 F := SemidirectProduct.inr Fr.σ with ha
  have hak : act A e C.k = a := Fr.act_κ
  have hkC := k_mem_C C
  set Y₀ : Subgroup CX := (centralizer ({a} : Set (PGammaL2 F))).comap (actC A e) with hY₀
  set Y : Subgroup X := Y₀.map CX.subtype with hY
  have hmemY : ∀ g, g ∈ Y ↔ g ∈ CX ∧ act A e g * a = a * act A e g := by
    intro g
    constructor
    · rintro ⟨h, hh, rfl⟩
      refine ⟨h.2, ?_⟩
      change act A e (h : X) * a = a * act A e (h : X)
      rw [act_of_mem e h.2]
      exact mem_centralizer_singleton_iff.mp hh
    · rintro ⟨hg, hcomm⟩
      refine ⟨⟨g, hg⟩, ?_, rfl⟩
      change actC A e ⟨g, hg⟩ ∈ centralizer ({a} : Set (PGammaL2 F))
      rw [mem_centralizer_singleton_iff, ← act_of_mem e hg]
      exact hcomm
  have hYC : Y ≤ CX := map_subtype_le _
  have hCkY : CX ⊓ centralizer ({C.k} : Set X) ≤ Y := by
    intro g hg
    obtain ⟨hgC, hgk⟩ := mem_inf.mp hg
    rw [hmemY]
    refine ⟨hgC, ?_⟩
    rw [← hak, ← act_mul e hgC hkC, ← act_mul e hkC hgC, mem_centralizer_singleton_iff.mp hgk]
  have hσ1 : Fr.σ ≠ 1 := by
    intro h
    have := Fr.orderOf_σ
    rw [h, orderOf_one] at this
    norm_num at this
  have hao : orderOf a = 2 := by
    rw [ha, orderOf_injective (SemidirectProduct.inr : (F ≃+* F) →* PGammaL2 F)
      SemidirectProduct.inr_injective, Fr.orderOf_σ]
  have hset : {y | ∃ g ∈ (actC A e).range, g * a * g⁻¹ = y} =
      {y | ∃ g ∈ (SemidirectProduct.inl : PGL2 F →* PGammaL2 F).range, g * a * g⁻¹ = y} := by
    ext y
    constructor
    · rintro ⟨g, -, rfl⟩
      have ho : orderOf (g * a * g⁻¹) = 2 :=
        (SemiconjBy.orderOf_eq g (by change g * a = g * a * g⁻¹ * g; group)).symm.trans hao
      have hr : (g * a * g⁻¹).right = Fr.σ := by rw [right_conj]; rfl
      obtain ⟨C₀, hC₀⟩ := exists_conj_inr_of_involution Fr.odd _ ho (by rw [hr]; exact hσ1)
      refine ⟨SemidirectProduct.inl C₀, ⟨C₀, rfl⟩, ?_⟩
      rw [hr] at hC₀
      calc SemidirectProduct.inl C₀ * a * (SemidirectProduct.inl C₀)⁻¹
          = SemidirectProduct.inl C₀ * ((SemidirectProduct.inl C₀)⁻¹ * (g * a * g⁻¹) *
              SemidirectProduct.inl C₀) * (SemidirectProduct.inl C₀)⁻¹ := by rw [hC₀]
        _ = g * a * g⁻¹ := by group
    · rintro ⟨g, ⟨p, rfl⟩, rfl⟩
      exact ⟨_, inl_mem_range C S Fr e p, rfl⟩
  have hYidx : Y.relIndex CX = ((SemidirectProduct.inl : PGL2 F →* PGammaL2 F).range ⊓
      centralizer ({a} : Set (PGammaL2 F))).relIndex
        (SemidirectProduct.inl : PGL2 F →* PGammaL2 F).range := by
    rw [relIndex, hY]
    change ((Y₀.map CX.subtype).comap CX.subtype).index = _
    rw [comap_map_eq_self_of_injective (subtype_injective CX), hY₀, Subgroup.index_comap,
      ← inf_relIndex_right, inf_comm, relIndex_inf_centralizer_eq_ncard, hset,
      ← relIndex_inf_centralizer_eq_ncard]
  have hK₀ := Fr.K₀_odd
  have hr : Odd (Nat.card Fr.K₀) := by
    obtain ⟨p, n, -, hpodd, -, hc⟩ := hK₀
    rw [hc]
    exact hpodd.pow
  have hr3 : 3 ≤ Nat.card Fr.K₀ := by
    obtain ⟨p, n, hp, hpodd, hn, hc⟩ := hK₀
    have h2 := hp.two_le
    have hp2 : p ≠ 2 := fun h => by rw [h] at hpodd; exact absurd hpodd (by decide)
    rw [hc]
    calc 3 ≤ p := by omega
      _ ≤ p ^ n := Nat.le_self_pow (by omega) p
  have hmulI := relIndex_inl_centralizer_mul Fr
  rw [pgl2_card_formula, pgl2_card_formula, Fr.card_F] at hmulI
  obtain ⟨m, hm, hidx⟩ := index_k_eq hr hr3 hmulI
  rw [← hYidx] at hidx
  have hcardCX : Nat.card CX = Nat.card Y * (2 * m) := by
    have h := relIndex_mul_card Y CX
    rw [inf_of_le_left hYC, hidx] at h
    rw [← h, mul_comm]
  have hYpos : Nat.card Y ≠ 0 := Nat.card_pos.ne'
  have hmpos : m ≠ 0 := by rintro rfl; exact (Nat.not_even_iff_odd.mpr hm) ⟨0, rfl⟩
  have hm2 : m.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (fun h => (Nat.not_even_iff_odd.mpr hm)
      (even_iff_two_dvd.mpr h))
  have hv : (Nat.card CX).factorization 2 = (Nat.card Y).factorization 2 + 1 := by
    rw [hcardCX, Nat.factorization_mul hYpos (by positivity), Finsupp.add_apply,
      Nat.factorization_mul (by norm_num) hmpos, Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_two, hm2]
  have hTE : Nat.card (TE A) = 2 ^ (Nat.card Y).factorization 2 := by
    have h1 := card_T_eq_two_pow (A := A)
    rw [card_T_eq_two_mul_card_TE C, hv, pow_succ] at h1
    omega
  have hTEY : TE A ≤ Y ⊓ centralizer ({C.k} : Set X) := by
    intro g hg
    obtain ⟨r, hr', i, j, hi, hj, rfl⟩ := eq_of_mem_TE C hg
    have hrC := L_le_C (A := A) hr'.2
    have hgC : r * t ^ i * C.k ^ j ∈ CX :=
      mul_mem (mul_mem hrC (pow_mem t_mem_C i)) (pow_mem hkC j)
    refine Subgroup.mem_inf.mpr ⟨(hmemY _).mpr ⟨hgC, ?_⟩, ?_⟩
    · rw [act_mul e (mul_mem hrC (pow_mem t_mem_C i)) (pow_mem hkC j),
        act_mul e hrC (pow_mem t_mem_C i), act_pow e t_mem_C, act_t, one_pow, mul_one,
        act_pow e hkC, hak, act_of_mem_L e hr'.2]
      have h1 : incl F (rho e r) * a = a * incl F (rho e r) := by
        have := (commute_incl_iff (SemidirectProduct.inr Fr.σ) (rho e r)).mpr (by
          rw [semilinearAction_inr]
          exact Fr.rho_mem_fieldCent hr')
        rw [ha]
        exact this.symm
      have h2 : a ^ j * a = a * a ^ j := (Commute.self_pow a j).eq.symm
      calc incl F (rho e r) * a ^ j * a = incl F (rho e r) * (a ^ j * a) := by group
        _ = incl F (rho e r) * a * a ^ j := by rw [h2, mul_assoc]
        _ = a * incl F (rho e r) * a ^ j := by rw [h1]
        _ = a * (incl F (rho e r) * a ^ j) := by group
    · rw [mem_centralizer_singleton_iff]
      have hkr : C.k * r = r * C.k := commute_k C hr'
      have hkt : C.k * t ^ i = t ^ i * C.k :=
        (Commute.pow_right (commute_t_of_mem_C hkC) i)
      have hkk : C.k ^ j * C.k = C.k * C.k ^ j := (Commute.self_pow C.k j).eq.symm
      calc r * t ^ i * C.k ^ j * C.k = r * t ^ i * (C.k ^ j * C.k) := by group
        _ = r * (t ^ i * C.k) * C.k ^ j := by rw [hkk]; group
        _ = r * C.k * t ^ i * C.k ^ j := by rw [← hkt]; group
        _ = C.k * (r * t ^ i * C.k ^ j) := by rw [← hkr]; group
  have hTE' : Nat.card (TE A) = 2 ^ (Nat.card (Y ⊓ centralizer ({C.k} : Set X) :
      Subgroup X)).factorization 2 :=
    factorization_eq_of_sandwich hTE (Subgroup.card_dvd_of_le hTEY)
      (Subgroup.card_dvd_of_le inf_le_left) hYpos
  have h3 := card_eq_mul_two_pow (P := TE A) (Q := TE A) inf_le_left hTE hTE'
  have hodd : Odd ((Y ⊓ centralizer ({C.k} : Set X)).relIndex Y) := by
    have hpos : 0 < Nat.card (TE A) := Nat.card_pos
    have h4 : 2 ^ ((Y ⊓ centralizer ({C.k} : Set X)).relIndex Y).factorization 2 = 1 := by
      have := h3
      nlinarith [this]
    have h5 : ((Y ⊓ centralizer ({C.k} : Set X)).relIndex Y).factorization 2 = 0 :=
      Nat.pow_right_injective (le_refl 2) (by simp only []; rw [h4, pow_zero])
    have hne : (Y ⊓ centralizer ({C.k} : Set X)).relIndex Y ≠ 0 := by
      intro h0
      have := relIndex_mul_card (Y ⊓ centralizer ({C.k} : Set X)) Y
      rw [h0, zero_mul] at this
      exact hYpos this.symm
    rw [Nat.odd_iff]
    by_contra h6
    have h7 : 2 ∣ (Y ⊓ centralizer ({C.k} : Set X)).relIndex Y := by omega
    have := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hne).mp h7
    omega
  have hmul := relIndex_mul_relIndex (CX ⊓ centralizer ({C.k} : Set X)) Y CX hCkY hYC
  have hinf : (CX ⊓ centralizer ({C.k} : Set X)).relIndex Y =
      (Y ⊓ centralizer ({C.k} : Set X)).relIndex Y := by
    rw [← inf_relIndex_right (CX ⊓ centralizer ({C.k} : Set X)) Y,
      ← inf_relIndex_right (Y ⊓ centralizer ({C.k} : Set X)) Y]
    congr 1
    apply le_antisymm
    · exact le_inf (le_inf inf_le_right (inf_le_left.trans inf_le_right)) inf_le_right
    · exact le_inf (le_inf (inf_le_left.trans (inf_le_left.trans hYC))
        (inf_le_left.trans inf_le_right)) inf_le_right
  rw [← relIndex_inf_centralizer_eq_ncard, ← hmul, hinf, hidx]
  obtain ⟨o, ho⟩ := hodd
  obtain ⟨m', hm'⟩ := hm
  rw [ho, hm', Nat.ModEq]
  ring_nf
  omega

theorem relIndex_centralizer_dvd {G : Type*} [Group G] [Finite G] {N H : Subgroup G} [N.Normal]
    (hNH : N ≤ H) (x : G) :
    (N ⊓ centralizer ({x} : Set G)).relIndex N ∣ (H ⊓ centralizer ({x} : Set G)).relIndex H := by
  set K := H ⊓ centralizer ({x} : Set G) with hK
  have hKH : K ≤ H := inf_le_left
  have hsup := relIndex_sup_left K N
  have c1 := relIndex_mul_card N (N ⊔ K)
  rw [inf_of_le_left le_sup_left, hsup] at c1
  have c2 := relIndex_mul_card N K
  have c3 := relIndex_mul_card K N
  have c4 := relIndex_mul_card K H
  rw [inf_of_le_left hKH] at c4
  have c5 : Nat.card (N ⊔ K : Subgroup G) ∣ Nat.card H :=
    Subgroup.card_dvd_of_le (sup_le hNH hKH)
  have hKN : N ⊓ centralizer ({x} : Set G) = K ⊓ N := by
    rw [hK]
    apply le_antisymm
    · exact le_inf (le_inf (inf_le_left.trans hNH) inf_le_right) inf_le_left
    · exact le_inf inf_le_right (inf_le_left.trans inf_le_right)
  have hidxN : (N ⊓ centralizer ({x} : Set G)).relIndex N = K.relIndex N := by
    rw [hKN, inf_relIndex_right]
  rw [hidxN]
  have hpos : 0 < Nat.card K := Nat.card_pos
  have h1 : Nat.card (N ⊔ K : Subgroup G) = K.relIndex N * Nat.card K := by
    rw [← c1, ← c2, ← c3, inf_comm K N]
    ring
  rw [h1, ← c4] at c5
  exact Nat.dvd_of_mul_dvd_mul_right hpos c5

theorem four_dvd_index_d {q I : ℕ} (hq : q % 8 = 1) (hq3 : 3 < q)
    (h : I * (q + 1) = q * (q ^ 2 - 1) / 2) : 4 ∣ I := by
  obtain ⟨j, rfl⟩ : ∃ j, q = 8 * j + 1 := ⟨q / 8, by omega⟩
  have h1 : (8 * j + 1) * ((8 * j + 1) ^ 2 - 1) / 2 = (8 * j + 1) * (4 * j) * (8 * j + 2) := by
    have : (8 * j + 1) ^ 2 - 1 = 8 * j * (8 * j + 2) := by
      rw [Nat.sub_eq_iff_eq_add (by nlinarith)]
      ring
    rw [this, show (8 * j + 1) * (8 * j * (8 * j + 2)) =
      2 * ((8 * j + 1) * (4 * j) * (8 * j + 2)) by ring, Nat.mul_div_cancel_left _ two_pos]
  rw [h1, show 8 * j + 1 + 1 = 8 * j + 2 by ring] at h
  have hI : I = (8 * j + 1) * (4 * j) := Nat.eq_of_mul_eq_mul_right (by omega) h
  rw [hI]
  exact Dvd.intro_left ((8 * j + 1) * j) (by ring)

theorem card_conj_d_modEq (S : Gens A) (Fr : Frame A F C.k) :
    {b | ∃ g ∈ centralizer ({t} : Set X), g * C.d * g⁻¹ = b}.ncard ≡ 0 [MOD 4] := by
  classical
  set CX : Subgroup X := centralizer ({t} : Set X) with hCX
  set e := Fr.e with he
  set δ : PGammaL2 F := act A e C.d with hδ
  have hdC := d_mem_C C
  set Y₀ : Subgroup CX := (centralizer ({δ} : Set (PGammaL2 F))).comap (actC A e) with hY₀
  set Y : Subgroup X := Y₀.map CX.subtype with hY
  have hmemY : ∀ g, g ∈ Y ↔ g ∈ CX ∧ act A e g * δ = δ * act A e g := by
    intro g
    constructor
    · rintro ⟨h, hh, rfl⟩
      refine ⟨h.2, ?_⟩
      change act A e (h : X) * δ = δ * act A e (h : X)
      rw [act_of_mem e h.2]
      exact mem_centralizer_singleton_iff.mp hh
    · rintro ⟨hg, hcomm⟩
      refine ⟨⟨g, hg⟩, ?_, rfl⟩
      change actC A e ⟨g, hg⟩ ∈ centralizer ({δ} : Set (PGammaL2 F))
      rw [mem_centralizer_singleton_iff, ← act_of_mem e hg]
      exact hcomm
  have hYC : Y ≤ CX := map_subtype_le _
  have hCdY : CX ⊓ centralizer ({C.d} : Set X) ≤ Y := by
    intro g hg
    obtain ⟨hgC, hgd⟩ := mem_inf.mp hg
    rw [hmemY]
    refine ⟨hgC, ?_⟩
    rw [hδ, ← act_mul e hgC hdC, ← act_mul e hdC hgC, mem_centralizer_singleton_iff.mp hgd]
  have hYidx : Y.relIndex CX = ((actC A e).range ⊓ centralizer ({δ} : Set (PGammaL2 F))).relIndex
      (actC A e).range := by
    rw [relIndex, hY]
    change ((Y₀.map CX.subtype).comap CX.subtype).index = _
    rw [comap_map_eq_self_of_injective (subtype_injective CX), hY₀, Subgroup.index_comap,
      ← inf_relIndex_right, inf_comm]
  set N : Subgroup (PGammaL2 F) := (incl F).range with hN
  have hNn : N.Normal := ⟨fun n hn g => by
    obtain ⟨y, rfl⟩ := hn
    exact ⟨_, (conj_incl g y).symm⟩⟩
  have hNle : N ≤ (actC A e).range := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨⟨l, hl⟩, hlc⟩ := QuotientGroup.mk_surjective (e.symm y)
    have hrl : rho e l = y := by rw [rho_of_mem e hl, hlc, MulEquiv.apply_symm_apply]
    refine ⟨⟨l, L_le_C (A := A) hl⟩, ?_⟩
    rw [← act_of_mem e (L_le_C (A := A) hl), act_of_mem_L e hl, hrl]
  have hdvd := relIndex_centralizer_dvd hNle δ
  set t₀ := δ.left with ht₀
  have hδr : δ.right = 1 := right_act_d C S Fr e
  have hδeq : δ = SemidirectProduct.inl t₀ := SemidirectProduct.ext rfl hδr
  have ht₀2 : t₀ * t₀ = 1 := by
    have h2 := act_d_sq C e
    rw [← hδ, hδeq, pow_two, ← map_mul] at h2
    exact SemidirectProduct.inl_injective (h2.trans (map_one _).symm)
  have ht₀1 : t₀ ≠ 1 := by
    intro h
    apply act_d_ne_one C e
    rw [← hδ, hδeq, h, map_one]
  have ht₀r : t₀ ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range :=
    not_sqLeft_act_d C S Fr e
  have hq : Nat.card F = Nat.card Fr.K₀ ^ 2 := Fr.card_F
  have hK₀ := Fr.K₀_odd
  obtain ⟨s, hs⟩ : Odd (Nat.card Fr.K₀) := by
    obtain ⟨p, n, -, hpodd, -, hc⟩ := hK₀
    rw [hc]
    exact hpodd.pow
  have hs1 : 1 ≤ s := by
    obtain ⟨p, n, hp, hpodd, hn, hc⟩ := hK₀
    have h2 := hp.two_le
    have hp2 : p ≠ 2 := fun h => by rw [h] at hpodd; exact absurd hpodd (by decide)
    have : 3 ≤ p ^ n := (show 3 ≤ p by omega).trans (Nat.le_self_pow (by omega) p)
    omega
  have hq8 : Nat.card F % 8 = 1 := by
    rw [hq, hs]
    rcases Nat.even_or_odd s with ⟨u, rfl⟩ | ⟨u, rfl⟩ <;> ring_nf <;> omega
  have hq3 : 3 < Nat.card F := by
    rw [hq, hs]
    nlinarith
  obtain ⟨φ⟩ := psl2_fix_outer_involution Fr.odd (by omega) hq3 ht₀2 ht₀1 ht₀r
  have hNC : N ⊓ centralizer ({δ} : Set (PGammaL2 F)) =
      (MonoidHom.eqLocus (pglAction F t₀).toMonoidHom (MonoidHom.id (PSL2 F))).map (incl F) := by
    ext x
    constructor
    · intro hx
      obtain ⟨⟨y, rfl⟩, hx⟩ := Subgroup.mem_inf.mp hx
      rw [mem_centralizer_singleton_iff] at hx
      refine ⟨y, ?_, rfl⟩
      have h1 := (commute_incl_iff δ y).mp hx.symm
      rw [hδeq, semilinearAction_inl] at h1
      exact h1
    · rintro ⟨y, hy, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨⟨y, rfl⟩, ?_⟩
      rw [mem_centralizer_singleton_iff]
      have h1 : semilinearAction F δ y = y := by
        rw [hδeq, semilinearAction_inl]
        exact hy
      exact ((commute_incl_iff δ y).mpr h1).symm
  have hcardNC : Nat.card (N ⊓ centralizer ({δ} : Set (PGammaL2 F)) : Subgroup _) =
      Nat.card F + 1 := by
    rw [hNC, card_map_of_injective (incl_injective F), Nat.card_congr φ.toEquiv,
      DihedralGroup.nat_card]
    omega
  have hcardN : Nat.card N = Nat.card (PSL2 F) :=
    (Nat.card_congr (MonoidHom.ofInjective (incl_injective F)).toEquiv).symm
  have hI := relIndex_mul_card (N ⊓ centralizer ({δ} : Set (PGammaL2 F))) N
  rw [inf_of_le_left inf_le_left, hcardNC, hcardN, psl2_card_formula F Fr.odd] at hI
  have h4 := four_dvd_index_d hq8 hq3 hI
  have h4Y : 4 ∣ Y.relIndex CX := by
    rw [hYidx]
    exact h4.trans hdvd
  have hmul := relIndex_mul_relIndex (CX ⊓ centralizer ({C.d} : Set X)) Y CX hCdY hYC
  rw [← relIndex_inf_centralizer_eq_ncard, ← hmul, Nat.modEq_zero_iff_dvd]
  exact Dvd.dvd.mul_left h4Y _

end CFSG.ComponentClassification.HSFLit.L2KD
