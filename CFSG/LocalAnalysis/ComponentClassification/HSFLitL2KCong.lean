module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2KFrame
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitCong
public import CFSG.GroupTheory.ABGDGroups.LinearCentralizers

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit.L2K

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer GorensteinWalter
open CFSG.ComponentClassification.AutL2Facts CFSG.ComponentClassification.CatalogueSchreierLinearTwo

theorem index_modEq_of_sq {q r : ℕ} (hr : Odd r) (hq : q = r ^ 2) (hr3 : 3 ≤ r) {n : ℕ}
    (hn : n * (q - 1) = q * (q ^ 2 - 1) / 2) : n ≡ 1 [MOD 4] := by
  obtain ⟨s, rfl⟩ := hr
  obtain ⟨j, hj⟩ : ∃ j, q = 8 * j + 1 := by
    rcases Nat.even_or_odd s with ⟨u, rfl⟩ | ⟨u, rfl⟩
    · exact ⟨u * (2 * u + 1), by rw [hq]; ring⟩
    · exact ⟨(2 * u + 1) * (u + 1), by rw [hq]; ring⟩
  have hj1 : 1 ≤ j := by
    have : 9 ≤ q := by rw [hq]; nlinarith
    omega
  subst hj
  have h1 : (8 * j + 1) * ((8 * j + 1) ^ 2 - 1) / 2 = 8 * j * ((8 * j + 1) * (4 * j + 1)) := by
    have : (8 * j + 1) ^ 2 - 1 = 16 * j * (4 * j + 1) := by
      rw [Nat.sub_eq_iff_eq_add (by nlinarith)]
      ring
    rw [this, show (8 * j + 1) * (16 * j * (4 * j + 1)) =
      2 * (8 * j * ((8 * j + 1) * (4 * j + 1))) by ring, Nat.mul_div_cancel_left _ two_pos]
  rw [h1, Nat.add_sub_cancel, mul_comm n] at hn
  have hn' : n = (8 * j + 1) * (4 * j + 1) := Nat.eq_of_mul_eq_mul_left (by omega) hn
  rw [hn', show (8 * j + 1) * (4 * j + 1) = 4 * (8 * j * j + 3 * j) + 1 by ring, Nat.ModEq,
    Nat.mul_add_mod]

theorem ncard_involutions_modEq {F : Type} [Field F] [Finite F]
    (hodd : IsOddPrimePower (Nat.card F))
    {r : ℕ} (hr : Odd r) (hq : Nat.card F = r ^ 2) (hr3 : 3 ≤ r) :
    {w : PSL2 F | BenderSuzuki.PFAppendixIII.IsInvolution w}.ncard ≡ 1 [MOD 4] := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : PSL2 F, orderOf w₀ = 2 := by
    have h2 : 2 ∣ Nat.card (PSL2 F) := even_iff_two_dvd.mp (even_psl2_card hodd)
    exact exists_prime_orderOf_dvd_card' 2 h2
  have hw₀I : BenderSuzuki.PFAppendixIII.IsInvolution w₀ :=
    ⟨fun h => by rw [h, orderOf_one] at hw₀; norm_num at hw₀,
      by have := pow_orderOf_eq_one w₀; rwa [hw₀] at this⟩
  have hset : {w : PSL2 F | BenderSuzuki.PFAppendixIII.IsInvolution w} =
      {y | ∃ g ∈ (⊤ : Subgroup (PSL2 F)), g * w₀ * g⁻¹ = y} := by
    ext w
    constructor
    · intro hw
      obtain ⟨g, hg⟩ := psl2_involutions_conjugate_of_odd_prime_power F hodd w₀ w hw₀I hw
      exact ⟨g, mem_top g, hg⟩
    · rintro ⟨g, -, rfl⟩
      refine ⟨fun h => hw₀I.1 ?_, ?_⟩
      · calc w₀ = g⁻¹ * (g * w₀ * g⁻¹) * g := by group
          _ = 1 := by rw [h]; group
      · rw [conj_pow, hw₀I.2, mul_one, mul_inv_cancel]
  rw [hset, ← relIndex_inf_centralizer_eq_ncard, top_inf_eq, relIndex_top_right]
  have hq4 : (Nat.card F : ℤ) ≡ 1 [ZMOD 4] := by
    obtain ⟨s, rfl⟩ := hr
    rw [hq, Int.ModEq]
    push_cast
    rw [show (2 * (s : ℤ) + 1) ^ 2 = 1 + 4 * (s ^ 2 + s) by ring, Int.add_mul_emod_self_left]
    norm_num
  obtain ⟨m, hm, ⟨φ⟩⟩ := ABGDGroups.psl2_centralizer_involution_dihedral hodd hq4 (Or.inl rfl) hw₀
  have hC : Nat.card (centralizer ({w₀} : Set (PSL2 F))) = Nat.card F - 1 := by
    rw [Nat.card_congr φ.toEquiv, DihedralGroup.nat_card]
    have h1 : 1 ≤ Nat.card F := Nat.card_pos
    omega
  have hmul := (centralizer ({w₀} : Set (PSL2 F))).card_mul_index
  rw [hC, psl2_card_formula F hodd, mul_comm] at hmul
  exact index_modEq_of_sq hr hq hr3 hmul

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
variable {F : Type} [Field F] [Finite F]

theorem card_conj_z_modEq (C : A.CaseK) (S : Gens A) {κ : X} (Fr : Frame A F κ)
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

end CFSG.ComponentClassification.HSFLit.L2K
