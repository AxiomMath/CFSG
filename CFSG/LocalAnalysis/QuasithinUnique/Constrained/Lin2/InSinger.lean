module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLinearPointKernelSemilinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Defs

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open
open CFSG.ShultStronglyClosedTI.CyclicSemiregular CFSG.ShultStronglyClosedTI.LinearChain
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped IsMulCommutative

theorem mul_add_one_lt_pow_succ (x m : ℕ) (hx : 1 ≤ x) (hm : 2 ≤ m) :
    x * m + 1 < (x + 1) ^ m := by
  induction m, hm using Nat.le_induction with
  | base => nlinarith
  | succ k hk ih =>
    have e : (x + 1) * (x * k + 1) = x * (k + 1) + 1 + x * x * k := by ring
    calc x * (k + 1) + 1 ≤ (x + 1) * (x * k + 1) := by rw [e]; exact Nat.le_add_right _ _
      _ < (x + 1) * (x + 1) ^ k := by apply Nat.mul_lt_mul_of_pos_left ih (by omega)
      _ = (x + 1) ^ (k + 1) := by ring

theorem eq_one_of_pow_le_mul_add_one {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m)
    (h : r ^ m ≤ (r - 1) * m + 1) : m = 1 := by
  by_contra hne
  have hm2 : 2 ≤ m := by omega
  obtain ⟨x, rfl⟩ : ∃ x, r = x + 1 := ⟨r - 1, by omega⟩
  have := mul_add_one_lt_pow_succ x m (by omega) hm2
  simp at h
  omega

theorem right_eq_one_of_card {k : Type} [Field k] [Finite k] {B : Type} [Group B] [Finite B]
    (ι : B →* kˣ ⋊[ringAutUnits k] RingAut k) {E : Subgroup B}
    (hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hinj : ∀ e ∈ E, ι e = 1 → e = 1)
    (hcard : Nat.card E + 1 = Nat.card k) : ∀ ε ∈ E, (ι ε).right = 1 := by
  classical
  let θ : B →* RingAut k := SemidirectProduct.rightHom.comp ι
  let θE : E →* RingAut k := θ.comp E.subtype
  let H' : Subgroup (RingAut k) := θE.range
  have hker := Subgroup.card_ker_mul_card_of_surjective θE.rangeRestrict_surjective
  rw [MonoidHom.ker_rangeRestrict] at hker
  have hker' : Nat.card θE.ker * Nat.card H' = Nat.card E := hker
  have hfin : Finite H' := Finite.of_surjective θE.rangeRestrict θE.rangeRestrict_surjective
  have hfint : Fintype H' := Fintype.ofFinite H'
  have hart : Module.finrank (FixedPoints.subfield H' k) k = Nat.card H' := by
    rw [Nat.card_eq_fintype_card]
    exact FixedPoints.finrank_eq_card H' k
  have hpow : Nat.card k = Nat.card (FixedPoints.subfield H' k) ^
      Module.finrank (FixedPoints.subfield H' k) k := Module.natCard_eq_pow_finrank
  rw [hart] at hpow
  have hright : ∀ κ : θE.ker, (ι ((κ : E) : B)).right = 1 := by
    intro κ
    have := κ.2
    rw [MonoidHom.mem_ker] at this
    exact this
  have hfix : ∀ κ : θE.ker, ∀ h : H',
      h • ((ι ((κ : E) : B)).left : k) = ((ι ((κ : E) : B)).left : k) := by
    intro κ h
    obtain ⟨ε, hε⟩ := h.2
    have hcomm : ι ((ε : E) : B) * ι ((κ : E) : B) = ι ((κ : E) : B) * ι ((ε : E) : B) := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact hEcomm _ ε.2 _ (κ : E).2
    have hl := congrArg SemidirectProduct.left hcomm
    rw [SemidirectProduct.mul_left, SemidirectProduct.mul_left, hright κ] at hl
    simp only [map_one, MulAut.one_apply] at hl
    have hl' : (ι ((ε : E) : B)).left *
        (ringAutUnits k (ι ((ε : E) : B)).right) (ι ((κ : E) : B)).left =
        (ι ((ε : E) : B)).left * (ι ((κ : E) : B)).left := by
      rw [hl, mul_comm]
    have h1 := mul_left_cancel hl'
    have h2 : (ι ((ε : E) : B)).right ((ι ((κ : E) : B)).left : k) =
        ((ι ((κ : E) : B)).left : k) := by
      have := congrArg (fun u : kˣ => (u : k)) h1
      simpa only [coe_ringAutUnits_apply] using this
    have : (h : RingAut k) = (ι ((ε : E) : B)).right := by
      rw [← hε]
      rfl
    rw [show h • ((ι ((κ : E) : B)).left : k) = (h : RingAut k) ((ι ((κ : E) : B)).left : k) from
      rfl, this]
    exact h2
  have hmem : ∀ κ : θE.ker, ((ι ((κ : E) : B)).left : k) ∈ FixedPoints.subfield H' k :=
    fun κ => MulAction.mem_fixedPoints.2 (hfix κ)
  let f : θE.ker → {x : FixedPoints.subfield H' k // x ≠ 0} := fun κ =>
    ⟨⟨(ι ((κ : E) : B)).left, hmem κ⟩,
      fun h0 => (ι ((κ : E) : B)).left.ne_zero (congrArg Subtype.val h0)⟩
  have hf : Function.Injective f := by
    intro κ₁ κ₂ h12
    have h1 : ((ι ((κ₁ : E) : B)).left : k) = (ι ((κ₂ : E) : B)).left := by
      have := congrArg
        (fun z : {x : FixedPoints.subfield H' k // x ≠ 0} =>
          ((z.1 : FixedPoints.subfield H' k) : k)) h12
      exact this
    have h2 : (ι ((κ₁ : E) : B)).left = (ι ((κ₂ : E) : B)).left := Units.ext h1
    have h3 : ι ((κ₁ : E) : B) = ι ((κ₂ : E) : B) :=
      SemidirectProduct.ext h2 (by rw [hright κ₁, hright κ₂])
    have h4 : ι (((κ₁ : E) : B) * ((κ₂ : E) : B)⁻¹) = 1 := by
      rw [map_mul, map_inv, h3, mul_inv_cancel]
    have h5 : (((κ₁ : E) : B) * ((κ₂ : E) : B)⁻¹) ∈ E :=
      E.mul_mem (κ₁ : E).2 (E.inv_mem (κ₂ : E).2)
    have h6 := hinj _ h5 h4
    apply Subtype.ext
    apply Subtype.ext
    exact mul_inv_eq_one.1 h6
  have hle := Nat.card_le_card_of_injective f hf
  have hsub : Nat.card {x : FixedPoints.subfield H' k // x ≠ 0} =
      Nat.card (FixedPoints.subfield H' k) - 1 := by
    have : Fintype (FixedPoints.subfield H' k) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    simp
  rw [hsub] at hle
  have hr : 2 ≤ Nat.card (FixedPoints.subfield H' k) := Finite.one_lt_card
  have hm1 : 1 ≤ Nat.card H' := Nat.card_pos
  have key : Nat.card (FixedPoints.subfield H' k) ^ Nat.card H' ≤
      (Nat.card (FixedPoints.subfield H' k) - 1) * Nat.card H' + 1 := by
    have h1 : Nat.card θE.ker * Nat.card H' ≤
        (Nat.card (FixedPoints.subfield H' k) - 1) * Nat.card H' := Nat.mul_le_mul_right _ hle
    calc Nat.card (FixedPoints.subfield H' k) ^ Nat.card H' = Nat.card k := hpow.symm
      _ = Nat.card E + 1 := hcard.symm
      _ = Nat.card θE.ker * Nat.card H' + 1 := by rw [hker']
      _ ≤ _ := Nat.add_le_add_right h1 1
  have hone := eq_one_of_pow_le_mul_add_one hr hm1 key
  have hbot : H' = ⊥ := Subgroup.eq_bot_of_card_eq _ hone
  intro ε hε
  have : θE ⟨ε, hε⟩ ∈ H' := ⟨⟨ε, hε⟩, rfl⟩
  rw [hbot, Subgroup.mem_bot] at this
  exact this

section Singer

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_one_of_centralizes_of_acts_regularly {Z D : Subgroup G} (hZ1 : Z ≠ ⊥)
    (hDreg : ActsRegularlyOn D (nonIdentity Z)) {d : G} (hd : d ∈ D)
    (hc : ∀ z ∈ Z, d * z = z * d) : d = 1 := by
  obtain ⟨⟨z₀, hz₀⟩, hz₀1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZ1
  have hz₀1 : z₀ ≠ 1 := fun h => hz₀1' (Subtype.ext h)
  refine hDreg.2.2 z₀ ⟨hz₀, hz₀1⟩ d hd ?_
  calc d⁻¹ * z₀ * d = d⁻¹ * (z₀ * d) := by rw [mul_assoc]
    _ = d⁻¹ * (d * z₀) := by rw [← hc z₀ hz₀]
    _ = z₀ := by group

theorem commute_of_singer {Z D E B : Subgroup G} {e : ℕ} (he1 : 1 ≤ e)
    (hZ : IsElemAbelian 2 Z) (hZcard : Nat.card Z = 2 ^ e)
    (hBN : B ≤ Subgroup.normalizer (Z : Set G)) (hDB : D ≤ B) (hEB : E ≤ B)
    (hDnorm : ∀ b ∈ B, ∀ d ∈ D, b * d * b⁻¹ ∈ D)
    (hDcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hDreg : ActsRegularlyOn D (nonIdentity Z)) (hDcard : Nat.card D = 2 ^ e - 1)
    (hEfree : ∀ x ∈ E, (∀ z ∈ Z, x * z = z * x) → x = 1) (hEcard : Nat.card E = 2 ^ e - 1) :
    ∀ d ∈ D, ∀ x ∈ E, d * x = x * d := by
  classical
  have hZc : IsMulCommutative Z := hZ.1
  let _ : Module (ZMod 2) (Additive Z) := AddCommGroup.zmodModule (n := 2) fun v => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact Subtype.ext (hZ.2 _ v.toMul.2)
  have : Finite (Additive Z) := inferInstanceAs (Finite Z)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ1 : Z ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hZcard
    have : 2 ≤ 2 ^ e := Nat.le_self_pow (by omega) 2
    omega
  set N := Subgroup.normalizer (Z : Set G) with hNdef
  let ρ₀ : N →* LinearMap.GeneralLinearGroup (ZMod 2) (Additive Z) :=
    (mulAutGL 2 Z).comp Z.normalizerMonoidHom
  have hρ₀ : ∀ (n : N) (v : Additive Z),
      ((((ρ₀ n : LinearMap.GeneralLinearGroup (ZMod 2) (Additive Z)) :
        Module.End (ZMod 2) (Additive Z)) v).toMul : G) = (n : G) * (v.toMul : G) * (n : G)⁻¹ :=
    fun _ _ => rfl
  have hρ₀ker : ∀ n : N, ρ₀ n = 1 ↔ ∀ z ∈ Z, (n : G) * z = z * (n : G) := by
    intro n
    constructor
    · intro hn x hx
      have h1 := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2) (Additive Z) =>
        (((g : Module.End (ZMod 2) (Additive Z)) (Additive.ofMul ⟨x, hx⟩)).toMul : G)) hn
      simp only [hρ₀, toMul_ofMul, Units.val_one, Module.End.one_apply] at h1
      calc (n : G) * x = (n : G) * x * (n : G)⁻¹ * n := by group
        _ = x * n := by rw [h1]
    · intro hn
      apply Units.ext
      apply LinearMap.ext
      intro v
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [hρ₀]
      change (n : G) * (v.toMul : G) * (n : G)⁻¹ = (v.toMul : G)
      rw [hn _ v.toMul.2, mul_inv_cancel_right]
  let ρ : B →* LinearMap.GeneralLinearGroup (ZMod 2) (Additive Z) :=
    ρ₀.comp (Subgroup.inclusion hBN)
  have hρ : ∀ b : B, ρ b = ρ₀ ⟨b, hBN b.2⟩ := fun _ => rfl
  let X : Subgroup B := D.subgroupOf B
  have hXn : X.Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hDnorm g g.2 x hx
  have hXcomm : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := fun a ha b hb =>
    Subtype.ext (hDcomm a ha b hb)
  have hne : ∀ v : Additive Z, v ≠ 0 → (v.toMul : G) ∈ nonIdentity Z := fun v hv =>
    ⟨v.toMul.2, fun h => hv (congrArg Additive.ofMul (Subtype.ext h))⟩
  have htrans : ∀ v w : Additive Z, v ≠ 0 → w ≠ 0 → ∃ x ∈ X,
      ((ρ x : LinearMap.GeneralLinearGroup (ZMod 2) (Additive Z)) :
        Module.End (ZMod 2) (Additive Z)) v = w := by
    intro v w hv hw
    obtain ⟨b, hb, hbz⟩ := hDreg.2.1 _ (hne v hv) _ (hne w hw)
    refine ⟨⟨b⁻¹, hDB (D.inv_mem hb)⟩, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      exact D.inv_mem hb
    · apply Additive.toMul.injective
      apply Subtype.ext
      change (((ρ₀ ⟨b⁻¹, hBN (hDB (D.inv_mem hb))⟩ :
        LinearMap.GeneralLinearGroup (ZMod 2) (Additive Z)) :
        Module.End (ZMod 2) (Additive Z)) v).toMul.1 = w.toMul.1
      rw [hρ₀]
      simpa using hbz
  have hXinj : ∀ x ∈ X, ρ x = 1 → x = 1 := by
    intro x hx h1
    have hx' : (x : G) ∈ D := hx
    have h2 : ρ₀ ⟨x, hBN x.2⟩ = 1 := h1
    exact Subtype.ext (eq_one_of_centralizes_of_acts_regularly hZ1 hDreg hx' ((hρ₀ker _).1 h2))
  have hXcard : Nat.card X = 2 ^ e - 1 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDB).toEquiv, hDcard]
  have hdim : Module.finrank (ZMod 2) (Additive Z) = e := by
    have h1 := FiniteField.pow_finrank_eq_natCard 2 (Additive Z)
    have h2 : Nat.card (Additive Z) = Nat.card Z := rfl
    rw [h2, hZcard] at h1
    exact Nat.pow_right_injective (le_refl 2) h1
  obtain ⟨k₀, _, _, hk₀, ev, ι, hker, hcompat, himage⟩ :=
    semilinear_of_transitive_commutative (B := B) (V := Additive Z) he1 hdim ρ
      (X := X) hXcomm htrans hXinj hXcard
  let E' : Subgroup B := E.subgroupOf B
  have hE'comm : ∀ a ∈ E', ∀ b ∈ E', a * b = b * a := fun a ha b hb =>
    Subtype.ext (hEcomm a ha b hb)
  have hE'inj : ∀ x ∈ E', ι x = 1 → x = 1 := by
    intro x hx h1
    have h2 : x ∈ ι.ker := h1
    rw [hker] at h2
    have h3 : ρ₀ ⟨x, hBN x.2⟩ = 1 := h2
    exact Subtype.ext (hEfree x hx ((hρ₀ker _).1 h3))
  have hE'card : Nat.card E' + 1 = Nat.card k₀ := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEB).toEquiv, hEcard, hk₀]
    have : 1 ≤ 2 ^ e := Nat.one_le_two_pow
    omega
  have hright := right_eq_one_of_card ι hE'comm hE'inj hE'card
  intro d hd x hx
  let dB : B := ⟨d, hDB hd⟩
  let xB : B := ⟨x, hEB hx⟩
  have hdX : dB ∈ X := hd
  have hxE' : xB ∈ E' := hx
  have hιd : ι dB ∈ (SemidirectProduct.inl : k₀ˣ →* _).range := by
    rw [← himage]
    exact ⟨dB, hdX, rfl⟩
  obtain ⟨a, ha⟩ := hιd
  have hιx : ι xB = SemidirectProduct.inl (ι xB).left :=
    SemidirectProduct.ext rfl (by rw [SemidirectProduct.right_inl, hright xB hxE'])
  have hcommι : ι (dB * xB * dB⁻¹ * xB⁻¹) = 1 := by
    have h1 : ι (dB * xB * dB⁻¹ * xB⁻¹) =
        SemidirectProduct.inl (a * (ι xB).left * a⁻¹ * (ι xB).left⁻¹) := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← ha, hιx, ← map_inv, ← map_inv,
        ← map_mul, ← map_mul, ← map_mul]
      rfl
    rw [h1]
    have h2 : a * (ι xB).left * a⁻¹ * (ι xB).left⁻¹ = 1 := by
      calc a * (ι xB).left * a⁻¹ * (ι xB).left⁻¹ = (ι xB).left * a * a⁻¹ * (ι xB).left⁻¹ := by
            rw [mul_comm a]
        _ = 1 := by group
    rw [h2, map_one]
  have hker1 : (dB * xB * dB⁻¹ * xB⁻¹) ∈ ι.ker := hcommι
  rw [hker] at hker1
  have hρ1 : ρ₀ ⟨d * x * d⁻¹ * x⁻¹, hBN (dB * xB * dB⁻¹ * xB⁻¹).2⟩ = 1 := hker1
  have hcz := (hρ₀ker _).1 hρ1
  have hyD : d * x * d⁻¹ * x⁻¹ ∈ D := by
    have h1 := hDnorm x (hEB hx) d⁻¹ (D.inv_mem hd)
    have e1 : d * x * d⁻¹ * x⁻¹ = d * (x * d⁻¹ * x⁻¹) := by group
    rw [e1]
    exact D.mul_mem hd h1
  have hy1 := eq_one_of_centralizes_of_acts_regularly hZ1 hDreg hyD hcz
  have h3 : d * x * d⁻¹ = x := mul_inv_eq_one.1 hy1
  exact mul_inv_eq_iff_eq_mul.1 h3

end Singer

end CFSG.QuasithinUnique.Lin2
