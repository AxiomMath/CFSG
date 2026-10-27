module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InSinger

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open
open CFSG.ShultStronglyClosedTI.CyclicSemiregular CFSG.ShultStronglyClosedTI.LinearChain
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped IsMulCommutative

theorem eq_one_of_fixed_quotient {k : Type} [Field k] [Finite k] (σ : RingAut k)
    (h : ∀ u : kˣ, σ ((u : k) / σ (u : k)) = (u : k) / σ (u : k)) : σ = 1 := by
  classical
  by_contra hσ
  have hfinAut : Finite (RingAut k) :=
    Finite.of_injective (fun τ : RingAut k => (τ : k → k)) DFunLike.coe_injective
  let H' : Subgroup (RingAut k) := Subgroup.zpowers σ
  have hfinH : Fintype H' := Fintype.ofFinite H'
  have hH'card : Nat.card H' = orderOf σ := Nat.card_zpowers σ
  have hord : 2 ≤ orderOf σ := by
    have h1 : orderOf σ ≠ 1 := fun h1 => hσ (orderOf_eq_one_iff.1 h1)
    have h0 : 0 < orderOf σ := orderOf_pos σ
    omega
  have hart : Module.finrank (FixedPoints.subfield H' k) k = Nat.card H' := by
    rw [Nat.card_eq_fintype_card]
    exact FixedPoints.finrank_eq_card H' k
  have hpow : Nat.card k = Nat.card (FixedPoints.subfield H' k) ^
      Module.finrank (FixedPoints.subfield H' k) k := Module.natCard_eq_pow_finrank
  rw [hart, hH'card] at hpow
  have hfix : ∀ x : k, σ x = x → x ∈ FixedPoints.subfield H' k := by
    intro x hx
    have hst : H' ≤ MulAction.stabilizer (RingAut k) x :=
      Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 hx)
    exact MulAction.mem_fixedPoints.2 fun g => hst g.2
  let f : kˣ →* kˣ := MonoidHom.mk' (fun u : kˣ => u * (Units.map σ.toMonoidHom u)⁻¹)
    (by intro a b; simp only [map_mul, mul_inv]; exact mul_mul_mul_comm _ _ _ _)
  have hf : ∀ u : kˣ, ((f u : kˣ) : k) = (u : k) / σ (u : k) := by
    intro u
    show ((u * (Units.map σ.toMonoidHom u)⁻¹ : kˣ) : k) = _
    rw [Units.val_mul, Units.val_inv_eq_inv_val, div_eq_mul_inv]
    rfl
  have hker : ∀ u : kˣ, u ∈ f.ker → σ (u : k) = u := by
    intro u hu
    rw [MonoidHom.mem_ker] at hu
    have h1 := congrArg Units.val hu
    rw [hf] at h1
    simp only [Units.val_one] at h1
    have hne : σ (u : k) ≠ 0 := by
      intro h0
      exact u.ne_zero (σ.injective (by rw [h0, map_zero]))
    exact (div_eq_one_iff_eq hne).1 h1 |>.symm
  have hfintype : Fintype k := Fintype.ofFinite k
  have hsub : Nat.card {x : FixedPoints.subfield H' k // x ≠ 0} =
      Nat.card (FixedPoints.subfield H' k) - 1 := by
    have : Fintype (FixedPoints.subfield H' k) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    simp
  have hkerle : Nat.card f.ker ≤ Nat.card (FixedPoints.subfield H' k) - 1 := by
    let g : f.ker → {x : FixedPoints.subfield H' k // x ≠ 0} := fun u =>
      ⟨⟨(u.1 : kˣ), hfix _ (hker u.1 u.2)⟩, fun h0 => u.1.ne_zero (congrArg Subtype.val h0)⟩
    have hg : Function.Injective g := by
      intro u v huv
      have := congrArg
        (fun z : {x : FixedPoints.subfield H' k // x ≠ 0} =>
          ((z.1 : FixedPoints.subfield H' k) : k)) huv
      exact Subtype.ext (Units.ext this)
    have hle := Nat.card_le_card_of_injective g hg
    rw [hsub] at hle
    exact hle
  have hrangele : Nat.card f.range ≤ Nat.card (FixedPoints.subfield H' k) - 1 := by
    have hmem : ∀ y : f.range, ((y.1 : kˣ) : k) ∈ FixedPoints.subfield H' k := by
      rintro ⟨y, u, rfl⟩
      exact hfix _ (by rw [hf]; exact h u)
    let g : f.range → {x : FixedPoints.subfield H' k // x ≠ 0} := fun y =>
      ⟨⟨((y.1 : kˣ) : k), hmem y⟩, fun h0 => y.1.ne_zero (congrArg Subtype.val h0)⟩
    have hg : Function.Injective g := by
      intro u v huv
      have := congrArg
        (fun z : {x : FixedPoints.subfield H' k // x ≠ 0} =>
          ((z.1 : FixedPoints.subfield H' k) : k)) huv
      exact Subtype.ext (Units.ext this)
    have hle := Nat.card_le_card_of_injective g hg
    rw [hsub] at hle
    exact hle
  have hunits : Nat.card kˣ = Nat.card k - 1 := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_units]
  have hcard := Subgroup.card_ker_mul_card_range f
  rw [hunits] at hcard
  have hr : 2 ≤ Nat.card (FixedPoints.subfield H' k) := Finite.one_lt_card
  obtain ⟨r', hr'⟩ : ∃ r', Nat.card (FixedPoints.subfield H' k) = r' + 1 :=
    ⟨Nat.card (FixedPoints.subfield H' k) - 1, by omega⟩
  rw [hr'] at hkerle hrangele hpow
  simp only [Nat.add_sub_cancel] at hkerle hrangele
  have hpow2 : (r' + 1) ^ 2 ≤ Nat.card k := by
    rw [hpow]
    exact Nat.pow_le_pow_right (by omega) hord
  have hprod : Nat.card f.ker * Nat.card f.range ≤ r' * r' := Nat.mul_le_mul hkerle hrangele
  have hkpos : 0 < Nat.card k := Nat.card_pos
  have hr'1 : 1 ≤ r' := by omega
  have hk1 : Nat.card k = Nat.card f.ker * Nat.card f.range + 1 := by omega
  have hsq : (r' + 1) ^ 2 = r' * r' + 2 * r' + 1 := by ring
  omega

theorem inl_comm_eq {k : Type} [Field k] (x : kˣ ⋊[ringAutUnits k] RingAut k) (u : kˣ) :
    SemidirectProduct.inl u * x * (SemidirectProduct.inl u)⁻¹ * x⁻¹ =
      SemidirectProduct.inl (u * (ringAutUnits k x.right u)⁻¹) := by
  apply SemidirectProduct.ext
  · simp only [SemidirectProduct.mul_left, SemidirectProduct.inv_left, SemidirectProduct.mul_right,
      SemidirectProduct.inv_right, SemidirectProduct.left_inl, SemidirectProduct.right_inl,
      map_inv, map_one, MulAut.one_apply, one_mul, mul_one, inv_one, map_mul]
    rw [MulAut.apply_inv_self]
    simp [mul_comm, mul_left_comm, mul_assoc]
  · simp [SemidirectProduct.mul_right, SemidirectProduct.inv_right]

section Singer

variable {G : Type} [Group G] [Finite G]

theorem commute_of_singer_comm {Z D B : Subgroup G} {e : ℕ} (he1 : 1 ≤ e)
    (hZ : IsElemAbelian 2 Z) (hZcard : Nat.card Z = 2 ^ e)
    (hBN : B ≤ Subgroup.normalizer (Z : Set G)) (hDB : D ≤ B)
    (hDnorm : ∀ b ∈ B, ∀ d ∈ D, b * d * b⁻¹ ∈ D)
    (hDcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a)
    (hDreg : ActsRegularlyOn D (nonIdentity Z)) (hDcard : Nat.card D = 2 ^ e - 1)
    {d' : G} (hd' : d' ∈ B)
    (hcomm : ∀ d ∈ D, d' * (d * d' * d⁻¹ * d'⁻¹) = (d * d' * d⁻¹ * d'⁻¹) * d') :
    ∀ d ∈ D, d * d' = d' * d := by
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
  let xB : B := ⟨d', hd'⟩
  have hright : (ι xB).right = 1 := by
    apply eq_one_of_fixed_quotient
    intro u
    obtain ⟨δ, hδX, hδu⟩ : ∃ δ ∈ X, ι δ = SemidirectProduct.inl u := by
      have : SemidirectProduct.inl u ∈ X.map ι := by rw [himage]; exact ⟨u, rfl⟩
      obtain ⟨δ, hδ, h⟩ := this
      exact ⟨δ, hδ, h⟩
    have hδD : (δ : G) ∈ D := hδX
    have hcB : (δ * xB * δ⁻¹ * xB⁻¹ : B) ∈ X := by
      have h1 : ((δ * xB * δ⁻¹ * xB⁻¹ : B) : G) = (δ : G) * (d' * (δ : G)⁻¹ * d'⁻¹) := by
        have hx : (xB : G) = d' := rfl
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hx]
        group
      show ((δ * xB * δ⁻¹ * xB⁻¹ : B) : G) ∈ D
      rw [h1]
      exact D.mul_mem hδD (by
        have := hDnorm d' hd' _ (D.inv_mem hδD)
        exact this)
    have hcom : xB * (δ * xB * δ⁻¹ * xB⁻¹) = (δ * xB * δ⁻¹ * xB⁻¹) * xB := by
      apply Subtype.ext
      have hx : (xB : G) = d' := rfl
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hx]
      exact hcomm _ hδD
    have h2 : ι (δ * xB * δ⁻¹ * xB⁻¹) = SemidirectProduct.inl (u * (ringAutUnits k₀ (ι xB).right u)⁻¹) := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hδu]
      exact inl_comm_eq (ι xB) u
    have h3 : ι xB * ι (δ * xB * δ⁻¹ * xB⁻¹) = ι (δ * xB * δ⁻¹ * xB⁻¹) * ι xB := by
      rw [← map_mul, ← map_mul, hcom]
    rw [h2] at h3
    set v : k₀ˣ := u * (ringAutUnits k₀ (ι xB).right u)⁻¹ with hv
    have h4 := congrArg SemidirectProduct.left h3
    simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl, SemidirectProduct.right_inl,
      map_one, MulAut.one_apply] at h4
    have h5 : (ringAutUnits k₀ (ι xB).right) v = v := by
      have h6 : (ι xB).left * (ringAutUnits k₀ (ι xB).right) v = (ι xB).left * v := by
        rw [h4, mul_comm]
      exact mul_left_cancel h6
    have h7 := congrArg Units.val h5
    rw [coe_ringAutUnits_apply, hv] at h7
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, coe_ringAutUnits_apply] at h7
    simpa only [div_eq_mul_inv] using h7
  intro d hd
  let dB : B := ⟨d, hDB hd⟩
  have hdX : dB ∈ X := hd
  have hιd : ι dB ∈ (SemidirectProduct.inl : k₀ˣ →* _).range := by
    rw [← himage]
    exact ⟨dB, hdX, rfl⟩
  obtain ⟨a, ha⟩ := hιd
  have hιx : ι xB = SemidirectProduct.inl (ι xB).left :=
    SemidirectProduct.ext rfl (by rw [SemidirectProduct.right_inl, hright])
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
  have hρ1 : ρ₀ ⟨d * d' * d⁻¹ * d'⁻¹, hBN (dB * xB * dB⁻¹ * xB⁻¹).2⟩ = 1 := hker1
  have hcz := (hρ₀ker _).1 hρ1
  have hyD : d * d' * d⁻¹ * d'⁻¹ ∈ D := by
    have h1 := hDnorm d' hd' d⁻¹ (D.inv_mem hd)
    have e1 : d * d' * d⁻¹ * d'⁻¹ = d * (d' * d⁻¹ * d'⁻¹) := by group
    rw [e1]
    exact D.mul_mem hd h1
  have hy1 := eq_one_of_centralizes_of_acts_regularly hZ1 hDreg hyD hcz
  have h3 : d * d' * d⁻¹ = d' := mul_inv_eq_one.1 hy1
  exact mul_inv_eq_iff_eq_mul.1 h3

end Singer

end CFSG.QuasithinUnique.Lin2
