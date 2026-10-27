module

public import CFSG.Goldschmidt.Steps.G2Lin
public import CFSG.Goldschmidt.Steps.G2Cyc
public import CFSG.LinearAlgebra.LinearGroups.CyclicSylowIndexTwo

public section

namespace CFSG.Goldschmidt.G2

open Module CFSG.QuasithinUnique
open scoped Pointwise

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem odd_of_add_one_eq_two_pow {c r : ℕ} (hr : 1 ≤ r) (h : c + 1 = 2 ^ r) : Odd c := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  have h1 : 1 ≤ 2 ^ r' := Nat.one_le_two_pow
  rw [pow_succ] at h
  exact ⟨2 ^ r' - 1, by omega⟩

theorem odd_card_nonzero {S : Submodule (ZMod 2) V} (hS : S ≠ ⊥) :
    Odd (Nat.card {v : V // v ∈ S ∧ v ≠ 0}) := by
  have h1 := card_nonzero_add_one S
  rw [ONan.natCard_submodule] at h1
  exact odd_of_add_one_eq_two_pow (Submodule.one_le_finrank_iff.mpr hS) h1

omit [Finite V] in
theorem exists_fixed_of_odd {P : Subgroup (V ≃ₗ[ZMod 2] V)} (hP : IsPGroup 2 P) (s : Set V)
    (hs : ∀ p ∈ P, ∀ v ∈ s, p v ∈ s) (hodd : Odd (Nat.card s)) :
    ∃ v ∈ s, ∀ p ∈ P, p v = v := by
  let _ : MulAction P s :=
    { smul := fun p v => ⟨(p : V ≃ₗ[ZMod 2] V) v, hs p p.2 v v.2⟩
      one_smul := fun v => Subtype.ext rfl
      mul_smul := fun p q v => Subtype.ext rfl }
  obtain ⟨⟨v, hv⟩, hfix⟩ := IsPGroup.nonempty_fixed_point_of_prime_not_dvd_card hP s
    (by rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.mpr hodd)
  refine ⟨v, hv, fun p hp => ?_⟩
  have := MulAction.mem_fixedPoints.mp hfix ⟨p, hp⟩
  exact congrArg Subtype.val this

@[expose] noncomputable def restrictHom (D : Submodule (ZMod 2) V) :
    MulAction.stabilizer (V ≃ₗ[ZMod 2] V) D →* (D ≃ₗ[ZMod 2] D) where
  toFun g := (g : V ≃ₗ[ZMod 2] V).ofSubmodules D D (MulAction.mem_stabilizer_iff.mp g.2)
  map_one' := by
    ext v
    simp
  map_mul' g g' := by
    ext v
    rfl

omit [Finite V] in
theorem restrictHom_apply (D : Submodule (ZMod 2) V)
    (g : MulAction.stabilizer (V ≃ₗ[ZMod 2] V) D) (v : D) :
    ((restrictHom D g v : D) : V) = (g : V ≃ₗ[ZMod 2] V) v := rfl

omit [Finite V] in
theorem smul_eq_of_sq_smul_eq {Ω : Type*} {X : Subgroup (V ≃ₗ[ZMod 2] V)} [MulAction X Ω]
    (hodd : Odd (Nat.card X)) (g : X) (S : Ω) (h2 : g • g • S = S) : g • S = S := by
  have hord : Odd (orderOf g) := Odd.of_dvd_nat hodd (orderOf_dvd_natCard g)
  obtain ⟨t, ht⟩ := hord
  have hg2 : g ^ 2 • S = S := by rw [pow_two, mul_smul, h2]
  have hsq : ∀ n : ℕ, (g ^ 2) ^ n • S = S := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, mul_smul, hg2, ih]
  have h1 : g ^ (2 * t + 1) = 1 := by rw [← ht]; exact pow_orderOf_eq_one g
  calc g • S = g • (g ^ 2) ^ t • S := by rw [hsq]
    _ = g ^ (2 * t + 1) • S := by rw [← mul_smul, ← pow_mul, ← pow_succ']
    _ = S := by rw [h1, one_smul]

namespace LinHyp

variable {X : Subgroup (V ≃ₗ[ZMod 2] V)} {η : V ≃ₗ[ZMod 2] V} (h : LinHyp X η)
include h

theorem apply_mem_comSp_of_normalizes {x : V ≃ₗ[ZMod 2] V}
    (hx : x * η * x⁻¹ ∈ Subgroup.zpowers η) {d : V} (hd : d ∈ comSp η) : x d ∈ comSp η := by
  obtain ⟨u, rfl⟩ := mem_comSp.mp hd
  have hxe : x * η = (x * η * x⁻¹) * x := by group
  have h1 : x (η u - u) = (x * η * x⁻¹) (x u) - x u := by
    rw [map_sub]
    congr 1
    have := congrArg (fun f : V ≃ₗ[ZMod 2] V => f u) hxe
    simpa only [LinearEquiv.mul_apply] using this
  rw [h1]
  exact h.sub_mem_comSp hx _

theorem smul_comSp_of_normalizes {x : V ≃ₗ[ZMod 2] V} (hx : x * η * x⁻¹ ∈ Subgroup.zpowers η) :
    x • comSp η = comSp η := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨d, hd, rfl⟩
    exact h.apply_mem_comSp_of_normalizes hx hd
  · exact ONan.finrank_smul x _

theorem isCyclic_of_isPGroup
    (hnorm : ∀ x ∈ X, x • fixSp η = fixSp η → x * η * x⁻¹ ∈ Subgroup.zpowers η)
    (htr : ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃ x ∈ X, x v = w)
    (hcase : ∀ x ∈ X, x • fixSp η ⊓ comSp η ≠ ⊥ → x • fixSp η ≤ comSp η)
    {P : Subgroup (V ≃ₗ[ZMod 2] V)} (hPX : P ≤ X) (hP : IsPGroup 2 P) {w₀ : V}
    (hw₀ : w₀ ∈ fixSp η) (hw₀0 : w₀ ≠ 0) (hPw : ∀ p ∈ P, p w₀ = w₀) : IsCyclic P := by
  classical
  have hPW : ∀ p ∈ P, p • fixSp η = fixSp η := by
    intro p hp
    have hne : p • fixSp η ⊓ (1 : V ≃ₗ[ZMod 2] V) • fixSp η ≠ ⊥ := by
      intro hbot
      have hmem : w₀ ∈ p • fixSp η ⊓ (1 : V ≃ₗ[ZMod 2] V) • fixSp η := by
        refine Submodule.mem_inf.mpr ⟨?_, by rw [one_smul]; exact hw₀⟩
        rw [← hPw p hp]
        exact Submodule.smul_mem_pointwise_smul _ _ _ hw₀
      rw [hbot, Submodule.mem_bot] at hmem
      exact hw₀0 hmem
    have := h.smul_eq_of_inf_ne_bot (hPX hp) X.one_mem hne
    rwa [one_smul] at this
  have hPnorm : ∀ p ∈ P, p * η * p⁻¹ ∈ Subgroup.zpowers η :=
    fun p hp => hnorm p (hPX hp) (hPW p hp)
  have hPD : ∀ p ∈ P, ∀ d ∈ comSp η, p d ∈ comSp η :=
    fun p hp d hd => h.apply_mem_comSp_of_normalizes (hPnorm p hp) hd
  have hPWv : ∀ p ∈ P, ∀ w ∈ fixSp η, p w ∈ fixSp η := by
    intro p hp w hw
    rw [← hPW p hp]
    exact Submodule.smul_mem_pointwise_smul _ _ _ hw
  have hodd1 : Odd (Nat.card {v : V // v ∉ fixSp η ∧ v ∉ comSp η}) := by
    rw [h.card_compl]
    exact (odd_card_nonzero h.comSp_ne_bot).mul (odd_card_nonzero h.fixSp_ne_bot)
  obtain ⟨v₁, ⟨hv₁W, hv₁D⟩, hv₁⟩ := exists_fixed_of_odd hP {v | v ∉ fixSp η ∧ v ∉ comSp η}
    (by
      rintro p hp v ⟨hvW, hvD⟩
      refine ⟨fun h1 => hvW ?_, fun h1 => hvD ?_⟩
      · have := hPWv p⁻¹ (P.inv_mem hp) _ h1
        simpa using this
      · have := hPD p⁻¹ (P.inv_mem hp) _ h1
        simpa using this) hodd1
  have hv₁0 : v₁ ≠ 0 := fun h0 => hv₁W (h0 ▸ (fixSp η).zero_mem)
  obtain ⟨x₁, hx₁, hx₁w⟩ := htr w₀ v₁ hw₀0 hv₁0
  have hv₁S : v₁ ∈ x₁ • fixSp η := by
    rw [← hx₁w]
    exact Submodule.smul_mem_pointwise_smul _ _ _ hw₀
  have hPS : ∀ p ∈ P, p • (x₁ • fixSp η) = x₁ • fixSp η := by
    intro p hp
    rw [← mul_smul]
    refine h.smul_eq_of_inf_ne_bot (X.mul_mem (hPX hp) hx₁) hx₁ fun hbot => hv₁0 ?_
    have hmem : v₁ ∈ (p * x₁) • fixSp η ⊓ x₁ • fixSp η := by
      refine Submodule.mem_inf.mpr ⟨?_, hv₁S⟩
      rw [mul_smul, ← hv₁ p hp]
      exact Submodule.smul_mem_pointwise_smul _ _ _ hv₁S
    rwa [hbot, Submodule.mem_bot] at hmem
  have hSD : x₁ • fixSp η ⊓ comSp η = ⊥ := by
    by_contra hne
    exact hv₁D (hcase x₁ hx₁ hne hv₁S)
  have hSW : x₁ • fixSp η ⊓ fixSp η = ⊥ := by
    apply h.ti x₁ hx₁
    intro heq
    apply hv₁W
    rw [← heq]
    exact hv₁S
  have hcompl : IsCompl (x₁ • fixSp η) (comSp η) := by
    rw [Submodule.isCompl_iff_disjoint]
    · exact disjoint_iff.mpr hSD
    · rw [ONan.finrank_smul, add_comm, Submodule.finrank_add_eq_of_isCompl h.isCompl]
  have hfaith : ∀ p ∈ P, (∀ d ∈ comSp η, p d = d) → p = 1 := by
    intro p hp hpD
    ext v
    obtain ⟨d, hd, w, hw, rfl⟩ := h.exists_add v
    have hw' : p w = w := by
      have hwmem : w ∈ x₁ • fixSp η ⊔ comSp η := hcompl.sup_eq_top ▸ Submodule.mem_top
      obtain ⟨s, hs, d', hd', hsd⟩ := Submodule.mem_sup.mp hwmem
      have h1 : p w - w = p s - s := by
        rw [← hsd, map_add, hpD d' hd']
        abel
      have hps : p s ∈ x₁ • fixSp η := by
        rw [← hPS p hp]
        exact Submodule.smul_mem_pointwise_smul _ _ _ hs
      have h2 : p w - w ∈ x₁ • fixSp η ⊓ fixSp η :=
        Submodule.mem_inf.mpr ⟨h1 ▸ (x₁ • fixSp η).sub_mem hps hs,
          (fixSp η).sub_mem (hPWv p hp w hw) hw⟩
      rw [hSW, Submodule.mem_bot, sub_eq_zero] at h2
      exact h2
    rw [map_add, hpD d hd, hw', LinearEquiv.coe_one, id]
  obtain ⟨d₀, ⟨hd₀D, hd₀0⟩, hd₀⟩ := exists_fixed_of_odd hP {v | v ∈ comSp η ∧ v ≠ 0}
    (by
      rintro p hp v ⟨hvD, hv0⟩
      exact ⟨hPD p hp v hvD, fun h0 => hv0 (by simpa using congrArg (p : V ≃ₗ[ZMod 2] V).symm h0)⟩)
    (odd_card_nonzero h.comSp_ne_bot)
  have hηD : η ∈ MulAction.stabilizer (V ≃ₗ[ZMod 2] V) (comSp η) :=
    MulAction.mem_stabilizer_iff.mpr (h.smul_comSp_of_normalizes (by simp))
  have hPstab : P ≤ MulAction.stabilizer (V ≃ₗ[ZMod 2] V) (comSp η) :=
    fun p hp => MulAction.mem_stabilizer_iff.mpr (h.smul_comSp_of_normalizes (hPnorm p hp))
  let τ : P →* (comSp η ≃ₗ[ZMod 2] comSp η) :=
    (restrictHom (comSp η)).comp (Subgroup.inclusion hPstab)
  have hτ : ∀ (p : P) (d : comSp η), ((τ p d : comSp η) : V) = (p : V ≃ₗ[ZMod 2] V) d :=
    fun _ _ => rfl
  have hτinj : Function.Injective τ := by
    rw [injective_iff_map_eq_one]
    intro p hp
    apply Subtype.ext
    apply hfaith p p.2
    intro d hd
    have := congrArg (fun f : comSp η ≃ₗ[ZMod 2] comSp η => ((f ⟨d, hd⟩ : comSp η) : V)) hp
    simpa [hτ] using this
  set ζ := restrictHom (comSp η) ⟨η, hηD⟩ with hζ
  have hζpow : ∀ (i : ℕ) (d : comSp η), (((ζ ^ i) d : comSp η) : V) = (η ^ i) d := by
    intro i d
    rw [hζ, ← map_pow, restrictHom_apply]
    rfl
  have hcycR : IsCyclic τ.range := by
    refine isCyclic_of_normalizes_regular ζ (d₀ := ⟨d₀, hd₀D⟩)
      (fun h0 => hd₀0 (congrArg Subtype.val h0)) ?_ τ.range ?_ ?_
    · intro v hv
      have hv0 : (v : V) ≠ 0 := fun h0 => hv (Subtype.ext h0)
      obtain ⟨i, hi⟩ := h.trans d₀ hd₀D v v.2 hd₀0 hv0
      exact ⟨i, Subtype.ext (by rw [hζpow]; exact hi)⟩
    · rintro _ ⟨p, rfl⟩
      obtain ⟨i, hi⟩ := exists_pow_eq_of_mem_zpowers (hPnorm p p.2)
      refine ⟨i, LinearEquiv.ext fun d => Subtype.ext ?_⟩
      rw [hζpow, hi]
      simp only [LinearEquiv.mul_apply]
      rw [hτ, LinearEquiv.coe_inv]
      simp only [hζ, restrictHom_apply]
      rfl
    · rintro _ ⟨p, rfl⟩
      exact Subtype.ext (by rw [hτ]; exact hd₀ p p.2)
  exact isCyclic_of_injective τ.rangeRestrict (MonoidHom.rangeRestrict_injective_iff.mpr hτinj)

theorem odd_card
    (hidx : ∀ X₀ : Subgroup (V ≃ₗ[ZMod 2] V), X₀ ≤ X → (X₀.subgroupOf X).index ≠ 2)
    (hnorm : ∀ x ∈ X, x • fixSp η = fixSp η → x * η * x⁻¹ ∈ Subgroup.zpowers η)
    (htr : ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃ x ∈ X, x v = w)
    (hcase : ∀ x ∈ X, x • fixSp η ⊓ comSp η ≠ ⊥ → x • fixSp η ≤ comSp η) :
    Odd (Nat.card X) := by
  classical
  have : Finite X := ONan.finite_subgroup X
  let _ : Fintype X := Fintype.ofFinite X
  by_contra hodd
  have heven : Even (Fintype.card X) := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.not_odd_iff_even.mp hodd
  obtain ⟨P₀⟩ : Nonempty (Sylow 2 X) := inferInstance
  set P₁ := (P₀ : Subgroup X).map X.subtype with hP₁def
  have hP₁ : IsPGroup 2 P₁ := P₀.isPGroup'.map _
  have hV : (⊤ : Submodule (ZMod 2) V) ≠ ⊥ := by
    intro h0
    apply h.fixSp_ne_bot
    rw [eq_bot_iff, ← h0]
    exact le_top
  obtain ⟨v₀, ⟨-, hv₀0⟩, hv₀⟩ :=
    exists_fixed_of_odd hP₁ {v | v ∈ (⊤ : Submodule (ZMod 2) V) ∧ v ≠ 0}
      (by
        rintro p hp v ⟨-, hv0⟩
        refine ⟨Submodule.mem_top, fun h0 => hv0 ?_⟩
        simpa using congrArg (p : V ≃ₗ[ZMod 2] V).symm h0)
      (odd_card_nonzero hV)
  obtain ⟨w₀, hw₀, hw₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h.fixSp_ne_bot
  obtain ⟨x, hx, hxv⟩ := htr v₀ w₀ hv₀0 hw₀0
  set P := P₁.map (MulAut.conj x).toMonoidHom with hPdef
  have hP : IsPGroup 2 P := hP₁.map _
  have hPX : P ≤ X := by
    rintro _ ⟨p, hp, rfl⟩
    have hpX : p ∈ X := Subgroup.map_subtype_le _ hp
    simpa using X.mul_mem (X.mul_mem hx hpX) (X.inv_mem hx)
  have hPw : ∀ p ∈ P, p w₀ = w₀ := by
    rintro _ ⟨p, hp, rfl⟩
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply,
      LinearEquiv.mul_apply]
    rw [← hxv, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply, hv₀ p hp]
  have hcycP := h.isCyclic_of_isPGroup hnorm htr hcase hPX hP hw₀ hw₀0 hPw
  have hcyc₁ : IsCyclic P₁ := isCyclic_of_injective
    (P₁.equivMapOfInjective (MulAut.conj x).toMonoidHom (MulAut.conj x).injective).toMonoidHom
    (MulEquiv.injective _)
  have hcyc₀ : IsCyclic (P₀ : Subgroup X) := isCyclic_of_injective
    ((P₀ : Subgroup X).equivMapOfInjective X.subtype X.subtype_injective).toMonoidHom
    (MulEquiv.injective _)
  have key := CFSG.LinearGroups.cyclic_sylow_index_two heven P₀ hcyc₀
  obtain ⟨-, -, -, hker⟩ := key
  apply hidx ((Equiv.Perm.sign.comp (MulAction.toPermHom X X)).ker.map X.subtype)
    (Subgroup.map_subtype_le _)
  rw [show ((Equiv.Perm.sign.comp (MulAction.toPermHom X X)).ker.map X.subtype).subgroupOf X =
    (Equiv.Perm.sign.comp (MulAction.toPermHom X X)).ker from
      Subgroup.comap_map_eq_self_of_injective X.subtype_injective _]
  exact hker

end LinHyp

end CFSG.Goldschmidt.G2
