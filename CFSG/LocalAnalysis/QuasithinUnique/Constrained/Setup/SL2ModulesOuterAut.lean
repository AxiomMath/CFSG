module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesCollapse
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesFlip
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFullAutomorphism

public section

namespace CFSG.QuasithinUnique.Setup.SL2Modules

open scoped MatrixGroups
open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField

section Schur

variable {k₀ : Type*} [Field k₀] [CharP k₀ 2] {W : Type*} [AddCommGroup W] [Module k₀ W]
  {G : Type*} [Monoid G]

theorem eq_one_of_involution_commute (ρ : Representation k₀ G W) (hirr : ρ.IsIrreducible)
    (u : (Module.End k₀ W)ˣ) (hu : u * u = 1) (hcomm : ∀ g, u.val * ρ g = ρ g * u.val) :
    u = 1 := by
  obtain ⟨hWnt, hWirr⟩ := (isIrreducible_iff ρ).mp hirr
  set δ : Module.End k₀ W := u.val - 1 with hδ
  have hu' : u.val * u.val = 1 := by rw [← Units.val_mul, hu, Units.val_one]
  have hδ2 : δ * δ = 0 := by
    have h2 : (2 : Module.End k₀ W) = 0 := two_endo k₀
    have h3 : u.val + u.val = 0 := by
      rw [← two_mul, h2, zero_mul]
    have h4 : (1 : Module.End k₀ W) + 1 = 0 := by
      rw [one_add_one_eq_two, h2]
    calc δ * δ = u.val * u.val - u.val - u.val + 1 := by
          rw [hδ]; noncomm_ring
      _ = 0 := by
          rw [hu', sub_sub, h3, sub_zero, h4]
  have hδcomm : ∀ g, δ * ρ g = ρ g * δ := by
    intro g
    rw [hδ, sub_mul, mul_sub, hcomm g, one_mul, mul_one]
  have hinv : ∀ g, ∀ w ∈ LinearMap.ker δ, ρ g w ∈ LinearMap.ker δ := by
    intro g w hw
    rw [LinearMap.mem_ker] at hw ⊢
    have := congrArg (fun f : Module.End k₀ W => f w) (hδcomm g)
    simp only [Module.End.mul_apply] at this
    rw [this, hw, map_zero]
  have hker : LinearMap.ker δ = ⊤ := by
    rcases hWirr _ hinv with h | h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hWnt
      have hz : ∀ w : W, w = 0 := by
        intro w
        have h1 : δ (δ w) = 0 := by
          have := congrArg (fun f : Module.End k₀ W => f w) hδ2
          simpa using this
        have h2 : δ w ∈ LinearMap.ker δ := by
          rw [LinearMap.mem_ker]; exact h1
        rw [h, Submodule.mem_bot] at h2
        have h3 : w ∈ LinearMap.ker δ := by
          rw [LinearMap.mem_ker]; exact h2
        rwa [h, Submodule.mem_bot] at h3
      exact hxy ((hz x).trans (hz y).symm)
    · exact h
  have hδ0 : δ = 0 := LinearMap.ker_eq_top.mp hker
  apply Units.ext
  rw [Units.val_one]
  exact sub_eq_zero.mp hδ0

end Schur

section Odd

variable {k₀ : Type*} [Field k₀] [CharP k₀ 2] {W : Type*} [AddCommGroup W] [Module k₀ W]
  {G : Type*} [Monoid G]

omit [CharP k₀ 2] in
theorem finite_units_end [Finite W] : Finite (Module.End k₀ W)ˣ := by
  have : Finite (Module.End k₀ W) :=
    Finite.of_injective (fun f : Module.End k₀ W => (f : W → W)) DFunLike.coe_injective
  infer_instance

theorem odd_orderOf_of_commute [Finite W] (ρ : Representation k₀ G W) (hirr : ρ.IsIrreducible)
    (c : (Module.End k₀ W)ˣ) (hcomm : ∀ g, c.val * ρ g = ρ g * c.val) : Odd (orderOf c) := by
  have := finite_units_end (k₀ := k₀) (W := W)
  have hpos : 0 < orderOf c := orderOf_pos c
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  obtain ⟨o', ho'⟩ := hodd
  have hpow : (c ^ o') * (c ^ o') = 1 := by
    rw [← pow_add, ← ho']
    exact pow_orderOf_eq_one c
  have hcomm' : ∀ g, (c ^ o').val * ρ g = ρ g * (c ^ o').val := by
    intro g
    rw [Units.val_pow_eq_pow_val]
    exact (Commute.pow_left (hcomm g) o')
  have h1 : c ^ o' = 1 := eq_one_of_involution_commute ρ hirr (c ^ o') hpow hcomm'
  have h2 : orderOf c ∣ o' := orderOf_dvd_of_pow_eq_one h1
  have h3 := Nat.le_of_dvd (by omega) h2
  omega

theorem mem_of_commute_of_sq_mem [Finite W] (ρ : Representation k₀ G W) (hirr : ρ.IsIrreducible)
    (L : Subgroup (Module.End k₀ W)ˣ) (c : (Module.End k₀ W)ˣ)
    (hcomm : ∀ g, c.val * ρ g = ρ g * c.val) (hc2 : c * c ∈ L) : c ∈ L := by
  obtain ⟨j, hj⟩ := odd_orderOf_of_commute ρ hirr c hcomm
  have hc : c = (c * c) ^ (j + 1) := by
    calc c = c ^ (orderOf c + 1) := by rw [pow_succ, pow_orderOf_eq_one, one_mul]
      _ = (c * c) ^ (j + 1) := by
        rw [hj, ← pow_two, ← pow_mul]
        congr 1
  rw [hc]
  exact L.pow_mem hc2 _

end Odd

section Translation

variable {F : Type*} [Field F] {H : Type*} [Group H] (ρU : SL(2, F) →* H)
  (hρ : Function.Injective ρU)

@[expose] noncomputable def autHom :
    ↥(Subgroup.normalizer (ρU.range : Set H)) →* MulAut SL(2, F) :=
  (MulAut.congr (MonoidHom.ofInjective hρ).symm).toMonoidHom.comp ρU.range.normalizerMonoidHom

theorem rho_autHom (n : ↥(Subgroup.normalizer (ρU.range : Set H))) (g : SL(2, F)) :
    ρU (autHom ρU hρ n g) = (n : H) * ρU g * (n : H)⁻¹ := by
  simp only [autHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
    MulEquiv.trans_apply, MulEquiv.symm_symm]
  rw [MonoidHom.apply_ofInjective_symm]
  rfl

theorem autHom_eq_iff (n : ↥(Subgroup.normalizer (ρU.range : Set H))) (f : MulAut SL(2, F)) :
    autHom ρU hρ n = f ↔ ∀ h, (n : H) * ρU h * (n : H)⁻¹ = ρU (f h) := by
  constructor
  · rintro rfl h
    exact (rho_autHom ρU hρ n h).symm
  · intro hf
    refine MulEquiv.ext fun h => ?_
    apply hρ
    rw [rho_autHom, hf]

end Translation

section Outer

variable {F : Type*} [Field F] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
  (ρ : Representation (ZMod 2) SL(2, F) W) (hirr : ρ.IsIrreducible)
  (hρ : Function.Injective ρ.toHomUnits)

include hirr in
theorem mem_range_of_autHom_eq_conj (a : (Module.End (ZMod 2) W)ˣ)
    (ha : a ∈ Subgroup.normalizer (ρ.toHomUnits.range : Set (Module.End (ZMod 2) W)ˣ))
    (ha2 : a * a = 1) (g : SL(2, F)) (h : autHom ρ.toHomUnits hρ ⟨a, ha⟩ = MulAut.conj g) :
    a ∈ ρ.toHomUnits.range := by
  have hconj := (autHom_eq_iff ρ.toHomUnits hρ ⟨a, ha⟩ (MulAut.conj g)).mp h
  set ρU := ρ.toHomUnits with hρU
  set c := (ρU g)⁻¹ * a with hc
  have hcomm : ∀ h, c * ρU h = ρU h * c := by
    intro h
    have := hconj h
    simp only [MulAut.conj_apply, map_mul, map_inv] at this
    calc (ρU g)⁻¹ * a * ρU h = (ρU g)⁻¹ * (a * ρU h * a⁻¹) * a := by group
      _ = (ρU g)⁻¹ * (ρU g * ρU h * (ρU g)⁻¹) * a := by rw [this]
      _ = ρU h * ((ρU g)⁻¹ * a) := by group
  have hcommEnd : ∀ h, c.val * ρ h = ρ h * c.val := by
    intro h
    have := congrArg Units.val (hcomm h)
    simpa [hρU] using this
  have hcg : c * ρU g = ρU g * c := hcomm g
  have hasq : a = ρU g * c := by simp [hc]
  have hcc : c * c = (ρU g * ρU g)⁻¹ := by
    have h1 : (ρU g * c) * (ρU g * c) = 1 := by rw [← hasq]; exact ha2
    have h2 : ρU g * ρU g * (c * c) = 1 := by
      calc ρU g * ρU g * (c * c) = ρU g * (ρU g * c) * c := by group
        _ = ρU g * (c * ρU g) * c := by rw [hcg]
        _ = (ρU g * c) * (ρU g * c) := by group
        _ = 1 := h1
    exact eq_inv_of_mul_eq_one_right h2
  have hccmem : c * c ∈ ρU.range := by
    rw [hcc]
    exact ρU.range.inv_mem (ρU.range.mul_mem ⟨g, rfl⟩ ⟨g, rfl⟩)
  have hcmem : c ∈ ρU.range := mem_of_commute_of_sq_mem ρ hirr ρU.range c hcommEnd hccmem
  rw [hasq]
  exact ρU.range.mul_mem ⟨g, rfl⟩ hcmem

omit [Finite W] in
include hirr in
theorem eq_one_of_autHom_eq_one (a : (Module.End (ZMod 2) W)ˣ)
    (ha : a ∈ Subgroup.normalizer (ρ.toHomUnits.range : Set (Module.End (ZMod 2) W)ˣ))
    (ha2 : a * a = 1) (h : autHom ρ.toHomUnits hρ ⟨a, ha⟩ = 1) : a = 1 := by
  have hconj := (autHom_eq_iff ρ.toHomUnits hρ ⟨a, ha⟩ 1).mp h
  apply eq_one_of_involution_commute ρ hirr a ha2
  intro g
  have := hconj g
  have h2 : a * ρ.toHomUnits g = ρ.toHomUnits g * a := by
    calc a * ρ.toHomUnits g = (a * ρ.toHomUnits g * a⁻¹) * a := by group
      _ = ρ.toHomUnits g * a := by rw [this]; rfl
  have := congrArg Units.val h2
  simpa using this

end Outer

section Gamma

variable {F : Type*} [Field F] {n : ℕ}

@[expose] noncomputable def toGamma (hn : 1 ≤ n) (hcard : Nat.card F = 2 ^ n) {H : Type*} [Group H]
    (ρU : SL(2, F) →* H) (hρ : Function.Injective ρU) :
    ↥(Subgroup.normalizer (ρU.range : Set H)) →* Gamma F :=
  (gammaEquivMulAut hn hcard).symm.toMonoidHom.comp (autHom ρU hρ)

theorem gammaToMulAut_toGamma (hn : 1 ≤ n) (hcard : Nat.card F = 2 ^ n) {H : Type*} [Group H]
    (ρU : SL(2, F) →* H) (hρ : Function.Injective ρU)
    (m : ↥(Subgroup.normalizer (ρU.range : Set H))) :
    gammaToMulAut F (toGamma hn hcard ρU hρ m) = autHom ρU hρ m :=
  (gammaEquivMulAut hn hcard).apply_symm_apply (autHom ρU hρ m)

end Gamma

section Main

variable {F : Type*} [Field F] [Finite F] [CharP F 2] {W : Type*} [AddCommGroup W]
  [Module (ZMod 2) W] [Finite W]

theorem outer_data {n : ℕ} (hn : 1 ≤ n) (hcard : Nat.card F = 2 ^ n)
    (ρ : Representation (ZMod 2) SL(2, F) W) (hirr : ρ.IsIrreducible)
    (hρ : Function.Injective ρ.toHomUnits)
    (A : Subgroup (Module.End (ZMod 2) W)ˣ) [CFSG.IsElementaryAbelian 2 A]
    (hAN : A ≤ Subgroup.normalizer (ρ.toHomUnits.range : Set (Module.End (ZMod 2) W)ˣ))
    (hAL : ¬ A ≤ ρ.toHomUnits.range) :
    ∃ s : ℕ, 1 ≤ s ∧ n = 2 * s ∧ Nat.card A ≤ 2 ^ (s + 1) ∧
      ((∀ b ∈ A, b ∈ ρ.toHomUnits.range → b = 1) → Nat.card A = 2) ∧
      ∃ a ∈ A, a ∉ ρ.toHomUnits.range ∧ ∃ x : SL(2, F),
        ∀ g, ((ρ.toHomUnits x)⁻¹ * a * ρ.toHomUnits x) * ρ.toHomUnits g *
          ((ρ.toHomUnits x)⁻¹ * a * ρ.toHomUnits x)⁻¹ = ρ.toHomUnits (fieldAut F s g) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρU := ρ.toHomUnits with hρU
  let cN := toGamma hn hcard ρU hρ
  let cA : ↥A →* Gamma F := cN.comp (Subgroup.inclusion hAN)
  have hcA_val : ∀ a : ↥A, gammaToMulAut F (cA a) = autHom ρU hρ ⟨a, hAN a.2⟩ := fun a =>
    gammaToMulAut_toGamma hn hcard ρU hρ ⟨a, hAN a.2⟩
  have hsq : ∀ a : ↥A, (a : (Module.End (ZMod 2) W)ˣ) * a = 1 := by
    intro a
    have := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (CFSG.IsElementaryAbelian.exponent_dvd_p 2 A) a
    have h2 : a * a = 1 := by rw [← pow_two]; exact this
    exact congrArg Subtype.val h2
  have hinj : Function.Injective cA := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : autHom ρU hρ ⟨a, hAN a.2⟩ = 1 := by rw [← hcA_val a, ha, map_one]
    exact Subtype.ext (eq_one_of_autHom_eq_one ρ hirr hρ a (hAN a.2) (hsq a) h1)
  have hlin : ∀ a : ↥A, cA a ∈ linearKernel F ↔ (a : (Module.End (ZMod 2) W)ˣ) ∈ ρU.range := by
    intro a
    constructor
    · intro h
      rw [mem_linearKernel_iff] at h
      have hg : cA a = SemidirectProduct.inl (cA a).left :=
        SemidirectProduct.ext (by simp) (by simp [h])
      have h1 : autHom ρU hρ ⟨a, hAN a.2⟩ = MulAut.conj (cA a).left := by
        rw [← hcA_val a, hg, gammaToMulAut_inl]
        simp
      exact mem_range_of_autHom_eq_conj ρ hirr hρ a (hAN a.2) (hsq a) _ h1
    · rintro ⟨g, hg⟩
      have h1 : autHom ρU hρ ⟨a, hAN a.2⟩ = MulAut.conj g := by
        refine (autHom_eq_iff ρU hρ ⟨a, hAN a.2⟩ (MulAut.conj g)).mpr fun h => ?_
        rw [← hg]
        simp
      have h2 : cA a = SemidirectProduct.inl g := by
        apply (gammaToMulAut_bijective_of_card hcard).1
        rw [hcA_val a, h1, gammaToMulAut_inl]
      rw [mem_linearKernel_iff, h2]
      simp
  have hA'ea : CFSG.IsElementaryAbelian 2 cA.range := by
    refine { toIsMulCommutative := ⟨⟨fun x y => ?_⟩⟩, exponent_dvd_p := ?_ }
    · obtain ⟨a, ha⟩ := x.2
      obtain ⟨b, hb⟩ := y.2
      apply Subtype.ext
      show (x : Gamma F) * y = y * x
      have hab : a * b = b * a := (inferInstance : IsMulCommutative ↥A).is_comm.comm a b
      rw [← ha, ← hb, ← map_mul, ← map_mul, hab]
    · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x => ?_
      obtain ⟨a, ha⟩ := x.2
      apply Subtype.ext
      have h2 : a ^ 2 = 1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (CFSG.IsElementaryAbelian.exponent_dvd_p 2 A) a
      show (x : Gamma F) ^ 2 = 1
      rw [← ha, ← map_pow, h2, map_one]
  have houter : ¬ cA.range ≤ linearKernel F := by
    intro h
    apply hAL
    intro a ha
    exact (hlin ⟨a, ha⟩).mp (h ⟨⟨a, ha⟩, rfl⟩)
  obtain ⟨-, hper⟩ := (original_even_SL2_outer_involution_field_conjugacy_and_rank hn hcard).2
    cA.range hA'ea houter
  obtain ⟨a, haA, haL⟩ := Set.not_subset.mp hAL
  have hā : cA ⟨a, haA⟩ ∈ cA.range := ⟨⟨a, haA⟩, rfl⟩
  have hāout : cA ⟨a, haA⟩ ∉ linearKernel F := fun h => haL ((hlin ⟨a, haA⟩).mp h)
  obtain ⟨s, hs1, hns, hfrob, -, ⟨x, hx, -⟩, -, hAc, -, hAle, -⟩ := hper _ hā hāout
  have hcardA : Nat.card cA.range = Nat.card A :=
    Nat.card_congr (MonoidHom.ofInjective hinj).symm.toEquiv
  refine ⟨s, hs1, hns, hcardA ▸ hAle, ?_, a, haA, haL, x, ?_⟩
  · intro hB
    have hbot : linearIntersection cA.range = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro y hy
      have hy' : (y : Gamma F) ∈ linearKernel F := by
        have := (Subgroup.mem_subgroupOf.mp hy)
        exact (Subgroup.mem_inf.mp this).2
      obtain ⟨b, hb⟩ := y.2
      have hbL := (hlin b).mp (by rw [hb]; exact hy')
      have hb1 : (b : (Module.End (ZMod 2) W)ˣ) = 1 := hB b b.2 hbL
      have hb1' : b = 1 := Subtype.ext hb1
      apply Subtype.ext
      rw [← hb, hb1', map_one]
      rfl
    have h2 : Nat.card cA.range = 2 * Nat.card (linearIntersection cA.range) := hAc
    rw [hbot, Subgroup.card_bot] at h2
    omega
  · intro g
    set ā := cA ⟨a, haA⟩ with hādef
    have hcA' : gammaToMulAut F ā = autHom ρU hρ ⟨a, hAN haA⟩ := hcA_val ⟨a, haA⟩
    have hσ : ā.right.toRingHom = iterateFrobenius F 2 s := by
      ext c
      simp [hfrob c, iterateFrobenius_def]
    have hα : ∀ h, autHom ρU hρ ⟨a, hAN haA⟩ h = x * fieldAut F s (x⁻¹ * h * x) * x⁻¹ := by
      intro h
      have h1 : autHom ρU hρ ⟨a, hAN haA⟩ h = gammaToMulAut F ā h := by rw [hcA']
      rw [h1, hx]
      simp only [map_mul, map_inv, gammaToMulAut_inl, gammaToMulAut_inr, MulAut.mul_apply,
        MulAut.conj_apply, MulAut.inv_apply, sl2FieldAction_apply, hσ]
      rw [MulAut.conj_symm_apply]
      change x * fieldAut F s (x⁻¹ * h * x) * x⁻¹ = _
      simp only [map_mul, map_inv]
    have key : a * ρU (x * g * x⁻¹) * a⁻¹ = ρU x * ρU (fieldAut F s g) * (ρU x)⁻¹ := by
      have h2 := rho_autHom ρU hρ ⟨a, hAN haA⟩ (x * g * x⁻¹)
      rw [hα] at h2
      have e : x⁻¹ * (x * g * x⁻¹) * x = g := by group
      rw [e, map_mul, map_mul, map_inv] at h2
      exact h2.symm
    have hmain : ((ρU x)⁻¹ * a * ρU x) * ρU g * ((ρU x)⁻¹ * a * ρU x)⁻¹ =
        (ρU x)⁻¹ * (a * ρU (x * g * x⁻¹) * a⁻¹) * ρU x := by
      simp only [map_mul, map_inv]
      group
    rw [hmain, key]
    group

end Main

end CFSG.QuasithinUnique.Setup.SL2Modules
