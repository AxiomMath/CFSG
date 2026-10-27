module

public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.TransitivityInputs
public import CFSG.GroupTheory.ABGDGroups.LinearSignalizers
public import CFSG.GroupTheory.DihedralTwoClassFusion
public import CFSG.GroupTheory.DihedralTwoClassFusionSupport
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAReciprocalFusion
public import CFSG.GroupTheory.ABGLocalTools.PStabilityRelative

public section

namespace CFSG.ABGTheoremB.TotallyInverted.Inputs

open CFSG.QuasiDihedralFusion CFSG.GorensteinWalter CFSG.ABGDGroups

theorem exists_conj_eq_of_odd_orderOf_mul {X : Type*} [Group X] {a w : X} (ha : a * a = 1)
    (hw : w * w = 1) (ho : Odd (orderOf (a * w))) :
    ∃ u ∈ Subgroup.zpowers (a * w), u * w * u⁻¹ = a := by
  set o := a * w with ho_def
  obtain ⟨k, hk⟩ := ho
  set u := o ^ (k + 1) with hu_def
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
  have hu2 : u ^ 2 = o := by
    rw [hu_def, ← pow_mul, show (k + 1) * 2 = orderOf o + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  have hao : a * o * a⁻¹ = o⁻¹ := by
    rw [ho_def, mul_inv_rev, hainv, hwinv, ← mul_assoc, ha, one_mul]
  have hau : a * u * a⁻¹ = u⁻¹ := by
    rw [hu_def, ← inv_pow, ← hao]
    exact (conj_pow).symm
  refine ⟨u, Subgroup.pow_mem _ (Subgroup.mem_zpowers o) _, ?_⟩
  have hw' : w = a * o := by rw [ho_def, ← mul_assoc, ha, one_mul]
  have hua : u * a = a * u⁻¹ := by
    have h1 : a * u⁻¹ * a⁻¹ = u := by
      calc a * u⁻¹ * a⁻¹ = (a * u * a⁻¹)⁻¹ := by group
        _ = u := by rw [hau, inv_inv]
    calc u * a = a * u⁻¹ * a⁻¹ * a := by rw [h1]
      _ = a * u⁻¹ := by group
  rw [hw', ← hu2]
  calc u * (a * u ^ 2) * u⁻¹ = (u * a) * u ^ 2 * u⁻¹ := by group
    _ = a * u⁻¹ * u ^ 2 * u⁻¹ := by rw [hua]
    _ = a := by group

section Lift

variable {K Q : Type*} [Group K] [Group Q] {π : K →* Q}

theorem odd_orderOf_of_mem_ker [Finite K] (hodd : Odd (Nat.card π.ker)) {o : K}
    (ho : o ∈ π.ker) : Odd (orderOf o) := by
  have h := orderOf_dvd_natCard (⟨o, ho⟩ : π.ker)
  rw [Subgroup.orderOf_mk] at h
  exact hodd.of_dvd_nat h

omit [Group Q] in
theorem conj_mul_self_eq_one {g τ : K} (hτ : τ * τ = 1) :
    (g * τ * g⁻¹) * (g * τ * g⁻¹) = 1 := by
  calc (g * τ * g⁻¹) * (g * τ * g⁻¹) = g * (τ * τ) * g⁻¹ := by group
    _ = 1 := by rw [hτ, mul_one, mul_inv_cancel]

theorem exists_conj_eq_of_map_conj_eq [Finite K] (hπ : Function.Surjective π)
    (hodd : Odd (Nat.card π.ker)) {τ τ' : K} (hτ : τ * τ = 1) (hτ' : τ' * τ' = 1) {y : Q}
    (hy : y * π τ * y⁻¹ = π τ') : ∃ x : K, x * τ * x⁻¹ = τ' := by
  obtain ⟨x₀, rfl⟩ := hπ y
  have hker : τ' * (x₀ * τ * x₀⁻¹) ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, hy, ← map_mul, hτ', map_one]
  obtain ⟨u, -, hu⟩ := exists_conj_eq_of_odd_orderOf_mul hτ' (conj_mul_self_eq_one hτ)
    (odd_orderOf_of_mem_ker hodd hker)
  refine ⟨u * x₀, ?_⟩
  rw [← hu]
  group

theorem exists_threeCycle_of_map [Finite K] (hπ : Function.Surjective π)
    (hodd : Odd (Nat.card π.ker)) {τ : K} (hτ : τ * τ = 1) {b' y : Q} (hb'2 : b' * b' = 1)
    (hb'1 : b' ≠ 1) (hb'τ : b' ≠ π τ) (hcomm : π τ * b' = b' * π τ)
    (hy1 : y * π τ * y⁻¹ = b') (hy2 : y * b' * y⁻¹ = π τ * b') :
    ∃ b x : K, b * b = 1 ∧ b ≠ 1 ∧ b ≠ τ ∧ τ * b = b * τ ∧ x * τ * x⁻¹ = b ∧
      x * b * x⁻¹ = τ * b := by
  have hπτ2 : π τ * π τ = 1 := by rw [← map_mul, hτ, map_one]
  obtain ⟨b₀, rfl⟩ := hπ b'
  have hker : τ * (b₀ * τ * b₀⁻¹) ∈ π.ker := by
    have hc : π b₀ * π τ * (π b₀)⁻¹ = π τ := by rw [← hcomm]; group
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, hc, hπτ2]
  obtain ⟨u, hu, hu'⟩ := exists_conj_eq_of_odd_orderOf_mul hτ (conj_mul_self_eq_one hτ)
    (odd_orderOf_of_mem_ker hodd hker)
  have huk : π u = 1 := (Subgroup.zpowers_le.mpr hker) hu
  set b₁ := u * b₀ with hb₁
  have hb₁τ : Commute b₁ τ := by
    have h : b₁ * τ * b₁⁻¹ = τ := by
      calc b₁ * τ * b₁⁻¹ = u * (b₀ * τ * b₀⁻¹) * u⁻¹ := by rw [hb₁]; group
        _ = τ := hu'
    calc b₁ * τ = b₁ * τ * b₁⁻¹ * b₁ := by group
      _ = τ * b₁ := by rw [h]
  have hπb₁ : π b₁ = π b₀ := by rw [hb₁, map_mul, huk, one_mul]
  have hsq : b₁ ^ 2 ∈ π.ker := by rw [MonoidHom.mem_ker, map_pow, hπb₁, sq, hb'2]
  obtain ⟨j, hj⟩ := odd_orderOf_of_mem_ker hodd hsq
  set b := b₁ ^ (2 * j + 1) with hb
  have hb2 : b * b = 1 := by
    rw [hb, ← pow_add, show 2 * j + 1 + (2 * j + 1) = 2 * (2 * j + 1) by ring, pow_mul, ← hj,
      pow_orderOf_eq_one]
  have hπb : π b = π b₀ := by
    rw [hb, map_pow, hπb₁, pow_succ, pow_mul, sq, hb'2, one_pow, one_mul]
  have hτb : τ * b = b * τ := ((hb₁τ.pow_left (2 * j + 1)).eq).symm
  have hb1 : b ≠ 1 := fun h => hb'1 (by rw [← hπb, h, map_one])
  have hbτ : b ≠ τ := fun h => hb'τ (by rw [← hπb, h])
  obtain ⟨x₀, rfl⟩ := hπ y
  have hker₁ : b * (x₀ * τ * x₀⁻¹) ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, hy1, hπb, hb'2]
  obtain ⟨u₁, hu₁, hu₁'⟩ := exists_conj_eq_of_odd_orderOf_mul hb2 (conj_mul_self_eq_one hτ)
    (odd_orderOf_of_mem_ker hodd hker₁)
  have hu₁k : π u₁ = 1 := (Subgroup.zpowers_le.mpr hker₁) hu₁
  set x₁ := u₁ * x₀ with hx₁
  have hx₁τ : x₁ * τ * x₁⁻¹ = b := by
    calc x₁ * τ * x₁⁻¹ = u₁ * (x₀ * τ * x₀⁻¹) * u₁⁻¹ := by rw [hx₁]; group
      _ = b := hu₁'
  have hπx₁ : π x₁ = π x₀ := by rw [hx₁, map_mul, hu₁k, one_mul]
  set c := x₁ * b * x₁⁻¹ with hc
  have hτb2 : (τ * b) * (τ * b) = 1 := by
    calc (τ * b) * (τ * b) = τ * (b * τ) * b := by group
      _ = τ * (τ * b) * b := by rw [hτb]
      _ = (τ * τ) * (b * b) := by group
      _ = 1 := by rw [hτ, hb2, mul_one]
  have hker₂ : (τ * b) * c ∈ π.ker := by
    have hπc : π c = π τ * π b₀ := by
      rw [hc, map_mul, map_mul, map_inv, hπx₁, hπb, hy2]
    rw [MonoidHom.mem_ker, map_mul, hπc, map_mul, hπb]
    calc π τ * π b₀ * (π τ * π b₀) = π τ * (π b₀ * π τ) * π b₀ := by group
      _ = π τ * (π τ * π b₀) * π b₀ := by rw [hcomm]
      _ = (π τ * π τ) * (π b₀ * π b₀) := by group
      _ = 1 := by rw [hπτ2, hb'2, mul_one]
  obtain ⟨u₂, hu₂, hu₂'⟩ := exists_conj_eq_of_odd_orderOf_mul hτb2 (conj_mul_self_eq_one hb2)
    (odd_orderOf_of_mem_ker hodd hker₂)
  have hcb : c * b = b * c := by
    have e1 : c * b = x₁ * (b * τ) * x₁⁻¹ := by rw [hc, ← hx₁τ]; group
    have e2 : b * c = x₁ * (τ * b) * x₁⁻¹ := by rw [hc, ← hx₁τ]; group
    rw [e1, e2, hτb]
  have hu₂b : u₂ * b = b * u₂ := by
    have hmem : (τ * b) * c ∈ Subgroup.centralizer ({b} : Set K) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc τ * b * c * b = τ * b * (c * b) := by group
        _ = τ * b * (b * c) := by rw [hcb]
        _ = (τ * b) * b * c := by group
        _ = (b * τ) * b * c := by rw [hτb]
        _ = b * (τ * b * c) := by group
    exact Subgroup.mem_centralizer_singleton_iff.mp ((Subgroup.zpowers_le.mpr hmem) hu₂)
  refine ⟨b, u₂ * x₁, hb2, hb1, hbτ, hτb, ?_, ?_⟩
  · calc u₂ * x₁ * τ * (u₂ * x₁)⁻¹ = u₂ * (x₁ * τ * x₁⁻¹) * u₂⁻¹ := by group
      _ = u₂ * b * u₂⁻¹ := by rw [hx₁τ]
      _ = b := by rw [hu₂b]; group
  · calc u₂ * x₁ * b * (u₂ * x₁)⁻¹ = u₂ * c * u₂⁻¹ := by rw [hc]; group
      _ = τ * b := hu₂'

end Lift

section Automizer

variable {Γ : Type*} [Group Γ]

theorem normalizerMonoidHom_eq_one_iff_mem_centralizer (V : Subgroup Γ)
    (y : Subgroup.normalizer (V : Set Γ)) :
    V.normalizerMonoidHom y = 1 ↔ (y : Γ) ∈ Subgroup.centralizer (V : Set Γ) := by
  rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker]
  rfl

theorem three_dvd_automizerIndex_of_pow_three_mem [Finite Γ] (V : Subgroup Γ) {y : Γ}
    (hyN : y ∈ Subgroup.normalizer (V : Set Γ)) (hyC : y ∉ Subgroup.centralizer (V : Set Γ))
    (hy3 : y ^ 3 ∈ Subgroup.centralizer (V : Set Γ)) : 3 ∣ automizerIndex V := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [automizerIndex_eq_card_range]
  let y' : Subgroup.normalizer (V : Set Γ) := ⟨y, hyN⟩
  let ψ : V.normalizerMonoidHom.range := ⟨V.normalizerMonoidHom y', y', rfl⟩
  have hψ : orderOf ψ = 3 := by
    apply orderOf_eq_prime
    · apply Subtype.ext
      change V.normalizerMonoidHom y' ^ 3 = 1
      rw [← map_pow, normalizerMonoidHom_eq_one_iff_mem_centralizer]
      exact hy3
    · intro h
      apply hyC
      rw [← normalizerMonoidHom_eq_one_iff_mem_centralizer V y']
      exact congrArg Subtype.val h
  rw [← hψ]
  exact orderOf_dvd_natCard ψ

theorem isKleinFour_closure_of_threeCycle [Finite Γ] {a b x : Γ} (ha : a * a = 1)
    (ha1 : a ≠ 1) (hb : b * b = 1) (hb1 : b ≠ 1) (hba : b ≠ a) (hab : a * b = b * a)
    (hx1 : x * a * x⁻¹ = b) (hx2 : x * b * x⁻¹ = a * b) :
    IsKleinFour (Subgroup.closure {a, b}) ∧ a ∈ Subgroup.closure {a, b} ∧
      3 ∣ automizerIndex (Subgroup.closure {a, b}) := by
  have hoa : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact ha) ha1
  have hob : orderOf b = 2 := orderOf_eq_prime (by rw [sq]; exact hb) hb1
  set V := Subgroup.closure ({a, b} : Set Γ) with hV
  have haV : a ∈ V := Subgroup.subset_closure (by simp)
  have hbV : b ∈ V := Subgroup.subset_closure (by simp)
  refine ⟨ComponentClassification.UnbalancedGS.ReciprocalFusion.isKleinFour_closure_pair hoa hob
    hab (Ne.symm hba), haV, ?_⟩
  have hx3 : x * (a * b) * x⁻¹ = a := by
    calc x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
      _ = (b * a) * b := by rw [hx1, hx2, mul_assoc]
      _ = a * (b * b) := by rw [← hab, mul_assoc]
      _ = a := by rw [hb, mul_one]
  have hxN : x ∈ Subgroup.normalizer (V : Set Γ) := by
    apply Subgroup.mem_normalizer_fintype
    have hle : V ≤ V.comap (MulAut.conj x).toMonoidHom := by
      change Subgroup.closure ({a, b} : Set Γ) ≤ _
      rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      refine ⟨?_, ?_⟩
      · rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          hx1]
        exact hbV
      · rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          hx2]
        exact V.mul_mem haV hbV
    intro n hn
    exact hle hn
  have hxC : x ∉ Subgroup.centralizer (V : Set Γ) := by
    intro h
    have hc := Subgroup.mem_centralizer_iff.mp h a haV
    apply hba
    rw [← hx1, ← hc]
    group
  have hca : x ^ 3 * a * (x ^ 3)⁻¹ = a := by
    calc x ^ 3 * a * (x ^ 3)⁻¹ = x * (x * (x * a * x⁻¹) * x⁻¹) * x⁻¹ := by
          rw [pow_three]; group
      _ = a := by rw [hx1, hx2, hx3]
  have hcb : x ^ 3 * b * (x ^ 3)⁻¹ = b := by
    calc x ^ 3 * b * (x ^ 3)⁻¹ = x * (x * (x * b * x⁻¹) * x⁻¹) * x⁻¹ := by
          rw [pow_three]; group
      _ = b := by rw [hx2, hx3, hx1]
  have hx3C : x ^ 3 ∈ Subgroup.centralizer (V : Set Γ) := by
    have hle : V ≤ Subgroup.centralizer ({x ^ 3} : Set Γ) := by
      change Subgroup.closure ({a, b} : Set Γ) ≤ _
      rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hca).symm,
        Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hcb).symm⟩
    exact Subgroup.mem_centralizer_iff.mpr fun g hg =>
      Subgroup.mem_centralizer_singleton_iff.mp (hle hg)
  exact three_dvd_automizerIndex_of_pow_three_mem V hxN hxC hx3C

theorem exists_threeCycle_of_sq_not_mem_centralizer {Z : Subgroup Γ} (hZ : IsKleinFour Z)
    {a x : Γ} (haZ : a ∈ Z) (ha1 : a ≠ 1) (hxN : x ∈ Subgroup.normalizer (Z : Set Γ))
    (hx2 : x ^ 2 ∉ Subgroup.centralizer (Z : Set Γ)) :
    ∃ b : Γ, b * b = 1 ∧ b ≠ 1 ∧ b ≠ a ∧ a * b = b * a ∧ x * a * x⁻¹ = b ∧
      x * b * x⁻¹ = a * b := by
  have : IsKleinFour Z := hZ
  set φ : MulAut Z := Z.normalizerMonoidHom ⟨x, hxN⟩ with hφ
  have hnofix : ∀ v : Z, v ≠ 1 → φ v ≠ v := by
    intro v hv hfix
    apply hx2
    have h2 := mulAut_sq_eq_one_of_fixed_ne_one φ hv hfix
    have : (⟨x, hxN⟩ : Subgroup.normalizer (Z : Set Γ)) ^ 2 ∈ Z.normalizerMonoidHom.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact h2
    rw [Subgroup.normalizerMonoidHom_ker] at this
    exact this
  set a' : Z := ⟨a, haZ⟩
  have ha'1 : a' ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
  set b' : Z := φ a'
  set c' : Z := φ b'
  have hb'1 : b' ≠ 1 := fun h => ha'1 (φ.injective (by rw [map_one]; exact h))
  have hb'a : b' ≠ a' := hnofix a' ha'1
  have hc'b : c' ≠ b' := hnofix b' hb'1
  have hc'1 : c' ≠ 1 := fun h => hb'1 (φ.injective (by rw [map_one]; exact h))
  have hc'a : c' ≠ a' := by
    intro h
    have hab1 : a' * b' ≠ 1 := fun h' =>
      hb'a ((eq_inv_of_mul_eq_one_right h').trans (IsKleinFour.inv_eq_self a'))
    apply hnofix (a' * b') hab1
    rw [map_mul]
    change b' * c' = a' * b'
    rw [h]
    exact IsKleinFour.isMulCommutative.is_comm.comm b' a'
  have hc' : c' = a' * b' :=
    IsKleinFour.eq_mul_of_ne_all ha'1 hb'1 (Ne.symm hb'a) hc'1 hc'a hc'b
  refine ⟨(b' : Γ), congrArg Subtype.val (IsKleinFour.mul_self b'),
    fun h => hb'1 (Subtype.ext h), fun h => hb'a (Subtype.ext h),
    congrArg Subtype.val (IsKleinFour.isMulCommutative.is_comm.comm a' b'), rfl, ?_⟩
  change ((c' : Z) : Γ) = _
  rw [hc']
  rfl

theorem threeCycle_map {Y : Type*} [Group Y] (f : Γ →* Y) (hf : Function.Injective f)
    {a b x : Γ}
    (h : b * b = 1 ∧ b ≠ 1 ∧ b ≠ a ∧ a * b = b * a ∧ x * a * x⁻¹ = b ∧ x * b * x⁻¹ = a * b) :
    f b * f b = 1 ∧ f b ≠ 1 ∧ f b ≠ f a ∧ f a * f b = f b * f a ∧
      f x * f a * (f x)⁻¹ = f b ∧ f x * f b * (f x)⁻¹ = f a * f b := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨by rw [← map_mul, h1, map_one], fun h' => h2 (hf (by rw [h', map_one])),
    fun h' => h3 (hf h'), by rw [← map_mul, ← map_mul, h4], ?_, ?_⟩
  · rw [← map_inv, ← map_mul, ← map_mul, h5]
  · rw [← map_inv, ← map_mul, ← map_mul, h6, map_mul]

end Automizer

theorem alternatingGroup_four_exists_threeCycle :
    ∀ a : alternatingGroup (Fin 4), a ≠ 1 → a * a = 1 → ∃ b x : alternatingGroup (Fin 4),
      b * b = 1 ∧ b ≠ 1 ∧ b ≠ a ∧ a * b = b * a ∧ x * a * x⁻¹ = b ∧ x * b * x⁻¹ = a * b := by
  decide

theorem psl2_exists_threeCycle (F : Type) [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) {a : PSL2 F} (ha1 : a ≠ 1) (ha : a * a = 1) :
    ∃ b x : PSL2 F, b * b = 1 ∧ b ≠ 1 ∧ b ≠ a ∧ a * b = b * a ∧ x * a * x⁻¹ = b ∧
      x * b * x⁻¹ = a * b := by
  classical
  by_cases h3 : Nat.card F = 3
  · have : Fintype F := Fintype.ofFinite F
    have hFcard : Fintype.card F = 3 := by simpa [Nat.card_eq_fintype_card] using h3
    let e : PSL2 F ≃* alternatingGroup (Fin 4) :=
      (psl2RingEquiv (ZMod.ringEquivOfPrime F Nat.prime_three hFcard)).symm.trans
        psl2_three_equiv_alternatingGroup
    obtain ⟨b, x, hbx⟩ := alternatingGroup_four_exists_threeCycle (e a)
      (fun h => ha1 (e.injective (by rw [h, map_one]))) (by rw [← map_mul, ha, map_one])
    have h := threeCycle_map e.symm.toMonoidHom e.symm.injective hbx
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at h
    exact ⟨_, _, h⟩
  · have hq : 3 < Nat.card F := by
      obtain ⟨p, n, hp, hpodd, hn, hcard⟩ := hF
      have hp3 : 3 ≤ p := by
        have := hp.two_le
        obtain ⟨k, hk⟩ := hpodd
        omega
      have : p ≤ p ^ n := Nat.le_self_pow (by omega) p
      omega
    have hdih := psl2_odd_hasDihedralSylowTwo_model F hF
    have hsimple : IsSimpleGroup (PSL2 F) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
    obtain ⟨S₀⟩ : Nonempty (Sylow 2 (PSL2 F)) := inferInstance
    obtain ⟨m, hm, ⟨e₀⟩⟩ := hdih S₀
    have h4 : 4 ≤ Nat.card (PSL2 F) := by
      have hS₀ : Nat.card (S₀ : Subgroup (PSL2 F)) = 2 * 2 ^ m :=
        (Nat.card_congr e₀.toEquiv).trans DihedralGroup.nat_card
      have h2m : 2 ≤ 2 ^ m := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      exact (show 4 ≤ Nat.card (S₀ : Subgroup (PSL2 F)) by omega).trans
        (Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card _))
    have hno2 : ¬ ∃ N : Subgroup (PSL2 F), N.Normal ∧ N.index = 2 := by
      rintro ⟨N, hN, hidx⟩
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (H := N) with rfl | rfl
      · rw [Subgroup.index_bot] at hidx
        omega
      · rw [Subgroup.index_top] at hidx
        omega
    have hinv : BenderSuzuki.PFAppendixIII.IsInvolution a := ⟨ha1, by rw [sq]; exact ha⟩
    rcases gw_lemma_2_1 hdih with h1 | h2 | ⟨⟨N, hN, hidx⟩, -⟩
    · obtain ⟨Z₀, hZ₀S, hZ₀⟩ :=
        exists_kleinFour_le_of_dihedral_subgroup_mulEquiv (S₀ : Subgroup (PSL2 F)) hm e₀
      have : IsKleinFour Z₀ := hZ₀
      have : Nontrivial Z₀ := by
        rw [← Finite.one_lt_card_iff_nontrivial, hZ₀.card_four]
        norm_num
      obtain ⟨z, hz1⟩ := exists_ne (1 : Z₀)
      have hzinv : BenderSuzuki.PFAppendixIII.IsInvolution (z : PSL2 F) :=
        ⟨fun h => hz1 (Subtype.ext h), by
          rw [sq]; exact congrArg Subtype.val (IsKleinFour.mul_self z)⟩
      obtain ⟨g, hg⟩ := h1.2.1 z a hzinv hinv
      set Z := Z₀.map (MulAut.conj g).toMonoidHom with hZdef
      have hZ : IsKleinFour Z :=
        CFSG.ABGDGroups.isKleinFour_map_of_injective (MulAut.conj g).injective hZ₀
      have haZ : a ∈ Z := ⟨z, z.2, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hg]⟩
      have hZS : Z ≤ ((g • S₀ : Sylow 2 (PSL2 F)) : Subgroup (PSL2 F)) := by
        rintro _ ⟨y, hy, rfl⟩
        rw [Sylow.coe_subgroup_smul]
        exact Subgroup.smul_mem_pointwise_smul _ _ _ (hZ₀S hy)
      obtain ⟨x, hxN, hx⟩ := Set.exists_of_ssubset (h1.2.2 (g • S₀) Z hZS hZ)
      obtain ⟨b, hb⟩ := exists_threeCycle_of_sq_not_mem_centralizer hZ haZ ha1 hxN
        (fun h => hx ⟨hxN, h⟩)
      exact ⟨b, x, hb⟩
    · exact absurd h2.1 hno2
    · exact absurd (TwoClassFusion.exists_normal_index_two_of_normal_index_four hN hidx) hno2

theorem not_hasWreathedSylow_of_hasSemidihedralSylow {G : Type} [Group G] [Finite G] {n : ℕ}
    (hSD : HasSemidihedralSylow G n) (H : Subgroup G) : ¬ ∃ m, HasWreathedSylow H m := by
  rintro ⟨m, hm, hW⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 H) := inferInstance
  obtain ⟨ψ⟩ := hW P
  have hP2 : IsPGroup 2 ((P : Subgroup H).map H.subtype) := P.isPGroup'.map H.subtype
  obtain ⟨S, hS⟩ := hP2.exists_le_sylow
  obtain ⟨f⟩ := hSD.2 S
  let j₀ : Wreathed.Wreath (2 ^ m) →* G :=
    H.subtype.comp ((P : Subgroup H).subtype.comp ψ.symm.toMonoidHom)
  have hj₀ : Function.Injective j₀ :=
    H.subtype_injective.comp ((P : Subgroup H).subtype_injective.comp ψ.symm.injective)
  have hj₀S : ∀ w, j₀ w ∈ (S : Subgroup G) := fun w => hS ⟨_, (ψ.symm w).2, rfl⟩
  let j : Wreathed.Wreath (2 ^ m) →* CFSG.Open.SemidihedralGroup n :=
    f.symm.toMonoidHom.comp (j₀.codRestrict (S : Subgroup G) hj₀S)
  have hj : Function.Injective j := by
    intro w w' h
    have h' : (j₀.codRestrict (S : Subgroup G) hj₀S w : G) =
        j₀.codRestrict (S : Subgroup G) hj₀S w' :=
      congrArg Subtype.val (f.symm.injective h)
    exact hj₀ h'
  have hn3 : 3 ≤ n := by have := hSD.1; omega
  set C := (Subgroup.zpowers (Semidihedral.r n)).comap j with hC
  have hCidx : C.index ∣ 2 := by
    have := Semidihedral.rotation_normal n hn3
    have h := Subgroup.relIndex_dvd_index_of_normal (Subgroup.zpowers (Semidihedral.r n))
      j.range
    rw [Semidihedral.rotation_index n hn3] at h
    rw [hC, Subgroup.index_comap]
    exact h
  have hCcyc : IsCyclic C := by
    let k : C →* Subgroup.zpowers (Semidihedral.r n) :=
      (j.comp C.subtype).codRestrict _ (fun c => c.2)
    exact isCyclic_of_injective k (fun c c' h => Subtype.ext (hj (congrArg Subtype.val h)))
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := C)
  have hgdvd : Nat.card C ∣ 2 * 2 ^ m := by
    rw [← hg, ← Subgroup.orderOf_coe]
    exact orderOf_dvd_of_pow_eq_one (Wreathed.element_pow_twice_modulus _ _)
  have hcard := C.card_mul_index
  rw [Wreathed.card_wreath] at hcard
  have hc : Nat.card C ≤ 2 * 2 ^ m := Nat.le_of_dvd (by positivity) hgdvd
  have hi : C.index ≤ 2 := Nat.le_of_dvd (by norm_num) hCidx
  have h4 : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hle : 2 * (2 ^ m) ^ 2 ≤ 2 * 2 ^ m * 2 := by
    rw [← hcard]
    exact Nat.mul_le_mul hc hi
  nlinarith

theorem exists_mem_ne_one_ne {G : Type*} [Group G] {T : Subgroup G} (hT : IsKleinFour T)
    (a : G) : ∃ b ∈ T, b ≠ 1 ∧ b ≠ a := by
  by_contra h
  push Not at h
  have hsub : (T : Set G) ⊆ {1, a} := fun b hb => by
    by_cases hb1 : b = 1
    · exact Or.inl hb1
    · exact Or.inr (h b hb hb1)
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({1, a} : Set G).ncard ≤ 2 :=
    (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
  have h3 : (T : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hT.card_four
  omega

theorem exists_threeCycle_of_mem_linearCore {H : Type} [Group H] {F : Type} [Field F]
    [Finite F] {ι : H →* PGammaL2 F} {L E : Subgroup H} {S : Sylow 2 H}
    (hd : IsLinearDecomposition ι L E S) {τ : H} (hτL : τ ∈ linearCore ι) (hτ1 : τ ≠ 1)
    (hτ2 : τ * τ = 1) :
    ∃ b x : H, b * b = 1 ∧ b ≠ 1 ∧ b ≠ τ ∧ τ * b = b * τ ∧ x * τ * x⁻¹ = b ∧
      x * b * x⁻¹ = τ * b := by
  obtain ⟨eL⟩ := hd.nonempty_linearCore_mulEquiv
  set a : PSL2 F := eL ⟨τ, hτL⟩ with ha
  have ha1 : a ≠ 1 := fun h =>
    hτ1 (congrArg Subtype.val (eL.injective (h.trans (map_one eL).symm)))
  have ha2 : a * a = 1 := by
    rw [ha, ← map_mul]
    have : (⟨τ, hτL⟩ : linearCore ι) * ⟨τ, hτL⟩ = 1 := Subtype.ext hτ2
    rw [this, map_one]
  obtain ⟨b, x, hbx⟩ := psl2_exists_threeCycle F hd.isOddPrimePower_card ha1 ha2
  let f : PSL2 F →* H := (linearCore ι).subtype.comp eL.symm.toMonoidHom
  have hf : Function.Injective f := (linearCore ι).subtype_injective.comp eL.symm.injective
  have hfa : f a = τ := by simp [f, a]
  have h := threeCycle_map f hf hbx
  rw [hfa] at h
  exact ⟨f b, f x, h⟩

theorem exists_conj_of_not_mem_linearCore {H : Type} [Group H] [Finite H] {F : Type}
    [Field F] [Finite F] {ι : H →* PGammaL2 F} {L E : Subgroup H} {S : Sylow 2 H}
    (hd : IsLinearDecomposition ι L E S) {T : Subgroup H} (hT : IsKleinFour T)
    (hTS : T ≤ (S : Subgroup H)) {τ : H} (hτT : τ ∈ T) (hτ1 : τ ≠ 1)
    (hτL : τ ∉ linearCore ι) : ∃ x : H, ∃ τ' ∈ T, τ' ≠ τ ∧ x * τ * x⁻¹ = τ' := by
  classical
  set L₀ := linearCore ι with hL₀
  have : IsKleinFour T := hT
  have hTm : ∀ v ∈ T, v * v = 1 := fun v hv =>
    congrArg Subtype.val (IsKleinFour.mul_self (⟨v, hv⟩ : T))
  have hτ2 := hTm τ hτT
  have hτord : orderOf τ = 2 := orderOf_eq_prime (by rw [sq]; exact hτ2) hτ1
  have hSL : (S : Subgroup H) ≤ L := hd.sylow_le S
  have hτLL : τ ∈ L := hSL (hTS hτT)
  have hLpgl : L.map ι = pGammaL2PGLRange F := by
    rcases hd.map_eq with h | h | h
    · exfalso
      apply hτL
      change ι τ ∈ pGammaL2PSLRange F
      rw [← h]
      exact Subgroup.mem_map_of_mem ι hτLL
    · exact h
    · exact absurd (hd.mem_linearCore_of_map_eq_pGLStar h hτord) hτL
  have hidx : (L₀.subgroupOf L).index = 2 := by
    rcases hd.relIndex_linearCore with h | h
    · exact absurd (Subgroup.relIndex_eq_one.mp h hτLL) hτL
    · exact h
  have hsq : ∀ y ∈ L, y * y ∈ L₀ := by
    intro y hy
    have h := Subgroup.sq_mem_of_index_two hidx ⟨y, hy⟩
    rw [Subgroup.mem_subgroupOf, sq] at h
    exact h
  have hmul : ∀ y ∈ L, ∀ y' ∈ L, (y * y' ∈ L₀ ↔ (y ∈ L₀ ↔ y' ∈ L₀)) := by
    intro y hy y' hy'
    have h := Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨y, hy⟩) (b := ⟨y', hy'⟩)
    simp only [Subgroup.mem_subgroupOf] at h
    exact h
  obtain ⟨τ₂, hτ₂T, hτ₂1, hτ₂τ, hτ₂L⟩ : ∃ τ₂ ∈ T, τ₂ ≠ 1 ∧ τ₂ ≠ τ ∧ τ₂ ∉ L₀ := by
    obtain ⟨c, hcT, hc1, hcτ⟩ := exists_mem_ne_one_ne hT τ
    by_cases hcL : c ∈ L₀
    · refine ⟨τ * c, T.mul_mem hτT hcT, ?_, ?_, ?_⟩
      · intro h
        exact hcτ ((eq_inv_of_mul_eq_one_right h).trans (inv_eq_of_mul_eq_one_right hτ2))
      · intro h
        exact hc1 (mul_left_cancel (h.trans (mul_one τ).symm))
      · intro h
        exact hτL (((hmul τ hτLL c (hSL (hTS hcT))).mp h).mpr hcL)
    · exact ⟨c, hcT, hc1, hcτ, hcL⟩
  obtain ⟨m, hm1, ⟨e⟩⟩ := hd.hasDihedralSylowTwo (Or.inr hLpgl) S
  have hm2 : 2 ≤ m := by
    obtain ⟨eL⟩ := hd.nonempty_linearCore_mulEquiv
    obtain ⟨P⟩ : Nonempty (Sylow 2 (PSL2 F)) := inferInstance
    obtain ⟨m', hm', ⟨eP⟩⟩ := psl2_odd_hasDihedralSylowTwo_model F hd.isOddPrimePower_card P
    have h4 : 4 ∣ Nat.card L₀ := by
      rw [Nat.card_congr eL.toEquiv]
      have hP : Nat.card (P : Subgroup (PSL2 F)) = 2 * 2 ^ m' :=
        (Nat.card_congr eP.toEquiv).trans DihedralGroup.nat_card
      have h4P : 4 ∣ Nat.card (P : Subgroup (PSL2 F)) := by
        rw [hP]
        obtain ⟨k, rfl⟩ : ∃ k, m' = k + 1 := ⟨m' - 1, by omega⟩
        exact ⟨2 ^ k, by ring⟩
      exact h4P.trans (Subgroup.card_subgroup_dvd_card _)
    have hL : Nat.card L = 2 * Nat.card L₀ := by
      have h := Subgroup.relIndex_mul_card L₀ L
      rw [Subgroup.relIndex, hidx, inf_of_le_left hd.linearCore_le] at h
      exact h.symm
    have h8 : 2 ^ 3 ∣ Nat.card H := by
      have h8L : 2 ^ 3 ∣ Nat.card L := by
        rw [hL]
        obtain ⟨k, hk⟩ := h4
        exact ⟨k, by rw [hk]; ring⟩
      exact h8L.trans (Subgroup.card_subgroup_dvd_card L)
    have h8S := Sylow.pow_dvd_card_of_pow_dvd_card S h8
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card] at h8S
    by_contra hm
    obtain rfl : m = 1 := by omega
    norm_num at h8S
  set c : ZMod (2 ^ m) := ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) with hc
  set j : ZMod (2 ^ m) := ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m)) with hj
  have hjj : j + j = c := by
    rw [hj, hc, ← Nat.cast_add, ← two_mul, ← pow_succ']
    congr 2
    omega
  have hzL : ((e.symm (DihedralGroup.r c) : S) : H) ∈ L₀ := by
    have h : (e.symm (DihedralGroup.r c) : S) =
        e.symm (DihedralGroup.r j) * e.symm (DihedralGroup.r j) := by
      rw [← map_mul, DihedralGroup.r_mul_r, hjj]
    rw [h, Subgroup.coe_mul]
    exact hsq _ (hSL (e.symm (DihedralGroup.r j)).2)
  set τS : S := ⟨τ, hTS hτT⟩ with hτS
  set τ₂S : S := ⟨τ₂, hTS hτ₂T⟩ with hτ₂S
  have hτSord : orderOf (e τS) = 2 := by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hτord]
  obtain ⟨k, hk⟩ : ∃ k, e τS = DihedralGroup.sr k := by
    rcases TwoClassFusion.eq_r_half_or_sr_of_orderOf_eq_two hm2 hτSord with h | h
    · exfalso
      apply hτL
      have h' : τS = e.symm (DihedralGroup.r c) := by rw [← h, MulEquiv.symm_apply_apply]
      have h'' : τ = ((e.symm (DihedralGroup.r c) : S) : H) := congrArg Subtype.val h'
      rw [h'']
      exact hzL
    · exact h
  have hcomm : Commute (DihedralGroup.sr k) (e τ₂S) := by
    rw [← hk]
    have h0 : τ * τ₂ = τ₂ * τ := congrArg Subtype.val
      (IsKleinFour.isMulCommutative.is_comm.comm (⟨τ, hτT⟩ : T) ⟨τ₂, hτ₂T⟩)
    have h : Commute τS τ₂S := Subtype.ext h0
    exact h.map e
  have hk₂ : e τ₂S = DihedralGroup.sr (k + c) := by
    rcases TwoClassFusion.eq_of_commute_sr hm2 hcomm with h | h | h | h
    · exfalso
      apply hτ₂1
      exact congrArg Subtype.val (e.injective (h.trans (map_one e).symm))
    · exfalso
      apply hτ₂L
      have h' : τ₂S = e.symm (DihedralGroup.r c) := by rw [← h, MulEquiv.symm_apply_apply]
      have h'' : τ₂ = ((e.symm (DihedralGroup.r c) : S) : H) := congrArg Subtype.val h'
      rw [h'']
      exact hzL
    · exfalso
      apply hτ₂τ
      rw [← hk] at h
      exact congrArg Subtype.val (e.injective h)
    · exact h
  set g : S := e.symm (DihedralGroup.r j) with hg
  refine ⟨(g : H)⁻¹, τ₂, hτ₂T, hτ₂τ, ?_⟩
  have hconj : g⁻¹ * τS * g = τ₂S := by
    apply e.injective
    rw [map_mul, map_mul, map_inv, hg, MulEquiv.apply_symm_apply, hk, hk₂, DihedralGroup.inv_r,
      DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r, ← hjj]
    congr 1
    ring
  have h : ((g⁻¹ * τS * g : S) : H) = τ₂ := congrArg Subtype.val hconj
  rw [inv_inv]
  exact h

theorem fourFusion_of_isDGroup_of_oddCore_eq_bot {K : Type} [Group K] [Finite K]
    (hK : QuasiDihedralFusion.IsDGroup K) (hO : CFSG.oddCore K = ⊥)
    (hW : ¬ ∃ m, HasWreathedSylow K m)
    {T : Subgroup K} (hT : IsKleinFour T) {τ : K} (hτT : τ ∈ T) (hτ1 : τ ≠ 1) :
    (∃ x : K, ∃ τ' ∈ T, τ' ≠ τ ∧ x * τ * x⁻¹ = τ') ∨
      ∃ b x : K, b * b = 1 ∧ b ≠ 1 ∧ b ≠ τ ∧ τ * b = b * τ ∧ x * τ * x⁻¹ = b ∧
        x * b * x⁻¹ = τ * b := by
  have : IsKleinFour T := hT
  have hTm : ∀ v ∈ T, v * v = 1 := fun v hv =>
    congrArg Subtype.val (IsKleinFour.mul_self (⟨v, hv⟩ : T))
  have hτ2 := hTm τ hτT
  rcases aSeven_or_linearDecomposition hK hO hW with he7 | hlin
  ·
    left
    obtain ⟨e⟩ := he7
    obtain ⟨τ₂, hτ₂T, hτ₂1, hτ₂τ⟩ := exists_mem_ne_one_ne hT τ
    have hinv : ∀ v : K, v ≠ 1 → v * v = 1 →
        BenderSuzuki.PFAppendixIII.IsInvolution (e v) := fun v hv1 hv2 =>
      ⟨fun h => hv1 (e.injective (by rw [h, map_one])), by rw [sq, ← map_mul, hv2, map_one]⟩
    obtain ⟨g, hg⟩ := aSeven_involutions_conjugate (e τ) (e τ₂) (hinv τ hτ1 hτ2)
      (hinv τ₂ hτ₂1 (hTm τ₂ hτ₂T))
    refine ⟨e.symm g, τ₂, hτ₂T, hτ₂τ, e.injective ?_⟩
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hg
  · obtain ⟨S, hTS⟩ := (isPGroup_two_of_isKleinFour hT).exists_le_sylow
    obtain ⟨F, _, _, ι, L, E, hd⟩ := hlin S
    by_cases hτL : τ ∈ linearCore ι
    · exact Or.inr (exists_threeCycle_of_mem_linearCore hd hτL hτ1 hτ2)
    · exact Or.inl (exists_conj_of_not_mem_linearCore hd hT hTS hτT hτ1 hτL)

theorem fourFusion_of_isDGroup {K : Type} [Group K] [Finite K]
    (hK : QuasiDihedralFusion.IsDGroup K)
    (hW : ¬ ∃ m, HasWreathedSylow K m) {T : Subgroup K} (hT : IsKleinFour T) {τ : K}
    (hτT : τ ∈ T) (hτ1 : τ ≠ 1) :
    (∃ x : K, ∃ τ' ∈ T, τ' ≠ τ ∧ x * τ * x⁻¹ = τ') ∨
      ∃ V : Subgroup K, IsKleinFour V ∧ τ ∈ V ∧ 3 ∣ automizerIndex V := by
  set π := QuotientGroup.mk' (CFSG.oddCore K) with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hodd : Odd (Nat.card π.ker) := ABGDGroups.odd_card_ker_mk'_oddCore
  have : IsKleinFour T := hT
  have hTm : ∀ v ∈ T, v * v = 1 := fun v hv =>
    congrArg Subtype.val (IsKleinFour.mul_self (⟨v, hv⟩ : T))
  have hτ2 := hTm τ hτT
  have hTker : T ⊓ π.ker = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hvT, hvk⟩
    have hodd' := odd_orderOf_of_mem_ker hodd hvk
    have h2 : orderOf v ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hTm v hvT)
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp h)
    · rw [h] at hodd'
      exact absurd hodd' (by decide)
  have hT' : IsKleinFour (T.map π) := isKleinFour_map_of_inf_ker_eq_bot π hT hTker
  have hπτ1 : π τ ≠ 1 := fun h => hτ1 (by
    have h' : τ ∈ T ⊓ π.ker := ⟨hτT, h⟩
    rw [hTker] at h'
    exact h')
  rcases fourFusion_of_isDGroup_of_oddCore_eq_bot (isDGroup_quotient_oddCore hK)
      ABGLocalTools.oddCore_quotient_oddCore_eq_bot
      (fun ⟨m, hm⟩ => hW ⟨m, (hasWreathedSylow_quotient_oddCore_iff m).mp hm⟩) hT'
      (Subgroup.mem_map_of_mem π hτT) hπτ1 with
    ⟨y, _, ⟨τ', hτ'T, rfl⟩, hne, hy⟩ | ⟨b', y, hb'2, hb'1, hb'τ, hcomm, hy1, hy2⟩
  · obtain ⟨x, hx⟩ := exists_conj_eq_of_map_conj_eq hπ hodd hτ2 (hTm τ' hτ'T) hy
    exact Or.inl ⟨x, τ', hτ'T, fun h => hne (by rw [h]), hx⟩
  · obtain ⟨b, x, hb2, hb1, hbτ, hτb, hx1, hx2⟩ :=
      exists_threeCycle_of_map hπ hodd hτ2 hb'2 hb'1 hb'τ hcomm hy1 hy2
    obtain ⟨hV, hτV, h3⟩ := isKleinFour_closure_of_threeCycle hτ2 hτ1 hb2 hb1 hbτ hτb hx1 hx2
    exact Or.inr ⟨_, hV, hτV, h3⟩

theorem isKleinFour_subgroupOf_of_le {G : Type*} [Group G] {T H : Subgroup G} (hTH : T ≤ H)
    (hT : IsKleinFour T) : IsKleinFour (T.subgroupOf H) :=
  ⟨by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH).toEquiv]; exact hT.card_four,
    by rw [Monoid.exponent_eq_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hTH)]
       exact hT.exponent_two⟩

theorem dGroupFourFusion_of_semidihedral (G : Type) [Group G] [Finite G] :
    Sec10.DGroupFourFusion G := by
  rintro ⟨n, hSD⟩ H hH T₁ hT₁H hT₁ t ht ht1
  have hT : IsKleinFour (T₁.subgroupOf H) := isKleinFour_subgroupOf_of_le hT₁H hT₁
  have hτT : (⟨t, hT₁H ht⟩ : H) ∈ T₁.subgroupOf H := Subgroup.mem_subgroupOf.mpr ht
  have hτ1 : (⟨t, hT₁H ht⟩ : H) ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
  rcases fourFusion_of_isDGroup hH (not_hasWreathedSylow_of_hasSemidihedralSylow hSD H) hT
      hτT hτ1 with ⟨x, τ', hτ'T, hne, hx⟩ | ⟨V, hV, hτV, h3⟩
  · exact Or.inl ⟨x, x.2, τ', Subgroup.mem_subgroupOf.mp hτ'T, fun h => hne (Subtype.ext h),
      congrArg Subtype.val hx⟩
  · refine Or.inr ⟨V.map H.subtype, Subgroup.map_subtype_le V,
      isKleinFour_map_of_injective H.subtype_injective hV, ⟨_, hτV, rfl⟩, ?_⟩
    have hsub : (V.map H.subtype).subgroupOf H = V := by
      rw [← Subgroup.comap_subtype, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    rw [hsub]
    exact h3

end CFSG.ABGTheoremB.TotallyInverted.Inputs
