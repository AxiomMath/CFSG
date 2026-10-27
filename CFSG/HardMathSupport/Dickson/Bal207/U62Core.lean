module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open scoped Pointwise

theorem u62Aux_card_le_ker_cube {E : Type*} [Group E] [Finite E] (δ : E →* E)
    (h : ∀ x, δ (δ (δ x)) = 1) : Nat.card E ≤ Nat.card δ.ker ^ 3 := by
  set δ' : δ.range →* E := δ.comp δ.range.subtype with hδ'
  have h1 := Subgroup.card_ker_mul_card_range δ
  have h2 := Subgroup.card_ker_mul_card_range δ'
  have h3 : Nat.card δ'.ker ≤ Nat.card δ.ker := by
    refine Nat.card_le_card_of_injective
      (fun x => (⟨x.1.1, MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 x.2)⟩ : δ.ker)) ?_
    intro x y hxy
    have h := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext h)
  have h4 : Nat.card δ'.range ≤ Nat.card δ.ker := by
    apply Subgroup.card_le_of_le
    rintro _ ⟨⟨_, z, rfl⟩, rfl⟩
    exact MonoidHom.mem_ker.2 (h z)
  calc Nat.card E = Nat.card δ.ker * (Nat.card δ'.ker * Nat.card δ'.range) := by
        rw [h2, h1]
    _ ≤ Nat.card δ.ker * (Nat.card δ.ker * Nat.card δ.ker) := by gcongr
    _ = Nat.card δ.ker ^ 3 := by ring

theorem u62Aux_card_le_fix_cube {E : Type*} [CommGroup E] [Finite E] (a : E →* E)
    (ha : ∀ x, a (a (a x)) = x) (h3 : ∀ x : E, x ^ 3 = 1) :
    Nat.card E ≤ Nat.card (a / MonoidHom.id E).ker ^ 3 := by
  refine u62Aux_card_le_ker_cube _ fun x => ?_
  apply Additive.ofMul.injective
  have hb : 3 • Additive.ofMul (a x) = 0 := by rw [← ofMul_pow, h3, ofMul_one]
  have hc : 3 • Additive.ofMul (a (a x)) = 0 := by rw [← ofMul_pow, h3, ofMul_one]
  have key : Additive.ofMul ((a / MonoidHom.id E) ((a / MonoidHom.id E)
      ((a / MonoidHom.id E) x))) = 3 • Additive.ofMul (a x) - 3 • Additive.ofMul (a (a x)) := by
    simp only [MonoidHom.div_apply, MonoidHom.id_apply, map_div, ha, ofMul_div]
    abel
  rw [key, hb, hc, sub_zero, ofMul_one]

section Core

variable {K S : Type*} [Group K] [Group S]

theorem u62Aux_mem_center_of_conj_eq_one {y : K} (h : MulAut.conj y = 1) :
    y ∈ Subgroup.center K := by
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : y * g * y⁻¹ = g := by
    simpa only [MulAut.conj_apply, MulAut.one_apply] using congrArg (fun f : MulAut K => f g) h
  calc g * y = y * g * y⁻¹ * y := by rw [hg]
    _ = y * g := by group

theorem u62Aux_core [Finite K] {π : K →* S} (hker : π.ker = Subgroup.center K)
    (hZ : Nat.card {z : Subgroup.center K // z ^ 3 = 1} ≤ 3) {T P : Subgroup S} (hTP : T ≤ P)
    (hPT : ⁅P, P⁆ ≤ T) (hcent : ∀ x ∈ P, (∀ u ∈ ⁅P, P⁆, x * u = u * x) → x ∈ T)
    (hab : ∀ x y : K, π x ∈ T → π y ∈ T → x * y = y * x) {U : Subgroup K}
    (hUT : ∀ u ∈ U, π u ∈ T) (hU3 : ∀ u ∈ U, u ^ 3 = 1) (hUc : 81 ≤ Nat.card U)
    (Q : Sylow 3 K) (hQP : (Q : Subgroup K).map π = P) (α : MulAut K) (hα : α ^ 3 = 1)
    (hαQ : ∀ x ∈ (Q : Subgroup K), α x ∈ (Q : Subgroup K)) :
    ∃ y : K, y ^ 3 = 1 ∧ α y = y ∧ MulAut.conj y ∉ Subgroup.zpowers α := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hα3 : ∀ x, α (α (α x)) = x := fun x => by
    have h := congrArg (fun f : MulAut K => f x) hα
    simpa only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply] using h
  set C : Subgroup K := ⁅(Q : Subgroup K), (Q : Subgroup K)⁆ with hC
  have hαC : ∀ u ∈ C, α u ∈ C := by
    intro u hu
    have hQ' : (Q : Subgroup K).map α.toMonoidHom ≤ Q := by
      rintro _ ⟨x, hx, rfl⟩
      exact hαQ x hx
    have hle : C.map α.toMonoidHom ≤ C := by
      rw [hC, Subgroup.map_commutator]
      exact Subgroup.commutator_mono hQ' hQ'
    exact hle ⟨u, hu, rfl⟩
  have hCT : ∀ u ∈ C, π u ∈ T := by
    intro u hu
    apply hPT
    rw [← hQP, ← Subgroup.map_commutator]
    exact ⟨u, hu, rfl⟩
  have hAT : ∀ x ∈ (Q : Subgroup K), (∀ u ∈ C, x * u = u * x) → π x ∈ T := by
    intro x hxQ hxC
    have hxP : π x ∈ P := by
      rw [← hQP]
      exact ⟨x, hxQ, rfl⟩
    refine hcent (π x) hxP fun v hv => ?_
    rw [← hQP, ← Subgroup.map_commutator] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    rw [← map_mul, ← map_mul, hxC u hu]
  have hUQ : ∀ u ∈ U, u ∈ (Q : Subgroup K) := by
    intro u hu
    have huP : π u ∈ (Q : Subgroup K).map π := by
      rw [hQP]
      exact hTP (hUT u hu)
    obtain ⟨q, hq, hqu⟩ := huP
    have hz : q⁻¹ * u ∈ Subgroup.center K := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hqu, inv_mul_cancel]
    have hnorm : Subgroup.zpowers u ≤ Subgroup.normalizer ((Q : Subgroup K) : Set K) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
      intro h
      have hzh : (q⁻¹ * u) * h = h * (q⁻¹ * u) := (Subgroup.mem_center_iff.1 hz h).symm
      have hconj : u * h * u⁻¹ = q * h * q⁻¹ := by
        calc u * h * u⁻¹ = q * ((q⁻¹ * u) * h) * (q⁻¹ * u)⁻¹ * q⁻¹ := by group
          _ = q * (h * (q⁻¹ * u)) * (q⁻¹ * u)⁻¹ * q⁻¹ := by rw [hzh]
          _ = q * h * q⁻¹ := by group
      rw [hconj]
      exact Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hq) h
    have hp : IsPGroup 3 (Subgroup.zpowers u) := by
      refine IsPGroup.of_card_dvd_pow (n := 1) ?_
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_dvd_of_pow_eq_one (hU3 u hu)
    have heq := Q.is_maximal' (IsPGroup.to_sup_of_normal_left' Q.isPGroup' hp hnorm) le_sup_left
    rw [← heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
  have hUC : ∀ u ∈ U, ∀ v ∈ C, u * v = v * u := fun u hu v hv =>
    hab u v (hUT u hu) (hCT v hv)
  let E : Subgroup K :=
    { carrier := {y | y ∈ (Q : Subgroup K) ∧ (∀ u ∈ C, y * u = u * y) ∧ y ^ 3 = 1}
      mul_mem' := by
        rintro x y ⟨hxQ, hxC, hx3⟩ ⟨hyQ, hyC, hy3⟩
        refine ⟨(Q : Subgroup K).mul_mem hxQ hyQ, fun u hu => ?_, ?_⟩
        · rw [mul_assoc, hyC u hu, ← mul_assoc, hxC u hu, mul_assoc]
        · have hxy : Commute x y := hab x y (hAT x hxQ hxC) (hAT y hyQ hyC)
          rw [hxy.mul_pow, hx3, hy3, one_mul]
      one_mem' := ⟨(Q : Subgroup K).one_mem, fun u _ => by rw [one_mul, mul_one], one_pow 3⟩
      inv_mem' := by
        rintro x ⟨hxQ, hxC, hx3⟩
        refine ⟨(Q : Subgroup K).inv_mem hxQ, fun u hu => ?_, by rw [inv_pow, hx3, inv_one]⟩
        exact (Commute.inv_left (hxC u hu : Commute x u)).eq }
  have hmemE : ∀ y, y ∈ E ↔ y ∈ (Q : Subgroup K) ∧ (∀ u ∈ C, y * u = u * y) ∧ y ^ 3 = 1 :=
    fun y => Iff.rfl
  have hEα : ∀ y ∈ E, α y ∈ E := by
    intro y hy
    obtain ⟨hyQ, hyC, hy3⟩ := (hmemE y).1 hy
    refine (hmemE _).2 ⟨hαQ y hyQ, fun u hu => ?_, by rw [← map_pow, hy3, map_one]⟩
    have hv : α (α u) ∈ C := hαC _ (hαC u hu)
    calc α y * u = α y * α (α (α u)) := by rw [hα3]
      _ = α (y * α (α u)) := (map_mul α _ _).symm
      _ = α (α (α u) * y) := by rw [hyC _ hv]
      _ = α (α (α u)) * α y := map_mul α _ _
      _ = u * α y := by rw [hα3]
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    hab x y (hAT x ((hmemE x).1 hx).1 ((hmemE x).1 hx).2.1)
      (hAT y ((hmemE y).1 hy).1 ((hmemE y).1 hy).2.1)
  have hE3 : ∀ y ∈ E, y ^ 3 = 1 := fun y hy => ((hmemE y).1 hy).2.2
  have hUE : U ≤ E := fun u hu => (hmemE u).2 ⟨hUQ u hu, hUC u hu, hU3 u hu⟩
  have hEc : 81 ≤ Nat.card E := hUc.trans (Subgroup.card_le_of_le hUE)
  let c : E →* MulAut K := MulAut.conj.comp E.subtype
  have hck : Nat.card c.ker ≤ 3 := by
    refine le_trans (Nat.card_le_card_of_injective
      (fun y : c.ker => (⟨⟨((y : E) : K), u62Aux_mem_center_of_conj_eq_one y.2⟩,
        Subtype.ext (by simpa using hE3 _ (y : E).2)⟩ :
          {z : Subgroup.center K // z ^ 3 = 1})) ?_) hZ
    intro x y hxy
    have h := congrArg (fun z : {z : Subgroup.center K // z ^ 3 = 1} => ((z.1 : K))) hxy
    exact Subtype.ext (Subtype.ext h)
  letI : CommGroup E :=
    { (inferInstance : Group E) with mul_comm := fun x y => Subtype.ext (hEcomm x x.2 y y.2) }
  let aE : E →* E :=
    { toFun := fun y => ⟨α (y : K), hEα _ y.2⟩
      map_one' := Subtype.ext (map_one α)
      map_mul' := fun x y => Subtype.ext (map_mul α (x : K) (y : K)) }
  have haE : ∀ x, aE (aE (aE x)) = x := fun x => Subtype.ext (hα3 x)
  have hE3' : ∀ x : E, x ^ 3 = 1 := fun x => Subtype.ext (by simpa using hE3 _ x.2)
  have hcube := u62Aux_card_le_fix_cube aE haE hE3'
  set F := (aE / MonoidHom.id E).ker with hF
  have hFfix : ∀ y : E, y ∈ F → α y = y := by
    intro y hy
    rw [hF, MonoidHom.mem_ker, MonoidHom.div_apply, MonoidHom.id_apply, div_eq_one] at hy
    exact congrArg Subtype.val hy
  have hFc : 3 < Nat.card F := by
    by_contra hle
    push Not at hle
    have : Nat.card F ^ 3 ≤ 3 ^ 3 := Nat.pow_le_pow_left hle 3
    omega
  by_contra hcon
  push Not at hcon
  by_cases hA : ∀ y : E, y ∈ F → MulAut.conj (y : K) = 1
  · have hFk : F ≤ c.ker := fun y hy => hA y hy
    have := Subgroup.card_le_of_le hFk
    omega
  · push Not at hA
    obtain ⟨y₁, hy₁F, hy₁⟩ := hA
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hcon y₁ (hE3 _ y₁.2) (hFfix y₁ hy₁F))
    have hα3z : α ^ (3 : ℤ) = 1 := by rw [zpow_ofNat]; exact hα
    have hmod : α ^ k = α ^ (k % 3) := by
      conv_lhs => rw [← Int.emod_add_mul_ediv k 3]
      rw [zpow_add, zpow_mul, hα3z, one_zpow, mul_one]
    obtain ⟨y₀, hy₀E, hy₀⟩ : ∃ y₀ ∈ E, MulAut.conj y₀ = α := by
      have h3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
      rcases h3 with h | h | h
      · rw [hmod, h, zpow_zero] at hk
        exact absurd hk.symm hy₁
      · rw [hmod, h, zpow_one] at hk
        exact ⟨y₁, y₁.2, hk.symm⟩
      · refine ⟨(y₁ : K) ^ 2, E.pow_mem y₁.2 2, ?_⟩
        rw [map_pow, ← hk, hmod, h, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast,
          ← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hα, one_mul]
    have hαE : ∀ y ∈ E, α y = y := by
      intro y hy
      rw [← hy₀, MulAut.conj_apply, hEcomm _ hy₀E y hy, mul_inv_cancel_right]
    have hcr : c.range ≤ Subgroup.zpowers α := by
      rintro _ ⟨y, rfl⟩
      exact hcon y (hE3 _ y.2) (hαE y y.2)
    have h1 := Subgroup.card_ker_mul_card_range c
    have h2 : Nat.card c.range ≤ 3 := by
      refine (Subgroup.card_le_of_le hcr).trans ?_
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hα)
    have h9 : Nat.card c.ker * Nat.card c.range ≤ 3 * 3 := Nat.mul_le_mul hck h2
    omega

theorem u62Aux_main [Finite K] {π : K →* S} (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.center K)
    (hZ : Nat.card {z : Subgroup.center K // z ^ 3 = 1} ≤ 3) {T : Subgroup S} (P : Sylow 3 S)
    (hTP : T ≤ P) (hPT : ⁅(P : Subgroup S), (P : Subgroup S)⁆ ≤ T)
    (hcent : ∀ x ∈ (P : Subgroup S),
      (∀ u ∈ ⁅(P : Subgroup S), (P : Subgroup S)⁆, x * u = u * x) → x ∈ T)
    (hab : ∀ x y : K, π x ∈ T → π y ∈ T → x * y = y * x) {U : Subgroup K}
    (hUT : ∀ u ∈ U, π u ∈ T) (hU3 : ∀ u ∈ U, u ^ 3 = 1) (hUc : 81 ≤ Nat.card U)
    (α : MulAut K) (hα : α ^ 3 = 1) :
    ∃ y : K, y ^ 3 = 1 ∧ α y = y ∧ MulAut.conj y ∉ Subgroup.zpowers α := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q₀, hQ₀⟩ := Sylow.mapSurjective_surjective hπ 3 P
  have hQ₀P : (Q₀ : Subgroup K).map π = P := by
    rw [← hQ₀, Sylow.coe_mapSurjective]
  have hpg : IsPGroup 3 (Subgroup.zpowers α) := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one hα
  have hnd : ¬ 3 ∣ Nat.card (Sylow 3 K) := by
    intro h
    exact absurd ((card_sylow_modEq_one 3 K).symm.trans (Nat.modEq_zero_iff_dvd.2 h))
      (by decide)
  obtain ⟨Q, hQ⟩ := hpg.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 3 K) hnd
  have hαQ : α • Q = Q := hQ ⟨α, Subgroup.mem_zpowers α⟩
  have hαmem : ∀ z ∈ (Q : Subgroup K), α z ∈ (Q : Subgroup K) := by
    intro z hz
    have h := Subgroup.smul_mem_pointwise_smul z α (Q : Subgroup K) hz
    rw [← Sylow.pointwise_smul_def, hαQ] at h
    exact h
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K Q₀ Q
  have hQeq : (Q : Subgroup K) = MulAut.conj k • (Q₀ : Subgroup K) := by
    rw [← hk]
    rfl
  set α' : MulAut K := (MulAut.conj k)⁻¹ * α * MulAut.conj k with hα'
  have hα'Q : ∀ x ∈ (Q₀ : Subgroup K), α' x ∈ (Q₀ : Subgroup K) := by
    intro x hx
    have h1 : MulAut.conj k x ∈ (Q : Subgroup K) := by
      rw [hQeq]
      exact Subgroup.smul_mem_pointwise_smul x _ _ hx
    have h2 := hαmem _ h1
    rw [hQeq, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h2
    exact h2
  have hconj : (MulAut.conj k)⁻¹ * α * MulAut.conj k =
      (MulAut.conj k)⁻¹ * α * (MulAut.conj k)⁻¹⁻¹ := by rw [inv_inv]
  have hα'3 : α' ^ 3 = 1 := by
    rw [hα', hconj, conj_pow, hα, mul_one, mul_inv_cancel]
  obtain ⟨y', hy'3, hy'α, hy'c⟩ :=
    u62Aux_core hker hZ hTP hPT hcent hab hUT hU3 hUc Q₀ hQ₀P α' hα'3 hα'Q
  refine ⟨MulAut.conj k y', ?_, ?_, ?_⟩
  · rw [← map_pow, hy'3, map_one]
  · have h : (MulAut.conj k)⁻¹ (α (MulAut.conj k y')) = y' := hy'α
    calc α (MulAut.conj k y')
        = MulAut.conj k ((MulAut.conj k)⁻¹ (α (MulAut.conj k y'))) := by
          rw [MulAut.apply_inv_self]
      _ = MulAut.conj k y' := by rw [h]
  · intro hmem
    apply hy'c
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hmem
    refine Subgroup.mem_zpowers_iff.2 ⟨n, ?_⟩
    have hc : MulAut.conj (MulAut.conj k y') =
        MulAut.conj k * MulAut.conj y' * (MulAut.conj k)⁻¹ := by
      rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
    rw [hα', hconj, conj_zpow, hn, hc]
    group

end Core

end CFSG.HardMathSupport.Dickson.Bal207
