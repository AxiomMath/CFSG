module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCHGF2CenterFourCyclicRootsWeakClosure
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCHGF2CenterFourWidthFourRankFour
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCHGF2CenterFourWidthTwoCore
public import CFSG.LocalAnalysis.SteinbergCECyclicTwoQuotientFusion

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup CFSG.Open
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.ComponentInitial (bilinIsometryGroup)
open scoped IsMulCommutative commutatorElement Pointwise

namespace SteinbergCH

variable {G : Type*} [Group G]

theorem isElementaryAbelian_of_forall_sq_eq_one {H : Subgroup G} (h : ∀ x ∈ H, x ^ 2 = 1) :
    CFSG.IsElementaryAbelian 2 H where
  is_comm := ⟨fun x y => Subtype.ext (by
    have hinv : ∀ w ∈ H, w⁻¹ = w := fun w hw =>
      inv_eq_of_mul_eq_one_right (by rw [← sq, h w hw])
    have hxy := hinv _ (mul_mem x.2 y.2)
    rw [mul_inv_rev, hinv _ x.2, hinv _ y.2] at hxy
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact hxy.symm)⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
    Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact h x x.2)

theorem mem_sup_of_commute {H K : Subgroup G} (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {x : G} :
    x ∈ H ⊔ K ↔ ∃ h ∈ H, ∃ k ∈ K, h * k = x := by
  have hle : K ≤ normalizer (H : Set G) := fun k hk => mem_normalizer_iff.mpr fun h => by
    constructor
    · intro hh
      rw [← hc h hh k hk, mul_inv_cancel_right]
      exact hh
    · intro hh
      have h1 := hc _ hh k hk
      have h2 : h = k * h * k⁻¹ := by
        calc h = k⁻¹ * (k * h * k⁻¹ * k) := by group
          _ = k⁻¹ * (k * (k * h * k⁻¹)) := by rw [h1]
          _ = k * h * k⁻¹ := by group
      rw [h2]
      exact hh
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left H K hle, Set.mem_mul]
  rfl

theorem sq_mem_of_relIndex_eq_two {H K : Subgroup G} (h : H.relIndex K = 2) {x : G}
    (hx : x ∈ K) : x ^ 2 ∈ H := by
  have h1 := Subgroup.sq_mem_of_index_two (H := H.subgroupOf K) h ⟨x, hx⟩
  rw [mem_subgroupOf, Subgroup.coe_pow] at h1
  exact h1

theorem add_self_eq_zero_of_zmod_two {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (x : V) :
    x + x = 0 := by
  rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem lagrangian_of_ker_isotropic {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {b : LinearMap.BilinForm (ZMod 2) V} (hnd : b.Nondegenerate)
    {v : ℕ} (hdim : Module.finrank (ZMod 2) V = 2 * v) {T : Module.End (ZMod 2) V}
    (hT2 : ∀ x, T (T x) = x) {L : Submodule (ZMod 2) V} (hL : LinearMap.ker (T - 1) = L)
    (hiso : ∀ x ∈ L, ∀ y ∈ L, b x y = 0) :
    Module.finrank (ZMod 2) L = v ∧ LinearMap.range (T - 1) = L ∧ b.orthogonal L = L := by
  have hle : LinearMap.range (T - 1) ≤ LinearMap.ker (T - 1) := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.sub_apply, Module.End.one_apply,
      Module.End.one_apply, map_sub, hT2]
    calc x - T x - (T x - x) = (x + x) - (T x + T x) := by abel
      _ = 0 := by rw [add_self_eq_zero_of_zmod_two, add_self_eq_zero_of_zmod_two, sub_zero]
  have hrn := LinearMap.finrank_range_add_finrank_ker (T - 1)
  have h1 := Submodule.finrank_mono hle
  have hLorth : L ≤ b.orthogonal L := fun x hx y hy => hiso y hy x hx
  have h2 := Submodule.finrank_mono hLorth
  rw [LinearMap.BilinForm.finrank_orthogonal hnd] at h2
  rw [hL] at hrn h1
  have hLv : Module.finrank (ZMod 2) L = v := by omega
  refine ⟨hLv, Submodule.eq_of_le_of_finrank_eq (hL ▸ hle) (by omega), ?_⟩
  exact (Submodule.eq_of_le_of_finrank_eq hLorth
    (by rw [LinearMap.BilinForm.finrank_orthogonal hnd]; omega)).symm

theorem core_coe_mem {M Q : Subgroup G} (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M)
    (x : CFSG.pCore 2 M) : ((x : M) : G) ∈ Q := by
  rw [hQ]
  exact ⟨x, x.2, rfl⟩

theorem exists_core_coe {M Q : Subgroup G} (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M) {q : G}
    (hq : q ∈ Q) : ∃ x : CFSG.pCore 2 M, ((x : M) : G) = q := by
  rw [hQ] at hq
  obtain ⟨y, hy, rfl⟩ := hq
  exact ⟨⟨y, hy⟩, rfl⟩

theorem core_mem_center_iff {M Q : Subgroup G} (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M)
    (x : CFSG.pCore 2 M) :
    x ∈ center (CFSG.pCore 2 M) ↔ ((x : M) : G) ∈ (center Q).map Q.subtype := by
  constructor
  · intro hx
    refine ⟨⟨_, core_coe_mem hQ x⟩, mem_center_iff.mpr fun q => ?_, rfl⟩
    obtain ⟨y, hy⟩ := exists_core_coe hQ q.2
    apply Subtype.ext
    have h1 := congrArg (fun w : CFSG.pCore 2 M => ((w : M) : G)) (mem_center_iff.mp hx y)
    simp only [Subgroup.coe_mul] at h1
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hy]
    exact h1
  · rintro ⟨c, hc, hcx⟩
    rw [mem_center_iff]
    intro y
    have h1 := congrArg Subtype.val (mem_center_iff.mp hc ⟨_, core_coe_mem hQ y⟩)
    simp only [Subgroup.coe_mul] at h1
    rw [Subgroup.coe_subtype] at hcx
    rw [hcx] at h1
    exact Subtype.ext (Subtype.ext (by simpa using h1))

theorem core_ofMul_eq_iff {M Q : Subgroup G} (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M)
    (x y : CFSG.pCore 2 M) :
    Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)) =
        Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)) ↔
      ((x : M) : G)⁻¹ * ((y : M) : G) ∈ (center Q).map Q.subtype := by
  rw [Additive.ofMul.injective.eq_iff, QuotientGroup.eq, core_mem_center_iff hQ]
  simp

theorem bilin_eq_zero_iff_commute {M : Subgroup G} {z : G} (hz : orderOf z = 2)
    [CFSG.IsElementaryAbelian 2 (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))]
    {b : LinearMap.BilinForm (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))}
    (hrule : ∀ x y : CFSG.pCore 2 M, (((⁅x, y⁆ : CFSG.pCore 2 M) : M) : G) =
      z ^ (b (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
        (Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))).val)
    (x y : CFSG.pCore 2 M) :
    b (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
        (Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) = 0 ↔
      ((x : M) : G) * ((y : M) : G) = ((y : M) : G) * ((x : M) : G) := by
  have h := hrule x y
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz
    norm_num at hz
  have hcases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  constructor
  · intro h0
    rw [h0, ZMod.val_zero, pow_zero] at h
    have h1 : ⁅x, y⁆ = 1 := Subtype.ext (Subtype.ext h)
    rw [commutatorElement_eq_one_iff_mul_comm] at h1
    have h2 := congrArg (fun w : CFSG.pCore 2 M => ((w : M) : G)) h1
    simpa using h2
  · intro hc
    have h1 : ⁅x, y⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact Subtype.ext (Subtype.ext (by simpa using hc))
    rw [h1] at h
    rcases hcases (b (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
      (Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) with h0 | h0
    · exact h0
    · rw [h0, show (1 : ZMod 2).val = 1 from rfl, pow_one] at h
      exact absurd (by simpa using h.symm) hz1

theorem exists_core_conj {M : Subgroup G} {a : G} (haM : a ∈ M) (x : CFSG.pCore 2 M) :
    ∃ y : CFSG.pCore 2 M, ((y : M) : G) = a * ((x : M) : G) * a⁻¹ :=
  ⟨⟨⟨a, haM⟩ * (x : M) * (⟨a, haM⟩ : M)⁻¹, (CFSG.pCore_normal).conj_mem _ x.2 _⟩, rfl⟩

theorem action_apply_apply {M : Subgroup G}
    [CFSG.IsElementaryAbelian 2 (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))] {a : G}
    (haM : a ∈ M) (ha2 : a * a = 1)
    {T : Module.End (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))}
    (hT : ∀ x y : CFSG.pCore 2 M, ((y : M) : G) = a * ((x : M) : G) * a⁻¹ →
      T (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) =
        Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
    (x : Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) : T (T x) = x := by
  obtain ⟨x', rfl⟩ := Additive.ofMul.surjective x
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective x'
  obtain ⟨y₀, hy₀⟩ := exists_core_conj haM x₀
  obtain ⟨y₁, hy₁⟩ := exists_core_conj haM y₀
  rw [hT x₀ y₀ hy₀, hT y₀ y₁ hy₁]
  have h : ((y₁ : M) : G) = ((x₀ : M) : G) := by
    rw [hy₁, hy₀]
    calc a * (a * ((x₀ : M) : G) * a⁻¹) * a⁻¹ = (a * a) * ((x₀ : M) : G) * (a * a)⁻¹ := by
          group
      _ = ((x₀ : M) : G) := by rw [ha2, one_mul, inv_one, mul_one]
  rw [show y₁ = x₀ from Subtype.ext (Subtype.ext h)]

theorem action_sub_one_apply {M : Subgroup G}
    [CFSG.IsElementaryAbelian 2 (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))] {a : G}
    {T : Module.End (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))}
    (hT : ∀ x y : CFSG.pCore 2 M, ((y : M) : G) = a * ((x : M) : G) * a⁻¹ →
      T (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) =
        Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
    (x y : CFSG.pCore 2 M) (hy : ((y : M) : G) = a * ((x : M) : G) * a⁻¹) :
    (T - 1) (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) =
      Additive.ofMul ((x⁻¹ * y : CFSG.pCore 2 M) : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)) := by
  rw [LinearMap.sub_apply, Module.End.one_apply, hT x y hy, QuotientGroup.mk_mul,
    QuotientGroup.mk_inv, ofMul_mul, ofMul_inv]
  abel

theorem action_unique {M : Subgroup G}
    [CFSG.IsElementaryAbelian 2 (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))] {a : G}
    (haM : a ∈ M)
    {T T' : Module.End (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))}
    (hT : ∀ x y : CFSG.pCore 2 M, ((y : M) : G) = a * ((x : M) : G) * a⁻¹ →
      T (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) =
        Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
    (hT' : ∀ x y : CFSG.pCore 2 M, ((y : M) : G) = a * ((x : M) : G) * a⁻¹ →
      T' (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) =
        Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) : T = T' := by
  apply LinearMap.ext
  intro x
  obtain ⟨x', rfl⟩ := Additive.ofMul.surjective x
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective x'
  obtain ⟨y₀, hy₀⟩ := exists_core_conj haM x₀
  rw [hT x₀ y₀ hy₀, hT' x₀ y₀ hy₀]

theorem card_eq_card_inf_center_mul_card_image {M Q : Subgroup G}
    (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M) {H : Subgroup G} (hHQ : H ≤ Q) [Finite H] :
    Nat.card H = Nat.card ↥(H ⊓ (center Q).map Q.subtype) *
      Nat.card {x : Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)) //
        ∃ q : CFSG.pCore 2 M, ((q : M) : G) ∈ H ∧
          x = Additive.ofMul (q : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))} := by
  classical
  obtain ⟨e, heval⟩ : ∃ e : CFSG.pCore 2 M ≃* Q,
      ∀ x : CFSG.pCore 2 M, ((e x : Q) : G) = ((x : M) : G) := by
    subst hQ
    exact ⟨(CFSG.pCore 2 M).equivMapOfInjective M.subtype M.subtype_injective, fun _ => rfl⟩
  let φ : H →* CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M) :=
    (QuotientGroup.mk' _).comp (e.symm.toMonoidHom.comp (Subgroup.inclusion hHQ))
  have hφ : ∀ h : H, φ h = ((e.symm (Subgroup.inclusion hHQ h) : CFSG.pCore 2 M) :
      CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)) := fun _ => rfl
  have hj : ∀ h : H, (((e.symm (Subgroup.inclusion hHQ h) : CFSG.pCore 2 M) : M) : G) = h :=
    fun h => by rw [← heval, MulEquiv.apply_symm_apply]; rfl
  have hker : φ.ker = (H ⊓ (center Q).map Q.subtype).subgroupOf H := by
    ext h
    rw [MonoidHom.mem_ker, hφ, QuotientGroup.eq_one_iff, core_mem_center_iff hQ, hj,
      mem_subgroupOf, mem_inf]
    exact ⟨fun h1 => ⟨h.2, h1⟩, fun h1 => h1.2⟩
  have hrange : ∀ x, x ∈ φ.range ↔ ∃ q : CFSG.pCore 2 M, ((q : M) : G) ∈ H ∧
      Additive.ofMul x = Additive.ofMul (q : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)) := by
    intro x
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨e.symm (Subgroup.inclusion hHQ h), by rw [hj]; exact h.2, by rw [hφ]⟩
    · rintro ⟨q, hqH, hx⟩
      refine ⟨⟨_, hqH⟩, ?_⟩
      rw [hφ, Additive.ofMul.injective hx]
      congr 1
      apply e.injective
      rw [MulEquiv.apply_symm_apply]
      exact Subtype.ext (heval q).symm
  have h1 := card_eq_card_quotient_mul_card_subgroup φ.ker
  have h2 : Nat.card φ.range = Nat.card {x : Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)) //
      ∃ q : CFSG.pCore 2 M, ((q : M) : G) ∈ H ∧
        x = Additive.ofMul (q : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))} :=
    Nat.card_congr (Equiv.subtypeEquiv Additive.ofMul hrange)
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hker,
    Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv, h2] at h1
  rw [h1, mul_comm]

theorem exists_fixed_lift {Q Z : Subgroup G} {z c a q : G} (hz : orderOf z = 2) (hzZ : z ∈ Z)
    (huniq : ∀ y ∈ Z, orderOf y = 2 → y = z) (hcZ : c ∈ Z) (hcz : c ^ 2 = z)
    (hZQ : ∀ w ∈ Z, ∀ x ∈ Q, w * x = x * w) (hainv : ∀ w ∈ Z, a * w * a⁻¹ = w⁻¹)
    (hsq : q ^ 2 ∈ zpowers z) (hq : q ∈ Q) (hfix : q⁻¹ * (a * q * a⁻¹) ∈ Z) :
    ∃ w ∈ Z, a * (q * w) * a⁻¹ = q * w := by
  have := Fact.mk Nat.prime_two
  set y := q⁻¹ * (a * q * a⁻¹) with hy
  have haqy : a * q * a⁻¹ = q * y := by rw [hy]; group
  have hz2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have haz : a * z * a⁻¹ = z := by
    rw [hainv z hzZ]
    exact inv_eq_of_mul_eq_one_right (by rw [← sq, hz2])
  have hsq' : a * q ^ 2 * a⁻¹ = q ^ 2 := by
    rcases eq_one_or_eq_of_mem_zpowers hz hsq with h | h <;> rw [h]
    · group
    · exact haz
  have hy2 : y ^ 2 = 1 := by
    have h1 : (a * q * a⁻¹) ^ 2 = q ^ 2 := by
      rw [← hsq', sq, sq]
      group
    rw [haqy] at h1
    have hyq : y * q = q * y := hZQ y hfix q hq
    have h2 : (q * y) ^ 2 = q ^ 2 * y ^ 2 := by
      calc (q * y) ^ 2 = q * (y * q) * y := by rw [sq]; group
        _ = q * (q * y) * y := by rw [hyq]
        _ = q ^ 2 * y ^ 2 := by rw [sq, sq]; group
    rw [h2] at h1
    exact mul_left_cancel (h1.trans (mul_one _).symm)
  have hy' : y = 1 ∨ y = z := by
    by_cases h1 : y = 1
    · exact Or.inl h1
    · exact Or.inr (huniq y hfix (orderOf_eq_prime hy2 h1))
  rcases hy' with h1 | h1
  · refine ⟨1, one_mem _, ?_⟩
    rw [mul_one, haqy, h1, mul_one]
  · refine ⟨c, hcZ, ?_⟩
    calc a * (q * c) * a⁻¹ = (a * q * a⁻¹) * (a * c * a⁻¹) := by group
      _ = q * z * c⁻¹ := by rw [haqy, h1, hainv c hcZ]
      _ = q * c := by rw [← hcz]; group

theorem center_map_commute {Q : Subgroup G} {w x : G} (hw : w ∈ (center Q).map Q.subtype)
    (hx : x ∈ Q) : w * x = x * w := by
  obtain ⟨c, hc, rfl⟩ := hw
  exact (congrArg Subtype.val (mem_center_iff.mp hc ⟨x, hx⟩)).symm

theorem core_fixed_lagrangian [Finite G] {M Q : Subgroup G}
    (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M) {z c a : G} (hz : orderOf z = 2)
    (hzZ : z ∈ (center Q).map Q.subtype)
    (huniq : ∀ y ∈ (center Q).map Q.subtype, orderOf y = 2 → y = z)
    (hcZ : c ∈ (center Q).map Q.subtype) (hcz : c ^ 2 = z) (haM : a ∈ M) (ha2 : a * a = 1)
    (hainv : ∀ w ∈ (center Q).map Q.subtype, a * w * a⁻¹ = w⁻¹)
    (hsq : ∀ q ∈ Q, q ^ 2 ∈ zpowers z)
    (hPcomm : ∀ p ∈ Q ⊓ centralizer ({a} : Set G), ∀ p' ∈ Q ⊓ centralizer ({a} : Set G),
      p * p' = p' * p)
    [CFSG.IsElementaryAbelian 2 (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))]
    {b : LinearMap.BilinForm (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))}
    (hrule : ∀ x y : CFSG.pCore 2 M, (((⁅x, y⁆ : CFSG.pCore 2 M) : M) : G) =
      z ^ (b (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
        (Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))).val)
    (hnd : b.Nondegenerate) {v : ℕ}
    (hdim : Module.finrank (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) =
      2 * v)
    {T : Module.End (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))}
    (hT : ∀ x y : CFSG.pCore 2 M, ((y : M) : G) = a * ((x : M) : G) * a⁻¹ →
      T (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) =
        Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) :
    ∃ L : Submodule (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))),
      (∀ x, x ∈ L ↔ ∃ q : CFSG.pCore 2 M, ((q : M) : G) ∈ Q ⊓ centralizer ({a} : Set G) ∧
        x = Additive.ofMul (q : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) ∧
      (∀ x ∈ L, ∀ y ∈ L, b x y = 0) ∧ Module.finrank (ZMod 2) L = v ∧ b.orthogonal L = L ∧
      LinearMap.range (T - 1) = L ∧ LinearMap.ker (T - 1) = L := by
  classical
  have : Finite (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) :=
    inferInstanceAs (Finite (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
  have : FiniteDimensional (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) :=
    Module.Finite.of_finite
  have hcases : ∀ r : ZMod 2, r = 0 ∨ r = 1 := by decide
  let L : Submodule (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) :=
    { carrier := {x | ∃ q : CFSG.pCore 2 M, ((q : M) : G) ∈ Q ⊓ centralizer ({a} : Set G) ∧
        x = Additive.ofMul (q : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))}
      add_mem' := by
        rintro _ _ ⟨q, hq, rfl⟩ ⟨q', hq', rfl⟩
        refine ⟨q * q', ?_, ?_⟩
        · rw [Subgroup.coe_mul, Subgroup.coe_mul]
          exact mul_mem hq hq'
        · rw [QuotientGroup.mk_mul, ofMul_mul]
      zero_mem' := ⟨1, one_mem _, by rw [QuotientGroup.mk_one, ofMul_one]⟩
      smul_mem' := by
        rintro r _ ⟨q, hq, rfl⟩
        rcases hcases r with rfl | rfl
        · refine ⟨1, one_mem _, ?_⟩
          rw [zero_smul, QuotientGroup.mk_one, ofMul_one]
        · exact ⟨q, hq, one_smul _ _⟩ }
  have hmem : ∀ x, x ∈ L ↔ ∃ q : CFSG.pCore 2 M, ((q : M) : G) ∈ Q ⊓ centralizer ({a} : Set G) ∧
      x = Additive.ofMul (q : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)) := fun _ => Iff.rfl
  have hiso : ∀ x ∈ L, ∀ y ∈ L, b x y = 0 := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨p', hp', rfl⟩
    exact (bilin_eq_zero_iff_commute hz hrule p p').mpr (hPcomm _ hp _ hp')
  have hker : LinearMap.ker (T - 1) = L := by
    ext x
    rw [LinearMap.mem_ker]
    constructor
    · intro hx
      obtain ⟨x', rfl⟩ := Additive.ofMul.surjective x
      obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective x'
      obtain ⟨y₀, hy₀⟩ := exists_core_conj haM x₀
      rw [action_sub_one_apply hT x₀ y₀ hy₀] at hx
      have hfix : ((x₀ : M) : G)⁻¹ * (a * ((x₀ : M) : G) * a⁻¹) ∈ (center Q).map Q.subtype := by
        have h1 : (x₀⁻¹ * y₀ : CFSG.pCore 2 M) ∈ center (CFSG.pCore 2 M) := by
          rw [← QuotientGroup.eq_one_iff]
          exact Additive.ofMul.injective (hx.trans ofMul_one.symm)
        rw [core_mem_center_iff hQ] at h1
        rw [← hy₀]
        simpa using h1
      obtain ⟨w, hwZ, hw⟩ := exists_fixed_lift hz hzZ huniq hcZ hcz
        (fun w hw x hx => center_map_commute hw hx) hainv (hsq _ (core_coe_mem hQ x₀))
        (core_coe_mem hQ x₀) hfix
      obtain ⟨w₀, hw₀⟩ := exists_core_coe hQ (map_subtype_le _ hwZ)
      refine ⟨x₀ * w₀, ?_, ?_⟩
      · rw [Subgroup.coe_mul, Subgroup.coe_mul, hw₀]
        refine mem_inf.mpr ⟨mul_mem (core_coe_mem hQ x₀) (map_subtype_le _ hwZ), ?_⟩
        rw [mem_centralizer_singleton_iff]
        rw [mul_inv_eq_iff_eq_mul] at hw
        exact hw.symm
      · have hw0 : Additive.ofMul (w₀ : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)) = 0 := by
          rw [← ofMul_one, ← QuotientGroup.mk_one]
          refine Additive.ofMul.injective.eq_iff.mpr (QuotientGroup.eq_one_iff _ |>.mpr ?_)
          rw [core_mem_center_iff hQ, hw₀]
          exact hwZ
        rw [QuotientGroup.mk_mul, ofMul_mul, hw0, add_zero]
    · rintro ⟨p, hp, rfl⟩
      have hp' : ((p : M) : G) = a * ((p : M) : G) * a⁻¹ := by
        rw [← mem_centralizer_singleton_iff.mp (mem_inf.mp hp).2, mul_inv_cancel_right]
      rw [LinearMap.sub_apply, Module.End.one_apply, hT p p hp', sub_self]
  obtain ⟨hLv, hrange, horth⟩ :=
    lagrangian_of_ker_isotropic hnd hdim (action_apply_apply haM ha2 hT) hker hiso
  exact ⟨L, hmem, hiso, hLv, horth, hrange, hker⟩

theorem card_fixed_core [Finite G] {M Q : Subgroup G}
    (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M) {z a : G} (hz : orderOf z = 2)
    (hzZ : z ∈ (center Q).map Q.subtype)
    (huniq : ∀ y ∈ (center Q).map Q.subtype, orderOf y = 2 → y = z)
    (hainv : ∀ w ∈ (center Q).map Q.subtype, a * w * a⁻¹ = w⁻¹)
    [CFSG.IsElementaryAbelian 2 (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))]
    {L : Submodule (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))}
    (hmem : ∀ x, x ∈ L ↔ ∃ q : CFSG.pCore 2 M, ((q : M) : G) ∈ Q ⊓ centralizer ({a} : Set G) ∧
      x = Additive.ofMul (q : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
    {v : ℕ} (hLv : Module.finrank (ZMod 2) L = v) :
    Q ⊓ centralizer ({a} : Set G) ⊓ (center Q).map Q.subtype = zpowers z ∧
      Nat.card ↥(Q ⊓ centralizer ({a} : Set G)) = 2 ^ (v + 1) := by
  have := Fact.mk Nat.prime_two
  have : Finite (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) :=
    inferInstanceAs (Finite (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
  have hinf : Q ⊓ centralizer ({a} : Set G) ⊓ (center Q).map Q.subtype = zpowers z := by
    apply le_antisymm
    · intro w hw
      obtain ⟨hwP, hwZ⟩ := mem_inf.mp hw
      have hwa := mem_centralizer_singleton_iff.mp (mem_inf.mp hwP).2
      have h1 : w⁻¹ = w := by
        calc w⁻¹ = a * w * a⁻¹ := (hainv w hwZ).symm
          _ = w := by rw [← hwa, mul_inv_cancel_right]
      have h2 : w ^ 2 = 1 := by
        rw [sq]
        calc w * w = w⁻¹ * w := by rw [h1]
          _ = 1 := inv_mul_cancel w
      by_cases hw1 : w = 1
      · rw [hw1]
        exact one_mem _
      · rw [huniq w hwZ (orderOf_eq_prime h2 hw1)]
        exact mem_zpowers z
    · rw [zpowers_le]
      refine mem_inf.mpr ⟨mem_inf.mpr ⟨map_subtype_le _ hzZ, ?_⟩, hzZ⟩
      rw [mem_centralizer_singleton_iff]
      have h1 : a * z * a⁻¹ = z := by rw [hainv z hzZ, inv_eq_self_of_orderOf_eq_two hz]
      rw [mul_inv_eq_iff_eq_mul] at h1
      exact h1.symm
  refine ⟨hinf, ?_⟩
  have hc := card_eq_card_inf_center_mul_card_image hQ
    (inf_le_left : Q ⊓ centralizer ({a} : Set G) ≤ Q)
  rw [hinf, Nat.card_zpowers, hz] at hc
  have hL : Nat.card {x : Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)) //
      ∃ q : CFSG.pCore 2 M, ((q : M) : G) ∈ Q ⊓ centralizer ({a} : Set G) ∧
        x = Additive.ofMul (q : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))} = 2 ^ v := by
    rw [← Nat.card_congr (Equiv.subtypeEquivRight hmem), natCard_eq_two_pow_finrank, hLv]
  rw [hc, hL, pow_succ, mul_comm]

theorem centralizer_fixed_core_eq [Finite G] {M Q : Subgroup G}
    (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M) {z a : G} (hz : orderOf z = 2)
    (hPcomm : ∀ p ∈ Q ⊓ centralizer ({a} : Set G), ∀ p' ∈ Q ⊓ centralizer ({a} : Set G),
      p * p' = p' * p)
    [CFSG.IsElementaryAbelian 2 (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))]
    {b : LinearMap.BilinForm (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))}
    (hrule : ∀ x y : CFSG.pCore 2 M, (((⁅x, y⁆ : CFSG.pCore 2 M) : M) : G) =
      z ^ (b (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
        (Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))).val)
    {L : Submodule (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))}
    (hmem : ∀ x, x ∈ L ↔ ∃ q : CFSG.pCore 2 M, ((q : M) : G) ∈ Q ⊓ centralizer ({a} : Set G) ∧
      x = Additive.ofMul (q : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
    (horth : b.orthogonal L = L) :
    Q ⊓ centralizer ((Q ⊓ centralizer ({a} : Set G) : Subgroup G) : Set G) =
      (center Q).map Q.subtype ⊔ Q ⊓ centralizer ({a} : Set G) := by
  apply le_antisymm
  · rintro q ⟨hqQ, hqC⟩
    obtain ⟨q₀, rfl⟩ := exists_core_coe hQ hqQ
    have hqL : Additive.ofMul (q₀ : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)) ∈ L := by
      rw [← horth, LinearMap.BilinForm.mem_orthogonal_iff]
      intro n hn
      obtain ⟨p, hp, rfl⟩ := (hmem n).mp hn
      exact (bilin_eq_zero_iff_commute hz hrule p q₀).mpr (mem_centralizer_iff.mp hqC _ hp)
    obtain ⟨p, hp, hpq⟩ := (hmem _).mp hqL
    have hw := (core_ofMul_eq_iff hQ q₀ p).mp hpq
    have h1 : ((q₀ : M) : G) =
        ((p : M) : G) * (((q₀ : M) : G)⁻¹ * ((p : M) : G))⁻¹ := by group
    rw [h1]
    exact mul_mem (mem_sup_right hp) (mem_sup_left (inv_mem hw))
  · refine sup_le (fun w hw => ⟨map_subtype_le _ hw, mem_centralizer_iff.mpr fun p hp => ?_⟩)
      fun p hp => ⟨(mem_inf.mp hp).1, mem_centralizer_iff.mpr fun p' hp' => hPcomm _ hp' _ hp⟩
    exact (center_map_commute hw (mem_inf.mp hp).1).symm

theorem commutator_mem_sup_fixed [Finite G] {M Q : Subgroup G}
    (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M) {a : G} (haM : a ∈ M)
    [CFSG.IsElementaryAbelian 2 (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))]
    {T : Module.End (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))}
    (hT : ∀ x y : CFSG.pCore 2 M, ((y : M) : G) = a * ((x : M) : G) * a⁻¹ →
      T (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) =
        Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
    {L : Submodule (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))}
    (hmem : ∀ x, x ∈ L ↔ ∃ q : CFSG.pCore 2 M, ((q : M) : G) ∈ Q ⊓ centralizer ({a} : Set G) ∧
      x = Additive.ofMul (q : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
    (hrange : LinearMap.range (T - 1) = L) {q : G} (hq : q ∈ Q) :
    q⁻¹ * (a * q * a⁻¹) ∈ (center Q).map Q.subtype ⊔ Q ⊓ centralizer ({a} : Set G) := by
  obtain ⟨q₀, rfl⟩ := exists_core_coe hQ hq
  obtain ⟨y₀, hy₀⟩ := exists_core_conj haM q₀
  have h1 : Additive.ofMul ((q₀⁻¹ * y₀ : CFSG.pCore 2 M) :
      CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)) ∈ L := by
    rw [← hrange, ← action_sub_one_apply hT q₀ y₀ hy₀]
    exact LinearMap.mem_range_self _ _
  obtain ⟨p, hp, hpq⟩ := (hmem _).mp h1
  have hw := (core_ofMul_eq_iff hQ _ p).mp hpq
  have hd : (((q₀⁻¹ * y₀ : CFSG.pCore 2 M) : M) : G) =
      ((q₀ : M) : G)⁻¹ * (a * ((q₀ : M) : G) * a⁻¹) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv, hy₀]
  rw [hd] at hw
  have h2 : ((q₀ : M) : G)⁻¹ * (a * ((q₀ : M) : G) * a⁻¹) = ((p : M) : G) *
      ((((q₀ : M) : G)⁻¹ * (a * ((q₀ : M) : G) * a⁻¹))⁻¹ * ((p : M) : G))⁻¹ := by group
  rw [h2]
  exact mul_mem (mem_sup_right hp) (inv_mem (mem_sup_left hw))

theorem image_commutator_set {M Q : Subgroup G} (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M)
    {a : G} (haM : a ∈ M)
    [CFSG.IsElementaryAbelian 2 (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))]
    {T : Module.End (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))}
    (hT : ∀ x y : CFSG.pCore 2 M, ((y : M) : G) = a * ((x : M) : G) * a⁻¹ →
      T (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) =
        Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
    {D : Subgroup G} (hD : ∀ x, x ∈ D ↔ ∃ q ∈ Q, x = q⁻¹ * (a * q * a⁻¹))
    (x : Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) :
    (∃ d : CFSG.pCore 2 M, ((d : M) : G) ∈ D ∧
      x = Additive.ofMul (d : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) ↔
      x ∈ LinearMap.range (T - 1) := by
  have hcomm : ∀ q₀ y₀ : CFSG.pCore 2 M, ((y₀ : M) : G) = a * ((q₀ : M) : G) * a⁻¹ →
      (((q₀⁻¹ * y₀ : CFSG.pCore 2 M) : M) : G) =
        ((q₀ : M) : G)⁻¹ * (a * ((q₀ : M) : G) * a⁻¹) := fun q₀ y₀ hy => by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv, hy]
  constructor
  · rintro ⟨d, hdD, rfl⟩
    obtain ⟨q, hq, hdq⟩ := (hD _).mp hdD
    obtain ⟨q₀, rfl⟩ := exists_core_coe hQ hq
    obtain ⟨y₀, hy₀⟩ := exists_core_conj haM q₀
    have hd : d = q₀⁻¹ * y₀ := Subtype.ext (Subtype.ext (hdq.trans (hcomm q₀ y₀ hy₀).symm))
    rw [hd, ← action_sub_one_apply hT q₀ y₀ hy₀]
    exact LinearMap.mem_range_self _ _
  · rintro ⟨x', rfl⟩
    obtain ⟨x'', rfl⟩ := Additive.ofMul.surjective x'
    obtain ⟨q₀, rfl⟩ := QuotientGroup.mk_surjective x''
    obtain ⟨y₀, hy₀⟩ := exists_core_conj haM q₀
    refine ⟨q₀⁻¹ * y₀, (hD _).mpr ⟨_, core_coe_mem hQ q₀, hcomm q₀ y₀ hy₀⟩, ?_⟩
    exact action_sub_one_apply hT q₀ y₀ hy₀

theorem commutator_set_package {Q Z : Subgroup G} {z c a : G} (hz : orderOf z = 2)
    (hzZ : z ∈ Z) (hcZ : c ∈ Z) (hcz : c ^ 2 = z) (hZQ : Z ≤ Q)
    (hZcomm : ∀ w ∈ Z, ∀ x ∈ Q, w * x = x * w) (hainv : ∀ w ∈ Z, a * w * a⁻¹ = w⁻¹)
    (ha : orderOf a = 2) (haQ : ∀ q ∈ Q, a * q * a⁻¹ ∈ Q) (hQ' : ⁅Q, Q⁆ = zpowers z) :
    ∃ D : Subgroup G, (∀ x, x ∈ D ↔ ∃ q ∈ Q, x = q⁻¹ * (a * q * a⁻¹)) ∧ D = ⁅Q, zpowers a⁆ ∧
      D ≤ Q ∧ z ∈ D ∧ (D.subgroupOf Q).Normal := by
  have ha2 : a * a = 1 := by rw [← sq, ← ha]; exact pow_orderOf_eq_one a
  have hzinv : z⁻¹ = z := inv_eq_self_of_orderOf_eq_two hz
  have hz2 : z * z = 1 := by rw [← sq, ← hz]; exact pow_orderOf_eq_one z
  have hcQ : c ∈ Q := hZQ hcZ
  have hdQ : ∀ q ∈ Q, q⁻¹ * (a * q * a⁻¹) ∈ Q := fun q hq => mul_mem (inv_mem hq) (haQ q hq)
  have hdz : ∀ q ∈ Q, (q * c)⁻¹ * (a * (q * c) * a⁻¹) = q⁻¹ * (a * q * a⁻¹) * z := by
    intro q hq
    have h1 : a * (q * c) * a⁻¹ = (a * q * a⁻¹) * c⁻¹ := by
      rw [← hainv c hcZ]
      group
    have hc1 : c⁻¹ * (q⁻¹ * (a * q * a⁻¹)) = (q⁻¹ * (a * q * a⁻¹)) * c⁻¹ :=
      hZcomm c⁻¹ (inv_mem hcZ) _ (hdQ q hq)
    rw [h1]
    calc (q * c)⁻¹ * (a * q * a⁻¹ * c⁻¹) = c⁻¹ * (q⁻¹ * (a * q * a⁻¹)) * c⁻¹ := by group
      _ = q⁻¹ * (a * q * a⁻¹) * (c ^ 2)⁻¹ := by rw [hc1, sq]; group
      _ = q⁻¹ * (a * q * a⁻¹) * z := by rw [hcz, hzinv]
  have hmul : ∀ q₁ ∈ Q, ∀ q₂ ∈ Q,
      q₁⁻¹ * (a * q₁ * a⁻¹) * (q₂⁻¹ * (a * q₂ * a⁻¹)) = (q₁ * q₂)⁻¹ * (a * (q₁ * q₂) * a⁻¹) ∨
      q₁⁻¹ * (a * q₁ * a⁻¹) * (q₂⁻¹ * (a * q₂ * a⁻¹)) =
        (q₁ * q₂)⁻¹ * (a * (q₁ * q₂) * a⁻¹) * z := by
    intro q₁ hq₁ q₂ hq₂
    have hd₁Q := hdQ q₁ hq₁
    have hd₂Q := hdQ q₂ hq₂
    have h1 : (q₁ * q₂)⁻¹ * (a * (q₁ * q₂) * a⁻¹) =
        (q₂⁻¹ * (q₁⁻¹ * (a * q₁ * a⁻¹)) * q₂) * (q₂⁻¹ * (a * q₂ * a⁻¹)) := by group
    have h2 : q₂⁻¹ * (q₁⁻¹ * (a * q₁ * a⁻¹)) * q₂ =
        q₁⁻¹ * (a * q₁ * a⁻¹) * ⁅(q₁⁻¹ * (a * q₁ * a⁻¹))⁻¹, q₂⁻¹⁆ := by
      rw [commutatorElement_def]
      group
    have h3 : ⁅(q₁⁻¹ * (a * q₁ * a⁻¹))⁻¹, q₂⁻¹⁆ ∈ zpowers z := by
      rw [← hQ']
      exact commutator_mem_commutator (inv_mem hd₁Q) (inv_mem hq₂)
    rcases eq_one_or_eq_of_mem_zpowers hz h3 with h4 | h4
    · left
      rw [h1, h2, h4, mul_one]
    · right
      rw [h1, h2, h4]
      have hzd := hZcomm z hzZ _ hd₂Q
      calc q₁⁻¹ * (a * q₁ * a⁻¹) * (q₂⁻¹ * (a * q₂ * a⁻¹)) =
          q₁⁻¹ * (a * q₁ * a⁻¹) * (q₂⁻¹ * (a * q₂ * a⁻¹)) * (z * z) := by rw [hz2, mul_one]
        _ = q₁⁻¹ * (a * q₁ * a⁻¹) * ((q₂⁻¹ * (a * q₂ * a⁻¹)) * z) * z := by group
        _ = q₁⁻¹ * (a * q₁ * a⁻¹) * z * (q₂⁻¹ * (a * q₂ * a⁻¹)) * z := by rw [← hzd]; group
  have hconj : ∀ q : G, a * (a * q * a⁻¹) * a⁻¹ = q := fun q => by
    calc a * (a * q * a⁻¹) * a⁻¹ = (a * a) * q * (a * a)⁻¹ := by group
      _ = q := by rw [ha2, one_mul, inv_one, mul_one]
  have hinvd : ∀ q : G, (q⁻¹ * (a * q * a⁻¹))⁻¹ =
      (a * q * a⁻¹)⁻¹ * (a * (a * q * a⁻¹) * a⁻¹) := fun q => by
    rw [hconj]
    group
  let D : Subgroup G :=
    { carrier := {x | ∃ q ∈ Q, x = q⁻¹ * (a * q * a⁻¹)}
      mul_mem' := by
        rintro _ _ ⟨q₁, hq₁, rfl⟩ ⟨q₂, hq₂, rfl⟩
        rcases hmul q₁ hq₁ q₂ hq₂ with h | h
        · exact ⟨q₁ * q₂, mul_mem hq₁ hq₂, h⟩
        · exact ⟨q₁ * q₂ * c, mul_mem (mul_mem hq₁ hq₂) hcQ,
            h.trans (hdz _ (mul_mem hq₁ hq₂)).symm⟩
      one_mem' := ⟨1, one_mem _, by group⟩
      inv_mem' := by
        rintro _ ⟨q, hq, rfl⟩
        exact ⟨a * q * a⁻¹, haQ q hq, hinvd q⟩ }
  have hmemD : ∀ x, x ∈ D ↔ ∃ q ∈ Q, x = q⁻¹ * (a * q * a⁻¹) := fun _ => Iff.rfl
  have hzD : z ∈ D := by
    refine ⟨c, hcQ, ?_⟩
    rw [hainv c hcZ, ← hzinv, ← hcz, sq]
    group
  refine ⟨D, hmemD, ?_, fun x hx => ?_, hzD, ⟨fun n hn g => ?_⟩⟩
  · apply le_antisymm
    · rintro _ ⟨q, hq, rfl⟩
      have h1 : q⁻¹ * (a * q * a⁻¹) = ⁅q⁻¹, a⁆ := by
        rw [commutatorElement_def, inv_inv]
        group
      rw [h1]
      exact commutator_mem_commutator (inv_mem hq) (mem_zpowers a)
    · rw [commutator_le]
      intro q hq k hk
      rcases eq_one_or_eq_of_mem_zpowers ha hk with rfl | rfl
      · rw [commutatorElement_one_right]
        exact one_mem _
      · refine ⟨q⁻¹, inv_mem hq, ?_⟩
        rw [commutatorElement_def, inv_inv]
        group
  · obtain ⟨q, hq, rfl⟩ := (hmemD x).mp hx
    exact hdQ q hq
  · rw [mem_subgroupOf] at hn ⊢
    have h1 : ((g * n * g⁻¹ : Q) : G) = (n : G) * ⁅(n : G)⁻¹, (g : G)⁆ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [h1]
    refine mul_mem hn ?_
    have h2 : ⁅(n : G)⁻¹, (g : G)⁆ ∈ zpowers z := by
      rw [← hQ']
      exact commutator_mem_commutator (inv_mem n.2) g.2
    exact (zpowers_le.mpr hzD) h2

theorem conj_class_eq_mul {Q D : Subgroup G} {a : G} (ha2 : a * a = 1)
    (haQ : ∀ q ∈ Q, a * q * a⁻¹ ∈ Q) (hD : ∀ x, x ∈ D ↔ ∃ q ∈ Q, x = q⁻¹ * (a * q * a⁻¹)) :
    {w | ∃ q ∈ Q, q⁻¹ * a * q = w} = {w | ∃ d ∈ D, a * d = w} := by
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hconj : ∀ q : G, a * (a * q * a⁻¹) * a⁻¹ = q := fun q => by
    calc a * (a * q * a⁻¹) * a⁻¹ = (a * a) * q * (a * a)⁻¹ := by group
      _ = q := by rw [ha2, one_mul, inv_one, mul_one]
  ext w
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨(a * q * a⁻¹)⁻¹ * (a * (a * q * a⁻¹) * a⁻¹), (hD _).mpr ⟨_, haQ q hq, rfl⟩, ?_⟩
    calc a * ((a * q * a⁻¹)⁻¹ * (a * (a * q * a⁻¹) * a⁻¹)) = (a * a) * q⁻¹ * a⁻¹ * q := by
          rw [hconj]
          group
      _ = q⁻¹ * a * q := by rw [ha2, one_mul, hainv]
  · rintro ⟨d, hd, rfl⟩
    obtain ⟨q, hq, rfl⟩ := (hD d).mp hd
    exact ⟨a * q * a⁻¹, haQ q hq, by group⟩

theorem mem_of_mem_sup_of_sq_eq_one {Q Z P : Subgroup G} {z : G}
    (huniq : ∀ y ∈ Z, orderOf y = 2 → y = z) (hzP : z ∈ P) (hPQ : P ≤ Q)
    (hZQ : ∀ w ∈ Z, ∀ x ∈ Q, w * x = x * w) (hPsq : ∀ p ∈ P, p ^ 2 = 1) {x : G}
    (hx : x ∈ Z ⊔ P) (hx2 : x ^ 2 = 1) : x ∈ P := by
  have := Fact.mk Nat.prime_two
  obtain ⟨w, hw, p, hp, rfl⟩ :=
    (mem_sup_of_commute fun w hw p hp => hZQ w hw p (hPQ hp)).mp hx
  have hw2 : w ^ 2 = 1 := by
    have h1 : (w * p) ^ 2 = w ^ 2 * p ^ 2 := by
      rw [sq, sq, sq]
      calc w * p * (w * p) = w * (p * w) * p := by group
        _ = w * (w * p) * p := by rw [← hZQ w hw p (hPQ hp)]
        _ = w * w * (p * p) := by group
    rw [h1, hPsq p hp, mul_one] at hx2
    exact hx2
  have hwP : w ∈ P := by
    by_cases hw1 : w = 1
    · rw [hw1]
      exact one_mem _
    · rw [huniq w hw (orderOf_eq_prime hw2 hw1)]
      exact hzP
  exact mul_mem hwP hp

theorem sup_isMulCommutative_of_commute {Q Z P : Subgroup G} (hZQle : Z ≤ Q) (hPQ : P ≤ Q)
    (hZQ : ∀ w ∈ Z, ∀ x ∈ Q, w * x = x * w) (hPcomm : ∀ p ∈ P, ∀ p' ∈ P, p * p' = p' * p) :
    IsMulCommutative ↥(Z ⊔ P) := by
  have hc : ∀ w ∈ Z, ∀ p ∈ P, w * p = p * w := fun w hw p hp => hZQ w hw p (hPQ hp)
  refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
  obtain ⟨w, hw, p, hp, hx⟩ := (mem_sup_of_commute hc).mp x.2
  obtain ⟨w', hw', p', hp', hy⟩ := (mem_sup_of_commute hc).mp y.2
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hx, ← hy]
  have h1 : w * w' = w' * w := hZQ w hw w' (hZQle hw')
  calc w * p * (w' * p') = w * (p * w') * p' := by group
    _ = w * (w' * p) * p' := by rw [hc w' hw' p hp]
    _ = (w * w') * (p * p') := by group
    _ = (w' * w) * (p' * p) := by rw [h1, hPcomm p hp p' hp']
    _ = w' * (w * p') * p := by group
    _ = w' * (p' * w) * p := by rw [hc w hw p' hp']
    _ = w' * p' * (w * p) := by group

theorem exists_compl_zpowers {E : Subgroup G} [hE : CFSG.IsElementaryAbelian 2 E] [Finite E]
    {z : G} (hz : orderOf z = 2) (hzE : z ∈ E) :
    ∃ W : Subgroup G, W ≤ E ∧ zpowers z ⊓ W = ⊥ ∧ zpowers z ⊔ W = E ∧ (∀ w ∈ W, w ^ 2 = 1) ∧
      Nat.card E = 2 * Nat.card W := by
  have := Fact.mk Nat.prime_two
  obtain ⟨C, hC⟩ := CFSG.IsElementaryAbelian.exists_isCompl 2 E ((zpowers z).subgroupOf E)
  have hcommE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hinf : zpowers z ⊓ C.map E.subtype = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxz, y, hy, rfl⟩ := mem_inf.mp hx
    have hyB : y ∈ (zpowers z).subgroupOf E := mem_subgroupOf.mpr hxz
    have h1 := hC.disjoint.le_bot ⟨hyB, hy⟩
    rw [mem_bot] at h1 ⊢
    rw [h1]
    rfl
  have hsup : zpowers z ⊔ C.map E.subtype = E := by
    have h1 := congrArg (map E.subtype) hC.sup_eq_top
    rwa [Subgroup.map_sup, map_subgroupOf_eq_of_le (zpowers_le.mpr hzE), ← MonoidHom.range_eq_map,
      range_subtype] at h1
  refine ⟨C.map E.subtype, map_subtype_le _, hinf, hsup, ?_, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact congrArg Subtype.val
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hE.exponent_dvd_p y)
  · obtain ⟨φ⟩ := SteinbergBK.nonempty_prod_mulEquiv_sup (H := zpowers z) (K := C.map E.subtype)
      (fun x hx y hy => hcommE x (zpowers_le.mpr hzE hx) y (map_subtype_le _ hy)) hinf
    rw [← Nat.card_congr (φ.toEquiv.trans (MulEquiv.subgroupCongr hsup).toEquiv), Nat.card_prod,
      Nat.card_zpowers, hz]

theorem nonempty_mulEquiv_pi_of_sq_eq_one {W : Subgroup G} (hW : ∀ w ∈ W, w ^ 2 = 1) [Finite W]
    {k : ℕ} (hk : Nat.card W = 2 ^ k) : Nonempty (W ≃* (Fin k → Multiplicative (ZMod 2))) := by
  have := Fact.mk Nat.prime_two
  have hel := isElementaryAbelian_of_forall_sq_eq_one hW
  have : Finite (Additive W) := inferInstanceAs (Finite W)
  have : FiniteDimensional (ZMod 2) (Additive W) := Module.Finite.of_finite
  have hfin : Module.finrank (ZMod 2) (Additive W) = k := by
    have h1 := natCard_eq_two_pow_finrank (Additive W)
    rw [Nat.card_congr Additive.toMul, hk] at h1
    exact (Nat.pow_right_injective (le_refl 2) h1).symm
  let e : Additive W ≃ₗ[ZMod 2] (Fin k → ZMod 2) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [hfin, Module.finrank_fin_fun])
  exact ⟨(AddEquiv.toMultiplicativeRight e.toAddEquiv).trans
    (MulEquiv.funMultiplicative (Fin k) (ZMod 2))⟩

theorem nonempty_mulEquiv_cyclic_four_prod {X W : Subgroup G} (hX : IsCyclic X)
    (hX4 : Nat.card X = 4) (hW : ∀ w ∈ W, w ^ 2 = 1) [Finite W] {k : ℕ}
    (hWk : Nat.card W = 2 ^ k) (hcomm : ∀ x ∈ X, ∀ w ∈ W, x * w = w * x) (hXW : X ⊓ W = ⊥) :
    Nonempty (↥(X ⊔ W) ≃* Multiplicative (ZMod 4) × (Fin k → Multiplicative (ZMod 2))) := by
  obtain ⟨φ⟩ := SteinbergBK.nonempty_prod_mulEquiv_sup hcomm hXW
  obtain ⟨β⟩ := nonempty_mulEquiv_pi_of_sq_eq_one hW hWk
  have : IsCyclic X := hX
  have hcard : Nat.card X = Nat.card (Multiplicative (ZMod 4)) := by
    rw [hX4, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  exact ⟨φ.symm.trans (MulEquiv.prodCongr (mulEquivOfCyclicCardEq hcard) β)⟩

theorem sup_zpowers_elementary {P : Subgroup G} {a : G} (ha : orderOf a = 2) (haP : a ∉ P)
    (hPsq : ∀ p ∈ P, p ^ 2 = 1) (hPa : ∀ p ∈ P, p * a = a * p) [Finite P] {n : ℕ}
    (hPn : Nat.card P = 2 ^ n) :
    CFSG.IsElementaryAbelian 2 ↥(P ⊔ zpowers a) ∧ Nat.card ↥(P ⊔ zpowers a) = 2 ^ (n + 1) := by
  have ha2 : a ^ 2 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have hc : ∀ p ∈ P, ∀ y ∈ zpowers a, p * y = y * p := by
    intro p hp y hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_right (hPa p hp) k).eq
  have hinf : P ⊓ zpowers a = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxP, hxa⟩ := mem_inf.mp hx
    rcases eq_one_or_eq_of_mem_zpowers ha hxa with rfl | rfl
    · exact one_mem _
    · exact absurd hxP haP
  refine ⟨isElementaryAbelian_of_forall_sq_eq_one fun x hx => ?_, ?_⟩
  · obtain ⟨p, hp, y, hy, rfl⟩ := (mem_sup_of_commute hc).mp hx
    have hy2 : y ^ 2 = 1 := by
      rcases eq_one_or_eq_of_mem_zpowers ha hy with rfl | rfl
      · exact one_pow 2
      · exact ha2
    rw [(Commute.mul_pow (hc p hp y hy) 2), hPsq p hp, hy2, one_mul]
  · obtain ⟨φ⟩ := SteinbergBK.nonempty_prod_mulEquiv_sup hc hinf
    rw [← Nat.card_congr φ.toEquiv, Nat.card_prod, hPn, Nat.card_zpowers, ha, pow_succ]

theorem not_mem_core_centralizer {M Q : Subgroup G} (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M)
    {z a h : G} (hMC : M = centralizer ({z} : Set G)) (hh : h⁻¹ * z * h = a) (haz : a ≠ z)
    (hwc : {w | ∃ g : G, g⁻¹ * z * g = w} ∩ (Q : Set G) = {z}) :
    z ∉ CFSG.inSubgroup (CFSG.pCore 2) (centralizer ({a} : Set G)) := by
  intro hz
  obtain ⟨-, -, hcore⟩ := centralizer_conj_package hQ hMC hh
  rw [hcore] at hz
  obtain ⟨q, hq, hqz⟩ := hz
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hqz
  have hqG : q ∈ {w | ∃ g : G, g⁻¹ * z * g = w} ∩ (Q : Set G) :=
    ⟨⟨h⁻¹, by rw [← hqz]; group⟩, hq⟩
  rw [hwc, Set.mem_singleton_iff] at hqG
  rw [hqG] at hqz
  exact haz (hh.symm.trans hqz)

theorem exists_transfer_conjugate [Finite G] {S S₀ : Subgroup G} {z a : G}
    (hG : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) (hSG : IsSylowOf 2 S ⊤) (hS₀S : S₀ ≤ S)
    (hidx : S₀.relIndex S = 2) (hwcS₀ : {w | ∃ g : G, g⁻¹ * z * g = w} ∩ (S₀ : Set G) = {z})
    (haG : ∃ g : G, g⁻¹ * z * g = a) (haS : a ∈ S) (haS₀ : a ∉ S₀) (ha : orderOf a = 2) :
    ∃ g : G, g⁻¹ * a * g = z ∧ CFSG.conjugate (S ⊓ centralizer ({a} : Set G)) g ≤ S := by
  have := Fact.mk Nat.prime_two
  obtain ⟨-, hS2, hSidx⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hSG
  rw [relIndex_top_right] at hSidx
  have hnorm : (S₀.subgroupOf S).Normal := Subgroup.normal_of_index_eq_two hidx
  have hcyc : IsCyclic (S ⧸ S₀.subgroupOf S) := isCyclic_of_prime_card (p := 2) hidx
  obtain ⟨g, hg1, hg2⟩ := cyclic_two_quotient_transfer_centralizer_preserving_fusion hG
    (hS2.toSylow hSidx) (N := S₀) hS₀S (hN := hnorm) hcyc haS haS₀ ha
  refine ⟨g, ?_, hg2⟩
  obtain ⟨h, rfl⟩ := haG
  have h1 : g⁻¹ * (h⁻¹ * z * h) * g ∈ {w | ∃ g : G, g⁻¹ * z * g = w} ∩ (S₀ : Set G) :=
    ⟨⟨h * g, by group⟩, hg1⟩
  rw [hwcS₀] at h1
  exact h1

theorem centralizer_transfer_package [Finite G] {S S₀ : Subgroup G} {z a g : G}
    (hS₀S : S₀ ≤ S) (hidx : S₀.relIndex S = 2)
    (hwcS₀ : {w | ∃ g : G, g⁻¹ * z * g = w} ∩ (S₀ : Set G) = {z}) (hzS₀ : z ∈ S₀)
    (hzS : ∀ s ∈ S, s * z = z * s) (hz : orderOf z = 2) (haS : a ∈ S) (haz : a ≠ z)
    (hga : g⁻¹ * a * g = z) (hgS : CFSG.conjugate (S ⊓ centralizer ({a} : Set G)) g ≤ S)
    {R : Subgroup G} (hR : R = S ⊓ centralizer ({a} : Set G) ⊓ CFSG.conjugate S₀ g⁻¹) :
    R.relIndex (S ⊓ centralizer ({a} : Set G)) = 2 ∧ a ∈ R ∧ z ∉ R ∧
      zpowers z ⊔ R = S ⊓ centralizer ({a} : Set G) ∧ zpowers z ⊓ R = ⊥ ∧
      (∀ x ∈ zpowers z, ∀ y ∈ R, x * y = y * x) ∧
      Nonempty (↥(zpowers z) × ↥R ≃* ↥(S ⊓ centralizer ({a} : Set G))) := by
  have hmemR : ∀ x, x ∈ R ↔ x ∈ S ⊓ centralizer ({a} : Set G) ∧ g⁻¹ * x * g ∈ S₀ := by
    intro x
    rw [hR, mem_inf, mem_conjugate_iff_conj_mem, inv_inv]
  have hzC : z ∈ S ⊓ centralizer ({a} : Set G) := by
    refine mem_inf.mpr ⟨hS₀S hzS₀, ?_⟩
    rw [mem_centralizer_singleton_iff]
    exact (hzS a haS).symm
  have hzR : z ∉ R := by
    intro hzR'
    have h2 : g⁻¹ * z * g ∈ {w | ∃ g : G, g⁻¹ * z * g = w} ∩ (S₀ : Set G) :=
      ⟨⟨g, rfl⟩, ((hmemR z).mp hzR').2⟩
    rw [hwcS₀] at h2
    have h3 : g⁻¹ * a * g = g⁻¹ * z * g := hga.trans h2.symm
    apply haz
    calc a = g * (g⁻¹ * a * g) * g⁻¹ := by group
      _ = g * (g⁻¹ * z * g) * g⁻¹ := by rw [h3]
      _ = z := by group
  have haR : a ∈ R := by
    rw [hmemR]
    refine ⟨mem_inf.mpr ⟨haS, mem_centralizer_singleton_iff.mpr rfl⟩, ?_⟩
    rw [hga]
    exact hzS₀
  have hRle : R ≤ S ⊓ centralizer ({a} : Set G) := fun x hx => ((hmemR x).mp hx).1
  have hconjS : ∀ x ∈ S ⊓ centralizer ({a} : Set G), g⁻¹ * x * g ∈ S := fun x hx =>
    hgS (inv_mul_mul_mem_conjugate hx)
  have hidxR : R.relIndex (S ⊓ centralizer ({a} : Set G)) = 2 := by
    rw [relIndex_eq_two_iff_exists_notMem_and]
    refine ⟨z, hzC, hzR, fun y hy => ?_⟩
    by_cases hy₀ : g⁻¹ * y * g ∈ S₀
    · exact Or.inr ((hmemR y).mpr ⟨hy, hy₀⟩)
    · left
      refine (hmemR _).mpr ⟨mul_mem hy hzC, ?_⟩
      have hz₀ : g⁻¹ * z * g ∉ S₀ := fun h => hzR ((hmemR z).mpr ⟨hzC, h⟩)
      have h1 := Subgroup.mul_mem_iff_of_index_two (H := S₀.subgroupOf S) hidx
        (a := ⟨_, hconjS y hy⟩) (b := ⟨_, hconjS z hzC⟩)
      rw [mem_subgroupOf, mem_subgroupOf, mem_subgroupOf] at h1
      have h2 : g⁻¹ * (y * z) * g = (g⁻¹ * y * g) * (g⁻¹ * z * g) := by group
      rw [h2]
      exact h1.mpr (iff_of_false hy₀ hz₀)
  have hcomm : ∀ x ∈ zpowers z, ∀ y ∈ R, x * y = y * x := by
    intro x hx y hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
    exact (Commute.zpow_left (hzS y (mem_inf.mp (hRle hy)).1).symm k).eq
  have hinf : zpowers z ⊓ R = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxz, hxR⟩ := mem_inf.mp hx
    rcases eq_one_or_eq_of_mem_zpowers hz hxz with rfl | rfl
    · exact one_mem _
    · exact absurd hxR hzR
  obtain ⟨φ⟩ := SteinbergBK.nonempty_prod_mulEquiv_sup hcomm hinf
  have hsup : zpowers z ⊔ R = S ⊓ centralizer ({a} : Set G) := by
    apply eq_of_le_of_card_ge (sup_le (zpowers_le.mpr hzC) hRle)
    have h1 : Nat.card ↥(zpowers z ⊔ R) = 2 * Nat.card R := by
      rw [← Nat.card_congr φ.toEquiv, Nat.card_prod, Nat.card_zpowers, hz]
    have h2 := Subgroup.card_mul_index (R.subgroupOf (S ⊓ centralizer ({a} : Set G)))
    rw [show (R.subgroupOf (S ⊓ centralizer ({a} : Set G))).index = 2 from hidxR,
      Nat.card_congr (subgroupOfEquivOfLe hRle).toEquiv] at h2
    rw [h1, ← h2, mul_comm]
  exact ⟨hidxR, haR, hzR, hsup, hinf, hcomm, ⟨φ.trans (MulEquiv.subgroupCongr hsup)⟩⟩

theorem sup_center_fixed_mulEquiv [Finite G] {Q Z P : Subgroup G} {z : G}
    (hz : orderOf z = 2) (hZcyc : IsCyclic Z) (hZ4 : Nat.card Z = 4)
    (hZQ : ∀ w ∈ Z, ∀ x ∈ Q, w * x = x * w) (hPQ : P ≤ Q) (hPsq : ∀ p ∈ P, p ^ 2 = 1)
    (hPZ : P ⊓ Z = zpowers z) {v : ℕ} (hPcard : Nat.card P = 2 ^ (v + 1)) :
    Nonempty (↥(Z ⊔ P) ≃* Multiplicative (ZMod 4) × (Fin v → Multiplicative (ZMod 2))) := by
  have := isElementaryAbelian_of_forall_sq_eq_one hPsq
  have hzPZ : z ∈ P ⊓ Z := by rw [hPZ]; exact mem_zpowers z
  obtain ⟨W, hWP, hWinf, hWsup, hWsq, hWcard⟩ := exists_compl_zpowers hz (mem_inf.mp hzPZ).1
  have hWv : Nat.card W = 2 ^ v := by
    rw [hPcard, pow_succ, mul_comm] at hWcard
    exact (Nat.eq_of_mul_eq_mul_left (by norm_num) hWcard).symm
  have hZW : Z ⊓ W = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxZ, hxW⟩ := mem_inf.mp hx
    have hxz : x ∈ zpowers z := by rw [← hPZ]; exact mem_inf.mpr ⟨hWP hxW, hxZ⟩
    rw [← hWinf]
    exact mem_inf.mpr ⟨hxz, hxW⟩
  have hsup : Z ⊔ W = Z ⊔ P := by
    rw [← hWsup, ← sup_assoc, sup_eq_left.mpr (zpowers_le.mpr (mem_inf.mp hzPZ).2)]
  obtain ⟨φ⟩ := nonempty_mulEquiv_cyclic_four_prod hZcyc hZ4 hWsq hWv
    (fun x hx w hw => hZQ x hx w (hPQ (hWP hw))) hZW
  exact ⟨(MulEquiv.subgroupCongr hsup).symm.trans φ⟩

theorem commutator_alternatives [Finite G] {Z P D : Subgroup G} {z : G} (hz : orderOf z = 2)
    (hzD : z ∈ D) (hzP : z ∈ P) (hDZP : D ≤ Z ⊔ P)
    (hDcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x)
    (hΩ : ∀ x ∈ Z ⊔ P, x ^ 2 = 1 → x ∈ P) (hsqD : ∀ d ∈ D, d ^ 2 ∈ zpowers z)
    (hPsq : ∀ p ∈ P, p ^ 2 = 1) {v : ℕ} (hv : 1 ≤ v) (hDcard : Nat.card D = 2 ^ (v + 1))
    (hPcard : Nat.card P = 2 ^ (v + 1)) :
    Xor (D = P ∧ CFSG.IsElementaryAbelian 2 D)
      (Nonempty (D ≃* Multiplicative (ZMod 4) × (Fin (v - 1) → Multiplicative (ZMod 2))) ∧
        Nat.card ↥(D ⊓ P) = 2 ^ v) := by
  have := Fact.mk Nat.prime_two
  have hz2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz
    norm_num at hz
  by_cases hall : ∀ d ∈ D, d ^ 2 = 1
  · have hDP : D ≤ P := fun d hd => hΩ d (hDZP hd) (hall d hd)
    have hDeq : D = P := eq_of_le_of_card_ge hDP (by rw [hDcard, hPcard])
    refine Or.inl ⟨⟨hDeq, isElementaryAbelian_of_forall_sq_eq_one hall⟩, ?_⟩
    rintro ⟨⟨φ⟩, -⟩
    have h1 : (φ.symm (Multiplicative.ofAdd 1, 1)) ^ 2 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hall _ (φ.symm _).2)
    have h3 := congrArg φ h1
    rw [map_pow, MulEquiv.apply_symm_apply, map_one φ] at h3
    have h4 : (Multiplicative.ofAdd (1 : ZMod 4)) ^ 2 = 1 := by
      have := congrArg Prod.fst h3
      simpa using this
    exact absurd h4 (by decide)
  · push Not at hall
    obtain ⟨u, huD, hu2⟩ := hall
    have hu2z : u ^ 2 = z := (eq_one_or_eq_of_mem_zpowers hz (hsqD u huD)).resolve_left hu2
    have huP : u ∉ P := fun h => hu2 (hPsq u h)
    have hidx : (D ⊓ P).relIndex D = 2 := by
      rw [relIndex_eq_two_iff_exists_notMem_and]
      refine ⟨u, huD, fun h => huP (mem_inf.mp h).2, fun d hd => ?_⟩
      rcases eq_one_or_eq_of_mem_zpowers hz (hsqD d hd) with h | h
      · exact Or.inr (mem_inf.mpr ⟨hd, hΩ d (hDZP hd) h⟩)
      · refine Or.inl (mem_inf.mpr ⟨mul_mem hd huD, hΩ _ (hDZP (mul_mem hd huD)) ?_⟩)
        rw [(Commute.mul_pow (hDcomm d hd u huD) 2), h, hu2z, ← sq, hz2]
    have hDPcard : Nat.card ↥(D ⊓ P) = 2 ^ v := by
      have h1 := Subgroup.card_mul_index ((D ⊓ P).subgroupOf D)
      rw [show ((D ⊓ P).subgroupOf D).index = 2 from hidx,
        Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv, hDcard, pow_succ] at h1
      exact Nat.eq_of_mul_eq_mul_right (by norm_num) h1
    have : CFSG.IsElementaryAbelian 2 ↥(D ⊓ P) :=
      isElementaryAbelian_of_forall_sq_eq_one fun x hx => hPsq x (mem_inf.mp hx).2
    obtain ⟨W, hWle, hWinf, hWsup, hWsq, hWcard⟩ :=
      exists_compl_zpowers hz (mem_inf.mpr ⟨hzD, hzP⟩)
    have h2v : 2 ^ v = 2 * 2 ^ (v - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have hWk : Nat.card W = 2 ^ (v - 1) :=
      Nat.eq_of_mul_eq_mul_left (by norm_num) (hWcard.symm.trans (hDPcard.trans h2v))
    have hu4 : orderOf u = 4 :=
      orderOf_eq_prime_pow (p := 2) (n := 1) (by rw [pow_one, hu2z]; exact hz1)
        (by rw [show 2 ^ (1 + 1) = 2 * 2 from rfl, pow_mul, hu2z, hz2])
    have hcyc : IsCyclic (zpowers u) := inferInstance
    have hu4' : Nat.card (zpowers u) = 4 := by rw [Nat.card_zpowers, hu4]
    have hzu : z ∈ zpowers u := by rw [← hu2z]; exact pow_mem (mem_zpowers u) 2
    have hinf : zpowers u ⊓ W = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxu, hxW⟩ := mem_inf.mp hx
      have hx2 := hWsq x hxW
      by_cases hx1 : x = 1
      · rw [hx1]
        exact one_mem _
      · have hxo : orderOf (⟨x, hxu⟩ : zpowers u) = 2 := by
          rw [Subgroup.orderOf_mk]
          exact orderOf_eq_prime hx2 hx1
        have hzo : orderOf (⟨z, hzu⟩ : zpowers u) = 2 := by rw [Subgroup.orderOf_mk]; exact hz
        have hxz : x = z := congrArg Subtype.val (eq_of_orderOf_eq_two_of_isCyclic hxo hzo)
        rw [← hWinf]
        exact mem_inf.mpr ⟨hxz ▸ mem_zpowers z, hxW⟩
    have hcomm : ∀ x ∈ zpowers u, ∀ w ∈ W, x * w = w * x := by
      intro x hx w hw
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
      exact (Commute.zpow_left (hDcomm u huD w (mem_inf.mp (hWle hw)).1) k).eq
    obtain ⟨φ⟩ := nonempty_mulEquiv_cyclic_four_prod hcyc hu4' hWsq hWk hcomm hinf
    obtain ⟨ψ⟩ := SteinbergBK.nonempty_prod_mulEquiv_sup hcomm hinf
    have hsup : zpowers u ⊔ W = D := by
      apply eq_of_le_of_card_ge (sup_le (zpowers_le.mpr huD)
        (hWle.trans inf_le_left))
      rw [← Nat.card_congr ψ.toEquiv, Nat.card_prod, hu4', hWk, hDcard]
      rw [show v + 1 = (v - 1) + 2 by omega, pow_add]
      norm_num [mul_comm]
    refine Or.inr ⟨⟨⟨(MulEquiv.subgroupCongr hsup).symm.trans φ⟩, hDPcard⟩, ?_⟩
    rintro ⟨hDP, -⟩
    exact huP (hDP ▸ huD)

theorem index_ne_two_of_simple [Finite G] (hsimple : IsSimpleGroup G)
    (hnab : ∃ x y : G, x * y ≠ y * x) : ∀ N : Subgroup G, N.Normal → N.index ≠ 2 := by
  intro N hN h2
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal G _ hsimple N hN with rfl | rfl
  · rw [index_bot] at h2
    have := Fact.mk Nat.prime_two
    have : IsCyclic G := isCyclic_of_prime_card h2
    obtain ⟨x, y, hxy⟩ := hnab
    exact hxy (IsCyclic.isMulCommutative.is_comm.comm x y)
  · rw [index_top] at h2
    norm_num at h2

theorem sq_mem_zpowers_of_frattini [Finite G] {Q : Subgroup G} {z : G}
    (hexp : ∀ x ∈ Q, x ^ 4 = 1) (hΦ : (frattini Q).map Q.subtype = zpowers z) :
    ∀ q ∈ Q, q ^ 2 ∈ zpowers z := by
  have := Fact.mk Nat.prime_two
  have hQ2 : IsPGroup 2 Q := fun x =>
    ⟨2, Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hexp x x.2)⟩
  obtain ⟨-, -, hsqΦ, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hQ2
  intro q hq
  have h1 := hsqΦ (⟨q, hq⟩ : Q)
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
  rw [← hΦ]
  exact ⟨_, h1, rfl⟩

theorem exists_sq_eq_of_cyclic_four {Z : Subgroup G} {z : G} (hZcyc : IsCyclic Z)
    (hZ4 : Nat.card Z = 4) (huniq : ∀ y ∈ Z, orderOf y = 2 → y = z) : ∃ c ∈ Z, c ^ 2 = z := by
  obtain ⟨t, htZ, ht⟩ := exists_zpowers_eq_of_isCyclic hZcyc
  have hto : orderOf t = 4 := by rw [← Nat.card_zpowers, ht, hZ4]
  refine ⟨t, htZ, huniq _ (pow_mem htZ 2) ?_⟩
  rw [orderOf_pow' t (by norm_num), hto]
  norm_num

theorem finrank_core_eq [Finite G] {M Q : Subgroup G}
    (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M)
    [CFSG.IsElementaryAbelian 2 (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))]
    (hZcard : Nat.card (center Q) = 4) {v : ℕ} (hQv : Nat.card Q = 2 ^ (2 * v + 2)) :
    Module.finrank (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) = 2 * v := by
  have : Finite (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) :=
    inferInstanceAs (Finite (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
  have e : CFSG.pCore 2 M ≃* Q := by
    subst hQ
    exact (CFSG.pCore 2 M).equivMapOfInjective M.subtype M.subtype_injective
  have h1 := card_eq_card_quotient_mul_card_subgroup (center (CFSG.pCore 2 M))
  rw [Nat.card_congr e.toEquiv, hQv, Nat.card_congr (Subgroup.centerCongr e).toEquiv,
    hZcard] at h1
  have h2 := natCard_eq_two_pow_finrank (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
  rw [Nat.card_congr Additive.toMul] at h2
  rw [h2, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add] at h1
  have := Nat.pow_right_injective (le_refl 2) h1
  omega

theorem weak_closure_root_package
    {G : Type} [Group G] [Finite G] (hsimple : IsSimpleGroup G)
    (hnab : ∃ x y : G, x * y ≠ y * x) (hchar : IsCharacteristicPType G 2)
    (he : 3 ≤ CFSG.twoLocalOddRank G) {M B : Subgroup G} (hM : GLAIsMaxTwoLocal M)
    (hsym : GLASymplecticType (pCoreOf 2 M)) (hB : GLAIsBmax 3 B) (hBM : B ≤ M)
    {Q : Subgroup G} (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M)
    (hnex : ¬ IsExtraspecialPGroup 2 Q) (hexp : ∀ x ∈ Q, x ^ 4 = 1) {z : G}
    (hzZ : z ∈ (center Q).map Q.subtype) (hz : orderOf z = 2)
    (hwc : {w | ∃ g : G, g⁻¹ * z * g = w} ∩ (Q : Set G) = {z}) {S : Subgroup G}
    (hS : IsSylowOf 2 S M) :
    (S ⊓ centralizer ((center Q).map Q.subtype : Set G)).relIndex S = 2 ∧
    Q ≤ S ⊓ centralizer ((center Q).map Q.subtype : Set G) ∧
    (center Q).map Q.subtype ≤
      (center ↥(S ⊓ centralizer ((center Q).map Q.subtype : Set G))).map
        (S ⊓ centralizer ((center Q).map Q.subtype : Set G)).subtype ∧
    {w | ∃ g : G, g⁻¹ * z * g = w} ∩
      ((S ⊓ centralizer ((center Q).map Q.subtype : Set G) : Subgroup G) : Set G) = {z} ∧
    ∀ a ∈ ({w | ∃ g : G, g⁻¹ * z * g = w} ∩ (M : Set G)) \ {z},
      a ∉ M ⊓ centralizer ((center Q).map Q.subtype : Set G) ∧
      ∀ c ∈ (center Q).map Q.subtype, a * c * a⁻¹ = c⁻¹ := by
  obtain ⟨z'', hz''Z, hz''ord, huniq'', _inst, _b, -, -, -, _ι, -, -, hF⟩ :=
    gf2_center_four_all_cyclic_root_images_and_weak_closure_obstruction hchar he hM hsym hB hBM
      hQ hnex hexp _ rfl
  obtain rfl : z = z'' := huniq'' z hzZ hz
  have hF0 : ({w | ∃ g : G, g⁻¹ * z * g = w} ∩ (Q : Set G)) \ {z} = ∅ := by
    rw [hwc, Set.sdiff_self]
  obtain ⟨-, -, -, -, -, -, -, hinv, hsimp⟩ := hF _ hF0.symm
  obtain ⟨hidx, hQS₀, hZS₀, hwcS₀, -⟩ := hsimp rfl hsimple hnab S hS
  exact ⟨hidx, hQS₀, hZS₀, hwcS₀, hinv rfl⟩

theorem fixed_core_sq_eq_one {Q R C : Subgroup G} {z a : G} (hz : orderOf z = 2)
    (hQC : Q ⊓ centralizer ({a} : Set G) ≤ C) (hRC : R.relIndex C = 2) (hzR : z ∉ R)
    (hsq : ∀ q ∈ Q, q ^ 2 ∈ zpowers z) : ∀ p ∈ Q ⊓ centralizer ({a} : Set G), p ^ 2 = 1 := by
  intro p hp
  have h1 := sq_mem_of_relIndex_eq_two hRC (hQC hp)
  rcases eq_one_or_eq_of_mem_zpowers hz (hsq p (mem_inf.mp hp).1) with h | h
  · exact h
  · rw [h] at h1
    exact absurd h1 hzR

@[expose] def s0CommutatorConclusion {G : Type*} [Group G] (Q Z P D : Subgroup G) (z a : G)
    (v : ℕ) : Prop :=
  (∀ x, x ∈ D ↔ ∃ q ∈ Q, x = q⁻¹ * a⁻¹ * q * a) ∧
  IsMulCommutative D ∧ Nat.card D = 2 ^ (v + 1) ∧ D ≤ Q ∧ (D.subgroupOf Q).Normal ∧
  D ≤ Z ⊔ P ∧ D ⊓ Z = zpowers z ∧ (∀ d ∈ D, a * d * a⁻¹ = d⁻¹) ∧
  {w | ∃ q ∈ Q, q⁻¹ * a * q = w} = {w | ∃ d ∈ D, a * d = w} ∧
  Xor (D = P ∧ CFSG.IsElementaryAbelian 2 D)
    (Nonempty (D ≃* Multiplicative (ZMod 4) × (Fin (v - 1) → Multiplicative (ZMod 2))) ∧
      Nat.card ↥(D ⊓ P) = 2 ^ v) ∧
  (∀ d ∈ D, ∃ g : G, g⁻¹ * z * g = a * d) ∧
  {w | ∃ g : G, g⁻¹ * z * g = w} ∩ (D : Set G) = {z}

theorem s0_commutator_aux {G : Type*} [Group G] [Finite G] {M Q : Subgroup G}
    (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M) {z c a : G} (hz : orderOf z = 2)
    (hzZ : z ∈ (center Q).map Q.subtype)
    (huniq : ∀ y ∈ (center Q).map Q.subtype, orderOf y = 2 → y = z)
    (hcZ : c ∈ (center Q).map Q.subtype) (hcz : c ^ 2 = z) (haM : a ∈ M) (ha : orderOf a = 2)
    (hainv : ∀ w ∈ (center Q).map Q.subtype, a * w * a⁻¹ = w⁻¹)
    (hsq : ∀ q ∈ Q, q ^ 2 ∈ zpowers z) (hQ' : ⁅Q, Q⁆ = zpowers z)
    (haG : ∃ h : G, h⁻¹ * z * h = a)
    (hwc : {w | ∃ g : G, g⁻¹ * z * g = w} ∩ (Q : Set G) = {z})
    (hPsq : ∀ p ∈ Q ⊓ centralizer ({a} : Set G), p ^ 2 = 1) {v : ℕ} (hv : 1 ≤ v)
    (hPcard : Nat.card ↥(Q ⊓ centralizer ({a} : Set G)) = 2 ^ (v + 1))
    [CFSG.IsElementaryAbelian 2 (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))]
    {T : Module.End (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))}
    (hT : ∀ x y : CFSG.pCore 2 M, ((y : M) : G) = a * ((x : M) : G) * a⁻¹ →
      T (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) =
        Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
    {L : Submodule (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))}
    (hmem : ∀ x, x ∈ L ↔ ∃ q : CFSG.pCore 2 M, ((q : M) : G) ∈ Q ⊓ centralizer ({a} : Set G) ∧
      x = Additive.ofMul (q : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
    (hLv : Module.finrank (ZMod 2) L = v) (hrange : LinearMap.range (T - 1) = L)
    {D : Subgroup G} (hD : D = ⁅Q, zpowers a⁆) :
    s0CommutatorConclusion Q ((center Q).map Q.subtype) (Q ⊓ centralizer ({a} : Set G)) D z a
      v := by
  have : Finite (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) :=
    inferInstanceAs (Finite (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
  have ha2 : a * a = 1 := by rw [← sq, ← ha]; exact pow_orderOf_eq_one a
  have hainv' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hZQle : (center Q).map Q.subtype ≤ Q := map_subtype_le _
  have hZcomm : ∀ w ∈ (center Q).map Q.subtype, ∀ x ∈ Q, w * x = x * w :=
    fun w hw x hx => center_map_commute hw hx
  have haQ : ∀ q ∈ Q, a * q * a⁻¹ ∈ Q := fun q hq => by
    obtain ⟨q₀, rfl⟩ := exists_core_coe hQ hq
    obtain ⟨y₀, hy₀⟩ := exists_core_conj haM q₀
    rw [← hy₀]
    exact core_coe_mem hQ y₀
  obtain ⟨D', hD'mem, hD'eq, hD'Q, hzD, hDnorm⟩ :=
    commutator_set_package hz hzZ hcZ hcz hZQle hZcomm hainv ha haQ hQ'
  obtain rfl : D = D' := hD.trans hD'eq.symm
  have hPQ : Q ⊓ centralizer ({a} : Set G) ≤ Q := inf_le_left
  have hzP : z ∈ Q ⊓ centralizer ({a} : Set G) := by
    refine mem_inf.mpr ⟨hZQle hzZ, ?_⟩
    rw [mem_centralizer_singleton_iff]
    have h1 : a * z * a⁻¹ = z := by rw [hainv z hzZ, inv_eq_self_of_orderOf_eq_two hz]
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  have hPcomm : ∀ p ∈ Q ⊓ centralizer ({a} : Set G), ∀ p' ∈ Q ⊓ centralizer ({a} : Set G),
      p * p' = p' * p := fun p hp p' hp' =>
    congrArg Subtype.val ((isElementaryAbelian_of_forall_sq_eq_one hPsq).is_comm.comm
      ⟨p, hp⟩ ⟨p', hp'⟩)
  have hDZP : D ≤ (center Q).map Q.subtype ⊔ Q ⊓ centralizer ({a} : Set G) := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := (hD'mem x).mp hx
    exact commutator_mem_sup_fixed hQ haM hT hmem hrange hq
  have hZPcomm := sup_isMulCommutative_of_commute hZQle hPQ hZcomm hPcomm
  have hDcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hZPcomm.is_comm.comm ⟨x, hDZP hx⟩ ⟨y, hDZP hy⟩)
  have hDZ : D ⊓ (center Q).map Q.subtype = zpowers z := by
    apply le_antisymm
    · intro w hw
      obtain ⟨hwD, hwZ⟩ := mem_inf.mp hw
      obtain ⟨q, hq, rfl⟩ := (hD'mem _).mp hwD
      obtain ⟨u, huZ, hu⟩ :=
        exists_fixed_lift hz hzZ huniq hcZ hcz hZcomm hainv (hsq q hq) hq hwZ
      have h1 : a * q * a⁻¹ = (a * (q * u) * a⁻¹) * (a * u⁻¹ * a⁻¹) := by group
      rw [hu, hainv u⁻¹ (inv_mem huZ), inv_inv] at h1
      have h2 : q⁻¹ * (a * q * a⁻¹) = u ^ 2 := by
        rw [h1, sq]
        group
      rw [h2]
      exact hsq u (hZQle huZ)
    · rw [zpowers_le]
      exact mem_inf.mpr ⟨hzD, hzZ⟩
  have hDcard : Nat.card D = 2 ^ (v + 1) := by
    have h1 := card_eq_card_inf_center_mul_card_image hQ hD'Q
    rw [hDZ, Nat.card_zpowers, hz,
      Nat.card_congr (Equiv.subtypeEquivRight (image_commutator_set hQ haM hT hD'mem))] at h1
    have h2 : Nat.card ↥(LinearMap.range (T - 1)) = 2 ^ v := by
      rw [hrange, natCard_eq_two_pow_finrank, hLv]
    rw [h1, show Nat.card {x // x ∈ LinearMap.range (T - 1)} = 2 ^ v from h2, pow_succ,
      mul_comm]
  have hainvD : ∀ d ∈ D, a * d * a⁻¹ = d⁻¹ := by
    intro d hd
    obtain ⟨w, hw, p, hp, rfl⟩ :=
      (mem_sup_of_commute fun w hw p hp => hZcomm w hw p (hPQ hp)).mp (hDZP hd)
    have hpa : a * p * a⁻¹ = p := by
      rw [← mem_centralizer_singleton_iff.mp (mem_inf.mp hp).2, mul_inv_cancel_right]
    have hpinv : p⁻¹ = p := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hPsq p hp)
    calc a * (w * p) * a⁻¹ = (a * w * a⁻¹) * (a * p * a⁻¹) := by group
      _ = w⁻¹ * p := by rw [hainv w hw, hpa]
      _ = (w * p)⁻¹ := by rw [mul_inv_rev, hpinv]; exact hZcomm w⁻¹ (inv_mem hw) p (hPQ hp)
  have horbit := conj_class_eq_mul ha2 haQ hD'mem
  refine ⟨fun x => (hD'mem x).trans ?_, ⟨⟨fun x y => Subtype.ext (hDcomm x x.2 y y.2)⟩⟩,
    hDcard, hD'Q, hDnorm, hDZP, hDZ, hainvD, horbit,
    commutator_alternatives hz hzD hzP hDZP hDcomm
      (fun x hx hx2 => mem_of_mem_sup_of_sq_eq_one huniq hzP hPQ hZcomm hPsq hx hx2)
      (fun d hd => hsq d (hD'Q hd)) hPsq hv hDcard hPcard, fun d hd => ?_, ?_⟩
  · refine exists_congr fun q => and_congr_right fun _ => ?_
    rw [show q⁻¹ * a⁻¹ * q * a = q⁻¹ * (a * q * a⁻¹) by rw [hainv']; group]
  · have h1 : a * d ∈ {w | ∃ d ∈ D, a * d = w} := ⟨d, hd, rfl⟩
    rw [← horbit] at h1
    obtain ⟨q, -, hq⟩ := h1
    obtain ⟨h, rfl⟩ := haG
    exact ⟨h * q, by rw [← hq]; group⟩
  · ext w
    constructor
    · rintro ⟨hwG, hwD⟩
      have h1 : w ∈ {w | ∃ g : G, g⁻¹ * z * g = w} ∩ (Q : Set G) := ⟨hwG, hD'Q hwD⟩
      rwa [hwc] at h1
    · rintro rfl
      exact ⟨⟨1, by group⟩, hzD⟩

@[expose] def s0FixedConclusion {G : Type*} [Group G] (M Q Z P : Subgroup G) (z a : G)
    [CFSG.IsElementaryAbelian 2 (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))]
    (b : LinearMap.BilinForm (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))))
    (v : ℕ) : Prop :=
  CFSG.IsElementaryAbelian 2 P ∧ Nat.card P = 2 ^ (v + 1) ∧
  (∃ L : Submodule (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))),
    (∀ x, x ∈ L ↔ ∃ q : CFSG.pCore 2 M, ((q : M) : G) ∈ P ∧
      x = Additive.ofMul (q : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) ∧
    (∀ x ∈ L, ∀ y ∈ L, b x y = 0) ∧ Module.finrank (ZMod 2) L = v ∧ b.orthogonal L = L ∧
    ∀ T : Module.End (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))),
      (∀ x y : CFSG.pCore 2 M, ((y : M) : G) = a * ((x : M) : G) * a⁻¹ →
        T (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) =
          Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) →
      LinearMap.range (T - 1) = L ∧ LinearMap.ker (T - 1) = L ∧
        Module.finrank (ZMod 2) (LinearMap.range (T - 1)) = v) ∧
  CFSG.IsElementaryAbelian 2 ↥(P ⊔ zpowers a) ∧ Nat.card ↥(P ⊔ zpowers a) = 2 ^ (v + 2) ∧
  Q ⊓ centralizer (P : Set G) = Z ⊔ P ∧
  Nonempty (↥(Z ⊔ P) ≃* Multiplicative (ZMod 4) × (Fin v → Multiplicative (ZMod 2))) ∧
  ∀ D : Subgroup G, D = ⁅Q, zpowers a⁆ → s0CommutatorConclusion Q Z P D z a v

theorem s0_fixed_aux [Finite G] {M Q : Subgroup G} (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M)
    {z c a : G} (hz : orderOf z = 2) (hzZ : z ∈ (center Q).map Q.subtype)
    (huniq : ∀ y ∈ (center Q).map Q.subtype, orderOf y = 2 → y = z)
    (hcZ : c ∈ (center Q).map Q.subtype) (hcz : c ^ 2 = z)
    (hZcyc : IsCyclic ↥((center Q).map Q.subtype))
    (hZ4 : Nat.card ↥((center Q).map Q.subtype) = 4) (haM : a ∈ M) (ha : orderOf a = 2)
    (haQ : a ∉ Q) (hainv : ∀ w ∈ (center Q).map Q.subtype, a * w * a⁻¹ = w⁻¹)
    (hsq : ∀ q ∈ Q, q ^ 2 ∈ zpowers z) (hQ' : ⁅Q, Q⁆ = zpowers z)
    (haG : ∃ h : G, h⁻¹ * z * h = a)
    (hwc : {w | ∃ g : G, g⁻¹ * z * g = w} ∩ (Q : Set G) = {z})
    (hPsq : ∀ p ∈ Q ⊓ centralizer ({a} : Set G), p ^ 2 = 1)
    [CFSG.IsElementaryAbelian 2 (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))]
    {b : LinearMap.BilinForm (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))}
    (hrule : ∀ x y : CFSG.pCore 2 M, (((⁅x, y⁆ : CFSG.pCore 2 M) : M) : G) =
      z ^ (b (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
        (Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))).val)
    (hnd : b.Nondegenerate) {v : ℕ} (hv : 1 ≤ v)
    (hdim : Module.finrank (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) =
      2 * v)
    {T₀ : Module.End (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))}
    (hT₀ : ∀ x y : CFSG.pCore 2 M, ((y : M) : G) = a * ((x : M) : G) * a⁻¹ →
      T₀ (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) =
        Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
    {P : Subgroup G} (hP : P = Q ⊓ centralizer ({a} : Set G)) :
    s0FixedConclusion M Q ((center Q).map Q.subtype) P z a b v := by
  subst hP
  have ha2 : a * a = 1 := by rw [← sq, ← ha]; exact pow_orderOf_eq_one a
  have hPcomm : ∀ p ∈ Q ⊓ centralizer ({a} : Set G), ∀ p' ∈ Q ⊓ centralizer ({a} : Set G),
      p * p' = p' * p := fun p hp p' hp' =>
    congrArg Subtype.val ((isElementaryAbelian_of_forall_sq_eq_one hPsq).is_comm.comm
      ⟨p, hp⟩ ⟨p', hp'⟩)
  obtain ⟨L, hmem, hiso, hLv, horth, hrange, hker⟩ :=
    core_fixed_lagrangian hQ hz hzZ huniq hcZ hcz haM ha2 hainv hsq hPcomm hrule hnd hdim hT₀
  obtain ⟨hPZ, hPcard⟩ := card_fixed_core hQ hz hzZ huniq hainv hmem hLv
  have haP : a ∉ Q ⊓ centralizer ({a} : Set G) := fun h => haQ (mem_inf.mp h).1
  have hPa : ∀ p ∈ Q ⊓ centralizer ({a} : Set G), p * a = a * p := fun p hp =>
    mem_centralizer_singleton_iff.mp (mem_inf.mp hp).2
  obtain ⟨hEel, hEcard⟩ := sup_zpowers_elementary ha haP hPsq hPa hPcard
  unfold s0FixedConclusion
  refine ⟨isElementaryAbelian_of_forall_sq_eq_one hPsq, hPcard,
    ⟨L, hmem, hiso, hLv, horth, fun T hT => ?_⟩, hEel, hEcard,
    centralizer_fixed_core_eq hQ hz hPcomm hrule hmem horth,
    sup_center_fixed_mulEquiv hz hZcyc hZ4 (fun w hw x hx => center_map_commute hw hx)
      inf_le_left hPsq hPZ hPcard,
    fun D hD => s0_commutator_aux hQ hz hzZ huniq hcZ hcz haM ha hainv hsq hQ' haG hwc hPsq hv
      hPcard hT₀ hmem hLv hrange hD⟩
  obtain rfl : T = T₀ := action_unique haM hT hT₀
  exact ⟨hrange, hker, by rw [hrange, hLv]⟩

@[expose] def s0RootConclusion {G : Type*} [Group G] (M Q Z S S₀ : Subgroup G) (z a : G)
    [CFSG.IsElementaryAbelian 2 (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))]
    (b : LinearMap.BilinForm (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))))
    (v : ℕ) : Prop :=
  a ∈ S ∧ a ∉ S₀ ∧ (∀ c ∈ Z, a * c * a⁻¹ = c⁻¹) ∧
  z ∉ CFSG.inSubgroup (CFSG.pCore 2) (centralizer ({a} : Set G)) ∧
  (∃ g : G, g⁻¹ * a * g = z ∧ CFSG.conjugate (S ⊓ centralizer ({a} : Set G)) g ≤ S) ∧
  (∀ g : G, g⁻¹ * a * g = z → CFSG.conjugate (S ⊓ centralizer ({a} : Set G)) g ≤ S →
    ∀ R : Subgroup G, R = S ⊓ centralizer ({a} : Set G) ⊓ CFSG.conjugate S₀ g⁻¹ →
      R.relIndex (S ⊓ centralizer ({a} : Set G)) = 2 ∧ a ∈ R ∧ z ∉ R ∧
      zpowers z ⊔ R = S ⊓ centralizer ({a} : Set G) ∧ zpowers z ⊓ R = ⊥ ∧
      (∀ x ∈ zpowers z, ∀ y ∈ R, x * y = y * x) ∧
      Nonempty (↥(zpowers z) × ↥R ≃* ↥(S ⊓ centralizer ({a} : Set G)))) ∧
  ∀ P : Subgroup G, P = Q ⊓ centralizer ({a} : Set G) → s0FixedConclusion M Q Z P z a b v

theorem s0_root_aux [Finite G] {M Q S S₀ : Subgroup G}
    (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M) {z c : G} (hz : orderOf z = 2)
    (hzZ : z ∈ (center Q).map Q.subtype)
    (huniq : ∀ y ∈ (center Q).map Q.subtype, orderOf y = 2 → y = z)
    (hcZ : c ∈ (center Q).map Q.subtype) (hcz : c ^ 2 = z)
    (hZcyc : IsCyclic ↥((center Q).map Q.subtype))
    (hZ4 : Nat.card ↥((center Q).map Q.subtype) = 4)
    (hsq : ∀ q ∈ Q, q ^ 2 ∈ zpowers z) (hQ' : ⁅Q, Q⁆ = zpowers z)
    (hwc : {w | ∃ g : G, g⁻¹ * z * g = w} ∩ (Q : Set G) = {z})
    (hMC : M = centralizer ({z} : Set G)) (hG : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
    (hSG : IsSylowOf 2 S ⊤) (hSM : S ≤ M)
    (hS₀ : S₀ = S ⊓ centralizer (((center Q).map Q.subtype : Subgroup G) : Set G))
    (hidx : S₀.relIndex S = 2) (hQS₀ : Q ≤ S₀)
    (hwcS₀ : {w | ∃ g : G, g⁻¹ * z * g = w} ∩ (S₀ : Set G) = {z})
    (hroot : ∀ a ∈ ({w | ∃ g : G, g⁻¹ * z * g = w} ∩ (M : Set G)) \ {z},
      a ∉ M ⊓ centralizer (((center Q).map Q.subtype : Subgroup G) : Set G) ∧
      ∀ c ∈ (center Q).map Q.subtype, a * c * a⁻¹ = c⁻¹)
    [CFSG.IsElementaryAbelian 2 (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))]
    {b : LinearMap.BilinForm (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))}
    (hrule : ∀ x y : CFSG.pCore 2 M, (((⁅x, y⁆ : CFSG.pCore 2 M) : M) : G) =
      z ^ (b (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
        (Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))).val)
    (hnd : b.Nondegenerate) {v : ℕ} (hv : 1 ≤ v)
    (hdim : Module.finrank (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) =
      2 * v)
    {ι : M ⧸ CFSG.pCore 2 M →* bilinIsometryGroup b}
    (hιconj : ∀ (h : M) (x y : CFSG.pCore 2 M), (y : M) = h * x * h⁻¹ →
      (((ι (h : M ⧸ CFSG.pCore 2 M) : bilinIsometryGroup b) :
          LinearMap.GeneralLinearGroup (ZMod 2)
            (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) :
        Module.End (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))))
          (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) =
        Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
    {a : G} (ha : a ∈ ({w | ∃ g : G, g⁻¹ * z * g = w} ∩ (S : Set G)) \ {z}) :
    s0RootConclusion M Q ((center Q).map Q.subtype) S S₀ z a b v := by
  obtain ⟨⟨⟨h, hh⟩, haS⟩, haz⟩ := ha
  have haz' : a ≠ z := haz
  have haM : a ∈ M := hSM haS
  have haord : orderOf a = 2 := by
    have h1 := MulEquiv.orderOf_eq (MulAut.conj h⁻¹) z
    rw [MulAut.conj_apply, inv_inv, hh] at h1
    rw [h1, hz]
  obtain ⟨haMZ, hainv⟩ := hroot a ⟨⟨⟨h, hh⟩, haM⟩, haz⟩
  have hS₀S : S₀ ≤ S := hS₀ ▸ inf_le_left
  have haS₀ : a ∉ S₀ := fun h' => haMZ (mem_inf.mpr ⟨haM, (mem_inf.mp (hS₀ ▸ h')).2⟩)
  have haQ : a ∉ Q := fun h' => haS₀ (hQS₀ h')
  have hzS : ∀ s ∈ S, s * z = z * s := fun s hs => by
    have h1 := hSM hs
    rw [hMC, mem_centralizer_singleton_iff] at h1
    exact h1
  have hzS₀ : z ∈ S₀ := hQS₀ (map_subtype_le _ hzZ)
  obtain ⟨g₀, hg₀a, hg₀S⟩ :=
    exists_transfer_conjugate hG hSG hS₀S hidx hwcS₀ ⟨h, hh⟩ haS haS₀ haord
  obtain ⟨hR2, -, hzR, -⟩ :=
    centralizer_transfer_package hS₀S hidx hwcS₀ hzS₀ hzS hz haS haz' hg₀a hg₀S rfl
  have hPsq := fixed_core_sq_eq_one hz (inf_le_inf_right _ (hQS₀.trans hS₀S)) hR2 hzR hsq
  have hT₀ : ∀ x y : CFSG.pCore 2 M, ((y : M) : G) = a * ((x : M) : G) * a⁻¹ →
      (((ι ((⟨a, haM⟩ : M) : M ⧸ CFSG.pCore 2 M) : bilinIsometryGroup b) :
          LinearMap.GeneralLinearGroup (ZMod 2)
            (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) :
        Module.End (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))))
          (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) =
        Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)) :=
    fun x y hy => hιconj ⟨a, haM⟩ x y (Subtype.ext hy)
  unfold s0RootConclusion
  exact ⟨haS, haS₀, hainv, not_mem_core_centralizer hQ hMC hh haz' hwc, ⟨g₀, hg₀a, hg₀S⟩,
    fun g hga hgS R hR =>
      centralizer_transfer_package hS₀S hidx hwcS₀ hzS₀ hzS hz haS haz' hga hgS hR,
    fun P hP => s0_fixed_aux hQ hz hzZ huniq hcZ hcz hZcyc hZ4 haM haord haQ hainv hsq hQ'
      ⟨h, hh⟩ hwc hPsq hrule hnd hv hdim hT₀ hP⟩

theorem s0_fusion_aux
    {G : Type} [Group G] [Finite G] (hsimple : IsSimpleGroup G)
    (hnab : ∃ x y : G, x * y ≠ y * x) (hchar : IsCharacteristicPType G 2)
    (he : 4 ≤ CFSG.twoLocalOddRank G) {M B : Subgroup G} (hM : GLAIsMaxTwoLocal M)
    (hsym : GLASymplecticType (pCoreOf 2 M)) (hB : GLAIsBmax 3 B) (hBM : B ≤ M)
    {Q : Subgroup G} (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M)
    (hnex : ¬ IsExtraspecialPGroup 2 Q) (hexp : ∀ x ∈ Q, x ^ 4 = 1) {Z : Subgroup G}
    (hZ : Z = (center Q).map Q.subtype) {z : G} (hzZ : z ∈ Z) (hz : orderOf z = 2)
    (hwc : {w | ∃ g : G, g⁻¹ * z * g = w} ∩ (Q : Set G) = {z}) {S : Subgroup G}
    (hS : IsSylowOf 2 S M) {S₀ : Subgroup G} (hS₀ : S₀ = S ⊓ centralizer (Z : Set G)) :
    ∃ (_ : CFSG.IsElementaryAbelian 2 (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))),
    ∃ b : LinearMap.BilinForm (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))),
      (∀ x y : CFSG.pCore 2 M, (((⁅x, y⁆ : CFSG.pCore 2 M) : M) : G) =
        z ^ (b (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
          (Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))).val) ∧
      (∀ b' : LinearMap.BilinForm (ZMod 2)
          (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))),
        (∀ x y : CFSG.pCore 2 M, (((⁅x, y⁆ : CFSG.pCore 2 M) : M) : G) =
          z ^ (b' (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
            (Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))).val) → b' = b) ∧
      b.IsAlt ∧ b.Nondegenerate ∧
      (∃ ι : M ⧸ CFSG.pCore 2 M →* bilinIsometryGroup b, Function.Injective ι ∧
        ∀ (h : M) (x y : CFSG.pCore 2 M), (y : M) = h * x * h⁻¹ →
          (((ι (h : M ⧸ CFSG.pCore 2 M) : bilinIsometryGroup b) :
              LinearMap.GeneralLinearGroup (ZMod 2)
                (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) :
            Module.End (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))))
              (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) =
            Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) ∧
      ∃ v : ℕ,
        Module.finrank (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) = 2 * v ∧
        4 ≤ v ∧ IsSylowOf 2 S ⊤ ∧ S₀.relIndex S = 2 ∧ Q ≤ S₀ ∧
        Z ≤ (center S₀).map S₀.subtype ∧
        {w | ∃ g : G, g⁻¹ * z * g = w} ∩ (S₀ : Set G) = {z} ∧
        ∀ a ∈ ({w | ∃ g : G, g⁻¹ * z * g = w} ∩ (S : Set G)) \ {z},
          s0RootConclusion M Q Z S S₀ z a b v := by
  have he3 : 3 ≤ CFSG.twoLocalOddRank G := le_trans (by norm_num) he
  subst hZ
  obtain ⟨hZcyc, hZcard, z', hz'Z, -, huniq, hQ', hΦ,
      ⟨hVel₀, -, b, hrule, huniqb, halt, hnd, ρ, hρ, -, -, ⟨ι, hιinj, hιρ⟩, -⟩, hMC, hSyl, -⟩ :=
    gf2_center_four_symplectic_embedding_and_fusion hchar he3 hM hsym hB hBM hQ hnex hexp
  obtain rfl : z = z' := huniq z hzZ hz
  obtain ⟨-, -, -, -, -, -, v, hv4, hQv, -, -, -⟩ :=
    gf2_center_four_width_at_least_four_at_rank_four hchar he hM hsym hB hBM hQ hnex hexp rfl
  obtain ⟨hidx, hQS₀, hZS₀, hwcS₀, hroot⟩ :=
    weak_closure_root_package hsimple hnab hchar he3 hM hsym hB hBM hQ hnex hexp hzZ hz hwc hS
  rw [← hS₀] at hidx hQS₀ hZS₀ hwcS₀
  have hZcyc' : IsCyclic ↥((center Q).map Q.subtype) :=
    isCyclic_of_surjective ((center Q).equivMapOfInjective _ Q.subtype_injective).toMonoidHom
      (MulEquiv.surjective _)
  have hZ4 : Nat.card ↥((center Q).map Q.subtype) = 4 := by
    rw [card_map_of_injective Q.subtype_injective, hZcard]
  obtain ⟨c, hcZ, hcz⟩ := exists_sq_eq_of_cyclic_four hZcyc' hZ4 huniq
  have hdim := finrank_core_eq hQ hZcard hQv
  exact ⟨hVel₀, b, hrule, huniqb, halt, hnd, ⟨ι, hιinj, iota_conj_formula hρ hιρ⟩, v, hdim, hv4,
    hSyl S hS, hidx, hQS₀, hZS₀, hwcS₀, fun a ha => s0_root_aux hQ hz hzZ huniq hcZ hcz hZcyc'
      hZ4 (sq_mem_zpowers_of_frattini hexp hΦ) hQ' hwc hMC (index_ne_two_of_simple hsimple hnab)
      (hSyl S hS) hS.le hS₀ hidx hQS₀ hwcS₀ hroot hrule hnd (by omega) hdim
      (iota_conj_formula hρ hιρ) ha⟩

end SteinbergCH

open SteinbergCH

theorem gf2_center_four_S0_fusion_transfer_maximal_rank_images
    {G : Type} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G) (hnab : ∃ x y : G, x * y ≠ y * x)
    (hchar : IsCharacteristicPType G 2) (he : 4 ≤ CFSG.twoLocalOddRank G) {M B : Subgroup G}
    (hM : GLAIsMaxTwoLocal M) (hsym : GLASymplecticType (pCoreOf 2 M)) (hB : GLAIsBmax 3 B)
    (hBM : B ≤ M) {Q : Subgroup G} (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M)
    (hnex : ¬ IsExtraspecialPGroup 2 Q) (hexp : ∀ x ∈ Q, x ^ 4 = 1) {Z : Subgroup G}
    (hZ : Z = (center Q).map Q.subtype) {z : G} (hzZ : z ∈ Z) (hz : orderOf z = 2)
    (hwc : {w | ∃ g : G, g⁻¹ * z * g = w} ∩ (Q : Set G) = {z}) {S : Subgroup G}
    (hS : IsSylowOf 2 S M) {S₀ : Subgroup G} (hS₀ : S₀ = S ⊓ centralizer (Z : Set G)) :
    ∃ (_ : CFSG.IsElementaryAbelian 2 (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))),
    ∃ b : LinearMap.BilinForm (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))),
      (∀ x y : CFSG.pCore 2 M, (((⁅x, y⁆ : CFSG.pCore 2 M) : M) : G) =
        z ^ (b (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
          (Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))).val) ∧
      (∀ b' : LinearMap.BilinForm (ZMod 2)
          (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))),
        (∀ x y : CFSG.pCore 2 M, (((⁅x, y⁆ : CFSG.pCore 2 M) : M) : G) =
          z ^ (b' (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
            (Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))).val) → b' = b) ∧
      b.IsAlt ∧ b.Nondegenerate ∧
      (∃ ι : M ⧸ CFSG.pCore 2 M →* bilinIsometryGroup b, Function.Injective ι ∧
        ∀ (h : M) (x y : CFSG.pCore 2 M), (y : M) = h * x * h⁻¹ →
          (((ι (h : M ⧸ CFSG.pCore 2 M) : bilinIsometryGroup b) :
              LinearMap.GeneralLinearGroup (ZMod 2)
                (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) :
            Module.End (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))))
              (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) =
            Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) ∧
      ∃ v : ℕ,
        Module.finrank (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) =
          2 * v ∧
        4 ≤ v ∧ IsSylowOf 2 S ⊤ ∧ S₀.relIndex S = 2 ∧ Q ≤ S₀ ∧
        Z ≤ (center S₀).map S₀.subtype ∧
        {w | ∃ g : G, g⁻¹ * z * g = w} ∩ (S₀ : Set G) = {z} ∧
        ∀ a ∈ ({w | ∃ g : G, g⁻¹ * z * g = w} ∩ (S : Set G)) \ {z},
          a ∈ S ∧ a ∉ S₀ ∧ (∀ c ∈ Z, a * c * a⁻¹ = c⁻¹) ∧
          z ∉ CFSG.inSubgroup (CFSG.pCore 2) (centralizer ({a} : Set G)) ∧
          (∃ g : G, g⁻¹ * a * g = z ∧ CFSG.conjugate (S ⊓ centralizer ({a} : Set G)) g ≤ S) ∧
          (∀ g : G, g⁻¹ * a * g = z → CFSG.conjugate (S ⊓ centralizer ({a} : Set G)) g ≤ S →
            ∀ R : Subgroup G, R = S ⊓ centralizer ({a} : Set G) ⊓ CFSG.conjugate S₀ g⁻¹ →
              R.relIndex (S ⊓ centralizer ({a} : Set G)) = 2 ∧ a ∈ R ∧ z ∉ R ∧
              zpowers z ⊔ R = S ⊓ centralizer ({a} : Set G) ∧ zpowers z ⊓ R = ⊥ ∧
              (∀ x ∈ zpowers z, ∀ y ∈ R, x * y = y * x) ∧
              Nonempty (↥(zpowers z) × ↥R ≃* ↥(S ⊓ centralizer ({a} : Set G)))) ∧
          ∀ P : Subgroup G, P = Q ⊓ centralizer ({a} : Set G) →
            CFSG.IsElementaryAbelian 2 P ∧ Nat.card P = 2 ^ (v + 1) ∧
            (∃ L : Submodule (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))),
              (∀ x, x ∈ L ↔ ∃ q : CFSG.pCore 2 M, ((q : M) : G) ∈ P ∧
                x = Additive.ofMul (q : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) ∧
              (∀ x ∈ L, ∀ y ∈ L, b x y = 0) ∧ Module.finrank (ZMod 2) L = v ∧
              b.orthogonal L = L ∧
              ∀ T : Module.End (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))),
                (∀ x y : CFSG.pCore 2 M, ((y : M) : G) = a * ((x : M) : G) * a⁻¹ →
                  T (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) =
                    Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) →
                LinearMap.range (T - 1) = L ∧ LinearMap.ker (T - 1) = L ∧
                  Module.finrank (ZMod 2) (LinearMap.range (T - 1)) = v) ∧
            CFSG.IsElementaryAbelian 2 ↥(P ⊔ zpowers a) ∧
            Nat.card ↥(P ⊔ zpowers a) = 2 ^ (v + 2) ∧
            Q ⊓ centralizer (P : Set G) = Z ⊔ P ∧
            Nonempty (↥(Z ⊔ P) ≃* Multiplicative (ZMod 4) × (Fin v → Multiplicative (ZMod 2))) ∧
            ∀ D : Subgroup G, D = ⁅Q, zpowers a⁆ →
              (∀ x, x ∈ D ↔ ∃ q ∈ Q, x = q⁻¹ * a⁻¹ * q * a) ∧
              IsMulCommutative D ∧ Nat.card D = 2 ^ (v + 1) ∧ D ≤ Q ∧
              (D.subgroupOf Q).Normal ∧ D ≤ Z ⊔ P ∧ D ⊓ Z = zpowers z ∧
              (∀ d ∈ D, a * d * a⁻¹ = d⁻¹) ∧
              {w | ∃ q ∈ Q, q⁻¹ * a * q = w} = {w | ∃ d ∈ D, a * d = w} ∧
              Xor (D = P ∧ CFSG.IsElementaryAbelian 2 D)
                (Nonempty (D ≃* Multiplicative (ZMod 4) ×
                    (Fin (v - 1) → Multiplicative (ZMod 2))) ∧
                  Nat.card ↥(D ⊓ P) = 2 ^ v) ∧
              (∀ d ∈ D, ∃ g : G, g⁻¹ * z * g = a * d) ∧
              {w | ∃ g : G, g⁻¹ * z * g = w} ∩ (D : Set G) = {z} :=
  s0_fusion_aux hsimple hnab hchar he hM hsym hB hBM hQ hnex hexp hZ hzZ hz hwc hS hS₀

end CFSG.LocalAnalysis.GorensteinLyons
