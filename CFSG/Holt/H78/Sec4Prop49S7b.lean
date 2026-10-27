module

public import CFSG.Holt.H78.Sec4Prop49End
public import CFSG.Holt.H78.Sec4Prop49S7
import CFSG.Holt.H78.Sec4KnownKV
import CFSG.Holt.H78.Sec4U34
import CFSG.Holt.H78.Sec4CCL

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General Equiv CFSG.GH74.Uniqueness.Bender
open scoped Pointwise commutatorElement

namespace P49S7

section LineDef

variable {G : Type} [Group G] {Ω : Type} [MulAction G Ω] {α : Ω} {v : G}
  (C : P49Config G Ω α v)

noncomputable def linePt (x : C.D.Ψc C.i) : fixSet Ω (Subgroup.zpowers v) :=
  (C.exists_coord_eq_update x).choose

theorem coord_linePt (x : C.D.Ψc C.i) :
    C.D.coord (linePt C x) = Function.update (C.D.coord C.a) C.i x :=
  (C.exists_coord_eq_update x).choose_spec

theorem coord_linePt_self (x : C.D.Ψc C.i) : C.D.coord (linePt C x) C.i = x := by
  rw [coord_linePt, Function.update_self]

theorem coord_linePt_of_ne (x : C.D.Ψc C.i) {j : C.D.ι} (hj : j ≠ C.i) :
    C.D.coord (linePt C x) j = C.D.coord C.a j := by
  rw [coord_linePt, Function.update_of_ne hj]

end LineDef

section Line

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α : Ω} {v : G} (C : P49Config G Ω α v)

omit [Finite G] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem eq_linePt_iff {δ : fixSet Ω (Subgroup.zpowers v)} {x : C.D.Ψc C.i} :
    δ = linePt C x ↔ (∀ j, j ≠ C.i → C.D.coord δ j = C.D.coord C.a j) ∧ C.D.coord δ C.i = x := by
  constructor
  · rintro rfl
    exact ⟨fun j hj => coord_linePt_of_ne C x hj, coord_linePt_self C x⟩
  · rintro ⟨h1, h2⟩
    apply C.coord_injective
    funext j
    rcases eq_or_ne j C.i with rfl | hj
    · rw [h2, coord_linePt_self]
    · rw [h1 j hj, coord_linePt_of_ne C x hj]

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem linePt_injective : Function.Injective (linePt C) := fun x y h => by
  rw [← coord_linePt_self C x, h, coord_linePt_self]

omit [Finite G] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem linePt_a : linePt C (C.D.coord C.a C.i) = C.a :=
  ((eq_linePt_iff C).mpr ⟨fun _ _ => rfl, rfl⟩).symm

omit [Finite G] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem linePt_b : linePt C (C.D.coord C.b C.i) = C.b :=
  ((eq_linePt_iff C).mpr ⟨fun j hj => (C.coord_eq j hj).symm, rfl⟩).symm

theorem mem_holtDelta_linePt_iff (hS : Sec4Setting G Ω) {x y : C.D.Ψc C.i} (hxy : x ≠ y)
    (z : C.D.Ψc C.i) :
    ((linePt C z : fixSet Ω (Subgroup.zpowers v)) : Ω) ∈
        holtDelta G Ω (linePt C x : Ω) (linePt C y : Ω) ↔
      z ∈ holtDelta (C.D.M C.i) (C.D.Ψc C.i) x y := by
  let C' : P49Config G Ω (linePt C x : Ω) v :=
    { isTypeL := IsTypeL.of_mem_fixSet hS.star C.isTypeL (linePt C x).2
      D := C.D
      pPrimeCore_eq_bot := C.pPrimeCore_eq_bot
      isNaturalSE := C.isNaturalSE
      i := C.i
      a := linePt C x
      b := linePt C y
      coe_a := rfl
      coord_ne := by rw [coord_linePt_self, coord_linePt_self]; exact hxy
      coord_eq := fun j hj => by rw [coord_linePt_of_ne C x hj, coord_linePt_of_ne C y hj] }
  have h : ((linePt C z : fixSet Ω (Subgroup.zpowers v)) : Ω) ∈
      holtDelta G Ω (linePt C x : Ω) (linePt C y : Ω) ↔
        (∀ j, j ≠ C.i → C.D.coord (linePt C z) j = C.D.coord (linePt C x) j) ∧
          C.D.coord (linePt C z) C.i ∈ holtDelta (C.D.M C.i) (C.D.Ψc C.i)
            (C.D.coord (linePt C x) C.i) (C.D.coord (linePt C y) C.i) :=
    C'.mem_holtDelta_iff hS (linePt C z)
  rw [h, coord_linePt_self, coord_linePt_self, coord_linePt_self]
  exact ⟨fun h => h.2, fun h => ⟨fun j hj => by
    rw [coord_linePt_of_ne C z hj, coord_linePt_of_ne C x hj], h⟩⟩

theorem exists_line_action (hS : Sec4Setting G Ω) {c : G} (hcJ : c ∈ longInv G Ω)
    (hcv : c ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G))
    {z : C.D.Ψc C.i} (hcz : c • ((linePt C z : fixSet Ω (Subgroup.zpowers v)) : Ω) = linePt C z) :
    ∃ σ ∈ C.D.M C.i, σ ∈ longInvAt (Perm (C.D.Ψc C.i)) (C.D.Ψc C.i) z ∧
      ∀ w, c • ((linePt C w : fixSet Ω (Subgroup.zpowers v)) : Ω) = linePt C (σ w) := by
  have h3 := three_le_card_fixSet_of_isTypeL hS.star C.isTypeL
  have hcΦ : centralizerImageElt (Ω := Ω) hcv ∈
      longInv (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)) :=
    (hS.mem_longInv_centralizerImage_iff C.isPGroup_zpowers h3 _).mpr
      ⟨c, hcJ, hcv, fun ω => rfl⟩
  set cH : jHull (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)) :=
    ⟨_, mem_jHull_of_mem_longInv hcΦ⟩ with hcH
  have hfixz : (cH : typeLSection G Ω v) • linePt C z = linePt C z := Subtype.ext hcz
  have hρfix : ∀ j, C.D.ρ j cH (C.D.coord (linePt C z) j) = C.D.coord (linePt C z) j :=
    fun j => by rw [← C.D.coord_smul, hfixz]
  have hR := C.D.range_rho_of_not_isOuterFactor (C.isNaturalSE C.i).not_isOuterFactor
  refine ⟨C.D.ρ C.i cH, hR ▸ ⟨cH, rfl⟩, ⟨C.D.rho_mem_longInv hcΦ C.i, ?_⟩, fun w => ?_⟩
  · have := hρfix C.i
    rwa [coord_linePt_self] at this
  · have hpt : (cH : typeLSection G Ω v) • linePt C w = linePt C (C.D.ρ C.i cH w) := by
      rw [eq_linePt_iff]
      refine ⟨fun j hj => ?_, ?_⟩
      · rw [C.D.coord_smul, coord_linePt_of_ne C w hj]
        have := hρfix j
        rwa [coord_linePt_of_ne C z hj] at this
      · rw [C.D.coord_smul, coord_linePt_self]
    exact congrArg Subtype.val hpt

theorem exists_mem_apply_eq_apply_eq {Δ : Type} [Finite Δ] {M : Subgroup (Perm Δ)}
    (hM : IsNaturalSE M) {a b d d' : Δ} (hab : a ≠ b) (hdd' : d ≠ d') :
    ∃ m ∈ M, m a = d ∧ m b = d' := by
  obtain ⟨n, i, e, hA⟩ := hM.exists_isBenderAction
  have := hA.isPretransitive
  obtain ⟨m₁, hm₁⟩ := exists_smul_eq (↥M) a d
  have hm₁a : (m₁ : Perm Δ) a = d := hm₁
  have hb : (m₁ : Perm Δ) b ≠ d := fun h => hab ((m₁ : Perm Δ).injective (hm₁a.trans h.symm))
  obtain ⟨r, hr, hrb⟩ := hM.exists_mem_seRadical_apply_eq hb (Ne.symm hdd')
  refine ⟨r * m₁, mul_mem (seRadical_le hr) m₁.2, ?_, ?_⟩
  · rw [Perm.mul_apply, hm₁a]
    exact apply_eq_of_mem_seRadical hr
  · rw [Perm.mul_apply, hrb]

theorem exists_mem_closure_line_eq (hS : Sec4Setting G Ω) {V : Subgroup G} (hV : IsPGroup 2 V)
    (hvV : v ∈ V)
    (hVL : ∀ w, ((linePt C w : fixSet Ω (Subgroup.zpowers v)) : Ω) ∈ fixSet Ω V)
    {m : Perm (C.D.Ψc C.i)} (hm : m ∈ C.D.M C.i) :
    ∃ g ∈ Subgroup.closure (longInv G Ω ∩ Subgroup.centralizer (V : Set G)),
      ∀ w, g • ((linePt C w : fixSet Ω (Subgroup.zpowers v)) : Ω) = linePt C (m w) := by
  classical
  have hM := C.isNaturalSE C.i
  obtain ⟨n, i', e', hA⟩ := hM.exists_isBenderAction
  have : IsSimpleGroup (C.D.M C.i) := C.D.isSimpleGroup_M C.i
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x₀, hx₀⟩ := exists_prime_orderOf_dvd_card' 2 (C.D.factor C.i).two_dvd_card
  have hm' : m ∈ Subgroup.closure ((C.D.M C.i).subtype '' {y : C.D.M C.i | orderOf y = 2}) := by
    rw [← MonoidHom.map_closure, closure_orderOf_eq_two_eq_top hx₀, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
    exact hm
  have hvC : ∀ c ∈ Subgroup.centralizer (V : Set G),
      c ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) := fun c hc =>
    Subgroup.centralizer_le (Subgroup.zpowers_le.mpr hvV) hc
  clear hm
  induction hm' using Subgroup.closure_induction with
  | mem s hs =>
    obtain ⟨y, hy, rfl⟩ := hs
    set Y : Perm (C.D.Ψc C.i) := (y : Perm (C.D.Ψc C.i)) with hYdef
    have hyJ : Y ∈ longInv (Perm (C.D.Ψc C.i)) (C.D.Ψc C.i) :=
      mem_longInv_subgroup_perm_iff.mp (hA.mem_longInv_iff.mpr hy)
    obtain ⟨z, hz, hzu⟩ := hyJ.2
    have : Nontrivial (C.D.Ψc C.i) := hA.nontrivial
    obtain ⟨x, hxz⟩ := exists_ne z
    have hYx : Y x ≠ x := fun h => hxz (hzu x h)
    have hzΔ : z ∈ holtDelta (C.D.M C.i) (C.D.Ψc C.i) x (Y x) :=
      mem_holtDelta_subgroup_perm_iff.mpr ⟨Y, ⟨y.2, hyJ, rfl⟩, hz⟩
    have hxy : x ≠ Y x := fun h => hYx h.symm
    have hlz := (mem_holtDelta_linePt_iff C hS hxy z).mpr hzΔ
    obtain ⟨c, hc, hcz, hcV⟩ := hS.exists_mem_longInvSwap_centralizer_of_mem_holtDelta
      (fun h => hxy (linePt_injective C (Subtype.ext h))) hlz hV
      (le_inf (mem_fixSet_iff_le_stabilizer.mp (hVL x))
        (mem_fixSet_iff_le_stabilizer.mp (hVL (Y x))))
      (mem_fixSet_iff_le_stabilizer.mp (hVL z))
    obtain ⟨σ, hσM, hσJ, hσw⟩ := exists_line_action C hS hc.1 (hvC c hcV) hcz
    have hσx : σ x = Y x := linePt_injective C (Subtype.ext ((hσw x).symm.trans hc.2))
    have hσY : σ = Y := hM.eq_of_mem_longInvAt_of_apply_eq hσM y.2 hσJ ⟨hyJ, hz⟩ hxz hσx
    exact ⟨c, Subgroup.subset_closure ⟨hc.1, hcV⟩, fun w => by rw [hσw, hσY]; rfl⟩
  | one => exact ⟨1, one_mem _, fun w => by rw [one_smul, Perm.one_apply]⟩
  | mul m m' _ _ ih ih' =>
    obtain ⟨g, hg, hgw⟩ := ih
    obtain ⟨g', hg', hg'w⟩ := ih'
    exact ⟨g * g', mul_mem hg hg', fun w => by rw [mul_smul, hg'w, hgw, Perm.mul_apply]⟩
  | inv m _ ih =>
    obtain ⟨g, hg, hgw⟩ := ih
    refine ⟨g⁻¹, inv_mem hg, fun w => ?_⟩
    rw [inv_smul_eq_iff, hgw, ← Perm.mul_apply, mul_inv_cancel, Perm.one_apply]

theorem linePt_mem_holtDelta (hS : Sec4Setting G Ω) {x : C.D.Ψc C.i}
    (hx : x ∈ holtDelta (C.D.M C.i) (C.D.Ψc C.i) (C.D.coord C.a C.i) (C.D.coord C.b C.i)) :
    ((linePt C x : fixSet Ω (Subgroup.zpowers v)) : Ω) ∈ holtDelta G Ω α C.β :=
  (C.mem_holtDelta_iff hS (linePt C x)).mpr ⟨fun j hj => coord_linePt_of_ne C x hj, by
    rw [coord_linePt_self]
    exact hx⟩

theorem exists_mem_closure_of_fix_line (hS : Sec4Setting G Ω) {V : Subgroup G}
    (hV : IsPGroup 2 V) (hvV : v ∈ V)
    (hVL : ∀ w, ((linePt C w : fixSet Ω (Subgroup.zpowers v)) : Ω) ∈ fixSet Ω V) :
    ∃ g ∈ Subgroup.closure (longInv G Ω ∩ Subgroup.centralizer (V : Set G)),
      ∃ δ δ' : holtDelta G Ω α C.β, (δ : Ω) ∈ fixSet Ω (Subgroup.zpowers v) ∧
        (δ' : Ω) ∈ fixSet Ω (Subgroup.zpowers v) ∧ g • α = δ ∧ g • C.β = δ' := by
  have h3 := C.three_le_ncard_holtDelta_M
  obtain ⟨d, hd⟩ := Set.nonempty_of_ncard_ne_zero (by omega : (holtDelta (C.D.M C.i) (C.D.Ψc C.i)
    (C.D.coord C.a C.i) (C.D.coord C.b C.i)).ncard ≠ 0)
  obtain ⟨d', hd', hdd'⟩ := Set.exists_ne_of_one_lt_ncard (by omega : 1 < (holtDelta (C.D.M C.i)
    (C.D.Ψc C.i) (C.D.coord C.a C.i) (C.D.coord C.b C.i)).ncard) d
  obtain ⟨m, hm, hma, hmb⟩ := exists_mem_apply_eq_apply_eq (C.isNaturalSE C.i) C.coord_ne
    (Ne.symm hdd')
  obtain ⟨g, hg, hgw⟩ := exists_mem_closure_line_eq C hS hV hvV hVL hm
  refine ⟨g, hg, ⟨_, linePt_mem_holtDelta C hS hd⟩, ⟨_, linePt_mem_holtDelta C hS hd'⟩,
    (linePt C d).2, (linePt C d').2, ?_, ?_⟩
  · have h := hgw (C.D.coord C.a C.i)
    rw [linePt_a, hma] at h
    calc g • α = g • ((C.a : fixSet Ω (Subgroup.zpowers v)) : Ω) := by rw [C.coe_a]
      _ = _ := h
  · have h := hgw (C.D.coord C.b C.i)
    rw [linePt_b, hmb] at h
    exact h

end Line

section Unitary


theorem ne_and_ne_of_mem_holtDelta {Δ : Type*} {N : Subgroup (Perm Δ)} {a b d : Δ} (hab : a ≠ b)
    (hd : d ∈ holtDelta N Δ a b) : d ≠ a ∧ d ≠ b := by
  obtain ⟨x, hx, hxd⟩ := mem_holtDelta_subgroup_perm_iff.mp hd
  refine ⟨fun h => hab ?_, fun h => hab ?_⟩
  · rw [← hx.2.2, ← h, hxd]
  · rw [← apply_eq_of_mem_swapSet hx, ← h, hxd]

theorem mem_holtDelta_of_unitary {Δ : Type} [Finite Δ] {M : Subgroup (Perm Δ)} {n e : ℕ}
    (hA : IsBenderAction ↥M Δ n 3 e) {τ : Perm Δ}
    (hτN : τ ∈ Subgroup.normalizer (M : Set (Perm Δ))) (hτ2 : τ * τ = 1) (hτM : τ ∉ M)
    {b c d : Δ} (hcb : c ≠ b) (hτb : τ b = b) (hτc : τ c = c) (hτd : τ d = d) (hdb : d ≠ b)
    (hdc : d ≠ c) : b ∈ holtDelta M Δ c d := by
  have hM : IsNaturalSE M := isNaturalSE_iff.mpr ⟨n, 3, e, hA⟩
  have hdF : d ∈ fixedBy Δ τ := hτd
  rw [hA.fixedBy_eq_insert_image_of_unitary hτN hτ2 hτM hcb hτb hτc, Set.mem_insert_iff] at hdF
  rcases hdF with h | ⟨z, hz, hzc⟩
  · exact absurd h hdb
  · simp only at hzc
    have hzM : z ∈ M := seRadical_le hz.1
    have hz2 : z * z = 1 := hM.mul_self_eq_one_of_mem_rootCenter hz
    have hz1 : z ≠ 1 := fun h => hdc (by rw [← hzc, h, Perm.one_apply])
    have hzJ : z ∈ longInv (Perm Δ) Δ := by
      refine ⟨orderOf_eq_prime (by rw [sq]; exact hz2) hz1, ?_⟩
      have := hM.existsUnique_fixed (x := ⟨z, hzM⟩)
        (by rw [Subgroup.orderOf_mk]; exact orderOf_eq_prime (by rw [sq]; exact hz2) hz1)
      simpa using this
    exact mem_holtDelta_subgroup_perm_iff.mpr ⟨z, ⟨hzM, hzJ, hzc⟩, apply_eq_of_mem_seRadical hz.1⟩

end Unitary

section Lemma54

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α : Ω} {v : G} (C : P49Config G Ω α v)

theorem exists_mem_closure_of_not_fix_line (hS : Sec4Setting G Ω) {U : Subgroup G}
    (hU : IsPGroup 2 U) (hUv : ∀ u ∈ U, u * v = v * u)
    (hUαβ : U ≤ stabilizer G α ⊓ stabilizer G C.β)
    (hUB : ∀ δ : holtDelta G Ω α C.β, (δ : Ω) ∈ fixSet Ω (Subgroup.zpowers v) →
      (δ : Ω) ∈ fixSet Ω U)
    {u₀ : G} (hu₀ : u₀ ∈ U) {w₀ : C.D.Ψc C.i}
    (hw₀ : u₀ • ((linePt C w₀ : fixSet Ω (Subgroup.zpowers v)) : Ω) ≠ linePt C w₀)
    {V : Subgroup G} (hV : IsPGroup 2 V) (hVα : V ≤ stabilizer G α)
    (hVβ : V ≤ stabilizer G C.β)
    (hVB : ∀ δ : holtDelta G Ω α C.β, (δ : Ω) ∈ fixSet Ω (Subgroup.zpowers v) →
      (δ : Ω) ∈ fixSet Ω V) :
    ∃ g ∈ Subgroup.closure (longInv G Ω ∩ Subgroup.centralizer (V : Set G)),
      ∃ δ δ' : holtDelta G Ω α C.β, (δ : Ω) ∈ fixSet Ω (Subgroup.zpowers v) ∧
        (δ' : Ω) ∈ fixSet Ω (Subgroup.zpowers v) ∧ g • α = δ ∧ g • C.β = δ' := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hM := C.isNaturalSE C.i
  set a₀ := C.D.coord C.a C.i with ha₀
  set b₀ := C.D.coord C.b C.i with hb₀
  set X := holtDelta (C.D.M C.i) (C.D.Ψc C.i) a₀ b₀ with hX
  have hu₀v : u₀ ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) :=
    mem_centralizer_zpowers_iff.mpr (hUv u₀ hu₀)
  have hua : centralizerImageElt (Ω := Ω) hu₀v • C.a = C.a := Subtype.ext (by
    show u₀ • (C.a : Ω) = C.a
    rw [C.coe_a]
    exact (hUαβ hu₀).1)
  have hub : centralizerImageElt (Ω := Ω) hu₀v • C.b = C.b := Subtype.ext (hUαβ hu₀).2
  obtain ⟨σ, hσN, hσa, hσb, hσl⟩ :=
    C.D.exists_mem_normalizer_M_of_smul_eq C.coord_eq C.coord_ne hua hub
  have hline : ∀ w, u₀ • ((linePt C w : fixSet Ω (Subgroup.zpowers v)) : Ω) =
      linePt C (σ w) := fun w => by
    obtain ⟨h1, h2⟩ := hσl (linePt C w) fun j hj => coord_linePt_of_ne C w hj
    have : centralizerImageElt (Ω := Ω) hu₀v • linePt C w = linePt C (σ w) :=
      (eq_linePt_iff C).mpr ⟨h1, by rw [h2, coord_linePt_self]⟩
    exact congrArg Subtype.val this
  have hpow : ∀ (k : ℕ) w, u₀ ^ k • ((linePt C w : fixSet Ω (Subgroup.zpowers v)) : Ω) =
      linePt C ((σ ^ k) w) := by
    intro k
    induction k with
    | zero => intro w; rw [pow_zero, pow_zero, one_smul, Perm.one_apply]
    | succ k ih => intro w; rw [pow_succ, mul_smul, hline, ih, pow_succ, Perm.mul_apply]
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hU ⟨u₀, hu₀⟩
  have hu1 : u₀ ^ 2 ^ k = 1 := by
    have h := pow_orderOf_eq_one (⟨u₀, hu₀⟩ : U)
    rw [hk] at h
    exact congrArg Subtype.val h
  have hσk : σ ^ 2 ^ k = 1 := Equiv.ext fun w => linePt_injective C (Subtype.ext (by
    rw [← hpow, hu1, one_smul, Perm.one_apply]))
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hσk)
  have hσ1 : σ ≠ 1 := fun h => hw₀ (by rw [hline, h, Perm.one_apply])
  have hj0 : j ≠ 0 := fun h => hσ1 (orderOf_eq_one_iff.mp (by rw [hj, h, pow_zero]))
  set τ := σ ^ 2 ^ (j - 1) with hτdef
  have hτ2 : τ * τ = 1 := by
    rw [hτdef, ← pow_add, ← two_mul, ← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hj0),
      ← hj, pow_orderOf_eq_one]
  have hτ1 : τ ≠ 1 := pow_ne_one_of_lt_orderOf (by positivity) (by
    rw [hj]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hτN : τ ∈ Subgroup.normalizer (C.D.M C.i : Set (Perm (C.D.Ψc C.i))) := pow_mem hσN _
  have hτa : τ a₀ = a₀ := Perm.pow_apply_eq_self_of_apply_eq_self hσa _
  have hτb : τ b₀ = b₀ := Perm.pow_apply_eq_self_of_apply_eq_self hσb _
  have hτX : ∀ d ∈ X, τ d = d := fun d hd => by
    refine Perm.pow_apply_eq_self_of_apply_eq_self (linePt_injective C (Subtype.ext ?_)) _
    rw [← hline]
    exact mem_fixSet_iff_le_stabilizer.mp (hUB ⟨_, linePt_mem_holtDelta C hS hd⟩
      (linePt C d).2) hu₀
  have hτM : τ ∉ C.D.M C.i := fun h => by
    obtain ⟨z, -, hz⟩ := hM.existsUnique_fixed (x := ⟨τ, h⟩) (by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime (by rw [sq]; exact hτ2) hτ1)
    exact C.coord_ne ((hz a₀ hτa).trans (hz b₀ hτb).symm)
  have hd3 : 3 ≤ X.ncard := C.three_le_ncard_holtDelta_M
  obtain ⟨d, hd⟩ := Set.nonempty_of_ncard_ne_zero (by omega : X.ncard ≠ 0)
  obtain ⟨d', hd', hdd'⟩ := Set.exists_ne_of_one_lt_ncard (by omega : 1 < X.ncard) d
  obtain ⟨n, i', e', hA⟩ := hM.exists_isBenderAction
  obtain ⟨hi1, hi3, -⟩ := hA.params
  interval_cases i'
  ·
    exfalso
    have ha₀X : a₀ ∉ X := fun h => (ne_and_ne_of_mem_holtDelta C.coord_ne h).1 rfl
    have hb₀X : b₀ ∉ X := fun h => (ne_and_ne_of_mem_holtDelta C.coord_ne h).2 rfl
    have hall : insert a₀ (insert b₀ X) = Set.univ := by
      refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_ (Set.toFinite _)
      rw [Set.ncard_univ, Set.ncard_insert_of_notMem (fun h => by
          rcases h with h | h
          · exact C.coord_ne h
          · exact ha₀X h),
        Set.ncard_insert_of_notMem hb₀X, hA.ncard_holtDelta C.coord_ne, hA.card_eq, pow_one]
      have := Nat.one_le_two_pow (n := n)
      omega
    refine hτ1 (Equiv.ext fun y => ?_)
    have hy : y ∈ insert a₀ (insert b₀ X) := hall ▸ Set.mem_univ y
    rcases hy with rfl | rfl | hy
    · exact hτa
    · exact hτb
    · exact hτX y hy
  ·
    exact absurd (hA.mem_of_mul_self_eq_one_of_suzuki hτN hτ2) hτM
  ·
    obtain ⟨hda, hdb⟩ := ne_and_ne_of_mem_holtDelta C.coord_ne hd
    obtain ⟨hd'a, hd'b⟩ := ne_and_ne_of_mem_holtDelta C.coord_ne hd'
    have h1 : b₀ ∈ holtDelta (C.D.M C.i) (C.D.Ψc C.i) a₀ d :=
      mem_holtDelta_of_unitary hA hτN hτ2 hτM C.coord_ne hτb hτa (hτX d hd) hdb hda
    have h2 : d ∈ holtDelta (C.D.M C.i) (C.D.Ψc C.i) b₀ d' :=
      mem_holtDelta_of_unitary hA hτN hτ2 hτM (Ne.symm hdb) (hτX d hd) hτb (hτX d' hd') hdd'
        hd'b
    have hα' : ((linePt C a₀ : fixSet Ω (Subgroup.zpowers v)) : Ω) = α := by
      rw [ha₀, linePt_a]
      exact C.coe_a
    have hβ' : ((linePt C b₀ : fixSet Ω (Subgroup.zpowers v)) : Ω) = C.β := by rw [hb₀, linePt_b]
    have hG1 : C.β ∈ holtDelta G Ω α (linePt C d : fixSet Ω (Subgroup.zpowers v)) := by
      have := (mem_holtDelta_linePt_iff C hS (Ne.symm hda) b₀).mpr h1
      rwa [hα', hβ'] at this
    have hG2 : ((linePt C d : fixSet Ω (Subgroup.zpowers v)) : Ω) ∈
        holtDelta G Ω C.β (linePt C d' : fixSet Ω (Subgroup.zpowers v)) := by
      have := (mem_holtDelta_linePt_iff C hS (Ne.symm hd'b) d).mpr h2
      rwa [hβ'] at this
    have hαδ : α ≠ ((linePt C d : fixSet Ω (Subgroup.zpowers v)) : Ω) := fun h =>
      hda (linePt_injective C (Subtype.ext (hα'.trans h))).symm
    have hβδ' : C.β ≠ ((linePt C d' : fixSet Ω (Subgroup.zpowers v)) : Ω) := fun h =>
      hd'b (linePt_injective C (Subtype.ext (hβ'.trans h))).symm
    have hVδ := mem_fixSet_iff_le_stabilizer.mp (hVB ⟨_, linePt_mem_holtDelta C hS hd⟩
      (linePt C d).2)
    have hVδ' := mem_fixSet_iff_le_stabilizer.mp (hVB ⟨_, linePt_mem_holtDelta C hS hd'⟩
      (linePt C d').2)
    obtain ⟨c₁, hc₁, hc₁β, hc₁V⟩ := hS.exists_mem_longInvSwap_centralizer_of_mem_holtDelta
      hαδ hG1 hV (le_inf hVα hVδ) hVβ
    obtain ⟨c₂, hc₂, hc₂δ, hc₂V⟩ := hS.exists_mem_longInvSwap_centralizer_of_mem_holtDelta
      hβδ' hG2 hV (le_inf hVβ hVδ') hVδ
    refine ⟨c₂ * c₁, mul_mem (Subgroup.subset_closure ⟨hc₂.1, hc₂V⟩)
      (Subgroup.subset_closure ⟨hc₁.1, hc₁V⟩), ⟨_, linePt_mem_holtDelta C hS hd⟩,
      ⟨_, linePt_mem_holtDelta C hS hd'⟩, (linePt C d).2, (linePt C d').2, ?_, ?_⟩
    · rw [mul_smul, hc₁.2, hc₂δ]
    · rw [mul_smul, hc₁β, hc₂.2]

theorem exists_mem_closure_smul_mem_B (hS : Sec4Setting G Ω) {U : Subgroup G}
    (hU : IsPGroup 2 U) (hUv : ∀ u ∈ U, u * v = v * u)
    (hUαβ : U ≤ stabilizer G α ⊓ stabilizer G C.β)
    (hUB : ∀ δ : holtDelta G Ω α C.β, (δ : Ω) ∈ fixSet Ω (Subgroup.zpowers v) →
      (δ : Ω) ∈ fixSet Ω U) :
    ∃ g ∈ Subgroup.closure (longInv G Ω ∩ Subgroup.centralizer (U : Set G)),
      ∃ δ δ' : holtDelta G Ω α C.β, (δ : Ω) ∈ fixSet Ω (Subgroup.zpowers v) ∧
        (δ' : Ω) ∈ fixSet Ω (Subgroup.zpowers v) ∧ g • α = δ ∧ g • C.β = δ' := by
  have hvU : Subgroup.zpowers v ≤ Subgroup.normalizer (U : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro h
    have hvinv : ∀ u ∈ U, v * u * v⁻¹ = u := fun u hu => by
      rw [← hUv u hu, mul_inv_cancel_right]
    constructor
    · intro hh
      rw [hvinv h hh]
      exact hh
    · intro hh
      have h1 := hUv _ hh
      have h2 : v * h * v⁻¹ = h := by
        have : v * h = v * (v * h * v⁻¹) := by rw [← h1]; group
        exact (mul_left_cancel this).symm
      rw [← h2]
      exact hh
  have hV : IsPGroup 2 ↥(Subgroup.zpowers v ⊔ U) :=
    IsPGroup.to_sup_of_normal_right' C.isPGroup_zpowers hU hvU
  have hvV : v ∈ Subgroup.zpowers v ⊔ U := Subgroup.mem_sup_left (Subgroup.mem_zpowers v)
  have hfixV : ∀ ω : Ω, ω ∈ fixSet Ω (Subgroup.zpowers v) → ω ∈ fixSet Ω U →
      ω ∈ fixSet Ω (Subgroup.zpowers v ⊔ U) := fun ω h1 h2 =>
    mem_fixSet_iff_le_stabilizer.mpr (sup_le (mem_fixSet_iff_le_stabilizer.mp h1)
      (mem_fixSet_iff_le_stabilizer.mp h2))
  have hα : α ∈ fixSet Ω (Subgroup.zpowers v) := mem_fixSet_zpowers_iff.mpr C.v_smul_α
  have hβ : C.β ∈ fixSet Ω (Subgroup.zpowers v) := mem_fixSet_zpowers_iff.mpr C.v_smul_β
  have hVα : Subgroup.zpowers v ⊔ U ≤ stabilizer G α := mem_fixSet_iff_le_stabilizer.mp
    (hfixV α hα (mem_fixSet_iff_le_stabilizer.mpr (hUαβ.trans inf_le_left)))
  have hVβ : Subgroup.zpowers v ⊔ U ≤ stabilizer G C.β := mem_fixSet_iff_le_stabilizer.mp
    (hfixV C.β hβ (mem_fixSet_iff_le_stabilizer.mpr (hUαβ.trans inf_le_right)))
  have hcl : Subgroup.closure (longInv G Ω ∩
      Subgroup.centralizer ((Subgroup.zpowers v ⊔ U : Subgroup G) : Set G)) ≤
        Subgroup.closure (longInv G Ω ∩ Subgroup.centralizer (U : Set G)) :=
    Subgroup.closure_mono (Set.inter_subset_inter_right _
      (Subgroup.centralizer_le (le_sup_right : U ≤ Subgroup.zpowers v ⊔ U)))
  by_cases hfix : ∀ w, ∀ u ∈ U,
      u • ((linePt C w : fixSet Ω (Subgroup.zpowers v)) : Ω) = linePt C w
  · obtain ⟨g, hg, rest⟩ := exists_mem_closure_of_fix_line C hS hV hvV fun w =>
      hfixV _ (linePt C w).2 (mem_fixSet_iff_le_stabilizer.mpr fun u hu =>
        mem_stabilizer_iff.mpr (hfix w u hu))
    exact ⟨g, hcl hg, rest⟩
  · push Not at hfix
    obtain ⟨w₀, u₀, hu₀, hw₀⟩ := hfix
    obtain ⟨g, hg, rest⟩ := exists_mem_closure_of_not_fix_line C hS hU hUv hUαβ hUB hu₀ hw₀ hV
      hVα hVβ fun δ hδ => hfixV _ hδ (hUB δ hδ)
    exact ⟨g, hcl hg, rest⟩

theorem exists_involution_twoPointKernel (hS : Sec4Setting G Ω)
    (hT : ¬ Odd (Nat.card (twoPointKernel G Ω α C.β))) :
    ∃ x ∈ twoPointKernel G Ω α C.β, x * v = v * x ∧ orderOf x = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨γ, -, hγΔ, -, -⟩ := C.exists_mem_holtDelta_ne hS
  have hvH : Subgroup.zpowers v ≤ stabilizer G α ⊓ stabilizer G C.β ⊓ stabilizer G (γ : Ω) :=
    Subgroup.zpowers_le.mpr ⟨⟨C.v_smul_α, C.v_smul_β⟩, mem_fixSet_zpowers_iff.mp γ.2⟩
  obtain ⟨S, hvS, hSyl⟩ := exists_fusionIsSylowIn_ge C.isPGroup_zpowers hvH
  have hT1 : S ⊓ twoPointKernel G Ω α C.β ≠ ⊥ := fun h =>
    hT ((inf_twoPointKernel_eq_bot_iff hγΔ hSyl).mp h)
  have hSp : IsPGroup 2 S := hSyl.2.1
  have : Group.IsNilpotent S := hSp.isNilpotent
  set T' := (twoPointKernel G Ω α C.β).subgroupOf S with hT'
  have hT'n : T'.Normal := ⟨fun t ht s => by
    rw [hT', Subgroup.mem_subgroupOf] at ht ⊢
    exact conj_mem_twoPointKernel (Subgroup.mem_inf.mp (hSyl.1 s.2)).1 ht⟩
  have hT'1 : T' ≠ ⊥ := by
    intro h
    apply hT1
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hx.1⟩ : S) ∈ T' := hx.2
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  have hZ := Group.IsNilpotent.inf_center_ne_bot_of_normal hT'1
  have hP : IsPGroup 2 ↥(T' ⊓ Subgroup.center S) := hSp.to_subgroup _
  have : Nontrivial ↥(T' ⊓ Subgroup.center S) := (Subgroup.nontrivial_iff_ne_bot _).mpr hZ
  obtain ⟨n, hn0, hn⟩ := hP.nontrivial_iff_card.mp inferInstance
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (by rw [hn]; exact dvd_pow_self 2 hn0.ne')
  refine ⟨((x : S) : G), (x.2.1 : (x : S) ∈ T'), ?_, ?_⟩
  · have hc := Subgroup.mem_center_iff.mp x.2.2 ⟨v, hvS (Subgroup.mem_zpowers v)⟩
    exact (congrArg Subtype.val hc).symm
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]

theorem exists_mem_longInvSwap_rho_update (hS : Sec4Setting G Ω)
    (D' : HoltData (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β))
    (hT : Odd (Nat.card (twoPointKernel G Ω α C.β))) {w : G}
    (hw : w ∈ longInvSwap G Ω α C.β) (hwv : w * v = v * w) {m : D'.ι}
    (hm : IsNaturalSE (D'.M m)) :
    ∃ (c : G) (hc : c ∈ longInvSwap G Ω α C.β), c * v = v * c ∧
      ∀ k, D'.ρ k ⟨_, mem_jHull_of_mem_longInv (C.twoPointElt_mem_longInv hS hc)⟩ =
        Function.update (fun k => D'.ρ k
          ⟨_, mem_jHull_of_mem_longInv (C.twoPointElt_mem_longInv hS hw)⟩) m
          (D'.ρ m ⟨C.vHat, C.vHat_mem_jHull hS⟩) k := by
  classical
  have h3 := C.three_le_card_holtDelta hS
  set wH : jHull (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β) :=
    ⟨_, mem_jHull_of_mem_longInv (C.twoPointElt_mem_longInv hS hw)⟩ with hwH
  set xH : jHull (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β) :=
    ⟨C.vHat, C.vHat_mem_jHull hS⟩ with hxH
  set Y : ∀ k, Perm (D'.Ψc k) :=
    Function.update (fun k => D'.ρ k wH) m (D'.ρ m xH) with hY
  obtain ⟨z₀, hz₀, hz₀u⟩ := C.existsUnique_fixed_of_isNaturalSE D' hS hw hwv hm
  have hxx : xH * xH = 1 := Subtype.ext C.vHat_mul_vHat
  have hxmJ : D'.ρ m xH ∈ longInv (Perm (D'.Ψc m)) (D'.Ψc m) :=
    ⟨orderOf_eq_prime (by rw [sq, ← map_mul, hxx, map_one])
      (C.rho_vHat_ne_one_of_isNaturalSE D' hS hw hwv hm), ⟨z₀, hz₀, hz₀u⟩⟩
  have hYr : ∀ k, Y k ∈ (D'.ρ k).range := fun k => by
    rcases eq_or_ne k m with rfl | hk
    · rw [hY, Function.update_self]
      exact ⟨xH, rfl⟩
    · rw [hY, Function.update_of_ne hk]
      exact ⟨wH, rfl⟩
  have hYJ : ∀ k, Y k ∈ longInv (Perm (D'.Ψc k)) (D'.Ψc k) := fun k => by
    rcases eq_or_ne k m with rfl | hk
    · rw [hY, Function.update_self]
      exact hxmJ
    · rw [hY, Function.update_of_ne hk]
      exact D'.rho_mem_longInv (C.twoPointElt_mem_longInv hS hw) k
  have hYx : ∀ k, Y k * D'.ρ k xH = D'.ρ k xH * Y k := fun k => by
    rcases eq_or_ne k m with rfl | hk
    · rw [hY, Function.update_self]
    · rw [hY, Function.update_of_ne hk]
      exact C.rho_w_commute D' hS hw hwv k
  obtain ⟨zH, hzJ, hρz⟩ := D'.exists_mem_longInv_rho_eq Y hYr hYJ
  set x := C.vHat with hxdef
  set z : twoPointSection G Ω α C.β := zH.1 with hzdef
  have hzz : z * z = 1 := mul_self_eq_one_of_mem_longInv hzJ
  have hsoc : ⁅x, z⁆ ∈ D'.socPre := by
    rw [show ⁅x, z⁆ = x * (z * x⁻¹ * z⁻¹) by rw [commutatorElement_def]; group]
    exact mul_mem (C.vHat_mem_socPre hS D')
      (D'.conj_mem_socPre zH.2 (inv_mem (C.vHat_mem_socPre hS D')))
  have hker : ⁅x, z⁆ ∈ jOrbitKernel (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β) := by
    have h := (D'.mem_jOrbitKernel_iff_rho (h := ⁅xH, zH⁆)).mpr fun k => by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, hρz k]
      exact (hYx k).symm
    exact h
  have hO : ⁅x, z⁆ ∈ jOddCore (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β) := by
    rw [← D'.socPre_inf_jOrbitKernel]
    exact ⟨hsoc, hker⟩
  have hsq : (x * z) ^ 2 = ⁅x, z⁆ := by
    rw [commutatorElement_def, inv_eq_of_mul_eq_one_right C.vHat_mul_vHat,
      inv_eq_of_mul_eq_one_right hzz, sq, ← mul_assoc]
  have hodd : Odd (orderOf ((x * z) ^ 2)) := by
    rw [hsq]
    exact Odd.of_dvd_nat odd_card_jOddCore (Subgroup.orderOf_dvd_natCard _ hO)
  obtain ⟨k, hk⟩ := hodd
  obtain ⟨r, g, hrx, hgr, hzr⟩ := exists_conj_commute_of_odd C.vHat_mul_vHat hzz k
    (by rw [← hk]; exact pow_orderOf_eq_one _)
  have hrJ : r ∈ longInv (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β) := by
    rw [← hgr]
    exact conj_mem_longInv hzJ g
  have hoO : ((x * z) ^ 2) ^ k ∈ jOddCore (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β) :=
    pow_mem (hsq ▸ hO) k
  have hρr : ∀ j, D'.ρ j ⟨r, mem_jHull_of_mem_longInv hrJ⟩ = Y j := fun j => by
    have hr : (⟨r, mem_jHull_of_mem_longInv hrJ⟩ : jHull (twoPointSection G Ω α C.β)
        (holtDelta G Ω α C.β)) = zH * ⟨_, jOddCore_le_jHull hoO⟩ := Subtype.ext (by
      rw [Subgroup.coe_mul]
      show r = z * ((x * z) ^ 2) ^ k
      rw [← hzr, mul_inv_cancel_left])
    rw [hr, map_mul, D'.rho_eq_one_of_mem_jOddCore (h := ⟨_, jOddCore_le_jHull hoO⟩) hoO j,
      mul_one, hρz j]
  obtain ⟨c₁, hc₁, hc₁r⟩ := (hS.mem_longInv_twoPointSection_iff C.ne h3 r).mp hrJ
  have hc₁2 : c₁ * c₁ = 1 := mul_self_eq_one_of_mem_longInv hc₁.1
  have hxr : x * r * (x * r) = 1 := by
    calc x * r * (x * r) = x * (r * x) * r := by group
      _ = x * (x * r) * r := by rw [hrx]
      _ = (x * x) * (r * r) := by group
      _ = 1 := by rw [C.vHat_mul_vHat, mul_self_eq_one_of_mem_longInv hrJ, one_mul]
  have hvc₁ : ∀ δ : holtDelta G Ω α C.β,
      (v * c₁) • (δ : Ω) = (((x * r) • δ : holtDelta G Ω α C.β) : Ω) := fun δ => by
    rw [mul_smul, ← hc₁r δ]
    rfl
  have hκ : (v * c₁) ^ 2 ∈ twoPointKernel G Ω α C.β := by
    refine mem_twoPointKernel.mpr ⟨?_, ?_, fun δ hδ => ?_⟩
    · rw [sq, mul_smul, mul_smul, mul_smul, hc₁.2, C.v_smul_β, smul_eq_of_mem_longInvSwap hc₁,
        C.v_smul_α]
    · rw [sq, mul_smul, mul_smul, mul_smul, smul_eq_of_mem_longInvSwap hc₁, C.v_smul_α, hc₁.2,
        C.v_smul_β]
    · have h1 := hvc₁ ⟨δ, hδ⟩
      have h2 := hvc₁ ((x * r) • ⟨δ, hδ⟩)
      rw [sq, mul_smul]
      show (v * c₁) • (v * c₁) • ((⟨δ, hδ⟩ : holtDelta G Ω α C.β) : Ω) = δ
      rw [h1, h2, ← mul_smul, hxr, one_smul]
  have hκodd : Odd (orderOf ((v * c₁) ^ 2)) :=
    Odd.of_dvd_nat hT (Subgroup.orderOf_dvd_natCard _ hκ)
  obtain ⟨k', hk'⟩ := hκodd
  obtain ⟨c', g', hc'v, hg'c, hcc'⟩ := exists_conj_commute_of_odd C.v_mul_v hc₁2 k'
    (by rw [← hk']; exact pow_orderOf_eq_one _)
  have hc'eq : c' = c₁ * ((v * c₁) ^ 2) ^ k' := by rw [← hcc', mul_inv_cancel_left]
  obtain ⟨hκα, -, hκΔ⟩ := mem_twoPointKernel.mp (pow_mem hκ k')
  have hc'J : c' ∈ longInvSwap G Ω α C.β := ⟨by rw [← hg'c]; exact conj_mem_longInv hc₁.1 g',
    by rw [hc'eq, mul_smul, hκα, hc₁.2]⟩
  have hc'δ : ∀ δ : holtDelta G Ω α C.β, c' • (δ : Ω) = c₁ • (δ : Ω) := fun δ => by
    rw [hc'eq, mul_smul, hκΔ δ δ.2]
  refine ⟨c', hc'J, hc'v, fun j => ?_⟩
  have he : (⟨_, mem_jHull_of_mem_longInv (C.twoPointElt_mem_longInv hS hc'J)⟩ :
      jHull (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β)) =
        ⟨r, mem_jHull_of_mem_longInv hrJ⟩ :=
    Subtype.ext (Subtype.ext (Equiv.ext fun δ => Subtype.ext (by
      show c' • (δ : Ω) = ((r : Perm (holtDelta G Ω α C.β)) δ : Ω)
      rw [hc'δ, hc₁r])))
  rw [he, hρr j]

theorem exists_twoElement_of_odd (hS : Sec4Setting G Ω)
    (D' : HoltData (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β))
    (hT : Odd (Nat.card (twoPointKernel G Ω α C.β))) {m : D'.ι} (hm : IsNaturalSE (D'.M m)) :
    ∃ u : G, u * v = v * u ∧ u • α = α ∧ u • C.β = C.β ∧ IsPGroup 2 (Subgroup.zpowers u) ∧
      u ≠ 1 ∧ ∃ σ : Perm (D'.Ψc m),
        (∀ δ : holtDelta G Ω α C.β, u • (δ : Ω) = δ ↔ σ (D'.coord δ m) = D'.coord δ m) ∧
        ∀ δ : holtDelta G Ω α C.β, (δ : Ω) ∈ fixSet Ω (Subgroup.zpowers v) →
          σ (D'.coord δ m) = D'.coord δ m := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 := C.three_le_card_holtDelta hS
  obtain ⟨w, hw, hwv, hwv'⟩ := C.exists_mem_longInvSwap_mul hS
  obtain ⟨c, hc, hcv, hρc⟩ := exists_mem_longInvSwap_rho_update C hS D' hT hw hwv hm
  have hwJ := C.twoPointElt_mem_longInv hS hw
  have hcJ := C.twoPointElt_mem_longInv hS hc
  have huJ := C.twoPointElt_mem_longInv hS hwv'
  set wH : jHull (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β) :=
    ⟨_, mem_jHull_of_mem_longInv hwJ⟩ with hwH
  set cH : jHull (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β) :=
    ⟨_, mem_jHull_of_mem_longInv hcJ⟩ with hcH
  set uH : jHull (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β) :=
    ⟨_, mem_jHull_of_mem_longInv huJ⟩ with huH
  set xH : jHull (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β) :=
    ⟨C.vHat, C.vHat_mem_jHull hS⟩ with hxH
  set σ : Perm (D'.Ψc m) := D'.ρ m wH * D'.ρ m xH with hσ
  have hww : D'.ρ m wH * D'.ρ m wH = 1 :=
    mul_self_eq_one_of_mem_longInv (D'.rho_mem_longInv hwJ m)
  have hρk : ∀ k, k ≠ m → D'.ρ k (wH * cH) = 1 := fun k hk => by
    rw [map_mul, hρc k, Function.update_of_ne hk]
    exact mul_self_eq_one_of_mem_longInv (D'.rho_mem_longInv hwJ k)
  have hρm : D'.ρ m (wH * cH) = σ := by rw [map_mul, hρc m, Function.update_self]
  have hσ2 : σ * σ = 1 := by
    have hcomm := C.rho_w_commute D' hS hw hwv m
    have hxx : D'.ρ m xH * D'.ρ m xH = 1 := by
      rw [← map_mul, show xH * xH = 1 from Subtype.ext C.vHat_mul_vHat, map_one]
    calc σ * σ = D'.ρ m wH * (D'.ρ m xH * D'.ρ m wH) * D'.ρ m xH := by rw [hσ]; group
      _ = D'.ρ m wH * (D'.ρ m wH * D'.ρ m xH) * D'.ρ m xH := by rw [hcomm]
      _ = (D'.ρ m wH * D'.ρ m wH) * (D'.ρ m xH * D'.ρ m xH) := by group
      _ = 1 := by rw [hww, hxx, one_mul]
  have hprod : xH = wH * uH := Subtype.ext (Subtype.ext (Equiv.ext fun δ => Subtype.ext (by
    show v • (δ : Ω) = w • (w * v) • (δ : Ω)
    rw [smul_smul, ← mul_assoc, mul_self_eq_one_of_mem_longInv hw.1, one_mul])))
  have hσ1 : σ ≠ 1 := by
    intro h
    have hxu : D'.ρ m xH = D'.ρ m wH * D'.ρ m uH := by rw [hprod, map_mul]
    have hxw : D'.ρ m xH = D'.ρ m wH := by
      calc D'.ρ m xH = D'.ρ m wH * (D'.ρ m wH * D'.ρ m xH) := by rw [← mul_assoc, hww, one_mul]
        _ = D'.ρ m wH := by rw [← hσ, h, mul_one]
    rw [hxw] at hxu
    have h1 : D'.ρ m uH = 1 := mul_left_cancel (hxu.symm.trans (mul_one _).symm)
    have := (D'.rho_mem_longInv huJ m).1
    rw [h1, orderOf_one] at this
    omega
  have hwX := closure_longInvSwap_le_stabilizer_pair α C.β (Subgroup.subset_closure hw)
  have hcX := closure_longInvSwap_le_stabilizer_pair α C.β (Subgroup.subset_closure hc)
  obtain ⟨k₂, m₀, hm₀, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (w * c)).ne'
  set u := (w * c) ^ m₀ with hu
  have hu2 : u ^ 2 ^ k₂ = 1 := by rw [hu, ← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one]
  set EH := (wH * cH) ^ m₀ with hEH
  have huE : ∀ δ : holtDelta G Ω α C.β, u • (δ : Ω) =
      (((EH : twoPointSection G Ω α C.β) • δ : holtDelta G Ω α C.β) : Ω) := fun δ => by
    rw [hEH, Subgroup.coe_pow, Subgroup.coe_mul]
    exact (coe_mul_pow_smul_twoPointElt hcX hwX m₀ δ).symm
  have hEn : ∀ (n : ℕ) (δ : holtDelta G Ω α C.β),
      (((EH : twoPointSection G Ω α C.β) ^ n • δ : holtDelta G Ω α C.β) : Ω) = u ^ n • (δ : Ω) := by
    intro n
    induction n with
    | zero => intro δ; rw [pow_zero, pow_zero, one_smul, one_smul]
    | succ n ih =>
      intro δ
      rw [pow_succ' (EH : twoPointSection G Ω α C.β), mul_smul, pow_succ' u, mul_smul, ← huE, ih]
  have hEl : D'.ρ m EH = σ := by
    rw [hEH, map_pow, hρm]
    obtain ⟨t, rfl⟩ := hm₀
    rw [pow_succ, pow_mul, sq, hσ2, one_pow, one_mul]
  have hEk : ∀ k, k ≠ m → D'.ρ k EH = 1 := fun k hk => by rw [hEH, map_pow, hρk k hk, one_pow]
  have hES : (EH : twoPointSection G Ω α C.β) ∈ D'.socPre := by
    rw [hEH, Subgroup.coe_pow]
    exact pow_mem (hS.mul_mem_socPre_twoPointSection h3 D' hwJ hcJ) m₀
  have hE2O : ((EH : twoPointSection G Ω α C.β)) ^ 2 ∈
      jOddCore (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β) := by
    rw [← D'.socPre_inf_jOrbitKernel]
    refine ⟨pow_mem hES 2, ?_⟩
    have h := (D'.mem_jOrbitKernel_iff_rho (h := EH ^ 2)).mpr fun k => by
      rw [map_pow]
      rcases eq_or_ne k m with rfl | hk
      · rw [hEl, sq, hσ2]
      · rw [hEk k hk, one_pow]
    exact h
  have hEpow : (EH : twoPointSection G Ω α C.β) ^ 2 ^ k₂ = 1 :=
    Subtype.ext (Equiv.ext fun δ => Subtype.ext (by
      show (((EH : twoPointSection G Ω α C.β) ^ 2 ^ k₂ • δ : holtDelta G Ω α C.β) : Ω) = δ
      rw [hEn, hu2, one_smul]))
  have hE22 : ((EH : twoPointSection G Ω α C.β) ^ 2) ^ 2 ^ k₂ = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hEpow, one_pow]
  have hE1 : ((EH : twoPointSection G Ω α C.β)) ^ 2 = 1 := by
    have hodd : Odd (orderOf ((EH : twoPointSection G Ω α C.β) ^ 2)) :=
      Odd.of_dvd_nat odd_card_jOddCore (Subgroup.orderOf_dvd_natCard _ hE2O)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hE22)
    rw [hj] at hodd
    rcases j with _ | j
    · exact orderOf_eq_one_iff.mp (by rw [hj, pow_zero])
    · exact absurd hodd (Nat.not_odd_iff_even.mpr
        (Nat.even_pow.mpr ⟨even_two, Nat.succ_ne_zero j⟩))
  have hEne : (EH : twoPointSection G Ω α C.β) ≠ 1 := fun h => hσ1 (by
    rw [← hEl, show EH = 1 from Subtype.ext h, map_one])
  have hE2 : orderOf (EH : twoPointSection G Ω α C.β) = 2 := orderOf_eq_prime hE1 hEne
  have hiff : ∀ δ : holtDelta G Ω α C.β,
      u • (δ : Ω) = δ ↔ σ (D'.coord δ m) = D'.coord δ m := by
    intro δ
    rw [huE]
    constructor
    · intro h
      have h' : (EH : twoPointSection G Ω α C.β) • δ = δ := Subtype.ext h
      rw [← hEl, ← D'.coord_smul, h']
    · intro h
      have hc' : D'.coord δ = D'.coord ((EH : twoPointSection G Ω α C.β) • δ) :=
        funext fun k => by
          rw [D'.coord_smul EH δ k]
          rcases eq_or_ne k m with rfl | hk
          · rw [hEl, h]
          · rw [hEk k hk, Perm.one_apply]
      exact congrArg Subtype.val ((hS.lemma_2_4_iv_twoPointSection h3 D' EH.2 hE2
        ((D'.coord_eq_iff _ _).mp hc')).1 hES δ (mem_orbit_self δ))
  have hB : ∀ δ : holtDelta G Ω α C.β, (δ : Ω) ∈ fixSet Ω (Subgroup.zpowers v) →
      σ (D'.coord δ m) = D'.coord δ m := by
    intro δ hδ
    have hv := (C.mem_fixSet_iff_rho hS D' δ).mp hδ m
    obtain ⟨γ, hγw, hγv⟩ := C.exists_fixed_w D' hS hw hwv m
    obtain ⟨z₀, -, hz₀u⟩ := C.existsUnique_fixed_of_isNaturalSE D' hS hw hwv hm
    have h1 : D'.coord δ m = γ := (hz₀u _ hv).trans (hz₀u _ hγv).symm
    rw [hσ, Perm.mul_apply, hv, h1]
    exact (hγw γ).mpr rfl
  have hu1 : u ≠ 1 := by
    intro h
    apply hσ1
    refine Equiv.ext fun ψ => ?_
    obtain ⟨δ, hδ⟩ := D'.exists_coord_apply_eq m ψ
    rw [← hδ, Perm.one_apply]
    exact (hiff δ).mp (by rw [h, one_smul])
  have hx₁v : w * c * v = v * (w * c) := by rw [mul_assoc, hcv, ← mul_assoc, hwv, mul_assoc]
  have hx₁α : (w * c) • α = α := by rw [mul_smul, hc.2, smul_eq_of_mem_longInvSwap hw]
  have hx₁β : (w * c) • C.β = C.β := by rw [mul_smul, smul_eq_of_mem_longInvSwap hc, hw.2]
  refine ⟨u, (Commute.pow_left hx₁v m₀).eq, ?_, ?_, ?_, hu1, σ, hiff, hB⟩
  · rw [hu, ← mem_stabilizer_iff]
    exact pow_mem (mem_stabilizer_iff.mpr hx₁α) m₀
  · rw [hu, ← mem_stabilizer_iff]
    exact pow_mem (mem_stabilizer_iff.mpr hx₁β) m₀
  · obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hu2)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])

theorem false_of_twoGroup (hS : Sec4Setting G Ω)
    (D' : HoltData (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β))
    (hB : ∀ γ : holtDelta G Ω α C.β, (γ : Ω) ∈ fixSet Ω (Subgroup.zpowers v) →
      ∀ γ' : holtDelta G Ω α C.β, γ' ∈ orbit (jOddCore (twoPointSection G Ω α C.β)
        (holtDelta G Ω α C.β)) γ ↔ (γ' : Ω) ∈ fixSet Ω (Subgroup.zpowers v))
    {l : D'.ι} (hl : IsNaturalSE (D'.M l)) {U : Subgroup G} (hU : IsPGroup 2 U) (hU1 : U ≠ ⊥)
    (hUv : ∀ u ∈ U, u * v = v * u) (hUαβ : U ≤ stabilizer G α ⊓ stabilizer G C.β)
    (hline : ∀ δ δ' : holtDelta G Ω α C.β, (δ : Ω) ∈ fixSet Ω U →
      (∀ j, j ≠ l → D'.coord δ' j = D'.coord δ j) → (δ' : Ω) ∈ fixSet Ω U)
    (hUB : ∀ δ : holtDelta G Ω α C.β, (δ : Ω) ∈ fixSet Ω (Subgroup.zpowers v) →
      (δ : Ω) ∈ fixSet Ω U) : False := by
  obtain ⟨g, hg, δ, δ', hδ, hδ', hgα, hgβ⟩ := exists_mem_closure_smul_mem_B C hS hU hUv hUαβ hUB
  have hll : D'.coord δ l = D'.coord δ' l := by
    rw [(D'.coord_eq_iff δ δ').mpr ((hB δ hδ δ').mpr hδ')]
  exact false_of_mem_closure_smul_eq hS C.ne D' hl hU hU1 hUαβ hline hg δ δ' (hUB δ hδ)
    (hUB δ' hδ') hgα hgβ hll

end Lemma54

end P49S7

section Main

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω]

theorem Sec4Setting.p49Step97b (hS : Sec4Setting G Ω) : P49Step97b G Ω := by
  intro α v C D' hne hSE hB _
  obtain ⟨l⟩ := hne
  have hT : Odd (Nat.card (twoPointKernel G Ω α C.β)) := by
    by_contra hT
    obtain ⟨x, hxK, hxv, hx2⟩ := P49S7.exists_involution_twoPointKernel C hS hT
    obtain ⟨hxα, hxβ, hxΔ⟩ := mem_twoPointKernel.mp hxK
    have hU1 : Subgroup.zpowers x ≠ ⊥ := by
      rw [Ne, Subgroup.zpowers_eq_bot]
      rintro rfl
      rw [orderOf_one] at hx2
      omega
    have hfix : ∀ δ : holtDelta G Ω α C.β, (δ : Ω) ∈ fixSet Ω (Subgroup.zpowers x) := fun δ =>
      mem_fixSet_zpowers_iff.mpr (hxΔ δ δ.2)
    exact P49S7.false_of_twoGroup C hS D' hB (hSE l) (isPGroup_zpowers_of_orderOf_eq_two hx2) hU1
      (fun u hu => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
        exact (Commute.zpow_left hxv k).eq)
      (Subgroup.zpowers_le.mpr ⟨hxα, hxβ⟩) (fun _ δ' _ _ => hfix δ') fun δ _ => hfix δ
  refine ⟨?_, hT⟩
  by_contra hs
  push Not at hs
  obtain ⟨m, hml⟩ := Fintype.exists_ne_of_one_lt_card hs l
  obtain ⟨u, huv, huα, huβ, hU, hu1, σ, hiff, hσB⟩ :=
    P49S7.exists_twoElement_of_odd C hS D' hT (hSE m)
  have hU1 : Subgroup.zpowers u ≠ ⊥ := by
    rw [Ne, Subgroup.zpowers_eq_bot]
    exact hu1
  refine P49S7.false_of_twoGroup C hS D' hB (hSE l) hU hU1 (fun u' hu' => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu'
      exact (Commute.zpow_left huv k).eq)
    (Subgroup.zpowers_le.mpr ⟨huα, huβ⟩) (fun δ δ' hδ hδ' => ?_) fun δ hδ =>
      mem_fixSet_zpowers_iff.mpr ((hiff δ).mpr (hσB δ hδ))
  rw [mem_fixSet_zpowers_iff, hiff] at hδ ⊢
  rw [hδ' m hml]
  exact hδ

end Main

end CFSG.Holt.H78
