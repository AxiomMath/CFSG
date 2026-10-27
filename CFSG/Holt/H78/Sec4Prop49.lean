module

public import CFSG.Holt.H78.Sec4Toolkit
public import CFSG.Holt.H78.Lemma27Real
public import CFSG.Holt.H78.Lemma27SE
import CFSG.Holt.H78.SEModelFive
import CFSG.Holt.H78.Sec4KnownKV

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General CFSG.Open
open scoped Pointwise

theorem mem_fixSet_zpowers_iff {G Ω : Type*} [Group G] [MulAction G Ω] {v : G} {ω : Ω} :
    ω ∈ fixSet Ω (Subgroup.zpowers v) ↔ v • ω = ω := by
  rw [fixSet_zpowers, mem_fixedBy]

theorem mem_centralizer_zpowers_iff {G : Type*} [Group G] {v c : G} :
    c ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) ↔ c * v = v * c := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    exact (h v (Subgroup.mem_zpowers v)).symm
  · intro h g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact (Commute.zpow_left (Commute.symm h) k).eq

section Config

variable (G : Type) [Group G] (Ω : Type) [MulAction G Ω]

structure P49Config (α : Ω) (v : G) where
  isTypeL : IsTypeL G Ω α v
  D : HoltData (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v))
  pPrimeCore_eq_bot : CFSG.pPrimeCore 2 (typeLSection G Ω v) = ⊥
  isNaturalSE : ∀ k, IsNaturalSE (D.M k)
  i : D.ι
  a : fixSet Ω (Subgroup.zpowers v)
  b : fixSet Ω (Subgroup.zpowers v)
  coe_a : (a : Ω) = α
  coord_ne : D.coord a i ≠ D.coord b i
  coord_eq : ∀ j, j ≠ i → D.coord a j = D.coord b j

end Config

namespace P49Config

section Basic

variable {G : Type} [Group G] {Ω : Type} [MulAction G Ω] {α : Ω} {v : G}
  (C : P49Config G Ω α v)

include C

abbrev β : Ω := (C.b : Ω)

theorem a_ne_b : C.a ≠ C.b := fun h => C.coord_ne (by rw [h])

theorem ne : α ≠ C.β := fun h => C.a_ne_b (Subtype.ext (C.coe_a.trans h))

theorem v_smul_α : v • α = α := C.isTypeL.smul_eq

theorem v_smul_β : v • C.β = C.β := mem_fixSet_zpowers_iff.mp C.b.2

theorem v_mul_v : v * v = 1 := by
  rw [← sq, ← C.isTypeL.orderOf_eq_two, pow_orderOf_eq_one]

theorem isPGroup_zpowers : IsPGroup 2 (Subgroup.zpowers v) :=
  isPGroup_zpowers_of_orderOf_eq_two C.isTypeL.orderOf_eq_two

theorem v_mem_stabilizer_pair : v ∈ stabilizer G ({α, C.β} : Set Ω) :=
  stabilizer_inf_le_stabilizer_pair α C.β
    (Subgroup.mem_inf.mpr ⟨mem_stabilizer_iff.mpr C.v_smul_α, mem_stabilizer_iff.mpr C.v_smul_β⟩)

end Basic

section Coord

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α : Ω} {v : G} (C : P49Config G Ω α v)

include C

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem holtDelta_eq : holtDelta G Ω α C.β = holtDelta G Ω (C.a : Ω) (C.b : Ω) :=
  congrArg (fun x => holtDelta G Ω x C.β) C.coe_a.symm

omit [Finite G] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem jOddCore_eq_bot :
    jOddCore (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)) = ⊥ :=
  le_bot_iff.mp (by rw [← C.pPrimeCore_eq_bot]; exact jOddCore_le_pPrimeCore)

omit [Finite G] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem coord_injective : Function.Injective C.D.coord :=
  C.D.coord_injective C.jOddCore_eq_bot

omit [Finite G] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem smul_eq_iff_rho
    (h : jHull (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)))
    (δ : fixSet Ω (Subgroup.zpowers v)) :
    (h : typeLSection G Ω v) • δ = δ ↔ ∀ j, C.D.ρ j h (C.D.coord δ j) = C.D.coord δ j := by
  constructor
  · intro h1 j
    rw [← C.D.coord_smul, h1]
  · intro h1
    exact C.coord_injective (funext fun j => by rw [C.D.coord_smul, h1 j])

theorem mem_holtDelta_iff (hS : Sec4Setting G Ω) (δ : fixSet Ω (Subgroup.zpowers v)) :
    (δ : Ω) ∈ holtDelta G Ω α C.β ↔
      (∀ j, j ≠ C.i → C.D.coord δ j = C.D.coord C.a j) ∧
        C.D.coord δ C.i ∈ holtDelta (C.D.M C.i) (C.D.Ψc C.i) (C.D.coord C.a C.i)
          (C.D.coord C.b C.i) := by
  have hV := C.isPGroup_zpowers
  have h3 := three_le_card_fixSet_of_isTypeL hS.star C.isTypeL
  rw [C.holtDelta_eq, ← hS.mem_holtDelta_centralizerImage_iff hV h3 C.a_ne_b]
  constructor
  · rintro ⟨π, hπ, hπδ⟩
    set πH : jHull (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)) :=
      ⟨π, mem_jHull_of_mem_longInv hπ.1⟩
    have hρ : ∀ j, C.D.ρ j πH (C.D.coord C.a j) = C.D.coord C.b j := fun j => by
      rw [← C.D.coord_smul]
      exact congrArg (fun x => C.D.coord x j) hπ.2
    have hfix : ∀ j, C.D.ρ j πH (C.D.coord δ j) = C.D.coord δ j := fun j => by
      rw [← C.D.coord_smul]
      exact congrArg (fun x => C.D.coord x j) hπδ
    have hJ : ∀ j, C.D.ρ j πH ∈ longInv (Equiv.Perm (C.D.Ψc j)) (C.D.Ψc j) :=
      fun j => C.D.rho_mem_longInv hπ.1 j
    refine ⟨fun j hj => ?_, ?_⟩
    · obtain ⟨-, x, -, huniq⟩ := hJ j
      have ha : C.D.ρ j πH (C.D.coord C.a j) = C.D.coord C.a j :=
        (hρ j).trans (C.coord_eq j hj).symm
      exact (huniq _ (hfix j)).trans (huniq _ ha).symm
    · refine ⟨⟨C.D.ρ C.i πH, C.D.rho_mem_M_of_isNaturalSE (C.isNaturalSE C.i) πH⟩,
        ⟨mem_longInv_subgroup_iff.mpr (hJ C.i), hρ C.i⟩, hfix C.i⟩
  · rintro ⟨hline, y, hy, hyδ⟩
    obtain ⟨t₀, ht₀⟩ := C.D.longInvAt_nonempty C.a
    set t₀H : jHull (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)) :=
      ⟨t₀, mem_jHull_of_mem_longInv ht₀.1⟩
    set Y : ∀ j, Equiv.Perm (C.D.Ψc j) :=
      Function.update (fun j => C.D.ρ j t₀H) C.i (y : Equiv.Perm (C.D.Ψc C.i)) with hY
    have ht₀a : ∀ j, C.D.ρ j t₀H (C.D.coord C.a j) = C.D.coord C.a j := fun j => by
      rw [← C.D.coord_smul]
      exact congrArg (fun x => C.D.coord x j) ht₀.2
    have hYrange : ∀ j, Y j ∈ (C.D.ρ j).range := fun j => by
      rcases eq_or_ne j C.i with rfl | hj
      · rw [hY, Function.update_self,
          C.D.range_rho_of_not_isOuterFactor (C.isNaturalSE _).not_isOuterFactor]
        exact y.2
      · rw [hY, Function.update_of_ne hj]
        exact ⟨t₀H, rfl⟩
    have hYJ : ∀ j, Y j ∈ longInv (Equiv.Perm (C.D.Ψc j)) (C.D.Ψc j) := fun j => by
      rcases eq_or_ne j C.i with rfl | hj
      · rw [hY, Function.update_self]
        exact mem_longInv_subgroup_iff.mp hy.1
      · rw [hY, Function.update_of_ne hj]
        exact C.D.rho_mem_longInv ht₀.1 j
    have hYab : ∀ j, Y j (C.D.coord C.a j) = C.D.coord C.b j := fun j => by
      rcases eq_or_ne j C.i with rfl | hj
      · rw [hY, Function.update_self]
        exact hy.2
      · rw [hY, Function.update_of_ne hj, ht₀a j, C.coord_eq j hj]
    obtain ⟨u, hu, hρu⟩ := C.D.exists_mem_longInvSwap_rho_eq Y hYrange hYJ hYab
    refine ⟨u, hu, (C.smul_eq_iff_rho u δ).mpr fun j => ?_⟩
    rw [hρu j]
    rcases eq_or_ne j C.i with rfl | hj
    · rw [hY, Function.update_self]
      exact hyδ
    · rw [hY, Function.update_of_ne hj, hline j hj, ht₀a j]

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem three_le_ncard_holtDelta_M :
    3 ≤ (holtDelta (C.D.M C.i) (C.D.Ψc C.i) (C.D.coord C.a C.i) (C.D.coord C.b C.i)).ncard := by
  obtain ⟨n, k, e, hA⟩ := IsNaturalSE.exists_isBenderAction (C.isNaturalSE C.i)
  rw [hA.ncard_holtDelta C.coord_ne]
  have := hA.four_le_q
  omega

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem exists_coord_eq_update (x : C.D.Ψc C.i) :
    ∃ δ : fixSet Ω (Subgroup.zpowers v), C.D.coord δ = Function.update (C.D.coord C.a) C.i x :=
  C.D.coord_surjective _

theorem exists_mem_holtDelta_ne (hS : Sec4Setting G Ω) :
    ∃ δ δ' : fixSet Ω (Subgroup.zpowers v), (δ : Ω) ∈ holtDelta G Ω α C.β ∧
      (δ' : Ω) ∈ holtDelta G Ω α C.β ∧ δ ≠ δ' := by
  have h3 := C.three_le_ncard_holtDelta_M
  have h0 : (holtDelta (C.D.M C.i) (C.D.Ψc C.i) (C.D.coord C.a C.i)
      (C.D.coord C.b C.i)).ncard ≠ 0 := by omega
  have h1 : 1 < (holtDelta (C.D.M C.i) (C.D.Ψc C.i) (C.D.coord C.a C.i)
      (C.D.coord C.b C.i)).ncard := by omega
  obtain ⟨x, hx⟩ := Set.nonempty_of_ncard_ne_zero h0
  obtain ⟨x', hx', hxx'⟩ := Set.exists_ne_of_one_lt_ncard h1 x
  obtain ⟨δ, hδ⟩ := C.exists_coord_eq_update x
  obtain ⟨δ', hδ'⟩ := C.exists_coord_eq_update x'
  have hmem : ∀ (y : C.D.Ψc C.i) (ε : fixSet Ω (Subgroup.zpowers v)),
      y ∈ holtDelta (C.D.M C.i) (C.D.Ψc C.i) (C.D.coord C.a C.i) (C.D.coord C.b C.i) →
      C.D.coord ε = Function.update (C.D.coord C.a) C.i y → (ε : Ω) ∈ holtDelta G Ω α C.β :=
    fun y ε hy hε => (C.mem_holtDelta_iff hS ε).mpr
      ⟨fun j hj => by rw [hε, Function.update_of_ne hj], by rw [hε, Function.update_self]; exact hy⟩
  refine ⟨δ, δ', hmem x δ hx hδ, hmem x' δ' hx' hδ', fun h => hxx' ?_⟩
  have h1 : C.D.coord δ C.i = C.D.coord δ' C.i := by rw [h]
  rw [hδ, hδ', Function.update_self, Function.update_self] at h1
  exact h1.symm

theorem three_le_card_holtDelta (hS : Sec4Setting G Ω) : 3 ≤ Nat.card (holtDelta G Ω α C.β) := by
  obtain ⟨δ, δ', hδ, hδ', hne⟩ := C.exists_mem_holtDelta_ne hS
  have hodd := hS.star.odd_card_holtDelta α C.β
  have h2 : 1 < Nat.card (holtDelta G Ω α C.β) := by
    rw [Nat.card_coe_set_eq]
    exact (Set.one_lt_ncard_iff (Set.toFinite _)).mpr
      ⟨δ, δ', hδ, hδ', fun h => hne (Subtype.ext h)⟩
  obtain ⟨m, hm⟩ := hodd
  omega

theorem exists_mem_longInvSwap_mul (hS : Sec4Setting G Ω) :
    ∃ w ∈ longInvSwap G Ω α C.β, w * v = v * w ∧ w * v ∈ longInvSwap G Ω α C.β := by
  obtain ⟨t, ht, u, hu, -, htu, htuv, -⟩ := C.isTypeL
  have htv : t * v = v * t := by
    calc t * v = t * (t * u) := by rw [htuv]
      _ = t * (u * t) := by rw [htu.eq]
      _ = v * t := by rw [← mul_assoc, htuv]
  have htt : t * v = u := by
    rw [← htuv, ← mul_assoc, mul_self_eq_one_of_mem_longInv ht.1, one_mul]
  have htC : t ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) :=
    mem_centralizer_zpowers_iff.mpr htv
  have hV := C.isPGroup_zpowers
  have h3 := three_le_card_fixSet_of_isTypeL hS.star C.isTypeL
  have hK := hS.star_typeLSection C.isTypeL
  have htK : centralizerImageElt (Ω := Ω) htC ∈
      longInv (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)) :=
    (hS.mem_longInv_centralizerImage_iff hV h3 _).mpr ⟨t, ht.1, htC, fun _ => rfl⟩
  obtain ⟨π, hπ⟩ := longInvSwap_nonempty hK C.a C.b
  obtain ⟨h, -, hconj⟩ := exists_mem_jHull_conj_eq hK
    (hS.holtTheorem1Below_typeLSection C.isTypeL) htK hπ.1
  obtain ⟨c, hc, hch⟩ := mem_centralizerImage.mp h.2
  have hcv : c * v = v * c := mem_centralizer_zpowers_iff.mp hc
  have hcv' : c⁻¹ * v = v * c⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hcv, mul_inv_cancel_right]
  have hch' : ∀ ω : fixSet Ω (Subgroup.zpowers v),
      (((h⁻¹ : typeLSection G Ω v) : Equiv.Perm (fixSet Ω (Subgroup.zpowers v))) ω : Ω) =
        c⁻¹ • (ω : Ω) := fun ω => by
    rw [eq_inv_smul_iff, ← hch]
    simp
  have hw : (c * t * c⁻¹) • α = C.β := by
    have e1 := congrArg (fun g : typeLSection G Ω v =>
      ((g : Equiv.Perm (fixSet Ω (Subgroup.zpowers v))) C.a : Ω)) hconj
    simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply] at e1
    rw [show ((π : Equiv.Perm (fixSet Ω (Subgroup.zpowers v))) C.a : Ω) = C.β from
      congrArg Subtype.val hπ.2] at e1
    rw [← e1, hch, coe_centralizerImageElt_apply, hch', C.coe_a, mul_smul, mul_smul]
  have hwv : c * t * c⁻¹ * v = c * (t * v) * c⁻¹ := by
    rw [mul_assoc (c * t), hcv', ← mul_assoc, mul_assoc c]
  refine ⟨c * t * c⁻¹, ⟨conj_mem_longInv ht.1 c, hw⟩, ?_, ⟨?_, ?_⟩⟩
  · rw [hwv, htv, ← mul_assoc, hcv, mul_assoc v, mul_assoc v]
  · rw [hwv, htt]
    exact conj_mem_longInv hu.1 c
  · rw [mul_smul, C.v_smul_α, hw]

abbrev vHat : twoPointSection G Ω α C.β := twoPointElt C.v_mem_stabilizer_pair

theorem vHat_mem_jHull (hS : Sec4Setting G Ω) :
    C.vHat ∈ jHull (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β) := by
  obtain ⟨w, hw, -, hwv⟩ := C.exists_mem_longInvSwap_mul hS
  have hv : v ∈ Subgroup.closure (longInvSwap G Ω α C.β) := by
    have e : w * (w * v) = v := by
      rw [← mul_assoc, mul_self_eq_one_of_mem_longInv hw.1, one_mul]
    have h := mul_mem (Subgroup.subset_closure hw) (Subgroup.subset_closure hwv)
    rw [e] at h
    exact h
  exact twoPointElt_mem_jHull hS.star hv

theorem vHat_mem_socPre (hS : Sec4Setting G Ω)
    (D' : HoltData (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β)) :
    (C.vHat : twoPointSection G Ω α C.β) ∈ D'.socPre := by
  obtain ⟨w, hw, -, hwv⟩ := C.exists_mem_longInvSwap_mul hS
  have h3 := C.three_le_card_holtDelta hS
  have hwX := closure_longInvSwap_le_stabilizer_pair α C.β (Subgroup.subset_closure hw)
  have hwvX := closure_longInvSwap_le_stabilizer_pair α C.β (Subgroup.subset_closure hwv)
  have hŵ : twoPointElt hwX ∈ longInv (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β) :=
    (hS.mem_longInv_twoPointSection_iff C.ne h3 _).mpr ⟨w, hw, fun _ => rfl⟩
  have hŵ' : twoPointElt hwvX ∈ longInv (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β) :=
    (hS.mem_longInv_twoPointSection_iff C.ne h3 _).mpr ⟨w * v, hwv, fun _ => rfl⟩
  have e : C.vHat = twoPointElt hwX * twoPointElt hwvX := by
    refine Subtype.ext (Equiv.ext fun δ => Subtype.ext ?_)
    show v • (δ : Ω) = w • ((w * v) • (δ : Ω))
    rw [← mul_smul, ← mul_assoc, mul_self_eq_one_of_mem_longInv hw.1, one_mul]
  rw [e]
  exact D'.mul_mem_socPre_of_mem_longInv (hS.star_twoPoint C.ne h3)
    (hS.holtTheorem1Below_twoPoint h3) hŵ hŵ'

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem vHat_mul_vHat : C.vHat * C.vHat = 1 :=
  Subtype.ext (Equiv.ext fun δ => Subtype.ext (by
    show v • v • (δ : Ω) = (δ : Ω)
    rw [← mul_smul, C.v_mul_v, one_smul]))

theorem mem_fixSet_iff_rho (hS : Sec4Setting G Ω)
    (D' : HoltData (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β))
    (δ : holtDelta G Ω α C.β) :
    (δ : Ω) ∈ fixSet Ω (Subgroup.zpowers v) ↔
      ∀ j, D'.ρ j ⟨C.vHat, C.vHat_mem_jHull hS⟩ (D'.coord δ j) = D'.coord δ j := by
  constructor
  · intro hδ j
    have h1 : v • (δ : Ω) = δ := mem_fixSet_zpowers_iff.mp hδ
    have hxδ : C.vHat • δ = δ := Subtype.ext h1
    rw [← D'.coord_smul]
    exact congrArg (fun ε => D'.coord ε j) hxδ
  · intro h
    have hc : D'.coord δ = D'.coord (C.vHat • δ) := funext fun j => by
      rw [show C.vHat • δ = ((⟨C.vHat, C.vHat_mem_jHull hS⟩ :
        jHull (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β)) : twoPointSection G Ω α C.β) • δ
        from rfl, D'.coord_smul, h j]
    have horb := (D'.coord_eq_iff δ _).mp hc
    suffices hfix : C.vHat • δ = δ from
      mem_fixSet_zpowers_iff.mpr (congrArg Subtype.val hfix)
    by_cases h1 : C.vHat = 1
    · rw [h1, one_smul]
    · have h3 := C.three_le_card_holtDelta hS
      have h2 : orderOf C.vHat = 2 := orderOf_eq_prime (by rw [sq]; exact C.vHat_mul_vHat) h1
      exact (hS.lemma_2_4_iv_twoPointSection h3 D' (C.vHat_mem_jHull hS) h2 horb).1
        (C.vHat_mem_socPre hS D') δ (mem_orbit_self δ)

def lineSubgroup : Subgroup (jHull (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v))) :=
  ⨅ (j : C.D.ι) (_ : j ≠ C.i),
    (stabilizer (Equiv.Perm (C.D.Ψc j)) (C.D.coord C.a j)).comap (C.D.ρ j)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem mem_lineSubgroup {π : jHull (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v))} :
    π ∈ C.lineSubgroup ↔ ∀ j, j ≠ C.i → C.D.ρ j π (C.D.coord C.a j) = C.D.coord C.a j := by
  simp only [lineSubgroup, Subgroup.mem_iInf, Subgroup.mem_comap, mem_stabilizer_iff,
    Equiv.Perm.smul_def]

omit [Finite G] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem smul_eq_of_mem_lineSubgroup
    {π π' : jHull (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v))}
    (hπ : π ∈ C.lineSubgroup) (hπ' : π' ∈ C.lineSubgroup) (hρ : C.D.ρ C.i π = C.D.ρ C.i π')
    {δ : fixSet Ω (Subgroup.zpowers v)} (hδ : ∀ j, j ≠ C.i → C.D.coord δ j = C.D.coord C.a j) :
    (π : typeLSection G Ω v) • δ = (π' : typeLSection G Ω v) • δ := by
  refine C.coord_injective (funext fun j => ?_)
  rw [C.D.coord_smul, C.D.coord_smul]
  rcases eq_or_ne j C.i with rfl | hj
  · rw [hρ]
  · rw [hδ j hj, C.mem_lineSubgroup.mp hπ j hj, C.mem_lineSubgroup.mp hπ' j hj]

theorem centralizerImageElt_mem_jHull (hS : Sec4Setting G Ω) {c : G} (hcJ : c ∈ longInv G Ω)
    (hc : c ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)) :
    centralizerImageElt (Ω := Ω) hc ∈
      jHull (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)) :=
  mem_jHull_of_mem_longInv ((hS.mem_longInv_centralizerImage_iff C.isPGroup_zpowers
    (three_le_card_fixSet_of_isTypeL hS.star C.isTypeL) _).mpr ⟨c, hcJ, hc, fun _ => rfl⟩)

theorem rho_centralizerImageElt_coord_a (hS : Sec4Setting G Ω) {c : G}
    (hcJ : c ∈ longInvSwap G Ω α C.β)
    (hc : c ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)) (j : C.D.ι) :
    C.D.ρ j ⟨_, C.centralizerImageElt_mem_jHull hS hcJ.1 hc⟩ (C.D.coord C.a j) =
      C.D.coord C.b j := by
  rw [← C.D.coord_smul]
  congr 1
  exact Subtype.ext (by
    show c • (C.a : Ω) = C.b
    rw [C.coe_a]
    exact hcJ.2)

theorem rho_centralizerImageElt_coord_b (hS : Sec4Setting G Ω) {c : G}
    (hcJ : c ∈ longInvSwap G Ω α C.β)
    (hc : c ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)) (j : C.D.ι) :
    C.D.ρ j ⟨_, C.centralizerImageElt_mem_jHull hS hcJ.1 hc⟩ (C.D.coord C.b j) =
      C.D.coord C.a j := by
  rw [← C.rho_centralizerImageElt_coord_a hS hcJ hc j, ← Equiv.Perm.mul_apply, ← map_mul]
  have h2 : (⟨_, C.centralizerImageElt_mem_jHull hS hcJ.1 hc⟩ :
      jHull (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v))) *
        ⟨_, C.centralizerImageElt_mem_jHull hS hcJ.1 hc⟩ = 1 :=
    Subtype.ext (Subtype.ext (Equiv.ext fun ω => Subtype.ext (by
      show c • c • (ω : Ω) = ω
      rw [← mul_smul, mul_self_eq_one_of_mem_longInv hcJ.1, one_smul])))
  rw [h2, map_one, Equiv.Perm.one_apply]

abbrev pairElt (hS : Sec4Setting G Ω) {c c' : G} (hcJ : c ∈ longInv G Ω)
    (hc : c ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G))
    (hc'J : c' ∈ longInv G Ω)
    (hc' : c' ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)) :
    jHull (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)) :=
  ⟨_, C.centralizerImageElt_mem_jHull hS hcJ hc⟩ * ⟨_, C.centralizerImageElt_mem_jHull hS hc'J hc'⟩

theorem pairElt_mem (hS : Sec4Setting G Ω) {c c' : G} (hcJ : c ∈ longInvSwap G Ω α C.β)
    (hc : c ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G))
    (hc'J : c' ∈ longInvSwap G Ω α C.β)
    (hc' : c' ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)) :
    C.pairElt hS hcJ.1 hc hc'J.1 hc' ∈ C.lineSubgroup ∧
      C.D.ρ C.i (C.pairElt hS hcJ.1 hc hc'J.1 hc') ∈ C.D.M C.i ∧
      C.D.ρ C.i (C.pairElt hS hcJ.1 hc hc'J.1 hc') (C.D.coord C.a C.i) = C.D.coord C.a C.i ∧
      C.D.ρ C.i (C.pairElt hS hcJ.1 hc hc'J.1 hc') (C.D.coord C.b C.i) = C.D.coord C.b C.i := by
  have ha := C.rho_centralizerImageElt_coord_a hS hcJ hc
  have hb := C.rho_centralizerImageElt_coord_b hS hcJ hc
  have ha' := C.rho_centralizerImageElt_coord_a hS hc'J hc'
  have hb' := C.rho_centralizerImageElt_coord_b hS hc'J hc'
  refine ⟨C.mem_lineSubgroup.mpr fun j hj => ?_,
    C.D.rho_mem_M_of_isNaturalSE (C.isNaturalSE C.i) _, ?_, ?_⟩
  · rw [map_mul, Equiv.Perm.mul_apply, ha' j, ← C.coord_eq j hj, ha j, C.coord_eq j hj]
  · rw [map_mul, Equiv.Perm.mul_apply, ha', hb]
  · rw [map_mul, Equiv.Perm.mul_apply, hb', ha]

theorem coe_pairElt_smul (hS : Sec4Setting G Ω) {c c' : G} (hcJ : c ∈ longInv G Ω)
    (hc : c ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G))
    (hc'J : c' ∈ longInv G Ω)
    (hc' : c' ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G))
    (δ : fixSet Ω (Subgroup.zpowers v)) :
    (((C.pairElt hS hcJ hc hc'J hc' : typeLSection G Ω v) • δ : fixSet Ω _) : Ω) =
      (c * c') • (δ : Ω) := by
  rw [mul_smul]
  rfl

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem isCyclic_cartan :
    IsCyclic ↥(stabilizer (C.D.M C.i) (C.D.coord C.a C.i) ⊓
      stabilizer (C.D.M C.i) (C.D.coord C.b C.i)) := by
  obtain ⟨n, k, e, hA⟩ := IsNaturalSE.exists_isBenderAction (C.isNaturalSE C.i)
  exact hA.isCyclic_stabilizer_inf C.coord_ne

omit C [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem zpow_smul_eq {π : typeLSection G Ω v} {g : G}
    (h : ∀ ω : fixSet Ω (Subgroup.zpowers v), ((π • ω : fixSet Ω _) : Ω) = g • (ω : Ω)) (n : ℤ)
    (ω : fixSet Ω (Subgroup.zpowers v)) : ((π ^ n • ω : fixSet Ω _) : Ω) = g ^ n • (ω : Ω) := by
  have hinv : ∀ ω : fixSet Ω (Subgroup.zpowers v),
      ((π⁻¹ • ω : fixSet Ω _) : Ω) = g⁻¹ • (ω : Ω) := fun ω => by
    rw [eq_inv_smul_iff, ← h, smul_inv_smul]
  induction n using Int.induction_on generalizing ω with
  | zero => simp
  | succ n ih => rw [zpow_add_one, zpow_add_one, mul_smul, mul_smul, ← h, ih]
  | pred n ih => rw [zpow_sub_one, zpow_sub_one, mul_smul, mul_smul, ← hinv, ih]

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem cartan_comm {m m' : Equiv.Perm (C.D.Ψc C.i)} (hm : m ∈ C.D.M C.i)
    (hma : m (C.D.coord C.a C.i) = C.D.coord C.a C.i) (hmb : m (C.D.coord C.b C.i) =
      C.D.coord C.b C.i) (hm' : m' ∈ C.D.M C.i)
    (hm'a : m' (C.D.coord C.a C.i) = C.D.coord C.a C.i)
    (hm'b : m' (C.D.coord C.b C.i) = C.D.coord C.b C.i) : m * m' = m' * m := by
  have := C.isCyclic_cartan
  have h := IsCyclic.commGroup.mul_comm
    (⟨⟨m, hm⟩, Subgroup.mem_inf.mpr ⟨hma, hmb⟩⟩ : ↥(stabilizer (C.D.M C.i) (C.D.coord C.a C.i) ⊓
      stabilizer (C.D.M C.i) (C.D.coord C.b C.i))) ⟨⟨m', hm'⟩, Subgroup.mem_inf.mpr ⟨hm'a, hm'b⟩⟩
  exact congrArg (fun y : ↥(stabilizer (C.D.M C.i) (C.D.coord C.a C.i) ⊓
    stabilizer (C.D.M C.i) (C.D.coord C.b C.i)) => (y.1.1 : Equiv.Perm (C.D.Ψc C.i))) h

theorem pair_commute (hS : Sec4Setting G Ω) {c₁ c₂ c₃ c₄ : G}
    (h₁ : c₁ ∈ longInvSwap G Ω α C.β)
    (h₁' : c₁ ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G))
    (h₂ : c₂ ∈ longInvSwap G Ω α C.β)
    (h₂' : c₂ ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G))
    (h₃ : c₃ ∈ longInvSwap G Ω α C.β)
    (h₃' : c₃ ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G))
    (h₄ : c₄ ∈ longInvSwap G Ω α C.β)
    (h₄' : c₄ ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G))
    {δ : fixSet Ω (Subgroup.zpowers v)} (hδ : ∀ j, j ≠ C.i → C.D.coord δ j = C.D.coord C.a j) :
    (c₁ * c₂) • (c₃ * c₄) • (δ : Ω) = (c₃ * c₄) • (c₁ * c₂) • (δ : Ω) := by
  obtain ⟨hP, hPM, hPa, hPb⟩ := C.pairElt_mem hS h₁ h₁' h₂ h₂'
  obtain ⟨hQ, hQM, hQa, hQb⟩ := C.pairElt_mem hS h₃ h₃' h₄ h₄'
  set P := C.pairElt hS h₁.1 h₁' h₂.1 h₂'
  set Q := C.pairElt hS h₃.1 h₃' h₄.1 h₄'
  have hρ : C.D.ρ C.i (P * Q) = C.D.ρ C.i (Q * P) :=
    calc C.D.ρ C.i (P * Q) = C.D.ρ C.i P * C.D.ρ C.i Q := map_mul _ P Q
      _ = C.D.ρ C.i Q * C.D.ρ C.i P := C.cartan_comm hPM hPa hPb hQM hQa hQb
      _ = C.D.ρ C.i (Q * P) := (map_mul _ Q P).symm
  have h := C.smul_eq_of_mem_lineSubgroup (mul_mem hP hQ) (mul_mem hQ hP) hρ hδ
  have h' := congrArg Subtype.val h
  simp only [Subgroup.coe_mul, mul_smul] at h'
  rwa [C.coe_pairElt_smul, C.coe_pairElt_smul, C.coe_pairElt_smul, C.coe_pairElt_smul] at h'

theorem exists_zpow_pair (hS : Sec4Setting G Ω) {c₁ c₂ c₃ c₄ : G}
    (h₁ : c₁ ∈ longInvSwap G Ω α C.β)
    (h₁' : c₁ ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G))
    (h₂ : c₂ ∈ longInvSwap G Ω α C.β)
    (h₂' : c₂ ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G))
    (h₃ : c₃ ∈ longInvSwap G Ω α C.β)
    (h₃' : c₃ ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G))
    (h₄ : c₄ ∈ longInvSwap G Ω α C.β)
    (h₄' : c₄ ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)) :
    ∃ x y k l : ℤ, ∀ δ : fixSet Ω (Subgroup.zpowers v),
      (∀ j, j ≠ C.i → C.D.coord δ j = C.D.coord C.a j) →
        (c₁ * c₂) • (δ : Ω) = ((c₁ * c₂) ^ x * (c₃ * c₄) ^ y) ^ k • (δ : Ω) ∧
        (c₃ * c₄) • (δ : Ω) = ((c₁ * c₂) ^ x * (c₃ * c₄) ^ y) ^ l • (δ : Ω) := by
  obtain ⟨hP, hPM, hPa, hPb⟩ := C.pairElt_mem hS h₁ h₁' h₂ h₂'
  obtain ⟨hQ, hQM, hQa, hQb⟩ := C.pairElt_mem hS h₃ h₃' h₄ h₄'
  set P := C.pairElt hS h₁.1 h₁' h₂.1 h₂'
  set Q := C.pairElt hS h₃.1 h₃' h₄.1 h₄'
  have := C.isCyclic_cartan
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(stabilizer (C.D.M C.i)
    (C.D.coord C.a C.i) ⊓ stabilizer (C.D.M C.i) (C.D.coord C.b C.i)))
  set mP : ↥(stabilizer (C.D.M C.i) (C.D.coord C.a C.i) ⊓
    stabilizer (C.D.M C.i) (C.D.coord C.b C.i)) := ⟨⟨_, hPM⟩, Subgroup.mem_inf.mpr ⟨hPa, hPb⟩⟩
  set mQ : ↥(stabilizer (C.D.M C.i) (C.D.coord C.a C.i) ⊓
    stabilizer (C.D.M C.i) (C.D.coord C.b C.i)) := ⟨⟨_, hQM⟩, Subgroup.mem_inf.mpr ⟨hQa, hQb⟩⟩
  obtain ⟨k₀, hk₀⟩ := Subgroup.mem_zpowers_iff.mp (hg mP)
  obtain ⟨l₀, hl₀⟩ := Subgroup.mem_zpowers_iff.mp (hg mQ)
  set d : ℤ := (Int.gcd k₀ l₀ : ℤ)
  set x := Int.gcdA k₀ l₀
  set y := Int.gcdB k₀ l₀
  have hd : d = k₀ * x + l₀ * y := Int.gcd_eq_gcd_ab k₀ l₀
  have hgen : mP ^ x * mQ ^ y = g ^ d := by
    rw [← hk₀, ← hl₀, ← zpow_mul, ← zpow_mul, ← zpow_add, hd]
  have hkey : ∀ e : ℤ, d ∣ e → (mP ^ x * mQ ^ y) ^ (e / d) = g ^ e := fun e he => by
    rw [hgen, ← zpow_mul, Int.mul_ediv_cancel' he]
  refine ⟨x, y, k₀ / d, l₀ / d, fun δ hδ => ?_⟩
  have hρ : ∀ e : ℤ, d ∣ e → C.D.ρ C.i ((P ^ x * Q ^ y) ^ (e / d)) =
      (((g ^ e : ↥(stabilizer (C.D.M C.i) (C.D.coord C.a C.i) ⊓
        stabilizer (C.D.M C.i) (C.D.coord C.b C.i))) : C.D.M C.i) : Equiv.Perm _) :=
    fun e he => by
      rw [← hkey e he]
      simp [mP, mQ, map_zpow, map_mul]
  have hmem : ∀ e : ℤ, (P ^ x * Q ^ y) ^ e ∈ C.lineSubgroup := fun e =>
    zpow_mem (mul_mem (zpow_mem hP x) (zpow_mem hQ y)) e
  have hact : ∀ (e : ℤ) (ω : fixSet Ω (Subgroup.zpowers v)),
      ((((P ^ x * Q ^ y) ^ e : jHull _ _) : typeLSection G Ω v) • ω : fixSet Ω _) =
        (((c₁ * c₂) ^ x * (c₃ * c₄) ^ y) ^ e) • (ω : Ω) := fun e ω => by
    simp only [Subgroup.coe_zpow, Subgroup.coe_mul]
    refine zpow_smul_eq (fun ω' => ?_) e ω
    rw [mul_smul, zpow_smul_eq (fun ω'' => C.coe_pairElt_smul hS _ _ _ _ ω'') x,
      zpow_smul_eq (fun ω'' => C.coe_pairElt_smul hS _ _ _ _ ω'') y, ← mul_smul]
  constructor
  · rw [← C.coe_pairElt_smul hS h₁.1 h₁' h₂.1 h₂', ← hact]
    refine congrArg Subtype.val (C.smul_eq_of_mem_lineSubgroup hP (hmem _) ?_ hδ)
    rw [hρ k₀ (Int.gcd_dvd_left k₀ l₀), hk₀]
  · rw [← C.coe_pairElt_smul hS h₃.1 h₃' h₄.1 h₄', ← hact]
    refine congrArg Subtype.val (C.smul_eq_of_mem_lineSubgroup hQ (hmem _) ?_ hδ)
    rw [hρ l₀ (Int.gcd_dvd_right k₀ l₀), hl₀]

end Coord

end P49Config

end CFSG.Holt.H78
