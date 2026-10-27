module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixAlternatingEightNextNormalizerQuotient
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergCCOddNormalCore

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.AlternatingEight

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank FusionOrbits Degree64
open LinearMap (BilinForm)
open scoped Pointwise

section Conj

variable {G : Type*} [Group G] (C : Subgroup G)

@[expose] def conjAutOf : normalizer (C : Set G) →* MulAut C where
  toFun x :=
    { toFun := fun c => ⟨x * c * (x : G)⁻¹, (mem_normalizer_iff.1 x.2 c).1 c.2⟩
      invFun := fun c => ⟨(x : G)⁻¹ * c * x, by
        have h := (mem_normalizer_iff.1 (inv_mem x.2) c).1 c.2
        rwa [inv_inv] at h⟩
      left_inv := fun c => Subtype.ext (show (x : G)⁻¹ * ((x : G) * c * (x : G)⁻¹) * x = c by
        group)
      right_inv := fun c => Subtype.ext (show (x : G) * ((x : G)⁻¹ * c * x) * (x : G)⁻¹ = c by
        group)
      map_mul' := fun c c' => Subtype.ext (show (x : G) * (c * c') * (x : G)⁻¹ =
        ((x : G) * c * (x : G)⁻¹) * ((x : G) * c' * (x : G)⁻¹) by group) }
  map_one' := MulEquiv.ext fun c => Subtype.ext (show (1 : G) * c * (1 : G)⁻¹ = c by group)
  map_mul' x y := MulEquiv.ext fun c => Subtype.ext (show ((x : G) * y) * c * ((x : G) * y)⁻¹ =
    (x : G) * ((y : G) * c * (y : G)⁻¹) * (x : G)⁻¹ by group)

theorem coe_conjAutOf_apply (x : normalizer (C : Set G)) (c : C) :
    ((conjAutOf C x c : C) : G) = x * c * (x : G)⁻¹ :=
  rfl

theorem ker_conjAutOf :
    (conjAutOf C).ker = (centralizer (C : Set G)).subgroupOf (normalizer (C : Set G)) := by
  ext x
  rw [MonoidHom.mem_ker, mem_subgroupOf, mem_centralizer_iff]
  constructor
  · intro h c hc
    have h1 := congrArg Subtype.val (MulEquiv.ext_iff.1 h ⟨c, hc⟩)
    change (x : G) * c * (x : G)⁻¹ = c at h1
    calc c * x = (x : G) * c * (x : G)⁻¹ * x := by rw [h1]
      _ = x * c := by group
  · intro h
    refine MulEquiv.ext fun c => Subtype.ext ?_
    change (x : G) * c * (x : G)⁻¹ = c
    rw [← h c c.2]
    group

end Conj

theorem eq_one_of_mul_self_of_pow_odd {G : Type*} [Group G] {c : G} {m : ℕ} (hm : Odd m)
    (hc : c * c = 1) (hcm : c ^ m = 1) : c = 1 := by
  obtain ⟨j, rfl⟩ := hm
  rw [pow_succ, pow_mul, sq, hc, one_pow, one_mul] at hcm
  exact hcm

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z : G}
  (hzC : z ∈ centralizer (L : Set G)) (hsup : L ⊔ zpowers z = centralizer ({z} : Set G))
  (hinf : L ⊓ zpowers z = ⊥) (hz : orderOf z = 2)
variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {b : BilinForm (ZMod 2) V} (hb : b.IsAlt) (hnd : b.Nondegenerate)
  (hV : finrank (ZMod 2) V = 6) (φ : L ≃* bilinIsometryGroup b)
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e)
  (halt : AltOrbit z φ e)

local notation "𝒜" => pullSub φ (pointwiseStabilizer b (lagrangianOf e))
local notation "ℛ" => (𝒜 ⊔ zpowers z : Subgroup G)
local notation "𝒩" => normalizer ((ℛ : Subgroup G) : Set G)
local notation "𝒟" => CFSG.Assembly.pCoreOf 2 𝒩
local notation "θ₂" => RadicalLabels.radLabel φ he hzC hz hinf

include hzC hsup hz hb hnd hV he in
theorem centralizer_inf_eq {C₂ : Subgroup G} (hC₂c : Nat.card C₂ = 512) (hC₂R : C₂ ⊓ ℛ = 𝒜)
    (hC₂z : ∀ c ∈ C₂, c * z = z * c ↔ c ∈ 𝒜) (hC₂e : IsElementaryAbelian 2 C₂) :
    centralizer (C₂ : Set G) ⊓ centralizer ({z} : Set G) = 𝒜 := by
  obtain ⟨hAe, hAc, hAC, -⟩ := pullSub_radical hb hnd hV φ (isTotallyIsotropic_lagrangianOf he)
    finrank_lagrangianOf
  have hAL : 𝒜 ≤ L := pullSub_le φ _
  have hAC₂ : 𝒜 ≤ C₂ := hC₂R ▸ inf_le_left
  have hC₂Y : C₂ ≤ centralizer (C₂ : Set G) := fun c hc =>
    mem_centralizer_iff.2 fun c' hc' => mul_comm_of_isElementaryAbelian hC₂e hc' hc
  apply le_antisymm
  · rintro y ⟨hyY, hyz⟩
    have hyH : y ∈ L ⊔ zpowers z := by
      rw [hsup]
      exact hyz
    obtain ⟨l, hl, t, ht, rfl⟩ := (mem_sup_of_le_centralizer (zpowers_le_centralizer hzC)).1 hyH
    have htA : ∀ a ∈ 𝒜, a * t = t * a := fun a ha =>
      mem_centralizer_iff.1 (zpowers_le_centralizer hzC ht) a (hAL ha)
    have hlA : l ∈ centralizer (𝒜 : Set G) ⊓ L := by
      refine mem_inf.2 ⟨mem_centralizer_iff.2 fun a ha => ?_, hl⟩
      have h1 := mem_centralizer_iff.1 hyY a (hAC₂ ha)
      have h2 := htA a ha
      calc a * l = a * (l * t) * t⁻¹ := by group
        _ = l * t * a * t⁻¹ := by rw [h1]
        _ = l * (t * a) * t⁻¹ := by group
        _ = l * (a * t) * t⁻¹ := by rw [h2]
        _ = l * a := by group
    rw [hAC] at hlA
    rcases eq_one_or_eq_of_mem_zpowers hz ht with h | h
    · rwa [h, mul_one]
    · exfalso
      rw [h] at hyY
      have hzY : z ∈ centralizer (C₂ : Set G) := by
        have h1 : l⁻¹ * (l * z) ∈ centralizer (C₂ : Set G) :=
          mul_mem (inv_mem (hC₂Y (hAC₂ hlA))) hyY
        rwa [inv_mul_cancel_left] at h1
      have hle : C₂ ≤ 𝒜 := fun c hc => (hC₂z c hc).1 (mem_centralizer_iff.1 hzY c hc)
      have h1 := Subgroup.card_le_of_le hle
      rw [hC₂c, hAc] at h1
      norm_num at h1
  · intro a ha
    exact mem_inf.2 ⟨hC₂Y (hAC₂ ha), mem_centralizer_singleton_iff.2 ((hC₂z a (hAC₂ ha)).2 ha)⟩

include hzC hsup hinf hz hb hnd hV he halt in
theorem mem_of_inv_conj_mul_mem {C₂ : Subgroup G} (hC₂c : Nat.card C₂ = 512)
    (hC₂R : C₂ ⊓ ℛ = 𝒜) (hC₂z : ∀ c ∈ C₂, c * z = z * c ↔ c ∈ 𝒜)
    (hC₂e : IsElementaryAbelian 2 C₂) (hC₂N : ∀ g ∈ 𝒩, ∀ c ∈ C₂, g * c * g⁻¹ ∈ C₂)
    (hC₂comm : {x | ∃ c ∈ C₂, c⁻¹ * z⁻¹ * c * z = x} =
      (BinarySymThreeOrbit.layerSub θ₂ BinarySymThreeOrbit.altSym : Set G))
    {y : G} (hy : y ∈ centralizer (C₂ : Set G)) (hyz : (z * y * z⁻¹)⁻¹ * y ∈ C₂) : y ∈ C₂ := by
  have hAC₂ : 𝒜 ≤ C₂ := hC₂R ▸ inf_le_left
  have hzN : z ∈ 𝒩 := le_normalizer (mem_sup_right (mem_zpowers z))
  have hC₂Y : C₂ ≤ centralizer (C₂ : Set G) := fun c hc =>
    mem_centralizer_iff.2 fun c' hc' => mul_comm_of_isElementaryAbelian hC₂e hc' hc
  set u := (z * y * z⁻¹)⁻¹ * y with hu
  have hyu : y * u * y⁻¹ = u := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (mem_centralizer_iff.1 hy u hyz).symm
  set c₀ := z⁻¹ * (y * u * y⁻¹) * z with hc₀
  have hc₀C : c₀ ∈ C₂ := by
    have h1 := hC₂N z⁻¹ (inv_mem hzN) (y * u * y⁻¹) (by rw [hyu]; exact hyz)
    rwa [inv_inv] at h1
  have hyz' : y * z * y⁻¹ = z * c₀ := by
    rw [hc₀, hu]
    group
  obtain ⟨c, hc, hcz⟩ := exists_conj_eq_mul hzC hsup hinf hz hb hnd hV φ he halt hC₂z hC₂e
    hC₂comm hc₀C hyz'
  have h1 : c⁻¹ * y ∈ centralizer (C₂ : Set G) ⊓ centralizer ({z} : Set G) := by
    refine mem_inf.2 ⟨mul_mem (inv_mem (hC₂Y hc)) hy, mem_centralizer_singleton_iff.2 ?_⟩
    have h2 : (c⁻¹ * y) * z * (c⁻¹ * y)⁻¹ = z := by
      calc (c⁻¹ * y) * z * (c⁻¹ * y)⁻¹ = c⁻¹ * (y * z * y⁻¹) * c := by group
        _ = c⁻¹ * (c * z * c⁻¹) * c := by rw [hyz', ← hcz]
        _ = z := by group
    calc c⁻¹ * y * z = (c⁻¹ * y) * z * (c⁻¹ * y)⁻¹ * (c⁻¹ * y) := by group
      _ = z * (c⁻¹ * y) := by rw [h2]
  rw [centralizer_inf_eq hzC hsup hz hb hnd hV φ he hC₂c hC₂R hC₂z hC₂e] at h1
  have h2 := mul_mem hc (hAC₂ h1)
  rwa [mul_inv_cancel_left] at h2

include hzC hsup hinf hz hb hnd hV he halt in
theorem centralizer_structure {C₂ : Subgroup G} (hC₂c : Nat.card C₂ = 512)
    (hC₂R : C₂ ⊓ ℛ = 𝒜) (hC₂z : ∀ c ∈ C₂, c * z = z * c ↔ c ∈ 𝒜)
    (hC₂e : IsElementaryAbelian 2 C₂) (hC₂N : ∀ g ∈ 𝒩, ∀ c ∈ C₂, g * c * g⁻¹ ∈ C₂)
    (hC₂comm : {x | ∃ c ∈ C₂, c⁻¹ * z⁻¹ * c * z = x} =
      (BinarySymThreeOrbit.layerSub θ₂ BinarySymThreeOrbit.altSym : Set G)) :
    let Y := centralizer (C₂ : Set G)
    let K := (CFSG.oddCore Y).map Y.subtype
    (∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) ∧ Y = C₂ ⊔ K ∧ C₂ ⊓ K = ⊥ ∧ Odd (Nat.card K) ∧
      (∀ g ∈ normalizer (C₂ : Set G), ∀ k ∈ K, g * k * g⁻¹ ∈ K) ∧
      ∀ k ∈ K, z * k * z⁻¹ = k⁻¹ := by
  classical
  intro Y K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzN : z ∈ 𝒩 := le_normalizer (mem_sup_right (mem_zpowers z))
  have hzX : z ∈ normalizer (C₂ : Set G) := by
    rw [mem_normalizer_iff]
    intro c
    refine ⟨hC₂N z hzN c, fun hc => ?_⟩
    have h1 := hC₂N z⁻¹ (inv_mem hzN) _ hc
    rwa [show z⁻¹ * (z * c * z⁻¹) * z⁻¹⁻¹ = c by group] at h1
  have hz2 := z_mul_self hz
  have hC₂Y : C₂ ≤ Y := fun c hc =>
    mem_centralizer_iff.2 fun c' hc' => mul_comm_of_isElementaryAbelian hC₂e hc' hc
  have hYn : ∀ g ∈ normalizer (C₂ : Set G), ∀ y ∈ Y, g * y * g⁻¹ ∈ Y := by
    intro g hg y hy
    rw [mem_centralizer_iff]
    intro c hc
    have h1 : g⁻¹ * c * g ∈ C₂ := by
      have h2 := (mem_normalizer_iff.1 (inv_mem hg) c).1 hc
      rwa [inv_inv] at h2
    have h2 := mem_centralizer_iff.1 hy _ h1
    calc c * (g * y * g⁻¹) = g * ((g⁻¹ * c * g) * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * c * g)) * g⁻¹ := by rw [h2]
      _ = g * y * g⁻¹ * c := by group
  have hC₂Yn : (C₂.subgroupOf Y).Normal := ⟨fun c hc g => by
    rw [mem_subgroupOf] at hc ⊢
    have h := mem_centralizer_iff.1 g.2 c hc
    change (g : G) * c * (g : G)⁻¹ ∈ C₂
    rw [← h, mul_inv_cancel_right]
    exact hc⟩
  let cz : Y →* Y := ((MulAut.conj z).toMonoidHom.comp Y.subtype).codRestrict Y
    (fun y => hYn z hzX y y.2)
  have hcz : C₂.subgroupOf Y ≤ (C₂.subgroupOf Y).comap cz := fun c hc => by
    rw [mem_subgroupOf] at hc
    rw [mem_comap, mem_subgroupOf]
    exact (mem_normalizer_iff.1 hzX c).1 hc
  let φz : Y ⧸ C₂.subgroupOf Y →* Y ⧸ C₂.subgroupOf Y :=
    QuotientGroup.map (C₂.subgroupOf Y) (C₂.subgroupOf Y) cz hcz
  have hφz : ∀ y : Y, φz (y : Y ⧸ C₂.subgroupOf Y) = ((cz y : Y) : Y ⧸ C₂.subgroupOf Y) :=
    fun y => QuotientGroup.map_mk _ _ _ _ y
  have hczcz : ∀ y : Y, cz (cz y) = y := fun y => Subtype.ext (by
    change z * (z * y * z⁻¹) * z⁻¹ = y
    calc z * (z * y * z⁻¹) * z⁻¹ = (z * z) * y * (z * z)⁻¹ := by group
      _ = y := by rw [hz2]; group)
  have hinv : Function.Involutive φz := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hφz, hφz, hczcz]
  have hfpf : MonoidHom.FixedPointFree φz := by
    intro q hq
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hφz, QuotientGroup.eq, mem_subgroupOf] at hq
    change (z * y * z⁻¹)⁻¹ * y ∈ C₂ at hq
    rw [QuotientGroup.eq_one_iff, mem_subgroupOf]
    exact mem_of_inv_conj_mul_mem hzC hsup hinf hz hb hnd hV φ he halt hC₂c hC₂R hC₂z hC₂e hC₂N
      hC₂comm y.2 hq
  have hQodd := hfpf.odd_card_of_involutive hinv
  have hQinv := hfpf.coe_eq_inv_of_involutive hinv
  have hQcomm := hfpf.commute_all_of_involutive hinv
  set m := Nat.card (Y ⧸ C₂.subgroupOf Y) with hm
  have hpowC : ∀ y ∈ Y, y ^ m ∈ C₂ := by
    intro y hy
    have h1 : ((⟨y, hy⟩ : Y) : Y ⧸ C₂.subgroupOf Y) ^ m = 1 := pow_card_eq_one'
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
    exact h1
  have hYab : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x := by
    intro x hx y hy
    set c := x * y * x⁻¹ * y⁻¹ with hc
    have hcC : c ∈ C₂ := by
      have h1 := (hQcomm ((⟨x, hx⟩ : Y) : Y ⧸ C₂.subgroupOf Y)
        ((⟨y, hy⟩ : Y) : Y ⧸ C₂.subgroupOf Y)).eq
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, eq_comm, QuotientGroup.eq,
        mem_subgroupOf] at h1
      change (y * x)⁻¹ * (x * y) ∈ C₂ at h1
      have h2 := mem_centralizer_iff.1 (mul_mem hy hx) _ h1
      have h3 : c = (y * x) * ((y * x)⁻¹ * (x * y)) * (y * x)⁻¹ := by rw [hc]; group
      rw [h3, ← h2, mul_inv_cancel_right]
      exact h1
    have hcx : Commute c x := mem_centralizer_iff.1 hx c hcC
    have hcy : c * y = x * y * x⁻¹ := by rw [hc]; group
    have hind : ∀ k : ℕ, x ^ k * y * (x ^ k)⁻¹ = c ^ k * y := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        calc x ^ (k + 1) * y * (x ^ (k + 1))⁻¹ = x * (x ^ k * y * (x ^ k)⁻¹) * x⁻¹ := by group
          _ = x * c ^ k * y * x⁻¹ := by rw [ih]; group
          _ = c ^ k * (x * y * x⁻¹) := by rw [(hcx.symm.pow_right k).eq]; group
          _ = c ^ (k + 1) * y := by rw [← hcy]; group
    have hxm : x ^ m * y = y * x ^ m := mem_centralizer_iff.1 hy _ (hpowC x hx)
    have hcm : c ^ m = 1 := by
      have h1 := hind m
      rw [hxm, mul_inv_cancel_right] at h1
      exact (mul_eq_right.1 h1.symm)
    have hc1 : c = 1 :=
      eq_one_of_mul_self_of_pow_odd hQodd (mul_self_of_isElementaryAbelian hC₂e hcC) hcm
    have h1 : x * y * x⁻¹ * y⁻¹ = 1 := hc1
    calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
      _ = y * x := by rw [h1, one_mul]
  let K₀ : Subgroup Y :=
    { carrier := {y | y ^ m = 1}
      mul_mem' := fun {a b} ha hb => by
        change (a * b) ^ m = 1
        rw [(show Commute a b from Subtype.ext (hYab _ a.2 _ b.2)).mul_pow m]
        rw [show a ^ m = 1 from ha, show b ^ m = 1 from hb, one_mul]
      one_mem' := one_pow m
      inv_mem' := fun {a} ha => by
        change a⁻¹ ^ m = 1
        rw [inv_pow, show a ^ m = 1 from ha, inv_one] }
  have hK₀n : K₀.Normal := ⟨fun n hn g => by
    rw [show g * n * g⁻¹ = n from by
      rw [show g * n = n * g from Subtype.ext (hYab _ g.2 _ n.2), mul_inv_cancel_right]]
    exact hn⟩
  have hK₀odd : Odd (Nat.card K₀) := by
    by_contra hev
    rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hev
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hev
    have hxm : (x : Y) ^ m = 1 := x.2
    have h1 : orderOf x ∣ m := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_dvd_of_pow_eq_one hxm
    rw [hx] at h1
    exact (Nat.not_even_iff_odd.2 hQodd) (even_iff_two_dvd.2 h1)
  have hK₀le : K₀ ≤ CFSG.oddCore Y := le_sSup ⟨hK₀n, hK₀odd⟩
  have hcardY : Nat.card Y = m * 512 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (C₂.subgroupOf Y),
      Nat.card_congr (subgroupOfEquivOfLe hC₂Y).toEquiv, hC₂c]
  have hodd := OddNormalCore.odd_card_oddCore Y
  have hleK₀ : CFSG.oddCore Y ≤ K₀ := by
    intro k hk
    have h1 : orderOf k ∣ Nat.card (CFSG.oddCore Y) := by
      rw [← Subgroup.orderOf_mk k hk]
      exact orderOf_dvd_natCard _
    have h2 : orderOf k ∣ m * 512 := hcardY ▸ orderOf_dvd_natCard k
    have hcop : (orderOf k).Coprime 512 := by
      have h3 : Odd (orderOf k) := Odd.of_dvd_nat hodd h1
      exact (Nat.coprime_two_right.2 h3).pow_right 9
    exact orderOf_dvd_iff_pow_eq_one.1 (hcop.dvd_of_dvd_mul_right h2)
  have hmemK : ∀ {x : G}, x ∈ K ↔ ∃ hx : x ∈ Y, x ^ m = 1 := by
    intro x
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k.2, congrArg Subtype.val (hleK₀ hk)⟩
    · rintro ⟨hx, hxm⟩
      exact ⟨⟨x, hx⟩, hK₀le (Subtype.ext hxm : ((⟨x, hx⟩ : Y) ^ m) = 1), rfl⟩
  have hbot : C₂ ⊓ K = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxC, hxK⟩
    obtain ⟨-, hxm⟩ := hmemK.1 hxK
    exact eq_one_of_mul_self_of_pow_odd hQodd (mul_self_of_isElementaryAbelian hC₂e hxC) hxm
  have hKn : ∀ g ∈ normalizer (C₂ : Set G), ∀ k ∈ K, g * k * g⁻¹ ∈ K := by
    intro g hg k hk
    obtain ⟨hkY, hkm⟩ := hmemK.1 hk
    exact hmemK.2 ⟨hYn g hg k hkY, by rw [conj_pow, hkm, mul_one, mul_inv_cancel]⟩
  refine ⟨hYab, le_antisymm (fun y hy => ?_) (sup_le hC₂Y fun k hk => (hmemK.1 hk).1), hbot,
    ?_, hKn, fun k hk => ?_⟩
  ·
    have hcop : Nat.Coprime 512 m :=
      ((Nat.coprime_two_right.2 hQodd).pow_right 9).symm
    have hAB := Nat.gcd_eq_gcd_ab 512 m
    rw [hcop, Nat.cast_one, Nat.cast_ofNat] at hAB
    set A := Nat.gcdA 512 m
    set B := Nat.gcdB 512 m
    have hy1 : y = y ^ ((512 : ℤ) * A) * y ^ ((m : ℤ) * B) := by
      rw [← _root_.zpow_add, ← hAB, zpow_one]
    have hym2 : (y ^ m) ^ 2 = 1 := by
      rw [sq]
      exact mul_self_of_isElementaryAbelian hC₂e (hpowC y hy)
    rw [hy1]
    refine mul_mem (mem_sup_right (hmemK.2 ⟨zpow_mem hy _, ?_⟩)) (mem_sup_left ?_)
    · rw [← zpow_natCast, ← _root_.zpow_mul, show (512 : ℤ) * A * (m : ℤ) =
        (m : ℤ) * (2 * (256 * A)) by ring, _root_.zpow_mul, zpow_natCast, _root_.zpow_mul,
        show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, hym2, _root_.one_zpow]
    · rw [_root_.zpow_mul, zpow_natCast]
      exact zpow_mem (hpowC y hy) _
  · rw [Subgroup.card_map_of_injective Y.subtype_injective]
    exact hodd
  ·
    obtain ⟨hkY, hkm⟩ := hmemK.1 hk
    have hzk : z * k * z⁻¹ ∈ K := hKn z hzX k hk
    have h1 := congrFun hQinv ((⟨k, hkY⟩ : Y) : Y ⧸ C₂.subgroupOf Y)
    rw [hφz, ← QuotientGroup.mk_inv, QuotientGroup.eq, mem_subgroupOf] at h1
    change (z * k * z⁻¹)⁻¹ * k⁻¹ ∈ C₂ at h1
    have h2 : (z * k * z⁻¹)⁻¹ * k⁻¹ ∈ K := mul_mem (inv_mem hzk) (inv_mem hk)
    have h3 : (z * k * z⁻¹)⁻¹ * k⁻¹ ∈ C₂ ⊓ K := mem_inf.2 ⟨h1, h2⟩
    rw [hbot, mem_bot] at h3
    calc z * k * z⁻¹ = z * k * z⁻¹ * ((z * k * z⁻¹)⁻¹ * k⁻¹) := by rw [h3, mul_one]
      _ = k⁻¹ := by group

end Setting

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.AlternatingEight
