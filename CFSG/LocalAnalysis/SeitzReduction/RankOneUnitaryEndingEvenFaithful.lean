module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEnding
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingNormalizer
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingNormalizerBasic

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup
open scoped commutatorElement

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section ModCenter

variable {G : Type*} [Group G]

theorem conj_mem_center_of_mem_normalizer {U : Subgroup G} {x : G}
    (hx : x ∈ normalizer (U : Set G)) {z : G} (hz : z ∈ U ⊓ centralizer (U : Set G)) :
    x * z * x⁻¹ ∈ U ⊓ centralizer (U : Set G) := by
  obtain ⟨hzU, hzC⟩ := mem_inf.mp hz
  refine mem_inf.mpr ⟨(mem_normalizer_iff.mp hx z).mp hzU, mem_centralizer_iff.mpr fun w hw => ?_⟩
  have hw' : x⁻¹ * w * x ∈ U := (mem_normalizer_iff''.mp hx w).mp hw
  have h1 : (x⁻¹ * w * x) * z = z * (x⁻¹ * w * x) := mem_centralizer_iff.mp hzC _ hw'
  calc w * (x * z * x⁻¹) = x * ((x⁻¹ * w * x) * z) * x⁻¹ := by group
    _ = x * (z * (x⁻¹ * w * x)) * x⁻¹ := by rw [h1]
    _ = x * z * x⁻¹ * w := by group

@[expose] def centralizerModCenter (U : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ normalizer (U : Set G) ∧
    ∀ w ∈ U, x * w * x⁻¹ * w⁻¹ ∈ U ⊓ centralizer (U : Set G)}
  mul_mem' := by
    rintro x y ⟨hxN, hx⟩ ⟨hyN, hy⟩
    refine ⟨mul_mem hxN hyN, fun w hw => ?_⟩
    have e : x * y * w * (x * y)⁻¹ * w⁻¹ =
        (x * (y * w * y⁻¹ * w⁻¹) * x⁻¹) * (x * w * x⁻¹ * w⁻¹) := by group
    rw [e]
    exact mul_mem (conj_mem_center_of_mem_normalizer hxN (hy w hw)) (hx w hw)
  one_mem' := ⟨one_mem _, fun w _ => by
    rw [one_mul, inv_one, mul_one, mul_inv_cancel]
    exact one_mem _⟩
  inv_mem' := by
    rintro x ⟨hxN, hx⟩
    refine ⟨inv_mem hxN, fun w hw => ?_⟩
    have hw' : x⁻¹ * w * x ∈ U := (mem_normalizer_iff''.mp hxN w).mp hw
    have e : x⁻¹ * w * x⁻¹⁻¹ * w⁻¹ = (x * (x⁻¹ * w * x) * x⁻¹ * (x⁻¹ * w * x)⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem (hx _ hw')

theorem le_centralizerModCenter {U : Subgroup G}
    (hc : ∀ x ∈ U, ∀ y ∈ U, x * y * x⁻¹ * y⁻¹ ∈ centralizer (U : Set G)) :
    U ≤ centralizerModCenter U := fun x hx =>
  ⟨le_normalizer hx, fun w hw => mem_inf.mpr ⟨mul_mem (mul_mem (mul_mem hx hw) (inv_mem hx))
    (inv_mem hw), hc x hx w hw⟩⟩

theorem conj_mem_centralizerModCenter {U : Subgroup G} {g : G}
    (hg : g ∈ normalizer (U : Set G)) {x : G} (hx : x ∈ centralizerModCenter U) :
    g * x * g⁻¹ ∈ centralizerModCenter U := by
  obtain ⟨hxN, hx⟩ := hx
  refine ⟨mul_mem (mul_mem hg hxN) (inv_mem hg), fun w hw => ?_⟩
  have hw' : g⁻¹ * w * g ∈ U := (mem_normalizer_iff''.mp hg w).mp hw
  have e : g * x * g⁻¹ * w * (g * x * g⁻¹)⁻¹ * w⁻¹ =
      g * (x * (g⁻¹ * w * g) * x⁻¹ * (g⁻¹ * w * g)⁻¹) * g⁻¹ := by group
  rw [e]
  exact conj_mem_center_of_mem_normalizer hg (hx _ hw')

end ModCenter

namespace U3EndingData

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T R₂ U₁ : Subgroup G}
  {s : G}

theorem le_centralizerModCenter' (hD : U3EndingData G L f t T R₂ U₁ s) :
    U₁ ≤ centralizerModCenter U₁ :=
  le_centralizerModCenter fun x hx y hy => mem_centralizer_iff.mpr fun _ hz =>
    (mem_centralizer_iff.mp (hD.u1.le_centralizer hz) _ (hD.u1.comm_mem x hx y hy)).symm

theorem t_not_mem_centralizerModCenter
    (hD : U3EndingData G L f t T R₂ U₁ s) {Y₁ Y₂ : Subgroup G} (hY : Y₁ ⊔ Y₂ = U₁)
    (hinf : Y₁ ⊓ Y₂ = ⊥) (hcomm : ∀ a ∈ Y₁, ∀ b ∈ Y₂, a * b = b * a)
    (ht₁ : ∀ a ∈ Y₁, t * a * t⁻¹ ∈ Y₂) (ht₂ : ∀ b ∈ Y₂, t * b * t⁻¹ ∈ Y₁) :
    t ∉ centralizerModCenter U₁ := by
  rintro ⟨-, ht⟩
  obtain ⟨-, -, ⟨c, hc, c', hc', hcc'⟩, -⟩ :=
    hD.u1.product_facts_of_card_sylow hD.start hD.card_sylow hD.r2 hY hinf hcomm ht₁ ht₂
  have hcU : c ∈ U₁ := hY ▸ mem_sup_left hc
  have hc'U : c' ∈ U₁ := hY ▸ mem_sup_left hc'
  obtain ⟨-, hzC⟩ := mem_inf.mp (ht c hcU)
  have e : t * c * t⁻¹ = (t * c * t⁻¹ * c⁻¹) * c := by group
  have h1 : (t * c * t⁻¹) * c' = c' * (t * c * t⁻¹) := (hcomm c' hc' _ (ht₁ c hc)).symm
  have h2 : (t * c * t⁻¹ * c⁻¹) * c' = c' * (t * c * t⁻¹ * c⁻¹) :=
    (mem_centralizer_iff.mp hzC c' hc'U).symm
  apply hcc'
  rw [e] at h1
  have h3 : (t * c * t⁻¹ * c⁻¹) * (c * c') = (t * c * t⁻¹ * c⁻¹) * (c' * c) := by
    calc (t * c * t⁻¹ * c⁻¹) * (c * c') = (t * c * t⁻¹ * c⁻¹) * c * c' := by group
      _ = c' * ((t * c * t⁻¹ * c⁻¹) * c) := h1
      _ = (c' * (t * c * t⁻¹ * c⁻¹)) * c := by group
      _ = ((t * c * t⁻¹ * c⁻¹) * c') * c := by rw [h2]
      _ = (t * c * t⁻¹ * c⁻¹) * (c' * c) := by group
  exact mul_left_cancel h3

theorem mem_szT₁_of_mem_centralizerModCenter
    (hD : U3EndingData G L f t T R₂ U₁ s) {v : G} (hvT : v ∈ T) (hv2 : v ^ 2 = 1)
    (hvS : v ∉ szT₁ L T ⊔ zpowers t) {Y₁ Y₂ : Subgroup G} (hY : Y₁ ⊔ Y₂ = U₁)
    (hinf : Y₁ ⊓ Y₂ = ⊥) (hcomm : ∀ a ∈ Y₁, ∀ b ∈ Y₂, a * b = b * a)
    (ht₁ : ∀ a ∈ Y₁, t * a * t⁻¹ ∈ Y₂) (ht₂ : ∀ b ∈ Y₂, t * b * t⁻¹ ∈ Y₁) {x : G}
    (hxT : x ∈ T) (hx : x ∈ centralizerModCenter U₁) : x ∈ szT₁ L T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hD.start
  have hS2 := hD.card_sylow
  have hU := hD.u1
  obtain ⟨-, -, -, hTN₁, -⟩ := h.start_of_card_sylow hS2
  obtain ⟨-, -, hA₁comm, -⟩ := h.facts_of_card_sylow hS2
  have hT₁U : szT₁ L T ≤ U₁ := le_sup_left.trans hU.le
  have hxA : x ∈ centralizerModCenter (szT₁ L T) := by
    refine ⟨hTN₁ hxT, fun a ha => ?_⟩
    have h1 := hx.2 a (hT₁U ha)
    have h2 : x * a * x⁻¹ * a⁻¹ ∈ szT₁ L T :=
      mul_mem ((mem_normalizer_iff.mp (hTN₁ hxT) a).mp ha) (inv_mem ha)
    refine mem_inf.mpr ⟨h2, mem_centralizer_iff.mpr fun z hz => ?_⟩
    exact mem_centralizer_iff.mp (mem_inf.mp h1).2 z (hT₁U hz)
  have htC : ∀ a ∈ szT₁ L T, t * a * t⁻¹ = a := fun a ha => by
    rw [← mem_centralizer_iff.mp h.mem_centralizer_szT₁ a ha, mul_inv_cancel_right]
  have hTtA : szT₁ L T ⊔ zpowers t ≤ centralizerModCenter (szT₁ L T) := by
    refine sup_le (le_centralizerModCenter fun a ha b hb => ?_) ((zpowers_le (G := G)).mpr ?_)
    · have hab : ⁅a, b⁆ ∈ szA₁ (szT₁ L T) := by
        rw [hA₁comm]
        exact commutator_mem_commutator ha hb
      rw [commutatorElement_def] at hab
      exact (mem_inf.mp hab).2
    · refine ⟨mem_normalizer_iff.mpr fun a => ⟨fun ha => by rw [htC a ha]; exact ha,
        fun ha => ?_⟩, fun a ha => ?_⟩
      · have h1 : t * (t * a * t⁻¹) * t⁻¹ = t * a * t⁻¹ := htC _ ha
        have htt : t * t = 1 := by rw [← sq]; exact h.sq_eq_one
        have e : t * (t * a * t⁻¹) * t⁻¹ = a := by
          rw [show t * (t * a * t⁻¹) * t⁻¹ = (t * t) * a * (t * t)⁻¹ by group, htt, one_mul,
            inv_one, mul_one]
        rw [← e, h1]
        exact ha
      · rw [htC a ha, mul_inv_cancel]
        exact one_mem _
  by_cases hx1 : x ∈ szT₁ L T ⊔ zpowers t
  · obtain ⟨w, hw, z, hz, rfl⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ hx1
    rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hz with rfl | rfl
    · rw [mul_one]
      exact hw
    · exfalso
      apply hD.t_not_mem_centralizerModCenter hY hinf hcomm ht₁ ht₂
      have := mul_mem (hD.le_centralizerModCenter' (inv_mem (hT₁U hw))) hx
      rwa [inv_mul_cancel_left] at this
  · exfalso
    obtain ⟨φ, hφ, hcyc⟩ := h.exists_outHom_of_card_sylow hS2
    have : Finite (MulAut L) := U3Start.finite_mulAut L
    have hp : IsPGroup 2 φ.range :=
      h.isPGroup.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
    have hx1' : φ ⟨x, hxT⟩ ≠ 1 := fun e => hx1 ((hφ _).mp e)
    have hv1 : φ ⟨v, hvT⟩ ≠ 1 := fun e => hvS ((hφ _).mp e)
    have hvsq : φ ⟨v, hvT⟩ ^ 2 = 1 := by
      rw [← map_pow]
      have : (⟨v, hvT⟩ : T) ^ 2 = 1 := Subtype.ext (by simpa using hv2)
      rw [this, map_one]
    set X : φ.range := ⟨φ ⟨x, hxT⟩, ⟨_, rfl⟩⟩ with hXdef
    set V : φ.range := ⟨φ ⟨v, hvT⟩, ⟨_, rfl⟩⟩ with hVdef
    have hV1 : V ≠ 1 := fun e => hv1 (congrArg Subtype.val e)
    have hX1 : X ≠ 1 := fun e => hx1' (congrArg Subtype.val e)
    have hVo : orderOf V = 2 :=
      orderOf_eq_prime (Subtype.ext (by simpa using hvsq)) hV1
    obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.mp hp X
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hX1 (orderOf_eq_one_iff.mp (by simpa using hj))
    have hle : zpowers V ≤ zpowers X := by
      rw [IsCyclic.subgroup_le_iff_card_dvd, Nat.card_zpowers, Nat.card_zpowers, hVo, hj]
      exact dvd_pow_self 2 hj0
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hle (mem_zpowers V))
    have hk' : φ (⟨x, hxT⟩ ^ k * (⟨v, hvT⟩ : T)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_zpow]
      have := congrArg Subtype.val hk
      simp only [hXdef, hVdef, SubgroupClass.coe_zpow] at this
      rw [this, mul_inv_cancel]
    have hn : x ^ k * v⁻¹ ∈ szT₁ L T ⊔ zpowers t := by
      have := (hφ _).mp hk'
      simpa using this
    have hxk : x ^ k ∈ centralizerModCenter (szT₁ L T) := zpow_mem hxA k
    have hvA : v ∈ centralizerModCenter (szT₁ L T) := by
      have := mul_mem (inv_mem (hTtA hn)) hxk
      rwa [show (x ^ k * v⁻¹)⁻¹ * x ^ k = v by group] at this
    obtain ⟨a, ha, hav⟩ := h.exists_comm_not_mem_of_outer_of_card_sylow hS2 hvT hv2 hvS
    apply hav
    have := inv_mem (hvA.2 a ha)
    rwa [show (v * a * v⁻¹ * a⁻¹)⁻¹ = a * v * a⁻¹ * v⁻¹ by group] at this

theorem mem_of_mem_centralizerModCenter
    (hD : U3EndingData G L f t T R₂ U₁ s) {v : G} (hvT : v ∈ T) (hv2 : v ^ 2 = 1)
    (hvS : v ∉ szT₁ L T ⊔ zpowers t) {Y₁ Y₂ : Subgroup G} (hY : Y₁ ⊔ Y₂ = U₁)
    (hinf : Y₁ ⊓ Y₂ = ⊥) (hcomm : ∀ a ∈ Y₁, ∀ b ∈ Y₂, a * b = b * a)
    (ht₁ : ∀ a ∈ Y₁, t * a * t⁻¹ ∈ Y₂) (ht₂ : ∀ b ∈ Y₂, t * b * t⁻¹ ∈ Y₁) {P : Subgroup G}
    (hP2 : IsPGroup 2 P) (hUP : U₁ ≤ P) (hTP : T ≤ P) (hPN : P ≤ normalizer (U₁ : Set G))
    {y : G} (hyP : y ∈ P) (hy : y ∈ centralizerModCenter U₁) : y ∈ U₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hD.start
  have hU := hD.u1
  obtain ⟨htT, -⟩ := h.start_of_card_sylow hD.card_sylow
  have htP : t ∈ P := hTP htT
  have htU : t ∈ normalizer (U₁ : Set G) := hPN htP
  have hUK : U₁ ≤ centralizerModCenter U₁ := hD.le_centralizerModCenter'
  set K := centralizerModCenter U₁ ⊓ P with hKdef
  have htK : zpowers t ≤ normalizer (K : Set G) := by
    rw [zpowers_le]
    refine mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
    · obtain ⟨hx1, hx2⟩ := mem_inf.mp hx
      exact mem_inf.mpr ⟨conj_mem_centralizerModCenter htU hx1,
        mul_mem (mul_mem htP hx2) (inv_mem htP)⟩
    · obtain ⟨hx1, hx2⟩ := mem_inf.mp hx
      have h1 := conj_mem_centralizerModCenter (inv_mem htU) hx1
      have h2 : t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ ∈ P :=
        mul_mem (mul_mem (inv_mem htP) hx2) (inv_mem (inv_mem htP))
      rw [show t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x by group] at h1 h2
      exact mem_inf.mpr ⟨h1, h2⟩
  have ht_not := hD.t_not_mem_centralizerModCenter hY hinf hcomm ht₁ ht₂
  by_contra hyU
  have hlt : U₁ ⊔ zpowers t < K ⊔ zpowers t := by
    refine lt_of_le_of_ne (sup_le_sup_right (le_inf hUK hUP) _) fun heq => hyU ?_
    have hy' : y ∈ U₁ ⊔ zpowers t := heq ▸ mem_sup_left (mem_inf.mpr ⟨hy, hyP⟩)
    obtain ⟨u, hu, z, hz, rfl⟩ :=
      exists_mul_eq_of_mem_sup_of_le_normalizer ((zpowers_le (G := G)).mpr htU) hy'
    rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hz with rfl | rfl
    · rw [mul_one]
      exact hu
    · exfalso
      apply ht_not
      have := mul_mem (hUK (inv_mem hu)) hy
      rwa [inv_mul_cancel_left] at this
  have hQ2 : IsPGroup 2 (K ⊔ zpowers t : Subgroup G) :=
    hP2.to_le (sup_le inf_le_right ((zpowers_le (G := G)).mpr htP))
  obtain ⟨z, hzQ, hzH, hzN⟩ := exists_mem_normalizer_not_mem_of_lt_pGroup hQ2 hlt
  obtain ⟨k, hk, e, he, rfl⟩ := exists_mul_eq_of_mem_sup_of_le_normalizer htK hzQ
  have heH : e ∈ U₁ ⊔ zpowers t := mem_sup_right he
  have hkH : k ∉ U₁ ⊔ zpowers t := fun hm => hzH (mul_mem hm heH)
  have hkN : k ∈ normalizer ((U₁ ⊔ zpowers t : Subgroup G) : Set G) := by
    have := mul_mem hzN (inv_mem (le_normalizer heH))
    rwa [mul_inv_cancel_right] at this
  have hkt : k * t * k⁻¹ ∈ U₁ ⊔ zpowers t :=
    (mem_normalizer_iff.mp hkN t).mp (mem_sup_right (mem_zpowers t))
  obtain ⟨w, hw, hwe⟩ := hU.conj_of_mem k hkt
  have hxC : w⁻¹ * k ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc w⁻¹ * k * t = w⁻¹ * (k * t * k⁻¹) * k := by group
      _ = w⁻¹ * (w * t * w⁻¹) * k := by rw [hwe]
      _ = t * (w⁻¹ * k) := by group
  obtain ⟨hkC, hkP⟩ := mem_inf.mp hk
  have hxP : w⁻¹ * k ∈ P := mul_mem (inv_mem (hUP hw)) hkP
  have hxT : w⁻¹ * k ∈ T :=
    h.le_of_isPGroup_of_le_centralizer (hP2.to_le inf_le_left) inf_le_right (le_inf hTP h.le)
      (mem_inf.mpr ⟨hxP, hxC⟩)
  have hxK : w⁻¹ * k ∈ centralizerModCenter U₁ := mul_mem (hUK (inv_mem hw)) hkC
  have hxT₁ := hD.mem_szT₁_of_mem_centralizerModCenter hvT hv2 hvS hY hinf hcomm ht₁ ht₂ hxT hxK
  apply hkH
  have ek : k = w * (w⁻¹ * k) := by group
  rw [ek]
  exact mem_sup_left (mul_mem hw (hU.le (mem_sup_left hxT₁)))

end U3EndingData

end CFSG.SeitzReduction.RankOne
