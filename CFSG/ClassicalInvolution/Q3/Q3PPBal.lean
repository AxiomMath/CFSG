module

public import CFSG.ClassicalInvolution.Q3.Q3NMLie
public import CFSG.ClassicalInvolution.Q3.Q3OFAlphaF
public import CFSG.ClassicalInvolution.Q3.Q3OFStmt

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3PP

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution.Q3.Q3OF
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Q3.Q3W
open scoped commutatorElement

section Edge

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

structure EdgeData (K : Subgroup G) (K₁ K₂ : Subgroup G) (z₁ z₂ : G) : Prop where
  mem₁ : K₁ ∈ conjClass3 K
  mem₂ : K₂ ∈ conjClass3 K
  cls₁ : IsClassicalMember3 K₁ z₁
  cls₂ : IsClassicalMember3 K₂ z₂
  ne : z₁ ≠ z₂
  comm : Commutes K₁ K₂

namespace EdgeData

variable {K₁ K₂ : Subgroup G} {z₁ z₂ : G}

theorem sq₁ (h : EdgeData K K₁ K₂ z₁ z₂) : z₁ * z₁ = 1 :=
  Q3NT.mul_self_eq_one_of_orderOf_eq_two h.cls₁.orderOf_eq_two

theorem sq₂ (h : EdgeData K K₁ K₂ z₁ z₂) : z₂ * z₂ = 1 :=
  Q3NT.mul_self_eq_one_of_orderOf_eq_two h.cls₂.orderOf_eq_two

theorem mul_comm₁₂ (h : EdgeData K K₁ K₂ z₁ z₂) : z₁ * z₂ = z₂ * z₁ :=
  h.comm z₁ h.cls₁.mem z₂ h.cls₂.mem

theorem le_centralizer₁ (h : EdgeData K K₁ K₂ z₁ z₂) :
    K₂ ≤ Subgroup.centralizer ({z₁} : Set G) := fun y hy =>
  Subgroup.mem_centralizer_singleton_iff.mpr (h.comm z₁ h.cls₁.mem y hy).symm

theorem le_centralizer₂ (h : EdgeData K K₁ K₂ z₁ z₂) :
    K₁ ≤ Subgroup.centralizer ({z₂} : Set G) := fun y hy =>
  Subgroup.mem_centralizer_singleton_iff.mpr (h.comm y hy z₂ h.cls₂.mem)

theorem orderOf_prod (h : EdgeData K K₁ K₂ z₁ z₂) : orderOf (z₁ * z₂) = 2 := by
  have hsq : (z₁ * z₂) * (z₁ * z₂) = 1 := by
    calc z₁ * z₂ * (z₁ * z₂) = z₁ * (z₂ * z₁) * z₂ := by group
      _ = z₁ * (z₁ * z₂) * z₂ := by rw [← h.mul_comm₁₂]
      _ = (z₁ * z₁) * (z₂ * z₂) := by group
      _ = 1 := by rw [h.sq₁, h.sq₂, one_mul]
  have hne1 : z₁ * z₂ ≠ 1 := by
    intro h1
    apply h.ne
    calc z₁ = z₁ * (z₂ * z₂) := by rw [h.sq₂, mul_one]
      _ = (z₁ * z₂) * z₂ := (mul_assoc _ _ _).symm
      _ = z₂ := by rw [h1, one_mul]
  exact orderOf_eq_prime (by rw [pow_two]; exact hsq) hne1

end EdgeData

end Edge

section Balance

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}
  {K₁ K₂ : Subgroup G} {z₁ z₂ : G}

@[expose] def OddAutLayerRigidHyp : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Λ : Set (Subgroup Y)), InClass3 Λ → LieSystemMod3 Λ →
    classicalInvolutionOddCore Y = ⊥ →
    ∀ (K : Subgroup Y) (z : Y), K ∈ Λ → IsClassicalMember3 K z →
      ∀ α : MulAut Y, Odd (orderOf α) → (∀ c : Y, c * z = z * c → α c = c) → α = 1

omit
    [Finite G] [IsSimpleGroup G] in
theorem coe_conjAut_pow (Y : Subgroup G) (a : G) (ha : a ∈ Subgroup.normalizer (Y : Set G))
    (k : ℕ) (y : ↥Y) :
    ((((Q3NM.conjAut Y a ha) ^ k) y : ↥Y) : G) = a ^ k * (y : G) * (a ^ k)⁻¹ := by
  induction k generalizing y with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, MulAut.mul_apply, ih, Q3NM.conjAut_apply, pow_succ]
    group

omit
    [Finite G] [IsSimpleGroup G] in
theorem orderOf_conjAut_dvd (Y : Subgroup G) (a : G) (ha : a ∈ Subgroup.normalizer (Y : Set G)) :
    orderOf (Q3NM.conjAut Y a ha) ∣ orderOf a := by
  refine orderOf_dvd_of_pow_eq_one ?_
  ext y
  rw [coe_conjAut_pow, pow_orderOf_eq_one]
  simp

namespace EdgeData

theorem prod_mem_layer₁ (h : EdgeData K K₁ K₂ z₁ z₂) :
    z₁ * z₂ ∈ centralizingLayer (conjClass3 K) {z₁} := by
  have hK₁ : K₁ ∈ centralizingMembers (conjClass3 K) {z₁} :=
    ⟨h.mem₁, isSubnormal_le h.cls₁.subnormal⟩
  have hK₂ : K₂ ∈ centralizingMembers (conjClass3 K) {z₁} := ⟨h.mem₂, h.le_centralizer₁⟩
  exact Subgroup.mul_mem _ (le_centralizingLayer hK₁ h.cls₁.mem)
    (le_centralizingLayer hK₂ h.cls₂.mem)

theorem commute_of_mem_oddCore (hR : RouteD3Setup K z) (hnab : ∃ a b : G, a * b ≠ b * a)
    (h : EdgeData K K₁ K₂ z₁ z₂) {v g : G} (hv : v ∈ involutionOddCore (z₁ * z₂))
    (hvz : z₁ * v = v * z₁) (hg : g ∈ centralizingLayer (conjClass3 K) {z₁})
    (hgx : g * (z₁ * z₂) = (z₁ * z₂) * g) : v * g = g * v := by
  have hΩ := hR.inClass.conjInvariant
  have hO : LocalOddCentralizer3 (conjClass3 K) :=
    localOddCentralizer3_of_lieSystem lieSystemOddCentralizer3_proved hR.ih
  have hb : z₁ ∉ Subgroup.center G := fun hc =>
    Q3W.not_subset_center_of_ne_one hnab h.cls₁.ne_one (Set.singleton_subset_iff.mpr hc)
  have hcomm := commutator_mem_involutionOddCore_of_localOddCentralizer3 hΩ hO hb
    h.prod_mem_layer₁ h.orderOf_prod (r := v) (g := g)
    ⟨hv, Subgroup.mem_centralizer_singleton_iff.mpr hvz.symm⟩
    ⟨hg, Subgroup.mem_centralizer_singleton_iff.mpr hgx⟩
  rw [involutionOddCore_eq_bot_of_member hR h.mem₁ h.cls₁] at hcomm
  exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hcomm)

theorem centralizes_layer_of_oddAut (hOA : OddAutLayerRigidHyp) (hR : RouteD3Setup K z)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h : EdgeData K K₁ K₂ z₁ z₂) {v : G}
    (hvodd : Odd (orderOf v)) (hvz : z₁ * v = v * z₁)
    (hvg : ∀ g ∈ centralizingLayer (conjClass3 K) {z₁}, g * z₂ = z₂ * g → v * g = g * v) :
    ∀ y ∈ centralizingLayer (conjClass3 K) {z₁}, v * y = y * v := by
  classical
  have hΩ : ConjInvariant (conjClass3 K) := hR.inClass.conjInvariant
  set Y₁ : Subgroup G := centralizingLayer (conjClass3 K) {z₁} with hY₁
  have hb : ¬ ({z₁} : Set G) ⊆ Subgroup.center G :=
    Q3W.not_subset_center_of_ne_one hnab h.cls₁.ne_one
  have hvC : v ∈ Subgroup.centralizer ({z₁} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hvz.symm
  have hvN : v ∈ Subgroup.normalizer (Y₁ : Set G) := mem_normalizer_centralizingLayer hΩ hvC
  have hK₁mem : K₁ ∈ centralizingMembers (conjClass3 K) {z₁} :=
    ⟨h.mem₁, isSubnormal_le h.cls₁.subnormal⟩
  have hK₂mem : K₂ ∈ centralizingMembers (conjClass3 K) {z₁} := ⟨h.mem₂, h.le_centralizer₁⟩
  have hK₂Y : K₂ ≤ Y₁ := le_centralizingLayer hK₂mem
  have hz₂Y : z₂ ∈ Y₁ := hK₂Y h.cls₂.mem
  have hcls : InClass3 (restrictFamily (centralizingMembers (conjClass3 K) {z₁}) Y₁) :=
    inClass3_local hR.inClass {z₁} ⟨K₁, hK₁mem⟩
  have hLie : LieSystemMod3 (restrictFamily (centralizingMembers (conjClass3 K) {z₁}) Y₁) :=
    hR.ih {z₁} hb
  have hO1 : classicalInvolutionOddCore ↥Y₁ = ⊥ := by
    have h1 : oddCoreIn Y₁ ≤ involutionOddCore z₁ := oddCoreIn_centralizingLayer_le hΩ z₁
    rw [involutionOddCore_eq_bot_of_member hR h.mem₁ h.cls₁] at h1
    have h2 : (classicalInvolutionOddCore ↥Y₁).map Y₁.subtype = ⊥ := le_bot_iff.mp h1
    rw [Subgroup.map_eq_bot_iff, Subgroup.ker_subtype] at h2
    exact le_bot_iff.mp h2
  have hKmem : K₂.subgroupOf Y₁ ∈ restrictFamily (centralizingMembers (conjClass3 K) {z₁}) Y₁ :=
    ⟨K₂, hK₂mem, hK₂Y, rfl⟩
  let α : MulAut ↥Y₁ := Q3NM.conjAut Y₁ v hvN
  have hα : ∀ y : ↥Y₁, ((α y : ↥Y₁) : G) = v * (y : G) * v⁻¹ := fun y => rfl
  have hodd : Odd (orderOf α) := Odd.of_dvd_nat hvodd (orderOf_conjAut_dvd Y₁ v hvN)
  have hfix : ∀ c : ↥Y₁, c * ⟨z₂, hz₂Y⟩ = ⟨z₂, hz₂Y⟩ * c → α c = c := by
    intro c hc
    have hvc := hvg c c.2 (congrArg Subtype.val hc)
    apply Subtype.ext
    rw [hα]
    calc v * (c : G) * v⁻¹ = (c * v) * v⁻¹ := by rw [hvc]
      _ = c := by group
  have hα1 : α = 1 := hOA ↥Y₁ _ hcls hLie hO1 (K₂.subgroupOf Y₁) ⟨z₂, hz₂Y⟩ hKmem
    (h.cls₂.subgroupOf hK₂Y) α hodd hfix
  intro y hy
  have := congrArg (fun a : MulAut ↥Y₁ => ((a ⟨y, hy⟩ : ↥Y₁) : G)) hα1
  simp only [hα, MulAut.one_apply] at this
  calc v * y = (v * y * v⁻¹) * v := by group
    _ = y * v := by rw [this]

theorem commute_layer_of_oddAut (hOA : OddAutLayerRigidHyp) (hR : RouteD3Setup K z)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h : EdgeData K K₁ K₂ z₁ z₂) {v : G}
    (hv : v ∈ involutionOddCore (z₁ * z₂)) (hvz : z₁ * v = v * z₁) :
    ∀ y ∈ centralizingLayer (conjClass3 K) {z₁}, v * y = y * v := by
  have hvodd : Odd (orderOf v) :=
    Odd.of_dvd_nat (odd_card_oddCoreIn _) (Subgroup.orderOf_dvd_natCard _ hv)
  refine h.centralizes_layer_of_oddAut hOA hR hnab hvodd hvz fun g hg hgz₂ => ?_
  have hcz₁ : g ∈ Subgroup.centralizer ({z₁} : Set G) := centralizingLayer_le_centralizer _ _ hg
  have hg₁ : g * z₁ = z₁ * g := Subgroup.mem_centralizer_singleton_iff.mp hcz₁
  have hgx : g * (z₁ * z₂) = (z₁ * z₂) * g := by
    calc g * (z₁ * z₂) = (g * z₁) * z₂ := by rw [mul_assoc]
      _ = (z₁ * g) * z₂ := by rw [hg₁]
      _ = z₁ * (g * z₂) := by rw [mul_assoc]
      _ = z₁ * (z₂ * g) := by rw [hgz₂]
      _ = (z₁ * z₂) * g := by rw [mul_assoc]
  exact h.commute_of_mem_oddCore hR hnab hv hvz hg hgx

theorem oddCore_inf_centralizer_eq_bot (hOA : OddAutLayerRigidHyp) (hR : RouteD3Setup K z)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h : EdgeData K K₁ K₂ z₁ z₂) :
    involutionOddCore (z₁ * z₂) ⊓ Subgroup.centralizer ({z₁} : Set G) = ⊥ := by
  classical
  have hΩ : ConjInvariant (conjClass3 K) := hR.inClass.conjInvariant
  set Y₁ : Subgroup G := centralizingLayer (conjClass3 K) {z₁} with hY₁
  set V : Subgroup G := involutionOddCore (z₁ * z₂) ⊓ Subgroup.centralizer ({z₁} : Set G)
    with hV
  set Ĉ : Subgroup G := Subgroup.centralizer (Y₁ : Set G) with hĈ
  have hK₁mem : K₁ ∈ centralizingMembers (conjClass3 K) {z₁} :=
    ⟨h.mem₁, isSubnormal_le h.cls₁.subnormal⟩
  have hK₂mem : K₂ ∈ centralizingMembers (conjClass3 K) {z₁} := ⟨h.mem₂, h.le_centralizer₁⟩
  have hz₁Y : z₁ ∈ Y₁ := le_centralizingLayer hK₁mem h.cls₁.mem
  have hz₂Y : z₂ ∈ Y₁ := le_centralizingLayer hK₂mem h.cls₂.mem
  have hVĈ : V ≤ Ĉ := by
    intro v hv
    rw [hĈ, Subgroup.mem_centralizer_iff]
    intro y hy
    have hvz : z₁ * v = v * z₁ := (Subgroup.mem_centralizer_singleton_iff.mp hv.2).symm
    exact (h.commute_layer_of_oddAut hOA hR hnab hv.1 hvz y hy).symm
  have hĈz₁ : ∀ c ∈ Ĉ, c * z₁ = z₁ * c := fun c hc =>
    (Subgroup.mem_centralizer_iff.mp hc z₁ hz₁Y).symm
  have hĈz₂ : ∀ c ∈ Ĉ, c * z₂ = z₂ * c := fun c hc =>
    (Subgroup.mem_centralizer_iff.mp hc z₂ hz₂Y).symm
  have hnormV : Ĉ ≤ Subgroup.normalizer (V : Set G) := by
    intro c hc
    have hcx : c ∈ Subgroup.centralizer ({z₁ * z₂} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc c * (z₁ * z₂) = (c * z₁) * z₂ := by rw [mul_assoc]
        _ = (z₁ * c) * z₂ := by rw [hĈz₁ c hc]
        _ = z₁ * (c * z₂) := by rw [mul_assoc]
        _ = z₁ * (z₂ * c) := by rw [hĈz₂ c hc]
        _ = (z₁ * z₂) * c := by rw [mul_assoc]
    have hcz₁ : c ∈ Subgroup.centralizer ({z₁} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hĈz₁ c hc)
    have h1 : c ∈ Subgroup.normalizer (involutionOddCore (z₁ * z₂) : Set G) :=
      normalizer_oddCoreIn _ hcx
    have h2 : c ∈ Subgroup.normalizer (Subgroup.centralizer ({z₁} : Set G) : Set G) :=
      Subgroup.le_normalizer hcz₁
    rw [Subgroup.mem_normalizer_iff] at h1 h2 ⊢
    intro y
    exact ⟨fun hy => ⟨(h1 y).mp hy.1, (h2 y).mp hy.2⟩,
      fun hy => ⟨(h1 y).mpr hy.1, (h2 y).mpr hy.2⟩⟩
  have hoddV : Odd (Nat.card V) :=
    Odd.of_dvd_nat (odd_card_oddCoreIn (Subgroup.centralizer ({z₁ * z₂} : Set G)))
      (Subgroup.card_dvd_of_le inf_le_left)
  have h1 : V ≤ oddCoreIn Ĉ := le_oddCoreIn_of_normalizes hVĈ hnormV hoddV
  have hĈH : Ĉ ≤ Subgroup.centralizer ({z₁} : Set G) := fun c hc =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hĈz₁ c hc)
  have hconj : ∀ t ∈ Subgroup.centralizer ({z₁} : Set G), ∀ c ∈ Ĉ, t * c * t⁻¹ ∈ Ĉ := by
    intro t ht c hc
    rw [hĈ, Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : t⁻¹ * y * t ∈ Y₁ := by
      have := conj_mem_centralizingLayer hΩ ((Subgroup.centralizer ({z₁} : Set G)).inv_mem ht) hy
      simpa using this
    have hcy := Subgroup.mem_centralizer_iff.mp hc _ hy'
    calc y * (t * c * t⁻¹) = t * ((t⁻¹ * y * t) * c) * t⁻¹ := by group
      _ = t * (c * (t⁻¹ * y * t)) * t⁻¹ := by rw [hcy]
      _ = (t * c * t⁻¹) * y := by group
  have hnormĈ : Subgroup.centralizer ({z₁} : Set G) ≤ Subgroup.normalizer (Ĉ : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro c
    refine ⟨fun hc => hconj t ht c hc, fun hc => ?_⟩
    have := hconj t⁻¹ ((Subgroup.centralizer ({z₁} : Set G)).inv_mem ht) _ hc
    simpa [mul_assoc] using this
  have hsub : IsSubnormal Ĉ (Subgroup.centralizer ({z₁} : Set G)) :=
    isSubnormal_of_normal_subgroupOf hĈH
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hĈH).mpr hnormĈ)
  have h2 : oddCoreIn Ĉ ≤ oddCoreIn (Subgroup.centralizer ({z₁} : Set G)) :=
    oddCoreIn_le_of_isSubnormal hsub
  have h3 : oddCoreIn (Subgroup.centralizer ({z₁} : Set G)) = ⊥ :=
    involutionOddCore_eq_bot_of_member hR h.mem₁ h.cls₁
  exact le_bot_iff.mp (h1.trans (h2.trans h3.le))

end EdgeData

end Balance

end CFSG.ClassicalInvolution.Q3.Q3PP
