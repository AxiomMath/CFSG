module

public import CFSG.RankThree.Literature.FSmithForm
public import CFSG.GroupTheory.ExtraspecialCentralizerInnerAut
public import CFSG.RankThree.PartOne.S9.OddCore.TorsionBridge
public import CFSG.LocalAnalysis.ComponentClassification.AS81Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith
open scoped commutatorElement

structure XSub (G : Type) [Group G] where
  Q₁ : Subgroup G
  z : G
  extraspecial : IsExtraspecialPGroup 2 Q₁
  center_eq : centerIn Q₁ = zpowers z

namespace XSub

variable {G : Type} [Group G] (D : XSub G)

abbrev N : Subgroup G := normalizer (D.Q₁ : Set G)

abbrev QN : Subgroup D.N := D.Q₁.subgroupOf D.N

theorem le_N : D.Q₁ ≤ D.N := le_normalizer

theorem QN_normal : D.QN.Normal := normal_in_normalizer

theorem QN_extraspecial : IsExtraspecialPGroup 2 D.QN :=
  CFSG.RankThree.PartOne.Torsion37.isExtraspecialPGroup_of_mulEquiv
    (subgroupOfEquivOfLe D.le_N).symm D.extraspecial

instance instModuleQt : Module (ZMod 2) (Additive (Abelianization D.QN)) :=
  CFSG.GroupTheory.extraspecialQuotientModule D.QN_extraspecial

abbrev Qt : Type _ := Additive (Abelianization D.QN)

@[expose] def ofG (a : G) (ha : a ∈ D.Q₁) : D.QN := ⟨⟨a, D.le_N ha⟩, ha⟩

@[simp] theorem coe_ofG (a : G) (ha : a ∈ D.Q₁) : ((D.ofG a ha : D.N) : G) = a := rfl

theorem z_mem_center : D.z ∈ centerIn D.Q₁ := by
  rw [D.center_eq]
  exact mem_zpowers _

theorem z_mem : D.z ∈ D.Q₁ := D.z_mem_center.1

theorem z_comm {a : G} (ha : a ∈ D.Q₁) : a * D.z = D.z * a :=
  ((mem_centralizer_iff.mp D.z_mem_center.2) a ha)

theorem mem_center_iff_mem_zpowers {a : G} (ha : a ∈ D.Q₁) :
    (∀ b ∈ D.Q₁, a * b = b * a) ↔ a ∈ zpowers D.z := by
  rw [← D.center_eq]
  constructor
  · intro h
    exact ⟨ha, mem_centralizer_iff.mpr fun b hb => (h b hb).symm⟩
  · intro h b hb
    exact ((mem_centralizer_iff.mp h.2) b hb).symm

theorem card_zpowers_z : Nat.card (zpowers D.z) = 2 := by
  rw [← D.center_eq]
  have e : centerIn D.Q₁ = (center D.Q₁).map D.Q₁.subtype := by
    ext a
    constructor
    · rintro ⟨ha, hc⟩
      exact ⟨⟨a, ha⟩, mem_center_iff.mpr fun b => Subtype.ext
        ((mem_centralizer_iff.mp hc) b b.2), rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b.2, mem_centralizer_iff.mpr fun c hc =>
        congrArg Subtype.val ((mem_center_iff.mp hb) ⟨c, hc⟩)⟩
  rw [e, card_map_of_injective D.Q₁.subtype_injective]
  exact D.extraspecial.2.2.2

theorem orderOf_z : orderOf D.z = 2 := by
  rw [← Nat.card_zpowers]
  exact D.card_zpowers_z

theorem z_mul_z : D.z * D.z = 1 := by
  rw [← pow_two, ← D.orderOf_z, pow_orderOf_eq_one]

theorem z_ne_one : D.z ≠ 1 := by
  intro h
  have := D.orderOf_z
  rw [h, orderOf_one] at this
  exact absurd this (by norm_num)

theorem mem_zpowers_z_iff {a : G} : a ∈ zpowers D.z ↔ a = 1 ∨ a = D.z := by
  constructor
  · rintro ⟨k, rfl⟩
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · left
      change D.z ^ (m + m) = 1
      rw [← two_mul, zpow_mul, zpow_two, D.z_mul_z, one_zpow]
    · right
      change D.z ^ (2 * m + 1) = D.z
      rw [zpow_add_one, zpow_mul, zpow_two, D.z_mul_z, one_zpow, one_mul]
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact mem_zpowers _

open Classical in
@[expose] noncomputable def cl (a : G) : D.Qt :=
  if ha : a ∈ D.Q₁ then Additive.ofMul (Abelianization.of (D.ofG a ha)) else 0

theorem cl_of_mem {a : G} (ha : a ∈ D.Q₁) :
    D.cl a = Additive.ofMul (Abelianization.of (D.ofG a ha)) := by
  simp only [cl, ha, ↓reduceDIte]

theorem cl_mul {a b : G} (ha : a ∈ D.Q₁) (hb : b ∈ D.Q₁) : D.cl (a * b) = D.cl a + D.cl b := by
  rw [D.cl_of_mem ha, D.cl_of_mem hb, D.cl_of_mem (mul_mem ha hb), ← ofMul_of_mul]
  rfl

theorem cl_one : D.cl 1 = 0 := by
  rw [D.cl_of_mem (one_mem _)]
  exact congrArg Additive.ofMul (map_one Abelianization.of)

theorem cl_inv {a : G} (ha : a ∈ D.Q₁) : D.cl a⁻¹ = D.cl a := by
  have h := D.cl_mul (inv_mem ha) ha
  rw [inv_mul_cancel, D.cl_one] at h
  have h2 : D.cl a⁻¹ + D.cl a + D.cl a = D.cl a := by rw [← h, zero_add]
  rwa [add_assoc, ZModModule.add_self, add_zero] at h2

theorem cl_eq_zero_iff {a : G} (ha : a ∈ D.Q₁) : D.cl a = 0 ↔ a ∈ zpowers D.z := by
  rw [D.cl_of_mem ha, ofMul_of_eq_zero_iff D.QN_extraspecial, mem_center_iff,
    ← D.mem_center_iff_mem_zpowers ha]
  constructor
  · intro h b hb
    exact (congrArg (fun w : D.QN => ((w : D.N) : G)) (h (D.ofG b hb))).symm
  · intro h w
    exact Subtype.ext (Subtype.ext (h _ w.2).symm)

theorem cl_z : D.cl D.z = 0 := (D.cl_eq_zero_iff D.z_mem).mpr (mem_zpowers _)

theorem exists_cl (v : D.Qt) : ∃ a ∈ D.Q₁, D.cl a = v := by
  obtain ⟨w, rfl⟩ := exists_ofMul_of v
  have hw : ((w : D.N) : G) ∈ D.Q₁ := w.2
  exact ⟨((w : D.N) : G), hw, by rw [D.cl_of_mem hw]; rfl⟩

theorem cl_eq_cl_iff {a b : G} (ha : a ∈ D.Q₁) (hb : b ∈ D.Q₁) :
    D.cl a = D.cl b ↔ a⁻¹ * b ∈ zpowers D.z := by
  rw [← D.cl_eq_zero_iff (mul_mem (inv_mem ha) hb), D.cl_mul (inv_mem ha) hb, D.cl_inv ha]
  constructor
  · intro h
    rw [h]
    exact ZModModule.add_self _
  · intro h
    have h' := congrArg (· + D.cl b) h
    simp only [zero_add] at h'
    rw [← h', add_assoc, ZModModule.add_self, add_zero]

theorem conj_mem {g : G} (hg : g ∈ D.N) {a : G} (ha : a ∈ D.Q₁) : g * a * g⁻¹ ∈ D.Q₁ :=
  (mem_normalizer_iff.mp hg a).mp ha

@[expose] noncomputable def clSub (X : Subgroup G) : Submodule (ZMod 2) D.Qt :=
  Submodule.span (ZMod 2) {v | ∃ a ∈ X, a ∈ D.Q₁ ∧ D.cl a = v}

theorem mem_clSub_iff {X : Subgroup G} {v : D.Qt} :
    v ∈ D.clSub X ↔ ∃ a ∈ X, a ∈ D.Q₁ ∧ D.cl a = v := by
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem v hv => exact hv
    | zero => exact ⟨1, X.one_mem, D.Q₁.one_mem, D.cl_one⟩
    | add v w _ _ hv hw =>
      obtain ⟨a, haX, haQ, rfl⟩ := hv
      obtain ⟨b, hbX, hbQ, rfl⟩ := hw
      exact ⟨a * b, X.mul_mem haX hbX, D.Q₁.mul_mem haQ hbQ, D.cl_mul haQ hbQ⟩
    | smul c v _ hv =>
      obtain ⟨a, haX, haQ, rfl⟩ := hv
      rcases zmod2_cases c with rfl | rfl
      · exact ⟨1, X.one_mem, D.Q₁.one_mem, by rw [zero_smul, D.cl_one]⟩
      · exact ⟨a, haX, haQ, by rw [one_smul]⟩
  · intro hv
    exact Submodule.subset_span hv

theorem cl_mem_clSub {X : Subgroup G} {a : G} (haX : a ∈ X) (haQ : a ∈ D.Q₁) :
    D.cl a ∈ D.clSub X :=
  D.mem_clSub_iff.mpr ⟨a, haX, haQ, rfl⟩

theorem clSub_mono {X Y : Subgroup G} (h : X ≤ Y) : D.clSub X ≤ D.clSub Y := by
  intro v hv
  obtain ⟨a, haX, haQ, rfl⟩ := D.mem_clSub_iff.mp hv
  exact D.cl_mem_clSub (h haX) haQ

@[expose] noncomputable def clPre (W : Submodule (ZMod 2) D.Qt) : Subgroup G where
  carrier := {a | a ∈ D.Q₁ ∧ D.cl a ∈ W}
  mul_mem' := fun {a b} ha hb =>
    ⟨D.Q₁.mul_mem ha.1 hb.1, by rw [D.cl_mul ha.1 hb.1]; exact W.add_mem ha.2 hb.2⟩
  one_mem' := ⟨D.Q₁.one_mem, by rw [D.cl_one]; exact W.zero_mem⟩
  inv_mem' := fun {a} ha => ⟨D.Q₁.inv_mem ha.1, by rw [D.cl_inv ha.1]; exact ha.2⟩

theorem mem_clPre {W : Submodule (ZMod 2) D.Qt} {a : G} :
    a ∈ D.clPre W ↔ a ∈ D.Q₁ ∧ D.cl a ∈ W := Iff.rfl

theorem z_mem_clPre (W : Submodule (ZMod 2) D.Qt) : D.z ∈ D.clPre W :=
  ⟨D.z_mem, by rw [D.cl_z]; exact W.zero_mem⟩

theorem clPre_clSub {X : Subgroup G} (hX : X ≤ D.Q₁) (hz : D.z ∈ X) :
    D.clPre (D.clSub X) = X := by
  ext a
  constructor
  · rintro ⟨haQ, hv⟩
    obtain ⟨b, hbX, hbQ, hba⟩ := D.mem_clSub_iff.mp hv
    have h := (D.cl_eq_cl_iff hbQ haQ).mp hba
    rcases D.mem_zpowers_z_iff.mp h with h1 | h1
    · have e : a = b := by
        calc a = b * (b⁻¹ * a) := by group
          _ = b := by rw [h1, mul_one]
      rw [e]
      exact hbX
    · have e : a = b * D.z := by
        calc a = b * (b⁻¹ * a) := by group
          _ = b * D.z := by rw [h1]
      rw [e]
      exact X.mul_mem hbX hz
  · intro ha
    exact ⟨hX ha, D.cl_mem_clSub ha (hX ha)⟩

theorem card_clPre (W : Submodule (ZMod 2) D.Qt) : Nat.card (D.clPre W) = 2 * Nat.card W := by
  classical
  let f : D.clPre W →* Multiplicative W :=
    { toFun := fun a => Multiplicative.ofAdd ⟨D.cl a, a.2.2⟩
      map_one' := Multiplicative.toAdd.injective (Subtype.ext D.cl_one)
      map_mul' := fun a b => Multiplicative.toAdd.injective (Subtype.ext (D.cl_mul a.2.1 b.2.1)) }
  have hsurj : Function.Surjective f := by
    intro w
    obtain ⟨a, ha, haw⟩ := D.exists_cl ((Multiplicative.toAdd w : W) : D.Qt)
    exact ⟨⟨a, ha, haw ▸ (Multiplicative.toAdd w).2⟩,
      Multiplicative.toAdd.injective (Subtype.ext haw)⟩
  have hmem : ∀ a : D.clPre W, a ∈ f.ker ↔ (a : G) = 1 ∨ (a : G) = D.z := by
    intro a
    rw [MonoidHom.mem_ker, ← D.mem_zpowers_z_iff, ← D.cl_eq_zero_iff a.2.1]
    constructor
    · intro h
      exact congrArg Subtype.val (congrArg Multiplicative.toAdd h)
    · intro h
      exact Multiplicative.toAdd.injective (Subtype.ext h)
  have hker : Nat.card f.ker = 2 := by
    let z' : f.ker := ⟨⟨D.z, D.z_mem_clPre W⟩, (hmem _).mpr (Or.inr rfl)⟩
    refine (Nat.card_eq_two_iff' (1 : f.ker)).mpr ⟨z', fun h => D.z_ne_one ?_, fun y hy => ?_⟩
    · exact congrArg (fun w : f.ker => ((w : D.clPre W) : G)) h
    · rcases (hmem y).mp y.2 with h | h
      · exact absurd (Subtype.ext (Subtype.ext h)) hy
      · exact Subtype.ext (Subtype.ext h)
  rw [card_eq_card_quotient_mul_card_subgroup f.ker, hker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hsurj).toEquiv, mul_comm]
  rfl

theorem clSub_sup {X Y : Subgroup G} (hX : X ≤ D.Q₁) (hY : Y ≤ D.Q₁) :
    D.clSub (X ⊔ Y) = D.clSub X ⊔ D.clSub Y := by
  refine le_antisymm (fun v hv => ?_) (sup_le (D.clSub_mono le_sup_left)
    (D.clSub_mono le_sup_right))
  obtain ⟨a, ha, -, rfl⟩ := D.mem_clSub_iff.mp hv
  have key : ∀ a ∈ X ⊔ Y, a ∈ D.Q₁ ∧ D.cl a ∈ D.clSub X ⊔ D.clSub Y := by
    intro a ha
    rw [sup_eq_closure] at ha
    induction ha using Subgroup.closure_induction with
    | mem a ha =>
      rcases ha with ha | ha
      · exact ⟨hX ha, Submodule.mem_sup_left (D.cl_mem_clSub ha (hX ha))⟩
      · exact ⟨hY ha, Submodule.mem_sup_right (D.cl_mem_clSub ha (hY ha))⟩
    | one => exact ⟨one_mem _, by rw [D.cl_one]; exact Submodule.zero_mem _⟩
    | mul a b _ _ iha ihb =>
      refine ⟨mul_mem iha.1 ihb.1, ?_⟩
      rw [D.cl_mul iha.1 ihb.1]
      exact Submodule.add_mem _ iha.2 ihb.2
    | inv a _ iha => exact ⟨inv_mem iha.1, by rw [D.cl_inv iha.1]; exact iha.2⟩
  exact (key a ha).2

theorem clSub_inf_eq_bot {X Y : Subgroup G} (hY : Y ≤ D.Q₁) (hzY : D.z ∈ Y)
    (h : X ⊓ Y ≤ zpowers D.z) : D.clSub X ⊓ D.clSub Y = ⊥ := by
  refine eq_bot_iff.mpr fun v hv => ?_
  obtain ⟨a, haX, haQ, rfl⟩ := D.mem_clSub_iff.mp hv.1
  have haY : a ∈ Y := by
    have h1 := hv.2
    rw [← D.clPre_clSub hY hzY]
    exact ⟨haQ, h1⟩
  exact (Submodule.mem_bot _).mpr ((D.cl_eq_zero_iff haQ).mpr (h ⟨haX, haY⟩))

variable [Finite G]

noncomputable abbrev q : QuadraticForm (ZMod 2) D.Qt := extraspecialQuadForm D.QN_extraspecial

theorem q_nondegenerate : D.q.polarBilin.Nondegenerate :=
  extraspecialQuadForm_nondegenerate D.QN_extraspecial

theorem q_cl_eq_zero_iff {a : G} (ha : a ∈ D.Q₁) : D.q (D.cl a) = 0 ↔ a ^ 2 = 1 := by
  rw [D.cl_of_mem ha]
  change extraspecialQuadForm D.QN_extraspecial (Additive.ofMul (Abelianization.of _)) = 0 ↔ _
  rw [extraspecialQuadForm_apply]
  have e : (D.ofG a ha) ^ 2 = 1 ↔ a ^ 2 = 1 := by
    constructor
    · intro h
      have := congrArg (fun w : D.QN => ((w : D.N) : G)) h
      simpa using this
    · intro h
      exact Subtype.ext (Subtype.ext (by simpa using h))
  split_ifs with h
  · exact ⟨fun _ => e.mp h, fun _ => rfl⟩
  · exact ⟨fun h' => absurd h' (by decide), fun h' => absurd (e.mpr h') h⟩

theorem polar_cl_eq_zero_iff {a b : G} (ha : a ∈ D.Q₁) (hb : b ∈ D.Q₁) :
    polar D.q (D.cl a) (D.cl b) = 0 ↔ a * b = b * a := by
  rw [D.cl_of_mem ha, D.cl_of_mem hb, polar_extraspecialQuadForm_eq_zero_iff]
  constructor
  · intro h
    have := congrArg (fun w : D.QN => ((w : D.N) : G)) h
    simpa using this
  · intro h
    exact Subtype.ext (Subtype.ext (by simpa using h))

theorem polar_clSub_eq_zero {X Y : Subgroup G} (h : ∀ a ∈ X, ∀ b ∈ Y, a * b = b * a)
    {v w : D.Qt} (hv : v ∈ D.clSub X) (hw : w ∈ D.clSub Y) : polar D.q v w = 0 := by
  obtain ⟨a, haX, haQ, rfl⟩ := D.mem_clSub_iff.mp hv
  obtain ⟨b, hbY, hbQ, rfl⟩ := D.mem_clSub_iff.mp hw
  exact (D.polar_cl_eq_zero_iff haQ hbQ).mpr (h a haX b hbY)

theorem eq_zero_of_q_eq_zero {X : Subgroup G}
    (h : ∀ a ∈ X, a ∈ D.Q₁ → a ^ 2 = 1 → a ∈ zpowers D.z) {v : D.Qt} (hv : v ∈ D.clSub X)
    (hq : D.q v = 0) : v = 0 := by
  obtain ⟨a, haX, haQ, rfl⟩ := D.mem_clSub_iff.mp hv
  exact (D.cl_eq_zero_iff haQ).mpr (h a haX haQ ((D.q_cl_eq_zero_iff haQ).mp hq))

noncomputable abbrev O : Subgroup (D.Qt ≃ₗ[ZMod 2] D.Qt) :=
  TauCeti.QuadraticMap.orthogonalGroup D.q

@[expose] noncomputable def ρ : D.N →* D.O := extraspecialConjOrth D.QN_extraspecial D.QN_normal

theorem ρ_cl (g : D.N) {a : G} (ha : a ∈ D.Q₁) :
    ((D.ρ g : D.O) : D.Qt ≃ₗ[ZMod 2] D.Qt) (D.cl a) = D.cl ((g : G) * a * (g : G)⁻¹) := by
  rw [D.cl_of_mem ha, D.cl_of_mem (D.conj_mem g.2 ha)]
  change Additive.ofMul (Abelianization.of (conjAut D.QN_normal g (D.ofG a ha))) = _
  congr 2

theorem ρ_eq_one_of_mem {g : D.N} (hg : (g : G) ∈ D.Q₁) : D.ρ g = 1 := by
  refine Subtype.ext (LinearEquiv.ext fun v => ?_)
  obtain ⟨a, ha, rfl⟩ := D.exists_cl v
  rw [D.ρ_cl g ha]
  change D.cl ((g : G) * a * (g : G)⁻¹) = D.cl a
  rw [D.cl_mul (mul_mem hg ha) (inv_mem hg), D.cl_mul hg ha, D.cl_inv hg,
    add_comm (D.cl _) (D.cl a), add_assoc, ZModModule.add_self, add_zero]

theorem ρ_eq_one_of_mem_centralizer {g : D.N} (hg : (g : G) ∈ centralizer (D.Q₁ : Set G)) :
    D.ρ g = 1 := by
  refine Subtype.ext (LinearEquiv.ext fun v => ?_)
  obtain ⟨a, ha, rfl⟩ := D.exists_cl v
  rw [D.ρ_cl g ha]
  change D.cl ((g : G) * a * (g : G)⁻¹) = D.cl a
  rw [← mem_centralizer_iff.mp hg a ha, mul_inv_cancel_right]

theorem exists_mem_of_ρ_eq_one {g : D.N} (hg : D.ρ g = 1) :
    ∃ c ∈ D.Q₁, c⁻¹ * (g : G) ∈ centralizer (D.Q₁ : Set G) := by
  classical
  have hQ := D.QN_extraspecial
  have hQn := D.QN_normal
  have hfix : ∀ x : D.QN, (conjAut hQn g x) * x⁻¹ ∈ center D.QN := by
    intro x
    have h := congrArg (fun r : D.O => (r : D.Qt ≃ₗ[ZMod 2] D.Qt)
      (Additive.ofMul (Abelianization.of x))) hg
    simp only [OneMemClass.coe_one, LinearEquiv.coe_one, id] at h
    change Additive.ofMul (Abelianization.of (conjAut hQn g x)) =
      Additive.ofMul (Abelianization.of x) at h
    rw [← ofMul_of_eq_zero_iff hQ, ofMul_of_mul, h, ← ofMul_of_mul, mul_inv_cancel, map_one]
    rfl
  let μ : D.QN →* Multiplicative (ZMod 2) :=
    { toFun := fun x => Multiplicative.ofAdd (ind (conjAut hQn g x * x⁻¹))
      map_one' := by
        rw [map_one, inv_one, mul_one, ind_one]
        rfl
      map_mul' := fun x y => by
        rw [ind_conj_mul_inv_mul hQ hQn hfix, ofAdd_add] }
  let μ' : D.Qt →+ ZMod 2 := MonoidHom.toAdditive (Abelianization.lift μ)
  have : Module.Finite (ZMod 2) D.Qt := Module.Finite.of_finite
  obtain ⟨u, hu⟩ := (LinearMap.BilinForm.toDual (extraspecialQuadForm hQ).polarBilin
    (extraspecialQuadForm_nondegenerate hQ)).surjective (AddMonoidHom.toZModLinearMap 2 μ')
  obtain ⟨c, rfl⟩ := exists_ofMul_of u
  have key : ∀ x : D.QN, conjAut hQn g x * x⁻¹ = ⁅c, x⁆ := by
    intro x
    have h := LinearMap.congr_fun hu (Additive.ofMul (Abelianization.of x))
    rw [LinearMap.BilinForm.toDual_def, polarBilin_apply_apply,
      polar_extraspecialQuadForm_apply] at h
    have h' : ind ⁅c, x⁆ = ind (conjAut hQn g x * x⁻¹) := h
    by_contra hne
    have hc1 := commutatorElement_mem_center hQ c x
    by_cases ha : conjAut hQn g x * x⁻¹ = 1
    · rw [ha, ind_one, ind_eq_zero_iff] at h'
      exact hne (ha.trans h'.symm)
    · by_cases hb : ⁅c, x⁆ = 1
      · rw [hb, ind_one, eq_comm, ind_eq_zero_iff] at h'
        exact ha h'
      · exact hne (eq_of_mem_center hQ (hfix x) hc1 ha hb)
  refine ⟨((c : D.N) : G), c.2, mem_centralizer_iff.mpr fun y hy => ?_⟩
  have h1 := congrArg (fun w : D.QN => ((w : D.N) : G)) (key (D.ofG y hy))
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjAut_apply, commutatorElement_def,
    coe_ofG] at h1
  have h2 : (g : G) * y * (g : G)⁻¹ = ((c : D.N) : G) * y * ((c : D.N) : G)⁻¹ := by
    have := congrArg (· * y) h1
    simp only [inv_mul_cancel_right] at this
    exact this
  calc y * (((c : D.N) : G)⁻¹ * g) =
        ((c : D.N) : G)⁻¹ * (((c : D.N) : G) * y * ((c : D.N) : G)⁻¹) * g := by group
    _ = ((c : D.N) : G)⁻¹ * ((g : G) * y * (g : G)⁻¹) * g := by rw [h2]
    _ = ((c : D.N) : G)⁻¹ * g * y := by group

theorem ρ_eq_one_iff (g : D.N) :
    D.ρ g = 1 ↔ ∃ c ∈ D.Q₁, c⁻¹ * (g : G) ∈ centralizer (D.Q₁ : Set G) := by
  refine ⟨D.exists_mem_of_ρ_eq_one, fun ⟨c, hc, hcg⟩ => ?_⟩
  have hcN : c ∈ D.N := D.le_N hc
  have hdN : c⁻¹ * (g : G) ∈ D.N := mul_mem (inv_mem hcN) g.2
  have e : g = ⟨c, hcN⟩ * ⟨c⁻¹ * (g : G), hdN⟩ := Subtype.ext (by simp)
  rw [e, map_mul, D.ρ_eq_one_of_mem (g := ⟨c, hcN⟩) hc,
    D.ρ_eq_one_of_mem_centralizer (g := ⟨c⁻¹ * (g : G), hdN⟩) hcg, one_mul]

theorem card_submodule (W : Submodule (ZMod 2) D.Qt) :
    Nat.card W = 2 ^ finrank (ZMod 2) W := by
  have : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

theorem finrank_clSub {X : Subgroup G} (hX : X ≤ D.Q₁) (hz : D.z ∈ X) {n : ℕ}
    (hcard : Nat.card X = 2 ^ (n + 1)) : finrank (ZMod 2) (D.clSub X) = n := by
  have h := D.card_clPre (D.clSub X)
  rw [D.clPre_clSub hX hz, hcard, D.card_submodule, pow_succ, mul_comm] at h
  exact Nat.pow_right_injective le_rfl (Nat.eq_of_mul_eq_mul_left (by norm_num) h).symm

theorem finrank_Qt {n : ℕ} (hcard : Nat.card D.Q₁ = 2 ^ (n + 1)) :
    finrank (ZMod 2) D.Qt = n := by
  have htop : D.clSub D.Q₁ = ⊤ := by
    refine eq_top_iff.mpr fun v _ => ?_
    obtain ⟨a, ha, rfl⟩ := D.exists_cl v
    exact D.cl_mem_clSub ha ha
  rw [← finrank_top (ZMod 2) D.Qt, ← htop]
  exact D.finrank_clSub le_rfl D.z_mem hcard

theorem map_ρ_clSub (g : D.N) (X : Subgroup G) :
    (D.clSub X).map ((D.ρ g : D.O) : D.Qt ≃ₗ[ZMod 2] D.Qt).toLinearMap =
      D.clSub (X.map (MulAut.conj (g : G)).toMonoidHom) := by
  ext v
  rw [Submodule.mem_map, D.mem_clSub_iff]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨a, haX, haQ, rfl⟩ := D.mem_clSub_iff.mp hw
    exact ⟨(g : G) * a * (g : G)⁻¹, ⟨a, haX, rfl⟩, D.conj_mem g.2 haQ, (D.ρ_cl g haQ).symm⟩
  · rintro ⟨_, ⟨a, haX, rfl⟩, haQ, rfl⟩
    have haQ' : a ∈ D.Q₁ := by
      have h := D.conj_mem (inv_mem g.2) haQ
      have e : (g : G)⁻¹ * (MulAut.conj (g : G)).toMonoidHom a * ((g : G)⁻¹)⁻¹ = a := by
        show (g : G)⁻¹ * ((g : G) * a * (g : G)⁻¹) * ((g : G)⁻¹)⁻¹ = a
        group
      rwa [e] at h
    exact ⟨D.cl a, D.cl_mem_clSub haX haQ', D.ρ_cl g haQ'⟩

theorem mem_normalizer_of_map_ρ_clSub {X : Subgroup G} (hX : X ≤ D.Q₁) (hz : D.z ∈ X)
    (g : D.N) (h : (D.clSub X).map ((D.ρ g : D.O) : D.Qt ≃ₗ[ZMod 2] D.Qt).toLinearMap =
      D.clSub X) : (g : G) ∈ normalizer (X : Set G) := by
  rw [D.map_ρ_clSub] at h
  have hX' : X.map (MulAut.conj (g : G)).toMonoidHom ≤ D.Q₁ := by
    rintro _ ⟨a, ha, rfl⟩
    exact D.conj_mem g.2 (hX ha)
  have hz' : D.z ∈ X.map (MulAut.conj (g : G)).toMonoidHom := by
    refine ⟨(g : G)⁻¹ * D.z * g, ?_, by
      show (g : G) * ((g : G)⁻¹ * D.z * g) * (g : G)⁻¹ = D.z
      group⟩
    have hzc : (g : G)⁻¹ * D.z * g = D.z := by
      have h1 := D.conj_mem (inv_mem g.2) D.z_mem
      rw [inv_inv] at h1
      have h2 : (g : G)⁻¹ * D.z * g ∈ centerIn D.Q₁ := by
        refine ⟨h1, mem_centralizer_iff.mpr fun b hb => ?_⟩
        have h3 := D.z_comm (D.conj_mem g.2 hb)
        calc b * ((g : G)⁻¹ * D.z * g) = (g : G)⁻¹ * (((g : G) * b * (g : G)⁻¹) * D.z) * g := by
              group
          _ = (g : G)⁻¹ * (D.z * ((g : G) * b * (g : G)⁻¹)) * g := by rw [h3]
          _ = (g : G)⁻¹ * D.z * g * b := by group
      rw [D.center_eq] at h2
      rcases D.mem_zpowers_z_iff.mp h2 with h4 | h4
      · exfalso
        apply D.z_ne_one
        calc D.z = (g : G) * ((g : G)⁻¹ * D.z * g) * (g : G)⁻¹ := by group
          _ = 1 := by rw [h4]; group
      · exact h4
    rw [hzc]
    exact hz
  have e := D.clPre_clSub hX' hz'
  rw [h, D.clPre_clSub hX hz] at e
  rw [mem_normalizer_iff_map_conj_eq]
  exact e.symm

end XSub

end CFSG.ComponentClassification.AS81
