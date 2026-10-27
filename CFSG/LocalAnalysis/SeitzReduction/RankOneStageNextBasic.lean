module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneStageLayer

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.SteinbergBV CFSG.LocalAnalysis.SteinbergBX
open CFSG.ABGLocalTools

section Generic

variable {G : Type*} [Group G]

theorem mem_normalizer_sup_of_mem {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [← map_conj_eq_self_iff] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

theorem mem_normalizer_of_map_conj_le [Finite G] {H : Subgroup G} {g : G}
    (hle : H.map (MulAut.conj g).toMonoidHom ≤ H) : g ∈ normalizer (H : Set G) :=
  map_conj_eq_self_iff.mp (Subgroup.eq_of_le_of_card_ge hle (by rw [card_map_conj]))

end Generic

variable {D : Type} [Group D] [Finite D] {R X U P Up : Subgroup D} {n : ℕ}

structure SmallRootNextData (R X U P Up : Subgroup D) (n : ℕ) : Prop where
  stage : SmallRootStage R X U P n
  three_le : 3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard
  regular : GMSHasRegularNormal U R
  le : U ≤ Up
  le_tr : Up ≤ normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D)
  inf_eq : Up ⊓ (U ⊔ R) = U
  sup_eq : Up ⊔ R = normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D)
  le_normalizer_Y : normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ normalizer (R : Set D) ≤
    normalizer (Up : Set D)
  le_normalizer_NX : X ⊓ normalizer (U : Set D) ≤ normalizer (Up : Set D)
  ker : ∀ r ∈ R, r ≠ 1 → ∀ x ∈ Up, x * r * x⁻¹ * r⁻¹ = 1 → x ∈ U
  onto : ∀ r ∈ R, r ≠ 1 → ∀ u ∈ U, ∃ x ∈ Up, x * r * x⁻¹ * r⁻¹ = u

namespace SmallRootNextData

variable (hN : SmallRootNextData R X U P Up n)
include hN

theorem exists_setup : ∃ t ∈ R, t ≠ 1 ∧ GMS28.Setup R R X U P n t := by
  obtain ⟨t, htR, ht1⟩ := hN.stage.exists_ne_one
  exact ⟨t, htR, ht1, hN.stage.setup hN.three_le htR ht1⟩

theorem normalizer_V_le : normalizer ((U ⊔ R : Subgroup D) : Set D) ≤ normalizer (U : Set D) := by
  obtain ⟨t, -, -, hS⟩ := hN.exists_setup
  exact hS.normalizer_V_le

omit [Finite D] hN in
theorem tr_le_normalizer_U :
    normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D) ≤
      normalizer (U : Set D) :=
  inf_le_right.trans (centralizer_le_normalizer _)

omit [Finite D] in
theorem Up_le_normalizer_U : Up ≤ normalizer (U : Set D) :=
  hN.le_tr.trans tr_le_normalizer_U

theorem V_le_tr :
    U ⊔ R ≤ normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D) := by
  obtain ⟨t, -, -, hS⟩ := hN.exists_setup
  exact hS.V_le_tr

theorem P_le_Y : P ≤ normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ normalizer (R : Set D) := by
  obtain ⟨t, -, -, hS⟩ := hN.exists_setup
  obtain ⟨-, -, -, -, -, -, ⟨hPN, -⟩⟩ := hN.stage.1
  exact le_inf hS.P_le_normalizer_V hPN

omit [Finite D] hN in
theorem R_le_Y : R ≤ normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ normalizer (R : Set D) :=
  le_inf (le_sup_right.trans le_normalizer) le_normalizer

theorem NX_le_normalizer_V :
    X ⊓ normalizer (U : Set D) ≤ normalizer ((U ⊔ R : Subgroup D) : Set D) :=
  gms_NXU_le_L hN.stage.1

omit [Finite D] in
theorem NX_le_centralizer_R : X ⊓ normalizer (U : Set D) ≤ centralizer (R : Set D) := by
  obtain ⟨-, -, -, ⟨-, -, hXC⟩, -⟩ := hN.stage.1
  exact inf_le_left.trans hXC

theorem tr_le_normalizer_Up :
    normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D) ≤
      normalizer (Up : Set D) :=
  hN.stage.translations_le_normalizer hN.three_le hN.regular hN.le hN.le_tr

theorem sq_comm_mem :
    (∀ x ∈ normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D), x * x ∈ U) ∧
    ∀ x ∈ normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D),
      ∀ y ∈ normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D),
        x * y * x⁻¹ * y⁻¹ ∈ U := by
  obtain ⟨hsq, hcomm, -⟩ := smallRoot_layer hN.stage hN.three_le hN.regular
  exact ⟨hsq, hcomm⟩

theorem normalizer_V_eq :
    normalizer ((U ⊔ R : Subgroup D) : Set D) =
      (normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D)) ⊔
        (normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ normalizer (R : Set D)) :=
  (smallRoot_translations hN.stage hN.three_le hN.regular).2.2.2.2.2.2.1

theorem isPGroup_tr :
    IsPGroup 2 (normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D) :
      Subgroup D) :=
  (smallRoot_translations hN.stage hN.three_le hN.regular).1

theorem inf_NX_eq : Up ⊓ (X ⊓ normalizer (U : Set D)) = U := by
  obtain ⟨-, -, -, -, ⟨-, hUX, -, -⟩, -⟩ := hN.stage.1
  refine le_antisymm (fun x hx => ?_) (le_inf hN.le (le_inf hUX le_normalizer))
  obtain ⟨hxUp, hxNX⟩ := mem_inf.mp hx
  rw [← hN.stage.X_centralizer_U]
  exact mem_inf.mpr ⟨(mem_inf.mp hxNX).1, (mem_inf.mp (hN.le_tr hxUp)).2⟩

omit [Finite D] in
theorem comm_mem_of_mem_NX {m w : D} (hm : m ∈ X ⊓ normalizer (U : Set D))
    (hw : w ∈ normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D)) :
    m * w * m⁻¹ * w⁻¹ ∈ Up := by
  have hRUp : R ≤ normalizer (Up : Set D) := R_le_Y.trans hN.le_normalizer_Y
  rw [← hN.sup_eq] at hw
  have hw' : w ∈ ((Up ⊔ R : Subgroup D) : Set D) := hw
  rw [coe_mul_of_right_le_normalizer_left Up R hRUp] at hw'
  obtain ⟨x, hx, r, hr, rfl⟩ := hw'
  have hmr : m * r * m⁻¹ = r := by
    rw [← mem_centralizer_iff.mp (hN.NX_le_centralizer_R hm) r hr, mul_inv_cancel_right]
  have hmx : m * x * m⁻¹ ∈ Up := (mem_normalizer_iff.mp (hN.le_normalizer_NX hm) x).mp hx
  have e : m * (x * r) * m⁻¹ * (x * r)⁻¹ = (m * x * m⁻¹) * (m * r * m⁻¹) * r⁻¹ * x⁻¹ := by
    group
  rw [e, hmr, mul_inv_cancel_right]
  exact mul_mem hmx (inv_mem hx)

theorem normalizer_V_le_normalizer_sup :
    normalizer ((U ⊔ R : Subgroup D) : Set D) ≤
      normalizer ((Up ⊔ (X ⊓ normalizer (U : Set D)) : Subgroup D) : Set D) := by
  rw [hN.normalizer_V_eq]
  refine sup_le (fun w hw => ?_) (fun y hy => ?_)
  · refine mem_normalizer_of_map_conj_le ?_
    rw [Subgroup.map_sup]
    refine sup_le ((le_of_eq (map_conj_eq_self_iff.mpr (hN.tr_le_normalizer_Up hw))).trans
      le_sup_left) ?_
    rintro _ ⟨m, hm, rfl⟩
    have h1 := hN.comm_mem_of_mem_NX hm hw
    have e : (MulAut.conj w).toMonoidHom m = (w * m * w⁻¹ * m⁻¹) * m := by
      simp [MulAut.conj_apply]
    rw [e]
    have h2 : w * m * w⁻¹ * m⁻¹ = (m * w * m⁻¹ * w⁻¹)⁻¹ := by group
    rw [h2]
    exact mul_mem (mem_sup_left (inv_mem h1)) (mem_sup_right hm)
  · obtain ⟨hyV, hyR⟩ := mem_inf.mp hy
    exact mem_normalizer_sup_of_mem (hN.le_normalizer_Y hy)
      (gms_LR_normalizes hN.stage.1 hyV hyR).2.2.1

theorem isSylowOf_sup_NX : IsSylowOf 2 Up (Up ⊔ (X ⊓ normalizer (U : Set D))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, ⟨-, hUX, ⟨TU, hTU⟩, -⟩, -⟩ := hN.stage.1
  have hUSyl : IsSylowOf 2 U X :=
    ⟨TU, by rw [hTU, subgroupOf_map_subtype, inf_of_le_left hUX]⟩
  have hUNX : IsSylowOf 2 U (X ⊓ normalizer (U : Set D)) :=
    hUSyl.of_le (le_inf hUX le_normalizer) inf_le_left
  have hodd : ¬ 2 ∣ U.relIndex (X ⊓ normalizer (U : Set D)) := (isSylowOf_iff.mp hUNX).2.2
  have hUpH : Up ≤ (X ⊓ normalizer (U : Set D)) ⊔ Up := le_sup_right
  have hNXH : X ⊓ normalizer (U : Set D) ≤ (X ⊓ normalizer (U : Set D)) ⊔ Up := le_sup_left
  have : (Up.subgroupOf ((X ⊓ normalizer (U : Set D)) ⊔ Up)).Normal :=
    normal_subgroupOf_sup_of_le_normalizer hN.le_normalizer_NX
  have h1 := relIndex_sup_left ((X ⊓ normalizer (U : Set D)).subgroupOf
    ((X ⊓ normalizer (U : Set D)) ⊔ Up)) (Up.subgroupOf ((X ⊓ normalizer (U : Set D)) ⊔ Up))
  rw [← subgroupOf_sup hUpH hNXH, relIndex_subgroupOf (sup_le hUpH hNXH),
    relIndex_subgroupOf hNXH] at h1
  have h2 : Up.relIndex (X ⊓ normalizer (U : Set D)) = U.relIndex (X ⊓ normalizer (U : Set D)) := by
    rw [← inf_relIndex_right Up (X ⊓ normalizer (U : Set D)), hN.inf_NX_eq]
  refine isSylowOf_iff.mpr ⟨le_sup_left, hN.isPGroup_tr.to_le hN.le_tr, ?_⟩
  rw [h1, h2]
  exact hodd

theorem isSylowOf_tr_sup_P :
    IsSylowOf 2 ((normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D)) ⊔ P)
      (normalizer ((U ⊔ R : Subgroup D) : Set D)) := by
  obtain ⟨t, -, -, hS⟩ := hN.exists_setup
  obtain ⟨htr, hV₁, -⟩ := hN.stage.exists_isTorus_translations hN.regular hS
  exact hV₁.isSylowOf_sup hS htr

theorem mem_centralizer_of_comm_mem {y : D} (hy : y ∈ normalizer (R : Set D))
    (hC : ∀ x ∈ Up, y * x * y⁻¹ * x⁻¹ ∈ U) : y ∈ centralizer (U : Set D) := by
  obtain ⟨t, htR, ht1, hS⟩ := hN.exists_setup
  rw [mem_centralizer_iff]
  intro u hu
  obtain ⟨x, hx, hxu⟩ := hN.onto t htR ht1 u hu
  rw [hS.inv_t] at hxu
  have hxW := hN.le_tr hx
  have hcU : y * x * y⁻¹ * x⁻¹ ∈ U := hC x hx
  have hcW := hN.V_le_tr (mem_sup_left hcU)
  have e1 : y * x * y⁻¹ = (y * x * y⁻¹ * x⁻¹) * x := by group
  have h1 := hN.stage.comm_conj_of_mem_normalizer hN.three_le htR ht1 hy x
  rw [hS.inv_t] at h1
  have h2 := hS.comm_mul hcW hxW
  have hct : (y * x * y⁻¹ * x⁻¹) * t * (y * x * y⁻¹ * x⁻¹)⁻¹ * t = 1 := by
    rw [hS.commute_t hcU, mul_inv_cancel_right, hS.mul_self_t]
  rw [hct, one_mul, ← e1, h1, hxu] at h2
  calc u * y = y * u * y⁻¹ * y := by rw [h2]
    _ = y * u := by group

theorem mem_V_of_comm_mem {y : D} (hy : y ∈ normalizer (R : Set D))
    (hC : ∀ x ∈ Up, y * x * y⁻¹ * x⁻¹ ∈ U) : y ∈ U ⊔ R := by
  rw [← hN.stage.normalizer_inf_centralizer]
  exact mem_inf.mpr ⟨hy, hN.mem_centralizer_of_comm_mem hy hC⟩

theorem exists_singer_layer : ∃ d ∈ X ⊓ normalizer (U : Set D), orderOf d = 2 ^ n - 1 ∧
    X ⊓ normalizer (U : Set D) = U ⊔ zpowers d ∧ (∀ k : ℕ, d ^ k ∈ U → d ^ k = 1) ∧
    (∀ a ∈ Up, a ∉ U → ∀ b ∈ Up, b ∉ U → ∃ k : ℕ, (d ^ k * a * (d ^ k)⁻¹)⁻¹ * b ∈ U) ∧
    ∀ k : ℕ, ∀ a ∈ Up, a ∉ U → (d ^ k * a * (d ^ k)⁻¹)⁻¹ * a ∈ U → d ^ k = 1 := by
  obtain ⟨t, htR, ht1, hS⟩ := hN.exists_setup
  obtain ⟨d, hdN, hdord, hNX, hdtr, hdfix⟩ := hN.stage.exists_singer
  have hn3 := hN.stage.three_le
  have hdodd : Odd (orderOf d) := by
    have h8 : 8 ≤ 2 ^ n :=
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
    have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    rw [hdord]
    exact Nat.odd_iff.mpr (by omega)
  have hdR : d ∈ normalizer (R : Set D) :=
    centralizer_le_normalizer _ (hN.NX_le_centralizer_R hdN)
  have hφU : ∀ x ∈ Up, x * t * x⁻¹ * t ∈ U := fun x hx => hS.comm_mem (hN.le_tr hx)
  have hφker : ∀ x ∈ Up, x * t * x⁻¹ * t = 1 ↔ x ∈ U := by
    intro x hx
    refine ⟨fun h1 => hN.ker t htR ht1 x hx (by rw [hS.inv_t]; exact h1), fun h1 => ?_⟩
    rw [hS.commute_t h1, mul_inv_cancel_right, hS.mul_self_t]
  have hφmul : ∀ x ∈ Up, ∀ y ∈ Up,
      x * y * t * (x * y)⁻¹ * t = (x * t * x⁻¹ * t) * (y * t * y⁻¹ * t) :=
    fun x hx y hy => hS.comm_mul (hN.le_tr hx) (hN.le_tr hy)
  have hφinv : ∀ x ∈ Up, x⁻¹ * t * x⁻¹⁻¹ * t = (x * t * x⁻¹ * t)⁻¹ := by
    intro x hx
    have h1 := hφmul x hx x⁻¹ (inv_mem hx)
    rw [mul_inv_cancel, one_mul, inv_one, mul_one, hS.mul_self_t] at h1
    exact eq_inv_of_mul_eq_one_right h1.symm
  have hφconj : ∀ (k : ℕ) (x : D), d ^ k * x * (d ^ k)⁻¹ * t * (d ^ k * x * (d ^ k)⁻¹)⁻¹ * t =
      d ^ k * (x * t * x⁻¹ * t) * (d ^ k)⁻¹ := by
    intro k x
    have h1 := hN.stage.comm_conj_of_mem_normalizer hN.three_le htR ht1 (pow_mem hdR k) x
    rwa [hS.inv_t] at h1
  have hdUp : ∀ (k : ℕ), ∀ x ∈ Up, d ^ k * x * (d ^ k)⁻¹ ∈ Up := fun k x hx =>
    (mem_normalizer_iff.mp (pow_mem (hN.le_normalizer_NX hdN) k) x).mp hx
  have hkey : ∀ c ∈ Up, ∀ b ∈ Up, c⁻¹ * b ∈ U ↔ c * t * c⁻¹ * t = b * t * b⁻¹ * t := by
    intro c hc b hb
    rw [← hφker _ (mul_mem (inv_mem hc) hb), hφmul _ (inv_mem hc) _ hb, hφinv c hc]
    exact inv_mul_eq_one
  refine ⟨d, hdN, hdord, hNX, fun k hk => ?_, fun a ha haU b hb hbU => ?_,
    fun k a ha haU hk => ?_⟩
  · exact eq_one_of_odd_orderOf_of_sq_eq_one (hdodd.of_dvd_nat (orderOf_pow_dvd k))
      (gms_sq_V hN.stage.1 _ (mem_sup_left hk))
  · have ha1 : a * t * a⁻¹ * t ≠ 1 := fun h1 => haU ((hφker a ha).mp h1)
    have hb1 : b * t * b⁻¹ * t ≠ 1 := fun h1 => hbU ((hφker b hb).mp h1)
    obtain ⟨k, hk⟩ := hdtr _ (hφU a ha) _ (hφU b hb) ha1 hb1
    refine ⟨k, (hkey _ (hdUp k a ha) b hb).mpr ?_⟩
    rw [hφconj]
    exact hk
  · have h1 := (hkey _ (hdUp k a ha) a ha).mp hk
    rw [hφconj] at h1
    exact hdfix k _ (hφU a ha) (fun h2 => haU ((hφker a ha).mp h2)) h1

end SmallRootNextData

end CFSG.SeitzReduction.RankOne
