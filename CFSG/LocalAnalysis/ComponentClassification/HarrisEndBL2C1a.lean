module

public import CFSG.GroupTheory.DihedralTwoClassFusionSupport
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.ComponentClassification.HarrisLit

open Subgroup DihedralGroup

theorem EndB.dih_conj_mem {G : Type*} [Group G] {D : Subgroup G} {n : ℕ}
    (e : ↥D ≃* DihedralGroup n) {v : G} (hinv : ∀ a ∈ D, a * a = 1 → v * a * v⁻¹ ∈ D)
    {d : G} (hd : d ∈ D) : v * d * v⁻¹ ∈ D := by
  have hinv' : ∀ k : ZMod n, v * ((e.symm (sr k) : ↥D) : G) * v⁻¹ ∈ D := fun k =>
    hinv _ (e.symm (sr k)).2 (by
      rw [← Subgroup.coe_mul, ← map_mul, sr_mul_self, map_one, Subgroup.coe_one])
  rcases h : e ⟨d, hd⟩ with k | k
  · have hdk : d = ((e.symm (sr 0) : ↥D) : G) * ((e.symm (sr k) : ↥D) : G) := by
      have : (⟨d, hd⟩ : ↥D) = e.symm (sr 0) * e.symm (sr k) := by
        rw [← map_mul, sr_mul_sr, sub_zero, ← h, e.symm_apply_apply]
      exact congrArg Subtype.val this
    rw [hdk]
    have e2 : v * (((e.symm (sr 0) : ↥D) : G) * ((e.symm (sr k) : ↥D) : G)) * v⁻¹ =
        (v * ((e.symm (sr 0) : ↥D) : G) * v⁻¹) * (v * ((e.symm (sr k) : ↥D) : G) * v⁻¹) := by
      group
    rw [e2]
    exact mul_mem (hinv' 0) (hinv' k)
  · have hdk : d = ((e.symm (sr k) : ↥D) : G) := by
      have : (⟨d, hd⟩ : ↥D) = e.symm (sr k) := by rw [← h, e.symm_apply_apply]
      exact congrArg Subtype.val this
    rw [hdk]
    exact hinv' k

theorem EndB.dih_sr_conj {G : Type*} [Group G] {D : Subgroup G} {n : ℕ}
    (e : ↥D ≃* DihedralGroup n) (k : ZMod n) :
    ((e.symm (sr k) : ↥D) : G) * ((e.symm (r 1) : ↥D) : G) * ((e.symm (sr k) : ↥D) : G)⁻¹ =
      ((e.symm (r 1) : ↥D) : G)⁻¹ := by
  have h : e.symm (sr k) * e.symm (r 1) * (e.symm (sr k))⁻¹ = (e.symm (r 1))⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
    congr 1
    rw [inv_sr, sr_mul_r, sr_mul_sr, inv_r]
    congr 1
    ring
  have := congrArg Subtype.val h
  simpa using this

theorem EndB.dih_conj_r_mem {G : Type*} [Group G] {D : Subgroup G} {m : ℕ} (hm : 2 ≤ m)
    (e : ↥D ≃* DihedralGroup (2 ^ m)) {v : G} (hv : ∀ d ∈ D, v * d * v⁻¹ ∈ D) :
    v * ((e.symm (r 1) : ↥D) : G) * v⁻¹ ∈ zpowers ((e.symm (r 1) : ↥D) : G) := by
  have : NeZero (2 ^ m) := ⟨pow_ne_zero m two_ne_zero⟩
  have hyD := hv _ (e.symm (r 1)).2
  have hord : orderOf (e ⟨v * ((e.symm (r 1) : ↥D) : G) * v⁻¹, hyD⟩) = 2 ^ m := by
    have h1 : orderOf (e ⟨v * ((e.symm (r 1) : ↥D) : G) * v⁻¹, hyD⟩) =
        orderOf (v * ((e.symm (r 1) : ↥D) : G) * v⁻¹) := by
      rw [← Subgroup.orderOf_mk (v * ((e.symm (r 1) : ↥D) : G) * v⁻¹) hyD]
      exact orderOf_injective e.toMonoidHom e.injective _
    have h2 : orderOf (v * ((e.symm (r 1) : ↥D) : G) * v⁻¹) =
        orderOf ((e.symm (r 1) : ↥D) : G) :=
      orderOf_injective (MulAut.conj v).toMonoidHom (MulAut.conj v).injective _
    have h3 : orderOf ((e.symm (r 1) : ↥D) : G) = orderOf (r 1 : DihedralGroup (2 ^ m)) := by
      rw [Subgroup.orderOf_coe]
      exact orderOf_injective e.symm.toMonoidHom e.symm.injective _
    rw [h1, h2, h3, orderOf_r_one]
  rcases h : e ⟨v * ((e.symm (r 1) : ↥D) : G) * v⁻¹, hyD⟩ with j | j
  · have hj : (⟨v * ((e.symm (r 1) : ↥D) : G) * v⁻¹, hyD⟩ : ↥D) = e.symm (r 1) ^ j.val := by
      rw [← map_pow, r_one_pow, ZMod.natCast_zmod_val, ← h, e.symm_apply_apply]
    have h' : v * ((e.symm (r 1) : ↥D) : G) * v⁻¹ = ((e.symm (r 1) : ↥D) : G) ^ j.val := by
      have := congrArg Subtype.val hj
      rwa [Subgroup.coe_pow] at this
    rw [h']
    exact pow_mem (mem_zpowers _) _
  · exfalso
    rw [h, orderOf_sr] at hord
    have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega

theorem EndB.comm_conj_eq {G : Type*} [Group G] {y a b : G} (ha : a * y * a⁻¹ ∈ zpowers y)
    (ha' : a⁻¹ * y * a ∈ zpowers y) (hb : b * y * b⁻¹ ∈ zpowers y)
    (hb' : b⁻¹ * y * b ∈ zpowers y) :
    (a * b * a⁻¹ * b⁻¹) * y * (a * b * a⁻¹ * b⁻¹)⁻¹ = y := by
  obtain ⟨k₁, hk₁⟩ := mem_zpowers_iff.mp ha
  obtain ⟨k₃, hk₃⟩ := mem_zpowers_iff.mp ha'
  obtain ⟨k₂, hk₂⟩ := mem_zpowers_iff.mp hb
  obtain ⟨k₄, hk₄⟩ := mem_zpowers_iff.mp hb'
  have cz : ∀ (g : G) (i : ℤ), g * y ^ i * g⁻¹ = (g * y * g⁻¹) ^ i := fun g i => conj_zpow.symm
  have cz' : ∀ (g : G) (i : ℤ), g⁻¹ * y ^ i * g = (g⁻¹ * y * g) ^ i := fun g i => by
    simpa using cz g⁻¹ i
  have h13 : y ^ (k₁ * k₃) = y := by
    rw [zpow_mul, hk₁, ← cz, hk₃]
    group
  have h24 : y ^ (k₂ * k₄) = y := by
    rw [zpow_mul, hk₂, ← cz, hk₄]
    group
  calc (a * b * a⁻¹ * b⁻¹) * y * (a * b * a⁻¹ * b⁻¹)⁻¹ =
        a * (b * (a⁻¹ * (b⁻¹ * y * b) * a) * b⁻¹) * a⁻¹ := by group
    _ = a * (b * (a⁻¹ * y ^ k₄ * a) * b⁻¹) * a⁻¹ := by rw [← hk₄]
    _ = a * (b * (y ^ k₃) ^ k₄ * b⁻¹) * a⁻¹ := by rw [cz' a k₄, ← hk₃]
    _ = a * (b * y ^ (k₃ * k₄) * b⁻¹) * a⁻¹ := by rw [← zpow_mul]
    _ = a * (y ^ k₂) ^ (k₃ * k₄) * a⁻¹ := by rw [cz b, ← hk₂]
    _ = a * y ^ (k₂ * (k₃ * k₄)) * a⁻¹ := by rw [← zpow_mul]
    _ = (y ^ k₁) ^ (k₂ * (k₃ * k₄)) := by rw [cz a, ← hk₁]
    _ = (y ^ (k₁ * k₃)) ^ (k₂ * k₄) := by rw [← zpow_mul, ← zpow_mul]; congr 1; ring
    _ = y := by rw [h13, h24]

theorem EndB.dih_eq_sr {G : Type*} [Group G] {D : Subgroup G} {m : ℕ} (hm : 2 ≤ m)
    (e : ↥D ≃* DihedralGroup (2 ^ m)) {d : G} (hd : d ∈ D) (hd2 : d * d = 1) (hd1 : d ≠ 1)
    (hdz : d ≠ ((e.symm (r 1) : ↥D) : G) ^ (2 ^ (m - 1))) :
    ∃ k : ZMod (2 ^ m), d = ((e.symm (sr k) : ↥D) : G) := by
  have hord : orderOf (e ⟨d, hd⟩) = 2 := by
    rw [← orderOf_injective e.symm.toMonoidHom e.symm.injective]
    change orderOf (e.symm (e ⟨d, hd⟩)) = 2
    rw [e.symm_apply_apply, Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by rw [sq, hd2]) hd1
  rcases CFSG.GorensteinWalter.TwoClassFusion.eq_r_half_or_sr_of_orderOf_eq_two hm hord with
    h | ⟨k, hk⟩
  · exfalso
    apply hdz
    have : (⟨d, hd⟩ : ↥D) = e.symm (r 1) ^ (2 ^ (m - 1)) := by
      rw [← map_pow, r_one_pow, ← h, e.symm_apply_apply]
    have := congrArg Subtype.val this
    rwa [Subgroup.coe_pow] at this
  · refine ⟨k, ?_⟩
    have : (⟨d, hd⟩ : ↥D) = e.symm (sr k) := by rw [← hk, e.symm_apply_apply]
    exact congrArg Subtype.val this

theorem EndB.dih_two_classes {G : Type*} [Group G] {D : Subgroup G} {m : ℕ}
    (e : ↥D ≃* DihedralGroup (2 ^ m)) {b : ZMod (2 ^ m)}
    (hne : ∀ d ∈ D, ((e.symm (sr b) : ↥D) : G) ≠ d * ((e.symm (sr 0) : ↥D) : G) * d⁻¹)
    (k : ZMod (2 ^ m)) :
    ∃ d ∈ D, ((e.symm (sr k) : ↥D) : G) = d * ((e.symm (sr 0) : ↥D) : G) * d⁻¹ ∨
      ((e.symm (sr k) : ↥D) : G) = d * ((e.symm (sr b) : ↥D) : G) * d⁻¹ := by
  have key : ∀ a c : ZMod (2 ^ m), IsConj (sr a) (sr c) →
      ∃ d ∈ D, ((e.symm (sr a) : ↥D) : G) = d * ((e.symm (sr c) : ↥D) : G) * d⁻¹ := by
    intro a c h
    obtain ⟨g, hg⟩ := isConj_iff.mp h
    refine ⟨((e.symm g⁻¹ : ↥D) : G), (e.symm g⁻¹).2, ?_⟩
    have h1 : e.symm (sr a) = e.symm g⁻¹ * e.symm (sr c) * (e.symm g⁻¹)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul, ← hg]
      congr 1
      group
    have := congrArg Subtype.val h1
    simpa using this
  rcases CFSG.GorensteinWalter.TwoClassFusion.isConj_sr_zero_or_one k with hk | hk
  · obtain ⟨d, hd, h⟩ := key k 0 hk
    exact ⟨d, hd, Or.inl h⟩
  · rcases CFSG.GorensteinWalter.TwoClassFusion.isConj_sr_zero_or_one b with hb | hb
    · exfalso
      obtain ⟨d, hd, h⟩ := key b 0 hb
      exact hne d hd h
    · obtain ⟨d, hd, h⟩ := key k b (hk.trans hb.symm)
      exact ⟨d, hd, Or.inr h⟩

end CFSG.ComponentClassification.HarrisLit
