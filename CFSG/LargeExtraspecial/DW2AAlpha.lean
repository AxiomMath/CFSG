module

public import CFSG.LargeExtraspecial.DW2AGL
public import CFSG.LargeExtraspecial.DW2ATwo

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

namespace Alpha

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

structure Hyp (S : Setting G) (W : Submodule (ZMod 2) S.Qt) : Prop where
  inv : IsMbarInvariant S W
  sing : ∀ v ∈ W, S.q v = 0
  ne_bot : W ≠ ⊥
  lt : finrank (ZMod 2) W < S.width
  max : ∀ U : Submodule (ZMod 2) S.Qt, IsMbarInvariant S U → (∀ v ∈ U, S.q v = 0) → W ≤ U →
    U = W

@[expose] def IsDx (S : Setting G) (W : Submodule (ZMod 2) S.Qt) (h : G) : Prop :=
  h * S.z * h⁻¹ ∈ S.QG ∧ S.cl (h * S.z * h⁻¹) ∉ W

variable {W : Submodule (ZMod 2) S.Qt}

theorem Hyp.le_perp (hA : Hyp S W) : W ≤ perp S W := le_perp_of_forall_q hA.sing

theorem Hyp.cl_mem_perp (hA : Hyp S W) {h : G} (hQ : h * S.z * h⁻¹ ∈ S.QG) :
    S.cl (h * S.z * h⁻¹) ∈ perp S W :=
  cl_conj_mem_perp hA.inv hA.le_perp hA.lt hQ

omit [Finite G] in
theorem IsDx.ne_z {h : G} (hx : IsDx S W h) : h * S.z * h⁻¹ ≠ S.z :=
  conj_ne_z_of_not_mem hx.2

omit [Finite G] in
theorem IsDx.cl_ne_zero {h : G} (hx : IsDx S W h) : S.cl (h * S.z * h⁻¹) ≠ 0 :=
  fun e => hx.2 (e ▸ zero_mem _)

theorem IsDx.mul (hA : Hyp S W) {h : G} (hx : IsDx S W h) (m : S.M) : IsDx S W ((m : G) * h) := by
  have e : ((m : G) * h) * S.z * ((m : G) * h)⁻¹ = m * (h * S.z * h⁻¹) * (m : G)⁻¹ := by group
  refine ⟨by rw [e]; exact S.conj_mem_QG m.2 hx.1, fun hW => hx.2 ?_⟩
  rw [e, ← S.ρ_cl m hx.1] at hW
  have := hA.inv m⁻¹ _ hW
  rwa [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, ← map_mul, inv_mul_cancel, map_one] at this

section Abar

variable (hA : Hyp S W) {h : G} (hx : IsDx S W h)
include hA hx

theorem conjSub_le_M : conjSub (S.clPre W) h ≤ S.M :=
  DW.conjSub_le_M hA.inv hx.1 (hA.cl_mem_perp hx.1)

theorem mem_Abar_iff {t : S.O} :
    t ∈ Abar S (S.clPre W) h ↔ ∃ a, ∃ ha : a ∈ conjSub (S.clPre W) h,
      S.ρ ⟨a, conjSub_le_M hA hx ha⟩ = t := by
  rw [mem_Abar]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha.1, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ⟨ha, conjSub_le_M hA hx ha⟩, rfl⟩

theorem Abar_fix {t : S.O} (ht : t ∈ Abar S (S.clPre W) h) {w : S.Qt} (hw : w ∈ W) :
    (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := by
  obtain ⟨a, ha, rfl⟩ := (mem_Abar_iff hA hx).mp ht
  exact ρ_conjSub_fix hA.inv hx.1 (hA.cl_mem_perp hx.1) hx.2 ha hw

theorem Abar_isTypeA {t : S.O} (ht : t ∈ Abar S (S.clPre W) h) (ht1 : t ≠ 1) :
    IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2 ∧
      S.cl (h * S.z * h⁻¹) ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
  obtain ⟨a, ha, rfl⟩ := (mem_Abar_iff hA hx).mp ht
  exact isTypeA_ρ_conjSub hA.inv hA.sing hx.1 (hA.cl_mem_perp hx.1) hx.2 ha ht1

theorem card_Abar : Nat.card (Abar S (S.clPre W) h) = Nat.card W := by
  set H := conjSub (S.clPre W) h ⊓ S.M
  have hle := conjSub_le_M hA hx
  have hHM : H ≤ S.M := inf_le_right
  set f : H →* S.O := S.ρ.comp (inclusion hHM)
  have hrange : f.range = Abar S (S.clPre W) h := by
    rw [MonoidHom.range_comp, inclusion_range]
    rfl
  have hker : f.ker = S.QG.subgroupOf H := by
    ext b
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    exact S.ρ_eq_one_iff _
  have h1 := card_ker_mul_card_range f
  rw [hrange, hker] at h1
  have hQH : S.QG ⊓ H = zpowers (h * S.z * h⁻¹) := by
    ext b
    constructor
    · rintro ⟨hbQ, hb, -⟩
      rcases eq_of_mem_conjSub_QG hA.inv hx.1 hx.2 hb hbQ with rfl | rfl
      · exact one_mem _
      · exact mem_zpowers _
    · intro hb
      have hxH : h * S.z * h⁻¹ ∈ conjSub (S.clPre W) h := conj_mem_conjSub (S.z_mem_clPre W)
      exact ⟨(zpowers_le.mpr hx.1) hb, (zpowers_le.mpr hxH) hb, hle ((zpowers_le.mpr hxH) hb)⟩
  have hk : Nat.card (S.QG.subgroupOf H) = 2 := by
    rw [← inf_subgroupOf_right, Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv, hQH,
      Nat.card_zpowers, orderOf_eq_prime (S.s12_conj_z_sq h) (S.s12_conj_z_ne_one h)]
  have hH : Nat.card H = 2 * Nat.card W := by
    have e : H = conjSub (S.clPre W) h := inf_eq_left.mpr hle
    rw [e, conjSub, card_map_of_injective (MulAut.conj h).injective, S.card_clPre]
  rw [hk, hH] at h1
  exact Nat.eq_of_mul_eq_mul_left two_pos h1

theorem Abar_comm {s t : S.O} (hs : s ∈ Abar S (S.clPre W) h) (ht : t ∈ Abar S (S.clPre W) h) :
    s * t = t * s := by
  obtain ⟨a, ha, rfl⟩ := (mem_Abar_iff hA hx).mp hs
  obtain ⟨b, hb, rfl⟩ := (mem_Abar_iff hA hx).mp ht
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  change a * b = b * a
  rw [mem_conjSub] at ha hb
  have hc : (h⁻¹ * a * h) * (h⁻¹ * b * h) = (h⁻¹ * b * h) * (h⁻¹ * a * h) :=
    (S.polar_cl_eq_zero_iff ha.1 hb.1).mp (mem_perp.mp (hA.le_perp hb.2) _ ha.2)
  calc a * b = h * ((h⁻¹ * a * h) * (h⁻¹ * b * h)) * h⁻¹ := by group
    _ = h * ((h⁻¹ * b * h) * (h⁻¹ * a * h)) * h⁻¹ := by rw [hc]
    _ = b * a := by group

end Abar

variable (S W) in
@[expose] noncomputable def Xbar : Subgroup S.O :=
  closure {t | ∃ h : G, IsDx S W h ∧ t ∈ Abar S (S.clPre W) h}

theorem Abar_le_Xbar {h : G} (hx : IsDx S W h) : Abar S (S.clPre W) h ≤ Xbar S W :=
  fun _ ht => subset_closure ⟨h, hx, ht⟩

theorem Xbar_le_Mbar : Xbar S W ≤ S.Mbar := by
  rw [Xbar, closure_le]
  rintro t ⟨h, -, ht⟩
  exact Abar_le_Mbar _ _ ht

variable (hA : Hyp S W)
include hA

theorem conj_mem_Xbar (m : S.M) {t : S.O} (ht : t ∈ Xbar S W) :
    S.ρ m * t * (S.ρ m)⁻¹ ∈ Xbar S W := by
  induction ht using closure_induction with
  | mem t ht =>
    obtain ⟨h, hx, ht⟩ := ht
    exact subset_closure ⟨(m : G) * h, hx.mul hA m, conj_mem_Abar m ht⟩
  | one => simp
  | mul x y _ _ hx hy =>
    have : S.ρ m * (x * y) * (S.ρ m)⁻¹ =
        (S.ρ m * x * (S.ρ m)⁻¹) * (S.ρ m * y * (S.ρ m)⁻¹) := by group
    rw [this]
    exact (Xbar S W).mul_mem hx hy
  | inv x _ hx =>
    have : S.ρ m * x⁻¹ * (S.ρ m)⁻¹ = (S.ρ m * x * (S.ρ m)⁻¹)⁻¹ := by group
    rw [this]
    exact (Xbar S W).inv_mem hx

theorem Mbar_le_normalizer_Xbar : S.Mbar ≤ normalizer (Xbar S W : Set S.O) := by
  rintro _ ⟨m, rfl⟩
  rw [mem_normalizer_iff]
  intro t
  refine ⟨conj_mem_Xbar hA m, fun ht => ?_⟩
  have := conj_mem_Xbar hA m⁻¹ ht
  rw [map_inv, inv_inv] at this
  simpa [mul_assoc] using this

theorem Xbar_fix {t : S.O} (ht : t ∈ Xbar S W) {w : S.Qt} (hw : w ∈ W) :
    (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := by
  induction ht using closure_induction with
  | mem t ht =>
    obtain ⟨h, hx, ht⟩ := ht
    exact Abar_fix hA hx ht hw
  | one => rfl
  | mul x y _ _ hx hy =>
    change (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) w) = w
    rw [hy, hx]
  | inv x _ hx =>
    have e : ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) w) = w := by
      change ((x⁻¹ * x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w
      rw [inv_mul_cancel]
      rfl
    rwa [hx] at e

omit hA in
theorem sub_mem_perp_of_fix {t : S.O} (ht : ∀ w ∈ W, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w)
    (v : S.Qt) : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ perp S W := by
  rw [mem_perp]
  intro w hw
  have h1 := polar_apply_apply t w v
  rw [ht w hw] at h1
  rw [polar_sub_right, h1, sub_self]

theorem Xbar_sub_mem_perp {t : S.O} (ht : t ∈ Xbar S W) (v : S.Qt) :
    (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ perp S W :=
  sub_mem_perp_of_fix (fun _ hw => Xbar_fix hA ht hw) v

end Alpha

end CFSG.LargeExtraspecial.DW
