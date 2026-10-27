module

public import CFSG.GH74.Uniqueness.SU.SU8UAbs

public section

namespace CFSG.GH74.Uniqueness.SU.SU8

open Subgroup
open scoped commutatorElement

namespace UConf

@[expose] noncomputable def conjAut {M : Type*} [Group M] [Finite M] (c : M) (Z : Subgroup M)
    (hcZ : ∀ w ∈ Z, c * w * c⁻¹ ∈ Z) : MulAut ↥Z :=
  MulEquiv.ofBijective (((MulAut.conj c).toMonoidHom.comp Z.subtype).codRestrict Z
    (fun u => by simpa [MulAut.conj_apply] using hcZ u u.2)) (by
    have hinj : Function.Injective (((MulAut.conj c).toMonoidHom.comp Z.subtype).codRestrict Z
        (fun u => by simpa [MulAut.conj_apply] using hcZ u u.2)) := by
      intro a b h
      have h1 : c * (a : M) * c⁻¹ = c * (b : M) * c⁻¹ := congrArg Subtype.val h
      exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
    exact ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩)

theorem conjAut_apply {M : Type*} [Group M] [Finite M] (c : M) (Z : Subgroup M)
    (hcZ : ∀ w ∈ Z, c * w * c⁻¹ ∈ Z) (w : ↥Z) :
    ((conjAut c Z hcZ w : ↥Z) : M) = c * (w : M) * c⁻¹ := rfl

theorem conjAut_pow_apply {M : Type*} [Group M] [Finite M] (c : M) (Z : Subgroup M)
    (hcZ : ∀ w ∈ Z, c * w * c⁻¹ ∈ Z) (k : ℕ) (w : ↥Z) :
    (((conjAut c Z hcZ ^ k) w : ↥Z) : M) = c ^ k * (w : M) * (c ^ k)⁻¹ := by
  induction k generalizing w with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, MulAut.mul_apply, ih, conjAut_apply]
    simp only [pow_succ]
    group

theorem aut_five_trivial {X : Type*} [Group X] [Finite X] (α : MulAut X) (h5 : α ^ 5 = 1)
    (hX : Nat.card X < 5) : ∀ x : X, α x = x := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set Γ : Subgroup (MulAut X) := Subgroup.zpowers α with hΓ
  have hord : orderOf α ∣ 5 := orderOf_dvd_of_pow_eq_one h5
  have hΓp : IsPGroup 5 Γ := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hord with h | h
    · refine IsPGroup.of_card (n := 0) ?_
      rw [hΓ, Nat.card_zpowers, h]; simp
    · refine IsPGroup.of_card (n := 1) ?_
      rw [hΓ, Nat.card_zpowers, h]; simp
  have hmod := hΓp.card_modEq_card_fixedPoints (α := X)
  have hle : Nat.card (MulAction.fixedPoints Γ X) ≤ Nat.card X :=
    Nat.card_le_card_of_injective (fun x => x.1) Subtype.val_injective
  have heq : Nat.card (MulAction.fixedPoints Γ X) = Nat.card X := by
    have h1 : Nat.card X % 5 = Nat.card (MulAction.fixedPoints Γ X) % 5 := hmod
    omega
  have hall : (MulAction.fixedPoints Γ X) = Set.univ := by
    refine (Set.eq_univ_iff_ncard _).mpr ?_
    rw [← Nat.card_coe_set_eq]
    exact heq
  intro x
  have hx : x ∈ MulAction.fixedPoints Γ X := by rw [hall]; trivial
  exact hx ⟨α, Subgroup.mem_zpowers α⟩

theorem conj_fixes_of_pow_five {M : Type*} [Group M] [Finite M] (c : M) (hc5 : c ^ 5 = 1)
    (Z : Subgroup M) (hcZ : ∀ w ∈ Z, c * w * c⁻¹ ∈ Z) (hZ : Nat.card Z < 5) :
    ∀ w ∈ Z, c * w * c⁻¹ = w := by
  have h5 : conjAut c Z hcZ ^ 5 = 1 := by
    ext w
    rw [conjAut_pow_apply, hc5]
    simp
  intro w hw
  have := aut_five_trivial (conjAut c Z hcZ) h5 hZ ⟨w, hw⟩
  exact congrArg Subtype.val this

structure ConfData {M : Type*} [Group M] (R Z : Subgroup M) (y : M) : Prop where
  card_R : Nat.card R = 64
  card_Z : Nat.card Z = 4
  Z_le : Z ≤ R
  Z_central : ∀ w ∈ Z, ∀ r ∈ R, w * r = r * w
  Z_sq : ∀ w ∈ Z, w * w = 1
  Z_comm : Z ≤ ⁅R, R⁆
  y_norm : ∀ r ∈ R, y * r * y⁻¹ ∈ R
  y_fix : ∀ w ∈ Z, y * w * y⁻¹ = w
  fpf : ∀ r ∈ R, y * r * y⁻¹ * r⁻¹ ∈ Z → r ∈ Z
  per : ∀ r ∈ R, y ^ 5 * r * (y ^ 5)⁻¹ = r

structure KConf {K : Type*} [Group K] (P Zp : Subgroup K) (c : K) : Prop where
  card_P : Nat.card P = 64
  card_Z : Nat.card Zp = 4
  Z_le : Zp ≤ P
  Z_central : ∀ w ∈ Zp, ∀ p ∈ P, w * p = p * w
  Z_sq : ∀ w ∈ Zp, w * w = 1
  comm_eq : ⁅P, P⁆ = Zp
  invol : ∀ g ∈ P, g * g = 1 → g ∈ Zp
  c_norm : ∀ p ∈ P, c * p * c⁻¹ ∈ P
  c_five : c ^ 5 = 1
  fpf : ∀ p ∈ P, c * p * c⁻¹ * p⁻¹ ∈ Zp → p ∈ Zp

theorem commutator_map_subtype {M : Type*} [Group M] (R : Subgroup M) :
    (_root_.commutator ↥R).map R.subtype = ⁅R, R⁆ := by
  rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

theorem _root_.CFSG.GH74.Uniqueness.SU.SU8.UAbs.UData.of_conf {M : Type*} {Hb : Type} [Group M]
    [Group Hb] {R Z : Subgroup M} {y z : M}
    (d : ConfData R Z y) (ε : ↥R →* Hb) (hε : Function.Injective ε) (yb : Hb)
    (hyb : ∀ r : ↥R, yb * ε r * yb⁻¹ = ε ⟨y * r * y⁻¹, d.y_norm r r.2⟩)
    {K : Subgroup Hb} (hz1 : z ≠ 1) (hzZ : z ∈ Z)
    (hzC : ε ⟨z, d.Z_le hzZ⟩ ∈ centralizer (K : Set Hb))
    (hZC : ∀ (w : M) (hw : w ∈ Z), ε ⟨w, d.Z_le hw⟩ ∈ centralizer (K : Set Hb) → w = 1 ∨ w = z) :
    UAbs.UData K ε.range ((Z.subgroupOf R).map ε) yb (ε ⟨z, d.Z_le hzZ⟩) := by
  have hmemZ : ∀ a : ↥R, a ∈ Z.subgroupOf R ↔ (a : M) ∈ Z := fun a => Subgroup.mem_subgroupOf
  have hyk : ∀ (k : ℕ) (r : M), r ∈ R → y ^ k * r * (y ^ k)⁻¹ ∈ R := by
    intro k
    induction k with
    | zero => intro r hr; simpa using hr
    | succ k ih =>
      intro r hr
      have := d.y_norm _ (ih r hr)
      have e : y * (y ^ k * r * (y ^ k)⁻¹) * y⁻¹ = y ^ (k + 1) * r * (y ^ (k + 1))⁻¹ := by
        rw [pow_succ']; group
      rw [← e]; exact this
  have hybk : ∀ (k : ℕ) (a : ↥R),
      yb ^ k * ε a * (yb ^ k)⁻¹ = ε ⟨y ^ k * a * (y ^ k)⁻¹, hyk k a a.2⟩ := by
    intro k
    induction k with
    | zero => intro a; simp
    | succ k ih =>
      intro a
      have e : yb ^ (k + 1) * ε a * (yb ^ (k + 1))⁻¹ =
          yb * (yb ^ k * ε a * (yb ^ k)⁻¹) * yb⁻¹ := by
        rw [pow_succ']; group
      rw [e, ih, hyb]
      congr 1
      apply Subtype.ext
      show y * (y ^ k * (a : M) * (y ^ k)⁻¹) * y⁻¹ = y ^ (k + 1) * (a : M) * (y ^ (k + 1))⁻¹
      rw [pow_succ']; group
  have hzR : z ∈ R := d.Z_le hzZ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hzC, ?_⟩
  · rw [← d.card_R]
    exact (Nat.card_congr (MonoidHom.ofInjective hε).toEquiv).symm
  · rw [Subgroup.card_map_of_injective hε, ← d.card_Z]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe d.Z_le).toEquiv
  · rintro _ ⟨a, -, rfl⟩
    exact ⟨a, rfl⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (d.Z_central a ((hmemZ a).mp ha) b b.2)
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul]
    have : a * a = 1 := Subtype.ext (d.Z_sq a ((hmemZ a).mp ha))
    rw [this, map_one]
  · rintro _ ⟨a, ha, rfl⟩
    have h1 : (a : M) ∈ ⁅R, R⁆ := d.Z_comm ((hmemZ a).mp ha)
    rw [← commutator_map_subtype] at h1
    obtain ⟨v, hv, hva⟩ := h1
    have hva' : v = a := Subtype.ext hva
    rw [← hva']
    have : ε v ∈ (_root_.commutator ↥R).map ε := ⟨v, hv, rfl⟩
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map] at this
    exact this
  · rintro _ ⟨a, rfl⟩
    exact ⟨_, (hyb a).symm⟩
  · rintro _ ⟨a, ha, rfl⟩
    rw [hyb a]
    refine ⟨⟨y * a * y⁻¹, d.y_norm a a.2⟩, (hmemZ _).mpr ?_, rfl⟩
    show y * (a : M) * y⁻¹ ∈ Z
    rw [d.y_fix _ ((hmemZ a).mp ha)]
    exact (hmemZ a).mp ha
  · rw [hyb]
    congr 1
    exact Subtype.ext (d.y_fix z hzZ)
  · rintro _ ⟨a, rfl⟩ h
    rw [hyb a, ← map_inv, ← map_mul] at h
    obtain ⟨w, hw, hwe⟩ := h
    have hwa := hε hwe
    have hwZ : (w : M) ∈ Z := (hmemZ w).mp hw
    rw [hwa] at hwZ
    have h2 : y * (a : M) * y⁻¹ * (a : M)⁻¹ ∈ Z := by simpa using hwZ
    exact ⟨a, (hmemZ a).mpr (d.fpf a a.2 h2), rfl⟩
  · rintro _ ⟨a, rfl⟩
    rw [hybk 5 a]
    have : (⟨y ^ 5 * a * (y ^ 5)⁻¹, hyk 5 a a.2⟩ : ↥R) = a := Subtype.ext (d.per a a.2)
    rw [this, mul_inv_cancel]
    exact Subgroup.one_mem _
  · exact ⟨⟨z, hzR⟩, (hmemZ _).mpr hzZ, rfl⟩
  · intro h
    exact hz1 (congrArg Subtype.val (hε (h.trans (map_one ε).symm)))
  · rintro _ ⟨a, ha, rfl⟩ hC
    have h1 := hZC a ((hmemZ a).mp ha) (by simpa using hC)
    rcases h1 with h1 | h1
    · left
      have : a = 1 := Subtype.ext h1
      rw [this, map_one]
    · right
      have : a = ⟨z, hzR⟩ := Subtype.ext h1
      rw [this]

end UConf

end CFSG.GH74.Uniqueness.SU.SU8
