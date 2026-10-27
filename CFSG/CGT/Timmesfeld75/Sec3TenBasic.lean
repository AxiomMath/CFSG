module

public import CFSG.CGT.Timmesfeld75.Sec3TenFpf

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open DihedralGroup

section Quotient

variable {G : Type} [Group G] {T T₁ : Subgroup G}
  [hN : ((cfgM T T₁).subgroupOf (T ⊔ T₁)).Normal]

theorem Sec3.card_eq_mul_map [Finite G] (hS : Sec3 T T₁) :
    Nat.card T = Nat.card (normIn T T₁) * Nat.card ((T.subgroupOf (T ⊔ T₁)).map
      (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))) := by
  let φ : ↥T →* ↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁) :=
    (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁))).comp
      (Subgroup.inclusion (le_sup_left : T ≤ T ⊔ T₁))
  have hrange : φ.range = (T.subgroupOf (T ⊔ T₁)).map
      (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁))) := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨Subgroup.inclusion le_sup_left t, Subgroup.mem_subgroupOf.2 t.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨(y : G), Subgroup.mem_subgroupOf.1 hy⟩, rfl⟩
  have hker : φ.ker = (normIn T T₁).subgroupOf T := by
    ext t
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hS.cfg.inf_cfgM, Subgroup.mem_inf]
    constructor
    · intro ht
      have h1 : (Subgroup.inclusion le_sup_left t : ↥(T ⊔ T₁)) ∈
          (cfgM T T₁).subgroupOf (T ⊔ T₁) := (QuotientGroup.eq_one_iff _).1 ht
      exact ⟨t.2, Subgroup.mem_subgroupOf.1 h1⟩
    · rintro ⟨-, hM⟩
      exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hM)
  have h1 := Subgroup.card_ker_mul_card_range φ
  rw [hker, hrange, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (normIn_le T T₁)).toEquiv] at h1
  exact h1.symm

theorem Sec3.card_eq_two_mul_dihedral [Finite G] (hS : Sec3 T T₁) {n : ℕ} (hn : Odd n)
    (e : ↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁) ≃* DihedralGroup n) :
    Nat.card T = Nat.card (normIn T T₁) * 2 := by
  rw [hS.card_eq_mul_map, hS.card_map_dihedral hn e]

theorem Sec3.card_le_of_invariant_dihedral [Finite G] (hS : Sec3 T T₁) {n : ℕ} (hn : Odd n)
    (e : ↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁) ≃* DihedralGroup n) {V : Set G}
    (hVM : ∀ w ∈ V, w ∈ cfgM T T₁ ∧ w ≠ 1)
    (hV : ∀ x ∈ T ⊔ T₁, ∀ w ∈ V, x * w * x⁻¹ ∈ V) {w₀ : G} (hw₀ : w₀ ∈ V) : n ≤ V.ncard := by
  have : NeZero n := ⟨hn.pos.ne'⟩
  choose lift hlift using fun k : ZMod n => QuotientGroup.mk_surjective (e.symm (r k))
  let f : ZMod n → V := fun k => ⟨(lift k : G) * w₀ * (lift k : G)⁻¹, hV _ (lift k).2 w₀ hw₀⟩
  have hf : Function.Injective f := by
    intro k k' hkk
    by_contra hne
    have hfix : ((lift k' : G)⁻¹ * (lift k : G)) * w₀ *
        ((lift k' : G)⁻¹ * (lift k : G))⁻¹ = w₀ := by
      have h1 := congrArg Subtype.val hkk
      simp only [f] at h1
      calc ((lift k' : G)⁻¹ * (lift k : G)) * w₀ * ((lift k' : G)⁻¹ * (lift k : G))⁻¹
          = (lift k' : G)⁻¹ * ((lift k : G) * w₀ * (lift k : G)⁻¹) * (lift k' : G) := by group
        _ = w₀ := by rw [h1]; group
    have hxX : (lift k' : G)⁻¹ * (lift k : G) ∈ T ⊔ T₁ :=
      (T ⊔ T₁).mul_mem ((T ⊔ T₁).inv_mem (lift k').2) (lift k).2
    have himg : QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁))
        ⟨(lift k' : G)⁻¹ * (lift k : G), hxX⟩ = e.symm (r (k - k')) := by
      have : (⟨(lift k' : G)⁻¹ * (lift k : G), hxX⟩ : ↥(T ⊔ T₁)) = (lift k')⁻¹ * lift k := rfl
      rw [this, map_mul, map_inv]
      have e1 : QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) (lift k) = e.symm (r k) :=
        hlift k
      have e2 : QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) (lift k') = e.symm (r k') :=
        hlift k'
      rw [e1, e2, ← map_inv, ← map_mul, inv_r, r_mul_r]
      congr 2
      ring
    have hodd : Odd (orderOf (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁))
        ⟨(lift k' : G)⁻¹ * (lift k : G), hxX⟩)) := by
      rw [himg, MulEquiv.orderOf_eq]
      have h2 : (r (k - k') : DihedralGroup n) ^ n = 1 := by
        rw [r_pow]
        have : ((k - k') * (n : ZMod n)) = 0 := by simp
        rw [this]
        rfl
      exact hn.of_dvd_nat (orderOf_dvd_of_pow_eq_one h2)
    have hx1 : QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁))
        ⟨(lift k' : G)⁻¹ * (lift k : G), hxX⟩ ≠ 1 := by
      rw [himg]
      intro h1
      have h2 := e.symm.injective (h1.trans (map_one e.symm).symm)
      have h3 : (k - k') = 0 := DihedralGroup.r.inj (h2.trans r_zero)
      exact hne (sub_eq_zero.1 h3)
    exact (hVM w₀ hw₀).2 (hS.centralizer_cfgM_eq_bot_of_odd_dihedral hn e hxX hodd hx1 w₀
      (hVM w₀ hw₀).1 hfix)
  have hVfin : V.Finite := Set.toFinite V
  calc n = Nat.card (ZMod n) := (Nat.card_zmod n).symm
    _ ≤ Nat.card V := Nat.card_le_card_of_injective f hf
    _ = V.ncard := Nat.card_coe_set_eq V

end Quotient

end CFSG.CGT.Timmesfeld75
