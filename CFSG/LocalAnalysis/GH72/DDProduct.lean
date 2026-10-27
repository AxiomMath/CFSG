module

public import CFSG.LocalAnalysis.GH72.Vocabulary

public section

namespace CFSG.GH72

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]

@[expose] def ddMulHom {S S₁ S₂ : Subgroup G} (hd : DDDecomp S S₁ S₂) :
    ↥S₁ × ↥S₂ →* ↥S where
  toFun p :=
    ⟨(p.1 : G) * (p.2 : G),
      hd.sup_eq ▸ Subgroup.mul_mem_sup p.1.2 p.2.2⟩
  map_one' := by
    ext
    simp
  map_mul' p q := by
    apply Subtype.ext
    show ((p.1 : G) * (q.1 : G)) * ((p.2 : G) * (q.2 : G)) =
      ((p.1 : G) * (p.2 : G)) * ((q.1 : G) * (q.2 : G))
    have hcomm : (q.1 : G) * (p.2 : G) = (p.2 : G) * (q.1 : G) :=
      (Subgroup.mem_centralizer_iff.mp (hd.commute p.2.2) (q.1 : G) q.1.2)
    calc ((p.1 : G) * (q.1 : G)) * ((p.2 : G) * (q.2 : G))
        = (p.1 : G) * ((q.1 : G) * (p.2 : G)) * (q.2 : G) := by group
      _ = (p.1 : G) * ((p.2 : G) * (q.1 : G)) * (q.2 : G) := by rw [hcomm]
      _ = ((p.1 : G) * (p.2 : G)) * ((q.1 : G) * (q.2 : G)) := by group

@[simp]
theorem ddMulHom_apply {S S₁ S₂ : Subgroup G} (hd : DDDecomp S S₁ S₂) (p : ↥S₁ × ↥S₂) :
    ((ddMulHom hd p : ↥S) : G) = (p.1 : G) * (p.2 : G) := rfl

theorem ddMulHom_injective {S S₁ S₂ : Subgroup G} (hd : DDDecomp S S₁ S₂) :
    Function.Injective (ddMulHom hd) := by
  rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ hab
  have h : (a₁ : G) * (a₂ : G) = (b₁ : G) * (b₂ : G) := congrArg Subtype.val hab
  have hmem : (a₁ : G)⁻¹ * (b₁ : G) = (a₂ : G) * (b₂ : G)⁻¹ := by
    have hb : (b₁ : G) = (a₁ : G) * (a₂ : G) * (b₂ : G)⁻¹ := by
      calc (b₁ : G) = (b₁ : G) * (b₂ : G) * (b₂ : G)⁻¹ := by group
        _ = (a₁ : G) * (a₂ : G) * (b₂ : G)⁻¹ := by rw [← h]
    rw [hb]
    group
  have h₁ : (a₁ : G)⁻¹ * (b₁ : G) ∈ S₁ := Subgroup.mul_mem S₁ (Subgroup.inv_mem S₁ a₁.2) b₁.2
  have h₂ : (a₂ : G) * (b₂ : G)⁻¹ ∈ S₂ := Subgroup.mul_mem S₂ a₂.2 (Subgroup.inv_mem S₂ b₂.2)
  have hbot : (a₁ : G)⁻¹ * (b₁ : G) ∈ (⊥ : Subgroup G) := by
    rw [← hd.inf_eq]
    exact ⟨h₁, hmem ▸ h₂⟩
  rw [Subgroup.mem_bot] at hbot
  have hb₁ : b₁ = a₁ := by
    apply Subtype.ext
    calc (b₁ : G) = (a₁ : G) * ((a₁ : G)⁻¹ * (b₁ : G)) := by group
      _ = (a₁ : G) := by rw [hbot, mul_one]
  have hb₂ : b₂ = a₂ := by
    apply Subtype.ext
    have : (a₂ : G) = (b₂ : G) := by
      rw [← hb₁] at h
      exact mul_left_cancel h
    exact this.symm
  rw [hb₁, hb₂]

theorem ddMulHom_surjective {S S₁ S₂ : Subgroup G} (hd : DDDecomp S S₁ S₂) :
    Function.Surjective (ddMulHom hd) := by
  intro x
  have hx : (x : G) ∈ S₁ ⊔ S₂ := hd.sup_eq ▸ x.2
  have hcoe : ((S₁ ⊔ S₂ : Subgroup G) : Set G) = (S₁ : Set G) * (S₂ : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left S₁ S₂
      (hd.commute.trans (Subgroup.centralizer_le_normalizer (S₁ : Set G)))
  have hx' : (x : G) ∈ (S₁ : Set G) * (S₂ : Set G) := hcoe ▸ hx
  obtain ⟨a, ha, b, hb, hab⟩ := hx'
  exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩

@[expose] noncomputable def ddProdEquiv {S S₁ S₂ : Subgroup G} (hd : DDDecomp S S₁ S₂) :
    ↥S ≃* ↥S₁ × ↥S₂ :=
  (MulEquiv.ofBijective (ddMulHom hd) ⟨ddMulHom_injective hd, ddMulHom_surjective hd⟩).symm

@[simp]
theorem ddProdEquiv_symm_apply {S S₁ S₂ : Subgroup G} (hd : DDDecomp S S₁ S₂)
    (p : ↥S₁ × ↥S₂) :
    (((ddProdEquiv hd).symm p : ↥S) : G) = (p.1 : G) * (p.2 : G) := rfl

theorem ddProdEquiv_apply_mul {S S₁ S₂ : Subgroup G} (hd : DDDecomp S S₁ S₂) (x : ↥S) :
    (((ddProdEquiv hd x).1 : ↥S₁) : G) * (((ddProdEquiv hd x).2 : ↥S₂) : G) = (x : G) := by
  conv_rhs => rw [← (ddProdEquiv hd).symm_apply_apply x]
  rw [ddProdEquiv_symm_apply]

theorem isPGroup_dd {S S₁ S₂ : Subgroup G} (hd : DDDecomp S S₁ S₂) : IsPGroup 2 ↥S := by
  obtain ⟨a, ha, ⟨e₁⟩⟩ := hd.dih₁
  obtain ⟨b, hb, ⟨e₂⟩⟩ := hd.dih₂
  have hcard : Nat.card ↥S = 2 ^ (a + b + 2) := by
    rw [Nat.card_congr (ddProdEquiv hd).toEquiv, Nat.card_prod,
      Nat.card_congr e₁.toEquiv, Nat.card_congr e₂.toEquiv,
      DihedralGroup.nat_card, DihedralGroup.nat_card]
    have h1 : 2 * 2 ^ a = 2 ^ (a + 1) := (pow_succ' 2 a).symm
    have h2 : 2 * 2 ^ b = 2 ^ (b + 1) := (pow_succ' 2 b).symm
    rw [h1, h2, ← pow_add]
    congr 1
    omega
  exact IsPGroup.of_card (n := a + b + 2) (by rw [hcard])

theorem card_center_of_isDihNonab {D : Subgroup G} (hD : IsDihNonab D) :
    Nat.card (Subgroup.center ↥D) = 2 := by
  obtain ⟨a, ha, ⟨e⟩⟩ := hD
  have hcard : Nat.card (Subgroup.center ↥D) =
      Nat.card (Subgroup.center (DihedralGroup (2 ^ a))) :=
    Nat.card_congr (Subgroup.centerCongr e).toEquiv
  rw [hcard]
  haveI : NeZero (2 ^ a) := ⟨by positivity⟩
  have hne : 2 ^ a ≠ 2 := by
    intro h
    have ha1 : a = 1 := (Nat.pow_right_injective (by norm_num : 2 ≤ 2)) h
    omega
  have heven : Even (2 ^ a) := by
    refine ⟨2 ^ (a - 1), ?_⟩
    rw [← two_mul, ← pow_succ' 2 (a - 1), Nat.sub_add_cancel (by omega : 1 ≤ a)]
  rw [DihedralGroup.center_eq_closure_of_even_ne_two heven hne]
  rw [Nat.card_zpowers, DihedralGroup.orderOf_r]
  have hdiv : 2 ^ a / 2 = 2 ^ (a - 1) := by
    conv_lhs =>
      rw [show 2 ^ a = 2 * 2 ^ (a - 1) by
        rw [← pow_succ' 2 (a - 1), Nat.sub_add_cancel (by omega : 1 ≤ a)]]
    rw [Nat.mul_div_right (2 ^ (a - 1)) (by norm_num : 0 < 2)]
  have hlt : 2 ^ (a - 1) < 2 ^ a := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hval : ((2 ^ a / 2 : ℕ) : ZMod (2 ^ a)).val = 2 ^ (a - 1) := by
    rw [hdiv, ZMod.val_natCast_of_lt hlt]
  rw [hval]
  have hgcd : Nat.gcd (2 ^ a) (2 ^ (a - 1)) = 2 ^ (a - 1) :=
    Nat.gcd_eq_right (Nat.pow_dvd_pow 2 (by omega))
  rw [hgcd, show 2 ^ a = 2 * 2 ^ (a - 1) by
    rw [← pow_succ' 2 (a - 1), Nat.sub_add_cancel (by omega : 1 ≤ a)]]
  rw [Nat.mul_div_left 2 (by positivity)]

end CFSG.GH72
