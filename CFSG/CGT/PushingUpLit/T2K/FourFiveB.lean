module

public import CFSG.CGT.PushingUpLit.T2K.FourFiveA

public section

namespace CFSG.CGT.PushingUpLit.T2K

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L M T A : Subgroup G} {n : ℕ}

theorem card_sl2_field {F : Type} [Field F] [Finite F] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  classical
  have := Fintype.ofFinite F
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    Nat.card_eq_fintype_card, show Fintype.card F ^ 2 - Fintype.card F =
      Fintype.card F * (Fintype.card F - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
    Nat.mul_div_cancel _ (by omega), mul_comm]

@[expose] def ActsAs (L : Subgroup G) (a l : G) : Prop :=
  ∀ v ∈ blockU L, a * v * a⁻¹ = l * v * l⁻¹

omit [Finite G] in
theorem ActsAs.mul {a a' l l' : G} (h : ActsAs L a l) (h' : ActsAs L a' l') (hl' : l' ∈ L) :
    ActsAs L (a * a') (l * l') := by
  intro v hv
  have hv' : l' * v * l'⁻¹ ∈ blockU L := conj_mem_blockU (Subgroup.le_normalizer hl') hv
  have e : a * a' * v * (a * a')⁻¹ = a * (a' * v * a'⁻¹) * a⁻¹ := by group
  rw [e, h' v hv, h _ hv']
  group

omit [Finite G] in
theorem ActsAs.one_of_centralizes {a : G} (h : a ∈ Subgroup.centralizer (blockU L : Set G)) :
    ActsAs L a 1 := by
  intro v hv
  have := Subgroup.mem_centralizer_iff.1 h v hv
  rw [← this]
  group

theorem φ_eq_of_actsAs (h : NatBlock L n) {a l l' : G} (hl : l ∈ L) (hl' : l' ∈ L)
    (h1 : ActsAs L a l) (h2 : ActsAs L a l') :
    h.natData.φ ⟨l, hl⟩ = h.natData.φ ⟨l', hl'⟩ := by
  have hc : l⁻¹ * l' ∈ Subgroup.centralizer (blockU L : Set G) := by
    refine Subgroup.mem_centralizer_iff.2 fun v hv => ?_
    have e1 := h1 v hv
    have e2 := h2 v hv
    have e3 : l' * v * l'⁻¹ = l * v * l⁻¹ := e2.symm.trans e1
    calc v * (l⁻¹ * l') = l⁻¹ * (l * v * l⁻¹) * l' := by group
      _ = l⁻¹ * (l' * v * l'⁻¹) * l' := by rw [e3]
      _ = (l⁻¹ * l') * v := by group
  have hO : l⁻¹ * l' ∈ oTwoIn L := by
    rw [← h.inf_centralizer_blockU]
    exact ⟨L.mul_mem (L.inv_mem hl) hl', hc⟩
  have h3 := (h.natData.φ_ker ⟨l⁻¹ * l', L.mul_mem (L.inv_mem hl) hl'⟩).2 hO
  have e : (⟨l⁻¹ * l', L.mul_mem (L.inv_mem hl) hl'⟩ : ↥L) = (⟨l, hl⟩ : ↥L)⁻¹ * ⟨l', hl'⟩ := rfl
  rw [e, map_mul, map_inv, inv_mul_eq_one] at h3
  exact h3

namespace Hyp45

variable (H : Hyp45 L M T A n)
include H

theorem blockZ_le_A : blockZ L ≤ A := by
  intro z hz
  have hzV : z ∈ blockU L := hz.1
  have : z ∈ blockU L ⊓ Subgroup.centralizer (A : Set G) := by
    refine ⟨hzV, Subgroup.mem_centralizer_iff.2 fun a ha => ?_⟩
    obtain ⟨l, hl, hact⟩ := H.acts_as a ha
    have h1 := hact z hzV
    have h2 : l * z * l⁻¹ = z := by
      have := Subgroup.mem_centralizer_iff.1 hz.2 l hl
      rw [this, mul_inv_cancel_right]
    rw [h2] at h1
    calc a * z = (a * z * a⁻¹) * a := by group
      _ = z * a := by rw [h1]
  rw [H.centralizer_blockU_eq] at this
  exact this.2

theorem inv_mul_mem_centralizer {a l : G} (ha : a ∈ A) (hl : l ∈ L) (hact : ActsAs L a l) :
    l⁻¹ * a ∈ M ⊓ Subgroup.centralizer (blockU L : Set G) := by
  refine ⟨M.mul_mem (M.inv_mem (H.le hl)) (H.A_le_M ha), Subgroup.mem_centralizer_iff.2
    fun v hv => ?_⟩
  have h1 := hact v hv
  calc v * (l⁻¹ * a) = l⁻¹ * (l * v * l⁻¹) * a := by group
    _ = l⁻¹ * (a * v * a⁻¹) * a := by rw [h1]
    _ = (l⁻¹ * a) * v := by group

theorem acts_as' (a : ↥A) : ∃ l : G, l ∈ L ∧ ActsAs L a l := by
  obtain ⟨l, hl, h⟩ := H.acts_as a a.2
  exact ⟨l, hl, h⟩

noncomputable def lOf (a : ↥A) : G := Classical.choose (H.acts_as' a)

theorem lOf_mem (a : ↥A) : H.lOf a ∈ L := (Classical.choose_spec (H.acts_as' a)).1

theorem actsAs_lOf (a : ↥A) : ActsAs L a (H.lOf a) := (Classical.choose_spec (H.acts_as' a)).2

noncomputable def rhoFun (a : ↥A) : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n) :=
  H.block.natData.φ ⟨H.lOf a, H.lOf_mem a⟩

theorem rhoFun_eq {a : ↥A} {l : G} (hl : l ∈ L) (hact : ActsAs L a l) :
    H.rhoFun a = H.block.natData.φ ⟨l, hl⟩ :=
  φ_eq_of_actsAs H.block _ hl (H.actsAs_lOf a) hact

noncomputable def rho : ↥A →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n) :=
  MonoidHom.mk' H.rhoFun fun a a' => by
    have h1 := H.rhoFun_eq (a := a * a') (L.mul_mem (H.lOf_mem a) (H.lOf_mem a'))
      ((H.actsAs_lOf a).mul (H.actsAs_lOf a') (H.lOf_mem a'))
    rw [h1]
    have h2 : (⟨H.lOf a * H.lOf a', L.mul_mem (H.lOf_mem a) (H.lOf_mem a')⟩ : ↥L) =
        ⟨_, H.lOf_mem a⟩ * ⟨_, H.lOf_mem a'⟩ := rfl
    rw [h2, map_mul]
    rfl

theorem rho_apply_eq {a : ↥A} {l : G} (hl : l ∈ L) (hact : ActsAs L a l) :
    H.rho a = H.block.natData.φ ⟨l, hl⟩ := H.rhoFun_eq hl hact

theorem rho_eq_one_iff (a : ↥A) :
    H.rho a = 1 ↔ (a : G) ∈ Subgroup.centralizer (blockU L : Set G) := by
  constructor
  · intro h1
    have h2 : H.block.natData.φ ⟨H.lOf a, H.lOf_mem a⟩ = 1 :=
      (H.rho_apply_eq (H.lOf_mem a) (H.actsAs_lOf a)).symm.trans h1
    have hO := (H.block.natData.φ_ker _).1 h2
    refine Subgroup.mem_centralizer_iff.2 fun v hv => ?_
    have h3 := H.actsAs_lOf a v hv
    have h4 : H.lOf a * v * (H.lOf a)⁻¹ = v := by
      have := blockU_comm_of_short H.block.short v hv _ hO
      rw [← this, mul_inv_cancel_right]
    rw [h4] at h3
    calc v * a = (a * v * (a : G)⁻¹) * a := by rw [h3]
      _ = a * v := by group
  · intro h1
    have := H.rho_apply_eq (a := a) (L.one_mem) (ActsAs.one_of_centralizes h1)
    rw [this]
    exact (H.block.natData.φ_ker ⟨1, L.one_mem⟩).2 (oTwoIn L).one_mem

theorem ker_rho : H.rho.ker = (A ⊓ Subgroup.centralizer (blockU L : Set G)).subgroupOf A := by
  ext a
  rw [MonoidHom.mem_ker, H.rho_eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun h => ⟨a.2, h⟩, fun h => h.2⟩

theorem card_range_rho : Nat.card ↥H.rho.range = 2 ^ n := by
  have e := QuotientGroup.quotientKerEquivRange H.rho
  rw [← Nat.card_congr e.toEquiv, H.ker_rho]
  exact H.index_centralizer

theorem odd_index_range_rho : Odd H.rho.range.index := by
  have hq : Nat.card (GaloisField 2 n) = 2 ^ n :=
    GaloisField.card 2 n (by have := H.block.two_le; omega)
  have h1 := Subgroup.index_mul_card H.rho.range
  rw [H.card_range_rho, card_sl2_field, hq] at h1
  have hpos : 0 < 2 ^ n := by positivity
  have h2 : H.rho.range.index = (2 ^ n) ^ 2 - 1 := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h1, mul_comm]
  rw [h2]
  have hn : 1 ≤ n := by have := H.block.two_le; omega
  have h3 : 2 ≤ (2 ^ n) ^ 2 := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      _ ≤ (2 ^ n) ^ 2 := by
        rw [sq]
        exact Nat.le_mul_of_pos_left _ hpos
  have h4 : Even ((2 ^ n) ^ 2) := by
    rw [← pow_mul]
    exact (Nat.even_pow.2 ⟨even_two, by omega⟩)
  obtain ⟨k, hk⟩ := h4
  exact ⟨k - 1, by omega⟩

end Hyp45

end CFSG.CGT.PushingUpLit.T2K
