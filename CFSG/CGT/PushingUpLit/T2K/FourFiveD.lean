module

public import CFSG.CGT.PushingUpLit.T2K.FourFiveC

public section

namespace CFSG.CGT.PushingUpLit.T2K

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L M T A : Subgroup G} {n : ℕ}

theorem mem_of_isMaxElemAbelian {X : Subgroup G} (hX : IsMaxElemAbelian T X) {t : G} (ht : t ∈ T)
    (ht2 : t ^ 2 = 1) (hc : ∀ x ∈ X, x * t = t * x) : t ∈ X := by
  have hZ : IsElemAbelian 2 (Subgroup.zpowers t) := by
    refine isElemAbelian_of_forall' (fun a ha b hb => ?_) (fun a ha => ?_)
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact (Commute.zpow_zpow_self t i j).eq
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht2, one_zpow]
  have hcomm : ∀ a ∈ X, ∀ y ∈ Subgroup.zpowers t, a * y = y * a := by
    intro a ha y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ((Commute.zpow_right (show Commute a t from hc a ha) i)).eq
  have hAx := isElemAbelian_sup' hX.2.1 hZ hcomm
  have hle : X ⊔ Subgroup.zpowers t ≤ T := sup_le hX.1 ((Subgroup.zpowers_le).2 ht)
  have hcard := hX.2.2 _ hle hAx
  have heq : X ⊔ Subgroup.zpowers t = X := by
    symm
    exact Subgroup.eq_of_le_of_card_ge le_sup_left hcard
  have : t ∈ X ⊔ Subgroup.zpowers t := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  rwa [heq] at this

theorem odd_sq_two_pow_sub_one (hn : 1 ≤ n) : Odd ((2 ^ n) ^ 2 - 1) := by
  have hpos : 0 < 2 ^ n := by positivity
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

theorem card_le_of_isPGroup_sl2 {X : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))}
    (hX : IsPGroup 2 X) (hn : 1 ≤ n) : Nat.card X ≤ 2 ^ n := by
  have hq : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have hdvd : Nat.card X ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
    Subgroup.card_subgroup_dvd_card X
  rw [card_sl2_field, hq] at hdvd
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hX
  rw [hk] at hdvd ⊢
  have hcop : Nat.Coprime (2 ^ k) ((2 ^ n) ^ 2 - 1) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 (odd_sq_two_pow_sub_one hn))
  exact Nat.le_of_dvd (by positivity) (hcop.dvd_of_dvd_mul_right hdvd)

omit [Finite G] in
theorem commute_S_V {s v : G} (hs : s ∈ Subgroup.centralizer (L : Set G)) (hv : v ∈ blockU L) :
    s * v = v * s :=
  (Subgroup.mem_centralizer_iff.1 hs v (blockU_le L hv)).symm

namespace Hyp45

variable (H : Hyp45 L M T A n)
include H

theorem lOf_mem_T (a : ↥A) : H.lOf a ∈ T := by
  have hu := H.inv_mul_mem_centralizer a.2 (H.lOf_mem a) (H.actsAs_lOf a)
  exact H.block.mem_of_mul_mem_centralizer H.le H.normal H.sylow (H.A_le_T a.2) (H.lOf_mem a)
    hu.2

theorem tOf_mem (a : ↥A) :
    (H.lOf a)⁻¹ * (a : G) ∈ T ⊓ Subgroup.centralizer (blockU L : Set G) :=
  ⟨T.mul_mem (T.inv_mem (H.lOf_mem_T a)) (H.A_le_T a.2),
    (H.inv_mul_mem_centralizer a.2 (H.lOf_mem a) (H.actsAs_lOf a)).2⟩

theorem tOf_mem_M (a : ↥A) :
    (H.lOf a)⁻¹ * (a : G) ∈ M ⊓ Subgroup.centralizer (blockU L : Set G) :=
  H.inv_mul_mem_centralizer a.2 (H.lOf_mem a) (H.actsAs_lOf a)

theorem sq_rel (a : ↥A) :
    ∃ w ∈ blockU L, (H.lOf a) ^ 2 * w * ((H.lOf a)⁻¹ * (a : G)) ^ 2 = 1 := by
  have ha2 : (a : G) ^ 2 = 1 := H.A_isElemAbelian.2 a a.2
  have ht := H.tOf_mem_M a
  have hw : ⁅(H.lOf a)⁻¹ * (a : G), (H.lOf a)⁻¹⁆ ∈ blockU L :=
    H.block.comm_centralizer_mem_blockU H.normal ht _ (L.inv_mem (H.lOf_mem a))
  refine ⟨⁅(H.lOf a)⁻¹ * (a : G), (H.lOf a)⁻¹⁆⁻¹, (blockU L).inv_mem hw, ?_⟩
  have key : (H.lOf a) ^ 2 * ⁅(H.lOf a)⁻¹ * (a : G), (H.lOf a)⁻¹⁆⁻¹ *
      ((H.lOf a)⁻¹ * (a : G)) ^ 2 = (a : G) ^ 2 := by
    simp only [commutatorElement_def, pow_two]
    group
  rw [key, ha2]

theorem sq_lOf_mem_oTwoIn (a : ↥A) : (H.lOf a) ^ 2 ∈ oTwoIn L := by
  obtain ⟨w, hw, hrel⟩ := H.sq_rel a
  have ht2 : ((H.lOf a)⁻¹ * (a : G)) ^ 2 ∈ Subgroup.centralizer (L : Set G) :=
    H.block.sq_mem_centralizer H.normal (H.tOf_mem_M a)
  have e : (H.lOf a) ^ 2 = (w * ((H.lOf a)⁻¹ * (a : G)) ^ 2)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← mul_assoc]; exact hrel)
  rw [← H.block.inf_centralizer_blockU]
  refine ⟨L.pow_mem (H.lOf_mem a) 2, ?_⟩
  rw [e]
  exact (Subgroup.centralizer (blockU L : Set G)).inv_mem
    (mul_mem (H.blockU_le_centralizer hw) (Subgroup.centralizer_le (blockU_le L) ht2))

theorem sq_t_eq_one_of_sq_mem (hZ : blockZ L = ⊥) (a : ↥A) (hr2 : (H.lOf a) ^ 2 ∈ blockU L) :
    ((H.lOf a)⁻¹ * (a : G)) ^ 2 = 1 := by
  obtain ⟨w, hw, hrel⟩ := H.sq_rel a
  have ht2 : ((H.lOf a)⁻¹ * (a : G)) ^ 2 ∈ Subgroup.centralizer (L : Set G) :=
    H.block.sq_mem_centralizer H.normal (H.tOf_mem_M a)
  have e : ((H.lOf a)⁻¹ * (a : G)) ^ 2 = ((H.lOf a) ^ 2 * w)⁻¹ := eq_inv_of_mul_eq_one_right hrel
  have hV : ((H.lOf a)⁻¹ * (a : G)) ^ 2 ∈ blockU L := by
    rw [e]
    exact (blockU L).inv_mem (mul_mem hr2 hw)
  have hZ' : ((H.lOf a)⁻¹ * (a : G)) ^ 2 ∈ blockZ L := ⟨hV, ht2⟩
  rw [hZ] at hZ'
  exact Subgroup.mem_bot.1 hZ'

theorem bGrp_eq_sup : bGrp L A = (A ⊓ Subgroup.centralizer (L : Set G)) ⊔ blockU L := by
  unfold bGrp
  rw [H.inf_centralizer_eq]
  apply le_antisymm
  · exact sup_le (sup_le le_sup_left (inf_le_left.trans le_sup_right)) le_sup_right
  · exact sup_le (le_sup_left.trans le_sup_left) (le_sup_right)

theorem bGrp_eq_sup_S (hS : IsElemAbelian 2 (T ⊓ Subgroup.centralizer (L : Set G))) :
    bGrp L A = (T ⊓ Subgroup.centralizer (L : Set G)) ⊔ blockU L := by
  rw [H.bGrp_eq_sup, H.inf_centralizer_L_eq hS]

theorem S_le_A (hS : IsElemAbelian 2 (T ⊓ Subgroup.centralizer (L : Set G))) :
    T ⊓ Subgroup.centralizer (L : Set G) ≤ A := fun _ hs =>
  ((H.inf_centralizer_L_eq hS).ge hs).1

theorem tOf_comm_B (hS : IsElemAbelian 2 (T ⊓ Subgroup.centralizer (L : Set G))) (a : ↥A) :
    ∀ b ∈ bGrp L A, b * ((H.lOf a)⁻¹ * (a : G)) = ((H.lOf a)⁻¹ * (a : G)) * b := by
  intro b hb
  rw [H.bGrp_eq_sup_S hS] at hb
  have hcomm : ∀ x ∈ T ⊓ Subgroup.centralizer (L : Set G), ∀ y ∈ blockU L, x * y = y * x :=
    fun x hx y hy => commute_S_V hx.2 hy
  obtain ⟨s, hs, v, hv, rfl⟩ := exists_mul_of_mem_sup' hcomm hb
  have hsr : s * (H.lOf a)⁻¹ = (H.lOf a)⁻¹ * s :=
    (Subgroup.mem_centralizer_iff.1 hs.2 _ (L.inv_mem (H.lOf_mem a))).symm
  have hsa : s * (a : G) = (a : G) * s := H.A_comm (H.S_le_A hS hs) a.2
  have hts : s * ((H.lOf a)⁻¹ * (a : G)) = ((H.lOf a)⁻¹ * (a : G)) * s := by
    calc s * ((H.lOf a)⁻¹ * (a : G)) = (s * (H.lOf a)⁻¹) * (a : G) := by rw [mul_assoc]
      _ = (H.lOf a)⁻¹ * (s * (a : G)) := by rw [hsr, mul_assoc]
      _ = (H.lOf a)⁻¹ * ((a : G) * s) := by rw [hsa]
      _ = ((H.lOf a)⁻¹ * (a : G)) * s := by rw [mul_assoc]
  have htv : v * ((H.lOf a)⁻¹ * (a : G)) = ((H.lOf a)⁻¹ * (a : G)) * v :=
    Subgroup.mem_centralizer_iff.1 (H.tOf_mem a).2 v hv
  calc s * v * ((H.lOf a)⁻¹ * (a : G)) = s * (v * ((H.lOf a)⁻¹ * (a : G))) := mul_assoc _ _ _
    _ = s * (((H.lOf a)⁻¹ * (a : G)) * v) := by rw [htv]
    _ = (s * ((H.lOf a)⁻¹ * (a : G))) * v := (mul_assoc _ _ _).symm
    _ = (((H.lOf a)⁻¹ * (a : G)) * s) * v := by rw [hts]
    _ = ((H.lOf a)⁻¹ * (a : G)) * (s * v) := mul_assoc _ _ _

theorem exists_mul_of_sq_mem (hZ : blockZ L = ⊥)
    (hS : IsElemAbelian 2 (T ⊓ Subgroup.centralizer (L : Set G))) (a : ↥A)
    (hr2 : (H.lOf a) ^ 2 ∈ blockU L) :
    ∃ c ∈ A ⊓ L, ∃ s ∈ T ⊓ Subgroup.centralizer (L : Set G), (a : G) = c * s := by
  have ht2 := H.sq_t_eq_one_of_sq_mem hZ a hr2
  have htB : (H.lOf a)⁻¹ * (a : G) ∈ bGrp L A :=
    mem_of_isMaxElemAbelian H.isMaxElemAbelian_B (H.tOf_mem a).1 ht2 (H.tOf_comm_B hS a)
  rw [H.bGrp_eq_sup_S hS] at htB
  have hcomm : ∀ x ∈ T ⊓ Subgroup.centralizer (L : Set G), ∀ y ∈ blockU L, x * y = y * x :=
    fun x hx y hy => commute_S_V hx.2 hy
  obtain ⟨s, hs, v, hv, hsv⟩ := exists_mul_of_mem_sup' hcomm htB
  have hrs : (H.lOf a) * s = s * (H.lOf a) := (Subgroup.mem_centralizer_iff.1 hs.2 _
    (H.lOf_mem a)).symm.symm
  have hvs : v * s = s * v := Subgroup.mem_centralizer_iff.1 hs.2 v (blockU_le L hv)
  have hrv : (H.lOf a * v) * s = s * (H.lOf a * v) :=
    Subgroup.mem_centralizer_iff.1 hs.2 _ (L.mul_mem (H.lOf_mem a) (blockU_le L hv))
  have ha : (a : G) = (H.lOf a * v) * s := by
    calc (a : G) = H.lOf a * ((H.lOf a)⁻¹ * (a : G)) := by group
      _ = H.lOf a * (s * v) := by rw [hsv]
      _ = (H.lOf a * s) * v := by rw [mul_assoc]
      _ = (s * H.lOf a) * v := by rw [hrs]
      _ = s * (H.lOf a * v) := by rw [mul_assoc]
      _ = (H.lOf a * v) * s := hrv.symm
  refine ⟨H.lOf a * v, ⟨?_, L.mul_mem (H.lOf_mem a) (blockU_le L hv)⟩, s, hs, ha⟩
  have : H.lOf a * v = (a : G) * s⁻¹ := by
    rw [ha]
    group
  rw [this]
  exact A.mul_mem a.2 (A.inv_mem (H.S_le_A hS hs))

theorem exists_mul_of_oTwoIn_eq (hZ : blockZ L = ⊥)
    (hS : IsElemAbelian 2 (T ⊓ Subgroup.centralizer (L : Set G))) (hO : oTwoIn L = blockU L)
    (a : ↥A) : ∃ c ∈ A ⊓ L, ∃ s ∈ T ⊓ Subgroup.centralizer (L : Set G), (a : G) = c * s :=
  H.exists_mul_of_sq_mem hZ hS a (hO ▸ H.sq_lOf_mem_oTwoIn a)

theorem rho_range_eq :
    H.rho.range = ((T ⊓ L).subgroupOf L).map H.block.natData.φ := by
  have hn : 1 ≤ n := by have := H.block.two_le; omega
  apply Subgroup.eq_of_le_of_card_ge
  · rintro g ⟨a, rfl⟩
    exact ⟨⟨H.lOf a, H.lOf_mem a⟩, Subgroup.mem_subgroupOf.2 ⟨H.lOf_mem_T a, H.lOf_mem a⟩,
      (H.rho_apply_eq (H.lOf_mem a) (H.actsAs_lOf a)).symm⟩
  · have hTL : IsPGroup 2 (T ⊓ L : Subgroup G) := H.sylow.isPGroup.to_le inf_le_left
    have hX : IsPGroup 2 ((T ⊓ L).subgroupOf L) :=
      hTL.comap_of_injective L.subtype L.subtype_injective
    have hmap : IsPGroup 2 (((T ⊓ L).subgroupOf L).map H.block.natData.φ) := hX.map _
    rw [H.card_range_rho]
    exact card_le_of_isPGroup_sl2 hmap hn

theorem mem_A_of_sq_eq_one (hZ : blockZ L = ⊥)
    (hS : IsElemAbelian 2 (T ⊓ Subgroup.centralizer (L : Set G))) (hO : oTwoIn L = blockU L)
    {x : G} (hxL : x ∈ L) (hxT : x ∈ T) (hxV : x ∉ blockU L) (hx2 : x ^ 2 = 1) : x ∈ A := by
  let D := H.block.natData
  have hxO : x ∉ oTwoIn L := by rwa [hO]
  have hφx : D.φ ⟨x, hxL⟩ ∈ H.rho.range := by
    rw [H.rho_range_eq]
    exact ⟨⟨x, hxL⟩, Subgroup.mem_subgroupOf.2 ⟨hxT, hxL⟩, rfl⟩
  obtain ⟨a, ha⟩ := hφx
  obtain ⟨c, ⟨hcA, hcL⟩, s, hs, hacs⟩ := H.exists_mul_of_oTwoIn_eq hZ hS hO a
  have hactc : ActsAs L (a : G) c := by
    intro v hv
    rw [hacs]
    have hsv : s * v * s⁻¹ = v := by
      have := Subgroup.mem_centralizer_iff.1 hs.2 v (blockU_le L hv)
      rw [← this, mul_inv_cancel_right]
    calc c * s * v * (c * s)⁻¹ = c * (s * v * s⁻¹) * c⁻¹ := by group
      _ = c * v * c⁻¹ := by rw [hsv]
  have hρc : H.rho a = D.φ ⟨c, hcL⟩ := H.rho_apply_eq hcL hactc
  have hφeq : D.φ ⟨x, hxL⟩ = D.φ ⟨c, hcL⟩ := by rw [← ha, hρc]
  have hvV : c⁻¹ * x ∈ blockU L := by
    rw [← hO]
    refine (D.φ_ker ⟨c⁻¹ * x, L.mul_mem (L.inv_mem hcL) hxL⟩).1 ?_
    have e : (⟨c⁻¹ * x, L.mul_mem (L.inv_mem hcL) hxL⟩ : ↥L) =
        (⟨c, hcL⟩ : ↥L)⁻¹ * ⟨x, hxL⟩ := rfl
    rw [e, map_mul, map_inv, ← hφeq, inv_mul_cancel]
  have hcρ : H.rho ⟨c, hcA⟩ = D.φ ⟨c, hcL⟩ := H.rho_apply_eq hcL fun v _ => rfl
  have hcV : c ∉ Subgroup.centralizer (blockU L : Set G) := by
    intro hc
    have h1 := (H.rho_eq_one_iff ⟨c, hcA⟩).2 hc
    rw [hcρ, ← hφeq] at h1
    exact hxO ((D.φ_ker ⟨x, hxL⟩).1 h1)
  have hc2 : c ^ 2 = 1 := H.A_isElemAbelian.2 c hcA
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hc2)
  have hv2 : (c⁻¹ * x) ^ 2 = 1 := H.block.sq_eq_one_of_mem_blockU hvV
  have hvi : (c⁻¹ * x)⁻¹ = c⁻¹ * x := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hv2)
  have hcv : c * (c⁻¹ * x) * c⁻¹ = c⁻¹ * x := by
    have h1 : x * x = 1 := by rw [← pow_two]; exact hx2
    calc c * (c⁻¹ * x) * c⁻¹ = x * c⁻¹ := by group
      _ = x * c := by rw [hci]
      _ = (x * x) * (x⁻¹ * c) := by group
      _ = x⁻¹ * c := by rw [h1, one_mul]
      _ = (c⁻¹ * x)⁻¹ := by group
      _ = c⁻¹ * x := hvi
  have hfix : ((H.rho ⟨c, hcA⟩ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :
      Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec (D.ψe (c⁻¹ * x)) = D.ψe (c⁻¹ * x) := by
    rw [hcρ, ← D.ψe_conj hcL hvV, hcv]
  have hvCA := H.mem_centralizer_of_fixed_one hcA hcV hvV hfix
  rw [H.centralizer_blockU_eq] at hvCA
  have e : x = c * (c⁻¹ * x) := by group
  rw [e]
  exact A.mul_mem hcA hvCA.2

theorem eq_of_isMaxElemAbelian (hZ : blockZ L = ⊥)
    (hS : IsElemAbelian 2 (T ⊓ Subgroup.centralizer (L : Set G))) (hO : oTwoIn L = blockU L)
    {A' : Subgroup G} (hA' : IsMaxElemAbelian T A')
    (hA'V : ¬ A' ≤ Subgroup.centralizer (blockU L : Set G)) : A' = A := by
  have H' : Hyp45 L M T A' n := ⟨H.block, H.le, H.normal, H.sylow, hA', hA'V⟩
  have hinv : ∀ c' ∈ A' ⊓ L, c' ∉ blockU L → c' ∈ A := fun c' hc' hcV =>
    H.mem_A_of_sq_eq_one hZ hS hO hc'.2 (H'.A_le_T hc'.1) hcV (H'.A_isElemAbelian.2 c' hc'.1)
  obtain ⟨d, hdA', hdL, hdV⟩ : ∃ d ∈ A', d ∈ L ∧ d ∉ blockU L := by
    by_contra hcon
    push Not at hcon
    apply hA'V
    intro a₀ ha₀
    have ⟨c, hc, s, hs, hacs⟩ := H'.exists_mul_of_oTwoIn_eq hZ hS hO ⟨a₀, ha₀⟩
    have hcV : c ∈ blockU L := hcon c hc.1 hc.2
    rw [show a₀ = c * s from hacs]
    exact (Subgroup.centralizer (blockU L : Set G)).mul_mem (H.blockU_le_centralizer hcV)
      (Subgroup.centralizer_le (blockU_le L) hs.2)
  have hdA : d ∈ A := hinv d ⟨hdA', hdL⟩ hdV
  refine Subgroup.eq_of_le_of_card_ge (fun a' ha' => ?_)
    (hA'.2.2 A H.A_le_T H.A_isElemAbelian)
  obtain ⟨c', hc', s, hs, hacs⟩ := H'.exists_mul_of_oTwoIn_eq hZ hS hO ⟨a', ha'⟩
  have hsA : s ∈ A := H.S_le_A hS hs
  have hc'A : c' ∈ A := by
    by_cases hcV : c' ∈ blockU L
    ·
      have hdc : d * c' ∈ A' ⊓ L := ⟨A'.mul_mem hdA' hc'.1, L.mul_mem hdL hc'.2⟩
      have hdcV : d * c' ∉ blockU L := fun h => hdV (by
        have := (blockU L).mul_mem h ((blockU L).inv_mem hcV)
        simpa using this)
      have h1 : d * c' ∈ A := hinv _ hdc hdcV
      have := A.mul_mem (A.inv_mem hdA) h1
      simpa using this
    · exact hinv c' hc' hcV
  rw [show a' = c' * s from hacs]
  exact A.mul_mem hc'A hsA

end Hyp45

end CFSG.CGT.PushingUpLit.T2K
