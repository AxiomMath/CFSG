module

import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Assembly.Defs

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open

variable {G : Type*} [Group G]

theorem fi_cube_mul {x y c : G} (hc : c = x * y * x⁻¹ * y⁻¹) (hcen : ∀ g : G, c * g = g * c)
    (hc3 : c ^ 3 = 1) : (x * y) ^ 3 = x ^ 3 * y ^ 3 := by
  have e1 : y * x = c⁻¹ * (x * y) := by rw [hc]; group
  have hci : ∀ g : G, c⁻¹ * g = g * c⁻¹ := fun g => by
    calc c⁻¹ * g = c⁻¹ * (g * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * g) * c⁻¹ := by rw [hcen g]
      _ = g * c⁻¹ := by group
  have e2 : c⁻¹ * c⁻¹ * c⁻¹ = 1 := by
    have : c⁻¹ * c⁻¹ * c⁻¹ = (c ^ 3)⁻¹ := by group
    rw [this, hc3, inv_one]
  calc (x * y) ^ 3 = x * (y * x) * (y * x) * y := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = x * (c⁻¹ * (x * y)) * (c⁻¹ * (x * y)) * y := by rw [e1]
    _ = c⁻¹ * c⁻¹ * (x * x * y * x * y * y) := by
      calc x * (c⁻¹ * (x * y)) * (c⁻¹ * (x * y)) * y
          = (x * c⁻¹) * (x * y) * (c⁻¹ * (x * y)) * y := by group
        _ = (c⁻¹ * x) * (x * y) * (c⁻¹ * (x * y)) * y := by rw [← hci x]
        _ = c⁻¹ * (x * x * y * (c⁻¹ * (x * y)) * y) := by group
        _ = c⁻¹ * (x * x * y * c⁻¹ * (x * y) * y) := by group
        _ = c⁻¹ * (c⁻¹ * (x * x * y * (x * y) * y)) := by
          rw [show x * x * y * c⁻¹ = c⁻¹ * (x * x * y) by
            rw [← hci (x * x * y)]]
          group
        _ = c⁻¹ * c⁻¹ * (x * x * y * x * y * y) := by group
    _ = c⁻¹ * c⁻¹ * (x * x * (y * x) * y * y) := by group
    _ = c⁻¹ * c⁻¹ * (x * x * (c⁻¹ * (x * y)) * y * y) := by rw [e1]
    _ = c⁻¹ * c⁻¹ * c⁻¹ * (x * x * x * y * y * y) := by
      calc c⁻¹ * c⁻¹ * (x * x * (c⁻¹ * (x * y)) * y * y)
          = c⁻¹ * c⁻¹ * ((x * x * c⁻¹) * (x * y) * y * y) := by group
        _ = c⁻¹ * c⁻¹ * ((c⁻¹ * (x * x)) * (x * y) * y * y) := by rw [← hci (x * x)]
        _ = c⁻¹ * c⁻¹ * c⁻¹ * (x * x * x * y * y * y) := by group
    _ = x ^ 3 * y ^ 3 := by
      rw [e2, one_mul]
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]

section Basic

variable [Finite G]

omit [Finite G] in
theorem fi_comm_of_elemAbelian {E : Subgroup G} (hE : IsElemAbelian 3 E) {a b : G} (ha : a ∈ E)
    (hb : b ∈ E) : a * b = b * a := CFSG.Open.IsElemAbelian.comm hE ha hb

omit [Finite G] in
theorem fi_elemAbelian_of_le {E K : Subgroup G} (hE : IsElemAbelian 3 E) (hK : K ≤ E) :
    IsElemAbelian 3 K := CFSG.Open.IsElemAbelian.mono hE hK

omit [Finite G] in
theorem fi_elemAbelian_sup {S T : Subgroup G} (hS : IsElemAbelian 3 S) (hT : IsElemAbelian 3 T)
    (hST : ∀ s ∈ S, ∀ t ∈ T, s * t = t * s) : IsElemAbelian 3 (S ⊔ T) :=
  CFSG.Open.IsElemAbelian.sup_of_commute hS hT hST

theorem fi_exists_card_27 {E0 : Subgroup G} (hE : IsElemAbelian 3 E0) (h27 : 3 ^ 3 ∣ Nat.card E0) :
    ∃ E : Subgroup G, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥E0) 3 (n := 3) h27
  refine ⟨K.map E0.subtype, ?_, ?_⟩
  · refine fi_elemAbelian_of_le hE ?_
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rw [Subgroup.card_map_of_injective E0.subtype_injective, hK]

@[expose] def fiComHom {Z : Subgroup G} (hZc : Z ≤ Subgroup.center G)
    (hcomm : ∀ x y : G, x * y * x⁻¹ * y⁻¹ ∈ Z) (x : G) : G →* ↥Z where
  toFun y := ⟨x * y * x⁻¹ * y⁻¹, hcomm x y⟩
  map_one' := Subtype.ext (by simp)
  map_mul' y z := by
    apply Subtype.ext
    have hc2 : y * (x * z * x⁻¹ * z⁻¹) = (x * z * x⁻¹ * z⁻¹) * y :=
      Subgroup.mem_center_iff.1 (hZc (hcomm x z)) y
    show x * (y * z) * x⁻¹ * (y * z)⁻¹ = (x * y * x⁻¹ * y⁻¹) * (x * z * x⁻¹ * z⁻¹)
    calc x * (y * z) * x⁻¹ * (y * z)⁻¹
        = (x * y * x⁻¹ * y⁻¹) * (y * (x * z * x⁻¹ * z⁻¹)) * y⁻¹ := by group
      _ = (x * y * x⁻¹ * y⁻¹) * ((x * z * x⁻¹ * z⁻¹) * y) * y⁻¹ := by rw [hc2]
      _ = (x * y * x⁻¹ * y⁻¹) * (x * z * x⁻¹ * z⁻¹) := by group

@[expose] def fiCubeHom {Z : Subgroup G} (hZc : Z ≤ Subgroup.center G)
    (hcomm : ∀ x y : G, x * y * x⁻¹ * y⁻¹ ∈ Z) (hZ3 : ∀ z ∈ Z, z ^ 3 = 1)
    (hcube : ∀ x : G, x ^ 3 ∈ Z) : G →* ↥Z where
  toFun x := ⟨x ^ 3, hcube x⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (fi_cube_mul rfl
    (fun g => (Subgroup.mem_center_iff.1 (hZc (hcomm x y)) g).symm) (hZ3 _ (hcomm x y)))

theorem fiHom_index_le {Z : Subgroup G} (f : G →* ↥Z) (hZ : Nat.card Z ≤ 3) : f.ker.index ≤ 3 := by
  rw [Subgroup.index_ker]
  exact (Subgroup.card_le_card_group _).trans hZ

omit [Finite G] in
theorem fi_elemAbelian_zpowers {x : G} (hx : x ^ 3 = 1) : IsElemAbelian 3 (Subgroup.zpowers x) :=
  CFSG.Open.isElemAbelian_zpowers hx

theorem fi_three_mul_le (hG : IsPGroup 3 G) {H H' : Subgroup G} (hle : H ≤ H') (hne : H ≠ H') :
    3 * Nat.card H ≤ Nat.card H' := by
  obtain ⟨a, ha⟩ := (hG.to_subgroup H).exists_card_eq
  obtain ⟨b, hb⟩ := (hG.to_subgroup H').exists_card_eq
  have hd : Nat.card H ∣ Nat.card H' := Subgroup.card_dvd_of_le hle
  rw [ha, hb] at hd
  have hab : a ≤ b := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hd
  have hne' : a ≠ b := by
    rintro rfl
    exact hne (Subgroup.eq_of_le_of_card_ge hle (by rw [ha, hb]))
  rw [ha, hb, ← pow_succ']
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

end Basic

theorem i247fi_exists_elemAbelian_card_27 [Finite G] (hG : IsPGroup 3 G) {Z : Subgroup G}
    (hZc : Z ≤ Subgroup.center G) (hZ : Nat.card Z ≤ 3)
    (hcube : ∀ x : G, x ^ 3 ∈ Z) (hcomm : ∀ x y : G, x * y * x⁻¹ * y⁻¹ ∈ Z)
    (hcard : 3 ^ 4 * Nat.card Z ≤ Nat.card G) :
    ∃ E : Subgroup G, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZe : IsElemAbelian 3 Z := by
    have hZ3 : ∀ z ∈ Z, z ^ 3 = 1 := by
      obtain ⟨k, hk⟩ := (hG.to_subgroup Z).exists_card_eq
      have hk1 : k ≤ 1 := by
        by_contra h
        have : 3 ^ 2 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
        rw [← hk] at this
        omega
      intro z hz
      have : (⟨z, hz⟩ : ↥Z) ^ Nat.card Z = 1 := pow_card_eq_one'
      have h2 : z ^ Nat.card Z = 1 := congrArg Subtype.val this
      rw [hk] at h2
      interval_cases k
      · have : z = 1 := by simpa using h2
        simp [this]
      · simpa using h2
    exact ⟨⟨⟨fun a b => Subtype.ext (Subgroup.mem_center_iff.1 (hZc b.2) a)⟩⟩, hZ3⟩
  have hZ3 : ∀ z ∈ Z, z ^ 3 = 1 := hZe.2
  obtain ⟨k, hk⟩ := (hG.to_subgroup Z).exists_card_eq
  have hZcard : Nat.card Z = 1 ∨ Nat.card Z = 3 := by
    have hk1 : k ≤ 1 := by
      by_contra h
      have : 3 ^ 2 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [← hk] at this
      omega
    interval_cases k
    · left; simpa using hk
    · right; simpa using hk
  rcases hZcard with h1 | h3
  ·
    have hZbot : Z = ⊥ := Subgroup.card_eq_one.1 h1
    have hE : IsElemAbelian 3 (⊤ : Subgroup G) := by
      refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x _ => ?_⟩
      · have h := hcomm a b
        rw [hZbot, Subgroup.mem_bot] at h
        exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h)
      · have := hcube x
        rw [hZbot, Subgroup.mem_bot] at this
        exact this
    refine fi_exists_card_27 hE ?_
    obtain ⟨m, hm⟩ := hG.exists_card_eq
    rw [Subgroup.card_top, hm]
    rw [h1, mul_one, hm] at hcard
    have hm4 : 4 ≤ m := by
      by_contra h
      have : 3 ^ m ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact pow_dvd_pow 3 (by omega)
  · have hcen : ∀ g : G, ∀ z ∈ Z, g * z = z * g := fun g z hz =>
      Subgroup.mem_center_iff.1 (hZc hz) g
    have hZn : Z.Normal := ⟨fun n hn g => by
      rw [show g * n * g⁻¹ = n by rw [hcen g n hn]; group]
      exact hn⟩
    set cub := fiCubeHom hZc hcomm hZ3 hcube with hcub
    set K := cub.ker with hKdef
    have hKi : K.index ≤ 3 := fiHom_index_le cub hZ
    have hKcard : Nat.card G ≤ 3 * Nat.card K := by
      have := Subgroup.card_mul_index K
      nlinarith
    have hKx : ∀ x ∈ K, x ^ 3 = 1 := fun x hx =>
      congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
    obtain ⟨x1, hx1K, hx1Z⟩ : ∃ x1 ∈ K, x1 ∉ Z := by
      by_contra h
      push Not at h
      have : Nat.card K ≤ Nat.card Z := Subgroup.card_le_of_le (fun x hx => h x hx)
      omega
    set C1 := (fiComHom hZc hcomm x1).ker with hC1
    have hC1i : C1.index ≤ 3 := fiHom_index_le _ hZ
    set K1 := K ⊓ C1 with hK1
    have hK1i : K1.index ≤ 9 := by
      have : (K ⊓ C1).index ≤ K.index * C1.index := Subgroup.index_inf_le
      nlinarith
    have hK1card : Nat.card G ≤ 9 * Nat.card K1 := by
      have := Subgroup.card_mul_index K1
      nlinarith
    have hx1c : x1 ^ 3 = 1 := hKx x1 hx1K
    set A := Subgroup.zpowers x1 ⊔ Z with hA
    have hAcard : Nat.card A ≤ 9 := by
      have h1 := Subgroup.relIndex_mul_card Z A
      have hZA : Z ⊓ A = Z := inf_eq_left.2 le_sup_right
      have h2 : Z.relIndex A = Z.relIndex (Subgroup.zpowers x1) :=
        Subgroup.relIndex_sup_right (Subgroup.zpowers x1) Z
      have h3 := Subgroup.relIndex_mul_card Z (Subgroup.zpowers x1)
      have h4 : Nat.card (Subgroup.zpowers x1) ≤ 3 := by
        rw [Nat.card_zpowers]
        exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hx1c)
      have h5 : 0 < Nat.card ↥(Z ⊓ Subgroup.zpowers x1) := Nat.card_pos
      have h6 : Z.relIndex (Subgroup.zpowers x1) ≤ 3 := by
        nlinarith
      rw [hZA, h2] at h1
      nlinarith
    obtain ⟨x2, hx2K1, hx2A⟩ : ∃ x2 ∈ K1, x2 ∉ A := by
      by_contra h
      push Not at h
      have : Nat.card K1 ≤ Nat.card A := Subgroup.card_le_of_le (fun x hx => h x hx)
      omega
    have hx2K : x2 ∈ K := hx2K1.1
    have hx2c : x2 ^ 3 = 1 := hKx x2 hx2K
    have hx12 : x1 * x2 = x2 * x1 := by
      have h := MonoidHom.mem_ker.1 hx2K1.2
      have h' : x1 * x2 * x1⁻¹ * x2⁻¹ = 1 := congrArg Subtype.val h
      exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h')
    have hAe : IsElemAbelian 3 A := by
      refine fi_elemAbelian_sup (fi_elemAbelian_zpowers hx1c) hZe (fun s hs t ht => hcen s t ht)
    have hAx2 : ∀ a ∈ A, a * x2 = x2 * a := by
      have : A ≤ Subgroup.centralizer ({x2} : Set G) := by
        refine sup_le (fun a ha => ?_) (fun a ha => ?_)
        · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
          exact Subgroup.mem_centralizer_singleton_iff.2
            (((Commute.zpow_left (hx12 : Commute x1 x2) i)).eq)
        · exact Subgroup.mem_centralizer_singleton_iff.2 (hcen x2 a ha).symm
      exact fun a ha => Subgroup.mem_centralizer_singleton_iff.1 (this ha)
    have hE0e : IsElemAbelian 3 (A ⊔ Subgroup.zpowers x2) := by
      refine fi_elemAbelian_sup hAe (fi_elemAbelian_zpowers hx2c) (fun s hs t ht => ?_)
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
      exact ((Commute.zpow_right (hAx2 s hs : Commute s x2) i)).eq
    have h9 : 3 * Nat.card Z ≤ Nat.card A := by
      refine fi_three_mul_le hG le_sup_right ?_
      intro h
      exact hx1Z (h ▸ (le_sup_left : Subgroup.zpowers x1 ≤ A) (Subgroup.mem_zpowers x1))
    have h27 : 3 * Nat.card A ≤ Nat.card ↥(A ⊔ Subgroup.zpowers x2) := by
      refine fi_three_mul_le hG le_sup_left ?_
      intro h
      exact hx2A (h ▸ (le_sup_right : Subgroup.zpowers x2 ≤ A ⊔ Subgroup.zpowers x2)
        (Subgroup.mem_zpowers x2))
    obtain ⟨b, hb⟩ := (hG.to_subgroup (A ⊔ Subgroup.zpowers x2)).exists_card_eq
    refine fi_exists_card_27 hE0e ?_
    rw [hb] at h27 ⊢
    have : 3 ≤ b := by
      by_contra hb3
      have : 3 ^ b ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact pow_dvd_pow 3 this

end CFSG.HardMathSupport.Solomon.Coordinator
