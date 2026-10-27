module

public import CFSG.LargeExtraspecial.OrthoF2Pairs57
public import CFSG.LargeExtraspecial.S12LinAlg
public import CFSG.LargeExtraspecial.S12Seven

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

universe u

theorem S12NoNormalTwo.of_isPGroup_three {X : Type*} [Group X] {H : Subgroup X}
    (hH : IsPGroup 3 H) : S12NoNormalTwo H := by
  intro P hPH hP _
  have h3 : IsPGroup 3 P := hH.to_le hPH
  exact disjoint_self.mp (IsPGroup.disjoint_of_ne 2 3 (by norm_num) P P hP h3)

theorem s12_exists_decomp {X : Type*} [Group X] {Z : Subgroup X} [Finite Z]
    (hZc : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x) (hodd : Odd (Nat.card Z)) {t : X} (htt : t * t = 1)
    (htZ : ∀ y ∈ Z, t * y * t⁻¹ ∈ Z) {y : X} (hy : y ∈ Z) :
    ∃ c ∈ Z, ∃ k ∈ Z, y = c * k ∧ t * c * t⁻¹ = c ∧ t * k * t⁻¹ = k⁻¹ := by
  obtain ⟨e, he⟩ := hodd
  have hyn : y ^ Nat.card Z = 1 := by
    have h := pow_card_eq_one' (G := Z) (x := ⟨y, hy⟩)
    exact congrArg Subtype.val h
  set u := t * y * t⁻¹ with hu
  have huZ : u ∈ Z := htZ y hy
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have htu : t * u * t⁻¹ = y := by
    rw [hu, hti]
    calc t * (t * y * t) * t = (t * t) * y * (t * t) := by group
      _ = y := by rw [htt]; group
  have hyu : Commute y u := hZc y hy u huZ
  have hc : Commute (y * u) (y * u⁻¹) :=
    ((Commute.refl y).mul_right hyu.inv_right).mul_left
      (hyu.symm.mul_right (Commute.refl u).inv_right)
  refine ⟨(y * u) ^ (e + 1), Z.pow_mem (Z.mul_mem hy huZ) _, (y * u⁻¹) ^ (e + 1),
    Z.pow_mem (Z.mul_mem hy (Z.inv_mem huZ)) _, ?_, ?_, ?_⟩
  · rw [← hc.mul_pow]
    have e1 : y * u * (y * u⁻¹) = y * y := by
      calc y * u * (y * u⁻¹) = y * (u * y) * u⁻¹ := by group
        _ = y * (y * u) * u⁻¹ := by rw [hyu.eq]
        _ = y * y := by group
    rw [e1, ← pow_two, ← pow_mul, show 2 * (e + 1) = Nat.card Z + 1 by omega, pow_succ, hyn,
      one_mul]
  · rw [← conj_pow]
    congr 1
    calc t * (y * u) * t⁻¹ = (t * y * t⁻¹) * (t * u * t⁻¹) := by group
      _ = y * u := by rw [htu, ← hu, hyu.eq]
  · rw [← conj_pow, ← inv_pow]
    congr 1
    calc t * (y * u⁻¹) * t⁻¹ = (t * y * t⁻¹) * (t * u * t⁻¹)⁻¹ := by group
      _ = (y * u⁻¹)⁻¹ := by rw [htu, ← hu]; group

namespace Setting

variable {G : Type u} [Group G] [Finite G] (S : Setting G)

@[expose] noncomputable def invZ12 (g : G) (t : S.O) : Subgroup S.O where
  carrier := {y | y ∈ S.Z3Xbar12 g ∧ t * y * t⁻¹ = y⁻¹}
  mul_mem' := by
    rintro x y ⟨hx, hxt⟩ ⟨hy, hyt⟩
    refine ⟨(S.Z3Xbar12 g).mul_mem hx hy, ?_⟩
    calc t * (x * y) * t⁻¹ = (t * x * t⁻¹) * (t * y * t⁻¹) := by group
      _ = x⁻¹ * y⁻¹ := by rw [hxt, hyt]
      _ = (x * y)⁻¹ := by
        rw [mul_inv_rev,
          commute_of_mem_Z3Xbar12 ((S.Z3Xbar12 g).inv_mem hx) ((S.Z3Xbar12 g).inv_mem hy)]
  one_mem' := ⟨(S.Z3Xbar12 g).one_mem, by group⟩
  inv_mem' := by
    rintro x ⟨hx, hxt⟩
    refine ⟨(S.Z3Xbar12 g).inv_mem hx, ?_⟩
    rw [show t * x⁻¹ * t⁻¹ = (t * x * t⁻¹)⁻¹ by group, hxt]

@[expose] noncomputable def centZ12 (g : G) (t : S.O) : Subgroup S.O :=
  S.Z3Xbar12 g ⊓ centralizer ({t} : Set S.O)

variable {S}

theorem mem_invZ12 {g : G} {t y : S.O} :
    y ∈ S.invZ12 g t ↔ y ∈ S.Z3Xbar12 g ∧ t * y * t⁻¹ = y⁻¹ := Iff.rfl

theorem mem_centZ12 {g : G} {t y : S.O} :
    y ∈ S.centZ12 g t ↔ y ∈ S.Z3Xbar12 g ∧ y * t = t * y := by
  rw [centZ12, mem_inf, mem_centralizer_singleton_iff]

theorem invZ12_le {g : G} {t : S.O} : S.invZ12 g t ≤ S.Z3Xbar12 g := fun _ h => h.1

theorem isPGroup_invZ12 {g : G} {t : S.O} : IsPGroup 3 (S.invZ12 g t) :=
  isPGroup_Z3Xbar12.to_le invZ12_le

theorem s12_map_subtype_le (H : Subgroup S.O) :
    H.map S.O.subtype ≤ TauCeti.QuadraticMap.orthogonalGroup S.q := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

theorem s12_invZ12_map {g : G} {t : S.O} :
    Odd (Nat.card ((S.invZ12 g t).map S.O.subtype)) ∧
      ∀ x ∈ (S.invZ12 g t).map S.O.subtype,
        (t : S.Qt ≃ₗ[ZMod 2] S.Qt) * x * (t : S.Qt ≃ₗ[ZMod 2] S.Qt)⁻¹ = x⁻¹ := by
  refine ⟨?_, ?_⟩
  · rw [card_map_of_injective (subtype_injective _)]
    obtain ⟨m, hm⟩ := (isPGroup_invZ12 (S := S) (g := g) (t := t)).exists_card_eq
    rw [hm]
    exact Odd.pow (by decide)
  · rintro _ ⟨y, hy, rfl⟩
    have e := congrArg Subtype.val hy.2
    simpa using e

theorem card_invZ12_le {g : G} {t : S.O} (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) :
    Nat.card (S.invZ12 g t) ≤ 3 := by
  have h := aschbacher_5_7 S.q_nondegenerate htA (s12_map_subtype_le _)
    (s12_invZ12_map (g := g) (t := t)).1 (s12_invZ12_map (g := g) (t := t)).2
  rwa [card_map_of_injective (subtype_injective _)] at h

theorem invZ12_orderOf {g : G} {t : S.O} (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2)
    {i : S.O} (hi : i ∈ S.invZ12 g t) (hi1 : i ≠ 1) :
    orderOf i = 3 ∧ finrank (ZMod 2) (commSpace (i : S.Qt ≃ₗ[ZMod 2] S.Qt)) = 4 := by
  have h := orderOf_eq_three_of_inverted S.q_nondegenerate htA (s12_map_subtype_le _)
    (s12_invZ12_map (g := g) (t := t)).1 (s12_invZ12_map (g := g) (t := t)).2
    (x := (i : S.Qt ≃ₗ[ZMod 2] S.Qt)) ⟨i, hi, rfl⟩
    (fun e => hi1 (Subtype.ext e))
  refine ⟨?_, h.2⟩
  rw [← h.1]
  exact (Subgroup.orderOf_coe i).symm

theorem invZ12_eq_zpowers {g : G} {t : S.O} (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2)
    {i : S.O} (hi : i ∈ S.invZ12 g t) (hi1 : i ≠ 1) : S.invZ12 g t = zpowers i := by
  refine (eq_of_le_of_card_ge (zpowers_le.mpr hi) ?_).symm
  rw [Nat.card_zpowers, (invZ12_orderOf htA hi hi1).1]
  exact card_invZ12_le htA

theorem s12_finrank_commSpace_of_inverted {d k : S.O}
    (hd : IsTypeA S.q (d : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) (hk3 : k ^ 3 = 1) (hk1 : k ≠ 1)
    (hdk : d * k * d⁻¹ = k⁻¹) : finrank (ZMod 2) (commSpace (k : S.Qt ≃ₗ[ZMod 2] S.Qt)) = 4 := by
  have hodd : Odd (Nat.card ((zpowers k).map S.O.subtype)) := by
    rw [card_map_of_injective (subtype_injective _), Nat.card_zpowers, orderOf_eq_prime hk3 hk1]
    decide
  have hinv : ∀ x ∈ (zpowers k).map S.O.subtype,
      (d : S.Qt ≃ₗ[ZMod 2] S.Qt) * x * (d : S.Qt ≃ₗ[ZMod 2] S.Qt)⁻¹ = x⁻¹ := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hy
    have e : d * k ^ m * d⁻¹ = (k ^ m)⁻¹ := by rw [← conj_zpow, hdk, inv_zpow]
    have e' := congrArg Subtype.val e
    simpa using e'
  exact (orderOf_eq_three_of_inverted S.q_nondegenerate hd (s12_map_subtype_le _) hodd hinv
    (x := (k : S.Qt ≃ₗ[ZMod 2] S.Qt)) ⟨k, mem_zpowers k, rfl⟩
    (fun e => hk1 (Subtype.ext e))).2

theorem centZ12_le {g : G} {t : S.O} : S.centZ12 g t ≤ S.Z3Xbar12 g := inf_le_left

theorem conj_mem_centZ12 {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O} (ht : t ∈ S.Lbar g)
    {m : S.O} (hm : m ∈ S.Lbar g) {k : S.O} (hk : k ∈ S.centZ12 g t) :
    m * k * m⁻¹ ∈ S.centZ12 g t := by
  rw [mem_centZ12] at hk ⊢
  refine ⟨(mem_normalizer_iff.mp (Mbar_le_normalizer_Z3Xbar12 (S.Lbar_le_Mbar g hm)) k).mp hk.1,
    ?_⟩
  have hmt : m * t = t * m :=
    congrArg Subtype.val ((S.isElementaryAbelian_Lbar haQ).is_comm.comm ⟨m, hm⟩ ⟨t, ht⟩)
  have hmt' : m⁻¹ * t = t * m⁻¹ := by
    calc m⁻¹ * t = m⁻¹ * (t * m) * m⁻¹ := by group
      _ = m⁻¹ * (m * t) * m⁻¹ := by rw [hmt]
      _ = t * m⁻¹ := by group
  calc m * k * m⁻¹ * t = m * k * (t * m⁻¹) := by rw [mul_assoc (m * k), hmt']
    _ = m * (k * t) * m⁻¹ := by group
    _ = m * (t * k) * m⁻¹ := by rw [hk.2]
    _ = (m * t) * k * m⁻¹ := by group
    _ = t * (m * k * m⁻¹) := by rw [hmt]; group

theorem centZ12_inf_fixSub12_eq_bot {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 3 ≤ S.width) {t : S.O} (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) :
    S.centZ12 g t ⊓ S.fixSub12 (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) = ⊥ := by
  have hK : S12NoNormalTwo (S.centZ12 g t ⊓ S.fixSub12 (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt))) :=
    S12NoNormalTwo.of_isPGroup_three (isPGroup_Z3Xbar12.to_le (inf_le_left.trans centZ12_le))
  have haW := (S.timmesfeld_12_6 haQ hne ht htA).1
  refine S.s12_eq_bot_of_fix haQ hne hn hK
    (inf_le_left.trans (centZ12_le.trans Z3Xbar12_le_Mbar)) (fun k hk => hk.2 _ haW)
    fun ℓ hℓ => ?_
  have hcomm : ∀ {x : S.O}, x ∈ S.Lbar g → x * t = t * x := fun {x} hx =>
    congrArg Subtype.val ((S.isElementaryAbelian_Lbar haQ).is_comm.comm ⟨x, hx⟩ ⟨t, ht⟩)
  have hℓ' : ℓ⁻¹ ∈ S.Lbar g := (S.Lbar g).inv_mem hℓ
  refine mem_normalizer_of_conj_le (fun k hk => ⟨conj_mem_centZ12 haQ ht hℓ hk.1,
    conj_mem_fixSub12 (hcomm hℓ) hk.2⟩) (fun k hk => ⟨conj_mem_centZ12 haQ ht hℓ' hk.1,
    conj_mem_fixSub12 (hcomm hℓ') hk.2⟩)

theorem eq_of_agree_centZ12 {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 3 ≤ S.width) {t : S.O} (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) {c c' : S.O} (hc : c ∈ S.centZ12 g t)
    (hc' : c' ∈ S.centZ12 g t)
    (h : ∀ w ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt),
      (c : S.Qt ≃ₗ[ZMod 2] S.Qt) w = (c' : S.Qt ≃ₗ[ZMod 2] S.Qt) w) : c = c' := by
  have hK := centZ12_inf_fixSub12_eq_bot haQ hne hn ht htA
  have hmem : c⁻¹ * c' ∈ S.centZ12 g t ⊓ S.fixSub12 (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) := by
    refine ⟨(S.centZ12 g t).mul_mem ((S.centZ12 g t).inv_mem hc) hc', fun w hw => ?_⟩
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply, ← h w hw, ← LinearEquiv.mul_apply,
      ← Subgroup.coe_mul, inv_mul_cancel]
    rfl
  rw [hK, mem_bot] at hmem
  calc c = c * (c⁻¹ * c') := by rw [hmem, mul_one]
    _ = c' := by group

theorem centZ12_apply_mem {g : G} {t c : S.O} (hc : c ∈ S.centZ12 g t) {w : S.Qt}
    (hw : w ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    (c : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
  apply_mem_commSpace_of_commute (mem_centZ12.mp hc).2 hw

theorem centZ12_pow_three {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 3 ≤ S.width) {t : S.O} (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) {c : S.O} (hc : c ∈ S.centZ12 g t) :
    c ^ 3 = 1 := by
  have h6w := s12_pow_six_apply htA.2.2.2.1 (x := (c : S.Qt ≃ₗ[ZMod 2] S.Qt))
    (fun w hw => centZ12_apply_mem hc hw)
    (fun w hw => centZ12_apply_mem ((S.centZ12 g t).inv_mem hc) hw)
  have h6 : c ^ 6 = 1 := by
    refine eq_of_agree_centZ12 haQ hne hn ht htA ((S.centZ12 g t).pow_mem hc 6)
      (S.centZ12 g t).one_mem fun w hw => ?_
    rw [Subgroup.coe_pow, h6w w hw]
    rfl
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp (isPGroup_Z3Xbar12 (S := S) (g := g)))
    ⟨c, centZ12_le hc⟩
  rw [Subgroup.orderOf_mk] at hm
  have hd : orderOf c ∣ 6 := orderOf_dvd_of_pow_eq_one h6
  have hm1 : m ≤ 1 := by
    by_contra hcon
    have h9 : 3 ^ 2 ∣ 6 := (pow_dvd_pow 3 (by omega)).trans (hm ▸ hd)
    norm_num at h9
  refine orderOf_dvd_iff_pow_eq_one.mp ?_
  rw [hm]
  interval_cases m <;> norm_num

theorem centZ12_eq_or {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 3 ≤ S.width) {t : S.O} (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) {c c' : S.O} (hc : c ∈ S.centZ12 g t)
    (hc' : c' ∈ S.centZ12 g t) (hc'1 : c' ≠ 1) : c = 1 ∨ c = c' ∨ c = c' ^ 2 := by
  by_cases hc1 : c = 1
  · exact Or.inl hc1
  right
  have hmoved : ∀ {x : S.O}, x ∈ S.centZ12 g t → x ≠ 1 →
      ∃ w ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt), (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w ≠ w := by
    intro x hx hx1
    by_contra hcon
    push Not at hcon
    exact hx1 (eq_of_agree_centZ12 haQ hne hn ht htA hx (S.centZ12 g t).one_mem
      fun w hw => by rw [hcon w hw]; rfl)
  have h3 : ∀ {x : S.O}, x ∈ S.centZ12 g t → (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ^ 3 = 1 := by
    intro x hx
    rw [← Subgroup.coe_pow, centZ12_pow_three haQ hne hn ht htA hx]
    rfl
  rcases s12_eq_or_eq_sq_of_pow_three htA.2.2.2.1 (h3 hc') (h3 hc)
      (fun w hw => centZ12_apply_mem hc' hw) (fun w hw => centZ12_apply_mem hc hw)
      (hmoved hc' hc'1) (hmoved hc hc1) with h | h
  · exact Or.inl (eq_of_agree_centZ12 haQ hne hn ht htA hc hc' h)
  · right
    refine eq_of_agree_centZ12 haQ hne hn ht htA hc ((S.centZ12 g t).pow_mem hc' 2)
      fun w hw => ?_
    rw [h w hw, Subgroup.coe_pow]

end Setting

end CFSG.LargeExtraspecial
