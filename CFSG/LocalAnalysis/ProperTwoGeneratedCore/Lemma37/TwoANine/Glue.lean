module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.GlueAut
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.GlueLocal

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Equiv Subgroup
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem coe_zbar_eq_of_mem_center {J : Subgroup X} (hJ : IsTwoANine J) {zb : X} (hmem : zb ∈ J)
    (hc : zb ∈ center X) (hne : zb ≠ 1) : ((zbar J : J) : X) = zb := by
  have h : (⟨zb, hmem⟩ : J) ∈ center J := Subgroup.mem_center_iff.mpr fun g =>
    Subtype.ext (Subgroup.mem_center_iff.mp hc g)
  exact (congrArg Subtype.val (hJ.eq_zbar_of_mem_center h
    fun h1 => hne (congrArg Subtype.val h1))).symm

structure GlueSetting (J B : Subgroup X) (zb : X) : Prop where
  normal : J.Normal
  isTwoANine : IsTwoANine J
  mem : zb ∈ J
  mem_center : zb ∈ center X
  ne_one : zb ≠ 1
  oddCore_eq_bot : CFSG.pPrimeCore 2 X = ⊥
  not_le : ¬ J ≤ B
  exists_sylow_le : ∃ U : Sylow 2 X, (U : Subgroup X) ≤ B
  normalizer_le : ∀ D : Subgroup X, D ≤ B → 2 ≤ CFSG.Open.pRank 2 D →
    normalizer (D : Set X) ≤ B
  mem_of_conj_mem : ∀ {m y : X}, y ∈ B → orderOf y = 2 → y ≠ zb → m⁻¹ * y * m ∈ B → m ∈ B
  exists_sylow_centralizer : ∃ T : Sylow 2 X,
    ∀ k ∈ (T : Subgroup X), k ∈ centralizer (J : Set X) → k = 1 ∨ k = zb

theorem cycleType_swap_mul_swap_of_sq {i j k l : Fin 9}
    (h : (swap i j * swap k l) ^ 2 = 1 ∧ (swap i j * swap k l).support.card = 2 * 2) :
    (swap i j * swap k l).cycleType = {2, 2} := by
  rw [← multiset_replicate_two_two, cycleType_eq_replicate_iff_of_sq_eq_one h.1]
  exact h.2

namespace GlueSetting

variable {J B : Subgroup X} {zb : X} (hs : GlueSetting J B zb)
include hs

theorem coe_zbar : ((zbar J : J) : X) = zb :=
  coe_zbar_eq_of_mem_center hs.isTwoANine hs.mem hs.mem_center hs.ne_one

theorem mul_self : zb * zb = 1 := by
  rw [← hs.coe_zbar, ← Subgroup.coe_mul, hs.isTwoANine.zbar_mul_zbar, Subgroup.coe_one]

theorem eq_of_mem_centralizer {c : X} (hc : c ∈ centralizer (J : Set X)) : c = 1 ∨ c = zb := by
  have := hs.normal
  obtain ⟨T, hT⟩ := hs.exists_sylow_centralizer
  exact eq_one_or_eq_of_mem_centralizer_of_sylow hs.mem_center hs.oddCore_eq_bot T hT hc

section ConjPerm

variable [J.Normal] (e : J ⧸ center J ≃* alternatingGroup (Fin 9))

theorem eq_of_conjPerm_eq_one {m : X} (hm : conjPerm e m = 1) : m = 1 ∨ m = zb :=
  hs.eq_of_mem_centralizer (mem_centralizer_of_conjPerm_eq_one hs.isTwoANine.perfect e hm)

theorem conjPerm_zb : conjPerm e zb = 1 := by
  rw [← hs.coe_zbar, conjPerm_coe, hs.isTwoANine.proj_zbar e]
  rfl

theorem mem_of_sign_eq_one {m : X} (hm : Perm.sign (conjPerm e m) = 1) : m ∈ J := by
  obtain ⟨j, hj⟩ := proj_surjective e ⟨conjPerm e m, Perm.mem_alternatingGroup.mpr hm⟩
  have h1 : conjPerm e ((j : X)⁻¹ * m) = 1 := by
    rw [map_mul, map_inv, conjPerm_coe, hj]
    exact inv_mul_cancel _
  have hm' : m = (j : X) * ((j : X)⁻¹ * m) := by group
  rcases hs.eq_of_conjPerm_eq_one e h1 with h | h
  · rw [hm', h, mul_one]
    exact j.2
  · rw [hm', h]
    exact J.mul_mem j.2 hs.mem

theorem mul_self_eq_of_cycleType {x : X} (hx : (conjPerm e x).cycleType = {2, 2}) :
    x * x = zb := by
  have hsign : Perm.sign (conjPerm e x) = 1 := by
    rw [Perm.sign_of_cycleType, hx]
    decide
  have hxJ := hs.mem_of_sign_eq_one e hsign
  have h := hs.isTwoANine.sq_eq_zbar_of_cycleType_two_two e (x := ⟨x, hxJ⟩)
    (by rw [← conjPerm_coe]; exact hx)
  have h' := congrArg Subtype.val h
  rwa [Subgroup.coe_pow, hs.coe_zbar, sq] at h'

theorem exists_mul_self_eq_one_sign_eq_neg_one {m : X} (hm : m ∉ J) :
    ∃ f : X, f * f = 1 ∧ Perm.sign (conjPerm e f) = -1 := by
  have hsign : Perm.sign (conjPerm e m) = -1 :=
    (Int.units_eq_one_or _).resolve_left fun h => hm (hs.mem_of_sign_eq_one e h)
  have hev : (conjPerm e m)⁻¹ * swap 0 1 ∈ alternatingGroup (Fin 9) := by
    rw [Perm.mem_alternatingGroup, map_mul, map_inv, hsign, Perm.sign_swap (by decide)]
    rfl
  obtain ⟨j₁, hj₁⟩ := proj_surjective e ⟨_, hev⟩
  have ha : conjPerm e (m * j₁) = swap 0 1 := by
    rw [map_mul, conjPerm_coe, hj₁]
    exact mul_inv_cancel_left _ _
  set a := m * (j₁ : X) with ha'
  have haa : conjPerm e (a * a) = 1 := by
    rw [map_mul, ha]
    exact swap_mul_self 0 1
  rcases hs.eq_of_conjPerm_eq_one e haa with h1 | hz
  · exact ⟨a, h1, by rw [ha, Perm.sign_swap (by decide)]⟩
  obtain ⟨g₂, hg₂⟩ := proj_surjective e
    ⟨swap 0 2 * swap 1 3, Perm.mem_alternatingGroup.mpr (by decide)⟩
  obtain ⟨g₃, hg₃⟩ := proj_surjective e
    ⟨swap 0 4 * swap 1 5, Perm.mem_alternatingGroup.mpr (by decide)⟩
  set b := (g₂ : X) * a * (g₂ : X)⁻¹ with hb'
  set c := (g₃ : X) * a * (g₃ : X)⁻¹ with hc'
  have hb : conjPerm e b = swap 2 3 := by
    rw [hb', map_mul, map_mul, map_inv, ha, conjPerm_coe, hg₂]
    decide
  have hc : conjPerm e c = swap 4 5 := by
    rw [hc', map_mul, map_mul, map_inv, ha, conjPerm_coe, hg₃]
    decide
  have hconj : ∀ g : X, g * a * g⁻¹ * (g * a * g⁻¹) = zb := fun g => by
    calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
      _ = zb := by rw [hz, Subgroup.mem_center_iff.mp hs.mem_center g, mul_inv_cancel_right]
  have hab := hs.mul_self_eq_of_cycleType e (x := a * b) (by
    rw [map_mul, ha, hb]
    exact cycleType_swap_mul_swap_of_sq (by decide))
  have hac := hs.mul_self_eq_of_cycleType e (x := a * c) (by
    rw [map_mul, ha, hc]
    exact cycleType_swap_mul_swap_of_sq (by decide))
  have hbc := hs.mul_self_eq_of_cycleType e (x := b * c) (by
    rw [map_mul, hb, hc]
    exact cycleType_swap_mul_swap_of_sq (by decide))
  refine ⟨a * b * c, mul_mul_mul_self_eq_one_of_anticomm hs.mem_center hs.mul_self hab
    (hconj _) (mul_eq_mul_mul_of_mul_self_eq hs.mul_self hz (hconj _) hac)
    (mul_eq_mul_mul_of_mul_self_eq hs.mul_self (hconj _) (hconj _) hbc), ?_⟩
  rw [show conjPerm e (a * b * c) = swap 0 1 * swap 2 3 * swap 4 5 by
    rw [map_mul, map_mul, ha, hb, hc]]
  decide

end ConjPerm

theorem eq_top : J = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hs.normal
  have hJ := hs.isTwoANine
  obtain ⟨U, hUB⟩ := hs.exists_sylow_le
  obtain ⟨e, he⟩ := exists_mulEquiv_proj_mem_of_sylow_le hJ U hUB
  have hK := map_subgroupOf_eq_stabilizer_eight hJ e he hs.normalizer_le hs.not_le
  have hzB : zb ∈ B := hs.coe_zbar ▸ he _ (by rw [hJ.proj_zbar e]; exact ANineSylow.one_mem)
  by_contra hne
  obtain ⟨m, hm⟩ : ∃ m : X, m ∉ J := by
    by_contra h
    push Not at h
    exact hne (eq_top_iff.mpr fun x _ => h x)
  obtain ⟨f, hff, hfs⟩ := hs.exists_mul_self_eq_one_sign_eq_neg_one e hm
  have hf1 : f ≠ 1 := by
    rintro rfl
    rw [map_one, Perm.sign_one] at hfs
    exact absurd hfs (by decide)
  have hf2 : orderOf f = 2 := orderOf_eq_prime (by rw [sq]; exact hff) hf1
  obtain ⟨g, hg⟩ : ∃ g : X, g * f * g⁻¹ ∈ (U : Subgroup X) := by
    have hp : IsPGroup 2 (zpowers f) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hf2, pow_one])
    obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Q U
    refine ⟨g, ?_⟩
    have h := Subgroup.smul_mem_pointwise_smul f (MulAut.conj g) (Q : Subgroup X)
      (hQ (mem_zpowers f))
    rwa [← Sylow.coe_subgroup_smul, hg, MulAut.smul_def, MulAut.conj_apply] at h
  set f' := g * f * g⁻¹ with hf'
  have hf'B : f' ∈ B := hUB hg
  have hf'f' : f' * f' = 1 := by
    calc f' * f' = g * (f * f) * g⁻¹ := by rw [hf']; group
      _ = 1 := by rw [hff, mul_one, mul_inv_cancel]
  have hf'2 : orderOf f' = 2 := by
    rw [hf', ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hf2
  set σ := conjPerm e f' with hσ
  have hσs : Perm.sign σ = -1 := by
    rw [hσ, hf', map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hfs, mul_comm,
      inv_mul_cancel_left]
  have hσ2 : σ ^ 2 = 1 := by
    rw [sq, hσ, ← map_mul, hf'f', map_one]
  have hσ8 : σ 8 = 8 := apply_eight_of_forall_conj_apply_eight fun a ha8 => by
    have ha : a ∈ (B.subgroupOf J).map (proj e) := hK ▸ (show a • (8 : Fin 9) = 8 from ha8)
    obtain ⟨b, hb, rfl⟩ := ha
    rw [hσ, ← proj_conjNormal]
    have hmem : proj e (MulAut.conjNormal f' b) ∈ (B.subgroupOf J).map (proj e) :=
      ⟨_, Subgroup.mem_subgroupOf.mpr (by
        rw [MulAut.conjNormal_apply]
        exact B.mul_mem (B.mul_mem hf'B (Subgroup.mem_subgroupOf.mp hb)) (B.inv_mem hf'B)), rfl⟩
    rw [hK] at hmem
    exact hmem
  obtain ⟨c, -, hc8, hcσ⟩ := exists_isThreeCycle_commute_of_sign_eq_neg_one hσ2 hσ8 hσs
  obtain ⟨j, hj⟩ := proj_surjective e c
  have hcomm : conjPerm e ((j : X) * f' * (j : X)⁻¹ * f'⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, conjPerm_coe, hj, ← hσ, hcσ.eq,
      mul_inv_cancel_right, mul_inv_cancel]
  have hne' : f' ≠ zb := fun h => by
    rw [hσ, h, hs.conjPerm_zb e, Perm.sign_one] at hσs
    exact absurd hσs (by decide)
  have hy : (j : X)⁻¹⁻¹ * f' * (j : X)⁻¹ ∈ B := by
    rw [inv_inv]
    rcases hs.eq_of_conjPerm_eq_one e hcomm with h | h
    · rw [mul_inv_eq_one.mp h]
      exact hf'B
    · rw [mul_inv_eq_iff_eq_mul.mp h]
      exact B.mul_mem hzB hf'B
  have hjB : (j : X) ∈ B := by
    simpa using B.inv_mem (hs.mem_of_conj_mem hf'B hf'2 hne' hy)
  have hc8' : c ∈ MulAction.stabilizer (alternatingGroup (Fin 9)) (8 : Fin 9) :=
    hK ▸ ⟨j, Subgroup.mem_subgroupOf.mpr hjB, hj⟩
  exact hc8 hc8'

end GlueSetting

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
