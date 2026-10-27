module

public import CFSG.GH74.Uniqueness.SU.SU5J2Emb

public section

open Subgroup CFSG.GH74.Uniqueness.SU.SU5 CFSG.GH74.GLS.Bg.TwoGroups
open scoped commutatorElement

namespace CFSG.ComponentClassification.RankTwoAltFive

variable {G : Type*} [Group G]

theorem commutatorElement_mul_left' {g₁ g₂ h : G} (h₁ : ⁅g₂, h⁆ * g₁ = g₁ * ⁅g₂, h⁆)
    (h₂ : ⁅g₁, h⁆ * ⁅g₂, h⁆ = ⁅g₂, h⁆ * ⁅g₁, h⁆) : ⁅g₁ * g₂, h⁆ = ⁅g₁, h⁆ * ⁅g₂, h⁆ := by
  rw [h₂]
  calc ⁅g₁ * g₂, h⁆ = g₁ * ⁅g₂, h⁆ * h * g₁⁻¹ * h⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = ⁅g₂, h⁆ * g₁ * h * g₁⁻¹ * h⁻¹ := by rw [h₁]
    _ = ⁅g₂, h⁆ * ⁅g₁, h⁆ := by simp only [commutatorElement_def]; group

theorem commutatorElement_mul_right' {g h₁ h₂ : G} (h₁₂ : ⁅g, h₂⁆ * h₁ = h₁ * ⁅g, h₂⁆) :
    ⁅g, h₁ * h₂⁆ = ⁅g, h₁⁆ * ⁅g, h₂⁆ := by
  have e : ⁅g, h₂⁆ * h₁⁻¹ = h₁⁻¹ * ⁅g, h₂⁆ := by
    calc ⁅g, h₂⁆ * h₁⁻¹ = h₁⁻¹ * (h₁ * ⁅g, h₂⁆) * h₁⁻¹ := by group
      _ = h₁⁻¹ * (⁅g, h₂⁆ * h₁) * h₁⁻¹ := by rw [h₁₂]
      _ = h₁⁻¹ * ⁅g, h₂⁆ := by group
  calc ⁅g, h₁ * h₂⁆ = g * h₁ * g⁻¹ * (⁅g, h₂⁆ * h₁⁻¹) := by
        simp only [commutatorElement_def]; group
    _ = g * h₁ * g⁻¹ * (h₁⁻¹ * ⁅g, h₂⁆) := by rw [e]
    _ = ⁅g, h₁⁆ * ⁅g, h₂⁆ := by simp only [commutatorElement_def]; group

structure J2Gens (G : Type*) [Group G] where
  x : G
  p : G
  q : G
  P : Subgroup G
  C : Subgroup G
  x_sq : x * x = 1
  p_sq : p * p = 1
  q_sq : q * q = 1
  pq : p * q = q * p
  p_mem : p ∈ P
  q_mem : q ∈ P
  xp_mem : x * p * x⁻¹ ∈ P
  xq_mem : x * q * x⁻¹ ∈ P
  C_le : C ≤ P
  C_cent : ∀ c ∈ C, ∀ y ∈ P, c * y = y * c
  C_sq : ∀ c ∈ C, c * c = 1
  pp_mem : ⁅x * p * x⁻¹, p⁆ ∈ C
  pq_mem : ⁅x * p * x⁻¹, q⁆ ∈ C
  qq : ⁅x * q * x⁻¹, q⁆ = ⁅x * p * x⁻¹, p⁆
  qp : ⁅x * q * x⁻¹, p⁆ = ⁅x * p * x⁻¹, p⁆ * ⁅x * p * x⁻¹, q⁆

namespace J2Gens

variable (g : J2Gens G)

@[expose] def Y : F4c → G
  | .z0 => 1
  | .z1 => g.p
  | .w => g.q
  | .w2 => g.p * g.q

@[expose] def X (a : F4c) : G := g.x * g.Y (F4c.sg a) * g.x⁻¹

@[expose] def Z (c : F4c) : G := ⁅g.X 1, g.Y c⁆

theorem X_z0 : g.X .z0 = 1 := by
  change g.x * 1 * g.x⁻¹ = 1
  group

theorem X_w : g.X .w = g.X .z1 * g.X .w2 := by
  change g.x * (g.p * g.q) * g.x⁻¹ = (g.x * g.p * g.x⁻¹) * (g.x * g.q * g.x⁻¹)
  group

theorem qp_rw : g.q * g.p = g.p * g.q := g.pq.symm

theorem qp_rw' (r : G) : g.q * (g.p * r) = g.p * (g.q * r) := by
  rw [← mul_assoc, g.qp_rw, mul_assoc]

theorem pp_rw (r : G) : g.p * (g.p * r) = r := by rw [← mul_assoc, g.p_sq, one_mul]

theorem Y_add (a b : F4c) : g.Y (a + b) = g.Y a * g.Y b := by
  cases a <;> cases b <;> dsimp only [HAdd.hAdd, Add.add, F4c.add, Y] <;>
    simp only [mul_assoc, one_mul, mul_one, g.p_sq, g.q_sq, g.qp_rw, g.qp_rw', g.pp_rw]

theorem Y_mem (a : F4c) : g.Y a ∈ g.P := by
  cases a
  · exact one_mem _
  · exact g.p_mem
  · exact g.q_mem
  · exact mul_mem g.p_mem g.q_mem

theorem X_mem (a : F4c) : g.X a ∈ g.P := by
  cases a
  · rw [X_z0]; exact one_mem _
  · exact g.xp_mem
  · rw [X_w]; exact mul_mem g.xp_mem g.xq_mem
  · exact g.xq_mem

theorem X_add (a b : F4c) : g.X (a + b) = g.X a * g.X b := by
  simp only [X, F4c.sg_add, Y_add]
  group

theorem C_comm {c c' : G} (hc : c ∈ g.C) (hc' : c' ∈ g.C) : c * c' = c' * c :=
  g.C_cent c hc c' (g.C_le hc')

theorem Z_z0 : g.Z .z0 = 1 := commutatorElement_one_right _

theorem Z_w2 : g.Z .w2 = g.Z .z1 * g.Z .w :=
  commutatorElement_mul_right' (g.C_cent _ g.pq_mem _ g.p_mem)

theorem Z_mem (c : F4c) : g.Z c ∈ g.C := by
  cases c
  · rw [Z_z0]; exact one_mem _
  · exact g.pp_mem
  · exact g.pq_mem
  · rw [Z_w2]; exact mul_mem g.pp_mem g.pq_mem

theorem Z_comm (c : F4c) {y : G} (hy : y ∈ g.P) : g.Z c * y = y * g.Z c :=
  g.C_cent _ (g.Z_mem c) y hy

theorem Z_sq (c : F4c) : g.Z c * g.Z c = 1 := g.C_sq _ (g.Z_mem c)

theorem Z_add (a b : F4c) : g.Z (a + b) = g.Z a * g.Z b := by
  change ⁅g.X 1, g.Y (a + b)⁆ = ⁅g.X 1, g.Y a⁆ * ⁅g.X 1, g.Y b⁆
  rw [Y_add]
  exact commutatorElement_mul_right' (g.Z_comm b (g.Y_mem a))

theorem comm_w2_w : ⁅g.X .w2, g.Y .w⁆ = g.Z .z1 := g.qq

theorem comm_w2_z1 : ⁅g.X .w2, g.Y .z1⁆ = g.Z .z1 * g.Z .w := g.qp

theorem comm_w_z1 : ⁅g.X .w, g.Y .z1⁆ = g.Z .w := by
  have hm : ⁅g.X .w2, g.Y .z1⁆ ∈ g.C := by
    rw [comm_w2_z1]; exact mul_mem (g.Z_mem _) (g.Z_mem _)
  rw [X_w, commutatorElement_mul_left' (g.C_cent _ hm _ (g.X_mem .z1))
    (g.C_comm (g.Z_mem .z1) hm), comm_w2_z1]
  change g.Z .z1 * (g.Z .z1 * g.Z .w) = _
  rw [← mul_assoc, g.Z_sq, one_mul]

theorem comm_w_w : ⁅g.X .w, g.Y .w⁆ = g.Z .w2 := by
  have hm : ⁅g.X .w2, g.Y .w⁆ ∈ g.C := by rw [comm_w2_w]; exact g.Z_mem _
  rw [X_w, commutatorElement_mul_left' (g.C_cent _ hm _ (g.X_mem .z1))
    (g.C_comm (g.Z_mem .w) hm), comm_w2_w, Z_w2]
  exact g.C_comm (g.Z_mem _) (g.Z_mem _)

theorem comm_X_Y (a b : F4c) : ⁅g.X a, g.Y b⁆ = g.Z (a * b) := by
  have hY0 : g.Y .z0 = 1 := rfl
  cases a
  · rw [X_z0, commutatorElement_one_left]; exact g.Z_z0.symm
  · rw [show F4c.z1 * b = b from one_mul b]; rfl
  · cases b
    · rw [hY0, commutatorElement_one_right]; exact g.Z_z0.symm
    · exact g.comm_w_z1
    · exact g.comm_w_w
    · have hm : ⁅g.X .w, g.Y .w⁆ ∈ g.C := by rw [comm_w_w]; exact g.Z_mem _
      change ⁅g.X .w, g.Y .z1 * g.Y .w⁆ = g.Z .z1
      rw [commutatorElement_mul_right' (g.C_cent _ hm _ (g.Y_mem .z1)), comm_w_z1, comm_w_w,
        Z_w2, ← mul_assoc, g.C_comm (g.Z_mem _) (g.Z_mem _), mul_assoc, g.Z_sq, mul_one]
  · cases b
    · rw [hY0, commutatorElement_one_right]; exact g.Z_z0.symm
    · exact g.comm_w2_z1.trans g.Z_w2.symm
    · exact g.comm_w2_w
    · have hm : ⁅g.X .w2, g.Y .w⁆ ∈ g.C := by rw [comm_w2_w]; exact g.Z_mem _
      change ⁅g.X .w2, g.Y .z1 * g.Y .w⁆ = g.Z .w
      rw [commutatorElement_mul_right' (g.C_cent _ hm _ (g.Y_mem .z1)), comm_w2_z1, comm_w2_w,
        mul_assoc, g.C_comm (g.Z_mem _) (g.Z_mem _), ← mul_assoc, g.Z_sq, one_mul]

theorem X_mul_Y (a b : F4c) : g.X a * g.Y b = g.Y b * g.X a * g.Z (a * b) := by
  rw [← comm_X_Y, ← g.C_cent _ (g.comm_X_Y a b ▸ g.Z_mem (a * b)) _
    (mul_mem (g.Y_mem b) (g.X_mem a))]
  simp only [commutatorElement_def]
  group

theorem conj_Y (b : F4c) : g.x * g.Y b * g.x⁻¹ = g.X (F4c.sg b) := by
  rw [X, F4c.sg_sg]

theorem conj_X (a : F4c) : g.x * g.X a * g.x⁻¹ = g.Y (F4c.sg a) := by
  rw [X, show g.x * (g.x * g.Y (F4c.sg a) * g.x⁻¹) * g.x⁻¹ =
    (g.x * g.x) * g.Y (F4c.sg a) * (g.x⁻¹ * g.x⁻¹) by group, g.x_sq, ← mul_inv_rev, g.x_sq]
  group

theorem conj_Z (c : F4c) : g.x * g.Z c * g.x⁻¹ = g.Z (F4c.sg c) := by
  rw [Z, conjugate_commutatorElement, conj_Y, show (1 : F4c) = F4c.sg 1 from rfl, conj_X,
    F4c.sg_sg, ← commutatorElement_inv, comm_X_Y, mul_one]
  exact inv_eq_of_mul_eq_one_right (g.Z_sq _)

@[expose] def kappaFun (u : L34Syl) : G := g.Y u.b * g.X u.a * g.Z u.c

theorem kappaFun_mul (u u' : L34Syl) : g.kappaFun (u * u') = g.kappaFun u * g.kappaFun u' := by
  change g.Y (u.b + u'.b) * g.X (u.a + u'.a) * g.Z (u.c + u'.c + u.a * u'.b) =
    g.Y u.b * g.X u.a * g.Z u.c * (g.Y u'.b * g.X u'.a * g.Z u'.c)
  rw [Y_add, X_add, Z_add, Z_add]
  have h1 : g.Y u.b * g.X u.a * g.Z u.c * (g.Y u'.b * g.X u'.a * g.Z u'.c) =
      g.Y u.b * (g.X u.a * g.Y u'.b) * g.X u'.a * g.Z u'.c * g.Z u.c := by
    rw [mul_assoc (g.Y u.b * g.X u.a), g.Z_comm _
      (mul_mem (mul_mem (g.Y_mem _) (g.X_mem _)) (g.Z_mem _ |> g.C_le))]
    group
  rw [h1, X_mul_Y]
  have h2 : g.Y u.b * (g.Y u'.b * g.X u.a * g.Z (u.a * u'.b)) * g.X u'.a * g.Z u'.c * g.Z u.c =
      g.Y u.b * g.Y u'.b * (g.X u.a * g.X u'.a) * (g.Z (u.a * u'.b) * g.Z u'.c * g.Z u.c) := by
    rw [show g.Y u.b * (g.Y u'.b * g.X u.a * g.Z (u.a * u'.b)) * g.X u'.a =
      g.Y u.b * g.Y u'.b * g.X u.a * (g.Z (u.a * u'.b) * g.X u'.a) by group,
      g.Z_comm _ (g.X_mem _)]
    group
  rw [h2]
  congr 1
  rw [g.C_comm (g.Z_mem _) (g.Z_mem _), mul_assoc, g.C_comm (g.Z_mem _) (g.Z_mem _),
    ← mul_assoc, g.C_comm (g.Z_mem _) (g.Z_mem _)]

@[expose] def kappa : L34Syl →* G where
  toFun := g.kappaFun
  map_one' := by
    change g.Y 0 * g.X 0 * g.Z 0 = 1
    rw [show g.X 0 = 1 from g.X_z0, show g.Z 0 = 1 from g.Z_z0]
    change (1 : G) * 1 * 1 = 1
    group
  map_mul' := g.kappaFun_mul

theorem kappa_apply (u : L34Syl) : g.kappa u = g.Y u.b * g.X u.a * g.Z u.c := rfl

theorem kappa_phi (u : L34Syl) : g.kappa (phi u) = g.x * g.kappa u * g.x⁻¹ := by
  change g.Y (F4c.sg u.a) * g.X (F4c.sg u.b) * g.Z (F4c.sg u.a * F4c.sg u.b + F4c.sg u.c) =
    g.x * (g.Y u.b * g.X u.a * g.Z u.c) * g.x⁻¹
  rw [show g.x * (g.Y u.b * g.X u.a * g.Z u.c) * g.x⁻¹ =
    (g.x * g.Y u.b * g.x⁻¹) * (g.x * g.X u.a * g.x⁻¹) * (g.x * g.Z u.c * g.x⁻¹) by group,
    conj_Y, conj_X, conj_Z, X_mul_Y, Z_add, mul_comm (F4c.sg u.b)]
  simp only [mul_assoc]

@[expose] def chi : Multiplicative (ZMod 2) →* G where
  toFun e := if e = 1 then 1 else g.x
  map_one' := by simp
  map_mul' a b := by
    have hcases : ∀ e : Multiplicative (ZMod 2), e = 1 ∨ e = Multiplicative.ofAdd 1 := by decide
    have hne : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide
    have hsq : (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd 1 = 1 := by decide
    rcases hcases a with rfl | rfl <;> rcases hcases b with rfl | rfl
    · simp
    · simp
    · simp
    · rw [hsq]
      simp [hne, g.x_sq]

theorem chi_ofAdd : g.chi (Multiplicative.ofAdd 1) = g.x := by
  have hne : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide
  simp [chi, hne]

theorem compat (e : Multiplicative (ZMod 2)) :
    g.kappa.comp (psi e).toMonoidHom = (MulAut.conj (g.chi e)).toMonoidHom.comp g.kappa := by
  have hcases : ∀ e : Multiplicative (ZMod 2), e = 1 ∨ e = Multiplicative.ofAdd 1 := by decide
  rcases hcases e with rfl | rfl
  · ext u
    simp
  · have hne : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide
    ext u
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, chi_ofAdd]
    rw [← kappa_phi]
    simp [psi, hne]

@[expose] def hom : J2Syl →* G := SemidirectProduct.lift g.kappa g.chi g.compat

theorem hom_inl (u : L34Syl) : g.hom (SemidirectProduct.inl u) = g.kappa u :=
  SemidirectProduct.lift_inl _ _ _ _

theorem hom_inr (e : Multiplicative (ZMod 2)) : g.hom (SemidirectProduct.inr e) = g.chi e :=
  SemidirectProduct.lift_inr _ _ _ _

theorem hom_x0 : g.hom J2Syl.x0 = g.x := by
  change g.hom (SemidirectProduct.inr (Multiplicative.ofAdd 1)) = g.x
  rw [hom_inr, chi_ofAdd]

theorem hom_apply (s : J2Syl) : g.hom s = g.kappa s.left * g.chi s.right := by
  conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right s]
  rw [map_mul, hom_inl, hom_inr]

theorem hom_z0 : g.hom J2Syl.z0 = g.Z .z1 := by
  change g.hom (SemidirectProduct.inl ⟨0, 0, 1⟩) = _
  rw [hom_inl, kappa_apply]
  change g.Y .z0 * g.X .z0 * g.Z .z1 = _
  rw [X_z0]
  change 1 * 1 * g.Z .z1 = _
  rw [one_mul, one_mul]

theorem hom_injective (hd : g.Z .z1 ≠ 1) : Function.Injective g.hom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 J2Syl := IsPGroup.of_card (n := 7) (by rw [card_J2Syl]; norm_num)
  have : Group.IsNilpotent J2Syl := h2.isNilpotent
  rw [← MonoidHom.ker_eq_bot_iff]
  by_contra hne
  obtain ⟨t, ht1⟩ :=
    (Subgroup.ne_bot_iff_exists_ne_one).mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  obtain ⟨htk, htc⟩ := mem_inf.mp t.2
  rcases (J2Syl.center_iff t).1 (fun u => ((mem_center_iff.mp htc) u).symm) with h1 | h1
  · exact ht1 (Subtype.ext h1)
  · rw [h1, MonoidHom.mem_ker, hom_z0] at htk
    exact hd htk

theorem kappa_mem (u : L34Syl) : g.kappa u ∈ g.P :=
  mul_mem (mul_mem (g.Y_mem _) (g.X_mem _)) (g.C_le (g.Z_mem _))

theorem j2Emb {S : Subgroup G} (hd : g.Z .z1 ≠ 1) (hS : Nat.card S = 128) (hPS : g.P ≤ S)
    (hxS : g.x ∈ S) (hP : Nat.card g.P = 64) : J2Emb S g.P g.x := by
  have hf := g.hom_injective hd
  have : Finite S := Nat.finite_of_card_ne_zero (by rw [hS]; norm_num)
  have : Finite g.P := Nat.finite_of_card_ne_zero (by rw [hP]; norm_num)
  have hchi : ∀ e, g.chi e ∈ S := fun e => by
    by_cases he : e = 1
    · simp [chi, he]
    · simpa [chi, he] using hxS
  refine ⟨g.hom, hf, ?_, ?_, g.hom_x0⟩
  · apply eq_of_le_of_card_ge
    · rintro _ ⟨s, rfl⟩
      rw [hom_apply]
      exact mul_mem (hPS (g.kappa_mem _)) (hchi _)
    · rw [hS, card_range_of_injective hf, card_J2Syl]
  · apply eq_of_le_of_card_ge
    · rintro _ ⟨s, hs, rfl⟩
      have hs1 : s.right = 1 := hs
      rw [hom_apply, hs1, map_one, mul_one]
      exact g.kappa_mem _
    · rw [hP, card_map_of_injective hf, J2Syl.card_W]

end J2Gens

end CFSG.ComponentClassification.RankTwoAltFive
