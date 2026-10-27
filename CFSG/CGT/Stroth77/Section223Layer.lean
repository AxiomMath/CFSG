module

public import CFSG.CGT.Stroth77.Section223Frame
public import CFSG.CGT.Stroth77.Section41
public import CFSG.CGT.Stroth77.Section224A

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsSylowIn)

namespace StrothTypeIndex

theorem exists_uv_c_a (τ : StrothTypeIndex) :
    ∃ o : ℤ, Odd o ∧ τ.action.uv 1 0 = 2 ^ (τ.k 1 - τ.k 0) * o := by
  cases τ with
  | t100 m =>
    refine ⟨-1, ⟨-1, by norm_num⟩, ?_⟩
    show (-2 : ℤ) = 2 ^ ((m + 1) - m) * -1
    rw [Nat.add_sub_cancel_left]; norm_num
  | t101 s =>
    refine ⟨-1, ⟨-1, by norm_num⟩, ?_⟩
    show (-2 : ℤ) = 2 ^ ((s + 2) - (s + 1)) * -1
    rw [show s + 2 - (s + 1) = 1 by omega]; norm_num
  | t110 t =>
    refine ⟨-1 + 2 ^ (t + 1), ⟨2 ^ t - 1, by ring⟩, ?_⟩
    show (-2 + 2 ^ (t + 2) : ℤ) = 2 ^ ((t + 3) - (t + 2)) * (-1 + 2 ^ (t + 1))
    rw [show t + 3 - (t + 2) = 1 by omega]; ring
  | t111 t =>
    refine ⟨-1 + 2 ^ (t + 1), ⟨2 ^ t - 1, by ring⟩, ?_⟩
    show (-2 + 2 ^ (t + 2) : ℤ) = 2 ^ ((t + 3) - (t + 2)) * (-1 + 2 ^ (t + 1))
    rw [show t + 3 - (t + 2) = 1 by omega]; ring
  | t120 m _ =>
    refine ⟨1, odd_one, ?_⟩
    show (2 : ℤ) = 2 ^ ((m + 1) - m) * 1
    rw [Nat.add_sub_cancel_left]; norm_num
  | t121 m _ =>
    refine ⟨1, odd_one, ?_⟩
    show (2 : ℤ) = 2 ^ ((m + 1) - m) * 1
    rw [Nat.add_sub_cancel_left]; norm_num
  | t130 m hm =>
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
    refine ⟨1 + 2 ^ (m + 1), ⟨2 ^ m, by ring⟩, ?_⟩
    show (2 + 2 ^ (m + 2) : ℤ) = 2 ^ ((m + 2 + 1) - (m + 2)) * (1 + 2 ^ (m + 1))
    rw [Nat.add_sub_cancel_left]; ring
  | t131 m hm =>
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
    refine ⟨1 + 2 ^ (m + 1), ⟨2 ^ m, by ring⟩, ?_⟩
    show (2 + 2 ^ (m + 2) : ℤ) = 2 ^ ((m + 2 + 1) - (m + 2)) * (1 + 2 ^ (m + 1))
    rw [Nat.add_sub_cancel_left]; ring
  | t200 m =>
    refine ⟨-1, ⟨-1, by norm_num⟩, ?_⟩
    show (-4 : ℤ) = 2 ^ ((m + 2) - m) * -1
    rw [Nat.add_sub_cancel_left]; norm_num
  | t201 m =>
    refine ⟨-1, ⟨-1, by norm_num⟩, ?_⟩
    show (-4 : ℤ) = 2 ^ ((m + 2) - m) * -1
    rw [Nat.add_sub_cancel_left]; norm_num
  | t210 m _ =>
    refine ⟨-1 + 2 * 2 ^ (m - 2), ⟨2 ^ (m - 2) - 1, by ring⟩, ?_⟩
    show (-4 + 8 * 2 ^ (m - 2) : ℤ) = 2 ^ ((m + 2) - m) * (-1 + 2 * 2 ^ (m - 2))
    rw [Nat.add_sub_cancel_left]; ring
  | t211 m _ =>
    refine ⟨-1 + 2 * 2 ^ (m - 2), ⟨2 ^ (m - 2) - 1, by ring⟩, ?_⟩
    show (-4 + 8 * 2 ^ (m - 2) : ℤ) = 2 ^ ((m + 2) - m) * (-1 + 2 * 2 ^ (m - 2))
    rw [Nat.add_sub_cancel_left]; ring
  | t220 s _ =>
    refine ⟨1, odd_one, ?_⟩
    show (4 : ℤ) = 2 ^ ((s + 4) - (s + 2)) * 1
    rw [show s + 4 - (s + 2) = 2 by omega]; norm_num
  | t221 s _ =>
    refine ⟨1, odd_one, ?_⟩
    show (4 : ℤ) = 2 ^ ((s + 4) - (s + 2)) * 1
    rw [show s + 4 - (s + 2) = 2 by omega]; norm_num
  | t230 s _ =>
    refine ⟨1 + 2 * 2 ^ s, ⟨2 ^ s, by ring⟩, ?_⟩
    show (4 + 8 * 2 ^ s : ℤ) = 2 ^ ((s + 4) - (s + 2)) * (1 + 2 * 2 ^ s)
    rw [show s + 4 - (s + 2) = 2 by omega]; ring
  | t231 s _ =>
    refine ⟨1 + 2 * 2 ^ s, ⟨2 ^ s, by ring⟩, ?_⟩
    show (4 + 8 * 2 ^ s : ℤ) = 2 ^ ((s + 4) - (s + 2)) * (1 + 2 * 2 ^ s)
    rw [show s + 4 - (s + 2) = 2 by omega]; ring
  | t300 n =>
    refine ⟨-1, ⟨-1, by norm_num⟩, ?_⟩
    show (-1 : ℤ) = 2 ^ (n - n) * -1
    rw [Nat.sub_self]; norm_num
  | t310 m _ =>
    refine ⟨-1 + 2 * 2 ^ (m - 2), ⟨2 ^ (m - 2) - 1, by ring⟩, ?_⟩
    show (-1 + 2 * 2 ^ (m - 2) : ℤ) = 2 ^ (m - m) * (-1 + 2 * 2 ^ (m - 2))
    rw [Nat.sub_self]; ring
  | t320 m _ =>
    refine ⟨1, odd_one, ?_⟩
    show (1 : ℤ) = 2 ^ (m - m) * 1
    rw [Nat.sub_self]; norm_num
  | t330 m hm =>
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
    refine ⟨1 + 2 ^ (m + 1), ⟨2 ^ m, by ring⟩, ?_⟩
    show (1 + 2 ^ (m + 2 - 1) : ℤ) = 2 ^ ((m + 2) - (m + 2)) * (1 + 2 ^ (m + 1))
    rw [Nat.sub_self, show m + 2 - 1 = m + 1 by omega]; ring
  | t321 =>
    refine ⟨1, odd_one, ?_⟩
    show (1 : ℤ) = 2 ^ (3 - 3) * 1
    norm_num
  | t331 =>
    refine ⟨5, ⟨2, by norm_num⟩, ?_⟩
    show (5 : ℤ) = 2 ^ (3 - 3) * 5
    norm_num

theorem k_zero_le_k_one (τ : StrothTypeIndex) : τ.k 0 ≤ τ.k 1 := by
  cases τ <;> simp [StrothTypeIndex.k, Type100.k, Type101.k, Type110.k, Type111.k, Type120.k,
    Type121.k, Type130.k, Type131.k, Type200.k, Type201.k, Type210.k, Type211.k, Type220.k,
    Type221.k, Type230.k, Type231.k, Type300.k, Type310.k, Type32x.k, Type321.k, Type331.k]

end StrothTypeIndex

namespace S223

variable {G : Type} [Group G]

theorem inv_mul_mem_of_relIndex_eq_two {H K : Subgroup G} (hidx : H.relIndex K = 2) {y z : G}
    (hy : y ∈ K) (hz : z ∈ K) (hyH : y ∉ H) (hzH : z ∉ H) : y⁻¹ * z ∈ H := by
  have h2 : (H.subgroupOf K).index = 2 := hidx
  have hmem := (Subgroup.mul_mem_iff_of_index_two h2 (a := (⟨y, hy⟩ : K)⁻¹) (b := ⟨z, hz⟩)).2
    ⟨fun h => absurd (by simpa [Subgroup.mem_subgroupOf] using h) hyH,
      fun h => absurd (by simpa [Subgroup.mem_subgroupOf] using h) hzH⟩
  simpa [Subgroup.mem_subgroupOf] using hmem

theorem relIndex_eq_two_of_card [Finite G] {H K : Subgroup G} (hHK : H ≤ K)
    (h : Nat.card K = 2 * Nat.card H) : H.relIndex K = 2 := by
  have hmul := Subgroup.relIndex_mul_card (H := H) (K := K)
  rw [inf_of_le_left hHK, h] at hmul
  have hpos : 0 < Nat.card H := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos hmul

theorem comm_mul {D : Subgroup G} (hcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) {g : G}
    (hg : g ∈ Subgroup.normalizer (D : Set G)) {x y : G} (hx : x ∈ D) (hy : y ∈ D) :
    (x * y)⁻¹ * (g⁻¹ * (x * y) * g) = (x⁻¹ * (g⁻¹ * x * g)) * (y⁻¹ * (g⁻¹ * y * g)) := by
  have hxg : g⁻¹ * x * g ∈ D := (Subgroup.mem_normalizer_iff''.mp hg x).mp hx
  have hab : (x⁻¹ * (g⁻¹ * x * g)) * y⁻¹ = y⁻¹ * (x⁻¹ * (g⁻¹ * x * g)) :=
    hcomm _ (mul_mem (inv_mem hx) hxg) _ (inv_mem hy)
  calc (x * y)⁻¹ * (g⁻¹ * (x * y) * g) = y⁻¹ * (x⁻¹ * (g⁻¹ * x * g)) * (g⁻¹ * y * g) := by
        group
    _ = (x⁻¹ * (g⁻¹ * x * g)) * y⁻¹ * (g⁻¹ * y * g) := by rw [hab]
    _ = (x⁻¹ * (g⁻¹ * x * g)) * (y⁻¹ * (g⁻¹ * y * g)) := by group

theorem comm_conj (x r s : G) :
    x⁻¹ * ((r⁻¹ * s * r)⁻¹ * x * (r⁻¹ * s * r)) =
      r⁻¹ * ((r * x * r⁻¹)⁻¹ * (s⁻¹ * (r * x * r⁻¹) * s)) * r := by
  group

theorem conj_mem_omegaIn [Finite G] {D : Subgroup G}
    (hcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) {i : ℕ} {g : G}
    (hg : g ∈ Subgroup.normalizer (D : Set G)) {x : G} (hx : x ∈ omegaIn i D) :
    g⁻¹ * x * g ∈ omegaIn i D := by
  rw [mem_omegaIn_iff_of_comm hcomm] at hx ⊢
  refine ⟨(Subgroup.mem_normalizer_iff''.mp hg x).mp hx.1, ?_⟩
  have h := conj_pow (a := g⁻¹) (b := x) (i := 2 ^ i)
  rw [inv_inv] at h
  rw [h, hx.2, mul_one, inv_mul_cancel]

theorem mem_normalizer_omegaIn [Finite G] {D : Subgroup G} (hcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x)
    {i : ℕ} {g : G} (hg : g ∈ Subgroup.normalizer (D : Set G)) :
    g ∈ Subgroup.normalizer ((omegaIn i D : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff'']
  intro x
  refine ⟨conj_mem_omegaIn hcomm hg, fun hx => ?_⟩
  have h := conj_mem_omegaIn hcomm (inv_mem hg) hx
  simpa [mul_assoc] using h

end S223

namespace StrothWeakTypeData

variable {S : Type*} [Group S] {B : Subgroup S} {τ : StrothTypeIndex}

theorem e_inv_mul_conjBy (dB : StrothWeakTypeData B τ) {g : S} (hg : g ∈ Subgroup.normalizer B)
    {φ : Torus τ.k →+ Torus τ.k}
    (hconj : ∀ x : B, dB.e (Additive.ofMul (conjBy hg x)) = φ (dB.e (Additive.ofMul x)))
    (x : B) :
    dB.e (Additive.ofMul (x⁻¹ * conjBy hg x)) = φ (dB.e (Additive.ofMul x)) -
      dB.e (Additive.ofMul x) := by
  rw [ofMul_mul, map_add, ofMul_inv, map_neg, hconj]
  abel

theorem mul_self_eq_one_iff (dB : StrothWeakTypeData B τ) (y : B) :
    y * y = 1 ↔ (2 : ℤ) • dB.e (Additive.ofMul y) = 0 := by
  rw [two_zsmul, ← map_add, ← ofMul_mul, AddEquiv.map_eq_zero_iff]
  exact ⟨fun h => by rw [h, ofMul_one], fun h => Additive.ofMul.injective (by rw [h, ofMul_one])⟩

end StrothWeakTypeData

namespace StrothFrame

variable {G : Type} [Group G] [Finite G] (F : StrothFrame G)

theorem card_A : Nat.card F.A = 32 := by
  rw [F.dA.card]
  rfl

theorem two_zsmul_uv_sub : ∀ v : Torus (StrothTypeIndex.t100 1).k,
    (2 : ℤ) • ((StrothTypeIndex.t100 1).action.φuv v - v) = 0 := by decide

theorem two_zsmul_t_sub : ∀ v : Torus (StrothTypeIndex.t100 1).k,
    (2 : ℤ) • ((StrothTypeIndex.t100 1).action.φt v - v) = 0 := by decide

theorem two_zsmul_of_two_zsmul_rho_sub : ∀ v : Torus (StrothTypeIndex.t100 1).k,
    (2 : ℤ) • ((StrothTypeIndex.t100 1).action.φρ v - v) = 0 → (2 : ℤ) • v = 0 := by decide

theorem four_zsmul_A : ∀ v : Torus (StrothTypeIndex.t100 1).k, (4 : ℤ) • v = 0 := by decide

theorem comm_uv_mem_omegaIn_A {x : G} (hx : x ∈ F.A) :
    x⁻¹ * (F.dA.uv⁻¹ * x * F.dA.uv) ∈ omegaIn 1 F.A := by
  set a : F.A := ⟨x, hx⟩
  refine mem_omegaIn_one_of_mul_self (a⁻¹ * conjBy F.dA.uv_mem a).2 ?_
  have h := (F.dA.mul_self_eq_one_iff (a⁻¹ * conjBy F.dA.uv_mem a)).2 (by
    rw [F.dA.e_inv_mul_conjBy F.dA.uv_mem F.dA.uv_conj]
    exact two_zsmul_uv_sub _)
  exact congrArg Subtype.val h

theorem comm_t_mem_omegaIn_A {x : G} (hx : x ∈ F.A) :
    x⁻¹ * (F.dA.t⁻¹ * x * F.dA.t) ∈ omegaIn 1 F.A := by
  set a : F.A := ⟨x, hx⟩
  refine mem_omegaIn_one_of_mul_self (a⁻¹ * conjBy F.dA.t_mem a).2 ?_
  have h := (F.dA.mul_self_eq_one_iff (a⁻¹ * conjBy F.dA.t_mem a)).2 (by
    rw [F.dA.e_inv_mul_conjBy F.dA.t_mem F.dA.t_conj]
    exact two_zsmul_t_sub _)
  exact congrArg Subtype.val h

theorem mem_omegaIn_A_of_comm_rho_mem {x : G} (hx : x ∈ F.A)
    (h : x⁻¹ * (F.dA.ρ⁻¹ * x * F.dA.ρ) ∈ omegaIn 1 F.A) : x ∈ omegaIn 1 F.A := by
  have hcommA := comm_of_torus F.dA.e
  set a : F.A := ⟨x, hx⟩
  have h2 : (a⁻¹ * conjBy F.dA.ρ_mem a) * (a⁻¹ * conjBy F.dA.ρ_mem a) = 1 :=
    Subtype.ext (mul_self_eq_one_of_mem_omegaIn_one hcommA h)
  rw [F.dA.mul_self_eq_one_iff, F.dA.e_inv_mul_conjBy F.dA.ρ_mem F.dA.ρ_conj] at h2
  have h3 : a * a = 1 := (F.dA.mul_self_eq_one_iff a).2 (two_zsmul_of_two_zsmul_rho_sub _ h2)
  exact mem_omegaIn_one_of_mul_self hx (congrArg Subtype.val h3)

theorem pow_four_eq_one_of_mem_A {x : G} (hx : x ∈ F.A) : x ^ 4 = 1 := by
  have h : (⟨x, hx⟩ : F.A) ^ 4 = 1 := by
    apply Additive.ofMul.injective
    apply F.dA.e.injective
    rw [ofMul_pow, map_nsmul, ofMul_one, map_zero, ← natCast_zsmul]
    exact four_zsmul_A _
  exact congrArg Subtype.val h

theorem t_eq_conj : F.dA.t = F.dA.ρ⁻¹ * F.dA.uv * F.dA.ρ := by
  rw [mul_assoc, F.dA.uv_rho]
  group

end StrothFrame

namespace StrothFrame

variable {G : Type} [Group G] [Finite G]

structure IsTyped (F : StrothFrame G) (D : Subgroup G) {τ : StrothTypeIndex}
    (dD : StrothWeakTypeData D τ) : Prop where
  A_le : F.A ≤ D
  le_S : D ≤ (F.S : Subgroup G)
  uv_eq : dD.uv = F.dA.uv
  t_eq : dD.t = F.dA.t
  u_eq : dD.u = F.dA.u
  ρ_eq : dD.ρ = F.dA.ρ

variable {F : StrothFrame G} {D : Subgroup G} {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}

theorem IsD.isTyped (h : F.IsD D dD) : F.IsTyped D dD :=
  ⟨h.A_le, h.le_S, h.uv_eq, h.t_eq, h.u_eq, h.ρ_eq⟩

theorem IsTyped.isD_of_isSylowIn (h : F.IsTyped D dD)
    (hsyl : IsSylowIn 2 (Subgroup.centralizer (D : Set G)) D) : F.IsD D dD :=
  ⟨h.A_le, h.le_S, h.uv_eq, h.t_eq, h.u_eq, h.ρ_eq,
    S223.inf_centralizer_eq_of_isSylowIn hsyl F.S.2 h.le_S⟩

theorem IsTyped.omegaIn_one_eq (h : F.IsTyped D dD) : omegaIn 1 D = omegaIn 1 F.A := by
  refine (Subgroup.eq_of_le_of_card_ge (omegaIn_one_mono (comm_of_torus F.dA.e) h.A_le) ?_).symm
  rw [F.card_omegaIn_one_A]
  exact card_omegaIn_one_le dD.e

theorem IsTyped.mem_A_of_mul_self (h : F.IsTyped D dD) {x : G} (hx : x ∈ D) (hx2 : x * x = 1) :
    x ∈ F.A := by
  have hmem : x ∈ omegaIn 1 D := mem_omegaIn_one_of_mul_self hx hx2
  rw [h.omegaIn_one_eq] at hmem
  exact omegaIn_le 1 F.A hmem

end StrothFrame

namespace StrothFrame.IsD

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}
  {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}

theorem comm (_h : F.IsD D dD) : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := comm_of_torus dD.e

theorem omegaIn_one_le_A (h : F.IsD D dD) : omegaIn 1 D ≤ F.A := by
  rw [h.omegaIn_one_eq]
  exact omegaIn_le 1 F.A

theorem A_le_omegaIn_two (h : F.IsD D dD) : F.A ≤ omegaIn 2 D := fun _ hx =>
  mem_omegaIn_of_pow_eq_one (h.A_le hx) (F.pow_four_eq_one_of_mem_A hx)

theorem uv_mem_normalizer (h : F.IsD D dD) : F.dA.uv ∈ Subgroup.normalizer (D : Set G) :=
  h.uv_eq ▸ dD.uv_mem

theorem t_mem_normalizer (h : F.IsD D dD) : F.dA.t ∈ Subgroup.normalizer (D : Set G) :=
  h.t_eq ▸ dD.t_mem

theorem ρ_mem_normalizer (h : F.IsD D dD) : F.dA.ρ ∈ Subgroup.normalizer (D : Set G) :=
  h.ρ_eq ▸ dD.ρ_mem

theorem u_mem_normalizer (h : F.IsD D dD) : F.dA.u ∈ Subgroup.normalizer (D : Set G) :=
  h.u_eq ▸ dD.u_mem

theorem card_omegaIn_two (_h : F.IsD D dD) (hm : 2 ≤ τ.k 0) : Nat.card (omegaIn 2 D) = 64 := by
  have h1 : 2 ≤ τ.k 1 := hm.trans τ.k_zero_le_k_one
  have h2 : 2 ≤ τ.k 2 := by rw [τ.k_two]; exact h1
  rw [card_omegaIn_two_eq dD.e, card_four_torsion_torus, Fin.prod_univ_three,
    card_four_torsion_zmod_two_pow _ hm, card_four_torsion_zmod_two_pow _ h1,
    card_four_torsion_zmod_two_pow _ h2]
  norm_num

theorem card_four_torsion_le_four (k : ℕ) :
    Nat.card {z : ZMod (2 ^ k) // (4 : ℤ) • z = 0} ≤ 4 := by
  rcases le_or_gt 2 k with hk | hk
  · rw [card_four_torsion_zmod_two_pow k hk]
  · calc Nat.card {z : ZMod (2 ^ k) // (4 : ℤ) • z = 0} ≤ Nat.card (ZMod (2 ^ k)) :=
          Finite.card_subtype_le _
      _ = 2 ^ k := Nat.card_zmod _
      _ ≤ 4 := by interval_cases k <;> norm_num

theorem omegaIn_two_eq_A_of_le_one (h : F.IsD D dD) (hm : τ.k 0 ≤ 1) : omegaIn 2 D = F.A := by
  refine (Subgroup.eq_of_le_of_card_ge h.A_le_omegaIn_two ?_).symm
  rw [F.card_A, card_omegaIn_two_eq dD.e, card_four_torsion_torus, Fin.prod_univ_three]
  have h0 : Nat.card {z : ZMod (2 ^ τ.k 0) // (4 : ℤ) • z = 0} ≤ 2 :=
    calc Nat.card {z : ZMod (2 ^ τ.k 0) // (4 : ℤ) • z = 0} ≤ Nat.card (ZMod (2 ^ τ.k 0)) :=
          Finite.card_subtype_le _
      _ = 2 ^ τ.k 0 := Nat.card_zmod _
      _ ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hm
      _ = 2 := by norm_num
  calc _ ≤ 2 * 4 * 4 := Nat.mul_le_mul (Nat.mul_le_mul h0 (card_four_torsion_le_four _))
        (card_four_torsion_le_four _)
    _ = 32 := by norm_num

theorem uv_gen_zero_one (τ : StrothTypeIndex) :
    (τ.action.φuv (gen τ.k 0) - gen τ.k 0) 1 = ((τ.action.uv 1 0 : ℤ) : ZMod (2 ^ τ.k 1)) := by
  rw [Pi.sub_apply, matAct_gen_eq]
  simp [gen]

theorem exists_comm_uv_not_mem (h : F.IsD D dD) (hm : 2 ≤ τ.k 0) :
    ∃ x ∈ omegaIn 2 D, x⁻¹ * (F.dA.uv⁻¹ * x * F.dA.uv) ∉ omegaIn 1 D := by
  have hcomm := h.comm
  set N : ℕ := 2 ^ (τ.k 0 - 2)
  set xD : D := dD.c ^ N
  have hec : dD.e (Additive.ofMul dD.c) = gen τ.k 0 := by simp [StrothWeakTypeData.c]
  have hex : dD.e (Additive.ofMul xD) = N • gen τ.k 0 := by
    rw [ofMul_pow, map_nsmul, hec]
  refine ⟨(xD : G), mem_omegaIn_of_pow_eq_one xD.2 ?_, ?_⟩
  · have h4 : xD ^ (2 ^ 2) = 1 := by
      apply Additive.ofMul.injective
      apply dD.e.injective
      rw [ofMul_pow, map_nsmul, hex, ofMul_one, map_zero, smul_smul]
      funext i
      fin_cases i
      · change ((2 ^ 2 * N : ℕ) • (1 : ZMod (2 ^ τ.k 0))) = 0
        rw [nsmul_eq_mul, mul_one]
        have hpow : 2 ^ 2 * N = 2 ^ τ.k 0 := by
          rw [← pow_add]
          congr 1
          omega
        rw [hpow]
        exact ZMod.natCast_self _
      · simp [gen]
      · simp [gen]
    exact congrArg Subtype.val h4
  · intro hmem
    have hy : (xD⁻¹ * conjBy dD.uv_mem xD : D) * (xD⁻¹ * conjBy dD.uv_mem xD) = 1 := by
      apply Subtype.ext
      have h1 := mul_self_eq_one_of_mem_omegaIn_one hcomm hmem
      rw [← h.uv_eq] at h1
      simpa [conjBy_val, mul_assoc] using h1
    rw [dD.mul_self_eq_one_iff, dD.e_inv_mul_conjBy dD.uv_mem dD.uv_conj, hex, map_nsmul,
      ← nsmul_sub] at hy
    have hcoord := congrFun hy 1
    rw [Pi.smul_apply, Pi.smul_apply, uv_gen_zero_one, Pi.zero_apply] at hcoord
    obtain ⟨o, ho, hoeq⟩ := τ.exists_uv_c_a
    rw [hoeq] at hcoord
    have hn : 1 ≤ τ.k 1 := le_trans (by omega) (hm.trans τ.k_zero_le_k_one)
    have hval : (2 : ℤ) * (N : ℤ) * (2 ^ (τ.k 1 - τ.k 0) * o) = 2 ^ (τ.k 1 - 1) * o := by
      have hk := τ.k_zero_le_k_one
      rw [show (N : ℤ) = 2 ^ (τ.k 0 - 2) by simp [N], ← mul_assoc, ← pow_succ',
        ← pow_add]
      congr 2
      omega
    have hz : ((2 ^ (τ.k 1 - 1) * o : ℤ) : ZMod (2 ^ τ.k 1)) = 0 := by
      rw [← hval]
      simpa [zsmul_eq_mul, nsmul_eq_mul, mul_assoc] using hcoord
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
    obtain ⟨w, hw⟩ := hz
    have h2 : (2 : ℤ) ^ τ.k 1 = 2 ^ (τ.k 1 - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    rw [Nat.cast_pow, Nat.cast_ofNat, h2, mul_assoc] at hw
    have hw' : o = 2 * w := mul_left_cancel₀ (pow_ne_zero _ (by norm_num)) hw
    obtain ⟨r, hr⟩ := ho
    omega

theorem eq_A_of_le_omegaIn_two (h : F.IsD D dD) {X : Subgroup G} (h1 : omegaIn 1 D ≤ X)
    (h2 : X ≤ omegaIn 2 D) (hcard : Nat.card X = Nat.card F.A)
    (huvX : F.dA.uv ∈ Subgroup.normalizer (X : Set G))
    (htX : F.dA.t ∈ Subgroup.normalizer (X : Set G)) : X = F.A := by
  classical
  by_cases hm : 2 ≤ τ.k 0
  swap
  · have hΩ : omegaIn 2 D = F.A := h.omegaIn_two_eq_A_of_le_one (by omega)
    exact Subgroup.eq_of_le_of_card_ge (hΩ ▸ h2) hcard.symm.le
  have hcomm := h.comm
  have hΩ₁A := h.omegaIn_one_le_A
  have hAΩ₂ := h.A_le_omegaIn_two
  have hΩ₁ : omegaIn 1 D = omegaIn 1 F.A := h.omegaIn_one_eq
  have hcA : Nat.card F.A = 32 := F.card_A
  have hcΩ₁ : Nat.card (omegaIn 1 D) = 8 := by rw [hΩ₁]; exact F.card_omegaIn_one_A
  have hcΩ₂ : Nat.card (omegaIn 2 D) = 64 := h.card_omegaIn_two hm
  have huvD := h.uv_mem_normalizer
  have htD := h.t_mem_normalizer
  have hρD := h.ρ_mem_normalizer
  have huvA : F.dA.uv ∈ Subgroup.normalizer (F.A : Set G) := F.dA.uv_mem
  have htA : F.dA.t ∈ Subgroup.normalizer (F.A : Set G) := F.dA.t_mem
  have hρA : F.dA.ρ ∈ Subgroup.normalizer (F.A : Set G) := F.dA.ρ_mem
  have hidx : F.A.relIndex (omegaIn 2 D) = 2 :=
    S223.relIndex_eq_two_of_card hAΩ₂ (by rw [hcΩ₂, hcA])
  have hcoset : ∀ y ∈ omegaIn 2 D, ∀ z ∈ omegaIn 2 D, y ∉ F.A → z ∉ F.A → y⁻¹ * z ∈ F.A :=
    fun y hy z hz hyA hzA => S223.inv_mul_mem_of_relIndex_eq_two hidx hy hz hyA hzA
  have hconjA : ∀ {g : G}, g ∈ Subgroup.normalizer (F.A : Set G) → ∀ y : G,
      y ∈ F.A ↔ g⁻¹ * y * g ∈ F.A := fun hg y => Subgroup.mem_normalizer_iff''.mp hg y
  have hcommA : ∀ {g : G}, g ∈ Subgroup.normalizer (D : Set G) →
      g ∈ Subgroup.normalizer (F.A : Set G) → ∀ {y : G}, y ∈ omegaIn 2 D →
        y⁻¹ * (g⁻¹ * y * g) ∈ F.A := by
    intro g hgD hgA y hy
    by_cases hyA : y ∈ F.A
    · exact mul_mem (inv_mem hyA) ((hconjA hgA y).mp hyA)
    · exact hcoset y hy _ (S223.conj_mem_omegaIn hcomm hgD hy) hyA
        (fun h' => hyA ((hconjA hgA y).mpr h'))
  obtain ⟨x₀, hx₀Ω₂, hx₀⟩ := h.exists_comm_uv_not_mem hm
  set z₀ := x₀⁻¹ * (F.dA.uv⁻¹ * x₀ * F.dA.uv) with hz₀
  have hz₀A : z₀ ∈ F.A := hcommA huvD huvA hx₀Ω₂
  have hx₀A : x₀ ∉ F.A := fun hA => hx₀ (by rw [hΩ₁]; exact F.comm_uv_mem_omegaIn_A hA)
  have hstepD : ∀ y ∈ omegaIn 2 D, y ∉ F.A →
      (y⁻¹ * (F.dA.uv⁻¹ * y * F.dA.uv))⁻¹ * z₀ ∈ omegaIn 1 D := by
    intro y hy hyA
    have ha : y⁻¹ * x₀ ∈ F.A := hcoset y hy x₀ hx₀Ω₂ hyA hx₀A
    have hyD : y ∈ D := omegaIn_le 2 D hy
    have hsplit := S223.comm_mul hcomm huvD hyD (hAΩ₂.trans (omegaIn_le 2 D) ha)
    rw [mul_inv_cancel_left] at hsplit
    rw [hz₀, hsplit, ← mul_assoc, inv_mul_cancel, one_mul, hΩ₁]
    exact F.comm_uv_mem_omegaIn_A ha
  have hstepE : ∀ y ∈ omegaIn 2 D, y ∉ F.A →
      (y⁻¹ * (F.dA.t⁻¹ * y * F.dA.t))⁻¹ * (F.dA.ρ⁻¹ * z₀ * F.dA.ρ) ∈ omegaIn 1 D := by
    intro y hy hyA
    set y' := F.dA.ρ * y * F.dA.ρ⁻¹ with hy'
    have hy'Ω₂ : y' ∈ omegaIn 2 D := by
      have := S223.conj_mem_omegaIn hcomm (inv_mem hρD) hy
      simpa [hy'] using this
    have hy'A : y' ∉ F.A := by
      intro h'
      apply hyA
      have := (hconjA hρA y').mp h'
      simpa [hy', mul_assoc] using this
    have hω := hstepD y' hy'Ω₂ hy'A
    have hident := S223.comm_conj y F.dA.ρ F.dA.uv
    rw [← F.t_eq_conj, ← hy'] at hident
    rw [hident]
    have := S223.conj_mem_omegaIn hcomm hρD hω
    convert this using 1
    group
  by_contra hne
  obtain ⟨x', hx'X, hx'A⟩ : ∃ x' ∈ X, x' ∉ F.A := by
    by_contra hall
    refine hne (Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) hcard.symm.le)
    by_contra hxA
    exact hall ⟨x, hx, hxA⟩
  have hx'Ω₂ : x' ∈ omegaIn 2 D := h2 hx'X
  set p := x'⁻¹ * (F.dA.uv⁻¹ * x' * F.dA.uv) with hp
  set q := x'⁻¹ * (F.dA.t⁻¹ * x' * F.dA.t) with hq
  have hpX : p ∈ X := mul_mem (inv_mem hx'X) ((Subgroup.mem_normalizer_iff''.mp huvX x').mp hx'X)
  have hqX : q ∈ X := mul_mem (inv_mem hx'X) ((Subgroup.mem_normalizer_iff''.mp htX x').mp hx'X)
  have hpA : p ∈ F.A := hcommA huvD huvA hx'Ω₂
  have hqA : q ∈ F.A := hcommA htD htA hx'Ω₂
  have hpz : p⁻¹ * z₀ ∈ omegaIn 1 D := hstepD x' hx'Ω₂ hx'A
  have hqz : q⁻¹ * (F.dA.ρ⁻¹ * z₀ * F.dA.ρ) ∈ omegaIn 1 D := hstepE x' hx'Ω₂ hx'A
  have hpΩ : p ∉ omegaIn 1 D := by
    intro h'
    apply hx₀
    have := mul_mem h' hpz
    rwa [mul_inv_cancel_left] at this
  have hz₀ρ : F.dA.ρ⁻¹ * z₀ * F.dA.ρ ∉ omegaIn 1 D := by
    intro h'
    apply hx₀
    have := S223.conj_mem_omegaIn hcomm (inv_mem hρD) h'
    rwa [inv_inv, show F.dA.ρ * (F.dA.ρ⁻¹ * z₀ * F.dA.ρ) * F.dA.ρ⁻¹ = z₀ by group] at this
  have hqΩ : q ∉ omegaIn 1 D := by
    intro h'
    apply hz₀ρ
    have := mul_mem h' hqz
    rwa [mul_inv_cancel_left] at this
  set P₀ := X ⊓ F.A with hP₀
  have hΩ₁P₀ : omegaIn 1 D ≤ P₀ := le_inf h1 hΩ₁A
  have hcP₀ : Nat.card P₀ = 16 := by
    have hd32 : Nat.card P₀ ∣ 2 ^ 5 := by
      rw [show (2 : ℕ) ^ 5 = 32 by norm_num, ← hcA]
      exact Subgroup.card_dvd_of_le inf_le_right
    have hd8 : 8 ∣ Nat.card P₀ := by
      rw [← hcΩ₁]
      exact Subgroup.card_dvd_of_le hΩ₁P₀
    have hne32 : Nat.card P₀ ≠ 32 := by
      intro h32
      apply hne
      have hP₀A : P₀ = F.A := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h32, hcA])
      have hAX : F.A ≤ X := hP₀A ▸ inf_le_left
      exact (Subgroup.eq_of_le_of_card_ge hAX hcard.le).symm
    have hne8 : Nat.card P₀ ≠ 8 := by
      intro h8
      have hΩ₁eq : omegaIn 1 D = P₀ :=
        Subgroup.eq_of_le_of_card_ge hΩ₁P₀ (by rw [h8, hcΩ₁])
      exact hpΩ (hΩ₁eq ▸ ⟨hpX, hpA⟩)
    obtain ⟨j, hj, hcj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd32
    rw [hcj] at hd8 hne32 hne8 ⊢
    interval_cases j
    · norm_num at hd8
    · norm_num at hd8
    · norm_num at hd8
    · exact absurd (by norm_num) hne8
    · norm_num
    · exact absurd (by norm_num) hne32
  have hidx₁ : (omegaIn 1 D).relIndex P₀ = 2 :=
    S223.relIndex_eq_two_of_card hΩ₁P₀ (by rw [hcP₀, hcΩ₁])
  have hpq : p⁻¹ * q ∈ omegaIn 1 D :=
    S223.inv_mul_mem_of_relIndex_eq_two hidx₁ ⟨hpX, hpA⟩ ⟨hqX, hqA⟩ hpΩ hqΩ
  have hzρ : z₀⁻¹ * (F.dA.ρ⁻¹ * z₀ * F.dA.ρ) ∈ omegaIn 1 F.A := by
    rw [← hΩ₁]
    have := mul_mem (mul_mem (inv_mem hpz) hpq) hqz
    convert this using 1
    group
  have hz₀Ω : z₀ ∈ omegaIn 1 D := by
    rw [hΩ₁]
    exact F.mem_omegaIn_A_of_comm_rho_mem hz₀A hzρ
  exact hx₀ hz₀Ω

theorem le_normalizer_A (h : F.IsD D dD) {T : Subgroup G} (hT : IsPGroup 2 T)
    (hTD : T ≤ Subgroup.normalizer (D : Set G)) (huv : F.dA.uv ∈ T) (ht : F.dA.t ∈ T) :
    T ≤ Subgroup.normalizer (F.A : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hle
  set H : Subgroup T := (Subgroup.normalizer (F.A : Set G)).subgroupOf T with hH
  have hHlt : H < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hle fun x hx => ?_
    have hmem : (⟨x, hx⟩ : T) ∈ H := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hmem
  have : Group.IsNilpotent T := hT.isNilpotent
  obtain ⟨g, hgN, hgH⟩ :=
    SetLike.exists_of_lt (Group.normalizerCondition_of_isNilpotent H hHlt)
  set X : Subgroup G := F.A.map (MulAut.conj ((g : G)⁻¹)).toMonoidHom with hX
  have hmemX : ∀ x : G, x ∈ X ↔ (g : G) * x * (g : G)⁻¹ ∈ F.A := by
    intro x
    constructor
    · rintro ⟨a, ha, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using ha
    · intro hx
      exact ⟨(g : G) * x * (g : G)⁻¹, hx, by simp [mul_assoc]⟩
  have hgD : (g : G) ∈ Subgroup.normalizer (D : Set G) := hTD g.2
  have hcomm := h.comm
  have h1 : omegaIn 1 D ≤ X := fun x hx => (hmemX x).2 (h.omegaIn_one_le_A (by
    have := S223.conj_mem_omegaIn hcomm (inv_mem hgD) hx
    simpa using this))
  have h2 : X ≤ omegaIn 2 D := fun x hx => by
    have hx' := h.A_le_omegaIn_two ((hmemX x).1 hx)
    have := S223.conj_mem_omegaIn hcomm hgD hx'
    simpa [mul_assoc] using this
  have hcard : Nat.card X = Nat.card F.A :=
    Subgroup.card_map_of_injective (MulAut.conj ((g : G)⁻¹)).injective
  have hnorm : ∀ {w : G}, w ∈ T → w ∈ Subgroup.normalizer (F.A : Set G) →
      w ∈ Subgroup.normalizer (X : Set G) := by
    intro w hwT hwA
    have hk : (g : G) * w * (g : G)⁻¹ ∈ Subgroup.normalizer (F.A : Set G) := by
      have hin : (⟨w, hwT⟩ : T) ∈ H := Subgroup.mem_subgroupOf.mpr hwA
      have hin' := (Subgroup.mem_normalizer_iff.mp hgN _).mp hin
      exact Subgroup.mem_subgroupOf.mp hin'
    rw [Subgroup.mem_normalizer_iff'']
    intro x
    rw [hmemX, hmemX]
    have e : (g : G) * (w⁻¹ * x * w) * (g : G)⁻¹ =
        ((g : G) * w * (g : G)⁻¹)⁻¹ * ((g : G) * x * (g : G)⁻¹) *
          ((g : G) * w * (g : G)⁻¹) := by group
    rw [e]
    exact Subgroup.mem_normalizer_iff''.mp hk _
  have hXA := h.eq_A_of_le_omegaIn_two h1 h2 hcard (hnorm huv F.dA.uv_mem)
    (hnorm ht F.dA.t_mem)
  apply hgH
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    exact (hmemX a).1 (by rw [hXA]; exact ha)
  · intro ha
    have hX' := (hmemX a).2 ha
    rwa [hXA] at hX'

theorem exists_isSylowIn_normalizer (h : F.IsD D dD)
    (hsyl : IsSylowIn 2 (Subgroup.centralizer (D : Set G)) D) :
    ∃ F' : StrothFrame G, F'.IsD D dD ∧ IsSylowIn 2 (Subgroup.normalizer (D : Set G))
      ((F'.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT, hPT⟩ := S223.exists_isSylowIn_ge
    (inf_le_right : (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ≤ _)
    (F.S.2.to_le inf_le_left)
  have hDP : D ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) :=
    le_inf h.le_S Subgroup.le_normalizer
  have huvT : F.dA.uv ∈ T := hPT ⟨F.uv_mem_S, h.uv_mem_normalizer⟩
  have htT : F.dA.t ∈ T := hPT ⟨F.t_mem_S, h.t_mem_normalizer⟩
  have huT : F.dA.u ∈ T := hPT ⟨F.u_mem_S, h.u_mem_normalizer⟩
  have hTA := h.le_normalizer_A hT.2.1 hT.1 huvT htT
  obtain ⟨S', hA', huv', ht', hu', hns, hTS'⟩ := F.exists_withSylow_of_le hT.2.1 hTA
    ((h.A_le.trans hDP).trans hPT) huvT htT huT
  have hDS' : D ≤ (S' : Subgroup G) := (hDP.trans hPT).trans hTS'
  exact ⟨F.withSylow S' hA' huv' ht' hu' hns,
    h.withSylow S' hA' huv' ht' hu' hns hDS'
      (S223.inf_centralizer_eq_of_isSylowIn hsyl S'.2 hDS'),
    S223.isSylowIn_of_le hT (le_inf hTS' hT.1) inf_le_right (S'.2.to_le inf_le_left)⟩

theorem _root_.CFSG.CGT.Stroth77.StrothFrame.IsTyped.exists_isSylowIn_normalizer
    (h : F.IsTyped D dD) (hsyl : IsSylowIn 2 (Subgroup.centralizer (D : Set G)) D) :
    ∃ F' : StrothFrame G, F'.IsD D dD ∧ IsSylowIn 2 (Subgroup.normalizer (D : Set G))
      ((F'.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) :=
  (h.isD_of_isSylowIn hsyl).exists_isSylowIn_normalizer hsyl

end StrothFrame.IsD

end CFSG.CGT.Stroth77
