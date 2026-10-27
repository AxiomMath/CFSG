module

public import CFSG.Assembly.Defs
public import CFSG.CGT.Foote81L6.Basic

public section

namespace CFSG.CGT.Foote81L6

open Subgroup

section General

variable {G : Type*} [Group G]

theorem exists_conj_mem_of_isPGroup [Finite G] {p : ℕ} [Fact p.Prime] (S : Sylow p G)
    {P : Subgroup G} (hP : IsPGroup p P) : ∃ g : G, ∀ x ∈ P, g * x * g⁻¹ ∈ (S : Subgroup G) := by
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q S
  refine ⟨g, fun x hx => ?_⟩
  have : g * x * g⁻¹ ∈ ((g • Q : Sylow p G) : Subgroup G) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨x, hQ hx, rfl⟩
  rwa [hg] at this

theorem exists_ne_one_comm_of_le_normalizer {p : ℕ} [Fact p.Prime] {T N : Subgroup G}
    [Finite T] (hT : IsPGroup p T) (hNT : N ≤ T) (hnorm : T ≤ normalizer (N : Set G))
    (hN : N ≠ ⊥) : ∃ y ∈ N, y ≠ 1 ∧ ∀ x ∈ T, x * y = y * x := by
  haveI : Group.IsNilpotent T := hT.isNilpotent
  set N' : Subgroup T := N.subgroupOf T
  haveI : N'.Normal := ⟨fun x hx g => by
    rw [mem_subgroupOf] at hx ⊢
    simp only [coe_mul, coe_inv]
    exact (mem_normalizer_iff.1 (hnorm g.2) x).1 hx⟩
  have hN' : N' ≠ ⊥ := by
    intro h
    apply hN
    rw [eq_bot_iff]
    intro y hy
    have : (⟨y, hNT hy⟩ : T) ∈ N' := mem_subgroupOf.2 hy
    rw [h, mem_bot] at this
    exact congrArg Subtype.val this
  have h := Group.IsNilpotent.inf_center_ne_bot_of_normal hN'
  obtain ⟨⟨y, hy⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 h
  refine ⟨(y : G), mem_subgroupOf.1 (mem_inf.1 hy).1, fun h1 => hy1 (Subtype.ext (Subtype.ext h1)),
    fun x hx => ?_⟩
  have := mem_center_iff.1 (mem_inf.1 hy).2 ⟨x, hx⟩
  exact congrArg Subtype.val this

theorem mul_self_eq_one_of_mem_sup {H K : Subgroup G} (hc : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x)
    (hH : ∀ x ∈ H, x * x = 1) (hK : ∀ y ∈ K, y * y = 1) {g : G} (hg : g ∈ H ⊔ K) : g * g = 1 := by
  obtain ⟨x, hx, y, hy, rfl⟩ := (mem_sup_iff_of_le_normalizer (le_normalizer_of_comm hc)).1 hg
  calc x * y * (x * y) = x * (y * x) * y := by group
    _ = x * (x * y) * y := by rw [hc x hx y hy]
    _ = (x * x) * (y * y) := by group
    _ = 1 := by rw [hH x hx, hK y hy, one_mul]

theorem mul_self_eq_one_of_mem_zpowers {a g : G} (ha : a * a = 1) (hg : g ∈ zpowers a) :
    g * g = 1 := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hg
  rw [← zpow_add, zpow_eq_zpow_emod' _ (show a ^ 2 = 1 by rw [sq]; exact ha)]
  rw [show ((2 : ℕ) : ℤ) = 2 from rfl, Int.add_emod, ← two_mul, Int.mul_emod_right, zpow_zero]

theorem card_zpowers_of_involution {a : G} (ha : a * a = 1) (ha1 : a ≠ 1) :
    Nat.card (zpowers a) = 2 := by
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime (by rw [sq]; exact ha) ha1

end General

namespace FooteCore

variable {G : Type*} [Group G] {T : Subgroup G} {m n : ℕ} (D : FooteCore G T m n)

theorem goldschmidt_hyp [Finite G] (hT : ∀ Q : Subgroup G, IsPGroup 2 Q → T ≤ Q → Q = T)
    (hcl : StronglyInvolutionClosed D.A T) :
    ∀ x ∈ normalizer (D.A : Set G), x ∉ D.A → orderOf x = 2 →
      ∀ d ∈ D.A, orderOf d = 2 → ∀ g : G, g⁻¹ * x * g ≠ d := by
  intro x hxN hxA hx2 d hdA hd2 g hg
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := normalizer (D.A : Set G)
  have hTN : T ≤ N := D.T_le_normalizer_A
  let TS : Sylow 2 G := ⟨T, D.isPGroup_T, fun hQ hle => hT _ hQ hle⟩
  let TN : Sylow 2 N := TS.subtype hTN
  have hxzN : IsPGroup 2 (zpowers (⟨x, hxN⟩ : N)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hx2, pow_one]
  obtain ⟨c, hc⟩ := exists_conj_mem_of_isPGroup TN hxzN
  have hy := hc _ (mem_zpowers _)
  rw [Sylow.coe_subtype, mem_subgroupOf] at hy
  simp only [coe_mul, coe_inv] at hy
  have hyA : (c : G) * x * (c : G)⁻¹ ∉ D.A := by
    intro h
    apply hxA
    have := (mem_normalizer_iff.1 c.2 x).2 h
    exact this
  apply hyA
  have hx : x = g * d * g⁻¹ := by rw [← hg]; group
  have hy' : (c : G) * x * (c : G)⁻¹ = ((c : G) * g) * d * ((c : G) * g)⁻¹ := by
    rw [hx]; group
  rw [hy'] at hy ⊢
  exact hcl d hdA hd2 _ hy

theorem inf_B_eq_bot_of_card_le_four {P : Subgroup G} (hPT : P ≤ T)
    (hAP : D.A ≤ P) (hnorm : T ≤ normalizer (P : Set G))
    (hrank : ∀ E ≤ P, (∀ x ∈ E, x * x = 1) → Nat.card E ≤ 4) : P ⊓ D.B = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := D.finite_T
  by_contra hne
  have hnorm' : T ≤ normalizer ((P ⊓ D.B : Subgroup G) : Set G) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro x
    rw [mem_inf, mem_inf, ← mem_normalizer_iff.1 (hnorm hg), ← mem_normalizer_iff.1
      (D.T_le_normalizer_B hg)]
  obtain ⟨y, hy, hy1, hyc⟩ := exists_ne_one_comm_of_le_normalizer D.isPGroup_T
    (inf_le_left.trans hPT) hnorm' hne
  have hyB := (mem_inf.1 hy).2
  have hyb : y = D.b := by
    rcases D.eq_one_or_b_of_comm_B hyB (fun x hx => hyc x (D.B_le_T hx)) with h | h
    · exact absurd h hy1
    · exact h
  have hbP : D.b ∈ P := hyb ▸ (mem_inf.1 hy).1
  obtain ⟨x, hxA, hxx, hx1, hxa⟩ : ∃ x ∈ D.A, x * x = 1 ∧ x ≠ 1 ∧ x ≠ D.a := by
    obtain ⟨e⟩ := D.A_iso
    have hinv : ∀ i, (e.symm (DihedralGroup.sr i) : G) * e.symm (DihedralGroup.sr i) = 1 := by
      intro i
      rw [← coe_mul, ← map_mul, DihedralGroup.sr_mul_self, map_one, OneMemClass.coe_one]
    have hne1 : ∀ i, (e.symm (DihedralGroup.sr i) : G) ≠ 1 := by
      intro i h
      have : e.symm (DihedralGroup.sr i) = 1 := Subtype.ext h
      rw [MulEquiv.symm_apply_eq, map_one, DihedralGroup.one_def] at this
      cases this
    by_cases h0 : (e.symm (DihedralGroup.sr 0) : G) = D.a
    · refine ⟨e.symm (DihedralGroup.sr 1), (e.symm _).2, hinv 1, hne1 1, fun h1 => ?_⟩
      have : e.symm (DihedralGroup.sr 0) = e.symm (DihedralGroup.sr 1) :=
        Subtype.ext (h0.trans h1.symm)
      have h01 := DihedralGroup.sr.inj (e.symm.injective this)
      have h2 : (2 : ℕ) ≤ 2 ^ (m - 1) := by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right (by norm_num) (by have := D.two_le_m; omega)
      haveI : Fact (1 < 2 ^ (m - 1)) := ⟨by omega⟩
      exact zero_ne_one h01
    · exact ⟨e.symm (DihedralGroup.sr 0), (e.symm _).2, hinv 0, hne1 0, h0⟩
  have hcax : ∀ u ∈ zpowers D.a, ∀ v ∈ zpowers x, u * v = v * u := by
    intro u hu v hv
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hu
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hv
    exact ((Commute.zpow_left (D.a_comm x (mem_sup_left hxA)).symm i).zpow_right j).eq
  have hU : zpowers D.a ⊔ zpowers x ≤ D.A := sup_le (zpowers_le.2 D.a_mem) (zpowers_le.2 hxA)
  have hcUb : ∀ u ∈ zpowers D.a ⊔ zpowers x, ∀ v ∈ zpowers D.b, u * v = v * u := by
    intro u hu v hv
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hv
    exact (Commute.zpow_right (D.A_comm_B u (hU hu) D.b D.b_mem_B) j).eq
  have hEP : (zpowers D.a ⊔ zpowers x) ⊔ zpowers D.b ≤ P :=
    sup_le (hU.trans hAP) (zpowers_le.2 hbP)
  have hEelem : ∀ g ∈ (zpowers D.a ⊔ zpowers x) ⊔ zpowers D.b, g * g = 1 := by
    intro g hg
    refine mul_self_eq_one_of_mem_sup hcUb (fun u hu => ?_)
      (fun v hv => mul_self_eq_one_of_mem_zpowers D.b_mul_b hv) hg
    exact mul_self_eq_one_of_mem_sup hcax (fun v hv => mul_self_eq_one_of_mem_zpowers D.a_mul_a hv)
      (fun v hv => mul_self_eq_one_of_mem_zpowers hxx hv) hu
  have hinf1 : zpowers D.a ⊓ zpowers x = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨hga, hgx⟩ := mem_inf.1 hg
    rw [mem_bot]
    have hor : ∀ {c : G}, c * c = 1 → ∀ {h : G}, h ∈ zpowers c → h = 1 ∨ h = c := by
      intro c hc h hh
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hh
      rw [zpow_eq_zpow_emod' k (show c ^ 2 = 1 by rw [sq]; exact hc)]
      rcases Int.emod_two_eq_zero_or_one k with h0 | h1
      · left; rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h0, zpow_zero]
      · right; rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h1, zpow_one]
    rcases hor D.a_mul_a hga with h | h
    · exact h
    · rcases hor hxx hgx with h' | h'
      · exact h'
      · exact absurd (h.symm.trans h') (Ne.symm hxa)
  have hinf2 : (zpowers D.a ⊔ zpowers x) ⊓ zpowers D.b = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨hgU, hgb⟩ := mem_inf.1 hg
    have : g ∈ D.A ⊓ D.B := mem_inf.2 ⟨hU hgU, (zpowers_le.2 D.b_mem_B) hgb⟩
    rwa [D.A_inf_B] at this
  have hcard : Nat.card ↥((zpowers D.a ⊔ zpowers x) ⊔ zpowers D.b) = 8 := by
    rw [card_sup_of_le_normalizer (le_normalizer_of_comm hcUb) hinf2,
      card_sup_of_le_normalizer (le_normalizer_of_comm hcax) hinf1,
      card_zpowers_of_involution D.a_mul_a D.a_ne_one, card_zpowers_of_involution hxx hx1,
      card_zpowers_of_involution D.b_mul_b D.b_ne_one]
  have := hrank _ hEP hEelem
  omega

theorem eq_A_of_card_le_four {P : Subgroup G} (hPT : P ≤ T)
    (hAP : D.A ≤ P) (hnorm : T ≤ normalizer (P : Set G))
    (hrank : ∀ E ≤ P, (∀ x ∈ E, x * x = 1) → Nat.card E ≤ 4) : P = D.A := by
  have hPB := D.inf_B_eq_bot_of_card_le_four hPT hAP hnorm hrank
  have hPT₀ : ∀ y ∈ P, y ∈ D.T₀ → y ∈ D.A := by
    intro y hyP hyT₀
    obtain ⟨u, hu, v, hv, rfl⟩ := D.mem_T₀_iff.1 hyT₀
    have hvP : v ∈ P := by
      have : v = u⁻¹ * (u * v) := by group
      rw [this]
      exact mul_mem (inv_mem (hAP hu)) hyP
    have : v ∈ P ⊓ D.B := mem_inf.2 ⟨hvP, hv⟩
    rw [hPB, mem_bot] at this
    rw [this, mul_one]
    exact hu
  refine le_antisymm (fun x hxP => ?_) hAP
  by_cases hxT₀ : x ∈ D.T₀
  · exact hPT₀ x hxP hxT₀
  exfalso
  have hxT := hPT hxP
  have hxt : x * D.t ∈ D.T₀ := (D.mem_T_iff.1 hxT).resolve_left hxT₀
  obtain ⟨u, hu, v, hv, huv⟩ := D.mem_T₀_iff.1 hxt
  have hx : x = u * v * D.t := by
    rw [← huv, mul_assoc, D.t_mul_t, mul_one]
  have hxB : ∀ w ∈ D.B, x * w = w * x := by
    intro w hw
    have h1 : x * w * x⁻¹ * w⁻¹ ∈ P ⊓ D.B := by
      refine mem_inf.2 ⟨?_, ?_⟩
      · have : w * x⁻¹ * w⁻¹ ∈ P :=
          (mem_normalizer_iff.1 (hnorm (D.B_le_T hw)) _).1 (inv_mem hxP)
        have e : x * w * x⁻¹ * w⁻¹ = x * (w * x⁻¹ * w⁻¹) := by group
        rw [e]
        exact mul_mem hxP this
      · exact mul_mem ((mem_normalizer_iff.1 (D.T_le_normalizer_B hxT) w).1 hw) (inv_mem hw)
    rw [hPB, mem_bot] at h1
    have := congrArg (· * w) h1
    simp only [one_mul] at this
    calc x * w = x * w * x⁻¹ * w⁻¹ * w * x := by group
      _ = w * x := by rw [this]
  have hvt : (v * D.t) ^ 2 = 1 := by
    have hxx : x * x ∈ D.A := by
      refine hPT₀ _ (mul_mem hxP hxP) ?_
      rw [hx]
      have e : u * v * D.t * (u * v * D.t) =
          (u * v) * (D.t * (u * v) * D.t⁻¹) * (D.t * D.t) := by
        group
      rw [e, D.t_mul_t, mul_one]
      exact mul_mem (mul_mem (mem_sup_left hu) (mem_sup_right hv))
        ((mem_normalizer_iff.1 (D.T_le_normalizer_T₀ D.t_mem_T) _).1
          (mul_mem (mem_sup_left hu) (mem_sup_right hv)))
    have hu' : D.t * u * D.t⁻¹ ∈ D.A := D.conj_t_A u hu
    have hv' : D.t * v * D.t⁻¹ ∈ D.B := D.conj_t_B v hv
    have hc : v * (D.t * u * D.t⁻¹) = (D.t * u * D.t⁻¹) * v := (D.A_comm_B _ hu' v hv).symm
    have e : x * x = (u * (D.t * u * D.t⁻¹)) * (v * (D.t * v * D.t⁻¹)) := by
      rw [hx]
      calc u * v * D.t * (u * v * D.t)
          = u * (v * (D.t * u * D.t⁻¹)) * (D.t * v * D.t⁻¹) * (D.t * D.t) := by group
        _ = u * ((D.t * u * D.t⁻¹) * v) * (D.t * v * D.t⁻¹) * (D.t * D.t) := by rw [hc]
        _ = (u * (D.t * u * D.t⁻¹)) * (v * (D.t * v * D.t⁻¹)) := by rw [D.t_mul_t]; group
    have hvv : v * (D.t * v * D.t⁻¹) ∈ D.A ⊓ D.B := by
      refine mem_inf.2 ⟨?_, mul_mem hv hv'⟩
      have : v * (D.t * v * D.t⁻¹) = (u * (D.t * u * D.t⁻¹))⁻¹ * (x * x) := by rw [e]; group
      rw [this]
      exact mul_mem (inv_mem (mul_mem hu hu')) hxx
    rw [D.A_inf_B, mem_bot] at hvv
    rw [sq]
    calc v * D.t * (v * D.t) = v * (D.t * v * D.t⁻¹) * (D.t * D.t) := by group
      _ = 1 := by rw [hvv, D.t_mul_t, one_mul]
  have hvtB : ∀ w ∈ D.B, (v * D.t) * w = w * (v * D.t) := by
    intro w hw
    have h1 := hxB w hw
    rw [hx] at h1
    have huw : u * w = w * u := D.A_comm_B u hu w hw
    have : u * ((v * D.t) * w) = u * (w * (v * D.t)) := by
      calc u * ((v * D.t) * w) = u * v * D.t * w := by group
        _ = w * (u * v * D.t) := h1
        _ = (w * u) * (v * D.t) := by group
        _ = (u * w) * (v * D.t) := by rw [huw]
        _ = u * (w * (v * D.t)) := by group
    exact mul_left_cancel this
  obtain ⟨y, hyB, hy⟩ := D.Bt_conj v hv hvt
  have htB : D.B ≤ D.B ⊓ centralizer ({D.t} : Set G) := by
    intro w hw
    refine mem_inf.2 ⟨hw, mem_centralizer_singleton_iff.2 ?_⟩
    have hw' : y⁻¹ * w * y ∈ D.B := mul_mem (mul_mem (inv_mem hyB) hw) hyB
    have := hvtB _ hw'
    rw [← hy]
    calc w * (y * (v * D.t) * y⁻¹) = y * ((y⁻¹ * w * y) * (v * D.t)) * y⁻¹ := by group
      _ = y * ((v * D.t) * (y⁻¹ * w * y)) * y⁻¹ := by rw [this]
      _ = y * (v * D.t) * y⁻¹ * w := by group
  haveI : Finite ↥(D.B ⊓ centralizer ({D.t} : Set G)) :=
    Nat.finite_of_card_ne_zero (by rw [D.card_CBt]; positivity)
  have hcard := Subgroup.card_le_of_le htB
  rw [D.card_B, D.card_CBt] at hcard
  have := Nat.pow_le_pow_iff_right (by norm_num : 1 < 2) |>.1 hcard
  have := D.three_le_n
  omega

end FooteCore

end CFSG.CGT.Foote81L6
