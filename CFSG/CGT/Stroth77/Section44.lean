module

public import CFSG.CGT.Stroth77.Section43C
public import CFSG.CGT.Stroth77.Section44L6Exit

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.YamadaG23 (HasPSL6Sylow)

variable {G : Type} [Group G] [Finite G]

namespace Stroth44

variable {F : StrothFrame G} {D : Subgroup G} {m : ℕ} {dD : StrothWeakTypeData D (.t201 m)}

theorem one_le (h : F.IsD D dD) : 1 ≤ m := by
  have h1 := Subgroup.card_le_of_le h.A_le
  rw [F.dA.card, dD.card] at h1
  have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
  simp only [StrothTypeIndex.k, Type100.k, Type201.k, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h2
  omega

theorem uv_not_mem (h : F.IsD D dD) : dD.uv ∉ D := fun huv => F.uv_not_mem_centralizer_A (by
  rw [← h.uv_eq, Subgroup.mem_centralizer_iff]
  intro y hy
  exact congrArg Subtype.val (dD.isMulCommutative.is_comm.comm ⟨y, h.A_le hy⟩ ⟨_, huv⟩))

variable (dD) in
theorem u_mul_c : dD.u * (dD.c : G) = (dD.c : G) * dD.u := by
  have h := dD.conj_ofTorus dD.u_mem dD.u_conj Torus.c
  rw [show (StrothTypeIndex.t201 m).action.φu Torus.c = Torus.c from
    (Type201.u_c m).trans (one_zsmul _), ← StrothWeakTypeData.c_eq] at h
  calc dD.u * (dD.c : G) = dD.u * (dD.u⁻¹ * (dD.c : G) * dD.u) := by rw [h]
    _ = (dD.c : G) * dD.u := by group

variable (dD) in
theorem zab_ne_one : (dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1) ≠ 1 := by
  have h := ab_pow_ne_one201 (S := G) dD.e (c := dD.c) (a := dD.a) (b := dD.b)
    (dD.e.apply_symm_apply _) (dD.e.apply_symm_apply _) (dD.e.apply_symm_apply _)
  have hcomm : Commute (dD.a : G) (dD.b : G) :=
    congrArg Subtype.val (dD.isMulCommutative.is_comm.comm dD.a dD.b)
  rwa [hcomm.mul_pow] at h

theorem not_isConj_za {S Du : Subgroup G} {c₁ u e za : G}
    (hL6 : ∀ {v y : G}, IsConj v za → y ∈ S → v ∈ S → y * v = v * y → y * y = 1 → y ≠ 1 →
      y ≠ v → IsConj y (y * v))
    (hza : ¬ IsConj c₁ za) (hz2 : c₁ * c₁ = 1) (hz1 : c₁ ≠ 1) (hc₁S : c₁ ∈ S) (huS : u ∈ S)
    (heS : e ∈ S) (hc₁Du : c₁ ∈ Du) (huDu : u ∈ Du) (heDu : e ∉ Du)
    (hDuc₁ : Du ≤ Subgroup.centralizer {c₁}) (hc₁e : c₁ * e = e * c₁) (hue' : u * e = e * u)
    (huc₁ : u * c₁ = c₁ * u) (hu2 : u * u = 1) (he2 : e * e = 1)
    (hzu : IsConj (c₁ * u) za) (hue_c : IsConj (u * e) (c₁ * u * e))
    (hC11 : ∀ y ∈ S, y * e ∈ Du → y * y = 1 →
      (∃ q ∈ S, q⁻¹ * y * q = c₁ * y) ∨ (∃ q ∈ S, q⁻¹ * y * q = e) ∨
        (∃ q ∈ S, q⁻¹ * y * q = c₁ * e) ∨ (∃ q ∈ S, q⁻¹ * y * q = u * e) ∨
        ∃ q ∈ S, q⁻¹ * y * q = c₁ * u * e) :
    ∀ y ∈ S, y * e ∈ Du → y * y = 1 → ¬ IsConj y za := by
  have hDue : ∀ {d : G}, d ∈ Du → d * e ∉ Du := fun hd hde => heDu (by
    have := Du.mul_mem (Du.inv_mem hd) hde
    rwa [inv_mul_cancel_left] at this)
  have hyDu : ∀ {y : G}, y * e ∈ Du → y ∉ Du := fun hye hy => hDue hy hye
  have hyc₁ : ∀ {y : G}, y * e ∈ Du → y * c₁ = c₁ * y := by
    intro y hy
    have h1' : y * e * c₁ = c₁ * (y * e) := Subgroup.mem_centralizer_singleton_iff.1 (hDuc₁ hy)
    calc y * c₁ = y * e * c₁ * e⁻¹ := by rw [mul_assoc y e c₁, ← hc₁e]; group
      _ = c₁ * (y * e) * e⁻¹ := by rw [h1']
      _ = c₁ * y := by group
  have hueS : u * e ∈ S := S.mul_mem huS heS
  have hue1 : u * e ≠ 1 := fun h' => hDue huDu (by rw [h']; exact Du.one_mem)
  have hc₁uDu : c₁ * u ∈ Du := Du.mul_mem hc₁Du huDu
  have hc₁uS : c₁ * u ∈ S := S.mul_mem hc₁S huS
  have hc₁ue : c₁ * (u * e) = u * e * c₁ :=
    (hyc₁ (y := u * e) (by rw [mul_assoc, he2, mul_one]; exact huDu)).symm
  have hue_not : ¬ IsConj (u * e) za := by
    intro h'
    have hne : c₁ ≠ u * e := fun h'' => hDue huDu (by rw [← h'']; exact hc₁Du)
    have h0 := hL6 h' hc₁S hueS hc₁ue hz2 hz1 hne
    rw [← mul_assoc] at h0
    exact hza (h0.trans (hue_c.symm.trans h'))
  have hc₁ue_not : ¬ IsConj (c₁ * u * e) za := fun h' => hue_not (hue_c.trans h')
  have he1 : e ≠ 1 := fun h' => heDu (by rw [h']; exact Du.one_mem)
  have hec₁u : e * (c₁ * u) = c₁ * u * e := by
    calc e * (c₁ * u) = (e * c₁) * u := by group
      _ = (c₁ * e) * u := by rw [hc₁e]
      _ = c₁ * (e * u) := by group
      _ = c₁ * (u * e) := by rw [hue']
      _ = c₁ * u * e := by group
  have he_not : ¬ IsConj e za := by
    intro h'
    have hne : e ≠ c₁ * u := fun h'' => heDu (by rw [h'']; exact hc₁uDu)
    have h0 := hL6 hzu heS hc₁uS hec₁u he2 he1 hne
    rw [hec₁u] at h0
    exact hc₁ue_not (h0.symm.trans h')
  have hc₁eS : c₁ * e ∈ S := S.mul_mem hc₁S heS
  have hc₁e2 : c₁ * e * (c₁ * e) = 1 := by
    calc c₁ * e * (c₁ * e) = c₁ * (e * c₁) * e := by group
      _ = c₁ * (c₁ * e) * e := by rw [hc₁e]
      _ = (c₁ * c₁) * (e * e) := by group
      _ = 1 := by rw [hz2, he2, one_mul]
  have hc₁e1 : c₁ * e ≠ 1 := fun h' => hDue hc₁Du (by rw [h']; exact Du.one_mem)
  have hc₁ec₁u : c₁ * e * (c₁ * u) = u * e := by
    calc c₁ * e * (c₁ * u) = c₁ * (e * c₁) * u := by group
      _ = c₁ * (c₁ * e) * u := by rw [hc₁e]
      _ = (c₁ * c₁) * (e * u) := by group
      _ = u * e := by rw [hz2, one_mul, hue']
  have hc₁uc₁e : c₁ * u * (c₁ * e) = u * e := by
    calc c₁ * u * (c₁ * e) = c₁ * (u * c₁) * e := by group
      _ = c₁ * (c₁ * u) * e := by rw [huc₁]
      _ = (c₁ * c₁) * (u * e) := by group
      _ = u * e := by rw [hz2, one_mul]
  have hc₁e_not : ¬ IsConj (c₁ * e) za := by
    intro h'
    have hne : c₁ * e ≠ c₁ * u := fun h'' => heDu (by rw [mul_left_cancel h'']; exact huDu)
    have h0 := hL6 hzu hc₁eS hc₁uS (hc₁ec₁u.trans hc₁uc₁e.symm) hc₁e2 hc₁e1 hne
    rw [hc₁ec₁u] at h0
    exact hue_not (h0.symm.trans h')
  intro y hyS hye hy2 hyza
  rcases hC11 y hyS hye hy2 with ⟨q, -, hq⟩ | ⟨q, -, hq⟩ | ⟨q, -, hq⟩ | ⟨q, -, hq⟩ |
    ⟨q, -, hq⟩
  · have hy1 : y ≠ 1 := fun h' => hyDu hye (by rw [h']; exact Du.one_mem)
    have hne : c₁ ≠ y := fun h' => hyDu hye (by rw [← h']; exact hc₁Du)
    have h0 := hL6 hyza hc₁S hyS (hyc₁ hye).symm hz2 hz1 hne
    exact hza (h0.trans ((Stroth42.isConj_of_conj_eq hq).trans hyza))
  · exact he_not ((Stroth42.isConj_of_conj_eq hq).trans hyza)
  · exact hc₁e_not ((Stroth42.isConj_of_conj_eq hq).trans hyza)
  · exact hue_not ((Stroth42.isConj_of_conj_eq hq).trans hyza)
  · exact hc₁ue_not ((Stroth42.isConj_of_conj_eq hq).trans hyza)

end Stroth44

theorem StrothFrame.IsD.isConj_of_t201 {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
    {dD : StrothWeakTypeData D (.t201 m)} (h : F.IsD D dD)
    (hE : ∀ y ∈ Subgroup.closure
      {(dD.a : G) ^ 2 ^ (m + 1), (dD.b : G) ^ 2 ^ (m + 1), dD.uv, dD.t},
      y ≠ 1 → IsConj y ((dD.a : G) ^ 2 ^ (m + 1)))
    (hu : IsConj dD.u ((dD.c : G) ^ 2 ^ (m - 1)))
    (hzu : IsConj ((dD.c : G) ^ 2 ^ (m - 1) * dD.u) ((dD.a : G) ^ 2 ^ (m + 1)))
    (hC2 : ∀ y ∈ (F.S : Subgroup G), y * y = 1 → y ≠ 1 →
      y ≠ (dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1) →
      ∃ q ∈ (F.S : Subgroup G),
        q⁻¹ * y * q = y * ((dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1)))
    (hC2c : ∀ y ∈ (F.S : Subgroup G),
      y * ((dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1)) =
        (dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1) * y)
    (hl : ∃ q ∈ (F.S : Subgroup G), q⁻¹ * ((dD.c : G) ^ 2 ^ (m - 1) * dD.u) * q =
      (dD.c : G) ^ 2 ^ (m - 1) * ((dD.a : G) * (dD.b : G)⁻¹) ^ 2 ^ m * dD.u)
    (hx2 : (dD.c : G) ^ 2 ^ (m - 1) * dD.cab * dD.uv *
      ((dD.c : G) ^ 2 ^ (m - 1) * dD.cab * dD.uv) = 1)
    (hxl : (dD.c : G) ^ 2 ^ (m - 1) * dD.cab * dD.uv *
        ((dD.c : G) ^ 2 ^ (m - 1) * ((dD.a : G) * (dD.b : G)⁻¹) ^ 2 ^ m * dD.u) =
      (dD.c : G) ^ 2 ^ (m - 1) * ((dD.a : G) * (dD.b : G)⁻¹) ^ 2 ^ m * dD.u *
        ((dD.c : G) ^ 2 ^ (m - 1) * dD.cab * dD.uv))
    (hxlu : ∃ q ∈ (F.S : Subgroup G), q⁻¹ * ((dD.c : G) ^ 2 ^ (m - 1) * dD.cab * dD.uv *
      ((dD.c : G) ^ 2 ^ (m - 1) * ((dD.a : G) * (dD.b : G)⁻¹) ^ 2 ^ m * dD.u)) * q = dD.u) :
    IsConj ((dD.c : G) ^ 2 ^ (m - 1) * dD.cab * dD.uv) ((dD.c : G) ^ 2 ^ (m - 1)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm := Stroth44.one_le h
  have hoc : orderOf (dD.c : G) = 2 ^ m := by rw [Stroth42.orderOf_c_coe]; rfl
  obtain ⟨hz2, hz1⟩ := Stroth42.pow_mul_self_eq_one hm hoc
  set c₁ := (dD.c : G) ^ 2 ^ (m - 1) with hc₁
  set za := (dD.a : G) ^ 2 ^ (m + 1) with hza
  set w := za * (dD.b : G) ^ 2 ^ (m + 1) with hw
  set x := c₁ * dD.cab * dD.uv with hx
  set l := c₁ * ((dD.a : G) * (dD.b : G)⁻¹) ^ 2 ^ m * dD.u with hl'
  have hwza : IsConj w za := hE w (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
    (Subgroup.subset_closure (by simp))) (Stroth44.zab_ne_one dD)
  have hDS : D ≤ (F.S : Subgroup G) := h.le_S
  have hc₁D : c₁ ∈ D := D.pow_mem dD.c.2 _
  have hcabD : dD.cab ∈ D := D.mul_mem (D.mul_mem dD.c.2 dD.a.2) dD.b.2
  have huvS : dD.uv ∈ (F.S : Subgroup G) := h.uv_eq ▸ F.uv_mem_S
  have huS : dD.u ∈ (F.S : Subgroup G) := h.u_eq ▸ F.u_mem_S
  have hxS : x ∈ (F.S : Subgroup G) := (F.S : Subgroup G).mul_mem (hDS (D.mul_mem hc₁D hcabD)) huvS
  obtain ⟨q, hqS, hq⟩ := hl
  have hlS : l ∈ (F.S : Subgroup G) := by
    rw [← hq]
    exact (F.S : Subgroup G).mul_mem ((F.S : Subgroup G).mul_mem ((F.S : Subgroup G).inv_mem hqS)
      ((F.S : Subgroup G).mul_mem (hDS hc₁D) huS)) hqS
  have hlw : IsConj l w := ((Stroth42.isConj_of_conj_eq hq).trans hzu).trans hwza.symm
  obtain ⟨q', -, hq'⟩ := hxlu
  have hxlu' : IsConj (x * l) dD.u := (Stroth42.isConj_of_conj_eq hq').symm
  have hu1 : dD.u ≠ 1 := fun h1 => hz1 (isConj_one_right.1 (h1 ▸ hu))
  have hx1 : x ≠ 1 := fun h1 => Stroth44.uv_not_mem h (by
    rw [← mul_eq_one_iff_inv_eq.1 h1]
    exact D.inv_mem (D.mul_mem hc₁D hcabD))
  have hxl1 : x ≠ l := fun h' => hu1 (by rw [← hq', ← h', hx2]; group)
  have hwS : (F.S : Subgroup G) ≤ Subgroup.centralizer {w} := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.2 (hC2c y hy)
  have h6 := Stroth76.isConj_mul_of_isConj_central F.S hwS hC2 hlw hxS hlS hxl hx2 hx1 hxl1
  exact (h6.trans hxlu').trans hu

theorem StrothFrame.IsD.false_of_t201_noE16 {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
    {dD : StrothWeakTypeData D (.t201 m)} (h : F.IsD D dD)
    (hnc : ∃ x ∈ omegaIn 1 F.A, ∃ y ∈ omegaIn 1 F.A,
      orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y)
    (hSD : (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G))
    (hE : ∀ y ∈ Subgroup.closure
      {(dD.a : G) ^ 2 ^ (m + 1), (dD.b : G) ^ 2 ^ (m + 1), dD.uv, dD.t},
      y ≠ 1 → IsConj y ((dD.a : G) ^ 2 ^ (m + 1)))
    (hu : IsConj dD.u ((dD.c : G) ^ 2 ^ (m - 1)))
    (hzu : IsConj ((dD.c : G) ^ 2 ^ (m - 1) * dD.u) ((dD.a : G) ^ 2 ^ (m + 1)))
    (h3 : ∀ y ∈ D, y * y = 1 → y ≠ 1 →
      (∃ p ∈ Subgroup.closure {dD.uv, dD.t, dD.u}, p⁻¹ * y * p = (dD.c : G) ^ 2 ^ (m - 1)) ∨
        ∃ g ∈ dD.L, g⁻¹ * y * g = (dD.a : G) ^ 2 ^ (m + 1))
    (hC2 : ∀ y ∈ (F.S : Subgroup G), y * y = 1 → y ≠ 1 →
      y ≠ (dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1) →
      ∃ q ∈ (F.S : Subgroup G),
        q⁻¹ * y * q = y * ((dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1)))
    (hC2c : ∀ y ∈ (F.S : Subgroup G),
      y * ((dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1)) =
        (dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1) * y)
    (hl : ∃ q ∈ (F.S : Subgroup G), q⁻¹ * ((dD.c : G) ^ 2 ^ (m - 1) * dD.u) * q =
      (dD.c : G) ^ 2 ^ (m - 1) * ((dD.a : G) * (dD.b : G)⁻¹) ^ 2 ^ m * dD.u)
    (hx2 : (dD.c : G) ^ 2 ^ (m - 1) * dD.cab * dD.uv *
      ((dD.c : G) ^ 2 ^ (m - 1) * dD.cab * dD.uv) = 1)
    (hxl : (dD.c : G) ^ 2 ^ (m - 1) * dD.cab * dD.uv *
        ((dD.c : G) ^ 2 ^ (m - 1) * ((dD.a : G) * (dD.b : G)⁻¹) ^ 2 ^ m * dD.u) =
      (dD.c : G) ^ 2 ^ (m - 1) * ((dD.a : G) * (dD.b : G)⁻¹) ^ 2 ^ m * dD.u *
        ((dD.c : G) ^ 2 ^ (m - 1) * dD.cab * dD.uv))
    (hxlu : ∃ q ∈ (F.S : Subgroup G), q⁻¹ * ((dD.c : G) ^ 2 ^ (m - 1) * dD.cab * dD.uv *
      ((dD.c : G) ^ 2 ^ (m - 1) * ((dD.a : G) * (dD.b : G)⁻¹) ^ 2 ^ m * dD.u)) * q = dD.u)
    (hx16 : ∃ E : Subgroup G,
      E ≤ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1) * dD.cab * dD.uv} ∧
        (∀ y ∈ E, y * y = 1) ∧ Nat.card E = 16)
    (h7 : ∀ E : Subgroup G,
      E ≤ (F.S : Subgroup G) ⊓ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} →
        (∀ y ∈ E, y * y = 1) → Nat.card E ≠ 16)
    (h9 : ∀ X : Subgroup G,
      X ≤ (F.S : Subgroup G) ⊓ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} →
        IsMulCommutative X → Nat.card X = Nat.card D → X = D) :
    False := by
  have hm := Stroth44.one_le h
  have hoc : orderOf (dD.c : G) = 2 ^ m := by rw [Stroth42.orderOf_c_coe]; rfl
  obtain ⟨hz2, hz1⟩ := Stroth42.pow_mul_self_eq_one hm hoc
  have hx := h.isConj_of_t201 hE hu hzu hC2 hC2c hl hx2 hxl hxlu
  have hza := h.not_isConj_of_omega hnc h3
  have h3' : ∀ y ∈ D, y * y = 1 → y ≠ 1 → IsConj y ((dD.c : G) ^ 2 ^ (m - 1)) →
      ∃ p ∈ Subgroup.closure {dD.uv, dD.t, dD.u}, p⁻¹ * y * p = (dD.c : G) ^ 2 ^ (m - 1) := by
    intro y hyD hy2 hy1 hyz
    rcases h3 y hyD hy2 hy1 with hp | ⟨g, -, hg⟩
    · exact hp
    · exact absurd (hyz.symm.trans (Stroth42.isConj_of_conj_eq hg).symm) hza
  have hPS : Subgroup.closure {dD.uv, dD.t, dD.u} ≤ (F.S : Subgroup G) := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl)
    exacts [h.uv_eq ▸ F.uv_mem_S, h.t_eq ▸ F.t_mem_S, h.u_eq ▸ F.u_mem_S]
  exact Stroth42.not_isConj_of_e16 F.S dD.isMulCommutative h.le_S hSD hPS
    (D.pow_mem dD.c.2 _) h3' hz2 hz1 h7 h9 hx16 hx

theorem StrothFrame.IsD.false_of_t201_iii {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
    {dD : StrothWeakTypeData D (.t201 m)} (h : F.IsD D dD)
    (hnc : ∃ x ∈ omegaIn 1 F.A, ∃ y ∈ omegaIn 1 F.A,
      orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y)
    {e : G} (heN : e ∈ Subgroup.normalizer (D : Set G)) (he2 : e * e = 1)
    (hec : e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹) (hea : e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹)
    (heb : e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹) (heu : e⁻¹ * dD.u * e = dD.u)
    (hS : (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e)
    (hE : ∀ y ∈ Subgroup.closure
      {(dD.a : G) ^ 2 ^ (m + 1), (dD.b : G) ^ 2 ^ (m + 1), dD.uv, dD.t},
      y ≠ 1 → IsConj y ((dD.a : G) ^ 2 ^ (m + 1)))
    (hu : IsConj dD.u ((dD.c : G) ^ 2 ^ (m - 1)))
    (hzu : IsConj ((dD.c : G) ^ 2 ^ (m - 1) * dD.u) ((dD.a : G) ^ 2 ^ (m + 1)))
    (h1 : (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}).relIndex (F.S : Subgroup G) = 2)
    (h2 : e ∉ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u})
    (h3 : ∀ y ∈ D, y * y = 1 → y ≠ 1 →
      (∃ p ∈ Subgroup.closure {dD.uv, dD.t, dD.u}, p⁻¹ * y * p = (dD.c : G) ^ 2 ^ (m - 1)) ∨
        ∃ g ∈ dD.L, g⁻¹ * y * g = (dD.a : G) ^ 2 ^ (m + 1))
    (hC2 : ∀ y ∈ (F.S : Subgroup G), y * y = 1 → y ≠ 1 →
      y ≠ (dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1) →
      ∃ q ∈ (F.S : Subgroup G),
        q⁻¹ * y * q = y * ((dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1)))
    (hC2c : ∀ y ∈ (F.S : Subgroup G),
      y * ((dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1)) =
        (dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1) * y)
    (hl : ∃ q ∈ (F.S : Subgroup G), q⁻¹ * ((dD.c : G) ^ 2 ^ (m - 1) * dD.u) * q =
      (dD.c : G) ^ 2 ^ (m - 1) * ((dD.a : G) * (dD.b : G)⁻¹) ^ 2 ^ m * dD.u)
    (hx2 : (dD.c : G) ^ 2 ^ (m - 1) * dD.cab * dD.uv *
      ((dD.c : G) ^ 2 ^ (m - 1) * dD.cab * dD.uv) = 1)
    (hxl : (dD.c : G) ^ 2 ^ (m - 1) * dD.cab * dD.uv *
        ((dD.c : G) ^ 2 ^ (m - 1) * ((dD.a : G) * (dD.b : G)⁻¹) ^ 2 ^ m * dD.u) =
      (dD.c : G) ^ 2 ^ (m - 1) * ((dD.a : G) * (dD.b : G)⁻¹) ^ 2 ^ m * dD.u *
        ((dD.c : G) ^ 2 ^ (m - 1) * dD.cab * dD.uv))
    (hxlu : ∃ q ∈ (F.S : Subgroup G), q⁻¹ * ((dD.c : G) ^ 2 ^ (m - 1) * dD.cab * dD.uv *
      ((dD.c : G) ^ 2 ^ (m - 1) * ((dD.a : G) * (dD.b : G)⁻¹) ^ 2 ^ m * dD.u)) * q = dD.u)
    (hC7 : ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}, y * y = 1 → y ≠ 1 →
      IsConj y ((dD.c : G) ^ 2 ^ (m - 1)) ∨ IsConj y ((dD.a : G) ^ 2 ^ (m + 1)) ∨
        IsConj y dD.uv ∨ IsConj y ((dD.c : G) ^ 2 ^ (m - 1) * dD.cab * dD.uv) ∨
        IsConj y dD.u ∨ IsConj y ((dD.c : G) ^ 2 ^ (m - 1) * dD.u))
    (h9 : ∀ X : Subgroup G,
      X ≤ (F.S : Subgroup G) ⊓ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} →
        IsMulCommutative X → Nat.card X = Nat.card D → X = D)
    (hC15 : ∀ y ∈ (F.S : Subgroup G),
      y * (dD.c : G) ^ 2 ^ (m - 1) = (dD.c : G) ^ 2 ^ (m - 1) * y →
        y ∈ D ⊔ Subgroup.zpowers dD.u ∨ y * e ∈ D ⊔ Subgroup.zpowers dD.u)
    (hC11 : ∀ y ∈ (F.S : Subgroup G), y * e ∈ D ⊔ Subgroup.zpowers dD.u → y * y = 1 →
      (∃ q ∈ (F.S : Subgroup G), q⁻¹ * y * q = (dD.c : G) ^ 2 ^ (m - 1) * y) ∨
        (∃ q ∈ (F.S : Subgroup G), q⁻¹ * y * q = e) ∨
        (∃ q ∈ (F.S : Subgroup G), q⁻¹ * y * q = (dD.c : G) ^ 2 ^ (m - 1) * e) ∨
        (∃ q ∈ (F.S : Subgroup G), q⁻¹ * y * q = dD.u * e) ∨
        ∃ q ∈ (F.S : Subgroup G), q⁻¹ * y * q = (dD.c : G) ^ 2 ^ (m - 1) * dD.u * e)
    (hue : (∃ q ∈ (F.S : Subgroup G),
        q⁻¹ * (dD.u * e) * q = (dD.c : G) ^ 2 ^ (m - 1) * dD.u * e) ∨
      ∃ v ∈ (F.S : Subgroup G), (∃ q ∈ (F.S : Subgroup G), q⁻¹ * v * q = dD.uv) ∧
        v * (dD.u * e) = dD.u * e * v ∧
        ∃ q ∈ (F.S : Subgroup G), q⁻¹ * (dD.u * e * v) * q = (dD.c : G) ^ 2 ^ (m - 1) * dD.u * e)
    (hC13 : ∀ E : Subgroup G, E ≤ D ⊔ Subgroup.zpowers dD.u → (∀ y ∈ E, y * y = 1) →
      Nat.card E = 8 → (dD.c : G) ^ 2 ^ (m - 1) ∈ E)
    (hF : Subgroup.closure {(dD.a : G) ^ 2 ^ (m + 1), (dD.b : G) ^ 2 ^ (m + 1), dD.uv} ≤
        Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1) * dD.a * dD.b * e} ∧
      (∀ y ∈ Subgroup.closure {(dD.a : G) ^ 2 ^ (m + 1), (dD.b : G) ^ 2 ^ (m + 1), dD.uv},
        y * y = 1) ∧
      Nat.card (Subgroup.closure
        {(dD.a : G) ^ 2 ^ (m + 1), (dD.b : G) ^ 2 ^ (m + 1), dD.uv}) = 8) :
    False := by
  classical
  haveI := F.simple
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnonab := Stroth42.frame_exists_mul_ne F
  have hm := Stroth44.one_le h
  have hx := h.isConj_of_t201 hE hu hzu hC2 hC2c hl hx2 hxl hxlu
  have hoc : orderOf (dD.c : G) = 2 ^ m := by rw [Stroth42.orderOf_c_coe]; rfl
  obtain ⟨hz2, hz1⟩ := Stroth42.pow_mul_self_eq_one hm hoc
  have hza := h.not_isConj_of_omega hnc h3
  set P := Subgroup.closure {dD.uv, dD.t, dD.u} with hP
  set U := D ⊔ P with hU
  set Du := D ⊔ Subgroup.zpowers dD.u with hDu
  set c₁ := (dD.c : G) ^ 2 ^ (m - 1) with hc₁
  set za := (dD.a : G) ^ 2 ^ (m + 1) with hza'
  set w := za * (dD.b : G) ^ 2 ^ (m + 1) with hw
  have hcD : (dD.c : G) ∈ D := dD.c.2
  have hc₁D : c₁ ∈ D := D.pow_mem hcD _
  have hDS : D ≤ (F.S : Subgroup G) := h.le_S
  have hPN : P ≤ Subgroup.normalizer (D : Set G) := by
    rw [hP, Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl)
    exacts [dD.uv_mem, dD.t_mem, dD.u_mem]
  have hSD : (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) := by
    rw [hS]
    exact sup_le (sup_le Subgroup.le_normalizer hPN) ((Subgroup.zpowers_le).2 heN)
  have hUS : U ≤ (F.S : Subgroup G) := by rw [hS]; exact le_sup_left
  have hPS : P ≤ (F.S : Subgroup G) := le_sup_right.trans hUS
  have heS : e ∈ (F.S : Subgroup G) := by
    rw [hS]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers e)
  have huP : dD.u ∈ P := Subgroup.subset_closure (by simp)
  have huS : dD.u ∈ (F.S : Subgroup G) := hPS huP
  have huDu : dD.u ∈ Du := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hDuU : Du ≤ U := sup_le le_sup_left ((Subgroup.zpowers_le).2 (Subgroup.mem_sup_right huP))
  have heDu : e ∉ Du := fun h' => h2 (hDuU h')
  have hDue : ∀ {d : G}, d ∈ Du → d * e ∉ Du := fun hd hde => heDu (by
    have := Du.mul_mem (Du.inv_mem hd) hde
    rwa [inv_mul_cancel_left] at this)
  have hc₁S : c₁ ∈ (F.S : Subgroup G) := hDS hc₁D
  have hc₁Du : c₁ ∈ Du := Subgroup.mem_sup_left hc₁D
  have h3' : ∀ y ∈ D, y * y = 1 → y ≠ 1 → IsConj y c₁ → ∃ p ∈ P, p⁻¹ * y * p = c₁ := by
    intro y hyD hy2 hy1 hyz
    rcases h3 y hyD hy2 hy1 with hp | ⟨g, -, hg⟩
    · exact hp
    · exact absurd (hyz.symm.trans (Stroth42.isConj_of_conj_eq hg).symm) hza
  have hsyl : ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ Subgroup.centralizer {c₁} →
      ∃ k ∈ Subgroup.centralizer {c₁}, ∀ q ∈ Q, k⁻¹ * q * k ∈ (F.S : Subgroup G) :=
    fun Q hQ hQz => Stroth42.exists_conj_le_centralizer F.S dD.isMulCommutative hDS hSD hPS hc₁D
      h3' hz2 hz1 h9 hQ hQz
  have hwza : IsConj w za := hE w (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
    (Subgroup.subset_closure (by simp))) (Stroth44.zab_ne_one dD)
  have huv1 : dD.uv ≠ 1 := fun h1 => Stroth44.uv_not_mem h (h1 ▸ D.one_mem)
  have huvza : IsConj dD.uv za := hE _ (Subgroup.subset_closure (by simp)) huv1
  have hwS : (F.S : Subgroup G) ≤ Subgroup.centralizer {w} := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.2 (hC2c y hy)
  have hL6 : ∀ {v y : G}, IsConj v za → y ∈ (F.S : Subgroup G) → v ∈ (F.S : Subgroup G) →
      y * v = v * y → y * y = 1 → y ≠ 1 → y ≠ v → IsConj y (y * v) :=
    fun hv hy hvS hyv hy2 hy1 hne =>
      Stroth76.isConj_mul_of_isConj_central F.S hwS hC2 (hv.trans hwza.symm) hy hvS hyv hy2 hy1
        hne
  have hUcls : ∀ y ∈ U, y * y = 1 → y ≠ 1 → IsConj y c₁ ∨ IsConj y za := by
    intro y hyU hy2 hy1
    rcases hC7 y hyU hy2 hy1 with h' | h' | h' | h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr h'
    · exact Or.inr (h'.trans huvza)
    · exact Or.inl (h'.trans hx)
    · exact Or.inl (h'.trans hu)
    · exact Or.inr (h'.trans hzu)
  have hThom : ∀ y ∈ (F.S : Subgroup G), y ∉ U → orderOf y = 2 →
      IsConj y c₁ ∨ IsConj y za := by
    intro y hyS hyU hyo
    obtain ⟨g, hg⟩ := EvenSporadicStandard.exists_conj_mem_complement hnonab F.S.isPGroup'
      F.S.not_dvd_index hUS h1 hyS hyU hyo
    have hy2 : y * y = 1 := by rw [← sq, ← hyo]; exact pow_orderOf_eq_one y
    have hy1 : y ≠ 1 := by rintro rfl; rw [orderOf_one] at hyo; omega
    have hg2 : g⁻¹ * y * g * (g⁻¹ * y * g) = 1 := by
      calc g⁻¹ * y * g * (g⁻¹ * y * g) = g⁻¹ * (y * y) * g := by group
        _ = 1 := by rw [hy2]; group
    have hg1 : g⁻¹ * y * g ≠ 1 := fun h' => hy1 (by
      calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
        _ = 1 := by rw [h']; group)
    have hyg : IsConj y (g⁻¹ * y * g) := (Stroth42.isConj_of_conj_eq rfl).symm
    rcases hUcls _ hg hg2 hg1 with h' | h'
    · exact Or.inl (hyg.trans h')
    · exact Or.inr (hyg.trans h')
  have huc : dD.u * (dD.c : G) = (dD.c : G) * dD.u := Stroth44.u_mul_c dD
  have hue' : dD.u * e = e * dD.u := by
    calc dD.u * e = e * (e⁻¹ * dD.u * e) := by group
      _ = e * dD.u := by rw [heu]
  have hcpow : ∀ k : ℕ, e⁻¹ * (dD.c : G) ^ k * e = ((dD.c : G) ^ k)⁻¹ := fun k => by
    rw [← Stroth42.conj_pow', hec, inv_pow]
  have hc₁inv : e⁻¹ * c₁ * e = c₁ := by rw [hc₁, hcpow, inv_eq_of_mul_eq_one_right hz2]
  have hc₁e : c₁ * e = e * c₁ := by
    calc c₁ * e = e * (e⁻¹ * c₁ * e) := by group
      _ = e * c₁ := by rw [hc₁inv]
  have huc₁ : dD.u * c₁ = c₁ * dD.u := (Commute.pow_right huc _).eq
  have hDc₁ : D ≤ Subgroup.centralizer {c₁} := fun d hd =>
    Subgroup.mem_centralizer_singleton_iff.2
      (congrArg Subtype.val (dD.isMulCommutative.is_comm.comm ⟨d, hd⟩ ⟨c₁, hc₁D⟩))
  have hDuc₁ : Du ≤ Subgroup.centralizer {c₁} :=
    sup_le hDc₁ ((Subgroup.zpowers_le).2 (Subgroup.mem_centralizer_singleton_iff.2 huc₁))
  have hyU : ∀ {y : G}, y * e ∈ Du → y ∉ U := fun hy hyU => h2 (by
    have := U.mul_mem (U.inv_mem hyU) (hDuU hy)
    rwa [inv_mul_cancel_left] at this)
  have hu2 : dD.u * dD.u = 1 := dD.u_sq
  have hueS : dD.u * e ∈ (F.S : Subgroup G) := (F.S : Subgroup G).mul_mem huS heS
  have hue2 : dD.u * e * (dD.u * e) = 1 := by
    calc dD.u * e * (dD.u * e) = dD.u * (e * dD.u) * e := by group
      _ = dD.u * (dD.u * e) * e := by rw [hue']
      _ = (dD.u * dD.u) * (e * e) := by group
      _ = 1 := by rw [hu2, he2, one_mul]
  have hue1 : dD.u * e ≠ 1 := fun h' => hDue huDu (by rw [h']; exact Du.one_mem)
  have hc₁ue1 : c₁ * dD.u * e ≠ 1 := fun h' =>
    hDue (Du.mul_mem hc₁Du huDu) (by rw [h']; exact Du.one_mem)
  have hue_c : IsConj (dD.u * e) (c₁ * dD.u * e) := by
    rcases hue with ⟨q, -, hq⟩ | ⟨v, hvS, ⟨q, -, hq⟩, hvue, q', -, hq'⟩
    · exact (Stroth42.isConj_of_conj_eq hq).symm
    · have hvza : IsConj v za := (Stroth42.isConj_of_conj_eq hq).symm.trans huvza
      have hne : dD.u * e ≠ v := by
        intro h'
        apply hc₁ue1
        rw [← hq', ← h', hue2]; group
      exact (hL6 hvza hueS hvS hvue.symm hue2 hue1 hne).trans
        (Stroth42.isConj_of_conj_eq hq').symm
  have hK := Stroth44.not_isConj_za hL6 hza hz2 hz1 hc₁S huS heS hc₁Du huDu heDu hDuc₁ hc₁e hue'
    huc₁ hu2 he2 hzu hue_c hC11
  have hinDu : ∀ y ∈ (F.S : Subgroup G), y * c₁ = c₁ * y → y * y = 1 → IsConj y za →
      y ∈ Du := by
    intro y hyS hyc hy2 hyza
    rcases hC15 y hyS hyc with h' | h'
    · exact h'
    · exact absurd hyza (hK y hyS h' hy2)
  have habD : c₁ * dD.a * dD.b ∈ D := D.mul_mem (D.mul_mem hc₁D dD.a.2) dD.b.2
  have hy₀e : c₁ * dD.a * dD.b * e * e ∈ Du := by
    rw [mul_assoc _ e e, he2, mul_one]; exact Subgroup.mem_sup_left habD
  have hy₀S : c₁ * dD.a * dD.b * e ∈ (F.S : Subgroup G) :=
    (F.S : Subgroup G).mul_mem (hDS habD) heS
  have hcommD : ∀ {x y : G}, x ∈ D → y ∈ D → x * y = y * x := fun hx hy =>
    congrArg Subtype.val (dD.isMulCommutative.is_comm.comm ⟨_, hx⟩ ⟨_, hy⟩)
  have hy₀2 : c₁ * dD.a * dD.b * e * (c₁ * dD.a * dD.b * e) = 1 := by
    have hconj : e⁻¹ * (c₁ * dD.a * dD.b) * e = c₁ * (dD.a : G)⁻¹ * (dD.b : G)⁻¹ := by
      calc e⁻¹ * (c₁ * dD.a * dD.b) * e
          = (e⁻¹ * c₁ * e) * (e⁻¹ * dD.a * e) * (e⁻¹ * dD.b * e) := by group
        _ = c₁ * (dD.a : G)⁻¹ * (dD.b : G)⁻¹ := by rw [hc₁inv, hea, heb]
    have he' : e⁻¹ = e := inv_eq_of_mul_eq_one_right he2
    have hab : (dD.a : G) * dD.b = dD.b * dD.a := hcommD dD.a.2 dD.b.2
    have hac : (dD.a : G) * c₁ = c₁ * dD.a := hcommD dD.a.2 hc₁D
    have hbc : (dD.b : G) * c₁ = c₁ * dD.b := hcommD dD.b.2 hc₁D
    calc c₁ * dD.a * dD.b * e * (c₁ * dD.a * dD.b * e)
        = c₁ * dD.a * dD.b * (e⁻¹ * (c₁ * dD.a * dD.b) * e) := by rw [he']; group
      _ = c₁ * dD.a * dD.b * (c₁ * (dD.a : G)⁻¹ * (dD.b : G)⁻¹) := by rw [hconj]
      _ = c₁ * dD.a * (dD.b * c₁) * (dD.a : G)⁻¹ * (dD.b : G)⁻¹ := by group
      _ = c₁ * (dD.a * c₁) * dD.b * (dD.a : G)⁻¹ * (dD.b : G)⁻¹ := by rw [hbc]; group
      _ = c₁ * c₁ * (dD.a * dD.b) * (dD.a : G)⁻¹ * (dD.b : G)⁻¹ := by rw [hac]; group
      _ = c₁ * c₁ * (dD.b * dD.a) * (dD.a : G)⁻¹ * (dD.b : G)⁻¹ := by rw [hab]
      _ = c₁ * c₁ := by group
      _ = 1 := hz2
  have hy₀1 : c₁ * dD.a * dD.b * e ≠ 1 := fun h' => hyU hy₀e (by rw [h']; exact U.one_mem)
  have hy₀o : orderOf (c₁ * dD.a * dD.b * e) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hy₀2) hy₀1
  have hy₀c₁ : IsConj (c₁ * dD.a * dD.b * e) c₁ := by
    rcases hThom _ hy₀S (hyU hy₀e) hy₀o with h' | h'
    · exact h'
    · exact absurd h' (hK _ hy₀S hy₀e hy₀2)
  have hFE : Subgroup.closure {za, (dD.b : G) ^ 2 ^ (m + 1), dD.uv} ≤
      Subgroup.closure {za, (dD.b : G) ^ 2 ^ (m + 1), dD.uv, dD.t} :=
    Subgroup.closure_mono (by
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
      tauto)
  exact Stroth43C.not_isConj_of_e8 hsyl hinDu hza hz1 hF.1 hF.2.1 hF.2.2
    (fun y hy hy1 => hE y (hFE hy) hy1) hC13 hy₀c₁

theorem StrothFrame.IsD.stroth_4_4 {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
    {dD : StrothWeakTypeData D (.t201 m)} (h : F.IsD D dD)
    (hSR : (F.S : Subgroup G) = (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) ⊔
        Subgroup.closure {dD.uv, dD.t, dD.u})
    (h34b : (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ∨
      ∃ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
        (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ⊔ Subgroup.zpowers e ∧
        e⁻¹ * dD.uv * e = dD.cab ^ 2 * dD.uv ∧ e⁻¹ * dD.t * e = (dD.a : G)⁻¹ ^ 2 * dD.t ∧
        e⁻¹ * dD.u * e = dD.u ∧
        ((e⁻¹ * (dD.c : G) * e = dD.c ∧
            e⁻¹ * (dD.a : G) * e = dD.a * (dD.a : G) ^ 2 ^ (m + 1) ∧
            e⁻¹ * (dD.b : G) * e = dD.b * (dD.b : G) ^ 2 ^ (m + 1) ∧ e * e = (dD.c : G)⁻¹) ∨
          (e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹ ∧ e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹ ∧
            e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹ ∧ e * e = 1) ∨
          (e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹ ∧
            e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹ * (dD.a : G) ^ 2 ^ (m + 1) ∧
            e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹ * (dD.b : G) ^ 2 ^ (m + 1) ∧ e * e = 1)))
    (hA : (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} → False)
    (hii : ∀ e, e ∈ Subgroup.normalizer (D : Set G) →
      (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e →
      e⁻¹ * dD.uv * e = dD.cab ^ 2 * dD.uv → e⁻¹ * dD.t * e = (dD.a : G)⁻¹ ^ 2 * dD.t →
      e⁻¹ * dD.u * e = dD.u → e⁻¹ * (dD.c : G) * e = dD.c →
      e⁻¹ * (dD.a : G) * e = dD.a * (dD.a : G) ^ 2 ^ (m + 1) →
      e⁻¹ * (dD.b : G) * e = dD.b * (dD.b : G) ^ 2 ^ (m + 1) → e * e = (dD.c : G)⁻¹ → False)
    (hiii : ∀ e, e ∈ Subgroup.normalizer (D : Set G) →
      (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e →
      e⁻¹ * dD.uv * e = dD.cab ^ 2 * dD.uv → e⁻¹ * dD.t * e = (dD.a : G)⁻¹ ^ 2 * dD.t →
      e⁻¹ * dD.u * e = dD.u → e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹ →
      e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹ → e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹ →
      e * e = 1 → False) :
    ∃ e ∈ (F.S : Subgroup G),
      (F.S : Subgroup G) = D ⊔ Subgroup.closure {F.dA.uv, F.dA.t, F.dA.u, e} ∧
      e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹ ∧
      e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹ * (dD.a : G) ^ 2 ^ (m + 1) ∧
      e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹ * (dD.b : G) ^ 2 ^ (m + 1) ∧ e * e = 1 ∧
      e⁻¹ * dD.uv * e = dD.cab ^ 2 * dD.uv ∧ e⁻¹ * dD.t * e = (dD.a : G)⁻¹ ^ 2 * dD.t ∧
      e⁻¹ * dD.u * e = dD.u := by
  rcases h34b with hR | ⟨e, heR, hRe, huv, ht, hu, hcases⟩
  · rw [hR] at hSR
    exact (hA hSR).elim
  · have heN : e ∈ Subgroup.normalizer (D : Set G) := heR.1.2
    have hS' : (F.S : Subgroup G) =
        D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e := by
      rw [hSR, hRe, sup_right_comm]
    rcases hcases with ⟨hc, ha, hb, he⟩ | ⟨hc, ha, hb, he⟩ | ⟨hc, ha, hb, he⟩
    · exact (hii e heN hS' huv ht hu hc ha hb he).elim
    · exact (hiii e heN hS' huv ht hu hc ha hb he).elim
    · refine ⟨e, heR.1.1, ?_, hc, ha, hb, he, huv, ht, hu⟩
      have hset : ({F.dA.uv, F.dA.t, F.dA.u, e} : Set G) = {F.dA.uv, F.dA.t, F.dA.u} ∪ {e} := by
        ext y
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
        tauto
      rw [hS', hset, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure, ← h.uv_eq, ← h.t_eq,
        ← h.u_eq, sup_assoc]

theorem StrothFrame.IsD.hasPSL6Sylow_of_stroth_4_4 {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
    {dD : StrothWeakTypeData D (.t201 m)} (h : F.IsD D dD)
    (hSR : (F.S : Subgroup G) = (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) ⊔
        Subgroup.closure {dD.uv, dD.t, dD.u})
    (h34b : (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ∨
      ∃ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
        (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ⊔ Subgroup.zpowers e ∧
        e⁻¹ * dD.uv * e = dD.cab ^ 2 * dD.uv ∧ e⁻¹ * dD.t * e = (dD.a : G)⁻¹ ^ 2 * dD.t ∧
        e⁻¹ * dD.u * e = dD.u ∧
        ((e⁻¹ * (dD.c : G) * e = dD.c ∧
            e⁻¹ * (dD.a : G) * e = dD.a * (dD.a : G) ^ 2 ^ (m + 1) ∧
            e⁻¹ * (dD.b : G) * e = dD.b * (dD.b : G) ^ 2 ^ (m + 1) ∧ e * e = (dD.c : G)⁻¹) ∨
          (e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹ ∧ e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹ ∧
            e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹ ∧ e * e = 1) ∨
          (e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹ ∧
            e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹ * (dD.a : G) ^ 2 ^ (m + 1) ∧
            e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹ * (dD.b : G) ^ 2 ^ (m + 1) ∧ e * e = 1)))
    (hA : (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} → False)
    (hii : ∀ e, e ∈ Subgroup.normalizer (D : Set G) →
      (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e →
      e⁻¹ * dD.uv * e = dD.cab ^ 2 * dD.uv → e⁻¹ * dD.t * e = (dD.a : G)⁻¹ ^ 2 * dD.t →
      e⁻¹ * dD.u * e = dD.u → e⁻¹ * (dD.c : G) * e = dD.c →
      e⁻¹ * (dD.a : G) * e = dD.a * (dD.a : G) ^ 2 ^ (m + 1) →
      e⁻¹ * (dD.b : G) * e = dD.b * (dD.b : G) ^ 2 ^ (m + 1) → e * e = (dD.c : G)⁻¹ → False)
    (hiii : ∀ e, e ∈ Subgroup.normalizer (D : Set G) →
      (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e →
      e⁻¹ * dD.uv * e = dD.cab ^ 2 * dD.uv → e⁻¹ * dD.t * e = (dD.a : G)⁻¹ ^ 2 * dD.t →
      e⁻¹ * dD.u * e = dD.u → e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹ →
      e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹ → e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹ →
      e * e = 1 → False) :
    HasPSL6Sylow G := by
  obtain ⟨e, -, hS, hc, ha, hb, he, huv, ht, hu⟩ := h.stroth_4_4 hSR h34b hA hii hiii
  exact h.hasPSL6Sylow_of_stroth44 hc ha hb he huv ht hu hS

end CFSG.CGT.Stroth77
