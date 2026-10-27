module

public import CFSG.CGT.Stroth77.Stroth31DAFrame
public import CFSG.CGT.Stroth77.Section42Core
public import CFSG.CGT.Stroth76.FrameFusion

public section

namespace CFSG.CGT.Stroth77

open CFSG.CGT.Stroth77.Arch76

section Fusion

variable {G : Type} [Group G] [Finite G]

theorem co_even_of_two_nsmul_eq_zero :
    ∀ v : Co, 2 • v = 0 → v.2.1.val % 2 = 0 ∧ v.2.2.val % 2 = 0 := by
  decide

theorem StrothFrame.isConj_xy_sq_or_isConj_w (F : StrothFrame G) {z : G}
    (hz : z ∈ omegaIn 1 F.A) (hz2 : orderOf z = 2) :
    IsConj z ((F.dA.toConfig.x * F.dA.toConfig.y) ^ 2) ∨ IsConj z F.dA.toConfig.w := by
  set K := F.dA.toConfig with hK
  obtain ⟨h1, -, -, -, h5, -⟩ := Stroth76.frame_fusion F
  rw [← hK] at h1 h5
  have hzA : z ∈ K.A := omegaIn_le 1 F.A hz
  obtain ⟨v, rfl⟩ := K.exists_ev hzA
  have hsq : K.ev (2 • v) = 1 := by rw [K.ev_nsmul, ← hz2, pow_orderOf_eq_one]
  rw [K.ev_eq_one_iff] at hsq
  obtain ⟨hj, hl⟩ := co_even_of_two_nsmul_eq_zero v hsq
  set e := K.x ^ v.2.1.val * K.y ^ v.2.2.val with he
  have heE : e ∈ Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t} := by
    have hx : K.x ^ v.2.1.val = (K.x ^ 2) ^ (v.2.1.val / 2) := by
      rw [← pow_mul, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hj)]
    have hy : K.y ^ v.2.2.val = (K.y ^ 2) ^ (v.2.2.val / 2) := by
      rw [← pow_mul, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hl)]
    rw [he, hx, hy]
    exact mul_mem (pow_mem (Subgroup.subset_closure (by simp)) _)
      (pow_mem (Subgroup.subset_closure (by simp)) _)
  have hev : K.ev v = K.w ^ v.1.val * e := by
    rw [he, Arch76.Config.ev, mul_assoc]
  have hv1 : v.1.val = 0 ∨ v.1.val = 1 := by
    have := ZMod.val_lt v.1
    omega
  rcases hv1 with h0 | h0
  · rw [hev, h0, pow_zero, one_mul] at hz2 ⊢
    refine Or.inl (h1 e heE ?_)
    intro he1
    rw [he1, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  · rw [hev, h0, pow_one] at hz2 ⊢
    exact Or.inr (h5 e heE hz2)

theorem StrothFrame.isConj_of_isConj_w_xy_sq (F : StrothFrame G)
    (hw : IsConj F.dA.toConfig.w ((F.dA.toConfig.x * F.dA.toConfig.y) ^ 2)) :
    ∀ x ∈ omegaIn 1 F.A, ∀ y ∈ omegaIn 1 F.A, orderOf x = 2 → orderOf y = 2 → IsConj x y := by
  have key : ∀ z ∈ omegaIn 1 F.A, orderOf z = 2 →
      IsConj z ((F.dA.toConfig.x * F.dA.toConfig.y) ^ 2) := by
    intro z hz hz2
    rcases F.isConj_xy_sq_or_isConj_w hz hz2 with h | h
    · exact h
    · exact h.trans hw
  intro x hx y hy hx2 hy2
  exact (key x hx hx2).trans (key y hy hy2).symm

theorem StrothFrame.not_isConj_w_xy_sq (F : StrothFrame G)
    (hnc : ∃ x ∈ omegaIn 1 F.A, ∃ y ∈ omegaIn 1 F.A,
      orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y) :
    ¬ IsConj F.dA.toConfig.w ((F.dA.toConfig.x * F.dA.toConfig.y) ^ 2) := by
  intro hw
  obtain ⟨x, hx, y, hy, hx2, hy2, hxy⟩ := hnc
  exact hxy (F.isConj_of_isConj_w_xy_sq hw x hx y hy hx2 hy2)

end Fusion

section Order

theorem StrothWeakTypeData.card_sup_closure_le_eight_mul {G : Type*} [Group G] {D : Subgroup G}
    {τ : StrothTypeIndex} (dD : StrothWeakTypeData D τ) :
    Nat.card (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} : Subgroup G) ≤ 8 * Nat.card D := by
  have h := Stroth42Core.natCard_le_of_subset_range
    (E := D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u})
    (fun p : Torus τ.k × Bool × Bool × Bool => dD.ofTorus p.1 * dD.d8 p.2.1 p.2.2.1 p.2.2.2)
    (fun y hy => by
      obtain ⟨v, i, j, l, rfl⟩ := dD.mem_sup_iff.mp hy
      exact ⟨(v, i, j, l), rfl⟩)
  rw [Nat.card_prod, Nat.card_prod, Nat.card_prod, Nat.card_eq_fintype_card (α := Bool),
    Fintype.card_bool, natCard_torus, ← dD.card] at h
  linarith

variable {G : Type} [Group G] [Finite G]

theorem two_pow_eleven_le_card_sylow (S : Sylow 2 G) (h11 : 2 ^ 11 ∣ Nat.card G) :
    2 ^ 11 ≤ Nat.card (S : Subgroup G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Nat.le_of_dvd Nat.card_pos (S.pow_dvd_card_of_pow_dvd_card h11)

theorem StrothWeakTypeData.three_le_of_t300_of_dvd {D : Subgroup G} {n : ℕ}
    (dD : StrothWeakTypeData D (.t300 n)) (S : Sylow 2 G)
    (hS : (S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u})
    (h11 : 2 ^ 11 ∣ Nat.card G) : 3 ≤ n := by
  have h1 := two_pow_eleven_le_card_sylow S h11
  have h2 := dD.card_sup_closure_le_eight_mul
  rw [← hS, dD.card] at h2
  have hk : (StrothTypeIndex.t300 n).k 0 + (StrothTypeIndex.t300 n).k 1 +
      (StrothTypeIndex.t300 n).k 2 = 3 * n := by
    simp only [StrothTypeIndex.k, Type300.k, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    ring
  rw [hk] at h2
  have h3 : 2 ^ 11 ≤ 2 ^ (3 * n + 3) :=
    calc 2 ^ 11 ≤ Nat.card (S : Subgroup G) := h1
      _ ≤ 8 * 2 ^ (3 * n) := h2
      _ = 2 ^ (3 * n + 3) := by ring
  have h4 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h3
  omega

end Order

section DEqA

variable {G : Type} [Group G] [Finite G]

theorem StrothFrame.card_S_le_of_centralizer_A_eq (F : StrothFrame G)
    (hCA : Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) = F.A) :
    Nat.card (F.S : Subgroup G) ≤ 2 ^ 9 := by
  set T : Subgroup G := F.A ⊔ Subgroup.closure {F.dA.uv, F.dA.t, F.dA.u} with hTdef
  have hcardT : Nat.card T = 256 := F.card_T_eq
  rcases F.arch76Lemma2 hCA with hT | ⟨s, hsS, hSeq, hs2, -, -, -, hrel⟩
  · rw [hT, ← hTdef, hcardT]
    norm_num
  · have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
    have hA_mem : ∀ x ∈ F.A, x ∈ T := fun x hx => Subgroup.mem_sup_left hx
    have hUV_mem : F.dA.uv ∈ T :=
      Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
    have hT_mem : F.dA.t ∈ T :=
      Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
    have hU_mem : F.dA.u ∈ T :=
      Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
    have hsuv : s⁻¹ * F.dA.uv * s ∈ T := by
      rcases hrel with ⟨huv, -, -⟩ | ⟨huv, -, -⟩
      · rw [huv]
        exact T.mul_mem (T.mul_mem (hA_mem _ (inv_mem F.dA.a.2))
          (hA_mem _ (inv_mem F.dA.b.2))) hUV_mem
      · rw [huv]
        exact T.mul_mem (T.mul_mem (hA_mem _ F.dA.a.2)
          (hA_mem _ (inv_mem F.dA.b.2))) hUV_mem
    have hst : s⁻¹ * F.dA.t * s ∈ T := by
      rcases hrel with ⟨-, ht, -⟩ | ⟨-, ht, -⟩
      · rw [ht]; exact T.mul_mem (hA_mem _ F.dA.a.2) hT_mem
      · rw [ht]; exact T.mul_mem (T.mul_mem (hA_mem _ F.dA.a.2)
          (hA_mem _ (pow_mem F.dA.b.2 2))) hT_mem
    have hsu : s⁻¹ * F.dA.u * s ∈ T := by
      rcases hrel with ⟨-, -, hu⟩ | ⟨-, -, hu⟩
      · rw [hu]; exact hU_mem
      · rw [hu]; exact T.mul_mem (hA_mem _ F.dA.c.2) hU_mem
    have hTclosure : T = Subgroup.closure ((F.A : Set G) ∪ {F.dA.uv, F.dA.t, F.dA.u}) := by
      rw [hTdef, Subgroup.closure_union, Subgroup.closure_eq]
    have hsNA : s ∈ Subgroup.normalizer (F.A : Set G) := F.le_normalizer_A hCA hsS
    have hsNT : s ∈ Subgroup.normalizer T := by
      rw [hTclosure]
      have hle : Subgroup.closure ({s} : Set G) ≤
          Subgroup.normalizer (Subgroup.closure
            ((F.A : Set G) ∪ {F.dA.uv, F.dA.t, F.dA.u})) := by
        rw [Subgroup.le_normalizer_closure_iff]
        intro h hh g hg
        rcases closure_singleton_eq_one_or hs2 hh with h1 | h1
        · subst h
          simpa using Subgroup.subset_closure hg
        · subst h
          rcases hg with hg | hg
          · have hmemA : s * g * s⁻¹ ∈ F.A := by
              have := (Subgroup.mem_normalizer_iff.mp hsNA g).mp hg
              simpa [hsinv] using this
            exact Subgroup.subset_closure (Or.inl hmemA)
          · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
            rcases hg with rfl | rfl | rfl
            · rw [show s * F.dA.uv * s⁻¹ = s⁻¹ * F.dA.uv * s by rw [hsinv], ← hTclosure]
              exact hsuv
            · rw [show s * F.dA.t * s⁻¹ = s⁻¹ * F.dA.t * s by rw [hsinv], ← hTclosure]
              exact hst
            · rw [show s * F.dA.u * s⁻¹ = s⁻¹ * F.dA.u * s by rw [hsinv], ← hTclosure]
              exact hsu
      exact hle (Subgroup.subset_closure (Set.mem_singleton s))
    have hTeq : (F.S : Subgroup G) = T ⊔ Subgroup.closure ({s} : Set G) := by
      rw [hSeq, hTdef,
        show ({F.dA.uv, F.dA.t, F.dA.u, s} : Set G) = {F.dA.uv, F.dA.t, F.dA.u} ∪ {s} by
          ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]; tauto,
        Subgroup.closure_union, ← sup_assoc]
    have hcardS := card_sup_closure_singleton_le_mul_two T hs2 hsNT
    rw [← hTeq, hcardT] at hcardS
    calc Nat.card (F.S : Subgroup G) ≤ 2 * 256 := hcardS
      _ = 2 ^ 9 := by norm_num

variable {F : StrothFrame G} {D : Subgroup G} {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}

theorem StrothFrame.IsD.card_D_gt_of_dvd (h : F.IsD D dD) (h11 : 2 ^ 11 ∣ Nat.card G) :
    32 < Nat.card D := by
  by_contra hle
  push Not at hle
  have hDA : F.A = D :=
    Subgroup.eq_of_le_of_card_ge h.A_le (by rw [F.dA.card_eq_32]; exact hle)
  have hCA : Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) = F.A := by
    rw [inf_comm, hDA]; exact h.cent
  have h1 := two_pow_eleven_le_card_sylow F.S h11
  have h2 := F.card_S_le_of_centralizer_A_eq hCA
  have h3 := h1.trans h2
  norm_num at h3

theorem StrothFrame.IsD.five_le_k_sum (h : F.IsD D dD) : 5 ≤ τ.k 0 + τ.k 1 + τ.k 2 := by
  have hle := Subgroup.card_le_of_le h.A_le
  rw [F.dA.card, dD.card] at hle
  have h5 : (StrothTypeIndex.t100 1).k 0 + (StrothTypeIndex.t100 1).k 1 +
      (StrothTypeIndex.t100 1).k 2 = 5 := rfl
  rw [h5] at hle
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle

theorem StrothFrame.IsD.six_le_k_sum_of_dvd (h : F.IsD D dD) (h11 : 2 ^ 11 ∣ Nat.card G) :
    6 ≤ τ.k 0 + τ.k 1 + τ.k 2 := by
  have hgt := h.card_D_gt_of_dvd h11
  rw [dD.card, show (32 : ℕ) = 2 ^ 5 by norm_num] at hgt
  have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hgt
  omega

end DEqA

section Bounds

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}

theorem StrothFrame.IsD.one_le_of_t200 {m : ℕ} {dD : StrothWeakTypeData D (.t200 m)}
    (h : F.IsD D dD) : 1 ≤ m := by
  have := h.five_le_k_sum
  simp only [StrothTypeIndex.k, Type200.k, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at this
  omega

theorem StrothFrame.IsD.one_le_of_t201 {m : ℕ} {dD : StrothWeakTypeData D (.t201 m)}
    (h : F.IsD D dD) : 1 ≤ m := by
  have := h.five_le_k_sum
  simp only [StrothTypeIndex.k, Type201.k, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at this
  omega

theorem StrothFrame.IsD.two_le_of_t100_of_dvd {m : ℕ} {dD : StrothWeakTypeData D (.t100 m)}
    (h : F.IsD D dD) (h11 : 2 ^ 11 ∣ Nat.card G) : 2 ≤ m := by
  have := h.six_le_k_sum_of_dvd h11
  simp only [StrothTypeIndex.k, Type100.k, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at this
  omega

theorem StrothFrame.IsD.one_le_of_t101_of_dvd {s : ℕ} {dD : StrothWeakTypeData D (.t101 s)}
    (h : F.IsD D dD) (h11 : 2 ^ 11 ∣ Nat.card G) : 1 ≤ s := by
  have := h.six_le_k_sum_of_dvd h11
  simp only [StrothTypeIndex.k, Type101.k, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at this
  omega

end Bounds

end CFSG.CGT.Stroth77
