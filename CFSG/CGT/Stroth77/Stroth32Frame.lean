module

public import CFSG.CGT.Stroth76.FrameLemma7
public import CFSG.CGT.Stroth77.Sections34AssemblyAux
public import CFSG.CGT.Stroth77.Stroth32Assembly
public import CFSG.CGT.Stroth77.Stroth32Rho

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsSylowIn)

variable {G : Type} [Group G] [Finite G]

theorem StrothFrame.IsD.t100_hfus_of_two_le {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
    {dD : StrothWeakTypeData D (.t100 m)} (h : F.IsD D dD) (hm : 2 ≤ m)
    (hncD : ∃ x ∈ omegaIn 1 D, orderOf x = 2 ∧ ∃ y ∈ omegaIn 1 D, orderOf y = 2 ∧
      ¬ IsConj x y) :
    ∀ g : G, g⁻¹ * dD.u * g ≠ (dD.c : G) ^ 2 ^ (m - 1) * dD.u := by
  intro g hg
  obtain ⟨-, hu, hzu⟩ := h.t100_fusion hm
  have hca : IsConj ((dD.c : G) ^ 2 ^ (m - 1)) ((dD.a : G) ^ 2 ^ m) :=
    hu.symm.trans ((isConj_iff.2 ⟨g⁻¹, by rw [inv_inv]; exact hg⟩).trans hzu)
  have hnc : ∃ x ∈ omegaIn 1 F.A, ∃ y ∈ omegaIn 1 F.A,
      orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y := by
    obtain ⟨x, hx, hox, y, hy, hoy, hxy⟩ := hncD
    rw [h.omegaIn_one_eq] at hx hy
    exact ⟨x, hx, y, hy, hox, hoy, hxy⟩
  obtain ⟨hfusE, -, -, -, -, -⟩ := Stroth76.frame_fusion F
  obtain ⟨hc₁, ha₁, -⟩ := h.t100_omega_eq (by omega)
  have hx2 : F.dA.toConfig.x ^ 2 = (dD.a : G) ^ 2 ^ m := by
    rw [StrothWeakTypeData.toConfig_x, inv_pow, ← ha₁]
    exact inv_eq_of_mul_eq_one_right (Stroth43Fus.t100_a₁_mul_self dD (by omega))
  have hx2E : F.dA.toConfig.x ^ 2 ∈ Subgroup.closure {F.dA.toConfig.x ^ 2,
      F.dA.toConfig.y ^ 2, F.dA.toConfig.uv, F.dA.toConfig.t} :=
    Subgroup.subset_closure (by simp)
  have hx21 : F.dA.toConfig.x ^ 2 ≠ 1 := by
    rw [hx2]; exact Stroth43Fus.t100_a₁_ne_one dD (by omega)
  have hxy := hfusE _ hx2E hx21
  rw [hx2] at hxy
  apply F.not_isConj_w_xy_sq hnc
  rw [StrothWeakTypeData.toConfig_w, ← hc₁]
  exact hca.trans hxy

theorem StrothFrame.IsD.t100_false_of_le_one {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
    {dD : StrothWeakTypeData D (.t100 m)} (h : F.IsD D dD) (hm : m ≤ 1)
    (hncD : ∃ x ∈ omegaIn 1 D, orderOf x = 2 ∧ ∃ y ∈ omegaIn 1 D, orderOf y = 2 ∧
      ¬ IsConj x y) : False := by
  have hk := h.five_le_k_sum
  simp only [StrothTypeIndex.k, Type100.k, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hk
  have hcard : Nat.card D ≤ 32 := by
    rw [dD.card]
    simp only [StrothTypeIndex.k, Type100.k, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    calc 2 ^ (m + (m + 1) + (m + 1)) ≤ 2 ^ 5 :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 32 := by norm_num
  have hDA : F.A = D :=
    Subgroup.eq_of_le_of_card_ge h.A_le (by rw [F.dA.card_eq_32]; exact hcard)
  have hnc : ∃ x ∈ omegaIn 1 F.A, ∃ y ∈ omegaIn 1 F.A,
      orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y := by
    obtain ⟨x, hx, hox, y, hy, hoy, hxy⟩ := hncD
    rw [h.omegaIn_one_eq] at hx hy
    exact ⟨x, hx, y, hy, hox, hoy, hxy⟩
  apply Stroth76.frame_centralizer_inf_ne_A F (F.not_isConj_w_xy_sq hnc)
  rw [inf_comm, hDA]
  exact h.cent

theorem StrothFrame.IsD.t100_two_le {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
    {dD : StrothWeakTypeData D (.t100 m)} (h : F.IsD D dD)
    (hncD : ∃ x ∈ omegaIn 1 D, orderOf x = 2 ∧ ∃ y ∈ omegaIn 1 D, orderOf y = 2 ∧
      ¬ IsConj x y) : 2 ≤ m := by
  by_contra hm
  exact h.t100_false_of_le_one (by omega) hncD

theorem stroth_3_2_hfus100 :
    ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) {D : Subgroup G} {m : ℕ}
      (dD : StrothWeakTypeData D (.t100 m)), F.IsD D dD →
      (∃ x ∈ omegaIn 1 D, orderOf x = 2 ∧ ∃ y ∈ omegaIn 1 D, orderOf y = 2 ∧
        ¬ IsConj x y) →
      ∀ g : G, g⁻¹ * dD.u * g ≠ (dD.c : G) ^ 2 ^ (m - 1) * dD.u := by
  intro G _ _ F D m dD h hncD
  by_cases hm : 2 ≤ m
  · exact h.t100_hfus_of_two_le hm hncD
  · exact (h.t100_false_of_le_one (by omega) hncD).elim

theorem stroth_3_2_frame_of_fus100
    (h227 : ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) (D : Subgroup G)
      (τ : StrothTypeIndex) (dD : StrothWeakTypeData D τ), F.IsD D dD →
      (∀ x : G, x ∈ omegaIn 1 D → orderOf x = 2 →
        ∀ y : G, y ∈ omegaIn 1 D → orderOf y = 2 → ∃ g : G, y = g * x * g⁻¹) → τ.m = τ.n)
    (hfus100 : ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) {D : Subgroup G} {m : ℕ}
      (dD : StrothWeakTypeData D (.t100 m)), F.IsD D dD →
      (∃ x ∈ omegaIn 1 D, orderOf x = 2 ∧ ∃ y ∈ omegaIn 1 D, orderOf y = 2 ∧
        ¬ IsConj x y) →
      ∀ g : G, g⁻¹ * dD.u * g ≠ (dD.c : G) ^ 2 ^ (m - 1) * dD.u) :
    ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) (D : Subgroup G)
      (τ : StrothTypeIndex) (dD : StrothWeakTypeData D τ), F.IsD D dD →
      IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
      ∀ m, τ = .t100 m → (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ∨
      ∃ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
        (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ⊔ Subgroup.zpowers e ∧
        e⁻¹ * dD.uv * e = (dD.c : G) ^ 2 * dD.a * dD.b * dD.uv ∧
        e⁻¹ * dD.t * e = (dD.a : G)⁻¹ * dD.t ∧ e⁻¹ * dD.u * e = dD.u ∧
        ((e⁻¹ * (dD.c : G) * e = dD.c ∧ e⁻¹ * (dD.a : G) * e = dD.a * (dD.a : G) ^ 2 ^ m ∧
            e⁻¹ * (dD.b : G) * e = dD.b * (dD.b : G) ^ 2 ^ m ∧
            e * e = (dD.c : G)⁻¹ * (dD.c : G) ^ 2 ^ (m - 1)) ∨
          (e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹ ∧ e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹ ∧
            e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹ ∧ e * e = 1) ∨
          (e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹ ∧
            e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹ * (dD.a : G) ^ 2 ^ m ∧
            e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹ * (dD.b : G) ^ 2 ^ m ∧
            e * e = (dD.c : G) ^ 2 ^ (m - 1))) := by
  intro G _ _ F D τ dD h hns m hτ
  subst hτ
  have hncD : ∃ x ∈ omegaIn 1 D, orderOf x = 2 ∧ ∃ y ∈ omegaIn 1 D, orderOf y = 2 ∧
      ¬ IsConj x y := by
    by_contra hall
    have hmn := h227 F D _ dD h fun x hx hox y hy hoy => by
      by_contra hxy
      exact hall ⟨x, hx, hox, y, hy, hoy, fun hc => hxy (by
        obtain ⟨g, hg⟩ := isConj_iff.mp hc
        exact ⟨g, hg.symm⟩)⟩
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type100.k] at hmn
  have hm := h.t100_two_le hncD
  have hfus := hfus100 F dD h hncD
  exact h.t100_classify_R (h.setting hns) (by omega) hfus fun e he =>
    h.t100_proj_rho_mul_inv_mem (h.setting hns) hm hfus he

theorem stroth_3_2_frame_of_h227
    (h227 : ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) (D : Subgroup G)
      (τ : StrothTypeIndex) (dD : StrothWeakTypeData D τ), F.IsD D dD →
      (∀ x : G, x ∈ omegaIn 1 D → orderOf x = 2 →
        ∀ y : G, y ∈ omegaIn 1 D → orderOf y = 2 → ∃ g : G, y = g * x * g⁻¹) → τ.m = τ.n) :
    ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) (D : Subgroup G)
      (τ : StrothTypeIndex) (dD : StrothWeakTypeData D τ), F.IsD D dD →
      IsSylowIn 2 (Subgroup.normalizer (D : Set G))
        ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) →
      ∀ m, τ = .t100 m → (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ∨
      ∃ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
        (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ⊔ Subgroup.zpowers e ∧
        e⁻¹ * dD.uv * e = (dD.c : G) ^ 2 * dD.a * dD.b * dD.uv ∧
        e⁻¹ * dD.t * e = (dD.a : G)⁻¹ * dD.t ∧ e⁻¹ * dD.u * e = dD.u ∧
        ((e⁻¹ * (dD.c : G) * e = dD.c ∧ e⁻¹ * (dD.a : G) * e = dD.a * (dD.a : G) ^ 2 ^ m ∧
            e⁻¹ * (dD.b : G) * e = dD.b * (dD.b : G) ^ 2 ^ m ∧
            e * e = (dD.c : G)⁻¹ * (dD.c : G) ^ 2 ^ (m - 1)) ∨
          (e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹ ∧ e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹ ∧
            e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹ ∧ e * e = 1) ∨
          (e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹ ∧
            e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹ * (dD.a : G) ^ 2 ^ m ∧
            e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹ * (dD.b : G) ^ 2 ^ m ∧
            e * e = (dD.c : G) ^ 2 ^ (m - 1))) :=
  stroth_3_2_frame_of_fus100 h227 @stroth_3_2_hfus100

end CFSG.CGT.Stroth77
