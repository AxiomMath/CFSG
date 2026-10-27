module

public import CFSG.CGT.Foote81L6.TStruct.Normal

public section

namespace CFSG.CGT.Foote81L6

open Subgroup TStruct

namespace FooteCore

variable {G : Type*} [Group G] {T : Subgroup G} {m n : ℕ} (D : FooteCore G T m n)

theorem elemBound_A : ElemBound D.A 4 := by
  obtain ⟨e⟩ := D.A_iso
  haveI : NeZero (2 ^ (m - 1)) := ⟨by positivity⟩
  exact elemBound_of_dihedral e

theorem elemBound_B₀ : ElemBound D.B₀ 4 := by
  obtain ⟨e⟩ := D.B₀_iso
  haveI : NeZero (2 ^ (n - 1)) := ⟨by positivity⟩
  exact elemBound_of_dihedral e

theorem elemBound_B₁ : ElemBound D.B₁ 4 := by
  obtain ⟨e⟩ := D.B₁_iso
  haveI : NeZero (2 ^ (n - 1)) := ⟨by positivity⟩
  exact elemBound_of_dihedral e

theorem elemBound_CBt : ElemBound (D.B ⊓ centralizer {D.t}) 4 := by
  obtain ⟨e⟩ := D.CBt_iso
  exact elemBound_of_semidihedral (by have := D.three_le_n; omega) e

theorem elemBound_CB₀B₁s : ElemBound ((D.B₀ ⊔ D.B₁) ⊓ centralizer {D.s}) 4 := by
  obtain ⟨e⟩ := D.B₀_iso
  haveI : NeZero (2 ^ (n - 1)) := ⟨by positivity⟩
  rw [← D.sDiag_range]
  exact ElemBound.of_le_range D.sDiag D.sDiag_injective (card_le_four_of_mulEquiv_dihedral e)
    le_rfl

theorem elemBound_CTt : ElemBound (T ⊓ centralizer {D.t}) 16 := by
  have h1 : ElemBound ((T ⊓ centralizer {D.t}) ⊓ D.T₀) 8 :=
    ElemBound.index_two (c := D.a) (K := D.B ⊓ centralizer {D.t})
      (fun x hx => D.mem_CBt_or_of_comm_t (mem_inf.1 hx).2
        (mem_centralizer_singleton_iff.1 (mem_inf.1 (mem_inf.1 hx).1).2))
      (D.elemBound_CBt.mono inf_le_right)
  exact ElemBound.index_two (c := D.t) (fun x hx => D.mem_T_iff.1 (mem_inf.1 hx).1) h1

theorem elemBound_CT₀ {a₁ : G} (ha₁ : a₁ ∈ D.A) :
    ElemBound (D.T₀ ⊓ centralizer {a₁ * D.s}) 32 := by
  have hAC : ElemBound (D.A ⊔ ((D.B₀ ⊔ D.B₁) ⊓ centralizer {D.s})) 16 :=
    ElemBound.sup (fun x hx y hy => D.A_comm_B₀B₁ x hx y (mem_inf.1 hy).1)
      (eq_bot_iff.2 ((inf_le_inf_left _ inf_le_left).trans D.A_inf_B₀B₁.le))
      D.elemBound_A D.elemBound_CB₀B₁s
  refine ElemBound.index_two (c := D.s) (K := D.T₁)
    (fun x hx => D.mem_T₁_or_mul_s_mem_T₁ (mem_inf.1 hx).1) (hAC.mono ?_)
  intro x hx
  obtain ⟨hx', hx1⟩ := mem_inf.1 hx
  exact D.mem_A_sup_of_comm hx1 ha₁ (mem_centralizer_singleton_iff.1 (mem_inf.1 hx').2)

theorem le_T₀_of_mul_self {F : Subgroup G} (hFT : F ≤ T) (hF2 : ∀ x ∈ F, x * x = 1)
    (hcard : 16 < Nat.card F) : F ≤ D.T₀ := by
  by_contra hle
  obtain ⟨g, hgF, hg0⟩ := SetLike.not_le_iff_exists.1 hle
  obtain ⟨h, hh, hconj⟩ := D.exists_conj_t (hFT hgF) hg0 (hF2 g hgF)
  have := D.elemBound_CTt.card_le_of_conj hFT hF2 hgF (D.T₀_le_T hh) hconj
  omega

theorem le_T₁_of_mul_self {F : Subgroup G} (hFT : F ≤ T) (hF2 : ∀ x ∈ F, x * x = 1)
    (hcard : 32 < Nat.card F) : F ≤ D.T₁ := by
  have hF0 : F ≤ D.T₀ := D.le_T₀_of_mul_self hFT hF2 (by omega)
  by_contra hle
  obtain ⟨g, hgF, hg1⟩ := SetLike.not_le_iff_exists.1 hle
  obtain ⟨a₁, ha₁, -, u, hu, hconj⟩ := D.exists_conj_mul_s (hF0 hgF) hg1 (hF2 g hgF)
  have := (D.elemBound_CT₀ ha₁).card_le_of_conj hF0 hF2 hgF (D.B_le_T₀ (D.B₀_le_B hu)) hconj
  omega

theorem le_T₁_of_isElemAbelian {F : Subgroup G} (hFT : F ≤ T) (hF : CFSG.Open.IsElemAbelian 2 F)
    (hcard : Nat.card F = 2 ^ 6) : F ≤ D.T₁ :=
  D.le_T₁_of_mul_self hFT (isElemAbelian_two_iff.1 hF) (by rw [hcard]; norm_num)

theorem elem64_of_four {V V₀ V₁ : Subgroup G} (hV : V ≤ D.A) (hV₀ : V₀ ≤ D.B₀)
    (hV₁ : V₁ ≤ D.B₁) (h2 : ∀ x ∈ V, x * x = 1) (h20 : ∀ x ∈ V₀, x * x = 1)
    (h21 : ∀ x ∈ V₁, x * x = 1) (hc : Nat.card V = 4) (hc₀ : Nat.card V₀ = 4)
    (hc₁ : Nat.card V₁ = 4) :
    V ⊔ (V₀ ⊔ V₁) ≤ D.T₁ ∧ (∀ x ∈ V ⊔ (V₀ ⊔ V₁), x * x = 1) ∧
      Nat.card ↥(V ⊔ (V₀ ⊔ V₁)) = 2 ^ 6 := by
  have hc01 : ∀ x ∈ V₀, ∀ y ∈ V₁, x * y = y * x :=
    fun x hx y hy => D.B₀_comm_B₁ x (hV₀ hx) y (hV₁ hy)
  have hcA : ∀ x ∈ V, ∀ y ∈ V₀ ⊔ V₁, x * y = y * x :=
    fun x hx y hy => D.A_comm_B₀B₁ x (hV hx) y (sup_le_sup hV₀ hV₁ hy)
  have hi01 : V₀ ⊓ V₁ = ⊥ := eq_bot_iff.2 ((inf_le_inf hV₀ hV₁).trans D.B₀_inf_B₁.le)
  have hiA : V ⊓ (V₀ ⊔ V₁) = ⊥ :=
    eq_bot_iff.2 ((inf_le_inf hV (sup_le_sup hV₀ hV₁)).trans D.A_inf_B₀B₁.le)
  refine ⟨sup_le_sup hV (sup_le_sup hV₀ hV₁),
    fun x hx => mul_self_of_mem_sup h2 (fun y hy => mul_self_of_mem_sup h20 h21 hc01 hy) hcA hx,
    ?_⟩
  have h : Nat.card ↥(V ⊔ (V₀ ⊔ V₁)) = 4 * (4 * 4) := by
    rw [card_sup_of_le_normalizer (le_normalizer_of_comm hcA) hiA,
      card_sup_of_le_normalizer (le_normalizer_of_comm hc01) hi01, hc, hc₀, hc₁]
  exact h.trans (by norm_num)

theorem T₁_le_of_forall_elem64 {X : Subgroup G}
    (hX : ∀ F : Subgroup G, F ≤ D.T₁ → (∀ x ∈ F, x * x = 1) → Nat.card F = 2 ^ 6 → F ≤ X) :
    D.T₁ ≤ X := by
  obtain ⟨eA⟩ := D.A_iso
  obtain ⟨e₀⟩ := D.B₀_iso
  obtain ⟨e₁⟩ := D.B₁_iso
  have hm : 1 ≤ m - 1 := by have := D.two_le_m; omega
  have hn : 1 ≤ n - 1 := by have := D.three_le_n; omega
  obtain ⟨VA, hVA, hVA2, hVA4, -⟩ := exists_four_of_mulEquiv_dihedral hm eA (one_mem _) (mul_one 1)
  obtain ⟨V0, hV0, hV02, hV04, -⟩ := exists_four_of_mulEquiv_dihedral hn e₀ (one_mem _) (mul_one 1)
  obtain ⟨V1, hV1, hV12, hV14, -⟩ := exists_four_of_mulEquiv_dihedral hn e₁ (one_mem _) (mul_one 1)
  have key : ∀ {V V₀ V₁ : Subgroup G}, V ≤ D.A → V₀ ≤ D.B₀ → V₁ ≤ D.B₁ →
      (∀ x ∈ V, x * x = 1) → (∀ x ∈ V₀, x * x = 1) → (∀ x ∈ V₁, x * x = 1) →
      Nat.card V = 4 → Nat.card V₀ = 4 → Nat.card V₁ = 4 → V ⊔ (V₀ ⊔ V₁) ≤ X := by
    intro V V₀ V₁ h h₀ h₁ h2 h20 h21 hc hc₀ hc₁
    obtain ⟨hle, hsq, hcard⟩ := D.elem64_of_four h h₀ h₁ h2 h20 h21 hc hc₀ hc₁
    exact hX _ hle hsq hcard
  refine sup_le ?_ (sup_le ?_ ?_)
  · exact le_of_forall_four_le hm eA fun V hV hV2 hV4 =>
      le_sup_left.trans (key hV hV0 hV1 hV2 hV02 hV12 hV4 hV04 hV14)
  · exact le_of_forall_four_le hn e₀ fun V hV hV2 hV4 =>
      (le_sup_left.trans le_sup_right).trans (key hVA hV hV1 hVA2 hV2 hV12 hVA4 hV4 hV14)
  · exact le_of_forall_four_le hn e₁ fun V hV hV2 hV4 =>
      (le_sup_right.trans le_sup_right).trans (key hVA hV0 hV hVA2 hV02 hV2 hVA4 hV04 hV4)

theorem exists_elem32_s :
    ∃ F : Subgroup G, F ≤ D.T₀ ∧ (∀ x ∈ F, x * x = 1) ∧ Nat.card F = 2 ^ 5 ∧ D.s ∈ F := by
  obtain ⟨eA⟩ := D.A_iso
  obtain ⟨e₀⟩ := D.B₀_iso
  obtain ⟨V, hV, hV2, hV4, -⟩ :=
    exists_four_of_mulEquiv_dihedral (by have := D.two_le_m; omega) eA (one_mem _) (mul_one 1)
  obtain ⟨V₀, hV₀, hV₀2, hV₀4, -⟩ :=
    exists_four_of_mulEquiv_dihedral (by have := D.three_le_n; omega) e₀ (one_mem _) (mul_one 1)
  set C := (V₀.subgroupOf D.B₀).map D.sDiag with hC
  have hCC : C ≤ (D.B₀ ⊔ D.B₁) ⊓ centralizer {D.s} := by
    rw [hC, ← D.sDiag_range]
    exact map_le_range _ _
  have hC2 : ∀ x ∈ C, x * x = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    have hy2 : y * y = 1 := Subtype.ext (hV₀2 _ hy)
    rw [← map_mul, hy2, map_one]
  have hC4 : Nat.card C = 4 := by
    rw [hC, card_map_of_injective D.sDiag_injective,
      Nat.card_congr (subgroupOfEquivOfLe hV₀).toEquiv, hV₀4]
  have hs2 : ∀ x ∈ zpowers D.s, x * x = 1 := by
    intro x hx
    rcases eq_one_or_eq_of_mem_zpowers D.s_mul_s hx with rfl | rfl
    · exact mul_one 1
    · exact D.s_mul_s
  have hCs : ∀ x ∈ C, ∀ y ∈ zpowers D.s, x * y = y * x := by
    intro x hx y hy
    rcases eq_one_or_eq_of_mem_zpowers D.s_mul_s hy with rfl | rfl
    · rw [mul_one, one_mul]
    · exact mem_centralizer_singleton_iff.1 (mem_inf.1 (hCC hx)).2
  have hiCs : C ⊓ zpowers D.s = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxC, hxs⟩ := mem_inf.1 hx
    rcases eq_one_or_eq_of_mem_zpowers D.s_mul_s hxs with rfl | rfl
    · exact one_mem _
    · exact absurd (mem_inf.1 (hCC hxC)).1 D.s_not_mem_B₀B₁
  have hCsB : C ⊔ zpowers D.s ≤ D.B :=
    sup_le ((hCC.trans inf_le_left).trans D.B₀B₁_le_B) (zpowers_le.2 D.s_mem_B)
  have hcA : ∀ x ∈ V, ∀ y ∈ C ⊔ zpowers D.s, x * y = y * x :=
    fun x hx y hy => D.A_comm_B x (hV hx) y (hCsB hy)
  have hiA : V ⊓ (C ⊔ zpowers D.s) = ⊥ :=
    eq_bot_iff.2 ((inf_le_inf hV hCsB).trans D.A_inf_B.le)
  have h : Nat.card ↥(V ⊔ (C ⊔ zpowers D.s)) = 4 * (4 * 2) := by
    rw [card_sup_of_le_normalizer (le_normalizer_of_comm hcA) hiA,
      card_sup_of_le_normalizer (le_normalizer_of_comm hCs) hiCs, hV4, hC4, Nat.card_zpowers,
      D.orderOf_s]
  exact ⟨V ⊔ (C ⊔ zpowers D.s), sup_le_sup hV hCsB,
    fun x hx => mul_self_of_mem_sup hV2 (fun y hy => mul_self_of_mem_sup hC2 hs2 hCs hy) hcA hx,
    h.trans (by norm_num), mem_sup_right (mem_sup_right (mem_zpowers _))⟩

theorem T₀_le_of_forall_elem32 {X : Subgroup G}
    (hX : ∀ F : Subgroup G, F ≤ D.T₀ → (∀ x ∈ F, x * x = 1) → Nat.card F = 2 ^ 5 → F ≤ X) :
    D.T₀ ≤ X := by
  refine D.T₀_le_T₁_sup_s.trans (sup_le ?_ ?_)
  · refine D.T₁_le_of_forall_elem64 fun F hF hF2 hF6 x hx => ?_
    haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [hF6]; norm_num)
    obtain ⟨K, hK, hxK, hKF⟩ := Sylow.exists_subgroup_card_pow_prime_le_le (p := 2)
      Nat.prime_two (n := 5) (H := zpowers x) (L := F)
      (by
        rw [Nat.card_zpowers]
        exact (orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hF2 x hx)).trans (by norm_num))
      (by rw [hF6]; norm_num) (zpowers_le.2 hx)
    exact hX K (hKF.trans (hF.trans D.T₁_le_T₀)) (fun y hy => hF2 y (hKF hy)) hK
      (hxK (mem_zpowers x))
  · obtain ⟨F, hF, hF2, hF5, hsF⟩ := D.exists_elem32_s
    exact zpowers_le.2 (hX F hF hF2 hF5 hsF)

theorem map_T₁_eq {f : G →* G} (hf : Function.Injective f) (h : D.T₁.map f ≤ T) :
    D.T₁.map f = D.T₁ := by
  have hle : D.T₁.map f ≤ D.T₁ :=
    map_le_self_of_gen (fun F => (∀ x ∈ F, x * x = 1) ∧ Nat.card F = 2 ^ 6)
      (fun _ hX => D.T₁_le_of_forall_elem64 fun F hF hF2 hF6 => hX F hF ⟨hF2, hF6⟩) f
      (fun F hF hP => D.le_T₁_of_mul_self ((map_mono hF).trans h)
        (by rintro _ ⟨y, hy, rfl⟩; rw [← map_mul, hP.1 y hy, map_one])
        (by rw [card_map_of_injective hf, hP.2]; norm_num))
  haveI : Finite T := D.finite_T
  haveI : Finite D.T₁ := Finite.of_injective _ (inclusion_injective D.T₁_le_T)
  exact eq_of_le_of_card_ge hle (by rw [card_map_of_injective hf])

theorem map_T₀_eq {f : G →* G} (hf : Function.Injective f) (h : D.T₀.map f ≤ T) :
    D.T₀.map f = D.T₀ := by
  have hle : D.T₀.map f ≤ D.T₀ :=
    map_le_self_of_gen (fun F => (∀ x ∈ F, x * x = 1) ∧ Nat.card F = 2 ^ 5)
      (fun _ hX => D.T₀_le_of_forall_elem32 fun F hF hF2 hF5 => hX F hF ⟨hF2, hF5⟩) f
      (fun F hF hP => D.le_T₀_of_mul_self ((map_mono hF).trans h)
        (by rintro _ ⟨y, hy, rfl⟩; rw [← map_mul, hP.1 y hy, map_one])
        (by rw [card_map_of_injective hf, hP.2]; norm_num))
  haveI : Finite T := D.finite_T
  haveI : Finite D.T₀ := Finite.of_injective _ (inclusion_injective D.T₀_le_T)
  exact eq_of_le_of_card_ge hle (by rw [card_map_of_injective hf])

theorem exists_elem64_of_mem_T₁ {x : G} (hx : x ∈ D.T₁) (hx2 : x * x = 1) :
    ∃ F : Subgroup G, F ≤ D.T₁ ∧ CFSG.Open.IsElemAbelian 2 F ∧ Nat.card F = 2 ^ 6 ∧ x ∈ F := by
  obtain ⟨y, hy, w, hw, rfl⟩ := D.mem_T₁_iff.1 hx
  obtain ⟨w₀, hw₀, w₁, hw₁, rfl⟩ := D.mem_B₀B₁_iff.1 hw
  have hyw : y * (w₀ * w₁) = (w₀ * w₁) * y := D.A_comm_B₀B₁ y hy _ hw
  have h01 : w₀ * w₁ = w₁ * w₀ := D.B₀_comm_B₁ w₀ hw₀ w₁ hw₁
  have hsq : (y * y) * ((w₀ * w₀) * (w₁ * w₁)) = 1 := by
    calc (y * y) * ((w₀ * w₀) * (w₁ * w₁)) = (y * y) * (w₀ * (w₀ * w₁) * w₁) := by group
      _ = (y * y) * (w₀ * (w₁ * w₀) * w₁) := by rw [h01]
      _ = y * (y * (w₀ * w₁)) * (w₀ * w₁) := by group
      _ = y * ((w₀ * w₁) * y) * (w₀ * w₁) := by rw [hyw]
      _ = y * (w₀ * w₁) * (y * (w₀ * w₁)) := by group
      _ = 1 := hx2
  have hwB : (w₀ * w₀) * (w₁ * w₁) ∈ D.B :=
    D.B₀B₁_le_B (mul_mem (mem_sup_left (mul_mem hw₀ hw₀)) (mem_sup_right (mul_mem hw₁ hw₁)))
  obtain ⟨hyy, hww⟩ := D.mul_eq_one_T₀ (mul_mem hy hy) hwB hsq
  obtain ⟨hw₀₀, hw₁₁⟩ := D.mul_eq_one_B₀B₁ (mul_mem hw₀ hw₀) (mul_mem hw₁ hw₁) hww
  obtain ⟨eA⟩ := D.A_iso
  obtain ⟨e₀⟩ := D.B₀_iso
  obtain ⟨e₁⟩ := D.B₁_iso
  have hm : 1 ≤ m - 1 := by have := D.two_le_m; omega
  have hn : 1 ≤ n - 1 := by have := D.three_le_n; omega
  obtain ⟨V, hV, hV2, hV4, hyV⟩ := exists_four_of_mulEquiv_dihedral hm eA hy hyy
  obtain ⟨V₀, hV₀, hV₀2, hV₀4, hwV₀⟩ := exists_four_of_mulEquiv_dihedral hn e₀ hw₀ hw₀₀
  obtain ⟨V₁, hV₁, hV₁2, hV₁4, hwV₁⟩ := exists_four_of_mulEquiv_dihedral hn e₁ hw₁ hw₁₁
  obtain ⟨hle, hsq', hcard⟩ := D.elem64_of_four hV hV₀ hV₁ hV2 hV₀2 hV₁2 hV4 hV₀4 hV₁4
  exact ⟨_, hle, isElemAbelian_two_iff.2 hsq', hcard,
    mul_mem (mem_sup_left hyV) (mul_mem (mem_sup_right (mem_sup_left hwV₀))
      (mem_sup_right (mem_sup_right hwV₁)))⟩

end FooteCore

end CFSG.CGT.Foote81L6
