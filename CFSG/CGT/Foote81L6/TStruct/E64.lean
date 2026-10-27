module

public import CFSG.CGT.Foote81L6.TStruct.TAction

public section

namespace CFSG.CGT.Foote81L6

open Subgroup TStruct DihedralGroup
open scoped commutatorElement

theorem TStruct.mem_normalizer_of_forall_conj_mem {G : Type*} [Group G] {V : Subgroup G}
    [Finite V] {x : G} (h : ∀ v ∈ V, x * v * x⁻¹ ∈ V) : x ∈ normalizer (V : Set G) := by
  have hle : V.map (MulAut.conj x).toMonoidHom ≤ V := by
    rintro _ ⟨v, hv, rfl⟩
    exact h v hv
  have heq : V.map (MulAut.conj x).toMonoidHom = V :=
    eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj x).injective])
  refine mem_normalizer_iff.2 fun n => ⟨h n, fun hn => ?_⟩
  rw [← heq] at hn
  obtain ⟨v, hv, hvn⟩ := hn
  have : v = n := by
    have := congrArg (fun y => x⁻¹ * y * x) hvn
    simpa [mul_assoc] using this
  rwa [← this]

@[expose] def IsE64 {G : Type*} [Group G] (T E : Subgroup G) : Prop :=
  E ≤ T ∧ CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 2 ^ 6

theorem IsE64.mul_self {G : Type*} [Group G] {T E : Subgroup G} (hE : IsE64 T E) :
    ∀ x ∈ E, x * x = 1 :=
  isElemAbelian_two_iff.1 hE.2.1

theorem IsE64.finite {G : Type*} [Group G] {T E : Subgroup G} (hE : IsE64 T E) : Finite E :=
  Nat.finite_of_card_ne_zero (by rw [hE.2.2]; positivity)

namespace FooteCore

variable {G : Type*} [Group G] {T : Subgroup G} {m n : ℕ} (D : FooteCore G T m n)

@[expose] def Zab : Subgroup G := closure {D.a, D.b₀, D.b₁}

theorem finite_B₀B₁ : Finite ↥(D.B₀ ⊔ D.B₁) :=
  Nat.finite_of_card_ne_zero (by rw [D.card_B₀B₁]; positivity)

theorem le_T₁_of_isE64 {E : Subgroup G} (hE : IsE64 T E) : E ≤ D.T₁ :=
  D.le_T₁_of_isElemAbelian hE.1 hE.2.1 hE.2.2

theorem E64_decomp {E : Subgroup G} (hE : IsE64 T E) :
    E = (E ⊓ D.A) ⊔ ((E ⊓ D.B₀) ⊔ (E ⊓ D.B₁)) ∧ IsFourIn D.A (E ⊓ D.A) ∧
      IsFourIn D.B₀ (E ⊓ D.B₀) ∧ IsFourIn D.B₁ (E ⊓ D.B₁) := by
  haveI := D.finite_A
  haveI := D.finite_B₀
  haveI := D.finite_B₁
  haveI := D.finite_B₀B₁
  have hE2 := hE.mul_self
  obtain ⟨hEq, hA4, hB16⟩ := eq_sup_inf_of_card D.A_comm_B₀B₁ D.A_inf_B₀B₁ D.elemBound_A
    (ElemBound.sup D.B₀_comm_B₁ D.B₀_inf_B₁ D.elemBound_B₀ D.elemBound_B₁)
    (D.le_T₁_of_isE64 hE) hE2 (by rw [hE.2.2]; norm_num)
  obtain ⟨hEq', h04, h14⟩ := eq_sup_inf_of_card D.B₀_comm_B₁ D.B₀_inf_B₁ D.elemBound_B₀
    D.elemBound_B₁ (inf_le_right : E ⊓ (D.B₀ ⊔ D.B₁) ≤ D.B₀ ⊔ D.B₁) (fun x hx => hE2 x hx.1)
    (by rw [hB16])
  have e₀ : E ⊓ (D.B₀ ⊔ D.B₁) ⊓ D.B₀ = E ⊓ D.B₀ := by
    rw [inf_assoc, inf_of_le_right (le_sup_left : D.B₀ ≤ D.B₀ ⊔ D.B₁)]
  have e₁ : E ⊓ (D.B₀ ⊔ D.B₁) ⊓ D.B₁ = E ⊓ D.B₁ := by
    rw [inf_assoc, inf_of_le_right (le_sup_right : D.B₁ ≤ D.B₀ ⊔ D.B₁)]
  rw [e₀, e₁] at hEq'
  rw [e₀] at h04
  rw [e₁] at h14
  refine ⟨?_, ⟨inf_le_right, fun x hx => hE2 x hx.1, hA4⟩,
    ⟨inf_le_right, fun x hx => hE2 x hx.1, h04⟩, ⟨inf_le_right, fun x hx => hE2 x hx.1, h14⟩⟩
  conv_lhs => rw [hEq]
  rw [← hEq']

theorem mem_E64_iff {E : Subgroup G} (hE : IsE64 T E) {x : G} :
    x ∈ E ↔ ∃ u ∈ E ⊓ D.A, ∃ w₀ ∈ E ⊓ D.B₀, ∃ w₁ ∈ E ⊓ D.B₁, x = u * (w₀ * w₁) := by
  obtain ⟨hdec, -⟩ := D.E64_decomp hE
  have hle : (E ⊓ D.B₀) ⊔ (E ⊓ D.B₁) ≤ D.B₀ ⊔ D.B₁ :=
    sup_le_sup (inf_le_right : E ⊓ D.B₀ ≤ D.B₀) (inf_le_right : E ⊓ D.B₁ ≤ D.B₁)
  constructor
  · intro hx
    rw [hdec] at hx
    obtain ⟨u, hu, w, hw, rfl⟩ := (mem_sup_iff_of_le_normalizer (le_normalizer_of_comm
      fun x hx y hy => D.A_comm_B₀B₁ x (mem_inf.1 hx).2 y (hle hy))).1 hx
    obtain ⟨w₀, hw₀, w₁, hw₁, rfl⟩ := (mem_sup_iff_of_le_normalizer (le_normalizer_of_comm
      fun x hx y hy => D.B₀_comm_B₁ x (mem_inf.1 hx).2 y (mem_inf.1 hy).2)).1 hw
    exact ⟨u, hu, w₀, hw₀, w₁, hw₁, rfl⟩
  · rintro ⟨u, hu, w₀, hw₀, w₁, hw₁, rfl⟩
    exact mul_mem (mem_inf.1 hu).1 (mul_mem (mem_inf.1 hw₀).1 (mem_inf.1 hw₁).1)

theorem b₀_mem_E64 {E : Subgroup G} (hE : IsE64 T E) : D.b₀ ∈ E := by
  obtain ⟨e⟩ := D.B₀_iso
  have hn : 2 ≤ n - 1 := by have := D.three_le_n; omega
  have h := symm_zc_mem_four e (by omega) (D.E64_decomp hE).2.2.1
  rw [symm_zc_eq e hn D.b₀_mem D.b₀_ne_one fun y hy => D.b₀_comm y hy] at h
  exact (mem_inf.1 h).1

theorem b₁_mem_E64 {E : Subgroup G} (hE : IsE64 T E) : D.b₁ ∈ E := by
  obtain ⟨e⟩ := D.B₁_iso
  have hn : 2 ≤ n - 1 := by have := D.three_le_n; omega
  have h := symm_zc_mem_four e (by omega) (D.E64_decomp hE).2.2.2
  rw [symm_zc_eq e hn D.b₁_mem D.b₁_ne_one fun y hy => D.b₁_comm y hy] at h
  exact (mem_inf.1 h).1

theorem a_comm_A {y : G} (hy : y ∈ D.A) : y * D.a = D.a * y := D.a_comm y (mem_sup_left hy)

theorem A_le_E64 (hm : m = 2) {E : Subgroup G} (hE : IsE64 T E) : D.A ≤ E := by
  haveI := D.finite_A
  have h4 := (D.E64_decomp hE).2.1.2.2
  have heq : E ⊓ D.A = D.A :=
    eq_of_le_of_card_ge inf_le_right (by rw [h4, D.card_A, hm]; norm_num)
  rw [← heq]
  exact inf_le_left

theorem a_mem_E64 {E : Subgroup G} (hE : IsE64 T E) : D.a ∈ E := by
  by_cases hm : m = 2
  · exact D.A_le_E64 hm hE D.a_mem
  · obtain ⟨e⟩ := D.A_iso
    have hm2 : 2 ≤ m - 1 := by have := D.two_le_m; omega
    have h := symm_zc_mem_four e (by omega) (D.E64_decomp hE).2.1
    rw [symm_zc_eq e hm2 D.a_mem D.a_ne_one fun y hy => D.a_comm_A hy] at h
    exact (mem_inf.1 h).1

theorem inf_centralizer_At {U : Subgroup G} (hU : IsFourIn D.A U) :
    (D.A ⊔ zpowers D.t) ⊓ centralizer (U : Set G) = U := by
  obtain ⟨e⟩ := D.At_iso
  exact inf_centralizer_four e D.one_le_m ⟨hU.1.trans le_sup_left, hU.2.1, hU.2.2⟩

theorem mem_T₀_of_comm_four {U : Subgroup G} (hU : IsFourIn D.A U) {x : G} (hx : x ∈ T)
    (hc : ∀ u ∈ U, x * u = u * x) : x ∈ D.T₀ := by
  obtain ⟨α, hα, hαc, hαA⟩ := D.exists_At_conj_A hx
  rw [← hαA]
  have hαU : α ∈ (D.A ⊔ zpowers D.t) ⊓ centralizer (U : Set G) := by
    refine mem_inf.2 ⟨hα, mem_centralizer_iff.2 fun u hu => ?_⟩
    have h := hαc u (hU.1 hu)
    have h' : x * u * x⁻¹ = u := by rw [hc u hu, mul_inv_cancel_right]
    rw [h'] at h
    calc u * α = (α * u * α⁻¹) * α := by rw [← h]
      _ = α * u := by group
  rw [D.inf_centralizer_At hU] at hαU
  exact hU.1 hαU

theorem conj_b₀_of_not_mem_T₁ {x : G} (hx : x ∈ D.T₀) (hx1 : x ∉ D.T₁) :
    x * D.b₀ * x⁻¹ = D.b₁ := by
  have hxs : x * D.s ∈ D.T₁ := (D.mem_T₁_or_mul_s_mem_T₁ hx).resolve_left hx1
  obtain ⟨α, hα, w, hw, hαw⟩ := D.mem_T₁_iff.1 hxs
  have hxy : x = α * w * D.s := by
    calc x = x * D.s * D.s := by rw [mul_assoc, D.s_mul_s, mul_one]
      _ = α * w * D.s := by rw [hαw]
  rw [hxy]
  have h1 : D.s * D.b₀ * D.s⁻¹ = D.b₁ := D.conj_s_b₀
  have h2 : w * D.b₁ = D.b₁ * w := D.b₁_comm_B₀B₁ hw
  have h3 : α * D.b₁ = D.b₁ * α := D.A_comm_B α hα D.b₁ D.b₁_mem_B
  calc α * w * D.s * D.b₀ * (α * w * D.s)⁻¹ = α * w * (D.s * D.b₀ * D.s⁻¹) * w⁻¹ * α⁻¹ := by
        group
    _ = α * (w * D.b₁) * w⁻¹ * α⁻¹ := by rw [h1]; group
    _ = α * D.b₁ * α⁻¹ := by rw [h2]; group
    _ = D.b₁ := by rw [h3]; group

include D in
theorem centralizer_E64 {E : Subgroup G} (hE : IsE64 T E) :
    T ⊓ centralizer (E : Set G) = E := by
  obtain ⟨-, hA, hB₀, hB₁⟩ := D.E64_decomp hE
  apply le_antisymm
  · intro x hx
    obtain ⟨hxT, hxc⟩ := mem_inf.1 hx
    have hc : ∀ v ∈ E, x * v = v * x := fun v hv => ((mem_centralizer_iff.1 hxc) v hv).symm
    have hx0 : x ∈ D.T₀ := D.mem_T₀_of_comm_four hA hxT fun u hu => hc u (mem_inf.1 hu).1
    have hx1 : x ∈ D.T₁ := by
      by_contra hx1
      have h := D.conj_b₀_of_not_mem_T₁ hx0 hx1
      rw [hc D.b₀ (D.b₀_mem_E64 hE), mul_inv_cancel_right] at h
      exact D.b₀_ne_b₁ h
    obtain ⟨α, hα, w, hw, rfl⟩ := D.mem_T₁_iff.1 hx1
    obtain ⟨w₀, hw₀, w₁, hw₁, rfl⟩ := D.mem_B₀B₁_iff.1 hw
    obtain ⟨eA⟩ := D.A_iso
    obtain ⟨e₀⟩ := D.B₀_iso
    obtain ⟨e₁⟩ := D.B₁_iso
    have hm1 : 1 ≤ m - 1 := by have := D.two_le_m; omega
    have hn1 : 1 ≤ n - 1 := by have := D.three_le_n; omega
    have hαc : α ∈ D.A ⊓ centralizer ((E ⊓ D.A : Subgroup G) : Set G) := by
      refine mem_inf.2 ⟨hα, mem_centralizer_iff.2 fun v hv => ?_⟩
      obtain ⟨hvE, hvA⟩ := mem_inf.1 hv
      have h := hc v hvE
      have hw' : w₀ * w₁ * v = v * (w₀ * w₁) :=
        (D.A_comm_B₀B₁ v hvA _ (mul_mem (mem_sup_left hw₀) (mem_sup_right hw₁))).symm
      have : α * v * (w₀ * w₁) = v * α * (w₀ * w₁) := by
        calc α * v * (w₀ * w₁) = α * (v * (w₀ * w₁)) := mul_assoc _ _ _
          _ = α * (w₀ * w₁ * v) := by rw [hw']
          _ = α * (w₀ * w₁) * v := (mul_assoc _ _ _).symm
          _ = v * (α * (w₀ * w₁)) := h
          _ = v * α * (w₀ * w₁) := (mul_assoc _ _ _).symm
      exact (mul_right_cancel this).symm
    have hw₀c : w₀ ∈ D.B₀ ⊓ centralizer ((E ⊓ D.B₀ : Subgroup G) : Set G) := by
      refine mem_inf.2 ⟨hw₀, mem_centralizer_iff.2 fun v hv => ?_⟩
      obtain ⟨hvE, hvB⟩ := mem_inf.1 hv
      have h := hc v hvE
      have h1 : α * v = v * α := D.A_comm_B α hα v (D.B₀_le_B hvB)
      have h2 : w₁ * v = v * w₁ := (D.B₀_comm_B₁ v hvB w₁ hw₁).symm
      have : α * (w₀ * v) * w₁ = α * (v * w₀) * w₁ := by
        calc α * (w₀ * v) * w₁ = α * w₀ * (v * w₁) := by group
          _ = α * w₀ * (w₁ * v) := by rw [h2]
          _ = α * (w₀ * w₁) * v := by group
          _ = v * (α * (w₀ * w₁)) := h
          _ = (v * α) * w₀ * w₁ := by group
          _ = (α * v) * w₀ * w₁ := by rw [h1]
          _ = α * (v * w₀) * w₁ := by group
      exact (mul_left_cancel (mul_right_cancel this)).symm
    have hw₁c : w₁ ∈ D.B₁ ⊓ centralizer ((E ⊓ D.B₁ : Subgroup G) : Set G) := by
      refine mem_inf.2 ⟨hw₁, mem_centralizer_iff.2 fun v hv => ?_⟩
      obtain ⟨hvE, hvB⟩ := mem_inf.1 hv
      have h := hc v hvE
      have h1 : α * v = v * α := D.A_comm_B α hα v (D.B₁_le_B hvB)
      have h2 : w₀ * v = v * w₀ := D.B₀_comm_B₁ w₀ hw₀ v hvB
      have : α * w₀ * (w₁ * v) = α * w₀ * (v * w₁) := by
        calc α * w₀ * (w₁ * v) = α * (w₀ * w₁) * v := by group
          _ = v * (α * (w₀ * w₁)) := h
          _ = (v * α) * w₀ * w₁ := by group
          _ = (α * v) * w₀ * w₁ := by rw [h1]
          _ = α * (v * w₀) * w₁ := by group
          _ = α * (w₀ * v) * w₁ := by rw [h2]
          _ = α * w₀ * (v * w₁) := by group
      exact (mul_left_cancel this).symm
    rw [inf_centralizer_four eA hm1 hA] at hαc
    rw [inf_centralizer_four e₀ hn1 hB₀] at hw₀c
    rw [inf_centralizer_four e₁ hn1 hB₁] at hw₁c
    exact mul_mem (mem_inf.1 hαc).1 (mul_mem (mem_inf.1 hw₀c).1 (mem_inf.1 hw₁c).1)
  · intro x hx
    refine mem_inf.2 ⟨hE.1 hx, mem_centralizer_iff.2 fun v hv => ?_⟩
    exact comm_of_mul_self hE.mul_self hv hx

theorem card_R₀ {E : Subgroup G} (hE : IsE64 T E) :
    Nat.card ↥(D.B₀ ⊓ normalizer ((E ⊓ D.B₀ : Subgroup G) : Set G)) = 8 := by
  obtain ⟨e⟩ := D.B₀_iso
  exact card_inf_normalizer_four e (by have := D.three_le_n; omega) (D.E64_decomp hE).2.2.1

theorem card_R₁ {E : Subgroup G} (hE : IsE64 T E) :
    Nat.card ↥(D.B₁ ⊓ normalizer ((E ⊓ D.B₁ : Subgroup G) : Set G)) = 8 := by
  obtain ⟨e⟩ := D.B₁_iso
  exact card_inf_normalizer_four e (by have := D.three_le_n; omega) (D.E64_decomp hE).2.2.2

theorem card_R (hm : 3 ≤ m) {E : Subgroup G} (hE : IsE64 T E) :
    Nat.card ↥(D.A ⊓ normalizer ((E ⊓ D.A : Subgroup G) : Set G)) = 8 := by
  obtain ⟨e⟩ := D.A_iso
  exact card_inf_normalizer_four e (by omega) (D.E64_decomp hE).2.1

theorem mem_normalizer_of_mem_R₀ {E : Subgroup G} (hE : IsE64 T E) {d : G}
    (hd : d ∈ D.B₀ ⊓ normalizer ((E ⊓ D.B₀ : Subgroup G) : Set G)) :
    d ∈ normalizer (E : Set G) := by
  haveI := hE.finite
  obtain ⟨hdB, hdN⟩ := mem_inf.1 hd
  refine mem_normalizer_of_forall_conj_mem fun v hv => ?_
  obtain ⟨u, hu, w₀, hw₀, w₁, hw₁, rfl⟩ := (D.mem_E64_iff hE).1 hv
  have h1 : d * u = u * d := (D.A_comm_B u (mem_inf.1 hu).2 d (D.B₀_le_B hdB)).symm
  have h2 : d * w₁ = w₁ * d := D.B₀_comm_B₁ d hdB w₁ (mem_inf.1 hw₁).2
  have hw₀' : d * w₀ * d⁻¹ ∈ E ⊓ D.B₀ := (mem_normalizer_iff.1 hdN w₀).1 hw₀
  have h2' : d * w₁ * d⁻¹ = w₁ := by rw [h2, mul_inv_cancel_right]
  have e : d * (u * (w₀ * w₁)) * d⁻¹ = u * ((d * w₀ * d⁻¹) * w₁) := by
    calc d * (u * (w₀ * w₁)) * d⁻¹ = (d * u) * (w₀ * w₁) * d⁻¹ := by group
      _ = (u * d) * (w₀ * w₁) * d⁻¹ := by rw [h1]
      _ = u * ((d * w₀ * d⁻¹) * (d * w₁ * d⁻¹)) := by group
      _ = u * ((d * w₀ * d⁻¹) * w₁) := by rw [h2']
  rw [e]
  exact (D.mem_E64_iff hE).2 ⟨u, hu, _, hw₀', w₁, hw₁, rfl⟩

theorem mem_normalizer_of_mem_R₁ {E : Subgroup G} (hE : IsE64 T E) {d : G}
    (hd : d ∈ D.B₁ ⊓ normalizer ((E ⊓ D.B₁ : Subgroup G) : Set G)) :
    d ∈ normalizer (E : Set G) := by
  haveI := hE.finite
  obtain ⟨hdB, hdN⟩ := mem_inf.1 hd
  refine mem_normalizer_of_forall_conj_mem fun v hv => ?_
  obtain ⟨u, hu, w₀, hw₀, w₁, hw₁, rfl⟩ := (D.mem_E64_iff hE).1 hv
  have h1 : d * u = u * d := (D.A_comm_B u (mem_inf.1 hu).2 d (D.B₁_le_B hdB)).symm
  have h2 : d * w₀ = w₀ * d := (D.B₀_comm_B₁ w₀ (mem_inf.1 hw₀).2 d hdB).symm
  have hw₁' : d * w₁ * d⁻¹ ∈ E ⊓ D.B₁ := (mem_normalizer_iff.1 hdN w₁).1 hw₁
  have e : d * (u * (w₀ * w₁)) * d⁻¹ = u * (w₀ * (d * w₁ * d⁻¹)) := by
    calc d * (u * (w₀ * w₁)) * d⁻¹ = (d * u) * w₀ * w₁ * d⁻¹ := by group
      _ = u * (d * w₀) * w₁ * d⁻¹ := by rw [h1]; group
      _ = u * (w₀ * d) * w₁ * d⁻¹ := by rw [h2]
      _ = u * (w₀ * (d * w₁ * d⁻¹)) := by group
  rw [e]
  exact (D.mem_E64_iff hE).2 ⟨u, hu, w₀, hw₀, _, hw₁', rfl⟩

theorem mem_normalizer_of_mem_R {E : Subgroup G} (hE : IsE64 T E) {d : G}
    (hd : d ∈ D.A ⊓ normalizer ((E ⊓ D.A : Subgroup G) : Set G)) :
    d ∈ normalizer (E : Set G) := by
  haveI := hE.finite
  obtain ⟨hdA, hdN⟩ := mem_inf.1 hd
  refine mem_normalizer_of_forall_conj_mem fun v hv => ?_
  obtain ⟨u, hu, w₀, hw₀, w₁, hw₁, rfl⟩ := (D.mem_E64_iff hE).1 hv
  have hwB : w₀ * w₁ ∈ D.B₀ ⊔ D.B₁ :=
    mul_mem (mem_sup_left (mem_inf.1 hw₀).2) (mem_sup_right (mem_inf.1 hw₁).2)
  have h1 : d * (w₀ * w₁) = (w₀ * w₁) * d := D.A_comm_B₀B₁ d hdA _ hwB
  have hu' : d * u * d⁻¹ ∈ E ⊓ D.A := (mem_normalizer_iff.1 hdN u).1 hu
  have e : d * (u * (w₀ * w₁)) * d⁻¹ = (d * u * d⁻¹) * (w₀ * w₁) := by
    calc d * (u * (w₀ * w₁)) * d⁻¹ = d * u * d⁻¹ * (d * (w₀ * w₁)) * d⁻¹ := by group
      _ = d * u * d⁻¹ * ((w₀ * w₁) * d) * d⁻¹ := by rw [h1]
      _ = (d * u * d⁻¹) * (w₀ * w₁) := by group
  rw [e]
  exact (D.mem_E64_iff hE).2 ⟨_, hu', w₀, hw₀, w₁, hw₁, rfl⟩

theorem commutator_eq_B₀ {u w₀ w₁ y : G} (hu : u ∈ D.A) (hw₀ : w₀ ∈ D.B₀) (hw₁ : w₁ ∈ D.B₁)
    (hy : y ∈ D.B₀) : ⁅u * (w₀ * w₁), y⁆ = w₀ * (y * w₀⁻¹ * y⁻¹) := by
  have h1 : u * y = y * u := D.A_comm_B u hu y (D.B₀_le_B hy)
  have h2 : w₁ * y = y * w₁ := (D.B₀_comm_B₁ y hy w₁ hw₁).symm
  have hc : u * (w₀ * (y * w₀⁻¹ * y⁻¹)) = (w₀ * (y * w₀⁻¹ * y⁻¹)) * u :=
    D.A_comm_B u hu _ (D.B₀_le_B (mul_mem hw₀ (mul_mem (mul_mem hy (inv_mem hw₀))
      (inv_mem hy))))
  have e3 : y * u⁻¹ * y⁻¹ = u⁻¹ := by
    calc y * u⁻¹ * y⁻¹ = u⁻¹ * (u * y) * u⁻¹ * y⁻¹ := by group
      _ = u⁻¹ * (y * u) * u⁻¹ * y⁻¹ := by rw [h1]
      _ = u⁻¹ := by group
  rw [commutatorElement_def]
  calc u * (w₀ * w₁) * y * (u * (w₀ * w₁))⁻¹ * y⁻¹
      = u * w₀ * (w₁ * y) * w₁⁻¹ * w₀⁻¹ * u⁻¹ * y⁻¹ := by group
    _ = u * (w₀ * (y * w₀⁻¹ * y⁻¹)) * (y * u⁻¹ * y⁻¹) := by rw [h2]; group
    _ = (w₀ * (y * w₀⁻¹ * y⁻¹)) * u * u⁻¹ := by rw [hc, e3]
    _ = w₀ * (y * w₀⁻¹ * y⁻¹) := by group

theorem commutator_eq_B₁ {u w₀ w₁ y : G} (hu : u ∈ D.A) (hw₀ : w₀ ∈ D.B₀) (hw₁ : w₁ ∈ D.B₁)
    (hy : y ∈ D.B₁) : ⁅u * (w₀ * w₁), y⁆ = w₁ * (y * w₁⁻¹ * y⁻¹) := by
  have h1 : u * y = y * u := D.A_comm_B u hu y (D.B₁_le_B hy)
  have h2 : w₀ * y = y * w₀ := D.B₀_comm_B₁ w₀ hw₀ y hy
  have hX : w₁ * (y * w₁⁻¹ * y⁻¹) ∈ D.B₁ :=
    mul_mem hw₁ (mul_mem (mul_mem hy (inv_mem hw₁)) (inv_mem hy))
  have hc : u * (w₁ * (y * w₁⁻¹ * y⁻¹)) = (w₁ * (y * w₁⁻¹ * y⁻¹)) * u :=
    D.A_comm_B u hu _ (D.B₁_le_B hX)
  have hc' : w₀ * (w₁ * (y * w₁⁻¹ * y⁻¹)) = (w₁ * (y * w₁⁻¹ * y⁻¹)) * w₀ :=
    D.B₀_comm_B₁ w₀ hw₀ _ hX
  have e3 : y * u⁻¹ * y⁻¹ = u⁻¹ := by
    calc y * u⁻¹ * y⁻¹ = u⁻¹ * (u * y) * u⁻¹ * y⁻¹ := by group
      _ = u⁻¹ * (y * u) * u⁻¹ * y⁻¹ := by rw [h1]
      _ = u⁻¹ := by group
  have e4 : y * w₀⁻¹ * y⁻¹ = w₀⁻¹ := by
    calc y * w₀⁻¹ * y⁻¹ = w₀⁻¹ * (w₀ * y) * w₀⁻¹ * y⁻¹ := by group
      _ = w₀⁻¹ * (y * w₀) * w₀⁻¹ * y⁻¹ := by rw [h2]
      _ = w₀⁻¹ := by group
  have e5 : y * w₀⁻¹ * u⁻¹ * y⁻¹ = w₀⁻¹ * u⁻¹ := by
    calc y * w₀⁻¹ * u⁻¹ * y⁻¹ = (y * w₀⁻¹ * y⁻¹) * (y * u⁻¹ * y⁻¹) := by group
      _ = w₀⁻¹ * u⁻¹ := by rw [e4, e3]
  rw [commutatorElement_def]
  calc u * (w₀ * w₁) * y * (u * (w₀ * w₁))⁻¹ * y⁻¹
      = u * w₀ * (w₁ * (y * w₁⁻¹ * y⁻¹)) * (y * w₀⁻¹ * u⁻¹ * y⁻¹) := by group
    _ = u * w₀ * (w₁ * (y * w₁⁻¹ * y⁻¹)) * (w₀⁻¹ * u⁻¹) := by rw [e5]
    _ = u * (w₀ * (w₁ * (y * w₁⁻¹ * y⁻¹))) * w₀⁻¹ * u⁻¹ := by group
    _ = u * ((w₁ * (y * w₁⁻¹ * y⁻¹)) * w₀) * w₀⁻¹ * u⁻¹ := by rw [hc']
    _ = (u * (w₁ * (y * w₁⁻¹ * y⁻¹))) * u⁻¹ := by group
    _ = ((w₁ * (y * w₁⁻¹ * y⁻¹)) * u) * u⁻¹ := by rw [hc]
    _ = w₁ * (y * w₁⁻¹ * y⁻¹) := by group

theorem commutator_eq_A {u w₀ w₁ y : G} (hu : u ∈ D.A) (hw₀ : w₀ ∈ D.B₀) (hw₁ : w₁ ∈ D.B₁)
    (hy : y ∈ D.A) : ⁅u * (w₀ * w₁), y⁆ = u * (y * u⁻¹ * y⁻¹) := by
  have hwB : w₀ * w₁ ∈ D.B₀ ⊔ D.B₁ := mul_mem (mem_sup_left hw₀) (mem_sup_right hw₁)
  have h1 : y * (w₀ * w₁) = (w₀ * w₁) * y := D.A_comm_B₀B₁ y hy _ hwB
  have hc : (w₀ * w₁) * (y * u⁻¹ * y⁻¹) = (y * u⁻¹ * y⁻¹) * (w₀ * w₁) :=
    (D.A_comm_B₀B₁ _ (mul_mem (mul_mem hy (inv_mem hu)) (inv_mem hy)) _ hwB).symm
  have h1' : (w₀ * w₁) * y * (w₀ * w₁)⁻¹ = y := by rw [← h1, mul_inv_cancel_right]
  rw [commutatorElement_def]
  calc u * (w₀ * w₁) * y * (u * (w₀ * w₁))⁻¹ * y⁻¹
      = u * ((w₀ * w₁) * y * (w₀ * w₁)⁻¹) * u⁻¹ * y⁻¹ := by group
    _ = u * y * u⁻¹ * y⁻¹ := by rw [h1']
    _ = u * (y * u⁻¹ * y⁻¹) := by group

theorem commutator_E64_B₀ {E : Subgroup G} (hE : IsE64 T E) {d : G}
    (hd : d ∈ D.B₀ ⊓ normalizer ((E ⊓ D.B₀ : Subgroup G) : Set G)) (hdE : d ∉ E) :
    ⁅E, zpowers d⁆ = zpowers D.b₀ := by
  obtain ⟨-, -, hB₀, -⟩ := D.E64_decomp hE
  obtain ⟨e⟩ := D.B₀_iso
  have hn2 : 2 ≤ n - 1 := by have := D.three_le_n; omega
  have hz := symm_zc_eq e hn2 D.b₀_mem D.b₀_ne_one fun y hy => D.b₀_comm y hy
  apply le_antisymm
  · rw [commutator_le]
    intro v hv y hy
    have hyR : y ∈ D.B₀ ⊓ normalizer ((E ⊓ D.B₀ : Subgroup G) : Set G) := (zpowers_le.2 hd) hy
    obtain ⟨u, hu, w₀, hw₀, w₁, hw₁, rfl⟩ := (D.mem_E64_iff hE).1 hv
    rw [D.commutator_eq_B₀ (mem_inf.1 hu).2 (mem_inf.1 hw₀).2 (mem_inf.1 hw₁).2
      (mem_inf.1 hyR).1]
    have hinv := conj_of_mem_inf_normalizer_four e (by omega) hB₀ hyR (inv_mem hw₀)
    rw [hz] at hinv
    rcases hinv with h | h
    · rw [h, mul_inv_cancel]
      exact one_mem _
    · rw [h, ← mul_assoc, mul_inv_cancel, one_mul]
      exact mem_zpowers _
  · rw [zpowers_le]
    have hdE' : d ∉ E ⊓ D.B₀ := fun h => hdE (mem_inf.1 h).1
    obtain ⟨v, hv, hvd⟩ := exists_conj_of_not_mem_four e (by omega) hB₀ hd hdE'
    rw [hz] at hvd
    have hb : v * D.b₀ = D.b₀ * v := D.b₀_comm v (mem_inf.1 hv).2
    have hb' : D.b₀⁻¹ = D.b₀ := inv_eq_of_mul_eq_one_right D.b₀_mul_b₀
    have hc : ⁅v, d⁆ = D.b₀ := by
      rw [commutatorElement_def]
      calc v * d * v⁻¹ * d⁻¹ = v * (d * v * d⁻¹)⁻¹ := by group
        _ = v * (v * D.b₀)⁻¹ := by rw [hvd]
        _ = v * D.b₀⁻¹ * v⁻¹ := by group
        _ = D.b₀ := by rw [hb', hb]; group
    rw [← hc]
    exact commutator_mem_commutator (mem_inf.1 hv).1 (mem_zpowers d)

theorem commutator_E64_B₁ {E : Subgroup G} (hE : IsE64 T E) {d : G}
    (hd : d ∈ D.B₁ ⊓ normalizer ((E ⊓ D.B₁ : Subgroup G) : Set G)) (hdE : d ∉ E) :
    ⁅E, zpowers d⁆ = zpowers D.b₁ := by
  obtain ⟨-, -, -, hB₁⟩ := D.E64_decomp hE
  obtain ⟨e⟩ := D.B₁_iso
  have hn2 : 2 ≤ n - 1 := by have := D.three_le_n; omega
  have hz := symm_zc_eq e hn2 D.b₁_mem D.b₁_ne_one fun y hy => D.b₁_comm y hy
  apply le_antisymm
  · rw [commutator_le]
    intro v hv y hy
    have hyR : y ∈ D.B₁ ⊓ normalizer ((E ⊓ D.B₁ : Subgroup G) : Set G) := (zpowers_le.2 hd) hy
    obtain ⟨u, hu, w₀, hw₀, w₁, hw₁, rfl⟩ := (D.mem_E64_iff hE).1 hv
    rw [D.commutator_eq_B₁ (mem_inf.1 hu).2 (mem_inf.1 hw₀).2 (mem_inf.1 hw₁).2
      (mem_inf.1 hyR).1]
    have hinv := conj_of_mem_inf_normalizer_four e (by omega) hB₁ hyR (inv_mem hw₁)
    rw [hz] at hinv
    rcases hinv with h | h
    · rw [h, mul_inv_cancel]
      exact one_mem _
    · rw [h, ← mul_assoc, mul_inv_cancel, one_mul]
      exact mem_zpowers _
  · rw [zpowers_le]
    have hdE' : d ∉ E ⊓ D.B₁ := fun h => hdE (mem_inf.1 h).1
    obtain ⟨v, hv, hvd⟩ := exists_conj_of_not_mem_four e (by omega) hB₁ hd hdE'
    rw [hz] at hvd
    have hb : v * D.b₁ = D.b₁ * v := D.b₁_comm v (mem_inf.1 hv).2
    have hb' : D.b₁⁻¹ = D.b₁ := inv_eq_of_mul_eq_one_right D.b₁_mul_b₁
    have hc : ⁅v, d⁆ = D.b₁ := by
      rw [commutatorElement_def]
      calc v * d * v⁻¹ * d⁻¹ = v * (d * v * d⁻¹)⁻¹ := by group
        _ = v * (v * D.b₁)⁻¹ := by rw [hvd]
        _ = v * D.b₁⁻¹ * v⁻¹ := by group
        _ = D.b₁ := by rw [hb', hb]; group
    rw [← hc]
    exact commutator_mem_commutator (mem_inf.1 hv).1 (mem_zpowers d)

theorem commutator_E64_A (hm : 3 ≤ m) {E : Subgroup G} (hE : IsE64 T E) {d : G}
    (hd : d ∈ D.A ⊓ normalizer ((E ⊓ D.A : Subgroup G) : Set G)) (hdE : d ∉ E) :
    ⁅E, zpowers d⁆ = zpowers D.a := by
  obtain ⟨-, hA, -, -⟩ := D.E64_decomp hE
  obtain ⟨e⟩ := D.A_iso
  have hm2 : 2 ≤ m - 1 := by omega
  have hz := symm_zc_eq e hm2 D.a_mem D.a_ne_one fun y hy => D.a_comm_A hy
  apply le_antisymm
  · rw [commutator_le]
    intro v hv y hy
    have hyR : y ∈ D.A ⊓ normalizer ((E ⊓ D.A : Subgroup G) : Set G) := (zpowers_le.2 hd) hy
    obtain ⟨u, hu, w₀, hw₀, w₁, hw₁, rfl⟩ := (D.mem_E64_iff hE).1 hv
    rw [D.commutator_eq_A (mem_inf.1 hu).2 (mem_inf.1 hw₀).2 (mem_inf.1 hw₁).2
      (mem_inf.1 hyR).1]
    have hinv := conj_of_mem_inf_normalizer_four e (by omega) hA hyR (inv_mem hu)
    rw [hz] at hinv
    rcases hinv with h | h
    · rw [h, mul_inv_cancel]
      exact one_mem _
    · rw [h, ← mul_assoc, mul_inv_cancel, one_mul]
      exact mem_zpowers _
  · rw [zpowers_le]
    have hdE' : d ∉ E ⊓ D.A := fun h => hdE (mem_inf.1 h).1
    obtain ⟨v, hv, hvd⟩ := exists_conj_of_not_mem_four e (by omega) hA hd hdE'
    rw [hz] at hvd
    have hb : v * D.a = D.a * v := D.a_comm_A (mem_inf.1 hv).2
    have hb' : D.a⁻¹ = D.a := inv_eq_of_mul_eq_one_right D.a_mul_a
    have hc : ⁅v, d⁆ = D.a := by
      rw [commutatorElement_def]
      calc v * d * v⁻¹ * d⁻¹ = v * (d * v * d⁻¹)⁻¹ := by group
        _ = v * (v * D.a)⁻¹ := by rw [hvd]
        _ = v * D.a⁻¹ * v⁻¹ := by group
        _ = D.a := by rw [hb', hb]; group
    rw [← hc]
    exact commutator_mem_commutator (mem_inf.1 hv).1 (mem_zpowers d)

theorem exists_d₀ {E : Subgroup G} (hE : IsE64 T E) :
    ∃ d ∈ D.B₀ ⊓ normalizer ((E ⊓ D.B₀ : Subgroup G) : Set G), d * d = 1 ∧ d ∉ E ∧
      d ∈ normalizer (E : Set G) ∧ ⁅E, zpowers d⁆ = zpowers D.b₀ := by
  obtain ⟨e⟩ := D.B₀_iso
  obtain ⟨d, hd, hdE, hd2⟩ :=
    exists_involution_four e (by have := D.three_le_n; omega) (D.E64_decomp hE).2.2.1
  have hdE' : d ∉ E := fun h => hdE (mem_inf.2 ⟨h, (mem_inf.1 hd).1⟩)
  exact ⟨d, hd, hd2, hdE', D.mem_normalizer_of_mem_R₀ hE hd, D.commutator_E64_B₀ hE hd hdE'⟩

theorem exists_d₁ {E : Subgroup G} (hE : IsE64 T E) :
    ∃ d ∈ D.B₁ ⊓ normalizer ((E ⊓ D.B₁ : Subgroup G) : Set G), d * d = 1 ∧ d ∉ E ∧
      d ∈ normalizer (E : Set G) ∧ ⁅E, zpowers d⁆ = zpowers D.b₁ := by
  obtain ⟨e⟩ := D.B₁_iso
  obtain ⟨d, hd, hdE, hd2⟩ :=
    exists_involution_four e (by have := D.three_le_n; omega) (D.E64_decomp hE).2.2.2
  have hdE' : d ∉ E := fun h => hdE (mem_inf.2 ⟨h, (mem_inf.1 hd).1⟩)
  exact ⟨d, hd, hd2, hdE', D.mem_normalizer_of_mem_R₁ hE hd, D.commutator_E64_B₁ hE hd hdE'⟩

theorem exists_d (hm : 3 ≤ m) {E : Subgroup G} (hE : IsE64 T E) :
    ∃ d ∈ D.A ⊓ normalizer ((E ⊓ D.A : Subgroup G) : Set G), d * d = 1 ∧ d ∉ E ∧
      d ∈ normalizer (E : Set G) ∧ ⁅E, zpowers d⁆ = zpowers D.a := by
  obtain ⟨e⟩ := D.A_iso
  obtain ⟨d, hd, hdE, hd2⟩ := exists_involution_four e (by omega) (D.E64_decomp hE).2.1
  have hdE' : d ∉ E := fun h => hdE (mem_inf.2 ⟨h, (mem_inf.1 hd).1⟩)
  exact ⟨d, hd, hd2, hdE', D.mem_normalizer_of_mem_R hE hd, D.commutator_E64_A hm hE hd hdE'⟩

end FooteCore

end CFSG.CGT.Foote81L6
