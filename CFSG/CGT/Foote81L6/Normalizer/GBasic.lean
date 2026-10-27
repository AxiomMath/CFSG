module

public import CFSG.CGT.Foote81L6.NBar
public import CFSG.CGT.Foote81L6.E64Fix
public import CFSG.CGT.Foote81L6.T0Sylow
public import CFSG.Quasithin.Background.FixVZPowersMem

public section

namespace CFSG.CGT.Foote81L6.Normalizer

open Subgroup CFSG.Quasithin
open scoped IsMulCommutative

variable {G : Type*} [Group G] {T : Subgroup G} {n : ℕ} (D : FooteCore G T 2 n)

theorem Z_le_E64 {E : Subgroup G} (hE : IsE64 T E) :
    D.A ⊔ (zpowers D.b₀ ⊔ zpowers D.b₁) ≤ E :=
  sup_le (D.A_le_E64 rfl hE)
    (sup_le (zpowers_le.2 (D.b₀_mem_E64 hE)) (zpowers_le.2 (D.b₁_mem_E64 hE)))

theorem comm_of_mem_T₁_of_mem_Z {g x : G} (hg : g ∈ D.T₁)
    (hx : x ∈ D.A ⊔ (zpowers D.b₀ ⊔ zpowers D.b₁)) : g * x = x * g := by
  have hA : ∀ y ∈ D.A, g * y = y * g := fun y hy => by
    have hle : D.T₁ ≤ centralizer ({y} : Set G) := sup_le
      (fun z hz => mem_centralizer_singleton_iff.2 (D.A_comm_of_two hz hy))
      (fun z hz => mem_centralizer_singleton_iff.2 (D.A_comm_B y hy z (D.B₀B₁_le_B hz)).symm)
    exact mem_centralizer_singleton_iff.1 (hle hg)
  have hb₀ : g * D.b₀ = D.b₀ * g := by
    have hle : D.T₁ ≤ centralizer ({D.b₀} : Set G) := sup_le
      (fun x hx => mem_centralizer_singleton_iff.2 (D.A_comm_B x hx D.b₀ D.b₀_mem_B))
      (sup_le (fun x hx => mem_centralizer_singleton_iff.2 (D.b₀_comm x hx))
        (fun x hx => mem_centralizer_singleton_iff.2 (D.B₀_comm_B₁ D.b₀ D.b₀_mem x hx).symm))
    exact mem_centralizer_singleton_iff.1 (hle hg)
  have hb₁ : g * D.b₁ = D.b₁ * g := by
    have hle : D.T₁ ≤ centralizer ({D.b₁} : Set G) := sup_le
      (fun x hx => mem_centralizer_singleton_iff.2 (D.A_comm_B x hx D.b₁ D.b₁_mem_B))
      (sup_le (fun x hx => mem_centralizer_singleton_iff.2 (D.B₀_comm_B₁ x hx D.b₁ D.b₁_mem))
        (fun x hx => mem_centralizer_singleton_iff.2 (D.b₁_comm x hx)))
    exact mem_centralizer_singleton_iff.1 (hle hg)
  have hZ : D.A ⊔ (zpowers D.b₀ ⊔ zpowers D.b₁) ≤ centralizer ({g} : Set G) :=
    sup_le (fun y hy => mem_centralizer_singleton_iff.2 (hA y hy).symm)
      (sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 hb₀.symm))
        (zpowers_le.2 (mem_centralizer_singleton_iff.2 hb₁.symm)))
  exact (mem_centralizer_singleton_iff.1 (hZ hx)).symm

theorem card_Z : Nat.card ↥(D.A ⊔ (zpowers D.b₀ ⊔ zpowers D.b₁)) = 16 := by
  have hBle : zpowers D.b₀ ⊔ zpowers D.b₁ ≤ D.B :=
    sup_le (zpowers_le.2 D.b₀_mem_B) (zpowers_le.2 D.b₁_mem_B)
  have hb₀b₁ : zpowers D.b₀ ⊓ zpowers D.b₁ = ⊥ := eq_bot_iff.2
    ((inf_le_inf (zpowers_le.2 D.b₀_mem) (zpowers_le.2 D.b₁_mem)).trans D.B₀_inf_B₁.le)
  have hA : D.A ⊓ (zpowers D.b₀ ⊔ zpowers D.b₁) = ⊥ :=
    eq_bot_iff.2 ((inf_le_inf_left _ hBle).trans D.A_inf_B.le)
  rw [card_sup_of_le_normalizer (le_normalizer_of_comm fun x hx y hy => D.A_comm_B x hx y (hBle hy))
      hA,
    card_sup_of_le_normalizer (le_normalizer_of_comm fun x hx y hy => D.B₀_comm_B₁ x
      (zpowers_le.2 D.b₀_mem hx) y (zpowers_le.2 D.b₁_mem hy)) hb₀b₁,
    D.card_A, Nat.card_zpowers, Nat.card_zpowers, D.b₀_order, D.b₁_order]
  norm_num

theorem mem_Z_of_fix {E : Subgroup G} (hE : IsE64 T E) {d₀ d₁ : G} (hd₀ : d₀ ∈ D.B₀)
    (hd₀m : ∃ w ∈ E, d₀ * w * d₀⁻¹ ≠ w) (hd₁ : d₁ ∈ D.B₁) (hd₁m : ∃ w ∈ E, d₁ * w * d₁⁻¹ ≠ w)
    {v : G} (hv : v ∈ E) (h0 : d₀ * v * d₀⁻¹ = v) (h1 : d₁ * v * d₁⁻¹ = v) :
    v ∈ D.A ⊔ (zpowers D.b₀ ⊔ zpowers D.b₁) := by
  obtain ⟨α, hα, v₀, hv₀, v₁, hv₁, rfl⟩ := (D.mem_E64_iff hE).1 hv
  have hαA := (mem_inf.1 hα).2
  have hv₀B := (mem_inf.1 hv₀).2
  have hv₁B := (mem_inf.1 hv₁).2
  rw [D.conj_decomp_B₀ hd₀ hαA hv₁B] at h0
  rw [D.conj_decomp_B₁ hd₁ hαA hv₀B] at h1
  have e0 : d₀ * v₀ * d₀⁻¹ = v₀ := mul_right_cancel (mul_left_cancel h0)
  have e1 : d₁ * v₁ * d₁⁻¹ = v₁ := mul_left_cancel (mul_left_cancel h1)
  have hz₀ : v₀ ∈ zpowers D.b₀ := by
    rcases D.eq_one_or_b₀_of_fix_E64 hE hd₀ hd₀m hv₀ e0 with h | h <;> rw [h]
    · exact one_mem _
    · exact mem_zpowers _
  have hz₁ : v₁ ∈ zpowers D.b₁ := by
    rcases D.eq_one_or_b₁_of_fix_E64 hE hd₁ hd₁m hv₁ e1 with h | h <;> rw [h]
    · exact one_mem _
    · exact mem_zpowers _
  exact mul_mem (mem_sup_left hαA) (mul_mem (mem_sup_right (mem_sup_left hz₀))
    (mem_sup_right (mem_sup_right hz₁)))

section NBar

variable {F : Subgroup G} [IsMulCommutative ↥F]

theorem π_eq_of_inv_mul_mem (x y : ↥(normalizer (F : Set G))) (h : (x : G)⁻¹ * y ∈ F) :
    NBar.π F x = NBar.π F y := by
  have hFc : ∀ u ∈ F, ∀ v ∈ F, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (mul_comm (⟨u, hu⟩ : ↥F) ⟨v, hv⟩)
  have h1 : NBar.π F (x⁻¹ * y) = 1 := NBar.π_eq_one_of_mem F hFc _ h
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1

theorem ρ_π_eq_self_iff (x : ↥(normalizer (F : Set G))) (v : ↥F) :
    NBar.ρ F (NBar.π F x) v = v ↔ (x : G) * v * (x : G)⁻¹ = v := by
  rw [← NBar.ρ_π F x v]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem ρ_ne_one_of_not_mem {m : ℕ} (D : FooteCore G T m n) (hF : IsE64 T F)
    (x : ↥(normalizer (F : Set G))) (hxT : (x : G) ∈ T) (hxF : (x : G) ∉ F) :
    NBar.ρ F (NBar.π F x) ≠ 1 := by
  intro h
  apply hxF
  have h1 : NBar.π F x = 1 := NBar.ρ_injective F (h.trans (map_one _).symm)
  rw [NBar.π_eq_one_iff] at h1
  have hmem : (x : G) ∈ T ⊓ centralizer (F : Set G) := by
    refine mem_inf.2 ⟨hxT, mem_centralizer_iff.2 fun v hv => ?_⟩
    calc v * x = ((x : G) * v * (x : G)⁻¹) * x := by rw [h1 v hv]
      _ = x * v := by group
  rwa [D.centralizer_E64 hF] at hmem

variable (hF : IsE64 T F)

theorem isTransvectionWith_d₀ {d₀ : G}
    (hd₀ : d₀ ∈ D.B₀ ⊓ normalizer ((F ⊓ D.B₀ : Subgroup G) : Set G)) (hd₀F : d₀ ∉ F) :
    IsTransvectionWith (NBar.ρ F (NBar.π F ⟨d₀, D.mem_normalizer_of_mem_R₀ hF hd₀⟩))
        ⟨D.b₀, D.b₀_mem_E64 hF⟩ ∧
      NBar.ρ F (NBar.π F ⟨d₀, D.mem_normalizer_of_mem_R₀ hF hd₀⟩) ≠ 1 :=
  ⟨NBar.isTransvectionWith_of_commutator F _ (D.b₀_mem_E64 hF) D.b₀_ne_one D.b₀_mul_b₀
      (D.commutator_E64_B₀ hF hd₀ hd₀F).le,
    ρ_ne_one_of_not_mem D hF _ (D.B_le_T (D.B₀_le_B (mem_inf.1 hd₀).1)) hd₀F⟩

theorem isTransvectionWith_d₁ {d₁ : G}
    (hd₁ : d₁ ∈ D.B₁ ⊓ normalizer ((F ⊓ D.B₁ : Subgroup G) : Set G)) (hd₁F : d₁ ∉ F) :
    IsTransvectionWith (NBar.ρ F (NBar.π F ⟨d₁, D.mem_normalizer_of_mem_R₁ hF hd₁⟩))
        ⟨D.b₁, D.b₁_mem_E64 hF⟩ ∧
      NBar.ρ F (NBar.π F ⟨d₁, D.mem_normalizer_of_mem_R₁ hF hd₁⟩) ≠ 1 :=
  ⟨NBar.isTransvectionWith_of_commutator F _ (D.b₁_mem_E64 hF) D.b₁_ne_one D.b₁_mul_b₁
      (D.commutator_E64_B₁ hF hd₁ hd₁F).le,
    ρ_ne_one_of_not_mem D hF _ (D.B_le_T (D.B₁_le_B (mem_inf.1 hd₁).1)) hd₁F⟩

theorem exists_moved_of_ρ_ne_one {x : ↥(normalizer (F : Set G))}
    (hx : NBar.ρ F (NBar.π F x) ≠ 1) : ∃ w ∈ F, (x : G) * w * (x : G)⁻¹ ≠ w := by
  obtain ⟨v, hv⟩ := B1.exists_moved_of_ne_one hx
  exact ⟨v, v.2, fun h => hv ((ρ_π_eq_self_iff x v).2 h)⟩

theorem fix_iff_mem_Z {d₀ d₁ : G}
    (hd₀ : d₀ ∈ D.B₀ ⊓ normalizer ((F ⊓ D.B₀ : Subgroup G) : Set G)) (hd₀F : d₀ ∉ F)
    (hd₁ : d₁ ∈ D.B₁ ⊓ normalizer ((F ⊓ D.B₁ : Subgroup G) : Set G)) (hd₁F : d₁ ∉ F) (v : ↥F) :
    (NBar.ρ F (NBar.π F ⟨d₀, D.mem_normalizer_of_mem_R₀ hF hd₀⟩) v = v ∧
        NBar.ρ F (NBar.π F ⟨d₁, D.mem_normalizer_of_mem_R₁ hF hd₁⟩) v = v) ↔
      (v : G) ∈ D.A ⊔ (zpowers D.b₀ ⊔ zpowers D.b₁) := by
  rw [ρ_π_eq_self_iff, ρ_π_eq_self_iff]
  constructor
  · rintro ⟨h0, h1⟩
    exact mem_Z_of_fix D hF (mem_inf.1 hd₀).1
      (exists_moved_of_ρ_ne_one (isTransvectionWith_d₀ D hF hd₀ hd₀F).2) (mem_inf.1 hd₁).1
      (exists_moved_of_ρ_ne_one (isTransvectionWith_d₁ D hF hd₁ hd₁F).2) v.2 h0 h1
  · intro hv
    have h0 := comm_of_mem_T₁_of_mem_Z D (D.B₀B₁_le_T₁ (mem_sup_left (mem_inf.1 hd₀).1)) hv
    have h1 := comm_of_mem_T₁_of_mem_Z D (D.B₀B₁_le_T₁ (mem_sup_right (mem_inf.1 hd₁).1)) hv
    exact ⟨by rw [h0, mul_inv_cancel_right], by rw [h1, mul_inv_cancel_right]⟩

theorem card_fix_d₀_d₁ {d₀ d₁ : G}
    (hd₀ : d₀ ∈ D.B₀ ⊓ normalizer ((F ⊓ D.B₀ : Subgroup G) : Set G)) (hd₀F : d₀ ∉ F)
    (hd₁ : d₁ ∈ D.B₁ ⊓ normalizer ((F ⊓ D.B₁ : Subgroup G) : Set G)) (hd₁F : d₁ ∉ F) :
    Nat.card ↥(fixV (zpowers (NBar.ρ F (NBar.π F ⟨d₀, D.mem_normalizer_of_mem_R₀ hF hd₀⟩))) ⊓
      fixV (zpowers (NBar.ρ F (NBar.π F ⟨d₁, D.mem_normalizer_of_mem_R₁ hF hd₁⟩)))) = 16 := by
  set W := fixV (zpowers (NBar.ρ F (NBar.π F ⟨d₀, D.mem_normalizer_of_mem_R₀ hF hd₀⟩))) ⊓
      fixV (zpowers (NBar.ρ F (NBar.π F ⟨d₁, D.mem_normalizer_of_mem_R₁ hF hd₁⟩))) with hW
  have hmap : W.map F.subtype = D.A ⊔ (zpowers D.b₀ ⊔ zpowers D.b₁) := by
    ext g
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hv' : v ∈ W := hv
      rw [hW, mem_inf, mem_fixV_zpowers_iff_apply, mem_fixV_zpowers_iff_apply] at hv'
      exact (fix_iff_mem_Z D hF hd₀ hd₀F hd₁ hd₁F v).1 hv'
    · intro hg
      refine ⟨⟨g, Z_le_E64 D hF hg⟩, ?_, rfl⟩
      show _ ∈ W
      rw [hW, mem_inf, mem_fixV_zpowers_iff_apply, mem_fixV_zpowers_iff_apply]
      exact (fix_iff_mem_Z D hF hd₀ hd₀F hd₁ hd₁F _).2 hg
  rw [← card_Z D, ← hmap, card_map_of_injective F.subtype_injective]

theorem π_mem_of_mem_T₁ [Finite G] {d₀ d₁ : G}
    (hd₀ : d₀ ∈ D.B₀ ⊓ normalizer ((F ⊓ D.B₀ : Subgroup G) : Set G)) (hd₀F : d₀ ∉ F)
    (hd₁ : d₁ ∈ D.B₁ ⊓ normalizer ((F ⊓ D.B₁ : Subgroup G) : Set G)) (hd₁F : d₁ ∉ F)
    (x : ↥(normalizer (F : Set G))) (hx : (x : G) ∈ D.T₁) :
    NBar.π F x = 1 ∨ NBar.π F x = NBar.π F ⟨d₀, D.mem_normalizer_of_mem_R₀ hF hd₀⟩ ∨
      NBar.π F x = NBar.π F ⟨d₁, D.mem_normalizer_of_mem_R₁ hF hd₁⟩ ∨
      NBar.π F x = NBar.π F ⟨d₀, D.mem_normalizer_of_mem_R₀ hF hd₀⟩ *
        NBar.π F ⟨d₁, D.mem_normalizer_of_mem_R₁ hF hd₁⟩ := by
  obtain ⟨α, hα, w, hw, hxw⟩ := D.mem_T₁_iff.1 hx
  obtain ⟨w₀, hw₀, w₁, hw₁, rfl⟩ := D.mem_B₀B₁_iff.1 hw
  have hAF : D.A ≤ F := D.A_le_E64 rfl hF
  have hαN : α ∈ normalizer (F : Set G) := le_normalizer (hAF hα)
  have hconj₀ : ∀ r ∈ D.B₀, (x : G) * r * (x : G)⁻¹ = w₀ * r * w₀⁻¹ := fun r hr => by
    rw [hxw]
    have e1 : α * (w₀ * r * w₀⁻¹) = (w₀ * r * w₀⁻¹) * α :=
      D.A_comm_B α hα _ (D.B₀_le_B (mul_mem (mul_mem hw₀ hr) (inv_mem hw₀)))
    have e2 : w₁ * r = r * w₁ := (D.B₀_comm_B₁ r hr w₁ hw₁).symm
    calc α * (w₀ * w₁) * r * (α * (w₀ * w₁))⁻¹
        = α * (w₀ * (w₁ * r) * w₁⁻¹ * w₀⁻¹) * α⁻¹ := by group
      _ = α * (w₀ * r * w₀⁻¹) * α⁻¹ := by rw [e2]; group
      _ = w₀ * r * w₀⁻¹ := by rw [e1, mul_inv_cancel_right]
  have hconj₁ : ∀ r ∈ D.B₁, (x : G) * r * (x : G)⁻¹ = w₁ * r * w₁⁻¹ := fun r hr => by
    rw [hxw]
    have e1 : α * (w₁ * r * w₁⁻¹) = (w₁ * r * w₁⁻¹) * α :=
      D.A_comm_B α hα _ (D.B₁_le_B (mul_mem (mul_mem hw₁ hr) (inv_mem hw₁)))
    have e2 : w₀ * (w₁ * r * w₁⁻¹) = (w₁ * r * w₁⁻¹) * w₀ :=
      D.B₀_comm_B₁ w₀ hw₀ _ (mul_mem (mul_mem hw₁ hr) (inv_mem hw₁))
    calc α * (w₀ * w₁) * r * (α * (w₀ * w₁))⁻¹
        = α * (w₀ * (w₁ * r * w₁⁻¹) * w₀⁻¹) * α⁻¹ := by group
      _ = α * (w₁ * r * w₁⁻¹) * α⁻¹ := by rw [e2]; group
      _ = w₁ * r * w₁⁻¹ := by rw [e1, mul_inv_cancel_right]
  obtain ⟨-, -, hB₀, hB₁⟩ := D.E64_decomp hF
  have hR₀ : w₀ ∈ D.B₀ ⊓ normalizer ((F ⊓ D.B₀ : Subgroup G) : Set G) := by
    haveI : Finite ↥(F ⊓ D.B₀) := Nat.finite_of_card_ne_zero (by rw [hB₀.2.2]; norm_num)
    refine mem_inf.2 ⟨hw₀, TStruct.mem_normalizer_of_forall_conj_mem fun r hr => ?_⟩
    obtain ⟨hrF, hrB⟩ := mem_inf.1 hr
    rw [← hconj₀ r hrB]
    exact mem_inf.2 ⟨(mem_normalizer_iff.1 x.2 r).1 hrF,
      by rw [hconj₀ r hrB]; exact mul_mem (mul_mem hw₀ hrB) (inv_mem hw₀)⟩
  have hR₁ : w₁ ∈ D.B₁ ⊓ normalizer ((F ⊓ D.B₁ : Subgroup G) : Set G) := by
    haveI : Finite ↥(F ⊓ D.B₁) := Nat.finite_of_card_ne_zero (by rw [hB₁.2.2]; norm_num)
    refine mem_inf.2 ⟨hw₁, TStruct.mem_normalizer_of_forall_conj_mem fun r hr => ?_⟩
    obtain ⟨hrF, hrB⟩ := mem_inf.1 hr
    rw [← hconj₁ r hrB]
    exact mem_inf.2 ⟨(mem_normalizer_iff.1 x.2 r).1 hrF,
      by rw [hconj₁ r hrB]; exact mul_mem (mul_mem hw₁ hrB) (inv_mem hw₁)⟩
  have hw₀N := D.mem_normalizer_of_mem_R₀ hF hR₀
  have hw₁N := D.mem_normalizer_of_mem_R₁ hF hR₁
  have hxeq : x = (⟨α, hαN⟩ : ↥(normalizer (F : Set G))) * ⟨w₀, hw₀N⟩ * ⟨w₁, hw₁N⟩ :=
    Subtype.ext (by rw [hxw]; simp only [Subgroup.coe_mul]; group)
  have hπα : NBar.π F ⟨α, hαN⟩ = 1 :=
    NBar.π_eq_one_of_mem F (fun u hu v hv =>
      congrArg Subtype.val (mul_comm (⟨u, hu⟩ : ↥F) ⟨v, hv⟩)) _ (hAF hα)
  have hπ₀ : NBar.π F ⟨w₀, hw₀N⟩ = 1 ∨
      NBar.π F ⟨w₀, hw₀N⟩ = NBar.π F ⟨d₀, D.mem_normalizer_of_mem_R₀ hF hd₀⟩ := by
    by_cases hw₀F : w₀ ∈ F
    · left
      exact NBar.π_eq_one_of_mem F (fun u hu v hv =>
        congrArg Subtype.val (mul_comm (⟨u, hu⟩ : ↥F) ⟨v, hv⟩)) _ hw₀F
    · right
      haveI : Finite ↥(D.B₀ ⊓ normalizer ((F ⊓ D.B₀ : Subgroup G) : Set G)) :=
        Nat.finite_of_card_ne_zero (by rw [D.card_R₀ hF]; norm_num)
      have hle : F ⊓ D.B₀ ≤ D.B₀ ⊓ normalizer ((F ⊓ D.B₀ : Subgroup G) : Set G) :=
        le_inf inf_le_right le_normalizer
      have h := inv_mul_mem_of_card_eq_two_mul hle (by rw [D.card_R₀ hF, hB₀.2.2]) hR₀ hd₀
        (fun h => hw₀F (mem_inf.1 h).1) (fun h => hd₀F (mem_inf.1 h).1)
      exact π_eq_of_inv_mul_mem _ _ (mem_inf.1 h).1
  have hπ₁ : NBar.π F ⟨w₁, hw₁N⟩ = 1 ∨
      NBar.π F ⟨w₁, hw₁N⟩ = NBar.π F ⟨d₁, D.mem_normalizer_of_mem_R₁ hF hd₁⟩ := by
    by_cases hw₁F : w₁ ∈ F
    · left
      exact NBar.π_eq_one_of_mem F (fun u hu v hv =>
        congrArg Subtype.val (mul_comm (⟨u, hu⟩ : ↥F) ⟨v, hv⟩)) _ hw₁F
    · right
      haveI : Finite ↥(D.B₁ ⊓ normalizer ((F ⊓ D.B₁ : Subgroup G) : Set G)) :=
        Nat.finite_of_card_ne_zero (by rw [D.card_R₁ hF]; norm_num)
      have hle : F ⊓ D.B₁ ≤ D.B₁ ⊓ normalizer ((F ⊓ D.B₁ : Subgroup G) : Set G) :=
        le_inf inf_le_right le_normalizer
      have h := inv_mul_mem_of_card_eq_two_mul hle (by rw [D.card_R₁ hF, hB₁.2.2]) hR₁ hd₁
        (fun h => hw₁F (mem_inf.1 h).1) (fun h => hd₁F (mem_inf.1 h).1)
      exact π_eq_of_inv_mul_mem _ _ (mem_inf.1 h).1
  rw [hxeq, map_mul, map_mul, hπα, one_mul]
  rcases hπ₀ with h0 | h0 <;> rcases hπ₁ with h1 | h1 <;> rw [h0, h1]
  · exact Or.inl (one_mul 1)
  · exact Or.inr (Or.inr (Or.inl (one_mul _)))
  · exact Or.inr (Or.inl (mul_one _))
  · exact Or.inr (Or.inr (Or.inr rfl))

end NBar

end CFSG.CGT.Foote81L6.Normalizer
