module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheck
import all CFSG.Fischer.F4

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer

theorem fld_mul_conj (s : SU52) : fld * MulAut.conj s = MulAut.conj (fld s) * fld :=
  MulEquiv.ext fun g => by
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]

theorem fld_mul_fld : fld * fld = 1 := MulEquiv.ext fun g => fld_fld g

theorem fld_inv : fld⁻¹ = fld := inv_eq_of_mul_eq_one_right fld_mul_fld

theorem fld_mem_Ssub {s : SU52} (hs : s ∈ Ssub) : fld s ∈ Ssub := by
  obtain ⟨h1, h2⟩ := mem_Ssub.1 hs
  refine mem_Ssub.2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [mat_fld, Matrix.map_apply, h1 i j hij, map_zero]
  · rw [mat_fld, Matrix.map_apply, h2 i, map_one]

theorem fieldFactor_conj_mul_fld (s : SU52) : fieldFactor (MulAut.conj s * fld) ≠ 1 := by
  rw [map_mul, fieldFactor_conj, one_mul, fieldFactor_fld]
  exact barEquiv_ne_one

@[expose] def psiAut (p : SU52 × Bool) : MulAut SU52 :=
  MulAut.conj p.1 * if p.2 then fld else 1

theorem psiAut_injective : Function.Injective psiAut := by
  rintro ⟨s, b⟩ ⟨t, c⟩ h
  have hb : b = c := by
    have := congrArg fieldFactor h
    cases b <;> cases c <;> simp [psiAut, fieldFactor_fld, barEquiv_ne_one, barEquiv_ne_one.symm]
      at this ⊢
  subst hb
  have hs : MulAut.conj s = MulAut.conj t := by
    cases b
    · simpa [psiAut] using h
    · simpa [psiAut] using h
  rw [conj_inj.1 hs]

@[expose] def SfAut : Subgroup (MulAut SU52) where
  carrier := {α | ∃ s ∈ Ssub, α = MulAut.conj s ∨ α = MulAut.conj s * fld}
  mul_mem' := by
    rintro α β ⟨s, hs, rfl | rfl⟩ ⟨t, ht, rfl | rfl⟩
    · exact ⟨s * t, mul_mem hs ht, Or.inl (map_mul _ _ _).symm⟩
    · exact ⟨s * t, mul_mem hs ht, Or.inr (by rw [map_mul, mul_assoc])⟩
    · refine ⟨s * fld t, mul_mem hs (fld_mem_Ssub ht), Or.inr ?_⟩
      rw [mul_assoc, fld_mul_conj, ← mul_assoc, map_mul]
    · refine ⟨s * fld t, mul_mem hs (fld_mem_Ssub ht), Or.inl ?_⟩
      rw [mul_assoc, ← mul_assoc fld, fld_mul_conj, mul_assoc, fld_mul_fld, mul_one, map_mul]
  one_mem' := ⟨1, one_mem _, Or.inl (map_one _).symm⟩
  inv_mem' := by
    rintro α ⟨s, hs, rfl | rfl⟩
    · exact ⟨s⁻¹, inv_mem hs, Or.inl (map_inv _ _).symm⟩
    · refine ⟨fld s⁻¹, fld_mem_Ssub (inv_mem hs), Or.inr ?_⟩
      rw [mul_inv_rev, fld_inv, ← map_inv, fld_mul_conj]

theorem mem_SfAut_iff {α : MulAut SU52} :
    α ∈ SfAut ↔ ∃ s ∈ Ssub, ∃ b : Bool, α = psiAut (s, b) := by
  constructor
  · rintro ⟨s, hs, rfl | rfl⟩
    · exact ⟨s, hs, false, by simp [psiAut]⟩
    · exact ⟨s, hs, true, by simp [psiAut]⟩
  · rintro ⟨s, hs, b, rfl⟩
    cases b
    · exact ⟨s, hs, Or.inl (by simp [psiAut])⟩
    · exact ⟨s, hs, Or.inr (by simp [psiAut])⟩

theorem conj_mem_SfAut {s : SU52} (hs : s ∈ Ssub) : MulAut.conj s ∈ SfAut := ⟨s, hs, Or.inl rfl⟩

theorem fld_mem_SfAut : fld ∈ SfAut := ⟨1, one_mem _, Or.inr (by rw [map_one, one_mul])⟩

theorem card_SfAut : Nat.card SfAut = 2 ^ 11 := by
  have e : (SfAut : Set (MulAut SU52)) = psiAut '' ((Ssub : Set SU52) ×ˢ Set.univ) := by
    ext α
    rw [SetLike.mem_coe, mem_SfAut_iff]
    constructor
    · rintro ⟨s, hs, b, rfl⟩
      exact ⟨(s, b), ⟨hs, Set.mem_univ _⟩, rfl⟩
    · rintro ⟨⟨s, b⟩, ⟨hs, -⟩, rfl⟩
      exact ⟨s, hs, b, rfl⟩
  have h1 : Nat.card SfAut = Nat.card ((Ssub : Set SU52) ×ˢ (Set.univ : Set Bool)) := by
    change Nat.card (SfAut : Set (MulAut SU52)) = _
    rw [e, Nat.card_image_of_injective psiAut_injective]
  rw [h1, Nat.card_congr (Equiv.Set.prod _ _), Nat.card_prod, Nat.card_univ,
    Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]
  change Nat.card Ssub * 2 = 2 ^ 11
  rw [card_Ssub]
  norm_num

theorem factorization_card_mulAut : (Nat.card (MulAut SU52)).factorization 2 = 11 := by
  have h10 : (Nat.card SU52).factorization 2 = 10 :=
    Nat.pow_right_injective le_rfl card_SU52.2
  have h0 : Nat.card SU52 ≠ 0 := by rw [card_SU52.1]; norm_num
  rw [card_mulAut_SU52, Nat.factorization_mul h0 (by norm_num), Finsupp.add_apply, h10,
    Nat.Prime.factorization_self Nat.prime_two]

theorem exists_sylow_SfAut : ∃ P : Sylow 2 (MulAut SU52), (P : Subgroup (MulAut SU52)) = SfAut :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  ⟨Sylow.ofCard SfAut (by rw [card_SfAut, factorization_card_mulAut]), rfl⟩

theorem fld_conj_mem_SfAut {α : MulAut SU52} (hα : α ∈ SfAut) : fld * α * fld⁻¹ ∈ SfAut :=
  mul_mem (mul_mem fld_mem_SfAut hα) (inv_mem fld_mem_SfAut)

theorem fld_mul_conj_mul_inv (n : SU52) : fld * MulAut.conj n * fld⁻¹ = MulAut.conj (fld n) := by
  rw [fld_mul_conj, fld_inv, mul_assoc, fld_mul_fld, mul_one]

theorem exists_conj_le_SfAut {D : Subgroup (MulAut SU52)} (hD : IsPGroup 2 D) :
    ∃ n : SU52, ∀ α ∈ D, MulAut.conj n * α * (MulAut.conj n)⁻¹ ∈ SfAut := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := hD.exists_le_sylow
  obtain ⟨P₀, hP₀⟩ := exists_sylow_SfAut
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq (MulAut SU52) P P₀
  have hconj : ∀ α ∈ D, a * α * a⁻¹ ∈ SfAut := by
    intro α hα
    rw [← hP₀, ← ha, Sylow.coe_subgroup_smul]
    exact (Subgroup.mem_smul_pointwise_iff_exists _ _ _).2 ⟨α, hP hα, rfl⟩
  obtain ⟨n, rfl | rfl⟩ := exists_eq_conj_or_eq_conj_mul_fld a
  · exact ⟨n, hconj⟩
  · refine ⟨fld n, fun α hα => ?_⟩
    have h := fld_conj_mem_SfAut (hconj α hα)
    rw [← fld_mul_conj_mul_inv]
    convert h using 1
    simp only [mul_inv_rev, fld_inv, mul_assoc]

theorem exists_conj_eq_fld_of_mem_SfAut {x : MulAut SU52}
    (hx : x ∈ SfAut) (hxo : fieldFactor x ≠ 1) (hx2 : x * x = 1) :
    ∃ m ∈ Ssub, MulAut.conj m * x * (MulAut.conj m)⁻¹ = fld := by
  obtain ⟨s, hs, rfl | rfl⟩ := hx
  · exact absurd (fieldFactor_conj s) hxo
  · have hs2 : s * fld s = 1 := by
      have e : MulAut.conj s * fld * (MulAut.conj s * fld) = MulAut.conj (s * fld s) := by
        rw [mul_assoc, ← mul_assoc fld, fld_mul_conj, mul_assoc, fld_mul_fld, mul_one,
          ← map_mul]
      rw [e, ← map_one MulAut.conj] at hx2
      exact conj_inj.1 hx2
    obtain ⟨m, hm, hms⟩ := exists_mul_eq_fld hs hs2
    refine ⟨m, hm, ?_⟩
    calc MulAut.conj m * (MulAut.conj s * fld) * (MulAut.conj m)⁻¹
        = MulAut.conj m * MulAut.conj s * (fld * MulAut.conj m⁻¹) := by rw [← map_inv]; group
      _ = MulAut.conj (m * s * fld m⁻¹) * fld := by rw [fld_mul_conj, map_mul, map_mul]; group
      _ = fld := by rw [hms, map_inv, mul_inv_cancel, map_one, one_mul]

theorem exists_conj_eq_fld {x : MulAut SU52}
    (hxo : fieldFactor x ≠ 1) (hx2 : x * x = 1) :
    ∃ n : SU52, MulAut.conj n * x * (MulAut.conj n)⁻¹ = fld := by
  have hz : IsPGroup 2 (zpowers x) := isPGroup_two_of_sq fun y hy => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
    rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, hx2, one_zpow]
  obtain ⟨n, hn⟩ := exists_conj_le_SfAut hz
  have hx' := hn x (mem_zpowers x)
  have hxo' : fieldFactor (MulAut.conj n * x * (MulAut.conj n)⁻¹) ≠ 1 := by
    rwa [map_mul, map_mul, map_inv, fieldFactor_conj, one_mul, inv_one, mul_one]
  have hx2' : MulAut.conj n * x * (MulAut.conj n)⁻¹ * (MulAut.conj n * x * (MulAut.conj n)⁻¹) =
      1 := by
    rw [show MulAut.conj n * x * (MulAut.conj n)⁻¹ * (MulAut.conj n * x * (MulAut.conj n)⁻¹) =
      MulAut.conj n * (x * x) * (MulAut.conj n)⁻¹ by group, hx2, mul_one, mul_inv_cancel]
  obtain ⟨m, -, hm⟩ := exists_conj_eq_fld_of_mem_SfAut hx' hxo' hx2'
  refine ⟨m * n, ?_⟩
  rw [← hm, map_mul]
  group

theorem fld_mem_X₁ {g : SU52} (hg : g ∈ X₁sub) : fld g ∈ X₁sub := by
  obtain ⟨a, b, hg⟩ := mem_X₁sub.1 hg
  exact mem_X₁sub.2 ⟨bar a, bar b, by rw [mat_fld, hg, x₁Mat_map_bar]⟩

theorem fld_mem_X₂ {g : SU52} (hg : g ∈ X₂sub) : fld g ∈ X₂sub := by
  obtain ⟨a, hg⟩ := mem_X₂sub.1 hg
  exact mem_X₂sub.2 ⟨bar a, by rw [mat_fld, hg, x₂Mat_map_bar]⟩

theorem fld_mem_X₃ {g : SU52} (hg : g ∈ X₃sub) : fld g ∈ X₃sub := by
  obtain ⟨a, hg⟩ := mem_X₃sub.1 hg
  exact mem_X₃sub.2 ⟨bar a, by rw [mat_fld, hg, x₃Mat_map_bar]⟩

theorem fld_mem_X₄ {g : SU52} (hg : g ∈ X₄sub) : fld g ∈ X₄sub := by
  obtain ⟨a, b, hg⟩ := mem_X₄sub.1 hg
  exact mem_X₄sub.2 ⟨bar a, bar b, by rw [mat_fld, hg, x₄Mat_map_bar]⟩

theorem eq_zero_of_valid_fixed : ∀ a b : F4, a * bar a = b + bar b → bar a = a → bar b = b →
    a = 0 := by
  simp only [bar_apply]
  decide

theorem card_CS_fld : Nat.card (Ssub ⊓ CfldSub : Subgroup SU52) = 2 ^ 4 := by
  have hfix₁ : ∀ g ∈ ZX₁sub, fld g = g := by
    intro g hg
    obtain ⟨a, b, ha, hg⟩ := mem_x₁Sub.1 hg
    subst ha
    have hb : bar b = b := by
      rcases eq_zero_or_one_of_valid b (x₁_coord_rel hg) with rfl | rfl
      · exact map_zero _
      · exact map_one _
    exact ext_mat (by rw [mat_fld, hg, x₁Mat_map_bar, map_zero, hb])
  have hfix₄ : ∀ g ∈ ZX₄sub, fld g = g := by
    intro g hg
    obtain ⟨a, b, ha, hg⟩ := mem_x₄Sub.1 hg
    subst ha
    have hb : bar b = b := by
      rcases eq_zero_or_one_of_valid b (x₄_coord_rel hg) with rfl | rfl
      · exact map_zero _
      · exact map_one _
    exact ext_mat (by rw [mat_fld, hg, x₄Mat_map_bar, map_zero, hb])
  have hfix₂ : ∀ g ∈ X₂zsub, fld g = g := by
    intro g hg
    obtain ⟨a, ha, hg⟩ := mem_x₂Sub.1 hg
    exact ext_mat (by rw [mat_fld, hg, x₂Mat_map_bar, ha])
  have hfix₃ : ∀ g ∈ X₃zsub, fld g = g := by
    intro g hg
    obtain ⟨a, ha, hg⟩ := mem_x₃Sub.1 hg
    exact ext_mat (by rw [mat_fld, hg, x₃Mat_map_bar, ha])
  have h := card_of_nf (H := Ssub ⊓ CfldSub) (Y₁ := ZX₁sub) (Y₂ := X₂zsub) (Y₃ := X₃zsub)
    (Y₄ := ZX₄sub) ZX₁sub_le_X₁sub
    (fun g hg => by obtain ⟨a, -, hg⟩ := mem_x₂Sub.1 hg; exact mem_X₂sub.2 ⟨a, hg⟩)
    (fun g hg => by obtain ⟨a, -, hg⟩ := mem_x₃Sub.1 hg; exact mem_X₃sub.2 ⟨a, hg⟩)
    ZX₄sub_le_X₄sub
    (fun y₁ hy₁ y₂ hy₂ y₃ hy₃ y₄ hy₄ => by
      refine ⟨mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_, ?_⟩
      · exact mem_sup_left (mem_sup_left (mem_sup_left (ZX₁sub_le_X₁sub hy₁)))
      · obtain ⟨a, -, hg⟩ := mem_x₂Sub.1 hy₂
        exact mem_sup_left (mem_sup_left (mem_sup_right (mem_X₂sub.2 ⟨a, hg⟩)))
      · obtain ⟨a, -, hg⟩ := mem_x₃Sub.1 hy₃
        exact mem_sup_left (mem_sup_right (mem_X₃sub.2 ⟨a, hg⟩))
      · exact mem_sup_right (ZX₄sub_le_X₄sub hy₄)
      · change fld (y₁ * y₂ * y₃ * y₄) = y₁ * y₂ * y₃ * y₄
        rw [map_mul, map_mul, map_mul, hfix₁ y₁ hy₁, hfix₂ y₂ hy₂, hfix₃ y₃ hy₃,
          hfix₄ y₄ hy₄])
    (fun g ⟨hgS, hgf⟩ => by
      obtain ⟨g₁, hg₁, g₂, hg₂, g₃, hg₃, g₄, hg₄, rfl⟩ := exists_eq_nf hgS
      have hf : fld (g₁ * g₂ * g₃ * g₄) = g₁ * g₂ * g₃ * g₄ := hgf
      rw [map_mul, map_mul, map_mul] at hf
      have hinj := @nf_injective ⟨⟨fld g₁, fld_mem_X₁ hg₁⟩, ⟨fld g₂, fld_mem_X₂ hg₂⟩,
        ⟨fld g₃, fld_mem_X₃ hg₃⟩, ⟨fld g₄, fld_mem_X₄ hg₄⟩⟩ ⟨⟨g₁, hg₁⟩, ⟨g₂, hg₂⟩, ⟨g₃, hg₃⟩,
        ⟨g₄, hg₄⟩⟩ hf
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at hinj
      obtain ⟨e₁, e₂, e₃, e₄⟩ := hinj
      obtain ⟨a₁, b₁, m₁⟩ := mem_X₁sub.1 hg₁
      obtain ⟨a₂, m₂⟩ := mem_X₂sub.1 hg₂
      obtain ⟨a₃, m₃⟩ := mem_X₃sub.1 hg₃
      obtain ⟨a₄, b₄, m₄⟩ := mem_X₄sub.1 hg₄
      have f₁ := x₁Mat_inj (by rw [← m₁, ← x₁Mat_map_bar, ← m₁, ← mat_fld, e₁] :
        x₁Mat (bar a₁) (bar b₁) = x₁Mat a₁ b₁)
      have f₂ := x₂Mat_inj (by rw [← m₂, ← x₂Mat_map_bar, ← m₂, ← mat_fld, e₂] :
        x₂Mat (bar a₂) = x₂Mat a₂)
      have f₃ := x₃Mat_inj (by rw [← m₃, ← x₃Mat_map_bar, ← m₃, ← mat_fld, e₃] :
        x₃Mat (bar a₃) = x₃Mat a₃)
      have f₄ := x₄Mat_inj (by rw [← m₄, ← x₄Mat_map_bar, ← m₄, ← mat_fld, e₄] :
        x₄Mat (bar a₄) (bar b₄) = x₄Mat a₄ b₄)
      have ha₁ := eq_zero_of_valid_fixed a₁ b₁ (x₁_coord_rel m₁) f₁.1 f₁.2
      have ha₄ := eq_zero_of_valid_fixed a₄ b₄ (x₄_coord_rel m₄) f₄.1 f₄.2
      exact ⟨g₁, mem_x₁Sub.2 ⟨a₁, b₁, ha₁, m₁⟩, g₂, mem_x₂Sub.2 ⟨a₂, f₂, m₂⟩, g₃,
        mem_x₃Sub.2 ⟨a₃, f₃, m₃⟩, g₄, mem_x₄Sub.2 ⟨a₄, b₄, ha₄, m₄⟩, rfl⟩)
  rw [h, card_ZX₁sub, card_X₂zsub, card_X₃zsub, card_ZX₄sub]
  norm_num

theorem mem_image_of_comm_fld {α : MulAut SU52} (hα : α ∈ SfAut) (hc : α * fld = fld * α) :
    α ∈ psiAut '' (((Ssub ⊓ CfldSub : Subgroup SU52) : Set SU52) ×ˢ Set.univ) := by
  obtain ⟨t, ht, b, rfl⟩ := mem_SfAut_iff.1 hα
  have hft : fld t = t := by
    have hb : fld * (if b then fld else 1) = (if b then fld else 1) * fld := by
      cases b <;> simp
    have e : MulAut.conj t * ((if b then fld else 1) * fld) =
        MulAut.conj (fld t) * ((if b then fld else 1) * fld) := by
      calc MulAut.conj t * ((if b then fld else 1) * fld) = psiAut (t, b) * fld := by
            simp only [psiAut, mul_assoc]
        _ = fld * psiAut (t, b) := hc
        _ = fld * MulAut.conj t * (if b then fld else 1) := by simp only [psiAut, mul_assoc]
        _ = MulAut.conj (fld t) * (fld * (if b then fld else 1)) := by
            rw [fld_mul_conj, mul_assoc]
        _ = MulAut.conj (fld t) * ((if b then fld else 1) * fld) := by rw [hb]
    exact (conj_inj.1 (mul_right_cancel e)).symm
  exact ⟨(t, b), ⟨⟨ht, hft⟩, Set.mem_univ _⟩, rfl⟩

theorem card_le_of_centralize_outer {D : Subgroup (MulAut SU52)}
    (hD : IsPGroup 2 D) {x : MulAut SU52} (hxD : x ∈ D) (hxo : fieldFactor x ≠ 1)
    (hx2 : x * x = 1) (hc : ∀ y ∈ D, y * x = x * y) : Nat.card D ≤ 2 ^ 5 := by
  obtain ⟨n, hn⟩ := exists_conj_le_SfAut hD
  have hxo' : fieldFactor (MulAut.conj n * x * (MulAut.conj n)⁻¹) ≠ 1 := by
    rwa [map_mul, map_mul, map_inv, fieldFactor_conj, one_mul, inv_one, mul_one]
  have hx2' : MulAut.conj n * x * (MulAut.conj n)⁻¹ * (MulAut.conj n * x * (MulAut.conj n)⁻¹) =
      1 := by
    rw [show MulAut.conj n * x * (MulAut.conj n)⁻¹ * (MulAut.conj n * x * (MulAut.conj n)⁻¹) =
      MulAut.conj n * (x * x) * (MulAut.conj n)⁻¹ by group, hx2, mul_one, mul_inv_cancel]
  obtain ⟨m, hm, hmx⟩ := exists_conj_eq_fld_of_mem_SfAut (hn x hxD) hxo' hx2'
  set k : MulAut SU52 := MulAut.conj m * MulAut.conj n with hk
  have hkD : ∀ y ∈ D, k * y * k⁻¹ ∈ psiAut '' (((Ssub ⊓ CfldSub : Subgroup SU52) : Set SU52) ×ˢ
      Set.univ) := by
    intro y hy
    refine mem_image_of_comm_fld ?_ ?_
    · have h1 := hn y hy
      have h2 : MulAut.conj m * (MulAut.conj n * y * (MulAut.conj n)⁻¹) * (MulAut.conj m)⁻¹ ∈
          SfAut := mul_mem (mul_mem (conj_mem_SfAut hm) h1) (inv_mem (conj_mem_SfAut hm))
      convert h2 using 1
      rw [hk]
      group
    · have hkx : k * x * k⁻¹ = fld := by rw [← hmx, hk]; group
      rw [← hkx]
      calc k * y * k⁻¹ * (k * x * k⁻¹) = k * (y * x) * k⁻¹ := by group
        _ = k * (x * y) * k⁻¹ := by rw [hc y hy]
        _ = k * x * k⁻¹ * (k * y * k⁻¹) := by group
  have hcard : Nat.card D = Nat.card (D.map (MulAut.conj k).toMonoidHom) :=
    (Subgroup.card_map_of_injective (MulAut.conj k).injective).symm
  have hsub : ((D.map (MulAut.conj k).toMonoidHom : Subgroup (MulAut SU52)) : Set (MulAut SU52)) ⊆
      psiAut '' (((Ssub ⊓ CfldSub : Subgroup SU52) : Set SU52) ×ˢ Set.univ) := by
    rintro _ ⟨y, hy, rfl⟩
    exact hkD y hy
  calc Nat.card D = Nat.card (D.map (MulAut.conj k).toMonoidHom) := hcard
    _ ≤ Nat.card (psiAut '' (((Ssub ⊓ CfldSub : Subgroup SU52) : Set SU52) ×ˢ Set.univ)) :=
        Nat.card_mono (Set.toFinite _) hsub
    _ ≤ Nat.card ((((Ssub ⊓ CfldSub : Subgroup SU52) : Set SU52) ×ˢ (Set.univ : Set Bool))) :=
        Nat.card_image_le (Set.toFinite _)
    _ = 2 ^ 5 := by
        rw [Nat.card_congr (Equiv.Set.prod _ _), Nat.card_prod, Nat.card_univ,
          Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]
        change Nat.card (Ssub ⊓ CfldSub : Subgroup SU52) * 2 = 2 ^ 5
        rw [card_CS_fld]
        norm_num

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
