module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Glue78
public import CFSG.CharacterTheory.Semidihedral.NormalForm
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Glue74b

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec7

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G} {t u : G} {q : ℕ}

omit [Finite G] in
theorem orderOf_eq_two_of_isConj {a x : G} (ha : orderOf a = 2) (hx : IsConj a x) : orderOf x = 2 := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hx
  rw [← hc]
  have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective a
  simpa [MulAut.conj_apply, ha] using this

omit [Finite G] in
theorem four_le_orderOf {S : Subgroup G} (hS : IsPGroup 2 ↥S) {w : G} (hw : w ∈ S) (h1 : w ≠ 1)
    (h2 : orderOf w ≠ 2) : 4 ≤ orderOf w := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hS) ⟨w, hw⟩
  have hk' : orderOf w = 2 ^ k := by
    rw [← hk]
    exact Subgroup.orderOf_coe (⟨w, hw⟩ : ↥S)
  rcases k with _ | _ | k
  · exact absurd (orderOf_eq_one_iff.1 (by simpa using hk')) h1
  · exact absurd (by simpa using hk') h2
  · rw [hk', pow_succ, pow_succ]
    have : 0 < 2 ^ k := by positivity
    omega

namespace Cfg7

theorem S₀_elems (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) {x : G}
    (hx : x ∈ Pz S z ⊔ zpowers t) : x ∈ Pz S z ∨ ∃ p ∈ Pz S z, x = p * t := by
  rw [h.Pz_eq_sup hII] at hx ⊢
  exact h.Y0_elems hII hx

theorem normP (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) :
    ∀ s ∈ S, ∀ x ∈ Pz S z, s * x * s⁻¹ ∈ Pz S z := by
  intro s hs x hx
  rw [h.Pz_eq_sup hII] at hx ⊢
  exact h.S_normalizes_P hII s hs x hx

omit [Finite G] in
theorem mem_C_of_conj {g : G} (hgz : g⁻¹ * z * g = z) : g ∈ centralizer ({z} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc g * z = g * (g⁻¹ * z * g) := by rw [hgz]
    _ = z * g := by group

theorem PQ_le_XK (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) {K : Subgroup G} :
    Pof S K ⊔ Qof S K ≤ XK z K :=
  sup_le (fun _ ha => mem_sup_left ha.2)
    (fun _ ha => mem_sup_right ⟨ha.2, (h.m4 hII).S_syl.1 ha.1⟩)

theorem P_of_conj (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) (hc73 : Concl73 z S K₁ K₂)
    {x g : G} (hxS : x ∈ S) (hgz : g⁻¹ * z * g = z) (hxg : g⁻¹ * x * g ∈ Pz S z) : x ∈ Pz S z := by
  have hM := h.m4 hII
  have hgC : g ∈ centralizer ({z} : Set G) := mem_C_of_conj hgz
  have hgC' : g⁻¹ ∈ centralizer ({z} : Set G) := inv_mem hgC
  have hx₁ : g⁻¹ * x * g ∈ XK z K₁ := by
    have : Pz S z ≤ XK z K₁ := by
      rw [← h.PQ_eq hII hc73 (Or.inl rfl)]
      exact h.PQ_le_XK hII
    exact this hxg
  have key : g⁻¹ * x * g ∈ XK z K₁ ↔ x ∈ XK z (cmap g K₁) := by
    rw [← cmap_XK hgC K₁, mem_cmap]
  rw [key] at hx₁
  have hswap : cmap g K₁ = K₁ ∨ cmap g K₁ = K₂ := by
    simp only [cmap_eq_cj]
    rcases hM.perm g⁻¹ hgC' with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inl h1
    · exact Or.inr h1
  rcases hswap with h1 | h1
  · rw [h1] at hx₁
    have := h.inf_XK_le hII (Or.inl rfl) x hxS hx₁
    rwa [h.PQ_eq hII hc73 (Or.inl rfl)] at this
  · rw [h1] at hx₁
    have := h.inf_XK_le hII (Or.inr rfl) x hxS hx₁
    rwa [h.PQ_eq hII hc73 (Or.inr rfl)] at this

theorem S1_conj (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) {x g : G} (hxS₁ : x ∈ S1 S K₁)
    (hgz : g⁻¹ * z * g = z) (hxg : g⁻¹ * x * g ∈ S) : g⁻¹ * x * g ∈ S1 S K₁ := by
  have hgC' : g⁻¹ ∈ centralizer ({z} : Set G) := inv_mem (mem_C_of_conj hgz)
  have := h.Hs_normal hII (Or.inl rfl) g⁻¹ hgC' x
    (Subgroup.mem_inf.2 ⟨h.S_le_C hII hxS₁.1, hxS₁.2⟩)
  rw [inv_inv] at this
  exact ⟨hxg, this.2⟩

theorem card_P₁_eq_P₂ (h : Cfg7 G z S K₁ K₂ t u q) : Nat.card ↥(Pof S K₁) = Nat.card ↥(Pof S K₂) := by
  apply le_antisymm
  · refine Nat.card_le_card_of_injective
      (fun x : ↥(Pof S K₁) => (⟨t * x * t⁻¹, h.tP₁ x x.2⟩ : ↥(Pof S K₂))) ?_
    intro x y hxy
    have h1 := congrArg Subtype.val hxy
    simp only [mul_left_inj, mul_right_inj] at h1
    exact Subtype.ext h1
  · refine Nat.card_le_card_of_injective
      (fun x : ↥(Pof S K₂) => (⟨t * x * t⁻¹, h.tP₂ x x.2⟩ : ↥(Pof S K₁))) ?_
    intro x y hxy
    have h1 := congrArg Subtype.val hxy
    simp only [mul_left_inj, mul_right_inj] at h1
    exact Subtype.ext h1

theorem card_D (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q)
    (hidx : (Pz S z).relIndex (S1 S K₁) = 2) {D : Subgroup G} (hD : Data74 z S K₁ K₂ t D) :
    Nat.card ↥D = Nat.card ↥(Pof S K₁) := by
  obtain ⟨hN, ⟨e⟩⟩ := hD.quot
  have hPS₁ : Pof S K₁ ≤ S1 S K₁ := h.P₁_le_S1
  have h1 : Nat.card ↥(S1 S K₁) = Nat.card ↥(Pof S K₁) * Nat.card ↥D := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ((Pof S K₁).subgroupOf (S1 S K₁))]
    rw [Nat.card_congr e.toEquiv, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPS₁).toEquiv, mul_comm]
  have h2 := A.card_eq_two_mul_of_relIndex_two (h.Pz_le_S1 hII) hidx
  have h3 := A.card_sup_mul_card_inf_of_commute (h.P_comm hII)
  rw [← h.Pz_eq_sup hII, h.P_inf hII, Nat.card_zpowers, h.std.std.orderOf_z] at h3
  have h4 := h.card_P₁_eq_P₂
  have hpos : 0 < Nat.card ↥(Pof S K₁) := Nat.card_pos
  have h5 : Nat.card ↥(Pof S K₁) * Nat.card ↥D = Nat.card ↥(Pof S K₁) * Nat.card ↥(Pof S K₁) := by
    rw [← h1, h2]
    rw [← h4] at h3
    linarith
  exact Nat.eq_of_mul_eq_mul_left hpos h5

theorem sd_card_ge (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q)
    (hidx : (Pz S z).relIndex (S1 S K₁) = 2) {D : Subgroup G} (hD : Data74 z S K₁ K₂ t D)
    (hsd : ∃ n, IVK.IsSemidihedralTwoGroup ↥D n) : 16 ≤ Nat.card ↥(Pof S K₁) := by
  obtain ⟨n, hn, ⟨e⟩⟩ := hsd
  have h1 : Nat.card ↥D = 2 ^ n := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Semidihedral.card n (by omega)
  rw [← h.card_D hII hidx hD, h1]
  calc 16 = 2 ^ 4 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

end Cfg7

end CFSG.GH74.GLS.Stage1.Thm3.Sec7
