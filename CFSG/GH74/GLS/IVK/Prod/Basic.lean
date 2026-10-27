module

public import CFSG.GH74.GLS.IVK.Statements.Sec3
public import CFSG.GH74.GLS.IVK.L2.SLConj

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.GorensteinWalter
open CFSG.Semidihedral

section SL

variable {F : Type} [Field F]

theorem sl_central_involution {K : Type*} [Group K]
    (φ : K ≃* Matrix.SpecialLinearGroup (Fin 2) F) (z : K) (hz : orderOf z = 2)
    (hc : ∀ k : K, k * z = z * k) :
    (2 : F) ≠ 0 ∧ φ z = OddFieldSL2.minusIdentity F := by
  have hcenter : φ z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨k, rfl⟩ := φ.surjective g
    rw [← map_mul, ← map_mul, hc k]
  have hz1 : φ z ≠ 1 := by
    intro h
    have : z = 1 := φ.injective (by rw [h, map_one])
    rw [this, orderOf_one] at hz
    omega
  rcases (ProjectiveSL2Cover.mem_center_iff_eq_one_or_minusIdentity F (φ z)).1 hcenter with h | h
  · exact absurd h hz1
  · have hm : φ z = OddFieldSL2.minusIdentity F := by
      rw [h, ProjectiveSL2Cover.minusIdentity_eq_neg_one]
      rfl
    refine ⟨?_, hm⟩
    intro h2
    apply hz1
    rw [hm]
    have hn : (-1 : F) = 1 := by linear_combination (-1 : F) * h2
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [OddFieldSL2.minusIdentity, hn]

end SL

section Prod

variable {H : Type} [Group H] {K₁ K₂ : Subgroup H} {F₁ F₂ : Type} [Field F₁] [Field F₂]

namespace ProdSL2

theorem symm (h : ProdSL2 H K₁ K₂ F₁ F₂) : ProdSL2 H K₂ K₁ F₂ F₁ where
  comm a ha b hb := (h.comm b hb a ha).symm
  iso₁ := h.iso₂
  iso₂ := h.iso₁
  card_inter := by rw [inf_comm]; exact h.card_inter
  fstar_normal := by rw [sup_comm]; exact h.fstar_normal
  fstar_centralizer := by rw [sup_comm]; exact h.fstar_centralizer

theorem mem_sup_iff (h : ProdSL2 H K₁ K₂ F₁ F₂) (x : H) :
    x ∈ K₁ ⊔ K₂ ↔ ∃ a ∈ K₁, ∃ b ∈ K₂, x = a * b := by
  constructor
  · intro hx
    let S : Subgroup H :=
      { carrier := {x | ∃ a ∈ K₁, ∃ b ∈ K₂, x = a * b}
        one_mem' := ⟨1, K₁.one_mem, 1, K₂.one_mem, by simp⟩
        mul_mem' := by
          rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
          refine ⟨a * a', K₁.mul_mem ha ha', b * b', K₂.mul_mem hb hb', ?_⟩
          calc a * b * (a' * b') = a * (b * a') * b' := by group
            _ = a * (a' * b) * b' := by rw [← h.comm a' ha' b hb]
            _ = a * a' * (b * b') := by group
        inv_mem' := by
          rintro _ ⟨a, ha, b, hb, rfl⟩
          refine ⟨a⁻¹, K₁.inv_mem ha, b⁻¹, K₂.inv_mem hb, ?_⟩
          have := h.comm a ha b⁻¹ (K₂.inv_mem hb)
          calc (a * b)⁻¹ = b⁻¹ * a⁻¹ := mul_inv_rev a b
            _ = a⁻¹ * b⁻¹ := by
              have h1 : a⁻¹ * b⁻¹ = (b * a)⁻¹ := (mul_inv_rev b a).symm
              rw [h1, ← h.comm a ha b hb, mul_inv_rev] }
    have hle : K₁ ⊔ K₂ ≤ S := sup_le (fun a ha => ⟨a, ha, 1, K₂.one_mem, by simp⟩)
      (fun b hb => ⟨1, K₁.one_mem, b, hb, by simp⟩)
    exact hle hx
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact Subgroup.mul_mem_sup ha hb

theorem inter_eq (h : ProdSL2 H K₁ K₂ F₁ F₂) {z : H} (hz : z ∈ K₁ ⊓ K₂) (hz1 : z ≠ 1) :
    K₁ ⊓ K₂ = zpowers z ∧ orderOf z = 2 := by
  have hfin : Finite ↥(K₁ ⊓ K₂) := Nat.finite_of_card_ne_zero (by rw [h.card_inter]; norm_num)
  have hdvd : orderOf (⟨z, hz⟩ : ↥(K₁ ⊓ K₂)) ∣ 2 := by
    rw [← h.card_inter]
    exact orderOf_dvd_natCard _
  have ho : orderOf z = 2 := by
    rw [Subgroup.orderOf_mk] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
    · exact absurd (orderOf_eq_one_iff.1 h1) hz1
    · exact h2
  refine ⟨?_, ho⟩
  symm
  apply Subgroup.eq_of_le_of_card_ge
  · rw [Subgroup.zpowers_le]; exact hz
  · rw [h.card_inter, Nat.card_zpowers, ho]

theorem inter_cases (h : ProdSL2 H K₁ K₂ F₁ F₂) {z : H} (hz : z ∈ K₁ ⊓ K₂) (hz1 : z ≠ 1) :
    ∀ w ∈ K₁ ⊓ K₂, w = 1 ∨ w = z := by
  obtain ⟨hint, hzo⟩ := h.inter_eq hz hz1
  intro w hw
  rw [hint] at hw
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
  have hk := zpow_mod_orderOf z k
  rw [hzo] at hk
  have hk' : (k % ((2 : ℕ) : ℤ)) = 0 ∨ (k % ((2 : ℕ) : ℤ)) = 1 := by omega
  rcases hk' with h0 | h1
  · left; rw [← hk, h0]; simp
  · right; rw [← hk, h1]; simp


noncomputable def slEquiv₁ (h : ProdSL2 H K₁ K₂ F₁ F₂) :
    ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F₁ :=
  h.iso₁.some.trans (specialLinearGroupEquivStatedSL 2 F₁).symm

theorem z_data₁ (h : ProdSL2 H K₁ K₂ F₁ F₂) {z : H} (hz : z ∈ K₁ ⊓ K₂) (hz1 : z ≠ 1) :
    (2 : F₁) ≠ 0 ∧ h.slEquiv₁ ⟨z, hz.1⟩ = OddFieldSL2.minusIdentity F₁ := by
  have ho := (h.inter_eq hz hz1).2
  refine sl_central_involution h.slEquiv₁ ⟨z, hz.1⟩ (by rw [Subgroup.orderOf_mk]; exact ho)
    (fun k => Subtype.ext (h.comm k.1 k.2 z hz.2))

theorem finite₁ [Finite H] (h : ProdSL2 H K₁ K₂ F₁ F₂) : Finite F₁ := by
  have : Finite (Matrix.SpecialLinearGroup (Fin 2) F₁) :=
    Finite.of_equiv ↥K₁ h.slEquiv₁.toEquiv
  exact Finite.of_injective (β := Matrix.SpecialLinearGroup (Fin 2) F₁)
    (fun t : F₁ => (⟨!![1, t; 0, 1], by simp⟩ : Matrix.SpecialLinearGroup (Fin 2) F₁)) (by
      intro s t hst
      have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F₁ =>
        (g : Matrix (Fin 2) (Fin 2) F₁) 0 1) hst
      simpa using this)

theorem eq_one_or_eq_z₁ (h : ProdSL2 H K₁ K₂ F₁ F₂) {z : H} (hz : z ∈ K₁ ⊓ K₂) (hz1 : z ≠ 1)
    {a : H} (ha : a ∈ K₁) (ha2 : a * a = 1) : a = 1 ∨ a = z := by
  obtain ⟨h2, hφz⟩ := h.z_data₁ hz hz1
  have hinv : (h.slEquiv₁ ⟨a, ha⟩)⁻¹ = h.slEquiv₁ ⟨a, ha⟩ := by
    rw [← map_inv]
    congr 1
    apply Subtype.ext
    exact inv_eq_of_mul_eq_one_right ha2
  rcases OddFieldSL2.eq_one_or_minusIdentity_of_inv_eq_self F₁ h2 _ hinv with h1 | h1
  · left
    have : (⟨a, ha⟩ : ↥K₁) = 1 := h.slEquiv₁.injective (by rw [h1, map_one])
    exact congrArg Subtype.val this
  · right
    have : (⟨a, ha⟩ : ↥K₁) = ⟨z, hz.1⟩ := h.slEquiv₁.injective (by rw [h1, hφz])
    exact congrArg Subtype.val this

theorem exists_conj₁ [Finite H] (h : ProdSL2 H K₁ K₂ F₁ F₂) {z : H} (hz : z ∈ K₁ ⊓ K₂) (hz1 : z ≠ 1)
    {a a' : H} (ha : a ∈ K₁) (ha' : a' ∈ K₁) (haz : a * a = z) (ha'z : a' * a' = z) :
    ∃ g ∈ K₁, g * a * g⁻¹ = a' := by
  have := h.finite₁
  obtain ⟨h2, hφz⟩ := h.z_data₁ hz hz1
  have hF : ringChar F₁ ≠ 2 := by
    intro hc
    apply h2
    have := CharP.cast_eq_zero F₁ (ringChar F₁)
    rw [hc] at this
    exact_mod_cast this
  have hx : h.slEquiv₁ ⟨a, ha⟩ * h.slEquiv₁ ⟨a, ha⟩ = OddFieldSL2.minusIdentity F₁ := by
    rw [← map_mul, ← hφz]
    congr 1
    exact Subtype.ext haz
  have hy : h.slEquiv₁ ⟨a', ha'⟩ * h.slEquiv₁ ⟨a', ha'⟩ = OddFieldSL2.minusIdentity F₁ := by
    rw [← map_mul, ← hφz]
    congr 1
    exact Subtype.ext ha'z
  obtain ⟨g, hg⟩ := L2Torus.exists_sl_conj_of_sq_eq_neg_one hF h2 _ _ hx hy
  refine ⟨((h.slEquiv₁.symm g : ↥K₁) : H), (h.slEquiv₁.symm g).2, ?_⟩
  have : h.slEquiv₁.symm g * ⟨a, ha⟩ * (h.slEquiv₁.symm g)⁻¹ = ⟨a', ha'⟩ := by
    apply h.slEquiv₁.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hg]
  exact congrArg Subtype.val this


theorem swap_mem₁ {t : H} (hK : K₁.map (MulAut.conj t).toMonoidHom = K₂) {a : H} (ha : a ∈ K₁) :
    t * a * t⁻¹ ∈ K₂ := by
  rw [← hK]
  exact ⟨a, ha, rfl⟩

theorem swap_mem₂ {t : H} (ht2 : t * t = 1) (hK : K₁.map (MulAut.conj t).toMonoidHom = K₂)
    {b : H} (hb : b ∈ K₂) : t * b * t⁻¹ ∈ K₁ := by
  rw [← hK] at hb
  obtain ⟨a, ha, rfl⟩ := hb
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have : t * ((MulAut.conj t).toMonoidHom a) * t⁻¹ = a := by
    show t * (t * a * t⁻¹) * t⁻¹ = a
    rw [hti]
    calc t * (t * a * t) * t = (t * t) * a * (t * t) := by group
      _ = a := by rw [ht2]; group
  rw [this]
  exact ha

theorem t_comm_z (h : ProdSL2 H K₁ K₂ F₁ F₂) {z : H} (hz : z ∈ K₁ ⊓ K₂) (hz1 : z ≠ 1) {t : H}
    (ht2 : t * t = 1) (hK : K₁.map (MulAut.conj t).toMonoidHom = K₂) : t * z * t⁻¹ = z := by
  have hmem : t * z * t⁻¹ ∈ K₁ ⊓ K₂ := ⟨swap_mem₂ ht2 hK hz.2, swap_mem₁ hK hz.1⟩
  have hne : t * z * t⁻¹ ≠ 1 := by
    intro h1
    apply hz1
    have : z = t⁻¹ * (t * z * t⁻¹) * t := by group
    rw [this, h1]
    group
  exact (h.inter_cases hz hz1 _ hmem).resolve_left hne


theorem z_comm (h : ProdSL2 H K₁ K₂ F₁ F₂) {z : H} (hz : z ∈ K₁ ⊓ K₂) {x : H}
    (hx : x ∈ K₁ ⊔ K₂) : z * x = x * z := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (h.mem_sup_iff x).1 hx
  have h1 : z * a = a * z := (h.comm a ha z hz.2).symm
  have h2 : z * b = b * z := h.comm z hz.1 b hb
  calc z * (a * b) = (z * a) * b := by group
    _ = a * (z * b) := by rw [h1]; group
    _ = a * (b * z) := by rw [h2]
    _ = a * b * z := by group


end ProdSL2

end Prod

end CFSG.GH74.GLS.IVK
