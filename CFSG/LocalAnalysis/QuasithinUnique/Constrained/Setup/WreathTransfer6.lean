module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellSeed
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathTransfer4

public section

namespace CFSG.QuasithinUnique.Setup.Wreath

open scoped Pointwise commutatorElement
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Campbell

section Finite

variable {H : Type*} [Group H] [Finite H] {R M V W F : Subgroup H} {r : ℕ} {I : Fin r → Subgroup H}
  {Pm : Subgroup (Equiv.Perm (Fin r))} (h : WreathHyp R M V W F I Pm)

namespace WreathHyp

variable {t : ∀ i, MulAut ↥(planesIn W I i)}

include h

@[expose] def rhoV : H →* MulAut ↥V :=
  have := h.V_normal
  MulAut.conjNormal

omit [Finite H] in
theorem rhoV_apply (x : H) (v : ↥V) : ((h.rhoV x v : ↥V) : H) = x * v * x⁻¹ := by
  have := h.V_normal
  exact MulAut.conjNormal_apply x v

omit [Finite H] in
theorem ker_rhoV : h.rhoV.ker = Subgroup.centralizer (V : Set H) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx v hv
    have h1 := congrArg (fun a : MulAut ↥V => ((a ⟨v, hv⟩ : ↥V) : H)) hx
    simp only [h.rhoV_apply, MulAut.one_apply] at h1
    have h2 : x * v = v * x := by
      calc x * v = (x * v * x⁻¹) * x := by group
        _ = v * x := by rw [h1]
    exact h2.symm
  · intro hx
    refine MulEquiv.ext fun v => Subtype.ext ?_
    show ((h.rhoV x v : ↥V) : H) = (v : H)
    rw [h.rhoV_apply]
    have := hx v v.2
    calc x * (v : H) * x⁻¹ = (v : H) * x * x⁻¹ := by rw [this]
      _ = (v : H) := by group

theorem exists_g_odd : ∃ g ∈ oddOrderSubgroup (⊤ : Subgroup H),
    h.rho g ∈ h.D ∧ ∀ i, ∃ x ∈ planesIn W I i, h.rho g x ≠ x := by
  let _ := h.cg
  obtain ⟨δ, hδ, hδnt⟩ := exists_cubeBase_nontrivial h.planeFamily
  have hδ' : δ ∈ (oddOrderSubgroup (⊤ : Subgroup H)).map h.rho := by
    rw [h.rho_map_odd]
    exact hδ
  obtain ⟨g, hg, rfl⟩ := hδ'
  exact ⟨g, hg, hδ, hδnt⟩

omit [Finite H] in
theorem rho_conjugate_map (X : Subgroup H) (g : H) :
    (conjugate X g).map h.rho = (X.map h.rho).map (MulAut.conj (h.rho g)⁻¹).toMonoidHom := by
  unfold conjugate
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [map_mul, map_inv]

theorem rhoV_odd_le (ht : h.IsT0 t) {g : H} (hgnt : ∀ i, ∃ x ∈ planesIn W I i, h.rho g x ≠ x)
    (hgD : h.rho g ∈ h.D) :
    (oddOrderSubgroup (⊤ : Subgroup H)).map h.rhoV ≤
      (thompsonJ R ⊔ conjugate (thompsonJ R) g).map h.rhoV := by
  let _ := h.cg
  rintro _ ⟨n, hn, rfl⟩
  have hnD : h.rho n ∈ h.D := by
    rw [← h.rho_map_odd]
    exact ⟨n, hn, rfl⟩
  have hle := cubeBase_le_sup_conj h.planeFamily ht hgD hgnt
  have hmem : h.rho n ∈ (thompsonJ R ⊔ conjugate (thompsonJ R) g).map h.rho := by
    rw [Subgroup.map_sup, h.rho_conjugate_map, h.rho_J_eq_T0 ht]
    exact hle hnD
  obtain ⟨y, hy, hyn⟩ := hmem
  refine ⟨y, hy, ?_⟩
  have hker : y⁻¹ * n ∈ h.rho.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hyn]
    group
  rw [h.ker_rho_eq_centralizer_V, ← h.ker_rhoV, MonoidHom.mem_ker, map_mul, map_inv] at hker
  exact (inv_mul_eq_one.mp hker)

theorem card_V_eq : Nat.card ↥V = Nat.card ↥W * Nat.card ↥F := by
  have hc : ∀ x ∈ W, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    (isElemAbelian_iff.mp h.V_elem).1 x (h.W_le hx) y (h.F_le hy)
  have := card_sup_mul_card_inf hc
  rwa [h.W_sup_F, h.W_inf_F, Subgroup.card_bot, mul_one] at this

omit [Finite H] in
theorem card_W_eq : Nat.card ↥W = 4 ^ r := by
  let _ := h.cg
  have := h.planeFamily.card_W
  rwa [Fintype.card_fin] at this

theorem relIndex_F : F.relIndex V = 4 ^ r := by
  have h1 := Subgroup.relIndex_mul_card F V
  rw [inf_of_le_left h.F_le, h.card_V_eq, h.card_W_eq] at h1
  have hF : 0 < Nat.card ↥F := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hF h1

omit [Finite H] in
theorem V_inf_centralizer_eq {X : Subgroup H} (hX : ∀ x ∈ X, ∀ f ∈ F, x * f = f * x) :
    V ⊓ Subgroup.centralizer (X : Set H) = (W ⊓ Subgroup.centralizer (X : Set H)) ⊔ F := by
  apply le_antisymm
  · rintro v ⟨hv, hvc⟩
    have hv' : v ∈ W ⊔ F := h.W_sup_F ▸ hv
    obtain ⟨w, hw, f, hf, rfl⟩ :=
      CFSG.QuasithinUnique.Setup.Layer.mem_sup_mul (normal_le_normalizer' h.W_normal F) hv'
    have hwc : w ∈ Subgroup.centralizer (X : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h1 := Subgroup.mem_centralizer_iff.mp hvc x hx
      have h2 := hX x hx f hf
      have : x * w * f = w * x * f := by
        calc x * w * f = x * (w * f) := mul_assoc _ _ _
          _ = (w * f) * x := h1
          _ = w * (f * x) := mul_assoc _ _ _
          _ = w * (x * f) := by rw [h2]
          _ = w * x * f := (mul_assoc _ _ _).symm
      exact mul_right_cancel this
    exact Subgroup.mul_mem_sup ⟨hw, hwc⟩ hf
  · exact sup_le (inf_le_inf_right _ h.W_le) fun f hf =>
      ⟨h.F_le hf, Subgroup.mem_centralizer_iff.mpr fun x hx => hX x hx f hf⟩

theorem relIndex_V_inf_centralizer {X : Subgroup H} (hX : ∀ x ∈ X, ∀ f ∈ F, x * f = f * x) :
    (V ⊓ Subgroup.centralizer (X : Set H)).relIndex V *
      Nat.card ↥(W ⊓ Subgroup.centralizer (X : Set H)) = Nat.card ↥W := by
  set K := V ⊓ Subgroup.centralizer (X : Set H) with hK
  have hKV : K ≤ V := inf_le_left
  have h1 := Subgroup.relIndex_mul_card K V
  rw [inf_of_le_left hKV] at h1
  have hc : ∀ x ∈ W ⊓ Subgroup.centralizer (X : Set H), ∀ y ∈ F, x * y = y * x :=
    fun x hx y hy => (isElemAbelian_iff.mp h.V_elem).1 x (h.W_le hx.1) y (h.F_le hy)
  have h2 := card_sup_mul_card_inf hc
  have h3 : (W ⊓ Subgroup.centralizer (X : Set H)) ⊓ F = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ W ⊓ F := ⟨hx.1.1, hx.2⟩
    rw [h.W_inf_F] at this
    exact this
  rw [h3, Subgroup.card_bot, mul_one, ← h.V_inf_centralizer_eq hX] at h2
  rw [h2, h.card_V_eq] at h1
  have hF : 0 < Nat.card ↥F := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hF ?_
  rw [mul_assoc]
  exact h1

theorem J_centralizes_F (ht : h.IsT0 t) : ∀ x ∈ thompsonJ R, ∀ f ∈ F, x * f = f * x := by
  let _ := h.cg
  intro x hx f hf
  have hρ : h.rho x ∈ h.B := (h.rho_J_le_T0 ht ⟨x, hx, rfl⟩).2
  exact h.centralizes x (h.conj_planes_of_rho_mem_B hρ) f hf

theorem card_W_inf_centralizer_J (ht : h.IsT0 t) :
    Nat.card ↥(W ⊓ Subgroup.centralizer ((thompsonJ R : Subgroup H) : Set H)) = 2 ^ r := by
  let _ := h.cg
  rw [← h.card_fixV_map_rho, h.rho_J_eq_T0 ht, ht.card_fixV h.planeFamily]
  simp only [Fintype.card_fin, Finset.card_univ]
  congr 1
  omega

theorem relIndex_J (ht : h.IsT0 t) :
    (V ⊓ Subgroup.centralizer ((thompsonJ R : Subgroup H) : Set H)).relIndex V = 2 ^ r := by
  have h1 := h.relIndex_V_inf_centralizer (X := thompsonJ R) (h.J_centralizes_F ht)
  rw [h.card_W_inf_centralizer_J ht, h.card_W_eq] at h1
  have h4 : (4 : ℕ) ^ r = 2 ^ r * 2 ^ r := by
    rw [← mul_pow]
    norm_num
  rw [h4] at h1
  exact Nat.eq_of_mul_eq_mul_right (pow_pos two_pos r) h1

theorem conjugate_J_centralizes_F (ht : h.IsT0 t) {g : H}
    (hg : ∀ f ∈ F, g * f = f * g) :
    ∀ x ∈ conjugate (thompsonJ R) g, ∀ f ∈ F, x * f = f * x := by
  intro x hx f hf
  have hx' : g * x * g⁻¹ ∈ thompsonJ R := mem_cj.mp hx
  have h1 : (g * x * g⁻¹) * f = f * (g * x * g⁻¹) := h.J_centralizes_F ht _ hx' f hf
  have hgf := hg f hf
  have hgf' : g⁻¹ * f * g = f := by
    rw [mul_assoc, ← hgf]
    group
  calc x * f = (g⁻¹ * (g * x * g⁻¹) * g) * (g⁻¹ * f * g) := by rw [hgf']; group
    _ = g⁻¹ * ((g * x * g⁻¹) * f) * g := by group
    _ = g⁻¹ * (f * (g * x * g⁻¹)) * g := by rw [h1]
    _ = (g⁻¹ * f * g) * (g⁻¹ * (g * x * g⁻¹) * g) := by group
    _ = f * x := by rw [hgf']; group

theorem card_W_inf_centralizer_conjugate_J (ht : h.IsT0 t) (g : H) :
    Nat.card ↥(W ⊓ Subgroup.centralizer ((conjugate (thompsonJ R) g : Subgroup H) : Set H)) =
      2 ^ r := by
  have := h.W_normal
  have e : W ⊓ Subgroup.centralizer ((conjugate (thompsonJ R) g : Subgroup H) : Set H) =
      cj (W ⊓ Subgroup.centralizer ((thompsonJ R : Subgroup H) : Set H)) g := by
    rw [cj_inf, cj_eq_self_of_normal (Y := W)]
    exact congrArg _ (centralizer_cj (thompsonJ R) g)
  rw [e, card_cj]
  exact h.card_W_inf_centralizer_J ht

theorem relIndex_conjugate_J (ht : h.IsT0 t) {g : H} (hg : ∀ f ∈ F, g * f = f * g) :
    (V ⊓ Subgroup.centralizer ((conjugate (thompsonJ R) g : Subgroup H) : Set H)).relIndex V =
      2 ^ r := by
  have h1 := h.relIndex_V_inf_centralizer (X := conjugate (thompsonJ R) g)
    (h.conjugate_J_centralizes_F ht hg)
  rw [h.card_W_inf_centralizer_conjugate_J ht, h.card_W_eq] at h1
  have h4 : (4 : ℕ) ^ r = 2 ^ r * 2 ^ r := by
    rw [← mul_pow]
    norm_num
  rw [h4] at h1
  exact Nat.eq_of_mul_eq_mul_right (pow_pos two_pos r) h1

end WreathHyp

end Finite

end CFSG.QuasithinUnique.Setup.Wreath
