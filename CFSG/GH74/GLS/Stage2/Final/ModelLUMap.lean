module

public import CFSG.GH74.GLS.Stage2.Final.ModelLUTransport
public import CFSG.GH74.GLS.Stage2.Final.ModelOneClass
public import CFSG.GH74.GLS.LU.Local.Setup
public import CFSG.GH74.GLS.SP.Local.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelLUT

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.Stage2.Final.ModelBlock

variable {G H : Type} [Group G] [Group H]

theorem mem_map_iff_symm (Φ : G ≃* H) (K : Subgroup G) (x : G) :
    Φ x ∈ K.map Φ.toMonoidHom ↔ x ∈ K := by
  rw [Subgroup.mem_map_equiv]
  simp

theorem conj_map_comp (Φ : G ≃* H) (t : G) :
    (MulAut.conj (Φ t)).toMonoidHom.comp Φ.toMonoidHom =
      Φ.toMonoidHom.comp (MulAut.conj t).toMonoidHom := by
  ext x; simp [map_mul]

theorem swap_map (Φ : G ≃* H) {K₁ K₂ : Subgroup G} {t : G}
    (h : K₁.map (MulAut.conj t).toMonoidHom = K₂) :
    (K₁.map Φ.toMonoidHom).map (MulAut.conj (Φ t)).toMonoidHom = K₂.map Φ.toMonoidHom := by
  rw [Subgroup.map_map, conj_map_comp, ← Subgroup.map_map, h]

theorem normalizer_map (Φ : G ≃* H) {K : Subgroup G} {u : G}
    (h : u ∈ Subgroup.normalizer (K : Set G)) :
    Φ u ∈ Subgroup.normalizer ((K.map Φ.toMonoidHom : Subgroup H) : Set H) := by
  rw [Subgroup.mem_normalizer_iff] at h ⊢
  intro y
  obtain ⟨x, rfl⟩ := Φ.surjective y
  rw [mem_map_iff_symm]
  have : Φ u * Φ x * (Φ u)⁻¹ = Φ (u * x * u⁻¹) := by simp [map_mul]
  rw [this, mem_map_iff_symm]
  exact h x

theorem not_normalizer_of_map (Φ : G ≃* H) {K : Subgroup G} {s : G}
    (h : Φ s ∉ Subgroup.normalizer ((K.map Φ.toMonoidHom : Subgroup H) : Set H)) :
    s ∉ Subgroup.normalizer (K : Set G) := fun hs => h (normalizer_map Φ hs)

theorem luSyl_map [Finite G] [Finite H] (Φ : G ≃* H) {z : G} {S : Sylow 2 G} {S' : Sylow 2 H}
    (hS : (S' : Subgroup H) = (S : Subgroup G).map Φ.toMonoidHom) {K₁ K₂ : Subgroup G} {t u : G}
    (h : LUSyl G z S K₁ K₂ t u) :
    LUSyl H (Φ z) S' (K₁.map Φ.toMonoidHom) (K₂.map Φ.toMonoidHom) (Φ t) (Φ u) := by
  have hmem : ∀ x : G, x ∈ (S : Subgroup G) → Φ x ∈ (S' : Subgroup H) := fun x hx => by
    rw [hS]; exact ⟨x, hx, rfl⟩
  have hmem' : ∀ y : H, y ∈ (S' : Subgroup H) → ∃ x : G, x ∈ (S : Subgroup G) ∧ Φ x = y := by
    intro y hy
    rw [hS] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, hx, rfl⟩
  refine ⟨?_, ?_, hmem t h.t_mem, MonoidHom.map_isConj Φ.toMonoidHom h.t_conj, swap_map Φ h.t_swap,
    hmem u h.u_mem, ?_, ?_, MonoidHom.map_isConj Φ.toMonoidHom h.u_conj, ?_, normalizer_map Φ h.u_norm,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq]; exact h.z_inv
  · have h1 := ((centerIs_iff _ _).1 h.z_cen).map_equiv Φ
    rw [← hS] at h1
    exact (centerIs_iff _ _).2 h1
  · rw [MulEquiv.orderOf_eq]; exact h.u_ord
  · intro heq; exact h.u_ne (Φ.injective heq)
  · have := MonoidHom.map_isConj Φ.toMonoidHom h.uz_conj
    simpa [map_mul] using this
  · rw [← map_mul, ← map_mul, h.ut]
  · intro s' hs' hsn
    obtain ⟨s, hs, rfl⟩ := hmem' s' hs'
    obtain ⟨k, hk, hkc⟩ := h.coset s hs (not_normalizer_of_map Φ hsn)
    refine ⟨Φ k, ⟨hmem k hk.1, ?_⟩, ?_⟩
    · rw [← Subgroup.map_sup]
      exact ⟨k, hk.2, rfl⟩
    · have := MonoidHom.map_isConj Φ.toMonoidHom hkc
      simpa [map_mul] using this
  · intro s' hs' hc
    obtain ⟨s, hs, rfl⟩ := hmem' s' hs'
    have hc' : ∀ k ∈ K₁ ⊔ K₂, s * k = k * s := by
      intro k hk
      apply Φ.injective
      rw [map_mul, map_mul]
      apply hc
      rw [← Subgroup.map_sup]
      exact ⟨k, hk, rfl⟩
    have := h.cs s hs hc'
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 this
    exact Subgroup.mem_zpowers_iff.2 ⟨n, by rw [← hn, map_zpow]⟩
  · have h1 : Nat.card (S' : Subgroup H) = Nat.card (S : Subgroup G) := by
      rw [hS]; exact Subgroup.card_map_of_injective Φ.injective
    have h2 : (S' : Subgroup H) ⊓ (K₁.map Φ.toMonoidHom ⊔ K₂.map Φ.toMonoidHom) =
        ((S : Subgroup G) ⊓ (K₁ ⊔ K₂)).map Φ.toMonoidHom := by
      rw [Subgroup.map_inf _ _ _ Φ.injective, Subgroup.map_sup, hS]
    have h3 : Nat.card ↥((S' : Subgroup H) ⊓ (K₁.map Φ.toMonoidHom ⊔ K₂.map Φ.toMonoidHom)) =
        Nat.card ↥((S : Subgroup G) ⊓ (K₁ ⊔ K₂)) := by
      rw [h2]; exact Subgroup.card_map_of_injective Φ.injective
    rw [h1, h3]; exact h.card_S
  · rw [hS]; exact LUCenAb.map Φ h.cen_ab

theorem spSyl_map [Finite G] [Finite H] (Φ : G ≃* H) {z : G} {S : Sylow 2 G} {S' : Sylow 2 H}
    (hS : (S' : Subgroup H) = (S : Subgroup G).map Φ.toMonoidHom) {K₁ K₂ : Subgroup G} {t : G}
    (h : CFSG.GH74.GLS.SP.Local.SPSyl G z S K₁ K₂ t) :
    CFSG.GH74.GLS.SP.Local.SPSyl H (Φ z) S' (K₁.map Φ.toMonoidHom) (K₂.map Φ.toMonoidHom) (Φ t) := by
  have hmem : ∀ x : G, x ∈ (S : Subgroup G) → Φ x ∈ (S' : Subgroup H) := fun x hx => by
    rw [hS]; exact ⟨x, hx, rfl⟩
  refine ⟨?_, ?_, hmem t h.t_mem, ?_, swap_map Φ h.t_swap, ?_, ?_, ?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq]; exact h.z_inv
  · have h1 := ((centerIs_iff _ _).1 h.z_cen).map_equiv Φ
    rw [← hS] at h1
    exact (centerIs_iff _ _).2 h1
  · rw [MulEquiv.orderOf_eq]; exact h.t_ord
  · intro hc
    exact h.t_nconj (isConj_of_equiv Φ hc)
  · have := MonoidHom.map_isConj Φ.toMonoidHom h.tz_conj
    simpa [map_mul] using this
  · intro x hx y hy hx2 hy2 hxz hyz
    rw [← Subgroup.map_sup] at hx hy
    obtain ⟨x₀, hx₀, rfl⟩ := hx
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    change orderOf (Φ x₀) = 2 at hx2
    change orderOf (Φ y₀) = 2 at hy2
    change Φ x₀ ≠ Φ z at hxz
    change Φ y₀ ≠ Φ z at hyz
    rw [MulEquiv.orderOf_eq] at hx2 hy2
    have hx₀z : x₀ ≠ z := fun e => hxz (by rw [e])
    have hy₀z : y₀ ≠ z := fun e => hyz (by rw [e])
    obtain ⟨k, hk, hkx⟩ := h.K_one_class x₀ hx₀ y₀ hy₀ hx2 hy2 hx₀z hy₀z
    refine ⟨Φ k, ?_, ?_⟩
    · rw [← Subgroup.map_sup]; exact ⟨k, hk, rfl⟩
    · have : Φ (k * x₀ * k⁻¹) = Φ y₀ := by rw [hkx]
      simpa [map_mul] using this
  · obtain ⟨x, hx, hx2, hxz, hxt⟩ := h.K_inv_t
    refine ⟨Φ x, ⟨hmem x hx.1, ?_⟩, ?_, ?_, MonoidHom.map_isConj Φ.toMonoidHom hxt⟩
    · rw [← Subgroup.map_sup]; exact ⟨x, hx.2, rfl⟩
    · rw [MulEquiv.orderOf_eq]; exact hx2
    · intro e; exact hxz (Φ.injective e)
  · have h1 : Nat.card (S' : Subgroup H) = Nat.card (S : Subgroup G) := by
      rw [hS]; exact Subgroup.card_map_of_injective Φ.injective
    have h2 : (S' : Subgroup H) ⊓ (K₁.map Φ.toMonoidHom ⊔ K₂.map Φ.toMonoidHom) =
        ((S : Subgroup G) ⊓ (K₁ ⊔ K₂)).map Φ.toMonoidHom := by
      rw [Subgroup.map_inf _ _ _ Φ.injective, Subgroup.map_sup, hS]
    have h3 : Nat.card ↥((S' : Subgroup H) ⊓ (K₁.map Φ.toMonoidHom ⊔ K₂.map Φ.toMonoidHom)) =
        Nat.card ↥((S : Subgroup G) ⊓ (K₁ ⊔ K₂)) := by
      rw [h2]; exact Subgroup.card_map_of_injective Φ.injective
    rw [h1, h3]; exact h.index

theorem inf_centralizer_map (Φ : G ≃* H) (E : Subgroup G) (u : G) :
    (E ⊓ Subgroup.centralizer ({u} : Set G)).map Φ.toMonoidHom =
      E.map Φ.toMonoidHom ⊓ Subgroup.centralizer ({Φ u} : Set H) := by
  rw [Subgroup.map_inf _ _ _ Φ.injective, ModelLT.centralizer_map_equiv]

theorem isCyclic_map_iff (Φ : G ≃* H) (X : Subgroup G) :
    IsCyclic ↥(X.map Φ.toMonoidHom) ↔ IsCyclic ↥X :=
  ⟨fun _ => isCyclic_of_surjective (subEquiv Φ X).symm.toMonoidHom (subEquiv Φ X).symm.surjective,
   fun _ => isCyclic_of_surjective (subEquiv Φ X).toMonoidHom (subEquiv Φ X).surjective⟩

theorem luModelData_map [Finite G] [Finite H] (Φ : G ≃* H) {q : ℕ} {ε : ℤ} {z : G} {S : Sylow 2 G}
    {S' : Sylow 2 H} (hS : (S' : Subgroup H) = (S : Subgroup G).map Φ.toMonoidHom)
    {E₁ E₂ : Subgroup G} {t u : G} (h : LUModelData G q ε z S E₁ E₂ t u) :
    LUModelData H q ε (Φ z) S' (E₁.map Φ.toMonoidHom) (E₂.map Φ.toMonoidHom) (Φ t) (Φ u) := by
  refine ⟨luComps_map Φ h.comps, luSyl_map Φ hS h.syl, h.eps, h.mod8, ?_, ?_, ?_⟩
  · rw [← card_pPrimeCore_centralizer_of_equiv Φ z]
    exact h.A0_dvd
  · rw [← inf_centralizer_map]
    exact (isCyclic_map_iff Φ _).2 h.H_cyc
  · rw [← inf_centralizer_map, Nat.card_congr (subEquiv Φ _).toEquiv.symm]
    exact h.H_card

theorem spModelData_map [Finite G] [Finite H] (Φ : G ≃* H) {q : ℕ} {z : G} {S : Sylow 2 G}
    {S' : Sylow 2 H} (hS : (S' : Subgroup H) = (S : Subgroup G).map Φ.toMonoidHom)
    {E₁ E₂ : Subgroup G} {t : G} (h : CFSG.GH74.GLS.SP.Local.SPModelData G q z S E₁ E₂ t) :
    CFSG.GH74.GLS.SP.Local.SPModelData H q (Φ z) S' (E₁.map Φ.toMonoidHom) (E₂.map Φ.toMonoidHom)
      (Φ t) :=
  ⟨luComps_map Φ h.comps, spSyl_map Φ hS h.syl⟩

end CFSG.GH74.GLS.Stage2.Final.ModelLUT
