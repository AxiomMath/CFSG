module

public import CFSG.ClassicalInvolution.Phan.PhanQ43Theta

public section

namespace CFSG.ClassicalInvolution.PhanQ

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.PhanP
  CFSG.ClassicalInvolution.PhanD4 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.Phan

section Plane

variable {F K : Type} [Field F] [Field K] [Algebra F K] {ε : F} (D : KData F K ε)

theorem PhanSolid.Q_eq_zero {W : Submodule K (V8 K)} (hW : PhanSolid D W) (h2 : (2 : K) ≠ 0)
    {x : V8 K} (hx : x ∈ W) : Q8 x = 0 := by
  have h1 := hW.ts x hx x hx
  rw [B8_self] at h1
  exact (mul_eq_zero.1 h1).resolve_left h2

theorem isCollinear_iff_colK {W : Submodule K (V8 K)} (hW : PhanSolid D W) {σ : K ≃+* K}
    (hσu : IsUnitaryInvolution σ) (Θ : (Fin 4 → K) ≃ₗ[K] ↥W)
    (hΘ : ∀ u v, herm σ u v = her D (Θ v : V8 K) (Θ u : V8 K)) {u v : Fin 4 → K}
    (hu : herm σ u u ≠ 0) (hv : herm σ v v ≠ 0) :
    IsCollinear σ (K ∙ u) (K ∙ v) ↔ ColK D (Θ u : V8 K) (Θ v : V8 K) := by
  rw [isCollinear_span_iff hσu hu hv]
  unfold ColK gram
  rw [hΘ u u, hΘ v v, hΘ u v, hΘ v u, hW.ts _ (Θ u).2 _ (Θ v).2]
  constructor
  · intro h
    exact ⟨rfl, by intro h0; apply h; linear_combination h0⟩
  · intro h h0
    apply h.2
    linear_combination h0

theorem PhanSolid.exists_colK_in_plane [Finite K] {W : Submodule K (V8 K)} (hW : PhanSolid D W)
    (h2 : (2 : K) ≠ 0) (hε : ε ≠ 0) {σ : K ≃+* K} (hσ : ∀ x, σ x = D.τ x)
    (hσu : IsUnitaryInvolution σ) {q : ℕ} (hK : Nat.card K = q ^ 2) {u v : V8 K}
    (hu : u ∈ W) (hv : v ∈ W) (hffu : ffK D u) (hffv : ffK D v) (huv : ColK D u v)
    (X : Finset (V8 K)) (hX : ∀ x ∈ X, x ∈ W ∧ ffK D x)
    (hcard : X.card * (q + 1) < q ^ 2 - q) :
    ∃ e ∈ Submodule.span K {u, v}, ffK D e ∧ ∀ x ∈ X, ColK D x e := by
  classical
  obtain ⟨Θ, hΘ⟩ := PhanSolid.exists_isometry D hW h2 hε hσ
  let ι : V8 K → (Fin 4 → K) := fun x => if hx : x ∈ W then Θ.symm ⟨x, hx⟩ else 0
  have hι : ∀ x (hx : x ∈ W), (Θ (ι x) : V8 K) = x := fun x hx => by
    simp only [ι, hx, ↓reduceDIte, LinearEquiv.apply_symm_apply]
  have hherι : ∀ x y, x ∈ W → y ∈ W → herm σ (ι x) (ι y) = her D y x := by
    intro x y hx hy
    rw [hΘ, hι x hx, hι y hy]
  have hnsι : ∀ x, x ∈ W → ffK D x → herm σ (ι x) (ι x) ≠ 0 := by
    intro x hx hff
    rw [hherι x x hx hx]
    exact hff.2
  have hpt : ∀ x, x ∈ W → ffK D x →
      K ∙ ι x ∈ nsPts σ (⊤ : Submodule K (Fin 4 → K)) := fun x hx hff =>
    span_singleton_mem_nsPts (hnsι x hx hff) Submodule.mem_top
  have hcol : IsCollinear σ (K ∙ ι u) (K ∙ ι v) := by
    rw [isCollinear_iff_colK D hW hσu Θ hΘ (hnsι u hu hffu) (hnsι v hv hffv), hι u hu, hι v hv]
    exact huv
  have hL : Module.finrank K ↥((K ∙ ι u) ⊔ (K ∙ ι v)) = 2 :=
    finrank_sup_of_ne_pts (hpt u hu hffu).2.1 (hpt v hv hffv).2.1 hcol.1
  obtain ⟨e, he, hcolX⟩ := exists_collinear_all hσu hK hL hcol.2 (X.image fun x => K ∙ ι x)
    (by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
      exact hpt x (hX x hx).1 (hX x hx).2)
    (lt_of_le_of_lt (Nat.mul_le_mul_right _ Finset.card_image_le) hcard)
  obtain ⟨w, hw, hwL, rfl⟩ := mem_nsPts_iff.1 he
  have hΘw : (Θ w : V8 K) ∈ W := (Θ w).2
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hwL
  obtain ⟨α, rfl⟩ := Submodule.mem_span_singleton.1 hy
  obtain ⟨β, rfl⟩ := Submodule.mem_span_singleton.1 hz
  refine ⟨(Θ w : V8 K), ?_, ⟨hW.Q_eq_zero D h2 hΘw, ?_⟩, ?_⟩
  · rw [← hyz]
    refine Submodule.mem_span_pair.2 ⟨α, β, ?_⟩
    simp [map_add, map_smul, hι u hu, hι v hv]
  · rw [← hΘ w w]
    exact hw
  · intro x hx
    have := hcolX (K ∙ ι x) (Finset.mem_image_of_mem _ hx)
    rw [isCollinear_iff_colK D hW hσu Θ hΘ (hnsι x (hX x hx).1 (hX x hx).2) hw,
      hι x (hX x hx).1] at this
    exact this

end Plane

end CFSG.ClassicalInvolution.PhanQ
