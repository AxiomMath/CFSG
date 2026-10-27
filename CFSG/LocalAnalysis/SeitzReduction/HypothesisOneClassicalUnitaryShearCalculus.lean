module

public import Mathlib.Algebra.CharP.Two
public import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.SeitzReduction

namespace UnitaryShear

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {σ : K →+* K}
  {B : V →ₛₗ[σ] V →ₗ[K] K}

@[expose] def IsShear (B : V →ₛₗ[σ] V →ₗ[K] K) (W L : Submodule K V) (w u : V) (g : V → V) :
    Prop :=
  (∀ v ∈ L, g v = v - B u v • w) ∧ ∀ v, g v - v - B w v • u ∈ W

variable {W L : Submodule K V}

theorem isShear_id_zero_right (w : V) : IsShear B W L w 0 id :=
  ⟨fun v _ => by simp, fun v => by simp⟩

theorem isShear_id_zero_left (u : V) : IsShear B W L 0 u id :=
  ⟨fun v _ => by simp, fun v => by simp⟩

namespace IsShear

variable {w u : V} {g : V → V}

theorem apply_of_mem (hWL : W ≤ L) (hW : W = L.orthogonalBilin B) (hu : u ∈ L)
    (hg : IsShear B W L w u g) {x : V} (hx : x ∈ W) : g x = x := by
  have h0 : B u x = 0 := by
    rw [hW] at hx
    exact hx u hu
  rw [hg.1 x (hWL hx), h0, zero_smul, sub_zero]

theorem mapsTo (hWL : W ≤ L) (hw : w ∈ W) (hg : IsShear B W L w u g) {x : V} (hx : x ∈ L) :
    g x ∈ L := by
  rw [hg.1 x hx]
  exact L.sub_mem hx (L.smul_mem _ (hWL hw))

theorem sub_mem (hWL : W ≤ L) (hu : u ∈ L) (hg : IsShear B W L w u g) (v : V) :
    g v - v ∈ L := by
  have e : g v - v = (g v - v - B w v • u) + B w v • u := by abel
  rw [e]
  exact L.add_mem (hWL (hg.2 v)) (L.smul_mem _ hu)

theorem of_sub_mem (hL : L = W.orthogonalBilin B) {u' : V} (hu : u' - u ∈ W)
    (hg : IsShear B W L w u g) : IsShear B W L w u' g := by
  refine ⟨fun v hv => ?_, fun v => ?_⟩
  · have h0 : B (u' - u) v = 0 := by
      rw [hL] at hv
      exact hv _ hu
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at h0
    rw [hg.1 v hv, h0]
  · rw [show g v - v - B w v • u' = (g v - v - B w v • u) - B w v • (u' - u) by module]
    exact W.sub_mem (hg.2 v) (W.smul_mem _ hu)

theorem neg_left (hg : IsShear B W L w (-u) g) : IsShear B W L (-w) u g := by
  refine ⟨fun v hv => ?_, fun v => ?_⟩
  · rw [hg.1 v hv, map_neg, LinearMap.neg_apply, neg_smul, smul_neg]
  · have e : g v - v - B (-w) v • u = g v - v - B w v • -u := by
      rw [map_neg, LinearMap.neg_apply, neg_smul, smul_neg]
    rw [e]
    exact hg.2 v

theorem neg_right (hg : IsShear B W L (-w) u g) : IsShear B W L w (-u) g := by
  have h := neg_left (w := -w) (u := -u) (by rwa [neg_neg])
  rwa [neg_neg] at h

theorem comp_left (hWL : W ≤ L) (hL : L = W.orthogonalBilin B) (hW : W = L.orthogonalBilin B)
    (hw : w ∈ W) {u₁ u₂ : V} (hu₁ : u₁ ∈ L) (hu₂ : u₂ ∈ L) {g₁ g₂ : V → V}
    (hg₁ : IsShear B W L w u₁ g₁) (hg₂ : IsShear B W L w u₂ g₂) :
    IsShear B W L w (u₁ + u₂) (g₁ ∘ g₂) := by
  have hu₁w : B u₁ w = 0 := by
    have hw' := hw
    rw [hW] at hw'
    exact hw' u₁ hu₁
  refine ⟨fun v hv => ?_, fun v => ?_⟩
  · have h2 := hg₂.1 v hv
    simp only [Function.comp_apply]
    rw [hg₁.1 _ (hg₂.mapsTo hWL hw hv), h2, map_sub, map_smul, hu₁w, smul_zero, sub_zero,
      map_add, LinearMap.add_apply, add_smul]
    abel
  · have hd : B w (g₂ v) = B w v := by
      have hm : g₂ v - v ∈ L := hg₂.sub_mem hWL hu₂ v
      have h0 : B w (g₂ v - v) = 0 := by
        rw [hL] at hm
        exact hm w hw
      rw [map_sub, sub_eq_zero] at h0
      exact h0
    have e : (g₁ ∘ g₂) v - v - B w v • (u₁ + u₂) =
        (g₁ (g₂ v) - g₂ v - B w (g₂ v) • u₁) + (g₂ v - v - B w v • u₂) := by
      simp only [Function.comp_apply, hd]
      module
    rw [e]
    exact W.add_mem (hg₁.2 _) (hg₂.2 v)

theorem comp_right (hWL : W ≤ L) (hL : L = W.orthogonalBilin B) (hW : W = L.orthogonalBilin B)
    {w₁ w₂ : V} (hw₁ : w₁ ∈ W) (hw₂ : w₂ ∈ W) (hu : u ∈ L) {g₁ g₂ : V → V}
    (hg₁ : IsShear B W L w₁ u g₁) (hg₂ : IsShear B W L w₂ u g₂) :
    IsShear B W L (w₁ + w₂) u (g₁ ∘ g₂) := by
  have huw : B u w₂ = 0 := by
    have hw' := hw₂
    rw [hW] at hw'
    exact hw' u hu
  refine ⟨fun v hv => ?_, fun v => ?_⟩
  · have h2 := hg₂.1 v hv
    simp only [Function.comp_apply]
    rw [hg₁.1 _ (hg₂.mapsTo hWL hw₂ hv), h2, map_sub, map_smul, huw, smul_zero, sub_zero,
      smul_add]
    abel
  · have hd : B w₁ (g₂ v) = B w₁ v := by
      have hm : g₂ v - v ∈ L := hg₂.sub_mem hWL hu v
      have h0 : B w₁ (g₂ v - v) = 0 := by
        rw [hL] at hm
        exact hm w₁ hw₁
      rw [map_sub, sub_eq_zero] at h0
      exact h0
    have e : (g₁ ∘ g₂) v - v - B (w₁ + w₂) v • u =
        (g₁ (g₂ v) - g₂ v - B w₁ (g₂ v) • u) + (g₂ v - v - B w₂ v • u) := by
      simp only [Function.comp_apply, hd, map_add, LinearMap.add_apply]
      module
    rw [e]
    exact W.add_mem (hg₁.2 _) (hg₂.2 v)

theorem inverse (hWL : W ≤ L) (hL : L = W.orthogonalBilin B) (hW : W = L.orthogonalBilin B)
    (hw : w ∈ W) (hu : u ∈ L) (hg : IsShear B W L w u g) {g' : V → V}
    (hgg' : ∀ v, g (g' v) = v) (hg'g : ∀ v, g' (g v) = v) : IsShear B W L (-w) u g' := by
  have huw : B u w = 0 := by
    have hw' := hw
    rw [hW] at hw'
    exact hw' u hu
  refine ⟨fun x hx => ?_, fun v => ?_⟩
  ·
    have hy : x + B u x • w ∈ L := L.add_mem hx (L.smul_mem _ (hWL hw))
    have h1 : g (x + B u x • w) = x := by
      rw [hg.1 _ hy, map_add, map_smul, huw, smul_zero, add_zero]
      abel
    have h2 : g' x = x + B u x • w := by
      conv_lhs => rw [← h1]
      rw [hg'g]
    rw [h2, smul_neg, sub_neg_eq_add]
  · have h2 := hg.2 (g' v)
    rw [hgg'] at h2
    have hd : B w (g' v) = B w v := by
      have h3 : g' v - v ∈ L := by
        have e : g' v - v = -(v - g' v - B w (g' v) • u) - B w (g' v) • u := by abel
        rw [e]
        exact L.sub_mem (L.neg_mem (hWL h2)) (L.smul_mem _ hu)
      have h0 : B w (g' v - v) = 0 := by
        rw [hL] at h3
        exact h3 w hw
      rw [map_sub, sub_eq_zero] at h0
      exact h0
    have e : g' v - v - B (-w) v • u = -(v - g' v - B w (g' v) • u) := by
      rw [hd, map_neg, LinearMap.neg_apply, neg_smul]
      abel
    rw [e]
    exact W.neg_mem h2

theorem conj (hg : IsShear B W L w u g) (y : V →ₗ[K] V) {y' : V → V}
    (hyB : ∀ x x', B (y x) (y x') = B x x') (hyW : ∀ x ∈ W, y x ∈ W) (hyy' : ∀ v, y (y' v) = v)
    (hy'L : ∀ x ∈ L, y' x ∈ L) : IsShear B W L (y w) (y u) (fun v => y (g (y' v))) := by
  refine ⟨fun x hx => ?_, fun v => ?_⟩
  · show y (g (y' x)) = _
    rw [hg.1 _ (hy'L x hx), map_sub, map_smul, hyy', ← hyB u (y' x), hyy']
  · show y (g (y' v)) - v - B (y w) v • y u ∈ W
    have hB' : B (y w) v = B w (y' v) := by rw [← hyB w (y' v), hyy']
    have e : y (g (y' v)) - v - B (y w) v • y u = y (g (y' v) - y' v - B w (y' v) • u) := by
      rw [map_sub, map_sub, map_smul, hyy', hB']
    rw [e]
    exact hyW _ (hg.2 _)

theorem sub_one_cube (hWL : W ≤ L) (hW : W = L.orthogonalBilin B) (hw : w ∈ W) (hu : u ∈ L)
    (hg : IsShear B W L w u g) (v : V) :
    g (g (g v - v) - (g v - v)) - (g (g v - v) - (g v - v)) = 0 := by
  have h1 : g v - v ∈ L := hg.sub_mem hWL hu v
  have h2 : g (g v - v) - (g v - v) ∈ W := by
    rw [hg.1 _ h1, sub_sub_cancel_left]
    exact W.neg_mem (W.smul_mem _ hw)
  rw [hg.apply_of_mem hWL hW hu h2, sub_self]

end IsShear

section Closure

variable {P : (V → V) → Prop}

theorem forall_isShear_of_le_span_right (hWL : W ≤ L) (hL : L = W.orthogonalBilin B)
    (hW : W = L.orthogonalBilin B) (hP1 : P id) (hPc : ∀ g₁ g₂, P g₁ → P g₂ → P (g₁ ∘ g₂))
    {X : Set V} (hXL : X ⊆ L) (hLX : L ≤ W ⊔ Submodule.span K X)
    (hX : ∀ w ∈ W, ∀ x ∈ X, ∀ a : K, ∃ g, P g ∧ IsShear B W L w (a • x) g) :
    ∀ w ∈ W, ∀ u ∈ L, ∃ g, P g ∧ IsShear B W L w u g := by
  have hspanL : Submodule.span K X ≤ L := Submodule.span_le.mpr hXL
  have hspan : ∀ x ∈ Submodule.span K X, ∀ w ∈ W, ∀ a : K,
      ∃ g, P g ∧ IsShear B W L w (a • x) g := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact fun w hw a => hX w hw x hx a
    | zero => exact fun w _ a => ⟨id, hP1, by rw [smul_zero]; exact isShear_id_zero_right w⟩
    | add x y hx hy ihx ihy =>
      intro w hw a
      obtain ⟨g₁, hP₁, hg₁⟩ := ihx w hw a
      obtain ⟨g₂, hP₂, hg₂⟩ := ihy w hw a
      refine ⟨g₁ ∘ g₂, hPc _ _ hP₁ hP₂, ?_⟩
      rw [smul_add]
      exact hg₁.comp_left hWL hL hW hw (L.smul_mem a (hspanL hx)) (L.smul_mem a (hspanL hy)) hg₂
    | smul b x hx ihx =>
      intro w hw a
      rw [smul_smul]
      exact ihx w hw (a * b)
  intro w hw u hu
  obtain ⟨y, hy, x, hx, rfl⟩ := Submodule.mem_sup.mp (hLX hu)
  obtain ⟨g, hP, hg⟩ := hspan x hx w hw 1
  rw [one_smul] at hg
  exact ⟨g, hP, hg.of_sub_mem hL (by rwa [add_sub_cancel_right])⟩

theorem forall_isShear_of_le_span_left (hWL : W ≤ L) (hL : L = W.orthogonalBilin B)
    (hW : W = L.orthogonalBilin B) (hP1 : P id) (hPc : ∀ g₁ g₂, P g₁ → P g₂ → P (g₁ ∘ g₂))
    {Y : Set V} (hYW : Y ⊆ W) (hWY : W ≤ Submodule.span K Y)
    (hY : ∀ y ∈ Y, ∀ a : K, ∀ u ∈ L, ∃ g, P g ∧ IsShear B W L (a • y) u g) :
    ∀ w ∈ W, ∀ u ∈ L, ∃ g, P g ∧ IsShear B W L w u g := by
  have hspanW : Submodule.span K Y ≤ W := Submodule.span_le.mpr hYW
  have hspan : ∀ x ∈ Submodule.span K Y, ∀ u ∈ L, ∀ a : K,
      ∃ g, P g ∧ IsShear B W L (a • x) u g := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact fun u hu a => hY x hx a u hu
    | zero => exact fun u _ a => ⟨id, hP1, by rw [smul_zero]; exact isShear_id_zero_left u⟩
    | add x y hx hy ihx ihy =>
      intro u hu a
      obtain ⟨g₁, hP₁, hg₁⟩ := ihx u hu a
      obtain ⟨g₂, hP₂, hg₂⟩ := ihy u hu a
      refine ⟨g₁ ∘ g₂, hPc _ _ hP₁ hP₂, ?_⟩
      rw [smul_add]
      exact hg₁.comp_right hWL hL hW (W.smul_mem a (hspanW hx)) (W.smul_mem a (hspanW hy)) hu hg₂
    | smul b x hx ihx =>
      intro u hu a
      rw [smul_smul]
      exact ihx u hu (a * b)
  intro w hw u hu
  obtain ⟨g, hP, hg⟩ := hspan w (hWY hw) u hu 1
  rw [one_smul] at hg
  exact ⟨g, hP, hg⟩

end Closure

section Spanning

@[expose] def anisotropicPairs (B : V →ₛₗ[σ] V →ₗ[K] K) (S : Submodule K V) : Set V :=
  {e | e ∈ S ∧ B e e ≠ 0 ∧ ∃ f ∈ S, B f f ≠ 0 ∧ B e f = 0}

variable [CharP K 2] (hσ : ∀ a, σ (σ a) = a) (hB : ∀ x y, σ (B x y) = B y x) {θ : K}
  (hθ : θ + σ θ ≠ 0) {S R : Submodule K V} (hR : ∀ x ∈ S, x ∈ R ↔ ∀ y ∈ S, B y x = 0)

omit [CharP K 2] in
include hσ hB hθ in
theorem exists_anisotropic_of_pair {u v x : V} (hv : v ∈ S) (hx : x ∈ S) (huv : B u v = 0)
    (hux : B u x = 0) (hxv : B x v ≠ 0) : ∃ f ∈ S, B f f ≠ 0 ∧ B u f = 0 := by
  by_cases hvv : B v v = 0
  · by_cases hxx : B x x = 0
    ·
      refine ⟨v + σ (θ / B x v) • x, S.add_mem hv (S.smul_mem _ hx), ?_, ?_⟩
      · have hvx : B v x = σ (B x v) := (hB x v).symm
        have e1 : B (v + σ (θ / B x v) • x) (v + σ (θ / B x v) • x) = θ + σ θ := by
          simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
            hvv, hxx, hvx, hσ, RingHom.id_apply]
          rw [map_div₀, mul_zero, add_zero, zero_add, div_mul_cancel₀ _ hxv,
            div_mul_cancel₀ _ ((map_ne_zero σ).mpr hxv)]
        rw [e1]
        exact hθ
      · rw [map_add, map_smul, huv, hux, smul_zero, add_zero]
    · exact ⟨x, hx, hxx, hux⟩
  · exact ⟨v, hv, hvv, huv⟩

omit [CharP K 2] in
include hσ hB hθ hR in
theorem mem_anisotropicPairs_of_ne_zero {u : V} (hu : u ∈ S) (huu : B u u ≠ 0)
    (hS : ¬S ≤ R ⊔ Submodule.span K {u}) : u ∈ anisotropicPairs B S := by
  refine ⟨hu, huu, ?_⟩
  have hproj : ∀ x ∈ S, x - (B u x / B u u) • u ∈ S ∧ B u (x - (B u x / B u u) • u) = 0 := by
    intro x hx
    refine ⟨S.sub_mem hx (S.smul_mem _ hu), ?_⟩
    rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ huu, sub_self]
  obtain ⟨v, hv, huv, hvR⟩ : ∃ v ∈ S, B u v = 0 ∧ v ∉ R := by
    by_contra! hall
    apply hS
    intro x hx
    obtain ⟨h1, h2⟩ := hproj x hx
    have h3 := hall _ h1 h2
    have e : x = (x - (B u x / B u u) • u) + (B u x / B u u) • u := by abel
    rw [e]
    exact Submodule.add_mem_sup h3 (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u))
  obtain ⟨x, hx, hxv⟩ : ∃ x ∈ S, B x v ≠ 0 := by
    by_contra! hall
    exact hvR ((hR v hv).mpr hall)
  obtain ⟨hx', hux'⟩ := hproj x hx
  have hx'v : B (x - (B u x / B u u) • u) v ≠ 0 := by
    have huv' : B u v = 0 := huv
    rw [map_sub, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, huv', smul_zero, sub_zero]
    exact hxv
  obtain ⟨f, hf, hff, huf⟩ := exists_anisotropic_of_pair hσ hB hθ hv hx' huv hux' hx'v
  exact ⟨f, hf, hff, huf⟩

include hσ hB hθ hR in
theorem le_sup_span_anisotropicPairs (hS : ∀ e₀, ¬S ≤ R ⊔ Submodule.span K {e₀}) :
    S ≤ R ⊔ Submodule.span K (anisotropicPairs B S) := by
  intro u hu
  by_cases huR : u ∈ R
  · exact Submodule.mem_sup_left huR
  have hspan : ∀ e ∈ anisotropicPairs B S, e ∈ R ⊔ Submodule.span K (anisotropicPairs B S) :=
    fun e he => Submodule.mem_sup_right (Submodule.subset_span he)
  by_cases huu : B u u = 0
  ·
    obtain ⟨v₀, hv₀, hv₀u⟩ : ∃ v ∈ S, B v u ≠ 0 := by
      by_contra! hall
      exact huR ((hR u hu).mpr hall)
    set v := σ (B v₀ u)⁻¹ • v₀ with hvdef
    have hv : v ∈ S := S.smul_mem _ hv₀
    have hvu : B v u = 1 := by
      rw [hvdef, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hσ, inv_mul_cancel₀ hv₀u]
    have huv : B u v = 1 := by rw [← hB v u, hvu, map_one]
    by_cases hvv : B v v = 0
    ·
      have hθ' : σ θ + θ ≠ 0 := by rwa [add_comm]
      have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
      have e1 : u + θ • v ∈ anisotropicPairs B S := by
        refine ⟨S.add_mem hu (S.smul_mem _ hv), ?_, u + σ θ • v, S.add_mem hu (S.smul_mem _ hv),
          ?_, ?_⟩
        · simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
            RingHom.id_apply, huu, hvv, huv, hvu]
          rw [mul_zero, add_zero, zero_add, mul_one, mul_one]
          first
          | exact hθ
          | exact hθ'
        · simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
            RingHom.id_apply, huu, hvv, huv, hvu, hσ]
          rw [mul_zero, add_zero, zero_add, mul_one, mul_one]
          exact hθ
        · simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
            RingHom.id_apply, huu, hvv, huv, hvu]
          linear_combination (σ θ) * h2
      have e2 : u + σ θ • v ∈ anisotropicPairs B S := by
        refine ⟨S.add_mem hu (S.smul_mem _ hv), ?_, u + θ • v, S.add_mem hu (S.smul_mem _ hv),
          ?_, ?_⟩
        · simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
            RingHom.id_apply, huu, hvv, huv, hvu, hσ]
          rw [mul_zero, add_zero, zero_add, mul_one, mul_one]
          exact hθ
        · simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
            RingHom.id_apply, huu, hvv, huv, hvu]
          rw [mul_zero, add_zero, zero_add, mul_one, mul_one]
          first
          | exact hθ
          | exact hθ'
        · simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
            RingHom.id_apply, huu, hvv, huv, hvu, hσ]
          linear_combination θ * h2
      have e3 : u = (θ + σ θ)⁻¹ • (σ θ • (u + θ • v) + θ • (u + σ θ • v)) := by
        have h3 : σ θ • (u + θ • v) + θ • (u + σ θ • v) = (θ + σ θ) • u + (2 * (θ * σ θ)) • v := by
          module
        rw [h3, h2, zero_mul, zero_smul, add_zero, smul_smul, inv_mul_cancel₀ hθ, one_smul]
      rw [e3]
      exact Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.smul_mem _ _ (hspan _ e1))
        (Submodule.smul_mem _ _ (hspan _ e2)))
    ·
      have huv' : B (u + v) (u + v) = B v v := by
        simp only [map_add, LinearMap.add_apply, huu, huv, hvu]
        linear_combination (CharTwo.two_eq_zero : (2 : K) = 0)
      have h1 := mem_anisotropicPairs_of_ne_zero hσ hB hθ hR hv hvv (hS v)
      have h2 := mem_anisotropicPairs_of_ne_zero hσ hB hθ hR (S.add_mem hu hv)
        (by rw [huv']; exact hvv) (hS (u + v))
      have e : u = (u + v) - v := by abel
      rw [e]
      exact Submodule.sub_mem _ (hspan _ h2) (hspan _ h1)
  · exact hspan u (mem_anisotropicPairs_of_ne_zero hσ hB hθ hR hu huu (hS u))

end Spanning

section Adjust

variable (hB : ∀ x y, σ (B x y) = B y x) (htr : ∀ d, σ d = d → ∃ t, t + σ t = d)
  {N : V →ₗ[K] V} (hN2 : ∀ v, N (N v) = 0) (hNB : ∀ x y, B (N x) y = B x (N y))

include hB htr hN2 hNB in
theorem exists_adjusted_pair {e f : V} (he : B e (N e) ≠ 0) (hf : B f (N f) ≠ 0)
    (hef : B e (N f) = 0) :
    ∃ e' f' : V, N e' = N e ∧ B e' e' + B e' (N e') = 0 ∧ B f' f' + B f' (N f') = 0 ∧
      B e' f' = 0 ∧ B e' (N f') = 0 ∧ B e' (N e') = B e (N e) ∧ B f' (N f') = B f (N f) := by
  set a := B e (N e) with ha
  set c := B f (N f) with hc
  have hσa : σ a = a := by rw [ha, hB, hNB]
  have hσc : σ c = c := by rw [hc, hB, hNB]
  have hNeNe : B (N e) (N e) = 0 := by rw [hNB, hN2, map_zero]
  have hNfNf : B (N f) (N f) = 0 := by rw [hNB, hN2, map_zero]
  have hNeNf : B (N e) (N f) = 0 := by rw [hNB, hN2, map_zero]
  have hNfNe : B (N f) (N e) = 0 := by rw [hNB, hN2, map_zero]
  have hNee : B (N e) e = a := by rw [hNB]
  have hNff : B (N f) f = c := by rw [hNB]
  have hNef : B (N e) f = 0 := by rw [hNB, hef]
  have hfNe : B f (N e) = 0 := by rw [← hNB, ← hB, hef, map_zero]
  obtain ⟨t₀, ht₀⟩ := htr (-(B e e + a)) (by rw [map_neg, map_add, hB e e, hσa])
  obtain ⟨z₀, hz₀⟩ := htr (-(B f f + c)) (by rw [map_neg, map_add, hB f f, hσc])
  have ht : t₀ / a * a = t₀ := div_mul_cancel₀ _ he
  have hσt : σ (t₀ / a) * a = σ t₀ := by rw [map_div₀, hσa, div_mul_cancel₀ _ he]
  have hz : z₀ / c * c = z₀ := div_mul_cancel₀ _ hf
  have hσz : σ (z₀ / c) * c = σ z₀ := by rw [map_div₀, hσc, div_mul_cancel₀ _ hf]
  have hx : -B e f / a * a = -B e f := div_mul_cancel₀ _ he
  refine ⟨e + (t₀ / a) • N e, f + (-B e f / a) • N e + (z₀ / c) • N f, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [map_add, map_smul, hN2, smul_zero, add_zero]
  · simp only [map_add, map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, hN2, smul_zero, add_zero, hNeNe, hNee, ← ha]
    linear_combination ht + hσt + ht₀
  · simp only [map_add, map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, hN2, smul_zero, add_zero, hNeNe, hNfNf, hNeNf, hNfNe, hNff, hNef, hfNe, ← hc]
    linear_combination hz + hσz + hz₀
  · simp only [map_add, map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, hNeNe, hNeNf, hNef, hef, ← ha]
    linear_combination hx
  · simp only [map_add, map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, hN2, smul_zero, add_zero, hNeNf, hef]
    ring
  · simp only [map_add, map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, hN2, smul_zero, add_zero, hNeNe]
    ring
  · simp only [map_add, map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, hN2, smul_zero, add_zero, hNeNf, hNfNf]
    ring

end Adjust

end UnitaryShear

end CFSG.SeitzReduction
