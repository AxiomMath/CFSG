module

public import CFSG.ClassicalInvolution.ModelFacts.G2D4TD4Normal
public import CFSG.ClassicalInvolution.ModelFacts.G2D4SL2Gen

public noncomputable section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.CurtisTits
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley
open scoped MatrixGroups

section Generation

variable {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem range_slLong_sup_range_slShort : (slLong σ hσ).range ⊔ (slShort σ hσ).range = ⊤ := by
  have h : ⨆ i : Fin (twistedDatum σ).rank, rankOne (twistedDatum σ).rootGroup i = ⊤ :=
    CFSG.ClassicalInvolution.WeakCT.iSup_rankOne_eq_top_of_ct (D := twistedDatum σ)
      (twistedDatum_isCTGroupDatum σ hσ) rfl
  rw [eq_top_iff, ← h]
  refine iSup_le fun i => ?_
  match i with
  | ⟨0, _⟩ => exact le_trans (le_of_eq (ModelFacts.rankOne_long_eq_range hσ)) le_sup_left
  | ⟨1, _⟩ => exact le_trans (le_of_eq (ModelFacts.rankOne_short_eq_range hσ)) le_sup_right

include hσ in
theorem TK_le_centralizer_tauL {x : twistedGroup σ} (hx : x ∈ TK σ) :
    x ∈ Subgroup.centralizer ({slLong σ hσ (-1)} : Set (twistedGroup σ)) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact TK_mul_comm hx (slLong_neg_one_mem_TK hσ)

include hσ in
theorem slLong_mem_centralizer_tauL (A : SL(2, fixedField σ)) :
    slLong σ hσ A ∈ Subgroup.centralizer ({slLong σ hσ (-1)} : Set (twistedGroup σ)) := by
  rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, ← neg_one_mul_comm_SL2]

include hσ in
theorem slShort_le_sup_td4 (hK : (-1 : Kˣ) ≠ 1) [Finite K] (h7 : 7 ≤ Nat.card K)
    (hC₀ : graphFixedRootGroup TwistTag.D4 K σ ≤ (twistedIncl σ).range)
    (hgF : ∀ g : twistedGroup σ, twistedIncl σ g ∈ graphFixedRootGroup TwistTag.D4 K σ)
    {t₀ : twistedGroup σ} (ht₀ : t₀ ∈ TK σ) (A : SL(2, K)) :
    slShort σ hσ A ∈ Subgroup.centralizer ({slLong σ hσ (-1)} : Set (twistedGroup σ)) ⊔
      Subgroup.centralizer ({t₀ * m0 hσ} : Set (twistedGroup σ)) := by
  have h2K : (2 : K) ≠ 0 := two_ne_zero_of_neg_one_ne_one hK
  set y : twistedGroup σ := t₀ * m0 hσ with hy
  have hinvT : ∀ x ∈ TK σ, y * x * y⁻¹ = x⁻¹ := by
    intro x hx
    calc y * x * y⁻¹ = t₀ * (m0 hσ * x * (m0 hσ)⁻¹) * t₀⁻¹ := by rw [hy]; group
      _ = t₀ * x⁻¹ * t₀⁻¹ := by rw [m0_inverts_td4 hσ hx]
      _ = x⁻¹ := by rw [TK_mul_comm ht₀ (inv_mem hx)]; group
  have hτS : slShort σ hσ (-1) ∈ TK σ := slShort_neg_one_mem_TK hσ
  have hyτS : y * slShort σ hσ (-1) = slShort σ hσ (-1) * y := by
    have h1 := hinvT _ hτS
    have h2 : (slShort σ hσ (-1))⁻¹ = slShort σ hσ (-1) := by
      rw [← map_inv, inv_eq_of_mul_eq_one_right neg_one_mul_neg_one_SL2]
    rw [h2, mul_inv_eq_iff_eq_mul] at h1
    exact h1
  obtain ⟨D, hD⟩ := linAct_of_centralizes_short hσ hK h2K hC₀ hgF hyτS
  have hinv : ∀ a : Kˣ, y * slShort σ hσ (HSL a) * y⁻¹ = (slShort σ hσ (HSL a))⁻¹ := fun a =>
    hinvT _ ⟨_, twistedIncl_slShort_HSL hσ a⟩
  have hH : ∀ a : Kˣ, slShort σ hσ (HSL a) ∈
      Subgroup.centralizer ({slLong σ hσ (-1)} : Set (twistedGroup σ)) := fun a =>
    TK_le_centralizer_tauL hσ ⟨_, twistedIncl_slShort_HSL hσ a⟩
  have hdiag : ∀ s : Kˣ, ∃ g ∈ Subgroup.centralizer ({slLong σ hσ (-1)} : Set (twistedGroup σ)),
      ∀ A : SL(2, K), g * slShort σ hσ A * g⁻¹ = slShort σ hσ (glConjSL (diagGL s) A) := by
    intro s
    obtain ⟨s₀, hs₀⟩ := nuU_surjective hσ s
    obtain ⟨s', hs', hconj⟩ := torus_conj_slShort hσ (twistedIncl_slB_HSL hσ s₀)
    have hss : s' = s := Units.ext (by rw [hs', cB_zero, hs₀])
    subst hss
    exact ⟨slB σ hσ (HSL s₀), TK_le_centralizer_tauL hσ ⟨_, twistedIncl_slB_HSL hσ s₀⟩, hconj⟩
  exact chart_le_sup_centralizer h7 h2K (slShort_injective hσ) hD hinv hH hdiag A

include hσ in
theorem centralizer_sup_eq_top_td4 (hK : (-1 : Kˣ) ≠ 1) [Finite K] (h7 : 7 ≤ Nat.card K)
    (hC₀ : graphFixedRootGroup TwistTag.D4 K σ ≤ (twistedIncl σ).range)
    (hgF : ∀ g : twistedGroup σ, twistedIncl σ g ∈ graphFixedRootGroup TwistTag.D4 K σ)
    {t₀ : twistedGroup σ} (ht₀ : t₀ ∈ TK σ) :
    Subgroup.centralizer ({slLong σ hσ (-1)} : Set (twistedGroup σ)) ⊔
      Subgroup.centralizer ({t₀ * m0 hσ} : Set (twistedGroup σ)) = ⊤ := by
  rw [eq_top_iff, ← range_slLong_sup_range_slShort hσ]
  refine sup_le ?_ ?_
  · rintro _ ⟨A, rfl⟩
    exact Subgroup.mem_sup_left (slLong_mem_centralizer_tauL hσ A)
  · rintro _ ⟨A, rfl⟩
    exact slShort_le_sup_td4 hσ hK h7 hC₀ hgF ht₀ A

end Generation

section Conjugate

theorem sup_centralizer_conj_eq_top_iff_td4 {G : Type*} [Group G] (g u v : G) :
    Subgroup.centralizer ({g * u * g⁻¹} : Set G) ⊔ Subgroup.centralizer ({g * v * g⁻¹} : Set G) =
        ⊤ ↔ Subgroup.centralizer ({u} : Set G) ⊔ Subgroup.centralizer ({v} : Set G) = ⊤ := by
  rw [← conjSub_centralizer_singleton_g2d4, ← conjSub_centralizer_singleton_g2d4,
    ← Subgroup.map_sup]
  constructor
  · intro h
    exact Subgroup.map_injective (MulAut.conj g).injective
      (h.trans (Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective).symm)
  · intro h
    rw [h]
    exact Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective

variable {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem sup_centralizer_eq_top_td4 (hK : (-1 : Kˣ) ≠ 1) [Finite K] (h7 : 7 ≤ Nat.card K)
    (hC₀ : graphFixedRootGroup TwistTag.D4 K σ ≤ (twistedIncl σ).range)
    (hgF : ∀ g : twistedGroup σ, twistedIncl σ g ∈ graphFixedRootGroup TwistTag.D4 K σ)
    (hconj : ∀ u : twistedGroup σ, u * u = 1 → u ≠ 1 →
      ∃ g : twistedGroup σ, g * u * g⁻¹ = slLong σ hσ (-1))
    {u v : twistedGroup σ} (hu2 : u * u = 1) (hv2 : v * v = 1) (hu1 : u ≠ 1) (hv1 : v ≠ 1)
    (huv : u ≠ v) (hcomm : u * v = v * u) :
    Subgroup.centralizer ({u} : Set (twistedGroup σ)) ⊔
      Subgroup.centralizer ({v} : Set (twistedGroup σ)) = ⊤ := by
  obtain ⟨g, hg⟩ := hconj u hu2 hu1
  set v' : twistedGroup σ := g * v * g⁻¹ with hv'
  have hv'2 : v' * v' = 1 := by
    calc v' * v' = g * (v * v) * g⁻¹ := by rw [hv']; group
      _ = 1 := by rw [hv2]; group
  have hv'1 : v' ≠ 1 := by
    intro h
    apply hv1
    have : v = g⁻¹ * v' * g := by rw [hv']; group
    rw [this, h]
    group
  have hv'τ : v' ≠ slLong σ hσ (-1) := by
    intro h
    apply huv
    rw [← hg, hv'] at h
    have h' := mul_right_cancel (mul_left_cancel h : v * g⁻¹ = u * g⁻¹)
    exact h'.symm
  have hcommτ : v' * slLong σ hσ (-1) = slLong σ hσ (-1) * v' := by
    rw [← hg, hv']
    calc g * v * g⁻¹ * (g * u * g⁻¹) = g * (v * u) * g⁻¹ := by group
      _ = g * (u * v) * g⁻¹ := by rw [hcomm]
      _ = g * u * g⁻¹ * (g * v * g⁻¹) := by group
  have hSP : v' ∈ SProd σ hσ := mem_SProd_of_centralizes hσ hK hC₀ hgF hcommτ
  obtain ⟨x, hx, t, ht, hxv⟩ := exists_conj_to_torus_mul_td4 hσ hK hSP hv'2 hv'1 hv'τ
  have hxτ : x * slLong σ hσ (-1) * x⁻¹ = slLong σ hσ (-1) := by
    rw [SProd_le_centralizer hσ hx]
    group
  have h1 : (x * g) * u * (x * g)⁻¹ = slLong σ hσ (-1) := by
    calc (x * g) * u * (x * g)⁻¹ = x * (g * u * g⁻¹) * x⁻¹ := by group
      _ = slLong σ hσ (-1) := by rw [hg, hxτ]
  have h2 : (x * g) * v * (x * g)⁻¹ = t * m0 hσ := by
    calc (x * g) * v * (x * g)⁻¹ = x * v' * x⁻¹ := by rw [hv']; group
      _ = t * m0 hσ := hxv
  have key := centralizer_sup_eq_top_td4 hσ hK h7 hC₀ hgF ht
  rw [← sup_centralizer_conj_eq_top_iff_td4 (x * g) u v, h1, h2]
  exact key

end Conjugate

end CFSG.ClassicalInvolution.G2D4Models
