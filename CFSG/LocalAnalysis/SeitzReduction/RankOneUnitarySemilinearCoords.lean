module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySemilinearModel
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySemilinearField

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace U3RootCoords

variable {G : Type*} [Group G] {E : Type*} [Field E] [Finite E] [CharP E 2] {T₁ L : Subgroup G}
  {σ : E →+* E} {u v : G → E} (hc : U3RootCoords T₁ σ u v)
include hc

omit hc [Finite E] [CharP E 2] in
theorem conj_mem_szA₁_of_mem_normalizer {n y : G} (hn : n ∈ normalizer (T₁ : Set G))
    (hy : y ∈ szA₁ T₁) : n * y * n⁻¹ ∈ szA₁ T₁ := by
  obtain ⟨hyT, hyC⟩ := mem_szA₁.mp hy
  refine mem_szA₁.mpr ⟨(mem_normalizer_iff.mp hn y).mp hyT, mem_centralizer_iff.mpr fun z hz => ?_⟩
  have hz' : n⁻¹ * z * n ∈ T₁ := by
    have := (mem_normalizer_iff.mp (inv_mem hn) z).mp hz
    rwa [inv_inv] at this
  have h1 := mem_centralizer_iff.mp hyC _ hz'
  calc z * (n * y * n⁻¹) = n * ((n⁻¹ * z * n) * y) * n⁻¹ := by group
    _ = n * (y * (n⁻¹ * z * n)) * n⁻¹ := by rw [h1]
    _ = n * y * n⁻¹ * z := by group

theorem exists_semilinear {f : ℕ} (hf : 2 ≤ f) (hσ : ∀ x, σ x = x ^ (2 ^ f))
    (hE : Nat.card E = (2 ^ f) ^ 2) (hF : Nat.card {x : E // σ x = x} = 2 ^ f)
    (hA : ∀ y ∈ T₁, (y ∈ szA₁ T₁ ↔ u y = 0))
    (hborel : ∀ g ∈ L, g ∈ normalizer (T₁ : Set G) → ∃ s c : E, s ≠ 0 ∧ ∀ y ∈ T₁,
      u (g * y * g⁻¹) = s * u y ∧ v (g * y * g⁻¹) = s * σ s * v y + TraceForm.form σ c (s * u y))
    {d : G} (hdL : d ∈ L) (hdT : d ∈ normalizer (T₁ : Set G)) {μ₀ : E}
    (hμ₀o : orderOf μ₀ = ((2 ^ f) ^ 2 - 1) / Nat.gcd 3 (2 ^ f + 1))
    (hμ₀ : ∀ y ∈ T₁, u (d * y * d⁻¹) = μ₀ * u y)
    {x : G} (hxL : x ∈ normalizer (L : Set G)) (hxT : x ∈ normalizer (T₁ : Set G)) :
    ∃ μ : E, μ ≠ 0 ∧ ∃ τ : E →+* E, ∃ e : E, ∀ y ∈ T₁,
      u (x * y * x⁻¹) = μ * τ (u y) ∧
        v (x * y * x⁻¹) = μ * σ μ * τ (v y) + TraceForm.form σ e (μ * τ (u y)) := by
  classical
  have hσσ : ∀ z, σ (σ z) = z := TraceForm.sigma_sigma hσ hE
  have hq : 2 ≤ 2 ^ f := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf)
  have hconjT : ∀ n ∈ normalizer (T₁ : Set G), ∀ y ∈ T₁, n * y * n⁻¹ ∈ T₁ :=
    fun n hn y hy => (mem_normalizer_iff.mp hn y).mp hy
  have hxA : ∀ y ∈ T₁, u y = 0 → u (x * y * x⁻¹) = 0 := fun y hy hu =>
    (hA _ (hconjT x hxT y hy)).mp (conj_mem_szA₁_of_mem_normalizer hxT ((hA y hy).mpr hu))
  have hxA' : ∀ y ∈ T₁, u (x * y * x⁻¹) = 0 → u y = 0 := by
    intro y hy hu
    have h1 := conj_mem_szA₁_of_mem_normalizer (inv_mem hxT) ((hA _ (hconjT x hxT y hy)).mpr hu)
    rw [show x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y by group] at h1
    exact (hA y hy).mp h1
  obtain ⟨φ, hφ⟩ := hc.exists_addEquiv_conj hxT hxA hxA'
  have hgL : x * d * x⁻¹ ∈ L := (mem_normalizer_iff.mp hxL d).mp hdL
  have hgT : x * d * x⁻¹ ∈ normalizer (T₁ : Set G) := mul_mem (mul_mem hxT hdT) (inv_mem hxT)
  obtain ⟨s', c', -, hg⟩ := hborel _ hgL hgT
  obtain ⟨s₀, c₀, -, hd⟩ := hborel d hdL hdT
  have hs₀ : s₀ = μ₀ := by
    obtain ⟨y, hy, hy1⟩ := hc.u_surj 1
    have h1 := (hd y hy).1
    rw [hμ₀ y hy, hy1, mul_one, mul_one] at h1
    exact h1.symm
  rw [hs₀] at hd
  have hφμ : ∀ a, φ (μ₀ * a) = s' * φ a := by
    intro a
    obtain ⟨y, hy, hya⟩ := hc.u_surj a
    have hdy := hconjT d hdT y hy
    have hxy := hconjT x hxT y hy
    have e : x * (d * y * d⁻¹) * x⁻¹ = (x * d * x⁻¹) * (x * y * x⁻¹) * (x * d * x⁻¹)⁻¹ := by
      group
    have h1 := hφ _ hdy
    rw [hμ₀ y hy, e, (hg _ hxy).1, hφ y hy, hya] at h1
    exact h1.symm
  obtain ⟨τ, hτ⟩ := SemilinearField.exists_ringHom_of_mul hf hE hμ₀o φ.toAddMonoidHom
    φ.injective hφμ
  set μ : E := φ 1 with hμdef
  have hμ0 : μ ≠ 0 := fun h0 => one_ne_zero (φ.injective (h0.trans (map_zero φ).symm))
  have hφτ : ∀ a, φ a = μ * τ a := fun a => hτ a
  have hu : ∀ y ∈ T₁, u (x * y * x⁻¹) = μ * τ (u y) := fun y hy => by rw [hφ y hy, hφτ]
  have hτσ : ∀ z, τ (σ z) = σ (τ z) := SemilinearField.apply_sigma hσ τ
  have hvA : ∀ z ∈ T₁, u z = 0 → v (x * z * x⁻¹) = μ * σ μ * τ (v z) := by
    intro z hz hz0
    obtain ⟨a, ha⟩ :=
      SemilinearField.exists_mul_sigma_eq hσ hE hq (hc.sigma_v_of_u_eq_zero hz hz0)
    obtain ⟨y, hy, hya⟩ := hc.u_surj a
    obtain ⟨hy2u, hy2v⟩ := hc.sq hy
    have hzy : z = y ^ 2 :=
      hc.inj _ hz _ (pow_mem hy 2) (by rw [hz0, hy2u]) (by rw [hy2v, hya, ha])
    obtain ⟨-, hxy2v⟩ := hc.sq (hconjT x hxT y hy)
    have e : x * z * x⁻¹ = (x * y * x⁻¹) ^ 2 := by rw [hzy, pow_two, pow_two]; group
    rw [e, hxy2v, hu y hy, hya, hzy, hy2v, hya]
    simp only [map_mul, hτσ]
    ring
  choose sec hsecT hsecu using hc.u_surj
  set D : E → E := fun a => v (x * sec a * x⁻¹) - μ * σ μ * τ (v (sec a)) with hDdef
  have hD : ∀ y ∈ T₁, v (x * y * x⁻¹) = μ * σ μ * τ (v y) + D (u y) := by
    intro y hy
    have hy₀ := hsecT (u y)
    have hz : (sec (u y))⁻¹ * y ∈ T₁ := mul_mem (inv_mem hy₀) hy
    have hzu : u ((sec (u y))⁻¹ * y) = 0 := by rw [hc.u_mul_inv hy₀ hy, hsecu, sub_self]
    have hvy : v y = v (sec (u y)) + v ((sec (u y))⁻¹ * y) := by
      have h1 := hc.mul_v _ hy₀ _ hz
      rw [mul_inv_cancel_left, hzu, map_zero, mul_zero, sub_zero] at h1
      exact h1
    have hv2 : v (x * y * x⁻¹) =
        v (x * sec (u y) * x⁻¹) + v (x * ((sec (u y))⁻¹ * y) * x⁻¹) := by
      have e : x * y * x⁻¹ = (x * sec (u y) * x⁻¹) * (x * ((sec (u y))⁻¹ * y) * x⁻¹) := by group
      rw [e, hc.mul_v _ (hconjT x hxT _ hy₀) _ (hconjT x hxT _ hz), hxA _ hz hzu, map_zero,
        mul_zero, sub_zero]
    rw [hv2, hvA _ hz hzu, hvy, map_add, hDdef]
    ring
  have hDadd : ∀ a b, D (a + b) = D a + D b := by
    intro a b
    have ha := hsecT a
    have hb := hsecT b
    have h1 := hD _ (mul_mem ha hb)
    rw [show x * (sec a * sec b) * x⁻¹ = (x * sec a * x⁻¹) * (x * sec b * x⁻¹) by group,
      hc.mul_v _ (hconjT x hxT _ ha) _ (hconjT x hxT _ hb), hD _ ha, hD _ hb, hu _ ha, hu _ hb,
      hc.mul_v _ ha _ hb, hc.mul_u _ ha _ hb, hsecu, hsecu] at h1
    simp only [map_sub, map_add, map_mul, hτσ] at h1
    linear_combination -h1
  have hDσ : ∀ a, σ (D a) = D a := by
    intro a
    have ha := hsecT a
    have r1 := hc.rel _ (hconjT x hxT _ ha)
    have r2 := hc.rel _ ha
    rw [hD _ ha, hu _ ha, hsecu] at r1
    rw [hsecu] at r2
    have r3 := congrArg (fun z => μ * σ μ * τ z) r2
    simp only [map_add, map_mul, hτσ, hσσ, map_zero, mul_zero] at r1 r3
    have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
    linear_combination r1 - r3 - D a * h2
  have hs' : s' = τ μ₀ := by
    have h1 := hφμ 1
    rw [mul_one, hφτ, hφτ, map_one, mul_one] at h1
    have h2 : s' * μ = τ μ₀ * μ := by rw [← h1]; ring
    exact mul_right_cancel₀ hμ0 h2
  have hcomp : ∀ a, D (μ₀ * a) = τ μ₀ * σ (τ μ₀) * D a +
      TraceForm.form σ (c' - μ * τ c₀) (τ μ₀ * (μ * τ a)) := by
    intro a
    have ha := hsecT a
    have hdy := hconjT d hdT _ ha
    have hxy := hconjT x hxT _ ha
    have e : x * (d * sec a * d⁻¹) * x⁻¹ =
        (x * d * x⁻¹) * (x * sec a * x⁻¹) * (x * d * x⁻¹)⁻¹ := by group
    have h1 := hD _ hdy
    rw [e, (hg _ hxy).2, hD _ ha, hu _ ha, (hd _ ha).2, (hd _ ha).1, hsecu, hs'] at h1
    simp only [TraceForm.form, map_add, map_mul, map_sub, hτσ] at h1 ⊢
    linear_combination -h1
  obtain ⟨e, he⟩ := SemilinearField.exists_form_of_shift hf hσ hE hF hμ₀o
    (AddMonoidHom.mk' D hDadd) hDσ τ hcomp
  refine ⟨μ, hμ0, τ, e, fun y hy => ⟨hu y hy, ?_⟩⟩
  rw [hD y hy]
  congr 1
  exact he (u y)

end U3RootCoords

structure U3SemilinearCoords {G : Type*} [Group G] (L T : Subgroup G) (f : ℕ) {E : Type*}
    [Field E] (σ : E →+* E) (u v : G → E) : Prop where
  card : Nat.card E = (2 ^ f) ^ 2
  sigma : ∀ x, σ x = x ^ (2 ^ f)
  card_fixed : Nat.card {x : E // σ x = x} = 2 ^ f
  coords : U3RootCoords (szT₁ L T) σ u v
  mem_szA₁_iff : ∀ y ∈ szT₁ L T, (y ∈ szA₁ (szT₁ L T) ↔ u y = 0)
  semilinear : ∀ x ∈ normalizer (L : Set G), x ∈ normalizer (szT₁ L T : Set G) →
    ∃ μ : E, μ ≠ 0 ∧ ∃ τ : E →+* E, ∃ e : E, ∀ y ∈ szT₁ L T,
      u (x * y * x⁻¹) = μ * τ (u y) ∧
        v (x * y * x⁻¹) = μ * σ μ * τ (v y) + TraceForm.form σ e (μ * τ (u y))

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem exists_semilinearCoords_of_card_sylow
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2) (σ : E →+* E) (u v : G → E),
      U3SemilinearCoords L T f σ u v := by
  obtain ⟨E, hE, hF, hch, σ, hcard, hσ, hfix, u, v, hc, hA, hborel, d, hdL, hdT, μ₀, -, hμ₀o,
    hμ₀⟩ := h.exists_rootCoords_borel_of_card_sylow hS2
  exact ⟨E, hE, hF, hch, σ, u, v, hcard, hσ, hfix, hc, hA, fun x hxL hxT =>
    hc.exists_semilinear h.two_le hσ hcard hfix hA hborel hdL hdT hμ₀o hμ₀ hxL hxT⟩

end U3Start

end CFSG.SeitzReduction.RankOne
