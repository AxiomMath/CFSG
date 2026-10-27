module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsS6
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsModel2
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6Datum

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin A6Facts
open scoped commutatorElement

section Simple

variable {G : Type*} [Group G]

theorem commutator_zpowers_eq_of_simple {K : Subgroup G} (hK : IsSimpleGroup ↥K) {u : G}
    (hu : u ∈ Subgroup.normalizer (K : Set G)) (hnc : ¬ ∀ k ∈ K, u * k = k * u) :
    ⁅K, Subgroup.zpowers u⁆ = K := by
  set C := ⁅K, Subgroup.zpowers u⁆ with hC
  have hz : Subgroup.zpowers u ≤ Subgroup.normalizer (K : Set G) := Subgroup.zpowers_le.mpr hu
  have hCK : C ≤ K := by
    rw [hC, Subgroup.commutator_le]
    intro k hk w hw
    have hwk : w * k⁻¹ * w⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hz hw) k⁻¹).mp (K.inv_mem hk)
    have : ⁅k, w⁆ = k * (w * k⁻¹ * w⁻¹) := by rw [commutatorElement_def]; group
    rw [this]
    exact K.mul_mem hk hwk
  have hconj : ∀ k ∈ K, ∀ c ∈ C, k * c * k⁻¹ ∈ C := by
    intro k hk c hc
    have hc' := hc
    rw [hC, Subgroup.commutator_def] at hc'
    refine Subgroup.closure_induction (p := fun c _ => k * c * k⁻¹ ∈ C) ?_ ?_ ?_ ?_ hc'
    · rintro _ ⟨g₁, hg₁, g₂, hg₂, rfl⟩
      have e : k * ⁅g₁, g₂⁆ * k⁻¹ = ⁅k * g₁, g₂⁆ * ⁅k, g₂⁆⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact C.mul_mem (Subgroup.commutator_mem_commutator (K.mul_mem hk hg₁) hg₂)
        (C.inv_mem (Subgroup.commutator_mem_commutator hk hg₂))
    · simp
    · intro a b _ _ ha hb
      have : k * (a * b) * k⁻¹ = (k * a * k⁻¹) * (k * b * k⁻¹) := by group
      rw [this]; exact C.mul_mem ha hb
    · intro a _ ha
      have : k * a⁻¹ * k⁻¹ = (k * a * k⁻¹)⁻¹ := by group
      rw [this]; exact C.inv_mem ha
  have hnorm : (C.subgroupOf K).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : (n : G) ∈ C := hn
    show ((g * n * g⁻¹ : ↥K) : G) ∈ C
    have : ((g * n * g⁻¹ : ↥K) : G) = (g : G) * n * (g : G)⁻¹ := rfl
    rw [this]
    exact hconj g g.2 n hn'
  rcases hK.eq_bot_or_eq_top_of_normal (C.subgroupOf K) with h | h
  · exfalso
    apply hnc
    intro k hk
    have hkC : ⁅k, u⁆ ∈ C := Subgroup.commutator_mem_commutator hk (Subgroup.mem_zpowers u)
    have h1 : (⟨⁅k, u⁆, hCK hkC⟩ : ↥K) ∈ C.subgroupOf K := hkC
    rw [h, Subgroup.mem_bot] at h1
    have h2 : k * u * k⁻¹ * u⁻¹ = 1 := congrArg Subtype.val h1
    have h3 : k * u * k⁻¹ = u := mul_inv_eq_one.mp h2
    calc u * k = (k * u * k⁻¹) * k := by rw [h3]
      _ = k * u := by group
  · apply le_antisymm hCK
    intro k hk
    have : (⟨k, hk⟩ : ↥K) ∈ C.subgroupOf K := by rw [h]; trivial
    exact this

end Simple

section Part22

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  {N : Notation25 hs}

theorem A6Datum.exists_s6_inducesAut (D : A6Datum N) (hKH : N.H ≤ Subgroup.normalizer (N.K : Set G))
    (hsimple : IsSimpleGroup ↥N.K) (hK : Nat.card N.K = 360) {u : G} (huH : u ∈ N.H)
    (hu : D.Φ u ∈ s6) :
    ∃ (φ : ↥N.K ≃* alternatingGroup (Fin 6)) (σ : Equiv.Perm (Fin 6)),
      InducesAut u N.K φ (MulAut.conjNormal σ) := by
  obtain ⟨θ, hθinj, hθeven⟩ := exists_s6_hom
  have hKs6 : ∀ k : ↥N.K, D.Φ (k : G) ∈ s6 := fun k => psl29_le_s6 (D.K_mem _ k.2)
  let φ₀ : ↥N.K →* Equiv.Perm (Fin 6) :=
    { toFun := fun k => θ ⟨D.Φ (k : G), hKs6 k⟩
      map_one' := by
        have : (⟨D.Φ ((1 : ↥N.K) : G), hKs6 1⟩ : ↥s6) = 1 := by
          apply Subtype.ext
          show D.Φ 1 = 1
          exact D.Φ_one
        rw [this]
        exact θ.map_one
      map_mul' := fun a b => by
        have : (⟨D.Φ ((a * b : ↥N.K) : G), hKs6 (a * b)⟩ : ↥s6) =
            ⟨D.Φ a, hKs6 a⟩ * ⟨D.Φ b, hKs6 b⟩ := by
          apply Subtype.ext
          show D.Φ ((a : G) * b) = D.Φ a * D.Φ b
          exact D.mul a (N.K_le_H a.2) b (N.K_le_H b.2)
        show θ _ = θ _ * θ _
        rw [this, θ.map_mul] }
  have hφ₀even : ∀ k : ↥N.K, φ₀ k ∈ alternatingGroup (Fin 6) := fun k =>
    hθeven ⟨D.Φ (k : G), hKs6 k⟩ (D.K_mem _ k.2)
  let φ₁ : ↥N.K →* ↥(alternatingGroup (Fin 6)) := φ₀.codRestrict _ hφ₀even
  have hinj : Function.Injective φ₁ := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have h1 : φ₀ k = 1 := congrArg Subtype.val hk
    have h2 : (⟨D.Φ (k : G), hKs6 k⟩ : ↥s6) = 1 := hθinj (h1.trans θ.map_one.symm)
    have h3 : D.Φ (k : G) = 1 := congrArg Subtype.val h2
    apply Subtype.ext
    have h4 : D.Φ (k : G) = D.Φ 1 := by rw [h3, D.Φ_one]
    exact D.inj_K hsimple k.2 N.K.one_mem h4
  have hA : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have hbij : Function.Bijective φ₁ :=
    hinj.bijective_of_nat_card_le (by rw [hA, hK])
  refine ⟨MulEquiv.ofBijective φ₁ hbij, (θ ⟨D.Φ u, hu⟩)⁻¹, hKH huH, ?_⟩
  intro y y' hy'
  have hyH := N.K_le_H y.2
  have hΦ : D.Φ (y' : G) = (D.Φ u)⁻¹ * D.Φ (y : G) * D.Φ u := by
    rw [hy', D.mul _ (N.H.mul_mem (N.H.inv_mem huH) hyH) _ huH,
      D.mul _ (N.H.inv_mem huH) _ hyH, D.Φ_inv huH]
  have hθ : (⟨D.Φ (y' : G), hKs6 y'⟩ : ↥s6) =
      (⟨D.Φ u, hu⟩ : ↥s6)⁻¹ * ⟨D.Φ (y : G), hKs6 y⟩ * ⟨D.Φ u, hu⟩ := by
    apply Subtype.ext
    exact hΦ
  apply Subtype.ext
  show φ₀ y' = _
  have : φ₀ y' = θ ⟨D.Φ (y' : G), hKs6 y'⟩ := rfl
  rw [this, hθ, θ.map_mul, θ.map_mul, θ.map_inv]
  simp [φ₁, φ₀]

theorem A6Datum.mem_S_of_centralizes_z (D : A6Datum N) (hK0 : N.K0 = N.K)
    (hKH : N.H ≤ Subgroup.normalizer (N.K : Set G)) (h254 : Facts254 N)
    (hsimple : IsSimpleGroup ↥N.K) (hzS : N.z ∈ centerOf N.S) {c : G} (hcH : c ∈ N.H)
    (hcz : c * N.z = N.z * c) : c ∈ N.S := by
  have hzS' : N.z ∈ N.S := hzS.1
  have hzH : N.z ∈ N.H := N.S_le_H hzS'
  have hz1 : D.Φ N.z ≠ 1 := fun h1 => h254.z_not_mem (D.mem_SC_of_Φ_eq_one hK0 hzS' h1)
  have hΦzP : D.Φ N.z ∈ P0 := D.S_mem _ hzS'
  have hcent : ∀ p ∈ P0, D.Φ N.z * p = p * D.Φ N.z := by
    intro p hp
    obtain ⟨s, hs, rfl⟩ := D.S_surj p hp
    have hsz : N.z * s = s * N.z := (Subgroup.mem_centralizer_iff.mp hzS.2 s hs).symm
    rw [← D.mul _ hzH _ (N.S_le_H hs), ← D.mul _ (N.S_le_H hs) _ hzH, hsz]
  have hΦc : D.Φ c ∈ P0 := by
    refine centralizer_le_P0_of_central hΦzP hz1 hcent (D.mem c hcH) ?_
    rw [← D.mul _ hcH _ hzH, ← D.mul _ hzH _ hcH, hcz]
  obtain ⟨s, hs, hsc⟩ := D.S_surj _ hΦc
  have hsH := N.S_le_H hs
  have h1 : D.Φ (s⁻¹ * c) = 1 := by
    rw [D.mul _ (N.H.inv_mem hsH) _ hcH, D.Φ_inv hsH, hsc, inv_mul_cancel]
  have h2 := (D.ker _ (N.H.mul_mem (N.H.inv_mem hsH) hcH)).mp h1
  have hZ : ∀ x ∈ N.K, (∀ y ∈ N.K, x * y = y * x) → x = 1 := fun x hx hc =>
    N.center_K_trivial hsimple hx hc
  have h3 : s⁻¹ * c ∈ N.S := N.mem_S_of_centralizes hKH h254 hZ (N.H.mul_mem (N.H.inv_mem hsH) hcH) h2
  have : c = s * (s⁻¹ * c) := by group
  rw [this]
  exact N.S.mul_mem hs h3

end Part22

end CFSG.QuasithinUnique
