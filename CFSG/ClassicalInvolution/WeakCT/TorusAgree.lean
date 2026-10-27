module

public import CFSG.ClassicalInvolution.WeakCT.Torus
public import CFSG.ClassicalInvolution.WeakCT.Center

public section

namespace CFSG.ClassicalInvolution.WeakCT

open Matrix
open scoped MatrixGroups

section Abstract

variable {X : Type*} [Group X]

theorem le_of_centralizer_of_card_lt {M T T' A C : Subgroup X} [Finite T] (hTM : T ≤ M)
    (hAT : ∀ a ∈ A, ∀ t ∈ T, a * t = t * a) (hAC : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a)
    (hCM : ∀ c ∈ C, ∀ m ∈ M, c * m * c⁻¹ ∈ M)
    (hT : ∀ m ∈ M, (∀ a ∈ A, a * m = m * a) → m ∈ T)
    (hcard : Nat.card (MulAut T) < Nat.card C)
    (hT' : ∀ d ∈ C, d ≠ 1 → ∀ m ∈ M, d * m = m * d → m ∈ T') : T ≤ T' := by
  have key : ∀ c ∈ C, ∀ t ∈ T, c * t * c⁻¹ ∈ T := by
    intro c hc t ht
    refine hT _ (hCM c hc t (hTM ht)) fun a ha => ?_
    have h1 : a * c = c * a := hAC a ha c hc
    have h2 : a * t = t * a := hAT a ha t ht
    have h3 : a * c⁻¹ = c⁻¹ * a := (Commute.inv_right h1).eq
    calc a * (c * t * c⁻¹) = (a * c) * t * c⁻¹ := by group
      _ = c * (a * t) * c⁻¹ := by rw [h1]; group
      _ = c * (t * a) * c⁻¹ := by rw [h2]
      _ = c * t * (a * c⁻¹) := by group
      _ = c * t * (c⁻¹ * a) := by rw [h3]
      _ = c * t * c⁻¹ * a := by group
  have hnorm : C ≤ Subgroup.normalizer (T : Set X) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro t
    refine ⟨fun ht => key c hc t ht, fun ht => ?_⟩
    have := key c⁻¹ (C.inv_mem hc) _ ht
    simpa [mul_assoc] using this
  let φ : C →* MulAut T := T.normalizerMonoidHom.comp (Subgroup.inclusion hnorm)
  have hφ : ¬ Function.Injective φ := fun hinj =>
    absurd (Nat.card_le_card_of_injective _ hinj) (not_le.mpr hcard)
  rw [injective_iff_map_eq_one] at hφ
  obtain ⟨x, hx⟩ := not_forall.mp hφ
  obtain ⟨hx1, hx⟩ := not_imp.mp hx
  have hxker : Subgroup.inclusion hnorm x ∈ T.normalizerMonoidHom.ker := hx1
  rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf,
    Subgroup.mem_centralizer_iff] at hxker
  intro t ht
  refine hT' (x : X) x.2 (fun h => hx (Subtype.ext h)) t (hTM ht) ?_
  exact (hxker t ht).symm

theorem commute_of_map_commute {G : Type*} [Group G] (θ : G →* X)
    (hker : θ.ker ≤ Subgroup.center G) (B : Subgroup G)
    (hB : ∀ b ∈ B, b ∈ Subgroup.center G → b = 1) {x d : G} (hx : x ∈ B)
    (hd : d * x * d⁻¹ ∈ B) (h : θ x * θ d = θ d * θ x) : x * d = d * x := by
  have hmem : x * d * x⁻¹ * d⁻¹ ∈ B := by
    have : x * d * x⁻¹ * d⁻¹ = x * (d * x * d⁻¹)⁻¹ := by group
    rw [this]
    exact mul_mem hx (inv_mem hd)
  have hz : x * d * x⁻¹ * d⁻¹ ∈ θ.ker := by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [h]
    group
  have hz1 : x * d * x⁻¹ * d⁻¹ = 1 := hB _ hmem (hker hz)
  calc x * d = (x * d * x⁻¹ * d⁻¹) * (d * x) := by group
    _ = d * x := by rw [hz1, one_mul]

end Abstract

section Centralizer

variable {K : Type} [Field K] {X : Type} [Group X]

theorem B12_center (b : SL(3, K)) (hb : b ∈ B12 K) (hz : b ∈ Subgroup.center SL(3, K)) :
    b = 1 := by
  obtain ⟨A, rfl⟩ := hb
  rw [eq_one_of_blockSL_mem_center (by omega) (by omega) hz, map_one]

theorem B23_center (b : SL(3, K)) (hb : b ∈ B23 K) (hz : b ∈ Subgroup.center SL(3, K)) :
    b = 1 := by
  obtain ⟨A, rfl⟩ := hb
  rw [eq_one_of_blockSL_mem_center (by omega) (by omega) hz, map_one]

theorem mem_diagTorus2_of_map_commute_one {θ : SL(3, K) →* X}
    (hker : θ.ker ≤ Subgroup.center SL(3, K)) {s : Kˣ} (hs : s ≠ 1) {A : SL(2, K)}
    (h : θ (blockSL K 3 2 1 (by omega) A) * θ (blockSL K 3 2 0 (by omega) (torusHom K s)) =
      θ (blockSL K 3 2 0 (by omega) (torusHom K s)) * θ (blockSL K 3 2 1 (by omega) A)) :
    A ∈ diagTorus2 K := by
  have hd : blockSL K 3 2 0 (by omega) (torusHom K s) * blockSL K 3 2 1 (by omega) A *
      (blockSL K 3 2 0 (by omega) (torusHom K s))⁻¹ ∈ B23 K :=
    D12_conj_mem_B23 (mem_D12_iff.mpr ⟨s, rfl⟩) ⟨A, rfl⟩
  exact mem_diagTorus2_of_commute_one hs
    (commute_of_map_commute θ hker (B23 K) B23_center ⟨A, rfl⟩ hd h)

theorem mem_diagTorus2_of_map_commute_zero {θ : SL(3, K) →* X}
    (hker : θ.ker ≤ Subgroup.center SL(3, K)) {s : Kˣ} (hs : s ≠ 1) {A : SL(2, K)}
    (h : θ (blockSL K 3 2 0 (by omega) A) * θ (blockSL K 3 2 1 (by omega) (torusHom K s)) =
      θ (blockSL K 3 2 1 (by omega) (torusHom K s)) * θ (blockSL K 3 2 0 (by omega) A)) :
    A ∈ diagTorus2 K := by
  have hd : blockSL K 3 2 1 (by omega) (torusHom K s) * blockSL K 3 2 0 (by omega) A *
      (blockSL K 3 2 1 (by omega) (torusHom K s))⁻¹ ∈ B12 K :=
    D23_conj_mem_B12 (mem_D23_iff.mpr ⟨s, rfl⟩) ⟨A, rfl⟩
  exact mem_diagTorus2_of_commute_zero hs
    (commute_of_map_commute θ hker (B12 K) B12_center ⟨A, rfl⟩ hd h)

end Centralizer

section Agree

variable {K : Type} [Field K] [Finite K] {X : Type} [Group X]

theorem exists_unit_ne_one (hK : 3 ≤ Nat.card K) : ∃ s : Kˣ, s ≠ 1 := by
  have h2 : Nat.card Kˣ = Nat.card K - 1 := Nat.card_units K
  have h3 : 1 < Nat.card Kˣ := by omega
  have := Finite.one_lt_card_iff_nontrivial.mp h3
  exact exists_ne 1

theorem isCyclic_diagTorus2 : IsCyclic (diagTorus2 K) :=
  isCyclic_of_surjective (torusHom K).rangeRestrict (MonoidHom.rangeRestrict_surjective _)

theorem one_lt_card_diagTorus2 (hK : 3 ≤ Nat.card K) : 1 < Nat.card (diagTorus2 K) := by
  obtain ⟨s, hs⟩ := exists_unit_ne_one hK
  rw [Finite.one_lt_card_iff_nontrivial]
  refine ⟨⟨⟨_, s, rfl⟩, 1, fun h => hs ?_⟩⟩
  have h1 : torusHom K s = torusHom K 1 := by
    rw [map_one]
    exact congrArg Subtype.val h
  exact torusHom_injective h1

theorem finite_map_subgroup {G N : Type*} [Group G] [Group N] (H : Subgroup G) (g : G →* N)
    [Finite H] : Finite (H.map g) :=
  inferInstanceAs (Finite ↥(g '' (H : Set G)))

theorem card_mulAut_lt (G : Type*) [Group G] [Finite G] [IsCyclic G] (h : 1 < Nat.card G) :
    Nat.card (MulAut G) < Nat.card G := by
  rw [IsCyclic.card_mulAut]
  exact Nat.totient_lt _ h

theorem torus_agree (hK : 3 ≤ Nat.card K) {θ₁ θ₂ : SL(3, K) →* X}
    (h₁ : θ₁.ker ≤ Subgroup.center SL(3, K)) (h₂ : θ₂.ker ≤ Subgroup.center SL(3, K))
    (hM : (B23 K).map θ₁ = (B12 K).map θ₂)
    (hcomm : ∀ x ∈ (B12 K).map θ₁, ∀ y ∈ (B23 K).map θ₂, x * y = y * x) :
    (D23 K).map θ₁ = (D12 K).map θ₂ := by
  obtain ⟨s₀, hs₀⟩ := exists_unit_ne_one hK
  have : Finite ((D23 K).map θ₁) := finite_map_subgroup _ _
  have : Finite ((D12 K).map θ₂) := finite_map_subgroup _ _
  have hcyc : IsCyclic ((D23 K).map θ₁) := by
    rw [map_D23]
    exact (MulEquiv.isCyclic (Subgroup.equivMapOfInjective _ _
      (comp_blockSL_injective h₁ _ (by omega)))).1 isCyclic_diagTorus2
  have hcard₁ : Nat.card ((D23 K).map θ₁) = Nat.card (diagTorus2 K) := by
    rw [map_D23]
    exact Subgroup.card_map_of_injective (comp_blockSL_injective h₁ _ (by omega))
  have hcard₂ : Nat.card ((D23 K).map θ₂) = Nat.card (diagTorus2 K) := by
    rw [map_D23]
    exact Subgroup.card_map_of_injective (comp_blockSL_injective h₂ _ (by omega))
  have hcard₃ : Nat.card ((D12 K).map θ₂) = Nat.card (diagTorus2 K) := by
    rw [map_D12]
    exact Subgroup.card_map_of_injective (comp_blockSL_injective h₂ _ (by omega))
  have hle : (D23 K).map θ₁ ≤ (D12 K).map θ₂ := by
    refine le_of_centralizer_of_card_lt (M := (B12 K).map θ₂)
      (A := (D12 K).map θ₁) (C := (D23 K).map θ₂) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact (Subgroup.map_mono D23_le_B23).trans hM.le
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨t, ht, rfl⟩
      rw [← map_mul, ← map_mul, D12_D23_comm ha ht]
    · intro a ha c hc
      exact hcomm a (Subgroup.map_mono D12_le_B12 ha) c (Subgroup.map_mono D23_le_B23 hc)
    · rintro _ ⟨c, hc, rfl⟩ _ ⟨m, hm, rfl⟩
      exact ⟨c * m * c⁻¹, D23_conj_mem_B12 hc hm, by simp⟩
    · intro m hm hcentral
      rw [← hM] at hm
      obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := hm
      have hA := mem_diagTorus2_of_map_commute_one h₁ hs₀ (A := A)
        (hcentral _ ⟨_, mem_D12_iff.mpr ⟨s₀, rfl⟩, rfl⟩).symm
      exact ⟨_, ⟨A, hA, rfl⟩, rfl⟩
    · rw [hcard₂]
      calc Nat.card (MulAut ((D23 K).map θ₁)) < Nat.card ((D23 K).map θ₁) :=
            card_mulAut_lt _ (by rw [hcard₁]; exact one_lt_card_diagTorus2 hK)
        _ = Nat.card (diagTorus2 K) := hcard₁
    · rintro _ ⟨d, hd, rfl⟩ hd1 _ ⟨m, ⟨A, rfl⟩, rfl⟩ hdm
      obtain ⟨t, rfl⟩ := mem_D23_iff.mp hd
      have ht : t ≠ 1 := fun h => by
        subst h
        exact hd1 (by simp)
      have hA := mem_diagTorus2_of_map_commute_zero h₂ ht (A := A) hdm.symm
      exact ⟨_, ⟨A, hA, rfl⟩, rfl⟩
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard₃, hcard₁])

end Agree

end CFSG.ClassicalInvolution.WeakCT
