module

public import CFSG.Mathlib.FieldTheory.Finite.FrobeniusEightCoordinates
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialOuterQ3

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterQ2Three

open CFSG.Blueprint.Chevalley CFSG.FrobeniusEightCoordinates

private theorem commute_conj_of_conj_scale {G : Type*} [Group G] {z z₀ h₀ P P' : G}
    (hT : Commute z (z₀ * h₀ * z₀⁻¹)) (hA : Commute z (z₀ * P * z₀⁻¹))
    (hscale : h₀ * P * h₀⁻¹ = P') :
    Commute z (z₀ * P' * z₀⁻¹) := by
  have h' := (hT.mul_right hA).mul_right hT.inv_right
  have e : (z₀ * h₀ * z₀⁻¹) * (z₀ * P * z₀⁻¹) * (z₀ * h₀ * z₀⁻¹)⁻¹ =
      z₀ * (h₀ * P * h₀⁻¹) * z₀⁻¹ := by group
  rw [e, hscale] at h'
  exact h'

private theorem pair_triple_product {G : Type*} [Group G] (A0 B0 C0 A1 B1 C1 : G)
    (hCA : Commute C0 A1) (hBA : Commute B0 A1) (hCB : Commute C0 B1) :
    (A0 * B0 * C0) * (A1 * B1 * C1) = (A0 * A1) * (B0 * B1) * (C0 * C1) := by
  calc
    (A0 * B0 * C0) * (A1 * B1 * C1) = A0 * B0 * (C0 * A1) * B1 * C1 := by group
    _ = A0 * B0 * (A1 * C0) * B1 * C1 := by rw [hCA.eq]
    _ = A0 * (B0 * A1) * C0 * B1 * C1 := by group
    _ = A0 * (A1 * B0) * C0 * B1 * C1 := by rw [hBA.eq]
    _ = (A0 * A1) * (B0 * C0) * B1 * C1 := by group
    _ = (A0 * A1) * B0 * (C0 * B1) * C1 := by group
    _ = (A0 * A1) * B0 * (B1 * C0) * C1 := by rw [hCB.eq]
    _ = (A0 * A1) * (B0 * B1) * (C0 * C1) := by group

private theorem cyclic_three {G : Type*} [Group G] {A B C : G}
    (hAB : Commute A B) (hAC : Commute A C) (hBC : Commute B C) :
    B * C * A = A * B * C := by
  calc
    B * C * A = B * (C * A) := by group
    _ = B * (A * C) := by rw [← hAC.eq]
    _ = (B * A) * C := by group
    _ = (A * B) * C := by rw [← hAB.eq]
    _ = A * B * C := by group

private theorem mul_three_involutions {G : Type*} [Group G] {A B C : G}
    (hAB : Commute A B) (hAC : Commute A C) (hBC : Commute B C)
    (hA : A * A = 1) (hB : B * B = 1) (hC : C * C = 1) :
    (A * B * C) * (A * B * C) = 1 := by
  calc
    (A * B * C) * (A * B * C) = A * B * (C * A) * B * C := by group
    _ = A * B * (A * C) * B * C := by rw [← hAC.eq]
    _ = A * (B * A) * C * B * C := by group
    _ = A * (A * B) * C * B * C := by rw [← hAB.eq]
    _ = (A * A) * (B * C) * B * C := by group
    _ = (B * C) * (B * C) := by rw [hA, one_mul]; group
    _ = B * (C * B) * C := by group
    _ = B * (B * C) * C := by rw [← hBC.eq]
    _ = (B * B) * (C * C) := by group
    _ = 1 := by rw [hB, hC, mul_one]

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.FrobeniusEightCoordinates
open scoped MatrixGroups

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]


private theorem not_isRoot_add_of_orthogonal (hsl : SimplyLacedTag τ)
    {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β)
    (h0 : iform α β = 0) : ¬ IsRoot τ (α + β) := by
  intro hr
  have hαn : iform α α = 2 := outer_iform_self_of_simplyLaced hsl hα
  have hβn : iform β β = 2 := outer_iform_self_of_simplyLaced hsl hβ
  have h4 : iform (α + β) (α + β) = 4 := by
    rw [iform_add_left, iform_add_right, iform_add_right, hαn, h0,
      iform_comm β α, h0, hβn]
    norm_num
  have h2 := outer_iform_self_of_simplyLaced hsl hr
  omega

private theorem rootTorus_conj_pinnedX_of_iform_neg_one {δ γ : Fin τ.rank → ℤ}
    (hδ : IsRoot τ δ) (hγ : IsRoot τ γ) (hδγ : iform δ γ = -1)
    (hδn : iform δ δ = 2) (lam : Lˣ) (s : L) :
    rootTorusSL2 τ L δ lam * pinnedX τ L γ s * (rootTorusSL2 τ L δ lam)⁻¹ =
      pinnedX τ L γ (((lam⁻¹ : Lˣ) : L) * s) := by
  have e : 2 * iform δ γ / iform δ δ = -1 := by
    rw [hδγ, hδn]
    norm_num
  rw [outer_rootTorusSL2_conj_pinnedX hδ hγ lam s, e]
  simp

private noncomputable def tripleFixedPoint (γ γ₁ γ₂ : Fin τ.rank → ℤ) (μ0 b tBase : L) (k : L) :
    ModGL τ L :=
  pinnedX τ L γ (tBase * k) *
    pinnedX τ L γ₁ (μ0 * (tBase * k) ^ 2) *
      pinnedX τ L γ₂ (b * (tBase * k) ^ 4)

private noncomputable def tripleScaledPoint (γ γ₁ γ₂ : Fin τ.rank → ℤ) (μ0 b tBase : L) (k c0 : L) :
    ModGL τ L :=
  pinnedX τ L γ (c0 * (tBase * k)) *
    pinnedX τ L γ₁ (c0 * (μ0 * (tBase * k) ^ 2)) *
      pinnedX τ L γ₂ (c0 * (b * (tBase * k) ^ 4))

private theorem tripleFixedPoint_mem {Ψ : Set (Fin τ.rank → ℤ)} {γ γ₁ γ₂ : Fin τ.rank → ℤ}
    {μ0 b tBase k : L} (hγ : γ ∈ Ψ) (hγ₁ : γ₁ ∈ Ψ) (hγ₂ : γ₂ ∈ Ψ) :
    tripleFixedPoint γ γ₁ γ₂ μ0 b tBase k ∈ rootSpan τ L Ψ := by
  unfold tripleFixedPoint
  exact mul_mem (mul_mem (pinnedX_mem_rootSpan hγ _) (pinnedX_mem_rootSpan hγ₁ _))
    (pinnedX_mem_rootSpan hγ₂ _)

private theorem tripleFixedPoint_fixed
    {φ₁ : ModGL τ L →* ModGL τ L} {γ γ₁ γ₂ : Fin τ.rank → ℤ}
    {μ0 μ1 μ2 b c tBase : L}
    (hu0 : ∀ t, φ₁ (pinnedX τ L γ t) = pinnedX τ L γ₁ (μ0 * t ^ 2))
    (hu1 : ∀ t, φ₁ (pinnedX τ L γ₁ t) = pinnedX τ L γ₂ (μ1 * t ^ 2))
    (hu2 : ∀ t, φ₁ (pinnedX τ L γ₂ t) = pinnedX τ L γ (μ2 * t ^ 2))
    (hb : b = μ1 * μ0 ^ 2) (hc : c = μ2 * b ^ 2)
    (hct : c * tBase ^ 8 = tBase)
    (hcomm01 : ∀ a b : L, Commute (pinnedX τ L γ a) (pinnedX τ L γ₁ b))
    (hcomm12 : ∀ a b : L, Commute (pinnedX τ L γ₁ a) (pinnedX τ L γ₂ b))
    (hcomm02 : ∀ a b : L, Commute (pinnedX τ L γ a) (pinnedX τ L γ₂ b))
    {k : L} (hk : k ^ 8 = k) :
    φ₁ (tripleFixedPoint γ γ₁ γ₂ μ0 b tBase k) =
      tripleFixedPoint γ γ₁ γ₂ μ0 b tBase k := by
  unfold tripleFixedPoint
  rw [map_mul, map_mul]
  rw [hu0, hu1, hu2]
  have e1 : μ1 * (μ0 * (tBase * k) ^ 2) ^ 2 = b * (tBase * k) ^ 4 := by
    rw [hb]
    ring
  have e2 : μ2 * (b * (tBase * k) ^ 4) ^ 2 = tBase * k := by
    calc μ2 * (b * (tBase * k) ^ 4) ^ 2 = c * (tBase * k) ^ 8 := by
          rw [hc]
          ring
      _ = c * tBase ^ 8 * k ^ 8 := by ring
      _ = tBase * k := by rw [hct, hk]
  rw [e1, e2]
  have hAB : Commute (pinnedX τ L γ (tBase * k))
      (pinnedX τ L γ₁ (μ0 * (tBase * k) ^ 2)) := hcomm01 _ _
  have hAC : Commute (pinnedX τ L γ (tBase * k))
      (pinnedX τ L γ₂ (b * (tBase * k) ^ 4)) := hcomm02 _ _
  exact cyclic_three hAB hAC (hcomm12 _ _)

private theorem tripleFixedPoint_sq [CharP L 2]
    {γ γ₁ γ₂ : Fin τ.rank → ℤ} {μ0 b tBase k : L}
    (hcomm01 : ∀ a b : L, Commute (pinnedX τ L γ a) (pinnedX τ L γ₁ b))
    (hcomm12 : ∀ a b : L, Commute (pinnedX τ L γ₁ a) (pinnedX τ L γ₂ b))
    (hcomm02 : ∀ a b : L, Commute (pinnedX τ L γ a) (pinnedX τ L γ₂ b)) :
    tripleFixedPoint γ γ₁ γ₂ μ0 b tBase k *
        tripleFixedPoint γ γ₁ γ₂ μ0 b tBase k = 1 := by
  unfold tripleFixedPoint
  have hA : pinnedX τ L γ (tBase * k) * pinnedX τ L γ (tBase * k) = 1 := by
    rw [← pinnedX_add, CharTwo.add_self_eq_zero, pinnedX_zero]
  have hB : pinnedX τ L γ₁ (μ0 * (tBase * k) ^ 2) *
      pinnedX τ L γ₁ (μ0 * (tBase * k) ^ 2) = 1 := by
    rw [← pinnedX_add, CharTwo.add_self_eq_zero, pinnedX_zero]
  have hC : pinnedX τ L γ₂ (b * (tBase * k) ^ 4) *
      pinnedX τ L γ₂ (b * (tBase * k) ^ 4) = 1 := by
    rw [← pinnedX_add, CharTwo.add_self_eq_zero, pinnedX_zero]
  have hAB : Commute (pinnedX τ L γ (tBase * k))
      (pinnedX τ L γ₁ (μ0 * (tBase * k) ^ 2)) := hcomm01 _ _
  have hAC : Commute (pinnedX τ L γ (tBase * k))
      (pinnedX τ L γ₂ (b * (tBase * k) ^ 4)) := hcomm02 _ _
  have hBC : Commute (pinnedX τ L γ₁ (μ0 * (tBase * k) ^ 2))
      (pinnedX τ L γ₂ (b * (tBase * k) ^ 4)) := hcomm12 _ _
  exact mul_three_involutions hAB hAC hBC hA hB hC

private theorem rootTorus_conj_tripleFixedPoint {δ γ γ₁ γ₂ : Fin τ.rank → ℤ}
    (hδ : IsRoot τ δ) (hγ : IsRoot τ γ) (hγ₁ : IsRoot τ γ₁) (hγ₂ : IsRoot τ γ₂)
    (hδγ : iform δ γ = -1) (hδγ₁ : iform δ γ₁ = -1) (hδγ₂ : iform δ γ₂ = -1)
    (hδn : iform δ δ = 2) (lam : Lˣ) {μ0 b tBase k c0 : L}
    (hc0 : ((lam⁻¹ : Lˣ) : L) = c0) :
    rootTorusSL2 τ L δ lam * tripleFixedPoint γ γ₁ γ₂ μ0 b tBase k *
        (rootTorusSL2 τ L δ lam)⁻¹ =
      tripleScaledPoint γ γ₁ γ₂ μ0 b tBase k c0 := by
  unfold tripleFixedPoint tripleScaledPoint
  rw [show rootTorusSL2 τ L δ lam *
        (pinnedX τ L γ (tBase * k) *
          pinnedX τ L γ₁ (μ0 * (tBase * k) ^ 2) *
            pinnedX τ L γ₂ (b * (tBase * k) ^ 4)) *
        (rootTorusSL2 τ L δ lam)⁻¹ =
      (rootTorusSL2 τ L δ lam * pinnedX τ L γ (tBase * k) *
          (rootTorusSL2 τ L δ lam)⁻¹) *
        (rootTorusSL2 τ L δ lam * pinnedX τ L γ₁ (μ0 * (tBase * k) ^ 2) *
          (rootTorusSL2 τ L δ lam)⁻¹) *
        (rootTorusSL2 τ L δ lam * pinnedX τ L γ₂ (b * (tBase * k) ^ 4) *
          (rootTorusSL2 τ L δ lam)⁻¹) by group]
  rw [rootTorus_conj_pinnedX_of_iform_neg_one hδ hγ hδγ hδn lam (tBase * k),
      rootTorus_conj_pinnedX_of_iform_neg_one hδ hγ₁ hδγ₁ hδn lam
        (μ0 * (tBase * k) ^ 2),
      rootTorus_conj_pinnedX_of_iform_neg_one hδ hγ₂ hδγ₂ hδn lam
        (b * (tBase * k) ^ 4)]
  rw [hc0]

private theorem tripleScaledPoint_commute [CharP L 2]
    {δ γ γ₁ γ₂ : Fin τ.rank → ℤ}
    (hδ : IsRoot τ δ) (hγ : IsRoot τ γ) (hγ₁ : IsRoot τ γ₁) (hγ₂ : IsRoot τ γ₂)
    (hδγ : iform δ γ = -1) (hδγ₁ : iform δ γ₁ = -1) (hδγ₂ : iform δ γ₂ = -1)
    (hδn : iform δ δ = 2) {z z₀ : ModGL τ L}
    (hδc : ∀ x ∈ rootRankOneGroup τ L δ, Commute z (z₀ * x * z₀⁻¹))
    {μ0 b tBase k c0 : L}
    (hA : Commute z (z₀ * tripleFixedPoint γ γ₁ γ₂ μ0 b tBase k * z₀⁻¹)) :
    Commute z (z₀ * tripleScaledPoint γ γ₁ γ₂ μ0 b tBase k c0 * z₀⁻¹) := by
  rcases eq_or_ne c0 0 with rfl | hc0
  · have h1 : tripleScaledPoint γ γ₁ γ₂ μ0 b tBase k 0 = 1 := by
      unfold tripleScaledPoint
      simp only [zero_mul, pinnedX_zero, mul_one]
    rw [h1]
    have e : z₀ * (1 : ModGL τ L) * z₀⁻¹ = 1 := by group
    rw [e]
    exact Commute.one_right z
  · let lam : Lˣ := (Units.mk0 c0 hc0)⁻¹
    have hlamc : ((lam⁻¹ : Lˣ) : L) = c0 := by
      dsimp only [lam]
      simp
    have hT : Commute z (z₀ * rootTorusSL2 τ L δ lam * z₀⁻¹) :=
      hδc _ ⟨HSL lam, rfl⟩
    have hscale : rootTorusSL2 τ L δ lam *
        tripleFixedPoint γ γ₁ γ₂ μ0 b tBase k * (rootTorusSL2 τ L δ lam)⁻¹ =
        tripleScaledPoint γ γ₁ γ₂ μ0 b tBase k c0 :=
      rootTorus_conj_tripleFixedPoint hδ hγ hγ₁ hγ₂ hδγ hδγ₁ hδγ₂ hδn lam hlamc
    exact commute_conj_of_conj_scale hT hA hscale

theorem outer_three_commute_nonfixed [CharP L 2] (hsl : SimplyLacedTag τ)
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    {f : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ} (hf : IsIsometry Ψ f)
    {φ₁ : ModGL τ L →* ModGL τ L} (hpin : OuterPinned φ₁ f 2) {z z₀ : ModGL τ L}
    (hfixc : ∀ g ∈ rootSpan τ L Ψ, φ₁ g = g → g * g = 1 → Commute z (z₀ * g * z₀⁻¹))
    {γ δ : Fin τ.rank → ℤ} (hγ : γ ∈ Ψ) (hper : f (f (f γ)) = γ)
    (horth : iform γ (f γ) = 0)
    (hδ : δ ∈ Ψ) (hfδ : f δ = δ) (hγδ : iform γ δ = -1)
    (hδc : ∀ x ∈ rootRankOneGroup τ L δ, Commute z (z₀ * x * z₀⁻¹)) :
    ∀ u, Commute z (z₀ * pinnedX τ L γ u * z₀⁻¹) := by
  intro u
  classical
  have hγr : IsRoot τ γ := hΨ.isRoot γ hγ
  have hfγmem : f γ ∈ Ψ := hf.bijOn.mapsTo hγ
  have hfγr : IsRoot τ (f γ) := hΨ.isRoot (f γ) hfγmem
  have hf2γmem : f (f γ) ∈ Ψ := hf.bijOn.mapsTo hfγmem
  have hf2γr : IsRoot τ (f (f γ)) := hΨ.isRoot (f (f γ)) hf2γmem
  have hδr : IsRoot τ δ := hΨ.isRoot δ hδ
  have hδn : iform δ δ = 2 := outer_iform_self_of_simplyLaced hsl hδr
  have h01 : iform γ (f γ) = 0 := horth
  have h12 : iform (f γ) (f (f γ)) = 0 := by
    rw [hf.iform_eq γ hγ (f γ) hfγmem]
    exact horth
  have h02 : iform γ (f (f γ)) = 0 := by
    have h := hf.iform_eq (f γ) hfγmem (f (f γ)) hf2γmem
    rw [hper, h12, iform_comm] at h
    exact h
  have hn01 : ¬ IsRoot τ (γ + f γ) :=
    not_isRoot_add_of_orthogonal hsl hγr hfγr h01
  have hn12 : ¬ IsRoot τ (f γ + f (f γ)) :=
    not_isRoot_add_of_orthogonal hsl hfγr hf2γr h12
  have hn02 : ¬ IsRoot τ (γ + f (f γ)) :=
    not_isRoot_add_of_orthogonal hsl hγr hf2γr h02
  have hcomm01 : ∀ a b : L, Commute (pinnedX τ L γ a) (pinnedX τ L (f γ) b) :=
    fun a b => outer_commute_pinnedX hγr hfγr h01 hn01 a b
  have hcomm12 : ∀ a b : L, Commute (pinnedX τ L (f γ) a) (pinnedX τ L (f (f γ)) b) :=
    fun a b => outer_commute_pinnedX hfγr hf2γr h12 hn12 a b
  have hcomm02 : ∀ a b : L, Commute (pinnedX τ L γ a) (pinnedX τ L (f (f γ)) b) :=
    fun a b => outer_commute_pinnedX hγr hf2γr h02 hn02 a b
  have hδγ : iform δ γ = -1 := by rw [iform_comm, hγδ]
  have hδγ₁ : iform δ (f γ) = -1 := by
    rw [iform_comm, ← hfδ, hf.iform_eq γ hγ δ hδ, hγδ]
  have hδγ₂ : iform δ (f (f γ)) = -1 := by
    have h := hδγ₁
    rw [iform_comm] at h
    rw [← hf.iform_eq (f γ) hfγmem δ hδ] at h
    rw [hfδ] at h
    rw [iform_comm] at h
    exact h
  obtain ⟨-, μ0, hμ0, hu0⟩ := hpin γ hγr
  obtain ⟨-, μ1, hμ1, hu1⟩ := hpin (f γ) hfγr
  obtain ⟨-, μ2, hμ2, hu2⟩ := hpin (f (f γ)) hf2γr
  rw [hper] at hu2
  let b : L := μ1 * μ0 ^ 2
  let c : L := μ2 * b ^ 2
  have hb : b = μ1 * μ0 ^ 2 := rfl
  have hc : c = μ2 * b ^ 2 := rfl
  have hb_ne : b ≠ 0 := by
    rw [hb]
    exact mul_ne_zero hμ1 (pow_ne_zero 2 hμ0)
  have hc_ne : c ≠ 0 := by
    rw [hc]
    exact mul_ne_zero hμ2 (pow_ne_zero 2 hb_ne)
  obtain ⟨tBase, htBase7⟩ := IsAlgClosed.exists_pow_nat_eq c⁻¹ (by norm_num : 0 < 7)
  have htBase_ne : tBase ≠ 0 := by
    intro h
    have h0 : c⁻¹ = 0 := by
      rw [← htBase7, h, zero_pow (by norm_num : (7 : ℕ) ≠ 0)]
    exact (inv_ne_zero hc_ne) h0
  have hct : c * tBase ^ 8 = tBase := by
    calc c * tBase ^ 8 = c * tBase * tBase ^ 7 := by ring
      _ = c * tBase * c⁻¹ := by rw [htBase7]
      _ = tBase := by
        rw [mul_comm c tBase, mul_assoc, mul_inv_cancel₀ hc_ne, mul_one]
  have hinv1 : tBase⁻¹ * tBase = 1 := by
    rw [mul_comm, mul_inv_cancel₀ htBase_ne]
  have hinv2 : tBase⁻¹ * tBase ^ 2 = tBase := by
    calc tBase⁻¹ * tBase ^ 2 = (tBase⁻¹ * tBase) * tBase := by ring
      _ = tBase := by rw [hinv1, one_mul]
  have hinv4 : tBase⁻¹ * tBase ^ 4 = tBase ^ 3 := by
    calc tBase⁻¹ * tBase ^ 4 = (tBase⁻¹ * tBase) * tBase ^ 3 := by ring
      _ = tBase ^ 3 := by rw [hinv1, one_mul]
  obtain ⟨x0, x1, x2, t0, t1, t2, ht0, ht1, ht2, hsum0, hsum2, hsum4⟩ :=
    exists_frob_eight_span_coeffs u
  let c0 : L := x0 * tBase⁻¹
  let c1 : L := x1 * tBase⁻¹
  let c2 : L := x2 * tBase⁻¹
  have hA0 : c0 * (tBase * t0) = x0 * t0 := by
    calc c0 * (tBase * t0) = (x0 * tBase⁻¹) * (tBase * t0) := by dsimp only [c0]
      _ = x0 * (tBase⁻¹ * tBase) * t0 := by ring
      _ = x0 * t0 := by rw [hinv1]; ring
  have hA1 : c1 * (tBase * t1) = x1 * t1 := by
    calc c1 * (tBase * t1) = (x1 * tBase⁻¹) * (tBase * t1) := by dsimp only [c1]
      _ = x1 * (tBase⁻¹ * tBase) * t1 := by ring
      _ = x1 * t1 := by rw [hinv1]; ring
  have hA2 : c2 * (tBase * t2) = x2 * t2 := by
    calc c2 * (tBase * t2) = (x2 * tBase⁻¹) * (tBase * t2) := by dsimp only [c2]
      _ = x2 * (tBase⁻¹ * tBase) * t2 := by ring
      _ = x2 * t2 := by rw [hinv1]; ring
  have hB0 : c0 * (μ0 * (tBase * t0) ^ 2) = μ0 * tBase * (x0 * t0 ^ 2) := by
    calc c0 * (μ0 * (tBase * t0) ^ 2) =
          (x0 * tBase⁻¹) * (μ0 * (tBase * t0) ^ 2) := by dsimp only [c0]
      _ = (x0 * μ0) * (tBase⁻¹ * tBase ^ 2) * t0 ^ 2 := by ring
      _ = (x0 * μ0) * tBase * t0 ^ 2 := by rw [hinv2]
      _ = μ0 * tBase * (x0 * t0 ^ 2) := by ring
  have hB1 : c1 * (μ0 * (tBase * t1) ^ 2) = μ0 * tBase * (x1 * t1 ^ 2) := by
    calc c1 * (μ0 * (tBase * t1) ^ 2) =
          (x1 * tBase⁻¹) * (μ0 * (tBase * t1) ^ 2) := by dsimp only [c1]
      _ = (x1 * μ0) * (tBase⁻¹ * tBase ^ 2) * t1 ^ 2 := by ring
      _ = (x1 * μ0) * tBase * t1 ^ 2 := by rw [hinv2]
      _ = μ0 * tBase * (x1 * t1 ^ 2) := by ring
  have hB2 : c2 * (μ0 * (tBase * t2) ^ 2) = μ0 * tBase * (x2 * t2 ^ 2) := by
    calc c2 * (μ0 * (tBase * t2) ^ 2) =
          (x2 * tBase⁻¹) * (μ0 * (tBase * t2) ^ 2) := by dsimp only [c2]
      _ = (x2 * μ0) * (tBase⁻¹ * tBase ^ 2) * t2 ^ 2 := by ring
      _ = (x2 * μ0) * tBase * t2 ^ 2 := by rw [hinv2]
      _ = μ0 * tBase * (x2 * t2 ^ 2) := by ring
  have hC0 : c0 * (b * (tBase * t0) ^ 4) = b * tBase ^ 3 * (x0 * t0 ^ 4) := by
    calc c0 * (b * (tBase * t0) ^ 4) =
          (x0 * tBase⁻¹) * (b * (tBase * t0) ^ 4) := by dsimp only [c0]
      _ = (x0 * b) * (tBase⁻¹ * tBase ^ 4) * t0 ^ 4 := by ring
      _ = (x0 * b) * tBase ^ 3 * t0 ^ 4 := by rw [hinv4]
      _ = b * tBase ^ 3 * (x0 * t0 ^ 4) := by ring
  have hC1 : c1 * (b * (tBase * t1) ^ 4) = b * tBase ^ 3 * (x1 * t1 ^ 4) := by
    calc c1 * (b * (tBase * t1) ^ 4) =
          (x1 * tBase⁻¹) * (b * (tBase * t1) ^ 4) := by dsimp only [c1]
      _ = (x1 * b) * (tBase⁻¹ * tBase ^ 4) * t1 ^ 4 := by ring
      _ = (x1 * b) * tBase ^ 3 * t1 ^ 4 := by rw [hinv4]
      _ = b * tBase ^ 3 * (x1 * t1 ^ 4) := by ring
  have hC2 : c2 * (b * (tBase * t2) ^ 4) = b * tBase ^ 3 * (x2 * t2 ^ 4) := by
    calc c2 * (b * (tBase * t2) ^ 4) =
          (x2 * tBase⁻¹) * (b * (tBase * t2) ^ 4) := by dsimp only [c2]
      _ = (x2 * b) * (tBase⁻¹ * tBase ^ 4) * t2 ^ 4 := by ring
      _ = (x2 * b) * tBase ^ 3 * t2 ^ 4 := by rw [hinv4]
      _ = b * tBase ^ 3 * (x2 * t2 ^ 4) := by ring
  have hsumA : c0 * (tBase * t0) + c1 * (tBase * t1) + c2 * (tBase * t2) = u := by
    rw [hA0, hA1, hA2]
    exact hsum0
  have hsumB : c0 * (μ0 * (tBase * t0) ^ 2) + c1 * (μ0 * (tBase * t1) ^ 2) +
      c2 * (μ0 * (tBase * t2) ^ 2) = 0 := by
    rw [hB0, hB1, hB2]
    rw [show μ0 * tBase * (x0 * t0 ^ 2) + μ0 * tBase * (x1 * t1 ^ 2) +
          μ0 * tBase * (x2 * t2 ^ 2) =
        μ0 * tBase * (x0 * t0 ^ 2 + x1 * t1 ^ 2 + x2 * t2 ^ 2) by ring,
      hsum2, mul_zero]
  have hsumC : c0 * (b * (tBase * t0) ^ 4) + c1 * (b * (tBase * t1) ^ 4) +
      c2 * (b * (tBase * t2) ^ 4) = 0 := by
    rw [hC0, hC1, hC2]
    rw [show b * tBase ^ 3 * (x0 * t0 ^ 4) + b * tBase ^ 3 * (x1 * t1 ^ 4) +
          b * tBase ^ 3 * (x2 * t2 ^ 4) =
        b * tBase ^ 3 * (x0 * t0 ^ 4 + x1 * t1 ^ 4 + x2 * t2 ^ 4) by ring,
      hsum4, mul_zero]
  have hfix0 : φ₁ (tripleFixedPoint γ (f γ) (f (f γ)) μ0 b tBase t0) =
      tripleFixedPoint γ (f γ) (f (f γ)) μ0 b tBase t0 :=
    tripleFixedPoint_fixed (γ := γ) (γ₁ := f γ) (γ₂ := f (f γ))
      (μ0 := μ0) (μ1 := μ1) (μ2 := μ2) (b := b) (c := c) (tBase := tBase)
      (k := t0) hu0 hu1 hu2 hb hc hct hcomm01 hcomm12 hcomm02 ht0
  have hfix1 : φ₁ (tripleFixedPoint γ (f γ) (f (f γ)) μ0 b tBase t1) =
      tripleFixedPoint γ (f γ) (f (f γ)) μ0 b tBase t1 :=
    tripleFixedPoint_fixed (γ := γ) (γ₁ := f γ) (γ₂ := f (f γ))
      (μ0 := μ0) (μ1 := μ1) (μ2 := μ2) (b := b) (c := c) (tBase := tBase)
      (k := t1) hu0 hu1 hu2 hb hc hct hcomm01 hcomm12 hcomm02 ht1
  have hfix2 : φ₁ (tripleFixedPoint γ (f γ) (f (f γ)) μ0 b tBase t2) =
      tripleFixedPoint γ (f γ) (f (f γ)) μ0 b tBase t2 :=
    tripleFixedPoint_fixed (γ := γ) (γ₁ := f γ) (γ₂ := f (f γ))
      (μ0 := μ0) (μ1 := μ1) (μ2 := μ2) (b := b) (c := c) (tBase := tBase)
      (k := t2) hu0 hu1 hu2 hb hc hct hcomm01 hcomm12 hcomm02 ht2
  have hsq0 : tripleFixedPoint γ (f γ) (f (f γ)) μ0 b tBase t0 *
      tripleFixedPoint γ (f γ) (f (f γ)) μ0 b tBase t0 = 1 :=
    tripleFixedPoint_sq (γ := γ) (γ₁ := f γ) (γ₂ := f (f γ))
      (μ0 := μ0) (b := b) (tBase := tBase) (k := t0) hcomm01 hcomm12 hcomm02
  have hsq1 : tripleFixedPoint γ (f γ) (f (f γ)) μ0 b tBase t1 *
      tripleFixedPoint γ (f γ) (f (f γ)) μ0 b tBase t1 = 1 :=
    tripleFixedPoint_sq (γ := γ) (γ₁ := f γ) (γ₂ := f (f γ))
      (μ0 := μ0) (b := b) (tBase := tBase) (k := t1) hcomm01 hcomm12 hcomm02
  have hsq2 : tripleFixedPoint γ (f γ) (f (f γ)) μ0 b tBase t2 *
      tripleFixedPoint γ (f γ) (f (f γ)) μ0 b tBase t2 = 1 :=
    tripleFixedPoint_sq (γ := γ) (γ₁ := f γ) (γ₂ := f (f γ))
      (μ0 := μ0) (b := b) (tBase := tBase) (k := t2) hcomm01 hcomm12 hcomm02
  have hmem0 : tripleFixedPoint γ (f γ) (f (f γ)) μ0 b tBase t0 ∈ rootSpan τ L Ψ :=
    tripleFixedPoint_mem hγ hfγmem hf2γmem
  have hmem1 : tripleFixedPoint γ (f γ) (f (f γ)) μ0 b tBase t1 ∈ rootSpan τ L Ψ :=
    tripleFixedPoint_mem hγ hfγmem hf2γmem
  have hmem2 : tripleFixedPoint γ (f γ) (f (f γ)) μ0 b tBase t2 ∈ rootSpan τ L Ψ :=
    tripleFixedPoint_mem hγ hfγmem hf2γmem
  have hZ0 : Commute z (z₀ * tripleFixedPoint γ (f γ) (f (f γ)) μ0 b tBase t0 *
      z₀⁻¹) := hfixc _ hmem0 hfix0 hsq0
  have hZ1 : Commute z (z₀ * tripleFixedPoint γ (f γ) (f (f γ)) μ0 b tBase t1 *
      z₀⁻¹) := hfixc _ hmem1 hfix1 hsq1
  have hZ2 : Commute z (z₀ * tripleFixedPoint γ (f γ) (f (f γ)) μ0 b tBase t2 *
      z₀⁻¹) := hfixc _ hmem2 hfix2 hsq2
  have hS0 : Commute z (z₀ * tripleScaledPoint γ (f γ) (f (f γ)) μ0 b tBase t0 c0 *
      z₀⁻¹) :=
    tripleScaledPoint_commute (δ := δ) (γ := γ) (γ₁ := f γ) (γ₂ := f (f γ))
      (μ0 := μ0) (b := b) (tBase := tBase) (k := t0) (c0 := c0)
      hδr hγr hfγr hf2γr hδγ hδγ₁ hδγ₂ hδn hδc hZ0
  have hS1 : Commute z (z₀ * tripleScaledPoint γ (f γ) (f (f γ)) μ0 b tBase t1 c1 *
      z₀⁻¹) :=
    tripleScaledPoint_commute (δ := δ) (γ := γ) (γ₁ := f γ) (γ₂ := f (f γ))
      (μ0 := μ0) (b := b) (tBase := tBase) (k := t1) (c0 := c1)
      hδr hγr hfγr hf2γr hδγ hδγ₁ hδγ₂ hδn hδc hZ1
  have hS2 : Commute z (z₀ * tripleScaledPoint γ (f γ) (f (f γ)) μ0 b tBase t2 c2 *
      z₀⁻¹) :=
    tripleScaledPoint_commute (δ := δ) (γ := γ) (γ₁ := f γ) (γ₂ := f (f γ))
      (μ0 := μ0) (b := b) (tBase := tBase) (k := t2) (c0 := c2)
      hδr hγr hfγr hf2γr hδγ hδγ₁ hδγ₂ hδn hδc hZ2
  let S0 : ModGL τ L := tripleScaledPoint γ (f γ) (f (f γ)) μ0 b tBase t0 c0
  let S1 : ModGL τ L := tripleScaledPoint γ (f γ) (f (f γ)) μ0 b tBase t1 c1
  let S2 : ModGL τ L := tripleScaledPoint γ (f γ) (f (f γ)) μ0 b tBase t2 c2
  have hfinal : S0 * S1 * S2 = pinnedX τ L γ u := by
    dsimp only [S0, S1, S2]
    unfold tripleScaledPoint
    set a0 : L := c0 * (tBase * t0) with ha0
    set a1 : L := c1 * (tBase * t1) with ha1
    set a2 : L := c2 * (tBase * t2) with ha2
    set b0 : L := c0 * (μ0 * (tBase * t0) ^ 2) with hb0e
    set b1 : L := c1 * (μ0 * (tBase * t1) ^ 2) with hb1e
    set b2 : L := c2 * (μ0 * (tBase * t2) ^ 2) with hb2e
    set cc0 : L := c0 * (b * (tBase * t0) ^ 4) with hc0e
    set cc1 : L := c1 * (b * (tBase * t1) ^ 4) with hc1e
    set cc2 : L := c2 * (b * (tBase * t2) ^ 4) with hc2e
    have hpair01 :
        (pinnedX τ L γ a0 * pinnedX τ L (f γ) b0 * pinnedX τ L (f (f γ)) cc0) *
          (pinnedX τ L γ a1 * pinnedX τ L (f γ) b1 * pinnedX τ L (f (f γ)) cc1) =
        (pinnedX τ L γ a0 * pinnedX τ L γ a1) *
          (pinnedX τ L (f γ) b0 * pinnedX τ L (f γ) b1) *
            (pinnedX τ L (f (f γ)) cc0 * pinnedX τ L (f (f γ)) cc1) :=
      pair_triple_product _ _ _ _ _ _
        (hcomm02 a1 cc0).symm (hcomm01 a1 b0).symm (hcomm12 b1 cc0).symm
    have hpair12 :
        ((pinnedX τ L γ a0 * pinnedX τ L γ a1) *
            (pinnedX τ L (f γ) b0 * pinnedX τ L (f γ) b1) *
              (pinnedX τ L (f (f γ)) cc0 * pinnedX τ L (f (f γ)) cc1)) *
          (pinnedX τ L γ a2 * pinnedX τ L (f γ) b2 * pinnedX τ L (f (f γ)) cc2) =
        ((pinnedX τ L γ a0 * pinnedX τ L γ a1) * pinnedX τ L γ a2) *
          ((pinnedX τ L (f γ) b0 * pinnedX τ L (f γ) b1) * pinnedX τ L (f γ) b2) *
            ((pinnedX τ L (f (f γ)) cc0 * pinnedX τ L (f (f γ)) cc1) *
              pinnedX τ L (f (f γ)) cc2) :=
      pair_triple_product _ _ _ _ _ _
        (Commute.mul_left (hcomm02 a2 cc0).symm (hcomm02 a2 cc1).symm)
        (Commute.mul_left (hcomm01 a2 b0).symm (hcomm01 a2 b1).symm)
        (Commute.mul_left (hcomm12 b2 cc0).symm (hcomm12 b2 cc1).symm)
    have hAprod : pinnedX τ L γ a0 * pinnedX τ L γ a1 * pinnedX τ L γ a2 =
        pinnedX τ L γ (a0 + a1 + a2) := by
      rw [← pinnedX_add, ← pinnedX_add]
    have hBprod : pinnedX τ L (f γ) b0 * pinnedX τ L (f γ) b1 *
        pinnedX τ L (f γ) b2 = pinnedX τ L (f γ) (b0 + b1 + b2) := by
      rw [← pinnedX_add, ← pinnedX_add]
    have hCprod : pinnedX τ L (f (f γ)) cc0 * pinnedX τ L (f (f γ)) cc1 *
        pinnedX τ L (f (f γ)) cc2 = pinnedX τ L (f (f γ)) (cc0 + cc1 + cc2) := by
      rw [← pinnedX_add, ← pinnedX_add]
    have hsumA' : a0 + a1 + a2 = u := by
      rw [ha0, ha1, ha2]
      exact hsumA
    have hsumB' : b0 + b1 + b2 = 0 := by
      rw [hb0e, hb1e, hb2e]
      exact hsumB
    have hsumC' : cc0 + cc1 + cc2 = 0 := by
      rw [hc0e, hc1e, hc2e]
      exact hsumC
    rw [hpair01, hpair12, hAprod, hBprod, hCprod, hsumA', hsumB', hsumC']
    simp [pinnedX_zero]
  have hS0' : Commute z (z₀ * S0 * z₀⁻¹) := by
    dsimp only [S0]
    exact hS0
  have hS1' : Commute z (z₀ * S1 * z₀⁻¹) := by
    dsimp only [S1]
    exact hS1
  have hS2' : Commute z (z₀ * S2 * z₀⁻¹) := by
    dsimp only [S2]
    exact hS2
  have hSprod : Commute z (z₀ * (S0 * S1 * S2) * z₀⁻¹) := by
    have h' := (hS0'.mul_right hS1').mul_right hS2'
    have e : (z₀ * S0 * z₀⁻¹) * (z₀ * S1 * z₀⁻¹) * (z₀ * S2 * z₀⁻¹) =
        z₀ * (S0 * S1 * S2) * z₀⁻¹ := by group
    rwa [e] at h'
  rwa [hfinal] at hSprod

end CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterQ2Three
