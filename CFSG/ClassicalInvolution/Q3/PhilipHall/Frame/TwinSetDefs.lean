module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSetBase

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

section Defs

variable {Y : Type} [Group Y]

@[expose] def LongFundSetE3 (R : Subgroup Y) (t : Y) : Prop :=
  ∃ Λ : Subgroup Y → Subgroup Y,
    (∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      J ≤ Λ J ∧ IsClassicalMember3 (Λ J) t) ∧
    (∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      ∀ J' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R), J ≠ J' →
        ∀ x ∈ Λ J, ∀ y ∈ Λ J', x * y = y * x) ∧
    (∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      ∀ c ∈ Subgroup.centralizer ({t} : Set Y), conjSub c (Λ J) = Λ (conjSub c J))

theorem LongFundSetE3.hasLift {R : Subgroup Y} {t : Y} (h : LongFundSetE3 R t)
    (htw : ∃ K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      K' ≠ tightCore R) :
    TightHasLift R t := by
  obtain ⟨Λ, hΛ, -, -⟩ := h
  exact ⟨Λ (tightCore R), hΛ _ (tightCore_mem_twinSet_of_twin htw)⟩

theorem conj_mem_twinSet {R : Subgroup Y} {t : Y} (htU : IsUniqueInvolution (tightCore R) t)
    {J : Subgroup Y} (hJ : J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    {c : Y} (hc : c ∈ Subgroup.centralizer ({t} : Set Y)) :
    conjSub c J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) := by
  obtain ⟨hJΩ, z, hz₀, hz'⟩ := hJ
  have hzt : t = z := htU.eq hz₀
  subst hzt
  have hct : c * t * c⁻¹ = t := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hc
    rw [this]
    group
  refine ⟨?_, t, htU, ?_⟩
  · obtain ⟨g, rfl⟩ := hJΩ
    exact ⟨c * g, conjSub_mul c g _⟩
  · have := hz'.conj c
    rwa [hct] at this

theorem mem_normalizer_of_conjSub_le {C H : Subgroup Y} (hC : ∀ c ∈ C, c⁻¹ ∈ C)
    (h : ∀ c ∈ C, conjSub c H ≤ H) : ∀ c ∈ C, c ∈ Subgroup.normalizer (H : Set Y) := by
  intro c hc
  rw [mem_normalizer_iff_conjSub_eq]
  refine le_antisymm (h c hc) ?_
  have h2 := conjSub_mono (n := c) (h c⁻¹ (hC c hc))
  rwa [conjSub_conjSub_inv] at h2

theorem LongFundSetE3.toSet {R : Subgroup Y} {t : Y} (htU : IsUniqueInvolution (tightCore R) t)
    (h : LongFundSetE3 R t) : LongFundSet3 R t := by
  obtain ⟨Λ, hΛ, hcomm, heqv⟩ := h
  refine ⟨Λ, hΛ, hcomm, ?_⟩
  set V := twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) with hV
  set C : Subgroup Y := Subgroup.centralizer ({t} : Set Y) with hC
  have hle : (⨆ J ∈ V, Λ J) ≤ C := iSup₂_le fun J hJ => isSubnormal_le (hΛ J hJ).2.subnormal
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
  refine mem_normalizer_of_conjSub_le (fun c hc => C.inv_mem hc) ?_
  intro c hc
  unfold conjSub
  rw [Subgroup.map_iSup]
  refine iSup_le fun J => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hJ => ?_
  have := heqv J hJ c hc
  unfold conjSub at this
  rw [this]
  exact le_iSup₂_of_le (conjSub c J) (conj_mem_twinSet htU hJ hc) le_rfl

end Defs

@[expose] def Thm1RTwinLiftSetEBelow (n : ℕ) : Prop :=
  Thm1RTwinLiftGenBelow (fun _ _ R t => LongFundSetE3 R t) n

theorem thm1RTwinLiftSetEBelow_zero : Thm1RTwinLiftSetEBelow 0 :=
  fun _ _ _ hlt => absurd hlt (Nat.not_lt_zero _)

theorem Thm1RTwinLiftSetEBelow.mono {m n : ℕ} (h : m ≤ n) (H : Thm1RTwinLiftSetEBelow n) :
    Thm1RTwinLiftSetEBelow m :=
  Thm1RTwinLiftGenBelow.mono h H

theorem Thm1RTwinLiftSetEBelow.hasLift {n : ℕ} (H : Thm1RTwinLiftSetEBelow n) {Y : Type}
    [Group Y] [Finite Y] (hY : Nat.card Y < n) {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
    (hd : QuaternionBridge.Q8TwinDatum R S t)
    (hq : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2)) (hg : TightSelfGen R)
    (hO : TightOddFree Y) (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)))
    (hA : AEmpty (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (htw : ∃ K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      K' ≠ tightCore R) :
    TightInO2 t ∨ TwinE4 Y ∨ TightHasLift R t := by
  rcases H Y hY R S t hd hq hg hO hΩ hA htw with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (h.hasLift htw))

theorem Thm1RTwinLiftSetEBelow.toHasLift {n : ℕ} (H : Thm1RTwinLiftSetEBelow n) :
    Thm1RTwinHasLiftBelow n :=
  fun _ _ _ hlt _ _ _ hd hq hg hO hΩ hA htw => H.hasLift hlt hd hq hg hO hΩ hA htw

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
