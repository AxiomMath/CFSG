module

public import CFSG.LocalAnalysis.ABGTheoremB.IV7Data

public noncomputable section

namespace CFSG.ABGTheoremB

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools

universe u

namespace Setting

variable {G : Type u} [Group G] [Finite G] {σ : Setting G} {r : ℕ}

structure IV9UV (d : σ.IV7Data r) where
  U : Subgroup G
  U_normal : Subgroup.normalizer (d.R : Set G) ≤ Subgroup.normalizer (U : Set G)
  U_le : U ≤ d.R
  U_centralizer : Subgroup.normalizer (d.R : Set G) ⊓ Subgroup.centralizer (U : Set G) ≤
    solvRadIn (Subgroup.normalizer (d.R : Set G))
  U_minimal : ∀ X : Subgroup G,
    Subgroup.normalizer (d.R : Set G) ≤ Subgroup.normalizer (X : Set G) → X < U →
      ¬ Subgroup.normalizer (d.R : Set G) ⊓ Subgroup.centralizer (X : Set G) ≤
        solvRadIn (Subgroup.normalizer (d.R : Set G))
  V : Subgroup G
  V_normal : Subgroup.normalizer (d.R : Set G) ≤ Subgroup.normalizer (V : Set G)
  V_lt : V < U
  V_chief : (∀ a ∈ U, ∀ b ∈ U, a * b = b * a) → ∀ X : Subgroup G,
    Subgroup.normalizer (d.R : Set G) ≤ Subgroup.normalizer (X : Set G) → V ≤ X → X ≤ U →
      X = V ∨ X = U
  V_center : ¬ (∀ a ∈ U, ∀ b ∈ U, a * b = b * a) → V = centerOf U

@[expose] def IV9UV.H₁ {d : σ.IV7Data r} (e : IV9UV d) : Subgroup G :=
  Subgroup.normalizer ((d.P ⊓ e.U : Subgroup G) : Set G)

omit [Finite G] in
private theorem iv9uv_normalizer_le_normalizer_centerOf (H : Subgroup G) :
    Subgroup.normalizer (H : Set G) ≤ Subgroup.normalizer (centerOf H : Set G) :=
  (le_inf le_rfl ((Subgroup.normal_subgroupOf_iff_le_normalizer
    (Subgroup.centralizer_le_normalizer _)).mp
      (Subgroup.normal_subgroupOf_centralizer_normalizer _))).trans
    Subgroup.inf_normalizer_le_normalizer_inf

theorem IV9UV.nonempty (d : σ.IV7Data r)
    (hR : Subgroup.normalizer (d.R : Set G) ⊓ Subgroup.centralizer (d.R : Set G) ≤
      solvRadIn (Subgroup.normalizer (d.R : Set G)))
    (hK : ¬ Subgroup.normalizer (d.R : Set G) ≤ solvRadIn (Subgroup.normalizer (d.R : Set G))) :
    Nonempty (IV9UV d) := by
  set K := Subgroup.normalizer (d.R : Set G) with hKdef
  set 𝒰 : Set (Subgroup G) := {X | K ≤ Subgroup.normalizer (X : Set G) ∧ X ≤ d.R ∧
    K ⊓ Subgroup.centralizer (X : Set G) ≤ solvRadIn K} with h𝒰
  have hR𝒰 : d.R ∈ 𝒰 := ⟨le_rfl, le_rfl, hR⟩
  obtain ⟨U, hU𝒰, hUmin⟩ := WellFounded.has_min wellFounded_lt 𝒰 ⟨_, hR𝒰⟩
  obtain ⟨hUn, hUR, hUc⟩ := hU𝒰
  have hUne : U ≠ ⊥ := by
    rintro rfl
    apply hK
    intro k hk
    refine hUc ⟨hk, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
    rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hh
    rw [hh, mul_one, one_mul]
  have hUmin' : ∀ X : Subgroup G, K ≤ Subgroup.normalizer (X : Set G) → X < U →
      ¬ K ⊓ Subgroup.centralizer (X : Set G) ≤ solvRadIn K :=
    fun X hXn hXU hXc => hUmin X ⟨hXn, hXU.le.trans hUR, hXc⟩ hXU
  by_cases hab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a
  · set 𝒱 : Set (Subgroup G) := {X | K ≤ Subgroup.normalizer (X : Set G) ∧ X < U} with h𝒱
    have hbot : (⊥ : Subgroup G) ∈ 𝒱 := by
      refine ⟨fun k _ => Subgroup.mem_normalizer_iff.mpr fun h => ?_,
        bot_lt_iff_ne_bot.mpr hUne⟩
      simp only [Subgroup.mem_bot, conj_eq_one_iff]
    obtain ⟨V, ⟨hVn, hVU⟩, hVmax⟩ := WellFounded.has_min wellFounded_gt 𝒱 ⟨_, hbot⟩
    refine ⟨⟨U, hUn, hUR, hUc, hUmin', V, hVn, hVU, fun _ X hXn hVX hXU => ?_,
      fun h => absurd hab h⟩⟩
    rcases hXU.lt_or_eq with hXU | hXU
    · left
      by_contra hne
      exact hVmax X ⟨hXn, hXU⟩ (lt_of_le_of_ne hVX (Ne.symm hne))
    · exact Or.inr hXU
  · refine ⟨⟨U, hUn, hUR, hUc, hUmin', centerOf U,
      hUn.trans (iv9uv_normalizer_le_normalizer_centerOf U), lt_of_le_of_ne inf_le_left ?_,
      fun h => absurd h hab, fun _ => rfl⟩⟩
    intro hZU
    apply hab
    intro a ha b hb
    have hb' : b ∈ centerOf U := by rw [hZU]; exact hb
    exact Subgroup.mem_centralizer_iff.mp hb'.2 a ha

end Setting

end CFSG.ABGTheoremB
