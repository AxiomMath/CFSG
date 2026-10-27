module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Basic
public import CFSG.LieType.Simplicity.TitsModel

public section

namespace CFSG.QuasithinUnique.Setup.X6

open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ABGLocalTools
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

@[expose] def TitsSylowOvergroupLattice : Prop :=
  ∀ (X : Type) [Group X] [Finite X], ReeTitsModel X .Tits 2 1 →
    ∀ U : Subgroup X, CFSG.QuasithinUnique.IsSylowTwoOf U ⊤ →
      ∃ H N : Subgroup X, Nat.card U = 2048 ∧ U ≤ H ∧ U ≤ N ∧ Nat.card H = 10240 ∧
        Nat.card N = 6144 ∧ (∀ M : Subgroup X, U ≤ M → M = U ∨ M = H ∨ M = N ∨ M = ⊤) ∧
        Group.IsSolvable H ∧ Group.IsSolvable N

section Lattice

variable {X : Type} [Group X] {U H N : Subgroup X}

theorem ne_top_of_card (hH : Nat.card H = 10240) (hN : Nat.card N = 6144) : H ≠ ⊤ ∧ N ≠ ⊤ := by
  constructor
  · intro h
    have := Subgroup.card_dvd_of_le (le_top.trans_eq h.symm : N ≤ H)
    rw [hH, hN] at this
    omega
  · intro h
    have := Subgroup.card_dvd_of_le (le_top.trans_eq h.symm : H ≤ N)
    rw [hH, hN] at this
    omega

theorem invariant_of_overgroup_lattice (hU : Nat.card U = 2048) (hH : Nat.card H = 10240)
    (hN : Nat.card N = 6144) (hUH : U ≤ H) (hUN : U ≤ N)
    (hlat : ∀ M : Subgroup X, U ≤ M → M = U ∨ M = H ∨ M = N ∨ M = ⊤) {α : MulAut X}
    (hα : U.map α.toMonoidHom = U) :
    H.map α.toMonoidHom = H ∧ N.map α.toMonoidHom = N := by
  obtain ⟨hHt, hNt⟩ := ne_top_of_card hH hN
  have hcH : Nat.card (H.map α.toMonoidHom) = 10240 := by
    rw [Subgroup.card_map_of_injective α.injective, hH]
  have hcN : Nat.card (N.map α.toMonoidHom) = 6144 := by
    rw [Subgroup.card_map_of_injective α.injective, hN]
  have htop : ∀ P : Subgroup X, P.map α.toMonoidHom = ⊤ → P = ⊤ := by
    intro P hP
    apply Subgroup.map_injective (f := α.toMonoidHom) α.injective
    rw [hP, Subgroup.map_top_of_surjective _ α.surjective]
  have hUle : ∀ P : Subgroup X, U ≤ P → U ≤ P.map α.toMonoidHom := fun P hP => by
    rw [← hα]
    exact Subgroup.map_mono hP
  refine ⟨?_, ?_⟩
  · rcases hlat _ (hUle H hUH) with h | h | h | h
    · rw [h, hU] at hcH; omega
    · exact h
    · rw [h, hN] at hcH; omega
    · exact absurd (htop _ h) hHt
  · rcases hlat _ (hUle N hUN) with h | h | h | h
    · rw [h, hU] at hcN; omega
    · rw [h, hH] at hcN; omega
    · exact h
    · exact absurd (htop _ h) hNt

theorem generation_of_overgroup_lattice (hH : Nat.card H = 10240) (hN : Nat.card N = 6144)
    (hUH : U ≤ H) (hU : Nat.card U = 2048)
    (hlat : ∀ M : Subgroup X, U ≤ M → M = U ∨ M = H ∨ M = N ∨ M = ⊤) : H ⊔ N = ⊤ := by
  have hle : U ≤ H ⊔ N := hUH.trans le_sup_left
  rcases hlat _ hle with h | h | h | h
  · have := Subgroup.card_dvd_of_le (le_sup_left.trans_eq h : H ≤ U)
    rw [hH, hU] at this
    omega
  · have := Subgroup.card_dvd_of_le (le_sup_right.trans_eq h : N ≤ H)
    rw [hN, hH] at this
    omega
  · have := Subgroup.card_dvd_of_le (le_sup_left.trans_eq h : H ≤ N)
    rw [hH, hN] at this
    omega
  · exact h

end Lattice

section Model

theorem tits_model_two_extensions
    (hT : TitsSylowOvergroupLattice) {X : Type} [Group X] [Finite X]
    (hX : ReeTitsModel X .Tits 2 1) :
    IsSimpleGroup X ∧ Subgroup.center X = ⊥ ∧ ¬ IsMulCommutative X ∧
    TwoGeneratingSylowOvergroups X ∧
    (∀ D : Subgroup (MulAut X), inner X ≤ D → ∀ R : Subgroup (MulAut X),
      CFSG.QuasithinUnique.IsSylowTwoOf R D →
        ∃ M₁ M₂ : Subgroup (MulAut X), M₁ ≠ M₂ ∧ M₁ ⋖ D ∧ M₂ ⋖ D ∧ R ≤ M₁ ∧ R ≤ M₂) ∧
    ∀ U : Subgroup X, CFSG.QuasithinUnique.IsSylowTwoOf U ⊤ →
      ∃ H N : Subgroup X, Nat.card H = 10240 ∧ Nat.card N = 6144 ∧ U < H ∧ U < N ∧
        (∀ M : Subgroup X, U < M → M < ⊤ → M = H ∨ M = N) ∧ H ⊔ N = ⊤ ∧
        ∀ α : MulAut X, U.map α.toMonoidHom = U →
          H.map α.toMonoidHom = H ∧ N.map α.toMonoidHom = N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hnt, hsimple⟩ := CFSG.LieType.Simplicity.fam_tits_simplicity X 2 1 hX
  have : IsSimpleGroup X := hsimple
  have hdata : ∀ U : Subgroup X, CFSG.QuasithinUnique.IsSylowTwoOf U ⊤ →
      ∃ H N : Subgroup X, Nat.card H = 10240 ∧ Nat.card N = 6144 ∧ U < H ∧ U < N ∧
        (∀ M : Subgroup X, U < M → M < ⊤ → M = H ∨ M = N) ∧ H ⊔ N = ⊤ ∧
        ∀ α : MulAut X, U.map α.toMonoidHom = U →
          H.map α.toMonoidHom = H ∧ N.map α.toMonoidHom = N := by
    intro U hU
    obtain ⟨H, N, hu, hUH, hUN, hH, hN, hlat, -, -⟩ := hT X hX U hU
    refine ⟨H, N, hH, hN, lt_of_le_of_ne hUH fun h => ?_, lt_of_le_of_ne hUN fun h => ?_, ?_,
      generation_of_overgroup_lattice hH hN hUH hu hlat,
      fun α hα => invariant_of_overgroup_lattice hu hH hN hUH hUN hlat hα⟩
    · rw [← h, hu] at hH; omega
    · rw [← h, hu] at hN; omega
    · intro M hUM hMt
      rcases hlat M hUM.le with h | h | h | h
      · exact absurd h hUM.ne'
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h hMt.ne
  obtain ⟨U₀, hU₀'⟩ := exists_isSylowOf (G := X) 2 ⊤
  have hU₀ : CFSG.QuasithinUnique.IsSylowTwoOf U₀ ⊤ := isSylowTwoOf_iff_isSylowOf.2 hU₀'
  obtain ⟨H, N, hu, hUH, hUN, hH, hN, hlat, -, -⟩ := hT X hX U₀ hU₀
  obtain ⟨hHt, hNt⟩ := ne_top_of_card hH hN
  have hnn : ∀ P : Subgroup X, Nat.card P ≠ 1 → P ≠ ⊤ → ¬ P.Normal := by
    intro P h1 ht hn
    rcases Subgroup.Normal.eq_bot_or_eq_top P with h | h
    · apply h1
      rw [h]
      exact Subgroup.card_bot
    · exact ht h
  have hHn : ¬ H.Normal := hnn H (by omega) hHt
  have hNn : ¬ N.Normal := hnn N (by omega) hNt
  have hZ : Subgroup.center X = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center X) with h | h
    · exact h
    · exfalso
      have hc : ∀ a b : X, a * b = b * a := fun a b =>
        Subgroup.mem_center_iff.1 (by rw [h]; exact Subgroup.mem_top b) a
      have : IsMulCommutative X := isMulCommutative_iff.2 hc
      exact hHn inferInstance
  have hgenTop := generation_of_overgroup_lattice hH hN hUH hu hlat
  have hgen : TwoGeneratingSylowOvergroups X := by
    intro D hD R hR
    exact automorphism_invariant_generating_Sylow_overgroups_lift hZ hU₀' hHn hNn hgenTop
      (fun α hα => invariant_of_overgroup_lattice hu hH hN hUH hUN hlat hα) hD
      (isSylowTwoOf_iff_isSylowOf.1 hR)
  refine ⟨hsimple, hZ, fun hc => ?_, hgen, fun D hD R hR => (hgen D hD R hR).exists_two_maximal,
    hdata⟩
  obtain ⟨x, hx⟩ := exists_ne (1 : X)
  have hxc : x ∈ Subgroup.center X :=
    Subgroup.mem_center_iff.2 fun g => isMulCommutative_iff.1 hc g x
  rw [hZ] at hxc
  exact hx (Subgroup.mem_bot.1 hxc)

end Model

end CFSG.QuasithinUnique.Setup.X6
