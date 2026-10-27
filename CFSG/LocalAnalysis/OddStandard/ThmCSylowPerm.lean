module

public import CFSG.LocalAnalysis.OddStandard.ThmCTFacts
public import CFSG.LocalAnalysis.OddStandard.ThmCTSub

public section

namespace CFSG.OddStandard.ThmC.T

open CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23

theorem eight_le_orbit_of_central_moves {Ω : Type*} [MulAction Tc Ω] (ω : Ω) {z : Tc}
    (hz : z ∈ Subgroup.center Tc) (hzω : z • ω ≠ ω) :
    8 ≤ (MulAction.orbit Tc ω).ncard := by
  have hHz : ¬ Subgroup.center Tc ≤ MulAction.stabilizer Tc ω := fun h => hzω (by
    have := h hz
    rwa [MulAction.mem_stabilizer_iff] at this)
  obtain ⟨hP1, hP2⟩ := card_le_of_not_center_le hHz
  have hH8 : Nat.card (MulAction.stabilizer Tc ω) ≤ 8 := by omega
  have hidx : (MulAction.stabilizer Tc ω).index * Nat.card (MulAction.stabilizer Tc ω) = 64 := by
    rw [Subgroup.index_mul_card, card_Tc]
  rw [← MulAction.index_stabilizer Tc ω]
  by_contra hlt
  push Not at hlt
  have hpos : 0 < Nat.card (MulAction.stabilizer Tc ω) := Nat.card_pos
  nlinarith

theorem no_faithful_perm_le_fifteen {Ω : Type*} [Finite Ω] (hΩ : Nat.card Ω ≤ 15)
    (f : Tc →* Equiv.Perm Ω) : ¬ Function.Injective f := by
  intro hinj
  classical
  let _ : MulAction Tc Ω := MulAction.compHom Ω f
  have hsmul : ∀ (g : Tc) (ω : Ω), g • ω = f g ω := fun _ _ => rfl
  have hz1 : (⟨0, 0, 1⟩ : Tc) ≠ 1 := by decide
  have hzZ : (⟨0, 0, 1⟩ : Tc) ∈ Subgroup.center Tc := (mem_center_iff _).2 ⟨rfl, rfl⟩
  have hfz : f ⟨0, 0, 1⟩ ≠ 1 := fun h => hz1 (hinj (by rw [h, map_one]))
  obtain ⟨ω0, hω0⟩ : ∃ ω, f ⟨0, 0, 1⟩ ω ≠ ω := by
    by_contra h
    push Not at h
    exact hfz (Equiv.ext h)
  have hmove : (⟨0, 0, 1⟩ : Tc) • ω0 ≠ ω0 := by rwa [hsmul]
  have hO8 := eight_le_orbit_of_central_moves ω0 hzZ hmove
  have hHz : ¬ Subgroup.center Tc ≤ MulAction.stabilizer Tc ω0 := fun h => hω0 (by
    have := h hzZ
    rw [MulAction.mem_stabilizer_iff, hsmul] at this
    exact this)
  obtain ⟨hP1, hP2⟩ := card_le_of_not_center_le hHz
  have hidx : (MulAction.stabilizer Tc ω0).index * Nat.card (MulAction.stabilizer Tc ω0) = 64 := by
    rw [Subgroup.index_mul_card, card_Tc]
  have horb : (MulAction.stabilizer Tc ω0).index = (MulAction.orbit Tc ω0).ncard :=
    MulAction.index_stabilizer Tc ω0
  have hO15 : (MulAction.orbit Tc ω0).ncard ≤ 15 := (Set.ncard_le_card _).trans hΩ
  have hH8 : Nat.card (MulAction.stabilizer Tc ω0) ≤ 8 := by omega
  have hH8' : Nat.card (MulAction.stabilizer Tc ω0) = 8 := by
    have hidx' : (MulAction.stabilizer Tc ω0).index ≤ 15 := by rw [horb]; exact hO15
    generalize Nat.card (MulAction.stabilizer Tc ω0) = h at hH8 hidx
    generalize (MulAction.stabilizer Tc ω0).index = i at hidx hidx'
    interval_cases h <;> omega
  have h4 : 4 < Nat.card (MulAction.stabilizer Tc ω0) := by rw [hH8']; norm_num
  have hinfne := inf_center_ne_bot_of_card h4
  obtain ⟨z', hz'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hinfne
  obtain ⟨hz'H, hz'Z⟩ := Subgroup.mem_inf.1 z'.2
  have hz'1 : (z' : Tc) ≠ 1 := fun h => hz' (Subtype.ext h)
  generalize (z' : Tc) = z at hz'H hz'Z hz'1
  have h1 : z • ω0 = ω0 := hz'H
  have hcentral : ∀ (g : Tc) (ω : Ω), z • (g • ω) = g • (z • ω) := by
    intro g ω
    calc z • (g • ω) = (z * g) • ω := (mul_smul _ _ _).symm
      _ = (g * z) • ω := by rw [Subgroup.mem_center_iff.1 hz'Z g]
      _ = g • (z • ω) := mul_smul _ _ _
  have hfix : ∀ ω : Ω, z • ω = ω := by
    intro ω
    by_contra hmv
    have hO' := eight_le_orbit_of_central_moves ω hz'Z hmv
    have hωO : ω ∉ MulAction.orbit Tc ω0 := by
      rintro ⟨g, rfl⟩
      apply hmv
      rw [hcentral, h1]
    have hdisj : Disjoint (MulAction.orbit Tc ω0) (MulAction.orbit Tc ω) := by
      rw [Set.disjoint_left]
      intro x hx0 hx
      apply hωO
      have e1 : MulAction.orbit Tc x = MulAction.orbit Tc ω0 := MulAction.orbit_eq_iff.2 hx0
      have e2 : MulAction.orbit Tc x = MulAction.orbit Tc ω := MulAction.orbit_eq_iff.2 hx
      rw [← e1, e2]
      exact MulAction.mem_orbit_self ω
    have hun := Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)
    have hle := Set.ncard_le_card (MulAction.orbit Tc ω0 ∪ MulAction.orbit Tc ω)
    omega
  have : f z = 1 := Equiv.ext fun ω => hfix ω
  exact hz'1 (hinj (by rw [this, map_one]))

theorem IsT.no_faithful_perm_le_fifteen {P : Type*} [Group P] (hT : IsT P) {Ω : Type*} [Finite Ω]
    (hΩ : Nat.card Ω ≤ 15) (f : P →* Equiv.Perm Ω) : ¬ Function.Injective f := by
  obtain ⟨e⟩ := hT.nonempty_equiv
  intro hinj
  exact CFSG.OddStandard.ThmC.T.no_faithful_perm_le_fifteen hΩ (f.comp e.symm.toMonoidHom)
    (hinj.comp e.symm.injective)

end CFSG.OddStandard.ThmC.T
