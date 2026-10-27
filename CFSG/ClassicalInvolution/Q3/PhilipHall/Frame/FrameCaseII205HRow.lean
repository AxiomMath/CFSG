module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf43L3E8Shape
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFBase
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4 CFSG.Open

section Generic

theorem exists_noncomm_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : ∃ a b : Y, a * b ≠ b * a) : ∃ a b : X, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := h
  refine ⟨e.symm a, e.symm b, fun heq => hab ?_⟩
  have := congrArg e heq
  simpa using this

theorem isSolvable_of_card_two_pow {X : Type} [Group X] [Finite X] {n : ℕ}
    (h : Nat.card X = 2 ^ n) : Group.IsSolvable X := by
  haveI : IsPGroup 2 X := IsPGroup.of_card h
  haveI : Group.IsNilpotent X := IsPGroup.isNilpotent this
  infer_instance

theorem mem_of_q8_hom {Sg : Type} [Group Sg] [Finite Sg] (Φ : QuaternionGroup 2 →* Sg)
    {E : Subgroup Sg} [E.Normal] (e : (Sg ⧸ E) ≃* L3Two) :
    Φ (QuaternionGroup.a 2) ∈ E := by
  by_contra hnot
  have h1 : Φ (QuaternionGroup.a 1) * Φ (QuaternionGroup.a 1) = Φ (QuaternionGroup.a 2) := by
    rw [← map_mul]; exact congrArg Φ (by decide)
  have h2 : Φ (QuaternionGroup.xa 0) * Φ (QuaternionGroup.xa 0) = Φ (QuaternionGroup.a 2) := by
    rw [← map_mul]; exact congrArg Φ (by decide)
  have h3 : Φ (QuaternionGroup.xa 0) * Φ (QuaternionGroup.a 1) * (Φ (QuaternionGroup.xa 0))⁻¹ =
      (Φ (QuaternionGroup.a 1))⁻¹ := by
    have := congrArg Φ (show QuaternionGroup.xa 0 * QuaternionGroup.a 1 *
      (QuaternionGroup.xa 0)⁻¹ = (QuaternionGroup.a 1)⁻¹ by decide)
    simpa only [map_mul, map_inv] using this
  set x := Φ (QuaternionGroup.a 1) with hx
  set y := Φ (QuaternionGroup.xa 0) with hy
  set ex : Sg → L3Two := fun s => e (QuotientGroup.mk s) with hex
  have hmul : ∀ s t : Sg, ex (s * t) = ex s * ex t := fun s t => by
    simp [hex, QuotientGroup.mk_mul]
  have hinv : ∀ s : Sg, ex s⁻¹ = (ex s)⁻¹ := fun s => by
    simp [hex, QuotientGroup.mk_inv]
  have hone : ∀ s : Sg, ex s = 1 → s ∈ E := fun s hs => by
    have : QuotientGroup.mk s = (1 : Sg ⧸ E) := e.map_eq_one_iff.mp hs
    exact (QuotientGroup.eq_one_iff s).mp this
  have hi2 : ex x * ex x = ex (Φ (QuaternionGroup.a 2)) := by rw [← hmul, h1]
  have hj2 : ex y * ex y = ex (Φ (QuaternionGroup.a 2)) := by rw [← hmul, h2]
  have hne : ex x * ex x ≠ 1 := by
    rw [hi2]
    intro h
    exact hnot (hone _ h)
  have hconj : ex y * ex x * (ex y)⁻¹ = (ex x)⁻¹ := by
    have := congrArg ex h3
    rwa [hmul, hmul, hinv, hinv] at this
  exact l3Two_no_q8 (ex x) (ex y) (hi2.trans hj2.symm) hne hconj

theorem m12_nonabelian :
    ∃ a b : CFSG.Blueprint.NativeSporadic.M12, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have hsimp : IsSimpleGroup CFSG.Blueprint.NativeSporadic.M12 :=
    (CFSG.Sporadic.Mathieu.fam_m12_simplicity).2.2
  haveI : Finite CFSG.Blueprint.NativeSporadic.M12 := (CFSG.Sporadic.Mathieu.fam_m12_simplicity).1
  letI : CommGroup CFSG.Blueprint.NativeSporadic.M12 :=
    { (inferInstance : Group CFSG.Blueprint.NativeSporadic.M12) with
      mul_comm := fun a b => hcon a b }
  have hp := IsSimpleGroup.prime_card (α := CFSG.Blueprint.NativeSporadic.M12)
  rw [CFSG.Sporadic.Mathieu.card_M12] at hp
  norm_num at hp

end Generic

section Transfer

theorem transfer_uniq_odd {X : Type} [Group X] [Finite X] {T : Subgroup X}
    (Pc : Subgroup X → Prop) (hT : ∀ L : Subgroup X, CFSG.IsComponent L → Pc L → L ≤ T)
    (hU' : ∀ L₁' L₂' : Subgroup ↥T, CFSG.IsComponent L₁' → CFSG.IsComponent L₂' → L₁' = L₂')
    (hO' : ∀ L' : Subgroup ↥T, CFSG.IsComponent L' → Q3NM.AutOddFree ↥L') :
    (∀ L₁ L₂ : Subgroup X, CFSG.IsComponent L₁ → CFSG.IsComponent L₂ → Pc L₁ → Pc L₂ →
      L₁ = L₂) ∧
      ∀ L : Subgroup X, CFSG.IsComponent L → Pc L → Q3NM.AutOddFree ↥L := by
  refine ⟨fun L₁ L₂ h₁ h₂ m₁ m₂ => ?_, fun L hL hm => ?_⟩
  · have e := hU' (L₁.subgroupOf T) (L₂.subgroupOf T)
      (CFSG.LocalCores.component_overgroup h₁ (hT L₁ h₁ m₁))
      (CFSG.LocalCores.component_overgroup h₂ (hT L₂ h₂ m₂))
    rw [← Subgroup.map_subgroupOf_eq_of_le (hT L₁ h₁ m₁),
      ← Subgroup.map_subgroupOf_eq_of_le (hT L₂ h₂ m₂), e]
  · have hLT := hT L hL hm
    exact Q3NM.AutOddFree.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLT)
      (hO' _ (CFSG.LocalCores.component_overgroup hL hLT))

end Transfer

section Section

theorem isPGroup_of_mem_WSet {Q : Type} [Group Q] [Finite Q] {Ω : Set (Subgroup Q)}
    {W : Subgroup Q} (hW : W ∈ CFSG.ClassicalInvolution.Asc77.WSet Ω) : IsPGroup 2 W := by
  obtain ⟨η, hη, rfl⟩ := hW
  obtain ⟨S', hηS, -⟩ := hη
  have hle : (⨆ U ∈ η, U) ≤ (S' : Subgroup Q) := iSup₂_le fun U hU => (hηS.1 hU).2
  have hcard : Nat.card ↥(⨆ U ∈ η, U) ∣ Nat.card ↥(S' : Subgroup Q) :=
    Subgroup.card_dvd_of_le hle
  rw [Sylow.card_eq_multiplicity] at hcard
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hcard
  exact IsPGroup.of_card hj

end Section

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
