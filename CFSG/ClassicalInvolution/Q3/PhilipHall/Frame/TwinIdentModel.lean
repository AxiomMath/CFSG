module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinIdentKind
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.LiftTransfer
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Transport217
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520GlueLie
public import CFSG.ClassicalInvolution.Q3.Induction
public import CFSG.ClassicalInvolution.Asc77.AscT8V1
public import CFSG.ClassicalInvolution.Asc77.AscT8V2
public import CFSG.ClassicalInvolution.Asc77.AscT8V3
public import CFSG.ClassicalInvolution.Asc77.WP2Branch
public import CFSG.ClassicalInvolution.AschTight.S1916F2a
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FStarBasic
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmA
public import CFSG.ClassicalInvolution.Q3.Q3CLNine3
public import CFSG.ClassicalInvolution.Q3.Q3DBFuzzyEdge
public import CFSG.ClassicalInvolution.Q3.Q3KCGen
public import CFSG.ClassicalInvolution.Q3.Q3NFLink
public import CFSG.ClassicalInvolution.Q3.Q3T6BSymEx
public import CFSG.ClassicalInvolution.Q3.Q3TIMain
public import CFSG.ClassicalInvolution.Q3.Q3TIYOAMain
public import CFSG.ClassicalInvolution.Q3.Q3TKMem
public import CFSG.ClassicalInvolution.Q3.Q3WAEDict
public import CFSG.ClassicalInvolution.Q3.TL4SepSub
public import CFSG.ClassicalInvolution.SmallCases.NobqFinal
public import CFSG.ClassicalInvolution.Uniform.U3IH8
public import CFSG.Sporadic.J4.QT2LocProof
public import CFSG.Sporadic.J4.QTOutChar

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG.Open hiding StatedLieTag
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3T7
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinIdent
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520Aux
  CFSG.ClassicalInvolution.Disconnected.AschTight

section Tags

theorem model1520Covered_or_exceptional {d : ℕ} {ε : Bool}
    {tag : CFSG.Assembly.LowTwoRank.StatedLieTag} {k : ℕ} (h : IsOrthTag d ε tag k) :
    Model1520Covered tag k ∨ (tag = .PSU ∧ k = 4) ∨ (tag = .POmegaPlus ∧ k = 4) := by
  rcases h with ⟨-, rfl, hk⟩ | ⟨-, -, rfl, hk⟩ | ⟨-, -, rfl, hk⟩ | ⟨h7, -, rfl, hk⟩ |
    ⟨h8, -, -, rfl, hk⟩ | ⟨h8, -, -, rfl, hk⟩
  · exact Or.inl hk
  · exact Or.inl hk
  · exact Or.inr (Or.inl ⟨rfl, hk⟩)
  · exact Or.inl (by simp only [Model1520Covered]; omega)
  · by_cases h5 : 5 ≤ k
    · exact Or.inl h5
    · exact Or.inr (Or.inr ⟨rfl, by omega⟩)
  · exact Or.inl (by simp only [Model1520Covered]; omega)

end Tags

section TwinIdent

@[expose] def Model1520LieTarget (tag : CFSG.Assembly.LowTwoRank.StatedLieTag) (k : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X : Subgroup G) (ι : Type) (Φ : Set (Subgroup ↥X))
    (D : LieSystemData3 ι ↥X Φ) (i : ι), (∀ j, j = i) → D.kind i = CompData.model tag k →
      ∀ (L : Subgroup ↥X), L ∈ Φ → ∀ t : ↥X, IsClassicalMember3 L t → Model1520 X (t : G)

theorem oddCore_eq_bot_of_card_eq {Y : Type} [Group Y] [Finite Y] {M : Subgroup Y} {z : Y}
    (h : IsClassicalMember3 M z) (hc : Nat.card M = 24) : classicalInvolutionOddCore ↥M = ⊥ := by
  have h1 := h.card_eq
  rw [hc] at h1
  exact Subgroup.eq_bot_of_card_eq _ (by omega)

theorem eq_of_le_liftFam_of_card_eq {Y : Type} [Group Y] [Finite Y] {Δ : Set (Subgroup Y)}
    (hΩ : HypOmegaGen Δ) (h2 : ∀ K ∈ Δ, IsPGroup 2 K) {J J' M : Subgroup Y} (hJ : J ∈ Δ)
    (hJ' : J' ∈ Δ) (hM : M ∈ liftFam Δ) (hJM : J ≤ M) (hJ'M : J' ≤ M) (hc : Nat.card M = 24) :
    J = J' := by
  obtain ⟨z₀, hz₀⟩ := liftFam_mem3 hM
  have hm : IsClassicalMember3 M z₀ := hz₀.member.toQ3 (by norm_num)
  exact eq_of_isSylow2In_of_oddCore_eq_bot hm (oddCore_eq_bot_of_card_eq hm hc)
    (isSylow2In_of_le_liftFam hΩ hJ (h2 J hJ) hM hJM)
    (isSylow2In_of_le_liftFam hΩ hJ' (h2 J' hJ') hM hJ'M)

theorem isPGroup_of_mem_conjClass {Y : Type} [Group Y] {J : Subgroup Y} (h2 : IsPGroup 2 J)
    {K : Subgroup Y} (hK : K ∈ CoreAssembly.conjClass J) : IsPGroup 2 K := by
  obtain ⟨g, rfl⟩ := hK
  exact isPGroup_conjSub g h2

theorem twinIdent_lieSystem_of_twin {X : Type} [Group X] [Finite X] {n : ℕ} (hBelow : CIT3Below n)
    (hlt : Nat.card X < n) (hO : classicalInvolutionOddCore X = ⊥) {J : Subgroup X} {z : X}
    (hΩ : HypOmegaGen (CoreAssembly.conjClass J)) (h2 : IsPGroup 2 J)
    (hgen : (⨆ K ∈ CoreAssembly.conjClass J, K) = ⊤)
    (hl : HasLifts (CoreAssembly.conjClass J)) (hz : IsUniqueInvolution J z) {J' : Subgroup X}
    (hJ' : J' ∈ twinSet (CoreAssembly.conjClass J) J) (hne : J' ≠ J) :
    ∃ (ι : Type) (D : LieSystemData3 ι X (liftFam (CoreAssembly.conjClass J))) (i : ι),
      (∀ j, j = i) ∧ (∃ M ∈ liftFam (CoreAssembly.conjClass J), IsClassicalMember3 M z) ∧
      ∃ (tag : CFSG.Assembly.LowTwoRank.StatedLieTag) (k d : ℕ) (ε : Bool), 5 ≤ d ∧
        IsOrthTag d ε tag k ∧ D.kind i = CompData.model tag k := by
  set Δ : Set (Subgroup X) := CoreAssembly.conjClass J with hΔdef
  have hn : CITBelowT (.sl2 3 1) n :=
    (citBelowT_three_iff (p := 3) (f := 1) (by norm_num) n).mpr hBelow
  have hΔ : ConjInvariant Δ := hΩ.conjInvariant
  have hJΔ : J ∈ Δ := CoreAssembly.mem_conjClass_self J
  have hΛ : HypOmegaModU (.sl2 3 1) (liftFam Δ) := hypOmegaModU_liftFam hΔ
  have hgenΛ : omegaGen (liftFam Δ) = ⊤ :=
    (inClass3_liftFam hΔ ⟨J, hJΔ⟩ hl hgen).generated
  obtain ⟨L, u, hL⟩ := hl J hJΔ
  have hMΛ : satU (.sl2 3 1) L u ∈ liftFam Δ := satU_mem_liftFam hJΔ hL
  have htrans : ∀ K ∈ liftFam Δ, ∀ K' ∈ liftFam Δ, ∃ g : X, conjSub g K = K' := by
    intro K hK K' hK'
    obtain ⟨g₁, hg₁⟩ := liftFam_trans hΩ hMΛ (J₀ := J) hL.le_sat
      (fun J' hJ' => by obtain ⟨g, hg⟩ := hJ'; exact ⟨g, hg⟩) K hK
    obtain ⟨g₂, hg₂⟩ := liftFam_trans hΩ hMΛ (J₀ := J) hL.le_sat
      (fun J' hJ' => by obtain ⟨g, hg⟩ := hJ'; exact ⟨g, hg⟩) K' hK'
    refine ⟨g₂ * g₁⁻¹, ?_⟩
    rw [← hg₁, ← hg₂, ← conjSub_mul, mul_assoc, inv_mul_cancel, mul_one]
  have hne' : (liftFam Δ).Nonempty := ⟨_, hMΛ⟩
  have hcard : ∀ K ∈ liftFam Δ, Nat.card K = 24 := by
    obtain ⟨D, -⟩ := exists_omegaLieU_sect hn hlt hΛ hO hgenΛ htrans hne'
    exact D.card_eq (by norm_num)
  have huz : u = z := by
    rcases hz.unique u hL.inv.mem hL.inv.sq with h | h
    · exact absurd h hL.inv.ne_one
    · exact h
  obtain ⟨hJ'Δ, w, hw, hw'⟩ := hJ'
  have hwz : w = z := by
    rcases hz.unique w hw.mem hw.sq with h | h
    · exact absurd h hw.ne_one
    · exact h
  obtain ⟨L', u', hL'⟩ := hl J' hJ'Δ
  have hM'Λ : satU (.sl2 3 1) L' u' ∈ liftFam Δ := satU_mem_liftFam hJ'Δ hL'
  have hMz : IsUniqueInvolution (satU (.sl2 3 1) L u) z :=
    isUniqueInvolution_liftFam_of_le hMΛ hz hL.le_sat
  have hM'z : IsUniqueInvolution (satU (.sl2 3 1) L' u') z := by
    rw [← hwz]
    exact isUniqueInvolution_liftFam_of_le hM'Λ hw' hL'.le_sat
  have hMne : satU (.sl2 3 1) L' u' ≠ satU (.sl2 3 1) L u := by
    intro h
    have hJ'M : J' ≤ satU (.sl2 3 1) L u := h ▸ hL'.le_sat
    exact hne (eq_of_le_liftFam_of_card_eq hΩ (fun K hK => isPGroup_of_mem_conjClass h2 hK)
      hJ'Δ hJΔ hMΛ hJ'M hL.le_sat (hcard _ hMΛ))
  obtain ⟨ι, D, i, hone, tag, k, d, ε, hd, hdε, hk⟩ :=
    twinIdent_lieSystem hn hlt hΛ hO hgenΛ htrans
      ⟨_, hMΛ, _, ⟨hM'Λ, z, hMz, hM'z⟩, hMne⟩
  refine ⟨ι, D, i, hone, ⟨_, hMΛ, ?_⟩, tag, k, d, ε, hd, hdε, hk⟩
  rw [← huz]
  exact hL.member_sat

theorem twinIdent_model1520_or {G : Type} [Group G] [Finite G] (X : Subgroup G) {n : ℕ}
    (hBelow : CIT3Below n) (hlt : Nat.card ↥X < n) (hO : classicalInvolutionOddCore ↥X = ⊥)
    {J : Subgroup ↥X} {z : ↥X} (hΩ : HypOmegaGen (CoreAssembly.conjClass J)) (h2 : IsPGroup 2 J)
    (hgen : (⨆ K ∈ CoreAssembly.conjClass J, K) = ⊤)
    (hl : HasLifts (CoreAssembly.conjClass J)) (hz : IsUniqueInvolution J z) {J' : Subgroup ↥X}
    (hJ' : J' ∈ twinSet (CoreAssembly.conjClass J) J) (hne : J' ≠ J) :
    Model1520 X (z : G) ∨
      ∃ (ι : Type) (Φ : Set (Subgroup ↥X)) (D : LieSystemData3 ι ↥X Φ) (i : ι),
        (∀ j, j = i) ∧
        (D.kind i = CompData.model .PSU 4 ∨ D.kind i = CompData.model .POmegaPlus 4) ∧
        ∃ L ∈ Φ, IsClassicalMember3 L z := by
  obtain ⟨ι, D, i, hone, ⟨M, hM, hMz⟩, tag, k, d, ε, hd, hdε, hk⟩ :=
    twinIdent_lieSystem_of_twin hBelow hlt hO hΩ h2 hgen hl hz hJ' hne
  rcases model1520Covered_or_exceptional hdε with hcov | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl (model1520_of_lieSystem3 X D i hone tag k hcov hk hM hMz)
  · exact Or.inr ⟨ι, _, D, i, hone, Or.inl hk, M, hM, hMz⟩
  · exact Or.inr ⟨ι, _, D, i, hone, Or.inr hk, M, hM, hMz⟩

theorem twinIdent_model1520 {G : Type} [Group G] [Finite G] (X : Subgroup G) {n : ℕ}
    (hPSU : Model1520LieTarget .PSU 4) (hTri : Model1520LieTarget .POmegaPlus 4)
    (hBelow : CIT3Below n) (hlt : Nat.card ↥X < n) (hO : classicalInvolutionOddCore ↥X = ⊥)
    {J : Subgroup ↥X} {z : ↥X} (hΩ : HypOmegaGen (CoreAssembly.conjClass J)) (h2 : IsPGroup 2 J)
    (hgen : (⨆ K ∈ CoreAssembly.conjClass J, K) = ⊤)
    (hl : HasLifts (CoreAssembly.conjClass J)) (hz : IsUniqueInvolution J z) {J' : Subgroup ↥X}
    (hJ' : J' ∈ twinSet (CoreAssembly.conjClass J) J) (hne : J' ≠ J) :
    Model1520 X (z : G) := by
  rcases twinIdent_model1520_or X hBelow hlt hO hΩ h2 hgen hl hz hJ' hne with h |
    ⟨ι, Φ, D, i, hone, hk | hk, L, hL, hLz⟩
  · exact h
  · exact hPSU G X ι Φ D i hone hk L hL z hLz
  · exact hTri G X ι Φ D i hone hk L hL z hLz

end TwinIdent

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
