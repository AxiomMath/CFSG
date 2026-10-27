module

public import CFSG.LocalAnalysis.OddStandard.ThmCCoreDich
public import CFSG.LocalAnalysis.OddStandard.ThmCCoreFree
public import CFSG.LocalAnalysis.ComponentClassification.RadicalFreeLayer
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.OddStandard.ThmC.Core

open CFSG CFSG.Open Subgroup CFSG.ComponentClassification CFSG.OddStandard.ThmC
  CFSG.OddStandard.ThmC.T CFSG.GH74.GLS.Bg.TwoGroups
open scoped commutatorElement

theorem two_dvd_card_of_perfect (Y : Type) [Group Y] [Finite Y] [Group.IsPerfect Y]
    [Nontrivial Y] : 2 ∣ Nat.card Y := by
  by_contra h
  have hodd : Odd (Nat.card Y) := Nat.odd_iff.2 (by omega)
  exact Group.IsPerfect.not_isSolvable Y (CFSG.FeitThompson.isSolvable_of_odd_natCard Y hodd)

theorem pPrimeCore_eq_bot_of_simple (Y : Type) [Group Y] [Finite Y] [IsSimpleGroup Y]
    (heven : 2 ∣ Nat.card Y) : pPrimeCore 2 Y = ⊥ := by
  rcases (pPrimeCore_normal (p := 2) (G := Y)).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have hc := pPrimeCore_coprime_card (p := 2) (G := Y)
    rw [h, Subgroup.card_top] at hc
    exact absurd (Nat.Coprime.eq_one_of_dvd hc heven) (by norm_num)

theorem normalSimpleCore_of_hyps (hS2 : O2Structure) (hGor : CFSG.OddStandard.ThmC.O2.Gor42) :
    NormalSimpleCore := by
  intro X _ _ hO hO2 T hT
  have hfree : SolvableRadical.Free X := free_of_cores hO hO2
  have hcardT : Nat.card (T : Subgroup X) = 64 := IsT.card_eq hT
  have : Nontrivial X := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have h1 : Nat.card X = 1 := Nat.card_unique
    have h2 : Nat.card (T : Subgroup X) ≤ Nat.card X := Subgroup.card_le_card_group _
    omega
  set E : Subgroup X := Layer.subgroup X with hE
  have hEn : E.Normal := Layer.normal X
  have hEperf : Group.IsPerfect E := Layer.perfect X
  obtain ⟨L₀, hL₀⟩ := RadicalFreeLayer.exists_component hfree
  have hL₀nt : Nontrivial L₀ := Quasisimple.nontrivial hL₀.2.2
  have hEnt : Nontrivial E := by
    obtain ⟨x, hx1⟩ := exists_ne (1 : L₀)
    refine ⟨⟨⟨x, Layer.component_le hL₀ x.2⟩, 1, fun h => hx1 ?_⟩⟩
    have h' : (x : X) = 1 := congrArg Subtype.val h
    exact Subtype.ext h'
  have hEeven : 2 ∣ Nat.card E := two_dvd_card_of_perfect E
  have hOE : pPrimeCore 2 E = ⊥ := by
    have hfreeE := SolvableRadical.free_normal_subgroup hfree E
    refine hfreeE (pPrimeCore 2 E) pPrimeCore_normal ?_
    have hc := pPrimeCore_coprime_card (p := 2) (G := E)
    have hodd : Odd (Nat.card (pPrimeCore 2 E)) :=
      Nat.odd_iff.2 (by
        have : ¬ 2 ∣ Nat.card (pPrimeCore 2 E) := fun h =>
          absurd (Nat.Coprime.eq_one_of_dvd hc h) (by norm_num)
        omega)
    exact CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hTE : (T : Subgroup X) ≤ E := coreDichotomy hS2 hGor T hT E hEeven hOE
  have hcomp : ∀ L : Subgroup X, IsComponentOf L ⊤ → (T : Subgroup X) ≤ L := by
    intro L hL
    have hperf : Group.IsPerfect L := ⟨hL.2.2.1⟩
    have hnt : Nontrivial L := Quasisimple.nontrivial hL.2.2
    have hsimple : IsSimpleGroup L := RadicalFreeLayer.component_simple hfree L hL
    have heven : 2 ∣ Nat.card L := two_dvd_card_of_perfect L
    have hOL : pPrimeCore 2 L = ⊥ := pPrimeCore_eq_bot_of_simple L heven
    have hnorm : ∀ y ∈ E, ∀ l ∈ L, y * l * y⁻¹ ∈ L := fun y hy l hl => by
      have h1 := (Layer.normal_component hL).conj_mem ⟨l, Layer.component_le hL hl⟩
        (Subgroup.mem_subgroupOf.2 hl) ⟨y, hy⟩
      exact Subgroup.mem_subgroupOf.1 h1
    exact coreDichotomy_sub hS2 hGor T hT E L hTE (Layer.component_le hL) hnorm heven hOL
  have hunique : ∀ L L' : Subgroup X, IsComponentOf L ⊤ → IsComponentOf L' ⊤ → L = L' := by
    intro L L' hL hL'
    by_contra hne
    have hcomm := LocalComponents.commute_of_ne L L' hL hL' hne
    have hTab : ∀ a ∈ (T : Subgroup X), ∀ b ∈ (T : Subgroup X), a * b = b * a := by
      intro a ha b hb
      have h1 : ⁅a, b⁆ ∈ ⁅L, L'⁆ :=
        Subgroup.commutator_mem_commutator (hcomp L hL ha) (hcomp L' hL' hb)
      rw [hcomm, Subgroup.mem_bot] at h1
      exact commutatorElement_eq_one_iff_mul_comm.1 h1
    obtain ⟨Z, A, B, hTA⟩ := IsT.exists_tAmbient hT
    have hZT : (T : Subgroup X) ≤ Z := fun g hg =>
      (hTA.mem_Z g).2 ⟨hg, fun s hs => hTab g hg s hs⟩
    have hZle : Z ≤ (T : Subgroup X) := hTA.Z_le_A.trans hTA.A_le_S
    have heq : Z = (T : Subgroup X) := le_antisymm hZle hZT
    have hcZ : Nat.card Z = Nat.card (T : Subgroup X) := by rw [heq]
    rw [hTA.card_Z, hTA.card_S] at hcZ
    omega
  refine ⟨L₀, ⟨fun n hn g => ?_⟩, RadicalFreeLayer.component_simple hfree L₀ hL₀,
    hcomp L₀ hL₀⟩
  have hg : IsComponentOf (L₀.map (MulAut.conj g).toMonoidHom) ⊤ :=
    (LocalComponents.equiv_iff (MulAut.conj g) L₀).2 hL₀
  have hgeq := hunique _ _ hg hL₀
  have hmem : g * n * g⁻¹ ∈ L₀.map (MulAut.conj g).toMonoidHom :=
    ⟨n, hn, by simp [MulAut.conj_apply]⟩
  rwa [hgeq] at hmem

end CFSG.OddStandard.ThmC.Core
