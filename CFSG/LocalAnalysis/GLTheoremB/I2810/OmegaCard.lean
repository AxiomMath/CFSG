module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.Defs
public import CFSG.LieType.ChevTwo.Defs
import CFSG.LocalAnalysis.GLTheoremB.I2810.InducedAux
import CFSG.LocalAnalysis.GLTheoremB.I2810.OmegaAux
import CFSG.LocalAnalysis.GLTheoremB.I2810.OmegaOne
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidPlusFacts
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidMinusFacts

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open CFSG.LieType.ChevTwo
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.OmegaCard

variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

theorem quot_iso_model {ι : Type} [Fintype ι] [DecidableEq ι] (Q : (ι → ZMod 2) → ZMod 2)
    [IsSimpleGroup ↥(StatedOmega Q)] (hR : Red28 W K S) {a : X} {U₁ U₂ : Subgroup X}
    (hΩ : OmegaModelWith Q W K a U₁ U₂) :
    Nonempty ((↥(bar W K) ⧸ Subgroup.center ↥(bar W K)) ≃* ↥(StatedOmega Q)) := by
  obtain ⟨θ, t, hθs, hθW, -⟩ := hΩ
  obtain ⟨θb, hθb⟩ := OmegaAux.descend θ hθW
  have hsurj : Function.Surjective θb := by
    intro y
    obtain ⟨k, rfl⟩ := hθs y
    exact ⟨toBar W K k, by rw [← MonoidHom.comp_apply, hθb]⟩
  exact OmegaAux.quasisimple_quot_iso hR.quasi θb hsurj

theorem isOmegaTwo_quot (hR : Red28 W K S) {a : X} {U₁ U₂ : Subgroup X} {n : ℕ} (hn : 2 ≤ n)
    (hΩ : OmegaAny W K a U₁ U₂ n) :
    ∃ ε : Bool, IsOmegaTwo ε (n + 1) (↥(bar W K) ⧸ Subgroup.center ↥(bar W K)) := by
  rcases hΩ with hp | hmi
  · haveI : IsSimpleGroup ↥(StatedOmega (StatedQuadPlus (n + 1) (ZMod 2))) :=
      CFSG.ComponentClassification.RankTwoClassical.ORigid.isSimpleGroup_statedOmega_quadPlus_of_three_le
        (K := ZMod 2) (k := n + 1) (by omega)
    exact ⟨true, quot_iso_model _ hR hp⟩
  · haveI : IsSimpleGroup ↥(StatedOmega (StatedQuadMinus (n + 1) (ZMod 2) 1 1)) :=
      CFSG.ComponentClassification.RankTwoClassical.ORigid.isSimpleGroup_statedOmega_quadMinus_of_two_le
        (K := ZMod 2) (b := 1) (c := 1) (m := n + 1) (by omega) (by decide)
    exact ⟨false, quot_iso_model _ hR hmi⟩

theorem card_le_two (hL1 : OmegaTwoAutTwoPart) {G : Type} [Group G] [Finite G]
    (hG : commutator G = ⊤) (hGs : IsSimpleGroup (G ⧸ Subgroup.center G)) {ε : Bool} {n : ℕ}
    (hn : 1 ≤ n) (hΩ : IsOmegaTwo ε (n + 1) (G ⧸ Subgroup.center G))
    (F : Subgroup (MulAut G)) (hF2 : IsPGroup 2 ↥F)
    (hFin : F ⊓ (MulAut.conj : G →* MulAut G).range = ⊥) : Nat.card ↥F ≤ 2 := by
  set T : Subgroup (MulAut (G ⧸ Subgroup.center G)) := F.map (InducedAux.autCenterQuot G) with hT
  have hinj := InducedAux.autCenterQuot_injective hG
  have hT2 : IsPGroup 2 ↥T := hF2.map _
  have hTin : T ⊓ (MulAut.conj : (G ⧸ Subgroup.center G) →* MulAut (G ⧸ Subgroup.center G)).range =
      ⊥ := by
    rw [eq_bot_iff]
    rintro φ ⟨hφT, hφI⟩
    obtain ⟨f, hfF, rfl⟩ := hφT
    obtain ⟨c, hc⟩ := hφI
    obtain ⟨c0, rfl⟩ := QuotientGroup.mk_surjective c
    have h1 : InducedAux.autCenterQuot G (MulAut.conj c0) = InducedAux.autCenterQuot G f := by
      rw [InducedAux.autCenterQuot_conj]
      exact hc
    have h2 : f = MulAut.conj c0 := (hinj h1).symm
    have : f ∈ F ⊓ (MulAut.conj : G →* MulAut G).range := ⟨hfF, ⟨c0, h2.symm⟩⟩
    rw [hFin, Subgroup.mem_bot] at this
    rw [this, map_one]
    exact Subgroup.one_mem _
  have hle := hL1 ε n hn (G ⧸ Subgroup.center G) hGs hΩ T hT2 hTin
  rw [hT, Subgroup.card_map_of_injective hinj] at hle
  exact hle

theorem c1_cardS_aux (hL1 : OmegaTwoAutTwoPart) (h : Setup28 W K S) (hR : Red28 W K S)
    (h1 : Hyp28One W K S) {A : Subgroup X} (hA : Off28 W K S A)
    (hc : Nat.card ↥(indAut W K A) = 2) {a : X} {U₁ U₂ : Subgroup X} {n : ℕ} (hn : 1 ≤ n)
    (hΩ : OmegaAny W K a U₁ U₂ n) : Nat.card ↥(indAut W K S) = 2 := by
  have hn2 : 2 ≤ n := by
    by_contra hlt
    obtain rfl : n = 1 := by omega
    exact OmegaOne.false_of_n_one h hR h1 hΩ
  obtain ⟨ε, hε⟩ := isOmegaTwo_quot hR hn2 hΩ
  have hF2 : IsPGroup 2 ↥(indAut W K S) := by
    have := h.hS.of_surjective (InducedAux.indHom W K S h.hN).rangeRestrict
      (InducedAux.indHom W K S h.hN).rangeRestrict_surjective
    rwa [InducedAux.range_indHom S h.hN] at this
  have hle : Nat.card ↥(indAut W K S) ≤ 2 :=
    card_le_two hL1 hR.quasi.1.commutator_eq_top hR.quasi.2.1 (by omega) hε _ hF2 h1.2.2
  have hge : Nat.card ↥(indAut W K A) ≤ Nat.card ↥(indAut W K S) :=
    Subgroup.card_le_of_le (indAut_mono hA.isMax.1)
  omega

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.OmegaCard
