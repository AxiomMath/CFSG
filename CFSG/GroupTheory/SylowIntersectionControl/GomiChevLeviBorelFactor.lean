module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsChev
import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsChevMap
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevCentralQuotient
import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.Chev
import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsPLType
import CFSG.Mathlib.GroupTheory.PermCenter
public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

@[expose] def GomiLeviFactor (X : Type) [Group X] : Prop :=
  IsGomiChevTwo X ∨ Nonempty (X ≃* Equiv.Perm (Fin 6))

theorem GomiLeviFactor.of_mulEquiv {X X' : Type} [Group X] [Group X'] (e : X ≃* X')
    (h : GomiLeviFactor X) : GomiLeviFactor X' := by
  rcases h with h | h
  · exact Or.inl (IsGomiChevTwo.of_mulEquiv e h)
  · obtain ⟨f⟩ := h
    exact Or.inr ⟨e.symm.trans f⟩

theorem IsGomiChevTwo.of_isQuasisimple {X : Type} [Group X] [Finite X] (hq : CFSG.IsQuasisimple X)
    (hZ : Odd (Nat.card (center X))) (hC : IsChevTwo (X ⧸ center X)) : IsGomiChevTwo X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hqO : CFSG.Open.IsQuasisimple X := ⟨hq.1.commutator_eq_top, hq.2.1⟩
  have hpc : CFSG.pCore 2 X ≤ center X := by
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hqO
        (CFSG.pCore 2 X) with hle | htop
    · exact hle
    · exfalso
      have : Nontrivial X := CFSG.ComponentClassification.Quasisimple.nontrivial hqO
      have : Group.IsPerfect X := hq.1
      have hpg : IsPGroup 2 (⊤ : Subgroup X) := htop ▸ (CFSG.pCore_isPGroup (p := 2) (G := X))
      have : Group.IsNilpotent X := (hpg.of_equiv Subgroup.topEquiv).isNilpotent
      exact Group.IsPerfect.not_isSolvable X inferInstance
  refine ⟨hq, ?_, hC⟩
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := X)).exists_card_eq
  have hd : Nat.card (CFSG.pCore 2 X) ∣ Nat.card (center X) := Subgroup.card_dvd_of_le hpc
  rw [hk] at hd
  have hk0 : k = 0 := by
    by_contra hk0
    exact hZ.not_two_dvd_nat ((dvd_pow_self 2 hk0).trans hd)
  rw [hk0, pow_zero] at hk
  exact Subgroup.card_eq_one.mp hk

theorem GomiLeviFactor.pCore_eq_bot {X : Type} [Group X] (h : GomiLeviFactor X) :
    CFSG.pCore 2 X = ⊥ := by
  rcases h with h | h
  · exact h.2.1
  · obtain ⟨e⟩ := h
    rw [← CFSG.pCore_map_iso 2 e.symm, CFSG.AGLEmbedding.pCore_perm_six_eq_bot,
      Subgroup.map_bot]

theorem GomiLeviFactor.quotient {X : Type} [Group X] [Finite X] (h : GomiLeviFactor X)
    (N : Subgroup X) [N.Normal] (hN : N ≤ center X) : GomiLeviFactor (X ⧸ N) := by
  rcases h with h | h
  · refine Or.inl ?_
    have : Group.IsPerfect X := h.1.1
    have hqO : CFSG.Open.IsQuasisimple X := ⟨h.1.1.commutator_eq_top, h.1.2.1⟩
    have hcenter : (center X).map (QuotientGroup.mk' N) = center (X ⧸ N) :=
      CFSG.ComponentClassification.Quasisimple.center_map_of_central_kernel
        (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
        (by rw [QuotientGroup.ker_mk']; exact hN)
    let iso : (X ⧸ N) ⧸ center (X ⧸ N) ≃* X ⧸ center X :=
      (QuotientGroup.quotientMulEquivOfEq hcenter.symm).trans
        (QuotientGroup.quotientQuotientEquivQuotient N (center X) hN)
    have hqOpen : CFSG.Open.IsQuasisimple (X ⧸ N) :=
      CFSG.ComponentClassification.Quasisimple.central_quotient hqO N hN
    have hq : CFSG.IsQuasisimple (X ⧸ N) := by
      refine ⟨⟨hqOpen.1⟩, hqOpen.2, ?_⟩
      obtain ⟨a, b, hab⟩ := h.1.2.2
      exact ⟨iso.symm a, iso.symm b, fun hh => hab (by simpa using congrArg iso hh)⟩
    have hZ : Odd (Nat.card (center (X ⧸ N))) := by
      rw [← hcenter]
      exact Odd.of_dvd_nat ((IsGomiChevTwo.coprime_card_center h).odd_of_right)
        (Subgroup.card_map_dvd (H := center X) (f := QuotientGroup.mk' N))
    have hC : IsChevTwo ((X ⧸ N) ⧸ center (X ⧸ N)) :=
      CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.isChevTwo_of_mulEquiv iso.symm h.2.2
    exact IsGomiChevTwo.of_isQuasisimple hq hZ hC
  · obtain ⟨e⟩ := h
    refine Or.inr ?_
    have hZ : center X = ⊥ := by
      refine (Subgroup.map_eq_bot_iff_of_injective (H := center X) (f := e.toMonoidHom)
        e.injective).mp ?_
      have hmap : (center X).map e.toMonoidHom = center (Equiv.Perm (Fin 6)) :=
        Subgroup.map_center_eq e
      rw [hmap, center_perm_eq_bot_of_three_le_card (α := Fin 6) (by norm_num)]
    have hNbot : N = ⊥ := le_bot_iff.mp (hN.trans (le_of_eq hZ))
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hNbot).trans
      (QuotientGroup.quotientBot.trans e)⟩

theorem GomiLeviFactor.map {K Y : Type} [Group K] [Group Y] [Finite K] (f : K →* Y)
    (hf : f.ker ≤ center K) {A : Subgroup K} (h : GomiLeviFactor ↥A) :
    GomiLeviFactor ↥(A.map f) := by
  let fA : ↥A →* Y := f.domRestrict A
  have hker : fA.ker ≤ center ↥A := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hx1 : fA x = 1 := hx
    change (f.domRestrict A) x = 1 at hx1
    rw [MonoidHom.domRestrict_apply] at hx1
    exact Subgroup.mem_center_iff.mp (hf hx1) (y : K)
  have hrange : fA.range = A.map f := by
    change (f.domRestrict A).range = A.map f
    rw [MonoidHom.domRestrict_range]
  let e : ↥A ⧸ fA.ker ≃* ↥(A.map f) :=
    (QuotientGroup.quotientKerEquivRange fA).trans (MulEquiv.subgroupCongr hrange)
  exact GomiLeviFactor.of_mulEquiv e (GomiLeviFactor.quotient h fA.ker hker)

end CFSG.GroupTheory

end
