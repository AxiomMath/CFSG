module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.FixPrimeBar

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open CFSG.AGLEmbedding

structure FixBarFull {X : Type*} [Group X] [Finite X] (J : Subgroup X) (p : ℕ) (v : X) :
    Prop where
  base : FixBarData J p v
  fix_all : ∀ g : X, g * v = v * g → g ∈ J

theorem FixBarFull.map_mulEquiv {X X' : Type*} [Group X] [Finite X] [Group X'] [Finite X']
    (e : X ≃* X') {J : Subgroup X} {p : ℕ} {v : X} (h : FixBarFull J p v) :
    FixBarFull (J.map e.toMonoidHom) p (e v) := by
  refine ⟨h.base.map_mulEquiv e, fun g hg => ?_⟩
  have : e.symm g * v = v * e.symm g := by
    apply e.injective
    simpa using hg
  exact ⟨e.symm g, h.fix_all _ this, by simp⟩

variable {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y}

theorem exists_fixBarFull_of_fixThreeHyp {u : Y} (h : FixThreeHyp L J u)
    (hZ : Nat.card (Subgroup.center ↥L) = 1) :
    ∃ v : ↥L ⧸ Subgroup.center ↥L,
      FixBarFull ((J.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))) 3 v := by
  obtain ⟨v, hb, hf⟩ := exists_fixBarData_full_of_census h.parab Nat.prime_three h.cyc h.join h.pow
    h.not_mem h.fix hZ
  exact ⟨v, ⟨hb, hf⟩⟩

theorem exists_fixBarFull_of_fixPrimeHyp {p : ℕ} {u : Y} (h : FixPrimeHyp L J p u)
    (hZ : Nat.card (Subgroup.center ↥L) = 1) :
    ∃ v : ↥L ⧸ Subgroup.center ↥L,
      FixBarFull ((J.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))) p v := by
  obtain ⟨v, hb, hf⟩ := exists_fixBarData_full_of_census h.parab h.prime h.cyc h.join h.pow
    h.not_mem h.fix hZ
  exact ⟨v, ⟨hb, hf⟩⟩

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
