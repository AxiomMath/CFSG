module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanTwoGenInnerAbstract

public section

namespace CFSG.AGLEmbedding.TwoGenInner

open CFSG.RankThree.PartOne.OutStructure (Inn actionOnQuot actionOnQuot_mem_inner_iff)

theorem mem_sup_centralizer_of_pGoodOut {Y : Type} [Group Y] [Finite Y] (L : Subgroup Y)
    (hL : CFSG.Open.IsQuasisimple ↥L) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : PGoodOut p (↥L ⧸ Subgroup.center ↥L)) {x : Y}
    (hx : x ∈ Subgroup.closure
      {a : Y | a ∈ Subgroup.normalizer (L : Set Y) ∧ ∃ k : ℕ, a ^ 2 ^ k = 1})
    (hxp : ∃ k : ℕ, x ^ p ^ k = 1) : x ∈ L ⊔ Subgroup.centralizer (L : Set Y) := by
  have : Group.IsPerfect ↥L := ⟨hL.1⟩
  set N : Subgroup Y := Subgroup.normalizer (L : Set Y) with hN
  set ρ := actionOnQuot L with hρ
  set C := Subgroup.closure {α : MulAut (↥L ⧸ Subgroup.center ↥L) | ∃ k : ℕ, α ^ 2 ^ k = 1}
    with hC
  have hxN : x ∈ N :=
    (Subgroup.closure_le N).2 (fun a ha => ha.1) hx
  have hgen : {a : Y | a ∈ N ∧ ∃ k : ℕ, a ^ 2 ^ k = 1} ⊆ (C.comap ρ).map N.subtype := by
    rintro a ⟨haN, k, hk⟩
    refine ⟨⟨a, haN⟩, ?_, rfl⟩
    refine Subgroup.subset_closure ⟨k, ?_⟩
    rw [← map_pow]
    have : (⟨a, haN⟩ : N) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
    rw [this, map_one]
  have hxD : x ∈ (C.comap ρ).map N.subtype := (Subgroup.closure_le _).2 hgen hx
  obtain ⟨x', hx'C, hx'x⟩ := hxD
  have hx'eq : x' = ⟨x, hxN⟩ := Subtype.ext hx'x
  obtain ⟨k, hk⟩ := hxp
  have hpe : (ρ x') ^ p ^ k = 1 := by
    rw [← map_pow]
    have : x' ^ p ^ k = 1 := Subtype.ext (by rw [hx'eq]; simpa using hk)
    rw [this, map_one]
  have hinn : ρ x' ∈ Inn (↥L ⧸ Subgroup.center ↥L) :=
    twoGenPInner_of_pGoodOut hp hp2 h (ρ x') hx'C ⟨k, hpe⟩
  rw [hx'eq] at hinn
  exact (actionOnQuot_mem_inner_iff L hxN).1 hinn

end CFSG.AGLEmbedding.TwoGenInner
