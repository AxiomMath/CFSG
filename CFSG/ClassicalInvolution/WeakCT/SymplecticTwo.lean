module

public import CFSG.ClassicalInvolution.WeakCT.Symplectic
import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCRecognition
import CFSG.RankThree.PartOne.CTP.SpEven
import CFSG.ClassicalInvolution.WeakCT.SpTwoFrame
import CFSG.ClassicalInvolution.WeakCT.SpTwoInj

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.Assembly.LowTwoRank CFSG.LieType CFSG.LieType.Universal CFSG.Timmesfeld CFSG.Blueprint
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockStandardPair)
open scoped MatrixGroups

variable {F : Type} [Field F] {X : Type} [Group X]

private theorem sp_two_admissible {n : ℕ} (hn : 3 ≤ n) : StatedLieAdmissible .PSp n 2 1 :=
  ⟨Nat.prime_two, le_rfl, by omega, fun h => by
    have h1 : n = 2 := congrArg Prod.fst h
    omega⟩

private theorem edgeDown_comm_pair {n : ℕ} {U : Fin n → Subgroup X}
    (hcomm : ∀ i j : Fin n, i.val + 1 < j.val → ∀ x ∈ U i, ∀ y ∈ U j, x * y = y * x)
    (hpair : ∀ i j : Fin n, i.val + 1 = j.val → j.val + 1 < n →
      ∃ W, LinearBlockStandardPair F W (U i) (U j))
    {a b : Fin n} (ha : a.val + 1 = n) (hb : b.val + 2 = n) :
    (∀ i j : Fin n, i ≠ j → ¬ edgeDown n i j → ¬ edgeDown n j i →
      ∀ u ∈ U i, ∀ v ∈ U j, u * v = v * u) ∧
      (∀ i j : Fin n, edgeDown n i j → ¬ (i = a ∧ j = b) →
        ∃ W, LinearBlockStandardPair F W (U i) (U j)) := by
  constructor
  · intro i j hne h1 h2 u hu v hv
    simp only [edgeDown] at h1 h2
    rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h) : i.val ≠ j.val) with hlt | hgt
    · exact hcomm i j (by omega) u hu v hv
    · exact (hcomm j i (by omega) v hv u hu).symm
  · intro i j hij hn'
    simp only [edgeDown] at hij
    obtain ⟨W, hW⟩ := hpair j i hij (by
      by_contra hc
      exact hn' ⟨Fin.ext (by omega), Fin.ext (by omega)⟩)
    exact ⟨W, hW.symm⟩

private theorem exists_frame_sp_two_edgeDown {n : ℕ} (hn : 3 ≤ n) (hF : Nat.card F = 2)
    {U : Fin n → Subgroup X}
    (hcomm : ∀ i j : Fin n, i.val + 1 < j.val → ∀ x ∈ U i, ∀ y ∈ U j, x * y = y * x)
    (hpair : ∀ i j : Fin n, i.val + 1 = j.val → j.val + 1 < n →
      ∃ W, LinearBlockStandardPair F W (U i) (U j))
    (hsp : ∀ i j : Fin n, i.val + 1 = n → j.val + 2 = n →
      ∃ W, SymplecticBlockStandardPair F W (U i) (U j))
    {a b : Fin n} (ha : a.val + 1 = n) (hb : b.val + 2 = n) :
    ∃ ρ : Fin n → SL(2, F) →* X, (∀ k, Function.Injective (ρ k) ∧ (ρ k).range = U k) ∧
      (∀ i j : Fin n, edgeDown n i j → ¬ (i = a ∧ j = b) → ∃ ψ : SL(3, F) →* X,
        ψ.comp (blk F 0) = ρ i ∧ ψ.comp (blk F 1) = ρ j) ∧
      ∃ ψ : StatedSp 2 F →* X, ψ.comp (spBlock F 1) = ρ a ∧ ψ.comp (spBlock F 0) = ρ b := by
  obtain ⟨ρ, hρ, hψ, hψ4⟩ := exists_frame_of_chain_sp_two hF hn hcomm hpair hsp
  refine ⟨ρ, hρ, ?_, hψ4 a b ha hb⟩
  intro i j hij hn'
  refine hψ i j hij ?_
  by_contra h
  exact hn' ⟨Fin.ext (by omega), Fin.ext (by omega)⟩

theorem weakCT_symplectic_two_gen {n : ℕ} (hn : 3 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2) {X : Type} [Group X] (U : Fin n → Subgroup X) (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j : Fin n, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j : Fin n, i.val + 1 = j.val → j.val + 1 < n →
      ∃ W, LinearBlockStandardPair F W (U i) (U j))
    (hsp : ∀ i j : Fin n, i.val + 1 = n → j.val + 2 = n →
      ∃ W, CFSG.ClassicalInvolution.Models.SymplecticPairs.SymplecticBlockStandardPair F W
        (U i) (U j)) :
    ∃ Ψ : StatedSp n F →* X, Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center _ ∧
      IsQuasisimple X ∧ Subgroup.center X = (Subgroup.center (StatedSp n F)).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) .PSp n 2 1 ∧
      ∀ k, (CurtisTits.rankOne (Symplectic.rootDatum n F).rootGroup k).map Ψ = U k := by
  obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan (Symplectic.rootDatum n F).isFiniteType
    (Dv := (Symplectic.rootDatum n F).divisible) rfl
  have hE := Steinberg.Sp.chevalleyExtras (by omega : 2 ≤ n) O Steinberg.Sp.commC
    (Steinberg.Sp.commutatorFormula O)
  obtain ⟨a, ha⟩ : ∃ a : Fin n, a.val + 1 = n :=
    ⟨⟨n - 1, by omega⟩, by show n - 1 + 1 = n; omega⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin n, b.val + 2 = n :=
    ⟨⟨n - 2, by omega⟩, by show n - 2 + 2 = n; omega⟩
  have hsq : ∀ k : Fin n,
      Steinberg.weylElement (Steinberg.Sp.x n F) k 1 ^ 2 ∈ Symplectic.torus n F k := by
    intro k
    rw [weylElement_sp_one]
    exact (Symplectic.isCTGroupDatum n F).sq_mem k
  obtain ⟨hcomm', hpair'⟩ := edgeDown_comm_pair hcomm hpair ha hb
  obtain ⟨ρ, hρ, hψ, hψ4⟩ := exists_frame_sp_two_edgeDown hn hF hcomm hpair hsp ha hb
  exact CFSG.RankThree.PartOne.CTP.weakCT_of_frame_dl_of_longInj
    (fun φ h => hom_injective_of_long_two hF h)
    (CurtisTits.curtisTitsConclusion_symplectic (sp_two_admissible hn) (by rw [hF, pow_one]) hn)
    (leviConePresented_symplectic n F) hE rfl (doubleBondDiagram_cartanC hn ha hb)
    (Symplectic.steinbergExtras n F).torus_iSupIndep hsq hgen hcomm' hρ hψ hψ4

private theorem exists_weakCT_two_of_iSup {n : ℕ} (hn : 3 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2) {G : Type} [Group G] (U : Fin n → Subgroup G)
    (hcomm : ∀ i j : Fin n, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j : Fin n, i.val + 1 = j.val → j.val + 1 < n →
      ∃ W, LinearBlockStandardPair F W (U i) (U j))
    (hsp : ∀ i j : Fin n, i.val + 1 = n → j.val + 2 = n →
      ∃ W, SymplecticBlockStandardPair F W (U i) (U j)) :
    ∃ Ψ : StatedSp n F →* ↥(⨆ k, U k), Function.Surjective Ψ ∧
      Ψ.ker ≤ Subgroup.center (StatedSp n F) := by
  let Ks : Subgroup G := ⨆ k, U k
  have hUle : ∀ k, U k ≤ Ks := fun k => le_iSup U k
  obtain ⟨Ψ', hsurj, hker, -⟩ :=
    weakCT_symplectic_two_gen hn hF (fun k => (U k).subgroupOf Ks)
      (CFSG.ClassicalInvolution.Models.SymplecticPairs.iSup_subgroupOf_eq_top U)
      (fun i j hij a ha b hb =>
        Subtype.ext (hcomm i j hij a.1 (Subgroup.mem_subgroupOf.mp ha) b.1
          (Subgroup.mem_subgroupOf.mp hb)))
      (fun i j hij hj => by
        obtain ⟨W, hW⟩ := hpair i j hij hj
        exact ⟨W.subgroupOf Ks,
          CFSG.ClassicalInvolution.Models.SymplecticPairs.linearBlockStandardPair_subgroupOf
            ((CFSG.ClassicalInvolution.Models.SymplecticPairs.linearBlockStandardPair_le_sup
              hW).trans (sup_le (hUle i) (hUle j))) hW⟩)
      (fun i j hi hj => by
        obtain ⟨W, hW⟩ := hsp i j hi hj
        exact ⟨W.subgroupOf Ks,
          CFSG.ClassicalInvolution.Models.SymplecticPairs.symplecticBlockStandardPair_subgroupOf
            ((CFSG.ClassicalInvolution.Models.SymplecticPairs.symplecticBlockStandardPair_le_sup
              hW).trans (sup_le (hUle i) (hUle j))) hW⟩)
  exact ⟨Ψ', hsurj, hker⟩

theorem weakCT_symplectic_two {n : ℕ} (hn : 3 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2) {G : Type} [Group G] (U : Fin n → Subgroup G)
    (hcomm : ∀ i j : Fin n, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j : Fin n, i.val + 1 = j.val → j.val + 1 < n →
      ∃ W, LinearBlockStandardPair F W (U i) (U j))
    (hsp : ∀ i j : Fin n, i.val + 1 = n → j.val + 2 = n →
      ∃ W, CFSG.ClassicalInvolution.Models.SymplecticPairs.SymplecticBlockStandardPair F W
        (U i) (U j)) :
    ∃ Ψ : StatedSp n F →* G, Ψ.ker ≤ Subgroup.center (StatedSp n F) ∧
      Ψ.range = ⨆ k, U k := by
  obtain ⟨Ψ', hsurj, hker⟩ := exists_weakCT_two_of_iSup hn hF U hcomm hpair hsp
  refine ⟨(⨆ k, U k).subtype.comp Ψ', ?_, ?_⟩
  · intro x hx
    exact hker (Subtype.ext (MonoidHom.mem_ker.mp hx))
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top,
      Subgroup.range_subtype]

end CFSG.ClassicalInvolution.WeakCT
