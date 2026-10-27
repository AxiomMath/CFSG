module

public import CFSG.ClassicalInvolution.WeakCT.Blocks
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
import CFSG.RankThree.PartOne.CTP.SpEven
import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCRecognition
import CFSG.ClassicalInvolution.Balance.QNineStandard
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizePieces

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock shortBlock)
open scoped MatrixGroups

private theorem spCharts_shortBlock_congr {K : Type} [Field K] {n : ℕ} {i i' j j' : Fin n}
    (hij : i ≠ j) (hij' : i' ≠ j') (hi : i = i') (hj : j = j') :
    shortBlock K hij = shortBlock K hij' := by
  subst hi
  subst hj
  exact congrArg (shortBlock K) (Subsingleton.elim hij hij')

private theorem spCharts_comm {r : ℕ} {F : Type} [Field F] {G : Type} [Group G]
    (σ : SL(r + 2, F) →* G) (κ : StatedSp (r + 1) F →* G)
    (hagree : ∀ k : Fin r, (σ.comp (blockSL2 F (r + 1) k.succ)).range =
      (κ.comp (shortBlock F (Fin.castSucc_lt_succ (i := k)).ne)).range)
    (hcross : ∀ a ∈ (σ.comp (blockSL2 F (r + 1) 0)).range,
      ∀ b ∈ (κ.comp (longBlock F (r + 1) (Fin.last r))).range, a * b = b * a)
    (U : Fin (r + 2) → Subgroup G)
    (hU : ∀ k : Fin (r + 1), U (Fin.castSucc k) = (σ.comp (blockSL2 F (r + 1) k)).range)
    (hUlast : U (Fin.last (r + 1)) = (κ.comp (longBlock F (r + 1) (Fin.last r))).range) :
    ∀ i j : Fin (r + 2), i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a := by
  intro i j hij a ha b hb
  rcases Fin.eq_castSucc_or_eq_last (n := r + 1) i with ⟨i', rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last (n := r + 1) j with ⟨j', rfl⟩ | rfl
    · rw [hU i'] at ha
      rw [hU j'] at hb
      obtain ⟨A, rfl⟩ := MonoidHom.mem_range.mp ha
      obtain ⟨B, rfl⟩ := MonoidHom.mem_range.mp hb
      change σ (blockSL2 F (r + 1) i' A) * σ (blockSL2 F (r + 1) j' B) =
        σ (blockSL2 F (r + 1) j' B) * σ (blockSL2 F (r + 1) i' A)
      rw [← map_mul, ← map_mul,
        blockSL2_comm (K := F) (n := r + 1) i' j' (by simpa using hij) A B]
    · rw [hUlast] at hb
      have hi'lt : (i' : ℕ) < r := by
        have h := hij
        simp only [Fin.val_castSucc, Fin.val_last] at h
        omega
      rcases Nat.eq_zero_or_pos i'.val with h0 | hpos
      · have hi0 : i' = 0 := Fin.ext (by simpa using h0)
        rw [hi0, hU 0] at ha
        exact hcross a ha b hb
      · obtain ⟨k, hk⟩ : ∃ k : Fin r, k.succ = i' :=
          ⟨⟨i'.val - 1, by omega⟩, Fin.ext (by simp only [Fin.val_succ]; omega)⟩
        rw [← hk, hU k.succ, hagree k] at ha
        obtain ⟨A, rfl⟩ := MonoidHom.mem_range.mp ha
        obtain ⟨B, rfl⟩ := MonoidHom.mem_range.mp hb
        have hkval : (k : ℕ) + 1 = (i' : ℕ) := by
          have h := congrArg Fin.val hk
          simpa only [Fin.val_succ] using h
        have hki : Fin.last r ≠ k.castSucc := by
          intro h
          have h1 : (k.castSucc : ℕ) = r := by
            rw [← h]
            exact Fin.val_last r
          rw [Fin.val_castSucc] at h1
          omega
        have hkj : Fin.last r ≠ k.succ := by
          intro h
          have h1 : (k.succ : ℕ) = r := by
            rw [← h]
            exact Fin.val_last r
          rw [Fin.val_succ] at h1
          omega
        change κ (shortBlock F (Fin.castSucc_lt_succ (i := k)).ne A) *
            κ (longBlock F (r + 1) (Fin.last r) B) =
          κ (longBlock F (r + 1) (Fin.last r) B) *
            κ (shortBlock F (Fin.castSucc_lt_succ (i := k)).ne A)
        rw [← map_mul, ← map_mul,
          CFSG.ClassicalInvolution.Models.SymplecticPairs.commute_shortBlock_longBlock
            (Fin.castSucc_lt_succ (i := k)).ne hki hkj A B]
  · exact absurd hij (by have := j.isLt; simp only [Fin.val_last] at hij; omega)

theorem exists_linearBlockStandardPair_of_blockSL2_frame {r : ℕ} {F : Type} [Field F]
    {G : Type} [Group G]
    (σ : SL(r + 2, F) →* G) (hσ : σ.ker ≤ Subgroup.center SL(r + 2, F))
    (U : Fin (r + 2) → Subgroup G)
    (hU : ∀ k : Fin (r + 1), U (Fin.castSucc k) = (σ.comp (blockSL2 F (r + 1) k)).range) :
    ∀ i j : Fin (r + 2), i.val + 1 = j.val → j.val + 1 < r + 2 →
      ∃ W, LinearBlockStandardPair F W (U i) (U j) := by
  intro i j hij hj
  rcases Fin.eq_castSucc_or_eq_last (n := r + 1) i with ⟨i', rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last (n := r + 1) j with ⟨j', rfl⟩ | rfl
    · have hW := (weakCTSystem_standard (K := F) (r + 1)).pair i' j'
        (by simpa using hij.symm)
      have hmap :=
        CFSG.ClassicalInvolution.Balance.linearBlockStandardPair_map_of_ker_le_center hW σ hσ
      have e1 : (blockSL2 F (r + 1) i').range.map σ = U (Fin.castSucc i') := by
        rw [MonoidHom.map_range, hU i']
      have e2 : (blockSL2 F (r + 1) j').range.map σ = U (Fin.castSucc j') := by
        rw [MonoidHom.map_range, hU j']
      exact ⟨_, by rw [e1, e2] at hmap; exact hmap⟩
    · exact absurd hj (by simp only [Fin.val_last] at hj; omega)
  · exact absurd hij (by have := j.isLt; simp only [Fin.val_last] at hij; omega)

private theorem spCharts_sp {r : ℕ} (hr : 1 ≤ r) {F : Type} [Field F] {G : Type} [Group G]
    (σ : SL(r + 2, F) →* G) (κ : StatedSp (r + 1) F →* G) (hκ : Function.Injective κ)
    (hagree : ∀ k : Fin r, (σ.comp (blockSL2 F (r + 1) k.succ)).range =
      (κ.comp (shortBlock F (Fin.castSucc_lt_succ (i := k)).ne)).range)
    (U : Fin (r + 2) → Subgroup G)
    (hU : ∀ k : Fin (r + 1), U (Fin.castSucc k) = (σ.comp (blockSL2 F (r + 1) k)).range)
    (hUlast : U (Fin.last (r + 1)) = (κ.comp (longBlock F (r + 1) (Fin.last r))).range) :
    ∀ i j : Fin (r + 2), i.val + 1 = r + 2 → j.val + 2 = r + 2 →
      ∃ W, CFSG.ClassicalInvolution.Models.SymplecticPairs.SymplecticBlockStandardPair F W
        (U i) (U j) := by
  intro i j hi hj
  set k : Fin r := ⟨r - 1, by omega⟩ with hk
  have hkval : (k : ℕ) = r - 1 := rfl
  have hiL : i = Fin.last (r + 1) := Fin.ext (by simp only [Fin.val_last]; omega)
  have hjL : j = Fin.castSucc k.succ := Fin.ext (by
    simp only [Fin.val_castSucc, Fin.val_succ]
    omega)
  rw [hiL, hjL, hUlast, hU k.succ, hagree k]
  have hW :=
    CFSG.ClassicalInvolution.Models.SymplecticPairs.symplecticBlockStandardPair_longShort
      (K := F) (n := r + 1) (i := k.castSucc) (j := k.succ)
        (Fin.castSucc_lt_succ (i := k)).ne
  have hsucc : k.succ = (Fin.last r : Fin (r + 1)) := Fin.ext (by
    simp only [Fin.val_succ, Fin.val_last]
    omega)
  have e1 : (longBlock F (r + 1) k.succ).range.map κ =
      (κ.comp (longBlock F (r + 1) (Fin.last r))).range := by
    rw [MonoidHom.map_range, hsucc]
  have e2 : (shortBlock F (Fin.castSucc_lt_succ (i := k)).ne).range.map κ =
      (κ.comp (shortBlock F (Fin.castSucc_lt_succ (i := k)).ne)).range :=
    MonoidHom.map_range κ _
  have hmap :=
    CFSG.ClassicalInvolution.Models.SymplecticPairs.symplecticBlockStandardPair_map hW κ hκ
  exact ⟨_, by rw [e1, e2] at hmap; exact hmap⟩

private theorem spCharts_iSup_le {r : ℕ} {F : Type} [Field F] {G : Type} [Group G]
    (σ : SL(r + 2, F) →* G) (κ : StatedSp (r + 1) F →* G)
    (U : Fin (r + 2) → Subgroup G)
    (hU : ∀ k : Fin (r + 1), U (Fin.castSucc k) = (σ.comp (blockSL2 F (r + 1) k)).range)
    (hUlast : U (Fin.last (r + 1)) = (κ.comp (longBlock F (r + 1) (Fin.last r))).range) :
    (⨆ k, U k) ≤ σ.range ⊔ κ.range := by
  refine iSup_le fun k => ?_
  rcases Fin.eq_castSucc_or_eq_last (n := r + 1) k with ⟨k', rfl⟩ | rfl
  · rw [hU k', ← MonoidHom.map_range σ (blockSL2 F (r + 1) k')]
    exact (Subgroup.map_le_range σ _).trans le_sup_left
  · rw [hUlast, ← MonoidHom.map_range κ (longBlock F (r + 1) (Fin.last r))]
    exact (Subgroup.map_le_range κ _).trans le_sup_right

private theorem spCharts_le_iSup {r : ℕ} {F : Type} [Field F] {G : Type} [Group G]
    (σ : SL(r + 2, F) →* G) (κ : StatedSp (r + 1) F →* G)
    (hagree : ∀ k : Fin r, (σ.comp (blockSL2 F (r + 1) k.succ)).range =
      (κ.comp (shortBlock F (Fin.castSucc_lt_succ (i := k)).ne)).range)
    (U : Fin (r + 2) → Subgroup G)
    (hU : ∀ k : Fin (r + 1), U (Fin.castSucc k) = (σ.comp (blockSL2 F (r + 1) k)).range)
    (hUlast : U (Fin.last (r + 1)) = (κ.comp (longBlock F (r + 1) (Fin.last r))).range) :
    σ.range ⊔ κ.range ≤ ⨆ k, U k := by
  refine sup_le ?_ ?_
  · rw [MonoidHom.range_eq_map, ← iSup_range_blockSL2 (K := F) (n := r + 1),
      Subgroup.map_iSup]
    refine iSup_le fun k => ?_
    rw [MonoidHom.map_range, ← hU k]
    exact le_iSup U (Fin.castSucc k)
  · rw [MonoidHom.range_eq_map,
      ← CFSG.SeitzReduction.SymplecticPilot.iSup_simpleRootSL2_eq_top (F := F) (n := r + 1)
        (by omega), Subgroup.map_iSup]
    refine iSup_le fun k => ?_
    by_cases hk : k.val + 1 < r + 1
    · have hk' : k.val < r := by omega
      have hkc : (k : Fin (r + 1)) = (⟨k.val, hk'⟩ : Fin r).castSucc := Fin.ext rfl
      have hks : (⟨k.val + 1, hk⟩ : Fin (r + 1)) = (⟨k.val, hk'⟩ : Fin r).succ := Fin.ext rfl
      have hsb : shortBlock F (CFSG.LieType.Universal.Symplectic.SpExtras.ne_succ' hk) =
          shortBlock F (Fin.castSucc_lt_succ (i := (⟨k.val, hk'⟩ : Fin r))).ne :=
        spCharts_shortBlock_congr _ _ hkc hks
      rw [CFSG.SeitzReduction.SymplecticPilot.simpleRootSL2_of_lt hk, hsb, MonoidHom.map_range,
        ← hagree ⟨k.val, hk'⟩, ← hU (⟨k.val, hk'⟩ : Fin r).succ]
      exact le_iSup U (Fin.castSucc (⟨k.val, hk'⟩ : Fin r).succ)
    · have hkr : k.val = r := by have := k.isLt; omega
      have hkl : (k : Fin (r + 1)) = Fin.last r := Fin.ext (by simpa using hkr)
      have hlong : CFSG.SeitzReduction.SymplecticPilot.simpleRootSL2 F k =
          (longBlock F (r + 1) k).range := by
        rw [CFSG.SeitzReduction.SymplecticPilot.simpleRootSL2_of_not_lt hk]
        rfl
      rw [hlong, MonoidHom.map_range, hkl, ← hUlast]
      exact le_iSup U (Fin.last (r + 1))

private theorem spCharts_recog {n f : ℕ} (hadm : StatedLieAdmissible .PSp n 2 f) (hn : 3 ≤ n)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2 ^ f)
    (hq : 4 ≤ Nat.card F) {G : Type} [Group G] (U : Fin n → Subgroup G)
    (hcomm : ∀ i j : Fin n, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j : Fin n, i.val + 1 = j.val → j.val + 1 < n →
      ∃ W, LinearBlockStandardPair F W (U i) (U j))
    (hsp : ∀ i j : Fin n, i.val + 1 = n → j.val + 2 = n →
      ∃ W, CFSG.ClassicalInvolution.Models.SymplecticPairs.SymplecticBlockStandardPair F W
        (U i) (U j)) :
    ∃ Ψ : StatedSp n F →* G, Ψ.ker ≤ Subgroup.center (StatedSp n F) ∧
      Ψ.range = ⨆ k, U k := by
  let Ks : Subgroup G := ⨆ k, U k
  have hUle : ∀ k, U k ≤ Ks := fun k => le_iSup U k
  obtain ⟨Ψ', hsurj, hker, -⟩ :=
    CFSG.RankThree.PartOne.CTP.weakCT_symplectic_even hadm hn hF hq
      (fun k => (U k).subgroupOf Ks)
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
  refine ⟨Ks.subtype.comp Ψ', ?_, ?_⟩
  · intro x hx
    exact hker (Subtype.ext (MonoidHom.mem_ker.mp hx))
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top,
      Subgroup.range_subtype]

theorem weakCT_symplectic_even_of_charts {r f : ℕ} (hr : 1 ≤ r) {F : Type} [Field F] [Finite F]
    [CharP F 2] (hF : Nat.card F = 2 ^ f) (hq : 4 ≤ Nat.card F) {G : Type} [Group G]
    (σ : SL(r + 2, F) →* G) (hσ : σ.ker ≤ Subgroup.center SL(r + 2, F))
    (κ : StatedSp (r + 1) F →* G) (hκ : Function.Injective κ)
    (hagree : ∀ k : Fin r, (σ.comp (blockSL2 F (r + 1) k.succ)).range =
      (κ.comp (shortBlock F (Fin.castSucc_lt_succ (i := k)).ne)).range)
    (hcross : ∀ a ∈ (σ.comp (blockSL2 F (r + 1) 0)).range,
      ∀ b ∈ (κ.comp (longBlock F (r + 1) (Fin.last r))).range, a * b = b * a) :
    ∃ Ψ : StatedSp (r + 2) F →* G, Ψ.ker ≤ Subgroup.center (StatedSp (r + 2) F) ∧
      Ψ.range = σ.range ⊔ κ.range := by
  have hf : 1 ≤ f := by
    by_contra h
    have h0 : f = 0 := by omega
    have h1 : 2 ^ f = 1 := by rw [h0]; simp
    omega
  have hne : ((r + 2, 2 ^ f) : ℕ × ℕ) ≠ (2, 2) := by
    intro h
    have h1 : r + 2 = 2 := congrArg Prod.fst h
    omega
  have hadm : StatedLieAdmissible .PSp (r + 2) 2 f :=
    ⟨Nat.prime_two, hf, by omega, hne⟩
  let U : Fin (r + 2) → Subgroup G :=
    Fin.lastCases (motive := fun _ => Subgroup G)
      (κ.comp (longBlock F (r + 1) (Fin.last r))).range
      (fun k => (σ.comp (blockSL2 F (r + 1) k)).range)
  have hU : ∀ k : Fin (r + 1), U (Fin.castSucc k) = (σ.comp (blockSL2 F (r + 1) k)).range :=
    fun k => Fin.lastCases_castSucc k
  have hUlast : U (Fin.last (r + 1)) = (κ.comp (longBlock F (r + 1) (Fin.last r))).range :=
    Fin.lastCases_last
  have hgens : (⨆ k, U k) = σ.range ⊔ κ.range :=
    le_antisymm (spCharts_iSup_le σ κ U hU hUlast)
      (spCharts_le_iSup σ κ hagree U hU hUlast)
  obtain ⟨Ψ, hker, hrange⟩ := spCharts_recog hadm (by omega) hF hq U
    (spCharts_comm σ κ hagree hcross U hU hUlast)
    (exists_linearBlockStandardPair_of_blockSL2_frame σ hσ U hU)
    (spCharts_sp hr σ κ hκ hagree U hU hUlast)
  exact ⟨Ψ, hker, hrange.trans hgens⟩

end CFSG.ClassicalInvolution.WeakCT

end
