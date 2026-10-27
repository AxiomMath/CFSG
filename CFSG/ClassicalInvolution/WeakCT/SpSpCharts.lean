module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
import CFSG.RankThree.PartOne.CTP.SpEven
import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCRecognition
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizePieces
public import CFSG.ClassicalInvolution.WeakCT.Defs

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock shortBlock)
open scoped MatrixGroups

theorem weakCT_symplectic_even_of_chain {n f : ℕ} (hn : 3 ≤ n) {F : Type} [Field F] [Finite F]
    [CharP F 2] (hF : Nat.card F = 2 ^ f) (hq : 4 ≤ Nat.card F) {G : Type} [Group G]
    (U : Fin n → Subgroup G)
    (hcomm : ∀ i j : Fin n, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j : Fin n, i.val + 1 = j.val → j.val + 1 < n →
      ∃ W, LinearBlockStandardPair F W (U i) (U j))
    (hsp : ∀ i j : Fin n, i.val + 1 = n → j.val + 2 = n →
      ∃ W, CFSG.ClassicalInvolution.Models.SymplecticPairs.SymplecticBlockStandardPair F W
        (U i) (U j)) :
    ∃ Ψ : StatedSp n F →* G, Ψ.ker ≤ Subgroup.center (StatedSp n F) ∧
      Ψ.range = ⨆ k, U k := by
  have hf : 1 ≤ f := by
    by_contra h
    have h0 : f = 0 := by omega
    have h1 : 2 ^ f = 1 := by rw [h0]; simp
    omega
  have hne : ((n, 2 ^ f) : ℕ × ℕ) ≠ (2, 2) := by
    intro h
    have h1 : n = 2 := congrArg Prod.fst h
    omega
  have hadm : StatedLieAdmissible .PSp n 2 f := ⟨Nat.prime_two, hf, by omega, hne⟩
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

private theorem spSpCharts_range_comp_le {X Y Z : Type} [Group X] [Group Y] [Group Z]
    (g : Y →* Z) (f : X →* Y) : (g.comp f).range ≤ g.range := by
  rw [MonoidHom.range_comp]
  exact Subgroup.map_le_range g _

private theorem spSpCharts_shortBlock_congr {K : Type} [Field K] {n : ℕ} {i i' j j' : Fin n}
    (hij : i ≠ j) (hij' : i' ≠ j') (hi : i = i') (hj : j = j') :
    shortBlock K hij = shortBlock K hij' := by
  subst hi
  subst hj
  exact congrArg (shortBlock K) (Subsingleton.elim hij hij')

private theorem spSpCharts_shift {s : ℕ} {F : Type} [Field F] {G : Type} [Group G]
    (κ₁ κ₂ : StatedSp (s + 2) F →* G)
    (hagree : ∀ k : Fin s,
      (κ₁.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.succ)).ne)).range =
        (κ₂.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.castSucc)).ne)).range)
    (i : Fin (s + 1)) (hi : 0 < i.val) :
    ∃ k : Fin s, k.val + 1 = i.val ∧
      (κ₁.comp (shortBlock F (Fin.castSucc_lt_succ (i := i)).ne)).range =
        (κ₂.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.castSucc)).ne)).range := by
  obtain ⟨k, hk⟩ : ∃ k : Fin s, k.succ = i :=
    ⟨⟨i.val - 1, by have := i.isLt; omega⟩, Fin.ext (by simp only [Fin.val_succ]; omega)⟩
  refine ⟨k, ?_, ?_⟩
  · rw [← hk, Fin.val_succ]
  · rw [← hk]
    exact hagree k

private theorem spSpCharts_comm {s : ℕ} {F : Type} [Field F] {G : Type} [Group G]
    (κ₁ κ₂ : StatedSp (s + 2) F →* G)
    (hagree : ∀ k : Fin s,
      (κ₁.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.succ)).ne)).range =
        (κ₂.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.castSucc)).ne)).range)
    (hcross₁ : ∀ a ∈ (κ₁.comp (shortBlock F
        (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne)).range,
      ∀ b ∈ (κ₂.comp (shortBlock F (Fin.castSucc_lt_succ (i := Fin.last s)).ne)).range,
        a * b = b * a)
    (hcross₂ : ∀ a ∈ (κ₁.comp (shortBlock F
        (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne)).range,
      ∀ b ∈ (κ₂.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range, a * b = b * a)
    (U : Fin (s + 3) → Subgroup G)
    (hU : ∀ k : Fin (s + 1), U k.castSucc.castSucc =
      (κ₁.comp (shortBlock F (Fin.castSucc_lt_succ (i := k)).ne)).range)
    (hU₁ : U (Fin.last (s + 1)).castSucc =
      (κ₂.comp (shortBlock F (Fin.castSucc_lt_succ (i := Fin.last s)).ne)).range)
    (hU₂ : U (Fin.last (s + 2)) = (κ₂.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range) :
    ∀ i j : Fin (s + 3), i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a := by
  intro i j hij a ha b hb
  rcases Fin.eq_castSucc_or_eq_last (n := s + 2) i with ⟨i₁, rfl⟩ | rfl
  swap
  · exact absurd hij (by have := j.isLt; simp only [Fin.val_last]; omega)
  rcases Fin.eq_castSucc_or_eq_last (n := s + 1) i₁ with ⟨i', rfl⟩ | rfl
  swap
  · exfalso
    have := j.isLt
    simp only [Fin.val_castSucc, Fin.val_last] at hij
    omega
  rw [hU i'] at ha
  rcases Fin.eq_castSucc_or_eq_last (n := s + 2) j with ⟨j₁, rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last (n := s + 1) j₁ with ⟨j', rfl⟩ | rfl
    ·
      rw [hU j'] at hb
      have hv : i'.val + 1 < j'.val := by simpa only [Fin.val_castSucc] using hij
      obtain ⟨A, rfl⟩ := MonoidHom.mem_range.mp ha
      obtain ⟨B, rfl⟩ := MonoidHom.mem_range.mp hb
      simp only [MonoidHom.comp_apply]
      rw [← map_mul, ← map_mul,
        (CFSG.ClassicalInvolution.Models.SymplecticPairs.commute_shortBlock_shortBlock
          (Fin.castSucc_lt_succ (i := i')).ne (Fin.castSucc_lt_succ (i := j')).ne
          (Fin.ne_of_val_ne (by simp only [Fin.val_castSucc]; omega))
          (Fin.ne_of_val_ne (by simp only [Fin.val_castSucc, Fin.val_succ]; omega))
          (Fin.ne_of_val_ne (by simp only [Fin.val_castSucc, Fin.val_succ]; omega))
          (Fin.ne_of_val_ne (by simp only [Fin.val_succ]; omega)) A B).eq]
    ·
      rw [hU₁] at hb
      have hv : i'.val < s := by
        simp only [Fin.val_castSucc, Fin.val_last] at hij
        omega
      rcases Nat.eq_zero_or_pos i'.val with h0 | hpos
      · have hi0 : i' = 0 := Fin.ext (by simpa using h0)
        subst hi0
        exact hcross₁ a ha b hb
      · obtain ⟨k, hk, hk'⟩ := spSpCharts_shift κ₁ κ₂ hagree i' hpos
        rw [hk'] at ha
        obtain ⟨A, rfl⟩ := MonoidHom.mem_range.mp ha
        obtain ⟨B, rfl⟩ := MonoidHom.mem_range.mp hb
        simp only [MonoidHom.comp_apply]
        rw [← map_mul, ← map_mul,
          (CFSG.ClassicalInvolution.Models.SymplecticPairs.commute_shortBlock_shortBlock
            (Fin.castSucc_lt_succ (i := k.castSucc)).ne
            (Fin.castSucc_lt_succ (i := Fin.last s)).ne
            (Fin.ne_of_val_ne (by simp only [Fin.val_castSucc, Fin.val_last]; omega))
            (Fin.ne_of_val_ne (by simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_last]; omega))
            (Fin.ne_of_val_ne (by simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_last]; omega))
            (Fin.ne_of_val_ne (by simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_last]; omega))
            A B).eq]
  ·
    rw [hU₂] at hb
    rcases Nat.eq_zero_or_pos i'.val with h0 | hpos
    · have hi0 : i' = 0 := Fin.ext (by simpa using h0)
      subst hi0
      exact hcross₂ a ha b hb
    · obtain ⟨k, hk, hk'⟩ := spSpCharts_shift κ₁ κ₂ hagree i' hpos
      rw [hk'] at ha
      obtain ⟨A, rfl⟩ := MonoidHom.mem_range.mp ha
      obtain ⟨B, rfl⟩ := MonoidHom.mem_range.mp hb
      simp only [MonoidHom.comp_apply]
      rw [← map_mul, ← map_mul,
        CFSG.ClassicalInvolution.Models.SymplecticPairs.commute_shortBlock_longBlock
          (Fin.castSucc_lt_succ (i := k.castSucc)).ne
          (Fin.ne_of_val_ne (by simp only [Fin.val_castSucc, Fin.val_last]; omega))
          (Fin.ne_of_val_ne (by simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_last]; omega))
          A B]

private theorem spSpCharts_pair {s : ℕ} (hs : 1 ≤ s) {F : Type} [Field F] {G : Type} [Group G]
    (κ₁ κ₂ : StatedSp (s + 2) F →* G) (hκ₁ : Function.Injective κ₁)
    (hκ₂ : Function.Injective κ₂)
    (hagree : ∀ k : Fin s,
      (κ₁.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.succ)).ne)).range =
        (κ₂.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.castSucc)).ne)).range)
    (U : Fin (s + 3) → Subgroup G)
    (hU : ∀ k : Fin (s + 1), U k.castSucc.castSucc =
      (κ₁.comp (shortBlock F (Fin.castSucc_lt_succ (i := k)).ne)).range)
    (hU₁ : U (Fin.last (s + 1)).castSucc =
      (κ₂.comp (shortBlock F (Fin.castSucc_lt_succ (i := Fin.last s)).ne)).range) :
    ∀ i j : Fin (s + 3), i.val + 1 = j.val → j.val + 1 < s + 3 →
      ∃ W, LinearBlockStandardPair F W (U i) (U j) := by
  intro i j hij hj
  rcases Fin.eq_castSucc_or_eq_last (n := s + 2) j with ⟨j₁, rfl⟩ | rfl
  swap
  · exact absurd hj (by simp only [Fin.val_last]; omega)
  rcases Fin.eq_castSucc_or_eq_last (n := s + 2) i with ⟨i₁, rfl⟩ | rfl
  swap
  · exfalso
    have := j₁.isLt
    simp only [Fin.val_last, Fin.val_castSucc] at hij
    omega
  rcases Fin.eq_castSucc_or_eq_last (n := s + 1) i₁ with ⟨i', rfl⟩ | rfl
  swap
  · exfalso
    have := j₁.isLt
    simp only [Fin.val_last, Fin.val_castSucc] at hij
    omega
  have hker₁ : κ₁.ker ≤ Subgroup.center (StatedSp (s + 2) F) := by
    rw [(MonoidHom.ker_eq_bot_iff κ₁).mpr hκ₁]
    exact bot_le
  have hker₂ : κ₂.ker ≤ Subgroup.center (StatedSp (s + 2) F) := by
    rw [(MonoidHom.ker_eq_bot_iff κ₂).mpr hκ₂]
    exact bot_le
  rcases Fin.eq_castSucc_or_eq_last (n := s + 1) j₁ with ⟨j', rfl⟩ | rfl
  ·
    have hv : i'.val + 1 = j'.val := by simpa only [Fin.val_castSucc] using hij
    have hL := CFSG.ClassicalInvolution.Models.SymplecticPairs.isLeviPair_shortBlock (K := F)
      (Fin.castSucc_lt_succ (i := i')).ne
      (Fin.ne_of_val_ne (by simp only [Fin.val_succ]; omega) : i'.succ ≠ j'.succ)
      (Fin.ne_of_val_ne (by simp only [Fin.val_castSucc, Fin.val_succ]; omega) :
        i'.castSucc ≠ j'.succ)
    obtain ⟨W, hW⟩ := hL.exists_linearBlockStandardPair_map κ₁ hker₁
    refine ⟨W, ?_⟩
    rw [MonoidHom.map_range, MonoidHom.map_range] at hW
    rw [hU i', hU j',
      spSpCharts_shortBlock_congr (Fin.castSucc_lt_succ (i := j')).ne
        (Fin.ne_of_val_ne (by simp only [Fin.val_succ]; omega) : i'.succ ≠ j'.succ)
        (Fin.ext (by simp only [Fin.val_castSucc, Fin.val_succ]; omega)) rfl]
    exact hW
  ·
    have hv : i'.val = s := by
      simp only [Fin.val_castSucc, Fin.val_last] at hij
      omega
    obtain ⟨k, hk, hk'⟩ := spSpCharts_shift κ₁ κ₂ hagree i' (by omega)
    have hL := CFSG.ClassicalInvolution.Models.SymplecticPairs.isLeviPair_shortBlock (K := F)
      (Fin.castSucc_lt_succ (i := k.castSucc)).ne
      (Fin.ne_of_val_ne (by simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_last]; omega) :
        k.castSucc.succ ≠ (Fin.last s).succ)
      (Fin.ne_of_val_ne (by simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_last]; omega) :
        k.castSucc.castSucc ≠ (Fin.last s).succ)
    obtain ⟨W, hW⟩ := hL.exists_linearBlockStandardPair_map κ₂ hker₂
    refine ⟨W, ?_⟩
    rw [MonoidHom.map_range, MonoidHom.map_range] at hW
    rw [hU i', hk', hU₁,
      spSpCharts_shortBlock_congr (Fin.castSucc_lt_succ (i := Fin.last s)).ne
        (Fin.ne_of_val_ne (by simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_last]; omega) :
          k.castSucc.succ ≠ (Fin.last s).succ)
        (Fin.ext (by simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_last]; omega)) rfl]
    exact hW

private theorem spSpCharts_sp {s : ℕ} {F : Type} [Field F] {G : Type} [Group G]
    (κ₂ : StatedSp (s + 2) F →* G) (hκ₂ : Function.Injective κ₂)
    (U : Fin (s + 3) → Subgroup G)
    (hU₁ : U (Fin.last (s + 1)).castSucc =
      (κ₂.comp (shortBlock F (Fin.castSucc_lt_succ (i := Fin.last s)).ne)).range)
    (hU₂ : U (Fin.last (s + 2)) = (κ₂.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range) :
    ∀ i j : Fin (s + 3), i.val + 1 = s + 3 → j.val + 2 = s + 3 →
      ∃ W, CFSG.ClassicalInvolution.Models.SymplecticPairs.SymplecticBlockStandardPair F W
        (U i) (U j) := by
  intro i j hi hj
  have hiL : i = Fin.last (s + 2) := Fin.ext (by simp only [Fin.val_last]; omega)
  have hjL : j = (Fin.last (s + 1)).castSucc :=
    Fin.ext (by simp only [Fin.val_castSucc, Fin.val_last]; omega)
  rw [hiL, hjL, hU₂, hU₁]
  have hW :=
    CFSG.ClassicalInvolution.Models.SymplecticPairs.symplecticBlockStandardPair_longShort
      (K := F) (n := s + 2) (Fin.castSucc_lt_succ (i := Fin.last s)).ne
  have hmap :=
    CFSG.ClassicalInvolution.Models.SymplecticPairs.symplecticBlockStandardPair_map hW κ₂ hκ₂
  rw [MonoidHom.map_range, MonoidHom.map_range] at hmap
  exact ⟨_, hmap⟩

private theorem spSpCharts_iSup_le {s : ℕ} {F : Type} [Field F] {G : Type} [Group G]
    (κ₁ κ₂ : StatedSp (s + 2) F →* G) (U : Fin (s + 3) → Subgroup G)
    (hU : ∀ k : Fin (s + 1), U k.castSucc.castSucc =
      (κ₁.comp (shortBlock F (Fin.castSucc_lt_succ (i := k)).ne)).range)
    (hU₁ : U (Fin.last (s + 1)).castSucc =
      (κ₂.comp (shortBlock F (Fin.castSucc_lt_succ (i := Fin.last s)).ne)).range)
    (hU₂ : U (Fin.last (s + 2)) = (κ₂.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range) :
    (⨆ k, U k) ≤ κ₁.range ⊔ κ₂.range := by
  refine iSup_le fun k => ?_
  rcases Fin.eq_castSucc_or_eq_last (n := s + 2) k with ⟨k₁, rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last (n := s + 1) k₁ with ⟨k', rfl⟩ | rfl
    · rw [hU k']
      exact (spSpCharts_range_comp_le _ _).trans le_sup_left
    · rw [hU₁]
      exact (spSpCharts_range_comp_le _ _).trans le_sup_right
  · rw [hU₂]
    exact (spSpCharts_range_comp_le _ _).trans le_sup_right

private theorem spSpCharts_range_le {s : ℕ} {F : Type} [Field F] {G : Type} [Group G]
    (κ : StatedSp (s + 2) F →* G) (H : Subgroup G)
    (hshort : ∀ k : Fin (s + 1),
      (κ.comp (shortBlock F (Fin.castSucc_lt_succ (i := k)).ne)).range ≤ H)
    (hlong : (κ.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range ≤ H) :
    κ.range ≤ H := by
  rw [MonoidHom.range_eq_map,
    ← CFSG.SeitzReduction.SymplecticPilot.iSup_simpleRootSL2_eq_top (F := F) (n := s + 2)
      (by omega), Subgroup.map_iSup]
  refine iSup_le fun k => ?_
  by_cases hk : k.val + 1 < s + 2
  · have hk' : k.val < s + 1 := by omega
    have hsb : shortBlock F (CFSG.LieType.Universal.Symplectic.SpExtras.ne_succ' hk) =
        shortBlock F (Fin.castSucc_lt_succ (i := (⟨k.val, hk'⟩ : Fin (s + 1)))).ne :=
      spSpCharts_shortBlock_congr _ _ (Fin.ext rfl) (Fin.ext rfl)
    rw [CFSG.SeitzReduction.SymplecticPilot.simpleRootSL2_of_lt hk, hsb, MonoidHom.map_range]
    exact hshort ⟨k.val, hk'⟩
  · have hkl : k = Fin.last (s + 1) := Fin.ext (by have := k.isLt; simp only [Fin.val_last]; omega)
    have hlong' : CFSG.SeitzReduction.SymplecticPilot.simpleRootSL2 F k =
        (longBlock F (s + 2) k).range := by
      rw [CFSG.SeitzReduction.SymplecticPilot.simpleRootSL2_of_not_lt hk]
      rfl
    rw [hlong', MonoidHom.map_range, hkl]
    exact hlong

private theorem spSpCharts_le_iSup {s : ℕ} {F : Type} [Field F] {G : Type} [Group G]
    (κ₁ κ₂ : StatedSp (s + 2) F →* G)
    (hagree : ∀ k : Fin s,
      (κ₁.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.succ)).ne)).range =
        (κ₂.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.castSucc)).ne)).range)
    (hlong : (κ₁.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range =
      (κ₂.comp (longBlock F (s + 2) (Fin.last s).castSucc)).range)
    (U : Fin (s + 3) → Subgroup G)
    (hU : ∀ k : Fin (s + 1), U k.castSucc.castSucc =
      (κ₁.comp (shortBlock F (Fin.castSucc_lt_succ (i := k)).ne)).range)
    (hU₁ : U (Fin.last (s + 1)).castSucc =
      (κ₂.comp (shortBlock F (Fin.castSucc_lt_succ (i := Fin.last s)).ne)).range)
    (hU₂ : U (Fin.last (s + 2)) = (κ₂.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range) :
    κ₁.range ⊔ κ₂.range ≤ ⨆ k, U k := by
  have h₂ : κ₂.range ≤ ⨆ k, U k := by
    refine spSpCharts_range_le κ₂ _ (fun k => ?_) ?_
    · rcases Fin.eq_castSucc_or_eq_last (n := s) k with ⟨k', rfl⟩ | rfl
      · rw [← hagree k', ← hU k'.succ]
        exact le_iSup U _
      · rw [← hU₁]
        exact le_iSup U _
    · rw [← hU₂]
      exact le_iSup U _
  refine sup_le (spSpCharts_range_le κ₁ _ (fun k => ?_) ?_) h₂
  · rw [← hU k]
    exact le_iSup U _
  · rw [hlong]
    exact (spSpCharts_range_comp_le _ _).trans h₂

theorem exists_chain_of_spSpCharts {s : ℕ} (hs : 1 ≤ s) {F : Type} [Field F] {G : Type}
    [Group G] (κ₁ κ₂ : StatedSp (s + 2) F →* G) (hκ₁ : Function.Injective κ₁)
    (hκ₂ : Function.Injective κ₂)
    (hagree : ∀ k : Fin s,
      (κ₁.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.succ)).ne)).range =
        (κ₂.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.castSucc)).ne)).range)
    (hlong : (κ₁.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range =
      (κ₂.comp (longBlock F (s + 2) (Fin.last s).castSucc)).range)
    (hcross₁ : ∀ a ∈ (κ₁.comp (shortBlock F
        (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne)).range,
      ∀ b ∈ (κ₂.comp (shortBlock F (Fin.castSucc_lt_succ (i := Fin.last s)).ne)).range,
        a * b = b * a)
    (hcross₂ : ∀ a ∈ (κ₁.comp (shortBlock F
        (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne)).range,
      ∀ b ∈ (κ₂.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range, a * b = b * a) :
    ∃ U : Fin (s + 3) → Subgroup G,
      (∀ i j : Fin (s + 3), i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a) ∧
      (∀ i j : Fin (s + 3), i.val + 1 = j.val → j.val + 1 < s + 3 →
        ∃ W, LinearBlockStandardPair F W (U i) (U j)) ∧
      (∀ i j : Fin (s + 3), i.val + 1 = s + 3 → j.val + 2 = s + 3 →
        ∃ W, CFSG.ClassicalInvolution.Models.SymplecticPairs.SymplecticBlockStandardPair F W
          (U i) (U j)) ∧
      (⨆ k, U k) = κ₁.range ⊔ κ₂.range := by
  let U : Fin (s + 3) → Subgroup G :=
    Fin.lastCases (motive := fun _ => Subgroup G)
      (κ₂.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range
      (Fin.lastCases (motive := fun _ => Subgroup G)
        (κ₂.comp (shortBlock F (Fin.castSucc_lt_succ (i := Fin.last s)).ne)).range
        (fun k => (κ₁.comp (shortBlock F (Fin.castSucc_lt_succ (i := k)).ne)).range))
  have hU : ∀ k : Fin (s + 1), U k.castSucc.castSucc =
      (κ₁.comp (shortBlock F (Fin.castSucc_lt_succ (i := k)).ne)).range := fun k => by
    simp only [U, Fin.lastCases_castSucc]
  have hU₁ : U (Fin.last (s + 1)).castSucc =
      (κ₂.comp (shortBlock F (Fin.castSucc_lt_succ (i := Fin.last s)).ne)).range := by
    simp only [U, Fin.lastCases_castSucc, Fin.lastCases_last]
  have hU₂ : U (Fin.last (s + 2)) =
      (κ₂.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range := by
    simp only [U, Fin.lastCases_last]
  exact ⟨U, spSpCharts_comm κ₁ κ₂ hagree hcross₁ hcross₂ U hU hU₁ hU₂,
    spSpCharts_pair hs κ₁ κ₂ hκ₁ hκ₂ hagree U hU hU₁, spSpCharts_sp κ₂ hκ₂ U hU₁ hU₂,
    le_antisymm (spSpCharts_iSup_le κ₁ κ₂ U hU hU₁ hU₂)
      (spSpCharts_le_iSup κ₁ κ₂ hagree hlong U hU hU₁ hU₂)⟩

theorem weakCT_symplectic_even_of_spSpCharts {s f : ℕ} (hs : 1 ≤ s) {F : Type} [Field F]
    [Finite F] [CharP F 2] (hF : Nat.card F = 2 ^ f) (hq : 4 ≤ Nat.card F) {G : Type} [Group G]
    (κ₁ κ₂ : StatedSp (s + 2) F →* G) (hκ₁ : Function.Injective κ₁)
    (hκ₂ : Function.Injective κ₂)
    (hagree : ∀ k : Fin s,
      (κ₁.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.succ)).ne)).range =
        (κ₂.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.castSucc)).ne)).range)
    (hlong : (κ₁.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range =
      (κ₂.comp (longBlock F (s + 2) (Fin.last s).castSucc)).range)
    (hcross₁ : ∀ a ∈ (κ₁.comp (shortBlock F
        (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne)).range,
      ∀ b ∈ (κ₂.comp (shortBlock F (Fin.castSucc_lt_succ (i := Fin.last s)).ne)).range,
        a * b = b * a)
    (hcross₂ : ∀ a ∈ (κ₁.comp (shortBlock F
        (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne)).range,
      ∀ b ∈ (κ₂.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range, a * b = b * a) :
    ∃ Ψ : StatedSp (s + 3) F →* G, Ψ.ker ≤ Subgroup.center (StatedSp (s + 3) F) ∧
      Ψ.range = κ₁.range ⊔ κ₂.range := by
  obtain ⟨U, hcomm, hpair, hsp, hgens⟩ :=
    exists_chain_of_spSpCharts hs κ₁ κ₂ hκ₁ hκ₂ hagree hlong hcross₁ hcross₂
  obtain ⟨Ψ, hker, hrange⟩ := weakCT_symplectic_even_of_chain (by omega) hF hq U hcomm hpair hsp
  exact ⟨Ψ, hker, hrange.trans hgens⟩

private theorem spSpCharts_comm_shortBlock {s : ℕ} {F : Type} [Field F] {G : Type} [Group G]
    (κ : StatedSp (s + 2) F →* G) {i j : Fin (s + 1)} (hij : i.val + 1 < j.val) :
    ∀ a ∈ (κ.comp (shortBlock F (Fin.castSucc_lt_succ (i := i)).ne)).range,
      ∀ b ∈ (κ.comp (shortBlock F (Fin.castSucc_lt_succ (i := j)).ne)).range,
        a * b = b * a := by
  intro a ha b hb
  obtain ⟨A, rfl⟩ := MonoidHom.mem_range.mp ha
  obtain ⟨B, rfl⟩ := MonoidHom.mem_range.mp hb
  simp only [MonoidHom.comp_apply]
  rw [← map_mul, ← map_mul,
    (CFSG.ClassicalInvolution.Models.SymplecticPairs.commute_shortBlock_shortBlock
      (Fin.castSucc_lt_succ (i := i)).ne (Fin.castSucc_lt_succ (i := j)).ne
      (Fin.ne_of_val_ne (by simp only [Fin.val_castSucc]; omega))
      (Fin.ne_of_val_ne (by simp only [Fin.val_castSucc, Fin.val_succ]; omega))
      (Fin.ne_of_val_ne (by simp only [Fin.val_castSucc, Fin.val_succ]; omega))
      (Fin.ne_of_val_ne (by simp only [Fin.val_succ]; omega)) A B).eq]

private theorem spSpCharts_comm_shortBlock_longBlock {s : ℕ} {F : Type} [Field F] {G : Type}
    [Group G] (κ : StatedSp (s + 2) F →* G) {i : Fin (s + 1)} (hi : i.val + 1 < s + 1) :
    ∀ a ∈ (κ.comp (shortBlock F (Fin.castSucc_lt_succ (i := i)).ne)).range,
      ∀ b ∈ (κ.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range, a * b = b * a := by
  intro a ha b hb
  obtain ⟨A, rfl⟩ := MonoidHom.mem_range.mp ha
  obtain ⟨B, rfl⟩ := MonoidHom.mem_range.mp hb
  simp only [MonoidHom.comp_apply]
  rw [← map_mul, ← map_mul,
    CFSG.ClassicalInvolution.Models.SymplecticPairs.commute_shortBlock_longBlock
      (Fin.castSucc_lt_succ (i := i)).ne
      (Fin.ne_of_val_ne (by simp only [Fin.val_castSucc, Fin.val_last]; omega))
      (Fin.ne_of_val_ne (by simp only [Fin.val_succ, Fin.val_last]; omega))
      A B]

private theorem spSpCharts_shift₂ {s : ℕ} {F : Type} [Field F] {G : Type} [Group G]
    (κ₁ κ₂ κ₃ : StatedSp (s + 2) F →* G)
    (hagree₁₂ : ∀ k : Fin s,
      (κ₁.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.succ)).ne)).range =
        (κ₂.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.castSucc)).ne)).range)
    (hagree₂₃ : ∀ k : Fin s,
      (κ₂.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.succ)).ne)).range =
        (κ₃.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.castSucc)).ne)).range)
    (i : Fin (s + 1)) (hi : 1 < i.val) :
    ∃ k : Fin s, k.val + 2 = i.val ∧
      (κ₁.comp (shortBlock F (Fin.castSucc_lt_succ (i := i)).ne)).range =
        (κ₃.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.castSucc)).ne)).range := by
  obtain ⟨k, hk, hkr⟩ := spSpCharts_shift κ₁ κ₂ hagree₁₂ i (by omega)
  obtain ⟨m, hm, hmr⟩ := spSpCharts_shift κ₂ κ₃ hagree₂₃ k.castSucc
    (by simp only [Fin.val_castSucc]; omega)
  refine ⟨m, ?_, ?_⟩
  · simp only [Fin.val_castSucc] at hm
    omega
  · rw [hkr, hmr]

private theorem spSpCharts_pair_shortBlock {s : ℕ} {F : Type} [Field F] {G : Type} [Group G]
    (κ : StatedSp (s + 2) F →* G) (hκ : Function.Injective κ) (a c : Fin (s + 1))
    (hac : a.val + 1 = c.val) :
    ∃ W, LinearBlockStandardPair F W
      ((κ.comp (shortBlock F (Fin.castSucc_lt_succ (i := a)).ne)).range)
      ((κ.comp (shortBlock F (Fin.castSucc_lt_succ (i := c)).ne)).range) := by
  have hker : κ.ker ≤ Subgroup.center (StatedSp (s + 2) F) := by
    rw [(MonoidHom.ker_eq_bot_iff κ).mpr hκ]
    exact bot_le
  have h1 : a.castSucc ≠ c.castSucc :=
    Fin.ne_of_val_ne (by simp only [Fin.val_castSucc]; omega)
  have h3 : a.castSucc ≠ c.succ :=
    Fin.ne_of_val_ne (by simp only [Fin.val_castSucc, Fin.val_succ]; omega)
  obtain ⟨W, hW⟩ :=
    (CFSG.ClassicalInvolution.Models.SymplecticPairs.isLeviPair_shortBlock h1
      (Fin.castSucc_lt_succ (i := c)).ne h3).exists_linearBlockStandardPair_map κ hker
  rw [MonoidHom.map_range, MonoidHom.map_range] at hW
  refine ⟨W, ?_⟩
  rw [spSpCharts_shortBlock_congr h1 (Fin.castSucc_lt_succ (i := a)).ne rfl
    (Fin.ext (by simp only [Fin.val_castSucc, Fin.val_succ]; omega))] at hW
  exact hW

private theorem threeCharts_comm_short {s : ℕ} (hs : 1 ≤ s) {F : Type} [Field F] {G : Type}
    [Group G] (κ₁ κ₂ κ₃ : StatedSp (s + 2) F →* G)
    (hagree₁₂ : ∀ k : Fin s,
      (κ₁.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.succ)).ne)).range =
        (κ₂.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.castSucc)).ne)).range)
    (hagree₂₃ : ∀ k : Fin s,
      (κ₂.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.succ)).ne)).range =
        (κ₃.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.castSucc)).ne)).range)
    (hcross₁₂ : ∀ a ∈ (κ₁.comp (shortBlock F
        (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne)).range,
      ∀ b ∈ (κ₂.comp (shortBlock F (Fin.castSucc_lt_succ (i := Fin.last s)).ne)).range,
        a * b = b * a)
    (hcross₁₃ₛ : ∀ a ∈ (κ₁.comp (shortBlock F
        (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne)).range,
      ∀ b ∈ (κ₃.comp (shortBlock F (Fin.castSucc_lt_succ (i := Fin.last s)).ne)).range,
        a * b = b * a)
    (hcross₁₃ₗ : ∀ a ∈ (κ₁.comp (shortBlock F
        (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne)).range,
      ∀ b ∈ (κ₃.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range, a * b = b * a)
    (hcross₂₃ₛ : ∀ a ∈ (κ₂.comp (shortBlock F
        (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne)).range,
      ∀ b ∈ (κ₃.comp (shortBlock F (Fin.castSucc_lt_succ (i := Fin.last s)).ne)).range,
        a * b = b * a)
    (hcross₂₃ₗ : ∀ a ∈ (κ₂.comp (shortBlock F
        (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne)).range,
      ∀ b ∈ (κ₃.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range, a * b = b * a)
    (U : Fin (s + 4) → Subgroup G)
    (hU : ∀ k : Fin (s + 1), U k.castSucc.castSucc.castSucc =
      (κ₁.comp (shortBlock F (Fin.castSucc_lt_succ (i := k)).ne)).range)
    (hU₁ : U (Fin.last (s + 1)).castSucc.castSucc =
      (κ₂.comp (shortBlock F (Fin.castSucc_lt_succ (i := Fin.last s)).ne)).range)
    (hU₂ : U (Fin.last (s + 2)).castSucc =
      (κ₃.comp (shortBlock F (Fin.castSucc_lt_succ (i := Fin.last s)).ne)).range)
    (hU₃ : U (Fin.last (s + 3)) =
      (κ₃.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range)
    (i₃ : Fin (s + 1)) :
    ∀ j : Fin (s + 4), i₃.val + 1 < j.val →
      ∀ a ∈ U i₃.castSucc.castSucc.castSucc, ∀ b ∈ U j, a * b = b * a := by
  intro j hij a ha b hb
  rw [hU i₃] at ha
  rcases Fin.eq_castSucc_or_eq_last (n := s + 3) j with ⟨j₁, rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last (n := s + 2) j₁ with ⟨j₂, rfl⟩ | rfl
    · rcases Fin.eq_castSucc_or_eq_last (n := s + 1) j₂ with ⟨j₃, rfl⟩ | rfl
      · rw [hU j₃] at hb
        exact spSpCharts_comm_shortBlock κ₁ (by simpa only [Fin.val_castSucc] using hij)
          a ha b hb
      · rw [hU₁] at hb
        have hv : i₃.val + 1 < s + 1 := by
          simp only [Fin.val_castSucc, Fin.val_last] at hij
          omega
        rcases Nat.eq_zero_or_pos i₃.val with h0 | hpos
        · have hi0 : i₃ = 0 := Fin.ext (by simpa using h0)
          subst hi0
          exact hcross₁₂ a ha b hb
        · obtain ⟨k, hk, hkr⟩ := spSpCharts_shift κ₁ κ₂ hagree₁₂ i₃ hpos
          rw [hkr] at ha
          exact spSpCharts_comm_shortBlock κ₂ (i := k.castSucc) (j := Fin.last s)
            (by simp only [Fin.val_castSucc, Fin.val_last]; omega) a ha b hb
    · rw [hU₂] at hb
      have hv : i₃.val + 1 < s + 2 := by
        simp only [Fin.val_castSucc, Fin.val_last] at hij
        omega
      rcases Nat.lt_or_ge i₃.val 2 with hlt | hge
      · have hi01 : i₃.val = 0 ∨ i₃.val = 1 := by omega
        rcases hi01 with h0 | h1
        · have hi0 : i₃ = 0 := Fin.ext (by simpa using h0)
          subst hi0
          exact hcross₁₃ₛ a ha b hb
        · have hi1 : i₃ = (⟨0, by omega⟩ : Fin s).succ := Fin.ext (by
            simp only [Fin.val_succ]; omega)
          rw [hi1, hagree₁₂ ⟨0, by omega⟩] at ha
          exact hcross₂₃ₛ a ha b hb
      · obtain ⟨k, hk, hkr⟩ := spSpCharts_shift₂ κ₁ κ₂ κ₃ hagree₁₂ hagree₂₃ i₃ (by omega)
        rw [hkr] at ha
        exact spSpCharts_comm_shortBlock κ₃ (i := k.castSucc) (j := Fin.last s)
          (by simp only [Fin.val_castSucc, Fin.val_last]; omega) a ha b hb
  · rw [hU₃] at hb
    have hv : i₃.val + 1 < s + 3 := by
      simp only [Fin.val_last] at hij
      omega
    rcases Nat.lt_or_ge i₃.val 2 with hlt | hge
    · have hi01 : i₃.val = 0 ∨ i₃.val = 1 := by omega
      rcases hi01 with h0 | h1
      · have hi0 : i₃ = 0 := Fin.ext (by simpa using h0)
        subst hi0
        exact hcross₁₃ₗ a ha b hb
      · have hi1 : i₃ = (⟨0, by omega⟩ : Fin s).succ := Fin.ext (by
          simp only [Fin.val_succ]; omega)
        rw [hi1, hagree₁₂ ⟨0, by omega⟩] at ha
        exact hcross₂₃ₗ a ha b hb
    · obtain ⟨k, hk, hkr⟩ := spSpCharts_shift₂ κ₁ κ₂ κ₃ hagree₁₂ hagree₂₃ i₃ (by omega)
      rw [hkr] at ha
      exact spSpCharts_comm_shortBlock_longBlock κ₃ (i := k.castSucc)
        (by simp only [Fin.val_castSucc]; omega) a ha b hb

private theorem threeCharts_comm_mid {s : ℕ} (hs : 1 ≤ s) {F : Type} [Field F] {G : Type}
    [Group G] (κ₂ κ₃ : StatedSp (s + 2) F →* G)
    (hagree₂₃ : ∀ k : Fin s,
      (κ₂.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.succ)).ne)).range =
        (κ₃.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.castSucc)).ne)).range)
    (U : Fin (s + 4) → Subgroup G)
    (hU₁ : U (Fin.last (s + 1)).castSucc.castSucc =
      (κ₂.comp (shortBlock F (Fin.castSucc_lt_succ (i := Fin.last s)).ne)).range)
    (hU₃ : U (Fin.last (s + 3)) =
      (κ₃.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range) :
    ∀ j : Fin (s + 4), (Fin.last (s + 1)).val + 1 < j.val →
      ∀ a ∈ U (Fin.last (s + 1)).castSucc.castSucc, ∀ b ∈ U j, a * b = b * a := by
  intro j hij a ha b hb
  have hj : j = Fin.last (s + 3) := by
    apply Fin.ext
    have := j.isLt
    simp only [Fin.val_last] at hij ⊢
    omega
  subst hj
  rw [hU₁] at ha
  rw [hU₃] at hb
  obtain ⟨k, hk, hkr⟩ := spSpCharts_shift κ₂ κ₃ hagree₂₃ (Fin.last s)
    (by simp only [Fin.val_last]; omega)
  rw [hkr] at ha
  exact spSpCharts_comm_shortBlock_longBlock κ₃ (i := k.castSucc)
    (by simp only [Fin.val_castSucc]; omega) a ha b hb

private theorem threeCharts_comm {s : ℕ} (hs : 1 ≤ s) {F : Type} [Field F] {G : Type}
    [Group G] (κ₁ κ₂ κ₃ : StatedSp (s + 2) F →* G)
    (hagree₁₂ : ∀ k : Fin s,
      (κ₁.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.succ)).ne)).range =
        (κ₂.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.castSucc)).ne)).range)
    (hagree₂₃ : ∀ k : Fin s,
      (κ₂.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.succ)).ne)).range =
        (κ₃.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.castSucc)).ne)).range)
    (hcross₁₂ : ∀ a ∈ (κ₁.comp (shortBlock F
        (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne)).range,
      ∀ b ∈ (κ₂.comp (shortBlock F (Fin.castSucc_lt_succ (i := Fin.last s)).ne)).range,
        a * b = b * a)
    (hcross₁₃ₛ : ∀ a ∈ (κ₁.comp (shortBlock F
        (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne)).range,
      ∀ b ∈ (κ₃.comp (shortBlock F (Fin.castSucc_lt_succ (i := Fin.last s)).ne)).range,
        a * b = b * a)
    (hcross₁₃ₗ : ∀ a ∈ (κ₁.comp (shortBlock F
        (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne)).range,
      ∀ b ∈ (κ₃.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range, a * b = b * a)
    (hcross₂₃ₛ : ∀ a ∈ (κ₂.comp (shortBlock F
        (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne)).range,
      ∀ b ∈ (κ₃.comp (shortBlock F (Fin.castSucc_lt_succ (i := Fin.last s)).ne)).range,
        a * b = b * a)
    (hcross₂₃ₗ : ∀ a ∈ (κ₂.comp (shortBlock F
        (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne)).range,
      ∀ b ∈ (κ₃.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range, a * b = b * a)
    (U : Fin (s + 4) → Subgroup G)
    (hU : ∀ k : Fin (s + 1), U k.castSucc.castSucc.castSucc =
      (κ₁.comp (shortBlock F (Fin.castSucc_lt_succ (i := k)).ne)).range)
    (hU₁ : U (Fin.last (s + 1)).castSucc.castSucc =
      (κ₂.comp (shortBlock F (Fin.castSucc_lt_succ (i := Fin.last s)).ne)).range)
    (hU₂ : U (Fin.last (s + 2)).castSucc =
      (κ₃.comp (shortBlock F (Fin.castSucc_lt_succ (i := Fin.last s)).ne)).range)
    (hU₃ : U (Fin.last (s + 3)) =
      (κ₃.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range) :
    ∀ i j : Fin (s + 4), i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a := by
  intro i j hij a ha b hb
  rcases Fin.eq_castSucc_or_eq_last (n := s + 3) i with ⟨i₁, rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last (n := s + 2) i₁ with ⟨i₂, rfl⟩ | rfl
    · rcases Fin.eq_castSucc_or_eq_last (n := s + 1) i₂ with ⟨i₃, rfl⟩ | rfl
      · exact threeCharts_comm_short hs κ₁ κ₂ κ₃ hagree₁₂ hagree₂₃ hcross₁₂ hcross₁₃ₛ
          hcross₁₃ₗ hcross₂₃ₛ hcross₂₃ₗ U hU hU₁ hU₂ hU₃ i₃ j
          (by simpa only [Fin.val_castSucc] using hij) a ha b hb
      · exact threeCharts_comm_mid hs κ₂ κ₃ hagree₂₃ U hU₁ hU₃ j
          (by simpa only [Fin.val_castSucc] using hij) a ha b hb
    · exfalso
      have := j.isLt
      simp only [Fin.val_castSucc, Fin.val_last] at hij
      omega
  · exfalso
    have := j.isLt
    simp only [Fin.val_last] at hij
    omega
private theorem threeCharts_pair {s : ℕ} (hs : 1 ≤ s) {F : Type} [Field F] {G : Type} [Group G]
    (κ₁ κ₂ κ₃ : StatedSp (s + 2) F →* G) (hκ₁ : Function.Injective κ₁)
    (hκ₂ : Function.Injective κ₂) (hκ₃ : Function.Injective κ₃)
    (hagree₁₂ : ∀ k : Fin s,
      (κ₁.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.succ)).ne)).range =
        (κ₂.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.castSucc)).ne)).range)
    (hagree₂₃ : ∀ k : Fin s,
      (κ₂.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.succ)).ne)).range =
        (κ₃.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.castSucc)).ne)).range)
    (U : Fin (s + 4) → Subgroup G)
    (hU : ∀ k : Fin (s + 1), U k.castSucc.castSucc.castSucc =
      (κ₁.comp (shortBlock F (Fin.castSucc_lt_succ (i := k)).ne)).range)
    (hU₁ : U (Fin.last (s + 1)).castSucc.castSucc =
      (κ₂.comp (shortBlock F (Fin.castSucc_lt_succ (i := Fin.last s)).ne)).range)
    (hU₂ : U (Fin.last (s + 2)).castSucc =
      (κ₃.comp (shortBlock F (Fin.castSucc_lt_succ (i := Fin.last s)).ne)).range) :
    ∀ i j : Fin (s + 4), i.val + 1 = j.val → j.val + 1 < s + 4 →
      ∃ W, LinearBlockStandardPair F W (U i) (U j) := by
  intro i j hij hj
  rcases Fin.eq_castSucc_or_eq_last (n := s + 3) i with ⟨i₁, rfl⟩ | rfl
  swap
  · exfalso
    have := j.isLt
    simp only [Fin.val_last] at hij
    omega
  rcases Fin.eq_castSucc_or_eq_last (n := s + 2) i₁ with ⟨i₂, rfl⟩ | rfl
  swap
  · exfalso
    have := j.isLt
    simp only [Fin.val_castSucc, Fin.val_last] at hij
    omega
  rcases Fin.eq_castSucc_or_eq_last (n := s + 1) i₂ with ⟨i₃, rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last (n := s) i₃ with ⟨i₄, rfl⟩ | rfl
    ·
      have hj' : j = (i₄.succ).castSucc.castSucc.castSucc := by
        apply Fin.ext
        simp only [Fin.val_castSucc, Fin.val_succ] at hij ⊢
        omega
      rw [hj', hU i₄.castSucc, hU i₄.succ]
      exact spSpCharts_pair_shortBlock κ₁ hκ₁ i₄.castSucc i₄.succ rfl
    ·
      have hj' : j = (Fin.last (s + 1)).castSucc.castSucc := by
        apply Fin.ext
        simp only [Fin.val_last, Fin.val_castSucc] at hij ⊢
        omega
      rw [hj', hU (Fin.last s), hU₁]
      obtain ⟨m, hm, hmr⟩ := spSpCharts_shift κ₁ κ₂ hagree₁₂ (Fin.last s)
        (by simp only [Fin.val_last]; omega)
      rw [hmr]
      exact spSpCharts_pair_shortBlock κ₂ hκ₂ m.castSucc (Fin.last s) hm
  ·
    have hj' : j = (Fin.last (s + 2)).castSucc := by
      apply Fin.ext
      simp only [Fin.val_last, Fin.val_castSucc] at hij ⊢
      omega
    rw [hj', hU₁, hU₂]
    obtain ⟨m, hm, hmr⟩ := spSpCharts_shift κ₂ κ₃ hagree₂₃ (Fin.last s)
      (by simp only [Fin.val_last]; omega)
    rw [hmr]
    exact spSpCharts_pair_shortBlock κ₃ hκ₃ m.castSucc (Fin.last s) hm

private theorem threeCharts_sp {s : ℕ} {F : Type} [Field F] {G : Type} [Group G]
    (κ₃ : StatedSp (s + 2) F →* G) (hκ₃ : Function.Injective κ₃)
    (U : Fin (s + 4) → Subgroup G)
    (hU₂ : U (Fin.last (s + 2)).castSucc =
      (κ₃.comp (shortBlock F (Fin.castSucc_lt_succ (i := Fin.last s)).ne)).range)
    (hU₃ : U (Fin.last (s + 3)) =
      (κ₃.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range) :
    ∀ i j : Fin (s + 4), i.val + 1 = s + 4 → j.val + 2 = s + 4 →
      ∃ W, CFSG.ClassicalInvolution.Models.SymplecticPairs.SymplecticBlockStandardPair F W
        (U i) (U j) := by
  intro i j hi hj
  have hiL : i = Fin.last (s + 3) := Fin.ext (by simp only [Fin.val_last]; omega)
  have hjL : j = (Fin.last (s + 2)).castSucc :=
    Fin.ext (by simp only [Fin.val_castSucc, Fin.val_last]; omega)
  rw [hiL, hjL, hU₃, hU₂]
  have hW :=
    CFSG.ClassicalInvolution.Models.SymplecticPairs.symplecticBlockStandardPair_longShort
      (K := F) (n := s + 2) (Fin.castSucc_lt_succ (i := Fin.last s)).ne
  have hmap :=
    CFSG.ClassicalInvolution.Models.SymplecticPairs.symplecticBlockStandardPair_map hW κ₃ hκ₃
  rw [MonoidHom.map_range, MonoidHom.map_range] at hmap
  exact ⟨_, hmap⟩

private theorem threeCharts_iSup_le {s : ℕ} {F : Type} [Field F] {G : Type} [Group G]
    (κ₁ κ₂ κ₃ : StatedSp (s + 2) F →* G) (U : Fin (s + 4) → Subgroup G)
    (hU : ∀ k : Fin (s + 1), U k.castSucc.castSucc.castSucc =
      (κ₁.comp (shortBlock F (Fin.castSucc_lt_succ (i := k)).ne)).range)
    (hU₁ : U (Fin.last (s + 1)).castSucc.castSucc =
      (κ₂.comp (shortBlock F (Fin.castSucc_lt_succ (i := Fin.last s)).ne)).range)
    (hU₂ : U (Fin.last (s + 2)).castSucc =
      (κ₃.comp (shortBlock F (Fin.castSucc_lt_succ (i := Fin.last s)).ne)).range)
    (hU₃ : U (Fin.last (s + 3)) =
      (κ₃.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range) :
    (⨆ k, U k) ≤ κ₁.range ⊔ κ₂.range ⊔ κ₃.range := by
  refine iSup_le fun k => ?_
  rcases Fin.eq_castSucc_or_eq_last (n := s + 3) k with ⟨k₁, rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last (n := s + 2) k₁ with ⟨k₂, rfl⟩ | rfl
    · rcases Fin.eq_castSucc_or_eq_last (n := s + 1) k₂ with ⟨k₃, rfl⟩ | rfl
      · rw [hU k₃]
        exact (spSpCharts_range_comp_le _ _).trans (le_sup_left.trans le_sup_left)
      · rw [hU₁]
        exact (spSpCharts_range_comp_le _ _).trans (le_sup_right.trans le_sup_left)
    · rw [hU₂]
      exact (spSpCharts_range_comp_le _ _).trans le_sup_right
  · rw [hU₃]
    exact (spSpCharts_range_comp_le _ _).trans le_sup_right

private theorem threeCharts_le_iSup {s : ℕ} {F : Type} [Field F] {G : Type} [Group G]
    (κ₁ κ₂ κ₃ : StatedSp (s + 2) F →* G)
    (hagree₁₂ : ∀ k : Fin s,
      (κ₁.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.succ)).ne)).range =
        (κ₂.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.castSucc)).ne)).range)
    (hagree₂₃ : ∀ k : Fin s,
      (κ₂.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.succ)).ne)).range =
        (κ₃.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.castSucc)).ne)).range)
    (hlong₁₂ : (κ₁.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range =
      (κ₂.comp (longBlock F (s + 2) (Fin.last s).castSucc)).range)
    (hlong₂₃ : (κ₂.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range =
      (κ₃.comp (longBlock F (s + 2) (Fin.last s).castSucc)).range)
    (U : Fin (s + 4) → Subgroup G)
    (hU : ∀ k : Fin (s + 1), U k.castSucc.castSucc.castSucc =
      (κ₁.comp (shortBlock F (Fin.castSucc_lt_succ (i := k)).ne)).range)
    (hU₁ : U (Fin.last (s + 1)).castSucc.castSucc =
      (κ₂.comp (shortBlock F (Fin.castSucc_lt_succ (i := Fin.last s)).ne)).range)
    (hU₂ : U (Fin.last (s + 2)).castSucc =
      (κ₃.comp (shortBlock F (Fin.castSucc_lt_succ (i := Fin.last s)).ne)).range)
    (hU₃ : U (Fin.last (s + 3)) =
      (κ₃.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range) :
    κ₁.range ⊔ κ₂.range ⊔ κ₃.range ≤ ⨆ k, U k := by
  have h₃ : κ₃.range ≤ ⨆ k, U k := by
    refine spSpCharts_range_le κ₃ _ (fun k => ?_) ?_
    · rcases Fin.eq_castSucc_or_eq_last (n := s) k with ⟨m, rfl⟩ | rfl
      · rw [← hagree₂₃ m]
        by_cases hm : m.val + 1 = s
        · have hms : m.succ = Fin.last s :=
            Fin.ext (by simp only [Fin.val_succ, Fin.val_last]; omega)
          rw [hms, ← hU₁]
          exact le_iSup U _
        · have hm' : m.val + 1 < s := by have := m.isLt; omega
          have hms : m.succ = (⟨m.val + 1, hm'⟩ : Fin s).castSucc :=
            Fin.ext (by simp only [Fin.val_succ, Fin.val_castSucc])
          rw [hms, ← hagree₁₂ ⟨m.val + 1, hm'⟩, ← hU (⟨m.val + 1, hm'⟩ : Fin s).succ]
          exact le_iSup U _
      · rw [← hU₂]
        exact le_iSup U _
    · rw [← hU₃]
      exact le_iSup U _
  have h₂ : κ₂.range ≤ ⨆ k, U k := by
    refine spSpCharts_range_le κ₂ _ (fun k => ?_) ?_
    · rcases Fin.eq_castSucc_or_eq_last (n := s) k with ⟨m, rfl⟩ | rfl
      · rw [← hagree₁₂ m, ← hU m.succ]
        exact le_iSup U _
      · rw [← hU₁]
        exact le_iSup U _
    · rw [hlong₂₃]
      exact (spSpCharts_range_comp_le _ _).trans h₃
  refine sup_le (sup_le (spSpCharts_range_le κ₁ _ (fun k => ?_) ?_) h₂) h₃
  · rw [← hU k]
    exact le_iSup U _
  · rw [hlong₁₂]
    exact (spSpCharts_range_comp_le _ _).trans h₂

theorem exists_chain_of_three_spSpCharts {s : ℕ} (hs : 1 ≤ s) {F : Type} [Field F] {G : Type}
    [Group G] (κ₁ κ₂ κ₃ : StatedSp (s + 2) F →* G) (hκ₁ : Function.Injective κ₁)
    (hκ₂ : Function.Injective κ₂) (hκ₃ : Function.Injective κ₃)
    (hagree₁₂ : ∀ k : Fin s,
      (κ₁.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.succ)).ne)).range =
        (κ₂.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.castSucc)).ne)).range)
    (hlong₁₂ : (κ₁.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range =
      (κ₂.comp (longBlock F (s + 2) (Fin.last s).castSucc)).range)
    (hagree₂₃ : ∀ k : Fin s,
      (κ₂.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.succ)).ne)).range =
        (κ₃.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.castSucc)).ne)).range)
    (hlong₂₃ : (κ₂.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range =
      (κ₃.comp (longBlock F (s + 2) (Fin.last s).castSucc)).range)
    (hcross₁₂ : ∀ a ∈ (κ₁.comp (shortBlock F
        (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne)).range,
      ∀ b ∈ (κ₂.comp (shortBlock F (Fin.castSucc_lt_succ (i := Fin.last s)).ne)).range,
        a * b = b * a)
    (hcross₁₃ₛ : ∀ a ∈ (κ₁.comp (shortBlock F
        (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne)).range,
      ∀ b ∈ (κ₃.comp (shortBlock F (Fin.castSucc_lt_succ (i := Fin.last s)).ne)).range,
        a * b = b * a)
    (hcross₁₃ₗ : ∀ a ∈ (κ₁.comp (shortBlock F
        (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne)).range,
      ∀ b ∈ (κ₃.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range, a * b = b * a)
    (hcross₂₃ₛ : ∀ a ∈ (κ₂.comp (shortBlock F
        (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne)).range,
      ∀ b ∈ (κ₃.comp (shortBlock F (Fin.castSucc_lt_succ (i := Fin.last s)).ne)).range,
        a * b = b * a)
    (hcross₂₃ₗ : ∀ a ∈ (κ₂.comp (shortBlock F
        (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne)).range,
      ∀ b ∈ (κ₃.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range, a * b = b * a) :
    ∃ U : Fin (s + 4) → Subgroup G,
      (∀ i j : Fin (s + 4), i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a) ∧
      (∀ i j : Fin (s + 4), i.val + 1 = j.val → j.val + 1 < s + 4 →
        ∃ W, LinearBlockStandardPair F W (U i) (U j)) ∧
      (∀ i j : Fin (s + 4), i.val + 1 = s + 4 → j.val + 2 = s + 4 →
        ∃ W, CFSG.ClassicalInvolution.Models.SymplecticPairs.SymplecticBlockStandardPair F W
          (U i) (U j)) ∧
      (⨆ k, U k) = κ₁.range ⊔ κ₂.range ⊔ κ₃.range := by
  let U : Fin (s + 4) → Subgroup G :=
    Fin.lastCases (motive := fun _ => Subgroup G)
      (κ₃.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range
      (Fin.lastCases (motive := fun _ => Subgroup G)
        (κ₃.comp (shortBlock F (Fin.castSucc_lt_succ (i := Fin.last s)).ne)).range
        (Fin.lastCases (motive := fun _ => Subgroup G)
          (κ₂.comp (shortBlock F (Fin.castSucc_lt_succ (i := Fin.last s)).ne)).range
          (fun k : Fin (s + 1) =>
            (κ₁.comp (shortBlock F (Fin.castSucc_lt_succ (i := k)).ne)).range)))
  have hU : ∀ k : Fin (s + 1), U k.castSucc.castSucc.castSucc =
      (κ₁.comp (shortBlock F (Fin.castSucc_lt_succ (i := k)).ne)).range := fun k => by
    simp only [U, Fin.lastCases_castSucc]
  have hU₁ : U (Fin.last (s + 1)).castSucc.castSucc =
      (κ₂.comp (shortBlock F (Fin.castSucc_lt_succ (i := Fin.last s)).ne)).range := by
    simp only [U, Fin.lastCases_castSucc, Fin.lastCases_last]
  have hU₂ : U (Fin.last (s + 2)).castSucc =
      (κ₃.comp (shortBlock F (Fin.castSucc_lt_succ (i := Fin.last s)).ne)).range := by
    simp only [U, Fin.lastCases_castSucc, Fin.lastCases_last]
  have hU₃ : U (Fin.last (s + 3)) =
      (κ₃.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range := by
    simp only [U, Fin.lastCases_last]
  exact ⟨U, threeCharts_comm hs κ₁ κ₂ κ₃ hagree₁₂ hagree₂₃ hcross₁₂ hcross₁₃ₛ hcross₁₃ₗ
      hcross₂₃ₛ hcross₂₃ₗ U hU hU₁ hU₂ hU₃,
    threeCharts_pair hs κ₁ κ₂ κ₃ hκ₁ hκ₂ hκ₃ hagree₁₂ hagree₂₃ U hU hU₁ hU₂,
    threeCharts_sp κ₃ hκ₃ U hU₂ hU₃,
    le_antisymm (threeCharts_iSup_le κ₁ κ₂ κ₃ U hU hU₁ hU₂ hU₃)
      (threeCharts_le_iSup κ₁ κ₂ κ₃ hagree₁₂ hagree₂₃ hlong₁₂ hlong₂₃ U hU hU₁ hU₂ hU₃)⟩

end CFSG.ClassicalInvolution.WeakCT

end
