module

public import CFSG.ClassicalInvolution.Q3.Q3VCtFrAdj
public import CFSG.ClassicalInvolution.Q3.Q3VCtFrFlip
public import CFSG.ClassicalInvolution.Q3.Q3ZAdjMain
public import CFSG.ClassicalInvolution.Q3.Q3WChain
public import CFSG.ClassicalInvolution.WeakCT.SpPair
public import CFSG.ClassicalInvolution.WeakCT.TwistedTransport
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.ClassicalInvolution.WeakCT.TwistedE6Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear

public section

namespace CFSG.ClassicalInvolution.Q3.Q3V

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.ClassicalInvolution.Q3.Q3Z
open CFSG.ClassicalInvolution.WeakCT
  (blk blockSL spBlock LinearBlockStandardPair spBlock_one_eq_longBlock spBlock_zero_eq_shortBlock
    map_blk)
open scoped MatrixGroups

structure SpFrame (F : Type) [Field F] (n : ℕ) {X : Type} [Group X] (U : Fin n → Subgroup X) where
  ρ : Fin n → (SL(2, F) →* X)
  ρ_inj : ∀ k, Function.Injective (ρ k)
  ρ_range : ∀ k, (ρ k).range = U k
  ψ : ∀ i : Fin n, i.val + 2 < n → (SL(3, F) →* X)
  ψ_zero : ∀ (i j : Fin n) (h : i.val + 2 < n), j.val = i.val + 1 →
    (ψ i h).comp (blk F 0) = ρ j
  ψ_one : ∀ (i : Fin n) (h : i.val + 2 < n), (ψ i h).comp (blk F 1) = ρ i
  ψ4 : StatedSp 2 F →* X
  ψ4_long : ∀ a : Fin n, a.val + 1 = n → ψ4.comp (spBlock F 1) = ρ a
  ψ4_short : ∀ b : Fin n, b.val + 2 = n → ψ4.comp (spBlock F 0) = ρ b

abbrev SpFrame3 (n : ℕ) {X : Type} [Group X] (U : Fin n → Subgroup X) : Type :=
  SpFrame (GaloisField 3 1) n U

section Transport

variable {K K' : Type} [Field K] [Field K'] {X : Type} [Group X] {n : ℕ} {U : Fin n → Subgroup X}

private theorem map_comp_blk (φ : K →+* K') (s : Fin 2) :
    (Matrix.SpecialLinearGroup.map φ : SL(3, K) →* SL(3, K')).comp (blk K s) =
      (blk K' s).comp (Matrix.SpecialLinearGroup.map φ : SL(2, K) →* SL(2, K')) :=
  MonoidHom.ext fun A => map_blk φ s A

private theorem spMap_comp_spBlock_one (φ : K →+* K') :
    (spMap (n := 2) φ).comp (spBlock K 1) =
      (spBlock K' 1).comp (Matrix.SpecialLinearGroup.map φ : SL(2, K) →* SL(2, K')) := by
  rw [spBlock_one_eq_longBlock, spBlock_one_eq_longBlock]
  exact MonoidHom.ext fun A => spMap_longBlock φ 1 A

private theorem spMap_comp_spBlock_zero (φ : K →+* K') :
    (spMap (n := 2) φ).comp (spBlock K 0) =
      (spBlock K' 0).comp (Matrix.SpecialLinearGroup.map φ : SL(2, K) →* SL(2, K')) := by
  rw [spBlock_zero_eq_shortBlock, spBlock_zero_eq_shortBlock]
  exact MonoidHom.ext fun A => spMap_shortBlock φ zero_ne_one A

@[expose] noncomputable def SpFrame.ofRingEquiv (e : K ≃+* K') (fr : SpFrame K n U) :
    SpFrame K' n U where
  ρ k := (fr.ρ k).comp (Matrix.SpecialLinearGroup.map e.symm.toRingHom : SL(2, K') →* SL(2, K))
  ρ_inj k := (fr.ρ_inj k).comp (slMap_injective e.symm 2)
  ρ_range k := by
    rw [range_comp_of_surjective _ (slMap_surjective e.symm 2), fr.ρ_range]
  ψ i h :=
    (fr.ψ i h).comp (Matrix.SpecialLinearGroup.map e.symm.toRingHom : SL(3, K') →* SL(3, K))
  ψ_zero i j h hj := by
    rw [MonoidHom.comp_assoc, map_comp_blk, ← MonoidHom.comp_assoc, fr.ψ_zero i j h hj]
  ψ_one i h := by
    rw [MonoidHom.comp_assoc, map_comp_blk, ← MonoidHom.comp_assoc, fr.ψ_one i h]
  ψ4 := fr.ψ4.comp (spMap e.symm.toRingHom)
  ψ4_long a ha := by
    rw [MonoidHom.comp_assoc, spMap_comp_spBlock_one, ← MonoidHom.comp_assoc, fr.ψ4_long a ha]
  ψ4_short b hb := by
    rw [MonoidHom.comp_assoc, spMap_comp_spBlock_zero, ← MonoidHom.comp_assoc, fr.ψ4_short b hb]

end Transport

section ZModFrame

variable {X : Type} [Group X]

theorem exists_spFrame_zmod {n : ℕ} (hn : 3 ≤ n) (U : Fin n → Subgroup X)
    (hcomm : ∀ i j : Fin n, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hC : ∀ k : Fin 24, gluingComplete k = false → ∀ g : Fin 12 → X,
      RelsHold g (v6aWords k) → ∀ i, g i = 1)
    (hpair : ∀ i j : Fin n, i.val + 1 = j.val → j.val + 1 < n →
      ∃ W, LinearBlockStandardPair (ZMod 3) W (U i) (U j))
    (hsp : ∀ a b : Fin n, a.val + 1 = n → b.val + 2 = n →
      ∃ θB : StatedSp 2 (ZMod 3) →* X,
        Function.Injective (θB.comp (longBlock (ZMod 3) 2 1)) ∧
        Function.Injective
          (θB.comp (shortBlock (ZMod 3) (zero_ne_one : (0 : Fin 2) ≠ 1))) ∧
        (longBlock (ZMod 3) 2 1).range.map θB = U a ∧
        (shortBlock (ZMod 3) (zero_ne_one : (0 : Fin 2) ≠ 1)).range.map θB = U b) :
    Nonempty (SpFrame (ZMod 3) n U) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  obtain ⟨FA, hFA⟩ := Q3W.exists_ctFamily_of_pairs3 (by omega : 2 ≤ m + 2)
    (U := fun i : Fin (m + 2) => U ⟨i.val, by omega⟩)
    (fun i j hij x hx y hy => hcomm ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ hij x hx y hy)
    (fun i j hij => hpair ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ hij.symm (by simp only; omega))
  have hleft : (FA.θ ⟨m, by omega⟩).comp (blockSL (ZMod 3) 3 2 0 (by omega)) =
      FA.ι ⟨m, by omega⟩ := FA.left ⟨m, by omega⟩ (by simp)
  have hright : (FA.θ ⟨m, by omega⟩).comp (blockSL (ZMod 3) 3 2 1 (by omega)) =
      FA.ι ⟨m + 1, by omega⟩ := FA.right ⟨m, by omega⟩ (by simp)
  obtain ⟨θB, hιL, hιS, hB2, hB1⟩ := hsp ⟨m + 2, by omega⟩ ⟨m + 1, by omega⟩ rfl rfl
  obtain ⟨θB', hS, hιL', hB2'⟩ := exists_adjust_sp3 (U ⟨m, by omega⟩) (U ⟨m + 1, by omega⟩)
    (U ⟨m + 2, by omega⟩) (hcomm ⟨m, by omega⟩ ⟨m + 2, by omega⟩ (by simp)) hC
    (FA.θ ⟨m, by omega⟩) (by rw [hright]; exact (hFA _).2)
    (by rw [← MonoidHom.range_comp, hleft]; exact (hFA _).1)
    (by rw [← MonoidHom.range_comp, hright]; exact (hFA _).1) θB hιS hιL hB2 hB1
  let ρ : Fin (m + 3) → (SL(2, ZMod 3) →* X) := fun k =>
    if h : k.val < m + 2 then FA.ι ⟨k.val, h⟩ else θB'.comp (longBlock (ZMod 3) 2 1)
  have hρ_pos : ∀ (k : Fin (m + 3)) (h : k.val < m + 2), ρ k = FA.ι ⟨k.val, h⟩ :=
    fun k h => dite_eq_left h
  have hρ_neg : ∀ k : Fin (m + 3), ¬ k.val < m + 2 →
      ρ k = θB'.comp (longBlock (ZMod 3) 2 1) := fun k h => dite_eq_right h
  let ψ : ∀ i : Fin (m + 3), i.val + 2 < m + 3 → (SL(3, ZMod 3) →* X) := fun i h =>
    (FA.θ ⟨i.val, by omega⟩).comp (blockSwapAut (K := ZMod 3)).toMonoidHom
  refine ⟨{ ρ := ρ, ρ_inj := ?_, ρ_range := ?_, ψ := ψ, ψ_zero := ?_, ψ_one := ?_,
            ψ4 := θB', ψ4_long := ?_, ψ4_short := ?_ }⟩
  · intro k
    by_cases h : k.val < m + 2
    · rw [hρ_pos k h]
      exact (hFA ⟨k.val, h⟩).2
    · rw [hρ_neg k h]
      exact hιL'
  · intro k
    by_cases h : k.val < m + 2
    · rw [hρ_pos k h]
      exact (hFA ⟨k.val, h⟩).1
    · rw [hρ_neg k h, MonoidHom.range_comp]
      have hk : k = ⟨m + 2, by omega⟩ := Fin.ext (by have := k.2; simp only; omega)
      rw [hk]
      exact hB2'
  · intro i j h hj
    refine (comp_blockSwapAut_blk (FA.θ ⟨i.val, by omega⟩) 0).trans ?_
    rw [hρ_pos j (by omega)]
    exact (FA.right ⟨i.val, by omega⟩ (by simp only; omega)).trans
      (congrArg FA.ι (Fin.ext (by simp only; omega)))
  · intro i h
    refine (comp_blockSwapAut_blk (FA.θ ⟨i.val, by omega⟩) 1).trans ?_
    rw [hρ_pos i (by omega)]
    exact FA.left ⟨i.val, by omega⟩ (by simp only; omega)
  · intro a ha
    rw [spBlock_one_eq_longBlock, hρ_neg a (by omega)]
  · intro b hb
    rw [spBlock_zero_eq_shortBlock, hρ_pos b (by omega)]
    refine MonoidHom.ext fun A => ?_
    have hb' : (⟨b.val, by omega⟩ : Fin (m + 2)) = ⟨m + 1, by omega⟩ :=
      Fin.ext (by simp only; omega)
    rw [hb']
    show θB' (shortBlock (ZMod 3) (zero_ne_one : (0 : Fin 2) ≠ 1) A) = _
    rw [hS A, ← hright]
    rfl

end ZModFrame

theorem exists_spFrame_of_ringEquiv {F : Type} [Field F] (e : ZMod 3 ≃+* F) {n : ℕ} (hn : 3 ≤ n)
    {X : Type} [Group X] (U : Fin n → Subgroup X)
    (hcomm : ∀ i j : Fin n, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hC : ∀ k : Fin 24, gluingComplete k = false → ∀ g : Fin 12 → X,
      RelsHold g (v6aWords k) → ∀ i, g i = 1)
    (hpair : ∀ i j : Fin n, i.val + 1 = j.val → j.val + 1 < n →
      ∃ W, LinearBlockStandardPair F W (U i) (U j))
    (hsp : ∀ i j : Fin n, i.val + 1 = n → j.val + 2 = n →
      ∃ W, SymplecticBlockStandardPair F W (U i) (U j)) :
    Nonempty (SpFrame F n U) := by
  obtain ⟨fr⟩ := exists_spFrame_zmod hn U hcomm hC
    (fun i j h1 h2 => (hpair i j h1 h2).imp fun W hW => hW.of_ringEquiv e.symm)
    (fun a b ha hb => by
      obtain ⟨W, hW⟩ := hsp a b ha hb
      exact exists_pairB_zmod e hW)
  exact ⟨fr.ofRingEquiv e⟩

section Read

variable {F : Type} [Field F] {X : Type} [Group X] {n : ℕ} {U : Fin n → Subgroup X}

theorem SpFrame.edgeDown_data (fr : SpFrame F n U) {a b : Fin n} (ha : a.val + 1 = n)
    (hb : b.val + 2 = n) :
    (∀ k, Function.Injective (fr.ρ k) ∧ (fr.ρ k).range = U k) ∧
      (∀ i j : Fin n, j.val + 1 = i.val → ¬ (i = a ∧ j = b) →
        ∃ ψ : SL(3, F) →* X, ψ.comp (blk F 0) = fr.ρ i ∧ ψ.comp (blk F 1) = fr.ρ j) ∧
      ∃ ψ : StatedSp 2 F →* X, ψ.comp (spBlock F 1) = fr.ρ a ∧ ψ.comp (spBlock F 0) = fr.ρ b := by
  refine ⟨fun k => ⟨fr.ρ_inj k, fr.ρ_range k⟩, fun i j hij hne => ?_,
    ⟨fr.ψ4, fr.ψ4_long a ha, fr.ψ4_short b hb⟩⟩
  have hj : j.val + 2 < n := by
    have hi := i.2
    by_contra hcon
    exact hne ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
  exact ⟨fr.ψ j hj, fr.ψ_zero j i hj hij.symm, fr.ψ_one j hj⟩

theorem SpFrame.exists_psi_up (fr : SpFrame F n U) (i j : Fin n) (h : i.val + 2 < n)
    (hij : j.val = i.val + 1) :
    ∃ ψ : SL(3, F) →* X, ψ.comp (blk F 0) = fr.ρ i ∧ ψ.comp (blk F 1) = fr.ρ j :=
  ⟨(fr.ψ i h).comp (blockSwapAut (K := F)).toMonoidHom,
    (comp_blockSwapAut_blk (fr.ψ i h) 0).trans (fr.ψ_one i h),
    (comp_blockSwapAut_blk (fr.ψ i h) 1).trans (fr.ψ_zero i j h hij)⟩

theorem SpFrame.commute (fr : SpFrame F n U)
    (hcomm : ∀ i j : Fin n, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (i j : Fin n) (hij : i.val + 1 < j.val) (u v : SL(2, F)) :
    fr.ρ i u * fr.ρ j v = fr.ρ j v * fr.ρ i u :=
  hcomm i j hij _ (fr.ρ_range i ▸ ⟨u, rfl⟩) _ (fr.ρ_range j ▸ ⟨v, rfl⟩)

end Read

end CFSG.ClassicalInvolution.Q3.Q3V
