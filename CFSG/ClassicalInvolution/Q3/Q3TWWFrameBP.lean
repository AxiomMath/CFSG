module

public import CFSG.ClassicalInvolution.Q3.Q3TWWAdjBP
public import CFSG.ClassicalInvolution.Q3.Q3TWWAdjB
public import CFSG.ClassicalInvolution.Q3.Q3WChain
public import CFSG.ClassicalInvolution.Q3.Q3ZAdjMain
public import CFSG.ClassicalInvolution.WeakCT.SpPair
public import CFSG.ClassicalInvolution.WeakCT.SimplyLaced
public import CFSG.ClassicalInvolution.WeakCT.TwistedTransport
public import CFSG.ClassicalInvolution.WeakCT.DLWeakAgree
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.ClassicalInvolution.WeakCT.TwistedE6Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TW

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.ClassicalInvolution.Q3.Q3Z
open CFSG.ClassicalInvolution.WeakCT
  (blk blockSL spBlock LinearBlockStandardPair spBlock_one_eq_longBlock spBlock_zero_eq_shortBlock
    map_blk)
open scoped MatrixGroups

structure OddFramePair (F : Type) [Field F] (n : ℕ) {X : Type} [Group X]
    (U : Fin n → Subgroup X) where
  ρ : Fin n → (SL(2, F) →* X)
  ρ_inj : ∀ k : Fin n, k.val + 1 < n → Function.Injective (ρ k)
  ρ_range : ∀ k, (ρ k).range = U k
  ψ : ∀ i : Fin n, i.val + 2 < n → (SL(3, F) →* X)
  ψ_zero : ∀ (i : Fin n) (h : i.val + 2 < n), (ψ i h).comp (blk F 0) = ρ i
  ψ_one : ∀ (i j : Fin n) (h : i.val + 2 < n), j.val = i.val + 1 →
    (ψ i h).comp (blk F 1) = ρ j
  ψ4 : StatedSp 2 F →* X
  ψ4_long : ∀ a : Fin n, a.val + 2 = n → ψ4.comp (spBlock F 1) = ρ a
  ψ4_short : ∀ b : Fin n, b.val + 1 = n → ψ4.comp (spBlock F 0) = ρ b

section Transport

variable {K K' : Type} [Field K] [Field K'] {X : Type} [Group X] {n : ℕ} {U : Fin n → Subgroup X}

private theorem map_comp_blkBP (φ : K →+* K') (s : Fin 2) :
    (Matrix.SpecialLinearGroup.map φ : SL(3, K) →* SL(3, K')).comp (blk K s) =
      (blk K' s).comp (Matrix.SpecialLinearGroup.map φ : SL(2, K) →* SL(2, K')) :=
  MonoidHom.ext fun A => map_blk φ s A

private theorem spMap_comp_spBlock_oneBP (φ : K →+* K') :
    (spMap (n := 2) φ).comp (spBlock K 1) =
      (spBlock K' 1).comp (Matrix.SpecialLinearGroup.map φ : SL(2, K) →* SL(2, K')) := by
  rw [spBlock_one_eq_longBlock, spBlock_one_eq_longBlock]
  exact MonoidHom.ext fun A => spMap_longBlock φ 1 A

private theorem spMap_comp_spBlock_zeroBP (φ : K →+* K') :
    (spMap (n := 2) φ).comp (spBlock K 0) =
      (spBlock K' 0).comp (Matrix.SpecialLinearGroup.map φ : SL(2, K) →* SL(2, K')) := by
  rw [spBlock_zero_eq_shortBlock, spBlock_zero_eq_shortBlock]
  exact MonoidHom.ext fun A => spMap_shortBlock φ zero_ne_one A

@[expose] noncomputable def OddFramePair.ofRingEquiv (e : K ≃+* K') (fr : OddFramePair K n U) :
    OddFramePair K' n U where
  ρ k := (fr.ρ k).comp (Matrix.SpecialLinearGroup.map e.symm.toRingHom : SL(2, K') →* SL(2, K))
  ρ_inj k hk := (fr.ρ_inj k hk).comp (slMap_injective e.symm 2)
  ρ_range k := by
    rw [range_comp_of_surjective _ (slMap_surjective e.symm 2), fr.ρ_range]
  ψ i h :=
    (fr.ψ i h).comp (Matrix.SpecialLinearGroup.map e.symm.toRingHom : SL(3, K') →* SL(3, K))
  ψ_zero i h := by
    rw [MonoidHom.comp_assoc, map_comp_blkBP, ← MonoidHom.comp_assoc, fr.ψ_zero i h]
  ψ_one i j h hj := by
    rw [MonoidHom.comp_assoc, map_comp_blkBP, ← MonoidHom.comp_assoc, fr.ψ_one i j h hj]
  ψ4 := fr.ψ4.comp (spMap e.symm.toRingHom)
  ψ4_long a ha := by
    rw [MonoidHom.comp_assoc, spMap_comp_spBlock_oneBP, ← MonoidHom.comp_assoc, fr.ψ4_long a ha]
  ψ4_short b hb := by
    rw [MonoidHom.comp_assoc, spMap_comp_spBlock_zeroBP, ← MonoidHom.comp_assoc, fr.ψ4_short b hb]

end Transport

section PairZMod

variable {G : Type} [Group G] {F : Type} [Field F]

theorem exists_pairBP_zmod (e : ZMod 3 ≃+* F) {W U V : Subgroup G}
    (h : SymplecticBlockPair F W U V) :
    ∃ θ : StatedSp 2 (ZMod 3) →* G,
      Function.Injective (θ.comp (longBlock (ZMod 3) 2 1)) ∧
      (longBlock (ZMod 3) 2 1).range.map θ = U ∧
      (shortBlock (ZMod 3) (zero_ne_one : (0 : Fin 2) ≠ 1)).range.map θ = V := by
  obtain ⟨θ, c, -, -, hinjL, hU, hV⟩ := h
  let θ0 : StatedSp 2 F →* G := θ.comp (MulAut.conj c⁻¹).toMonoidHom
  let Φ2 : SL(2, ZMod 3) →* SL(2, F) := Matrix.SpecialLinearGroup.map e.toRingHom
  let Sp2 : StatedSp 2 (ZMod 3) →* StatedSp 2 F := spMap e.toRingHom
  have cL : (θ0.comp Sp2).comp (longBlock (ZMod 3) 2 1) = (θ0.comp (longBlock F 2 1)).comp Φ2 := by
    ext A
    exact congrArg θ0 (spMap_longBlock e.toRingHom 1 A)
  have cS : (θ0.comp Sp2).comp (shortBlock (ZMod 3) (zero_ne_one : (0 : Fin 2) ≠ 1)) =
      (θ0.comp (shortBlock F (zero_ne_one : (0 : Fin 2) ≠ 1))).comp Φ2 := by
    ext A
    exact congrArg θ0 (spMap_shortBlock e.toRingHom zero_ne_one A)
  refine ⟨θ0.comp Sp2, ?_, ?_, ?_⟩
  · rw [cL]
    exact hinjL.comp (slMap_injective e 2)
  · calc (longBlock (ZMod 3) 2 1).range.map (θ0.comp Sp2)
        = ((θ0.comp Sp2).comp (longBlock (ZMod 3) 2 1)).range := (MonoidHom.range_comp _ _).symm
      _ = (θ0.comp (longBlock F 2 1)).range := by
          rw [cL]
          exact range_comp_of_surjective _ (slMap_surjective e 2)
      _ = ((longBlock F 2 1).range.map (MulAut.conj c⁻¹).toMonoidHom).map θ := by
          rw [MonoidHom.range_comp, Subgroup.map_map]
      _ = U := hU
  · calc (shortBlock (ZMod 3) (zero_ne_one : (0 : Fin 2) ≠ 1)).range.map (θ0.comp Sp2)
        = ((θ0.comp Sp2).comp (shortBlock (ZMod 3) (zero_ne_one : (0 : Fin 2) ≠ 1))).range :=
          (MonoidHom.range_comp _ _).symm
      _ = (θ0.comp (shortBlock F (zero_ne_one : (0 : Fin 2) ≠ 1))).range := by
          rw [cS]
          exact range_comp_of_surjective _ (slMap_surjective e 2)
      _ = ((shortBlock F (zero_ne_one : (0 : Fin 2) ≠ 1)).range.map
            (MulAut.conj c⁻¹).toMonoidHom).map θ := by
          rw [MonoidHom.range_comp, Subgroup.map_map]
      _ = V := hV

end PairZMod

section ZModFrame

variable {X : Type} [Group X]

theorem exists_oddFramePair_zmod {n : ℕ} (hn : 3 ≤ n) (U : Fin n → Subgroup X)
    (hcomm : ∀ i j : Fin n, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hC : ∀ k : Fin 24, gluingComplete k = false → ∀ g : Fin 12 → X,
      RelsHold g (b3aWords k) → ∀ i, g i = 1)
    (hpair : ∀ i j : Fin n, i.val + 1 = j.val → j.val + 1 < n →
      ∃ W, LinearBlockStandardPair (ZMod 3) W (U i) (U j))
    (hsp : ∀ a b : Fin n, a.val + 2 = n → b.val + 1 = n →
      ∃ θB : StatedSp 2 (ZMod 3) →* X,
        Function.Injective (θB.comp (longBlock (ZMod 3) 2 1)) ∧
        (longBlock (ZMod 3) 2 1).range.map θB = U a ∧
        (shortBlock (ZMod 3) (zero_ne_one : (0 : Fin 2) ≠ 1)).range.map θB = U b) :
    Nonempty (OddFramePair (ZMod 3) n U) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  obtain ⟨FA, hFA⟩ := Q3W.exists_ctFamily_of_pairs3 (by omega : 2 ≤ m + 2)
    (U := fun i : Fin (m + 2) => U ⟨i.val, by omega⟩)
    (fun i j hij x hx y hy => hcomm ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ hij x hx y hy)
    (fun i j hij => hpair ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ hij.symm (by simp only; omega))
  have hleft : (FA.θ ⟨m, by omega⟩).comp (blockSL (ZMod 3) 3 2 0 (by omega)) =
      FA.ι ⟨m, by omega⟩ := FA.left ⟨m, by omega⟩ (by simp)
  have hright : (FA.θ ⟨m, by omega⟩).comp (blockSL (ZMod 3) 3 2 1 (by omega)) =
      FA.ι ⟨m + 1, by omega⟩ := FA.right ⟨m, by omega⟩ (by simp)
  obtain ⟨θB, hιL, hB1, hB2⟩ := hsp ⟨m + 1, by omega⟩ ⟨m + 2, by omega⟩ rfl rfl
  obtain ⟨θA', θB', hA'0, hBL, hιA', hA'1, hB2'⟩ := exists_adjust_b3_pair
    (U ⟨m, by omega⟩) (U ⟨m + 1, by omega⟩) (U ⟨m + 2, by omega⟩)
    (hcomm ⟨m, by omega⟩ ⟨m + 2, by omega⟩ (by simp)) hC (FA.θ ⟨m, by omega⟩)
    (by rw [hright]; exact (hFA _).2)
    (by rw [← MonoidHom.range_comp, hleft]; exact (hFA _).1)
    (by rw [← MonoidHom.range_comp, hright]; exact (hFA _).1) θB hιL hB1 hB2
  let ρ : Fin (m + 3) → (SL(2, ZMod 3) →* X) := fun k =>
    if h : k.val < m + 1 then FA.ι ⟨k.val, by omega⟩
    else if k.val = m + 1 then θA'.comp (blockSL (ZMod 3) 3 2 1 (by omega))
    else θB'.comp (shortBlock (ZMod 3) (zero_ne_one : (0 : Fin 2) ≠ 1))
  have hρ0 : ∀ (k : Fin (m + 3)) (h : k.val < m + 1), ρ k = FA.ι ⟨k.val, by omega⟩ :=
    fun k h => dite_eq_left h
  have hρ1 : ∀ k : Fin (m + 3), k.val = m + 1 →
      ρ k = θA'.comp (blockSL (ZMod 3) 3 2 1 (by omega)) := fun k h => by
    have h' : ¬ k.val < m + 1 := by omega
    show (if h : k.val < m + 1 then _ else _) = _
    rw [dite_eq_right h', ite_eq_left h]
  have hρ2 : ∀ k : Fin (m + 3), k.val = m + 2 →
      ρ k = θB'.comp (shortBlock (ZMod 3) (zero_ne_one : (0 : Fin 2) ≠ 1)) := fun k h => by
    have h' : ¬ k.val < m + 1 := by omega
    have h'' : ¬ k.val = m + 1 := by omega
    show (if h : k.val < m + 1 then _ else _) = _
    rw [dite_eq_right h', ite_eq_right h'']
  let ψ : ∀ i : Fin (m + 3), i.val + 2 < m + 3 → (SL(3, ZMod 3) →* X) := fun i h =>
    if h' : i.val < m then FA.θ ⟨i.val, by omega⟩ else θA'
  have hψ0 : ∀ (i : Fin (m + 3)) (h : i.val + 2 < m + 3) (h' : i.val < m),
      ψ i h = FA.θ ⟨i.val, by omega⟩ := fun i h h' => dite_eq_left h'
  have hψ1 : ∀ (i : Fin (m + 3)) (h : i.val + 2 < m + 3), i.val = m → ψ i h = θA' :=
    fun i h h' => dite_eq_right (by omega)
  refine ⟨{ ρ := ρ, ρ_inj := ?_, ρ_range := ?_, ψ := ψ, ψ_zero := ?_, ψ_one := ?_,
            ψ4 := θB', ψ4_long := ?_, ψ4_short := ?_ }⟩
  · intro k hk
    by_cases h : k.val < m + 1
    · rw [hρ0 k h]
      exact (hFA ⟨k.val, by omega⟩).2
    · have h1 : k.val = m + 1 := by omega
      rw [hρ1 k h1]
      exact hιA'
  · intro k
    by_cases h : k.val < m + 1
    · rw [hρ0 k h]
      exact (hFA ⟨k.val, by omega⟩).1
    · by_cases h1 : k.val = m + 1
      · rw [hρ1 k h1, MonoidHom.range_comp]
        have hk : k = ⟨m + 1, by omega⟩ := Fin.ext h1
        rw [hk]
        exact hA'1
      · rw [hρ2 k (by omega), MonoidHom.range_comp]
        have hk : k = ⟨m + 2, by omega⟩ := Fin.ext (by have := k.2; simp only; omega)
        rw [hk]
        exact hB2'
  · intro i h
    by_cases h' : i.val < m
    · rw [hψ0 i h h', hρ0 i (by omega)]
      exact FA.left ⟨i.val, by omega⟩ (by simp only; omega)
    · have him : i.val = m := by omega
      rw [hψ1 i h him, hρ0 i (by omega)]
      refine hA'0.trans ?_
      have : (⟨i.val, by omega⟩ : Fin (m + 2)) = ⟨m, by omega⟩ := Fin.ext him
      rw [this]
      exact hleft
  · intro i j h hj
    by_cases h' : i.val < m
    · rw [hψ0 i h h', hρ0 j (by omega)]
      refine (FA.right ⟨i.val, by omega⟩ (by simp only; omega)).trans ?_
      exact congrArg FA.ι (Fin.ext (by simp only; omega))
    · have him : i.val = m := by omega
      rw [hψ1 i h him, hρ1 j (by omega)]
      rfl
  · intro a ha
    rw [spBlock_one_eq_longBlock, hρ1 a (by omega)]
    exact MonoidHom.ext hBL
  · intro b hb
    rw [spBlock_zero_eq_shortBlock, hρ2 b (by omega)]

end ZModFrame

theorem exists_oddFramePair_of_ringEquiv {F : Type} [Field F] (e : ZMod 3 ≃+* F) {n : ℕ}
    (hn : 3 ≤ n) {X : Type} [Group X] (U : Fin n → Subgroup X)
    (hcomm : ∀ i j : Fin n, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hC : ∀ k : Fin 24, gluingComplete k = false → ∀ g : Fin 12 → X,
      RelsHold g (b3aWords k) → ∀ i, g i = 1)
    (hpair : ∀ i j : Fin n, i.val + 1 = j.val → j.val + 1 < n →
      ∃ W, LinearBlockStandardPair F W (U i) (U j))
    (hsp : ∀ i j : Fin n, i.val + 2 = n → j.val + 1 = n →
      ∃ W, SymplecticBlockPair F W (U i) (U j)) :
    Nonempty (OddFramePair F n U) := by
  obtain ⟨fr⟩ := exists_oddFramePair_zmod hn U hcomm hC
    (fun i j h1 h2 => (hpair i j h1 h2).imp fun W hW => hW.of_ringEquiv e.symm)
    (fun a b ha hb => by
      obtain ⟨W, hW⟩ := hsp a b ha hb
      exact exists_pairBP_zmod e hW)
  exact ⟨fr.ofRingEquiv e⟩

end CFSG.ClassicalInvolution.Q3.Q3TW
