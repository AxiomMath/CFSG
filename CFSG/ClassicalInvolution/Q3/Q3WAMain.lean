module

public import CFSG.ClassicalInvolution.Q3.Q3WL65
public import CFSG.ClassicalInvolution.WeakCT.TwistedTransport
public import CFSG.ClassicalInvolution.RouteD.TypeARecognition
public import CFSG.ClassicalInvolution.Q3.Q3WChain

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

theorem map_blockSL {K K' : Type} [Field K] [Field K'] (e : K →+* K') {m k i : ℕ}
    (h : i + k ≤ m) (A : SL(k, K)) :
    Matrix.SpecialLinearGroup.map e (blockSL K m k i h A) =
      blockSL K' m k i h (Matrix.SpecialLinearGroup.map e A) := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.map_apply_coe, coe_blockSL, coe_blockSL,
    Matrix.SpecialLinearGroup.map_apply_coe]
  ext a b
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Phan.blockMat_apply]
  split_ifs with hab
  · rfl
  · by_cases hb : a = b
    · subst hb
      simp
    · simp [hb]

theorem weakCT3_recognition_blocks {n : ℕ} (hn : 3 ≤ n) {X : Type} [Group X]
    {U : Fin n → Subgroup X}
    (hcomm : ∀ i j : Fin n, (i : ℕ) + 1 < j → ∀ x ∈ U i, ∀ y ∈ U j, x * y = y * x)
    (hpair : ∀ i j : Fin n, (j : ℕ) = i + 1 → ∃ W, LinearBlockStandardPair F3 W (U i) (U j))
    (hgen : ⨆ i, U i = ⊤) :
    ∃ ψ : SL(n + 1, F3) →* X, Function.Surjective ψ ∧
      ψ.ker ≤ Subgroup.center SL(n + 1, F3) ∧ CFSG.IsQuasisimple X ∧
      CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X)
        CFSG.Assembly.LowTwoRank.StatedLieTag.PSL (n + 1) 3 1 ∧
      ∀ i : Fin n, (blockSL2 F3 n i).range.map ψ = U i := by
  obtain ⟨F, hF⟩ := exists_ctFamily_of_pairs3 (by omega) hcomm hpair
  have hgen' : ⨆ i, (F.ι i).range = ⊤ := by
    simp only [fun i => (hF i).1]
    exact hgen
  have hnt : ∃ i, ∃ A, F.ι i A ≠ 1 := by
    refine ⟨⟨0, by omega⟩, xp 1, fun h => xp_one_ne_one ?_⟩
    exact (hF ⟨0, by omega⟩).2 (h.trans (map_one _).symm)
  obtain ⟨ψ, hψι, hsurj, hker, hqs, -, hmodel⟩ :=
    exists_recognition hn Nat.prime_three le_rfl (by simp) F hgen' hnt
  refine ⟨ψ, hsurj, hker, hqs, hmodel, fun i => ?_⟩
  have : ψ.comp (blockSL2 F3 n i) = F.ι i := MonoidHom.ext fun A => hψι i A
  rw [← MonoidHom.range_comp, this, (hF i).1]

theorem exists_psi_of_chain3 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3) {m : ℕ}
    (hm : 1 ≤ m) {G : Type} [Group G] {U : Fin (m + 2) → Subgroup G}
    (hcomm : ∀ i j : Fin (m + 2), (i : ℕ) + 1 < j → Commutes (U i) (U j))
    (hpair : ∀ i j : Fin (m + 2), (j : ℕ) = i + 1 →
      ∃ W, LinearBlockStandardPair K W (U i) (U j)) :
    ∃ ψ : SL(m + 1 + 2, K) →* G,
      ψ.ker ≤ Subgroup.center SL(m + 1 + 2, K) ∧ ψ.range = ⨆ i, U i ∧
      ∀ i : Fin (m + 2), (blockSL2 K (m + 2) i).range.map ψ = U i := by
  obtain ⟨e⟩ := nonempty_ringEquiv_zmod_three hK
  set Gs := ⨆ i, U i with hGs
  have hUle : ∀ i, U i ≤ Gs := fun i => le_iSup U i
  obtain ⟨ψ', hsurj, hker, -, -, hblk⟩ := weakCT3_recognition_blocks (X := ↥Gs) (n := m + 2)
    (by omega) (U := fun i => (U i).subgroupOf Gs)
    (fun i j hij x hx y hy => Subtype.ext (hcomm i j hij x.1 hx y.1 hy))
    (fun i j hj => by
      obtain ⟨W, hW⟩ := hpair i j hj
      exact ⟨W.subgroupOf Gs, WeakCT.LinearBlockStandardPair.of_ringEquiv e
        (linearBlockStandardPair_subgroupOf
          ((linearBlockStandardPair_le_sup hW).trans (sup_le (hUle i) (hUle j))) hW)⟩)
    (iSup_subgroupOf_self U)
  let ψ : SL(m + 1 + 2, K) →* G := Gs.subtype.comp (ψ'.comp (slEquiv e (m + 1 + 2)).toMonoidHom)
  refine ⟨ψ, ?_, ?_, ?_⟩
  · intro x hx
    have h1 : ψ' (slEquiv e (m + 1 + 2) x) = 1 :=
      Subtype.ext (MonoidHom.mem_ker.mp hx)
    have h2 := hker h1
    rw [Subgroup.mem_center_iff]
    intro y
    apply (slEquiv e (m + 1 + 2)).injective
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.mp h2 _
  · have h1 : (ψ'.comp (slEquiv e (m + 1 + 2)).toMonoidHom).range = ⊤ :=
      MonoidHom.range_eq_top.mpr (hsurj.comp (slEquiv e (m + 1 + 2)).surjective)
    show (Gs.subtype.comp (ψ'.comp (slEquiv e (m + 1 + 2)).toMonoidHom)).range = Gs
    rw [MonoidHom.range_comp, h1, Subgroup.map_top, Subgroup.range_subtype]
  · intro i
    have hs : (blockSL2 K (m + 2) i).range.map (slEquiv e (m + 1 + 2)).toMonoidHom =
        (blockSL2 F3 (m + 2) i).range := by
      ext x
      constructor
      · rintro ⟨_, ⟨A, rfl⟩, rfl⟩
        exact ⟨slEquiv e 2 A, (map_blockSL e.toRingHom _ A).symm⟩
      · rintro ⟨B, rfl⟩
        obtain ⟨A, rfl⟩ := (slEquiv e 2).surjective B
        exact ⟨_, ⟨A, rfl⟩, map_blockSL e.toRingHom _ A⟩
    show (blockSL2 K (m + 2) i).range.map
      (Gs.subtype.comp (ψ'.comp (slEquiv e (m + 1 + 2)).toMonoidHom)) = U i
    rw [← Subgroup.map_map, ← Subgroup.map_map, hs, hblk i, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr (hUle i)]

end CFSG.ClassicalInvolution.Q3.Q3W
