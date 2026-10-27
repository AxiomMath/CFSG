module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma137

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

namespace Lemma138

@[expose] def InputI27102 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → p ≠ 2 → ∀ (J B : Subgroup X),
    ((∃ k : ℕ, 5 ≤ k * p ∧ IsAltType (k * p) J) ∨ (∃ k : ℕ, IsAltType (k * p + 2) J) ∨
      (∃ n : ℕ, Nonempty (↥J ≃* ↥(⁅(StatedSp n (ZMod 2)), (StatedSp n (ZMod 2))⁆ : Subgroup
        (GL (Fin n ⊕ Fin n) (ZMod 2))))) ∨
      (∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧ IsOmegaTwo ε (n + 1) J ∧ HasFixedPointFreeOrder ε n p)) →
    IsElemAbelian p B → B ≤ Subgroup.normalizer (J : Set X) →
    (B ⊓ J) ⊔ (B ⊓ Subgroup.centralizer (J : Set X)) = B →
    (B ⊓ J) ⊓ (B ⊓ Subgroup.centralizer (J : Set X)) = ⊥ →
    CFSG.Open.pRank p (B ⊓ J) = CFSG.Open.pRank p J →
    4 ≤ CFSG.Open.pRank p B →
    J = ⨆ (U : Subgroup X) (_ : U ≤ B) (_ : 2 ≤ CFSG.Open.pRank p U), J ⊓ Subgroup.normalizer (U : Set X)

@[expose] def InputI27111 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → p ≠ 2 → ∀ (L B : Subgroup X),
    IsKGroup ↥L → CFSG.Open.IsQuasisimple ↥L → IsElemAbelian p B →
    B ≤ Subgroup.normalizer (L : Set X) →
    (∀ A : Subgroup X, A ≤ B ⊔ L → IsElemAbelian p A → Nat.card A ≤ Nat.card B) →
    4 ≤ CFSG.Open.pRank p B →
    ∀ J0 : Subgroup X,
      IsComponentOf J0 (⨆ (U : Subgroup X) (_ : U ≤ B) (_ : 2 ≤ CFSG.Open.pRank p U),
        L ⊓ Subgroup.normalizer (U : Set X)) →
      ((∃ k : ℕ, 5 ≤ k * p ∧ IsAltType (k * p) J0) ∨ (∃ k : ℕ, IsAltType (k * p + 2) J0) ∨
        (∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧ HasFixedPointFreeOrder ε n p ∧
          Nonempty (↥J0 ≃* ↥(⁅(StatedSp n (ZMod 2)), (StatedSp n (ZMod 2))⁆ : Subgroup
            (GL (Fin n ⊕ Fin n) (ZMod 2))))) ∨
        (∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧ IsOmegaTwo ε (n + 1) J0 ∧
          HasFixedPointFreeOrder ε n p)) →
      ¬ (p = 3 ∧ IsAltType 5 J0) →
      (∃ E : Subgroup X, E ≤ B ∧ Nat.card B ≤ p ^ 2 * Nat.card E ∧
        GLAPLayer p (J0 ⊓ Subgroup.centralizer (E : Set X)) ≠ ⊥) →
      L = ⨆ (U : Subgroup X) (_ : U ≤ B) (_ : 2 ≤ CFSG.Open.pRank p U),
        L ⊓ Subgroup.normalizer (U : Set X)

@[expose] def InputI226 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → ∀ (Y Qa : Subgroup G),
    GLAPLayer p Y = Y → GLALayer Y = Y → IsPGroup p ↥Qa →
    Qa ≤ Subgroup.normalizer (Y : Set G) →
    ∀ J : Subgroup G, GLAPComponent p (GLAPLayer p (Y ⊓ Subgroup.centralizer (Qa : Set G))) J →
      ∃ S : Set (Subgroup G), (∀ C ∈ S, IsComponentOf C Y) ∧
        (∀ g ∈ Qa, ∀ C ∈ S, GLBConj g C ∈ S) ∧
        (⨆ g ∈ Y, GLBConj g J) = ⨆ C ∈ S, C ∧
        ∀ S' : Set (Subgroup G), S' ⊆ S → (∀ g ∈ Qa, ∀ C ∈ S', GLBConj g C ∈ S') →
          S'.Nonempty → ⨆ C ∈ S', C = ⨆ C ∈ S, C

@[expose] def InputI181 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → IsKGroup X →
    ∀ Q : Subgroup X, IsPGroup p ↥Q →
      GLAPLayer p (Subgroup.centralizer (Q : Set X)) ≤ GLAPLayer p ⊤

@[expose] def InputI113p : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsKGroup X → ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ B : Subgroup X, GLAIsBmax p B → ∀ L : Subgroup X, GLAPComponent p ⊤ L →
      ¬ B ≤ Subgroup.normalizer (L : Set X) →
      p ∣ Nat.card (Subgroup.center (↥L ⧸ GLAPPrimeCore p ↥L))

@[expose] def gammaTwoIn {X : Type} [Group X] [Finite X] (p : ℕ) (B J : Subgroup X) : Subgroup X :=
  ⨆ (U : Subgroup X) (_ : U ≤ B) (_ : 2 ≤ CFSG.Open.pRank p U), J ⊓ Subgroup.normalizer (U : Set X)

theorem glaPLayer_le_self {X : Type} [Group X] [Finite X] (p : ℕ) (Z : Subgroup X) :
    GLAPLayer p Z ≤ Z :=
  sSup_le fun L hL => hL.1

theorem le_of_simple_inf {Q : Type} [Group Q] {K N : Subgroup Q} (hKs : IsSimpleGroup ↥K)
    (hN : ∀ k ∈ K, ∀ x ∈ N, k * x * k⁻¹ ∈ N) {w : Q} (hwK : w ∈ K) (hwN : w ∈ N) (hw1 : w ≠ 1) :
    K ≤ N := by
  let M : Subgroup ↥K := N.subgroupOf K
  haveI : M.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := hN (g : Q) g.2 (n : Q) hn
    simpa using this⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M with h | h
  · exfalso
    have hmem : (⟨w, hwK⟩ : ↥K) ∈ M := Subgroup.mem_subgroupOf.2 hwN
    rw [h, Subgroup.mem_bot] at hmem
    exact hw1 (congrArg Subtype.val hmem)
  · intro k hk
    have hkM : (⟨k, hk⟩ : ↥K) ∈ M := by rw [h]; exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 hkM

theorem isQuasisimple_of_simple_nonabelian {H : Type} [Group H] [IsSimpleGroup H]
    (hnc : ¬ IsMulCommutative H) : CFSG.Open.IsQuasisimple H := by
  refine ⟨?_, ?_⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator H) with h | h
    · exfalso
      apply hnc
      refine ⟨⟨fun a b => ?_⟩⟩
      have hc : (⊤ : Subgroup H) ≤ Subgroup.centralizer ((⊤ : Subgroup H) : Set H) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
      have ha : a ∈ Subgroup.centralizer ((⊤ : Subgroup H) : Set H) := hc (Subgroup.mem_top a)
      exact ((Subgroup.mem_centralizer_iff.1 ha) b (Subgroup.mem_top b)).symm
    · exact h
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center H) with h | h
    · exact MulEquiv.isSimpleGroup ((QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot)
    · exfalso
      apply hnc
      refine ⟨⟨fun a b => ?_⟩⟩
      have ha : a ∈ Subgroup.center H := h ▸ Subgroup.mem_top a
      exact ((Subgroup.mem_center_iff.1 ha) b).symm

theorem mem_iSup_conj {Q : Type} [Group Q] {Y W : Subgroup Q} {y : Q} (hy : y ∈ Y) {x : Q}
    (hx : x ∈ ⨆ g ∈ Y, GLBConj g W) : y * x * y⁻¹ ∈ ⨆ g ∈ Y, GLBConj g W := by
  have hle : (⨆ g ∈ Y, GLBConj g W) ≤ GLBConj y (⨆ g ∈ Y, GLBConj g W) := by
    refine iSup₂_le fun g hg => ?_
    have h1 : GLBConj g W = GLBConj y (GLBConj (g * y⁻¹) W) := by
      rw [gLBConj_gLBConj]
      simp
    rw [h1]
    exact gLBConj_mono y (le_iSup₂ (f := fun g (_ : g ∈ Y) => GLBConj g W) (g * y⁻¹)
      (Y.mul_mem hg (Y.inv_mem hy)))
  exact mem_gLBConj.1 (hle hx)

theorem core_isComponent
    {Q : Type} [Group Q] [Finite Q] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hI2710 : InputI27102) (hI2711 : InputI27111) (hI226 : InputI226)
    {Y : Subgroup Q} (hYn : Y.Normal) (hYL : GLAPLayer p Y = Y) (hYA : GLALayer Y = Y)
    {B Ft K M' W : Subgroup Q}
    (hB : IsElemAbelian p B) (hB4 : 4 ≤ CFSG.Open.pRank p B)
    (hmax : ∀ A : Subgroup Q, IsElemAbelian p A → Nat.card A ≤ Nat.card B)
    (hFB : Ft ≤ B) (hFi : Nat.card B ≤ p ^ 2 * Nat.card Ft)
    (hKs : IsSimpleGroup ↥K) (hKnc : ¬ IsMulCommutative ↥K)
    (hKJ : (∃ k : ℕ, 5 ≤ k * p ∧ IsAltType (k * p) K) ∨ (∃ k : ℕ, IsAltType (k * p + 2) K) ∨
      (∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧ HasFixedPointFreeOrder ε n p ∧
        Nonempty (↥K ≃* ↥(⁅(StatedSp n (ZMod 2)), (StatedSp n (ZMod 2))⁆ : Subgroup
          (GL (Fin n ⊕ Fin n) (ZMod 2))))) ∨
      (∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧ IsOmegaTwo ε (n + 1) K ∧ HasFixedPointFreeOrder ε n p))
    (hKn3 : ¬ (p = 3 ∧ IsAltType 5 K))
    (hKB : B ≤ Subgroup.normalizer (K : Set Q))
    (hKsplit : (B ⊓ K) ⊔ (B ⊓ Subgroup.centralizer (K : Set Q)) = B)
    (hKint : (B ⊓ K) ⊓ (B ⊓ Subgroup.centralizer (K : Set Q)) = ⊥)
    (hKrk : CFSG.Open.pRank p (B ⊓ K) = CFSG.Open.pRank p K)
    (hKM : IsSubnormal K M')
    (hΓM : ∀ U : Subgroup Q, U ≤ B → 2 ≤ CFSG.Open.pRank p U →
      Subgroup.normalizer (U : Set Q) ≤ M')
    (hNI : ∀ C : Subgroup Q, IsComponentOf C ⊤ → ¬ B ≤ Subgroup.normalizer (C : Set Q) → C ≤ M')
    (hKG : ∀ C : Subgroup Q, IsComponentOf C ⊤ → IsKGroup ↥C)
    (hLK : GLAPLayer p (K ⊓ Subgroup.centralizer (Ft : Set Q)) ≠ ⊥)
    (hW : GLAPComponent p (GLAPLayer p (Y ⊓ Subgroup.centralizer (Ft : Set Q))) W)
    (hWK : W ≤ K) (hWne : W ≠ ⊥) :
    IsComponentOf K ⊤ := by
  haveI := hKs
  have hBp : IsPGroup p ↥B := Lemma137.isPGroup_of_isElemAbelian hB
  have hFp : IsPGroup p ↥Ft := IsPGroup.to_le hBp hFB
  have hFN : Ft ≤ Subgroup.normalizer (Y : Set Q) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hWY : W ≤ Y := by
    have h1 : W ≤ GLAPLayer p (Y ⊓ Subgroup.centralizer (Ft : Set Q)) := hW.1
    exact h1.trans ((glaPLayer_le_self p _).trans inf_le_left)
  obtain ⟨⟨w, hwW⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hWne
  have hw1' : w ≠ 1 := fun h => hw1 (Subtype.ext h)
  have hKY : K ≤ Y :=
    le_of_simple_inf hKs (fun k _ x hx => Subgroup.Normal.conj_mem hYn x hx k)
      (hWK hwW) (hWY hwW) hw1'
  have hWX : W ≤ ⨆ g ∈ Y, GLBConj g W := by
    have h1 := le_iSup₂ (f := fun g (_ : g ∈ Y) => GLBConj g W) (1 : Q) Y.one_mem
    rw [gLBConj_one] at h1
    exact h1
  have hKX : K ≤ ⨆ g ∈ Y, GLBConj g W :=
    le_of_simple_inf hKs (fun k hk x hx => mem_iSup_conj (hKY hk) hx)
      (hWK hwW) (hWX hwW) hw1'
  obtain ⟨S, hS1, -, hS3, hS4⟩ := hI226 Q p hp Y Ft hYL hYA hFp hFN W hW
  have hCtop : ∀ C ∈ S, IsComponentOf C ⊤ := fun C hC =>
    ⟨le_top, isSubnormal_trans' (hS1 C hC).2.1 (isSubnormal_of_normal hYn), (hS1 C hC).2.2⟩
  have hSM : ∀ C ∈ S, C ≤ M' := by
    intro C hC
    by_contra hCM
    have hBC : B ≤ Subgroup.normalizer (C : Set Q) := by
      by_contra hBC
      exact hCM (hNI C (hCtop C hC) hBC)
    have hfix : ∀ g ∈ Ft, GLBConj g C = C := by
      intro g hg
      ext x
      rw [mem_gLBConj]
      exact (Subgroup.mem_normalizer_iff.1 (hBC (hFB hg)) x).symm
    have hsing : C = ⨆ C' ∈ S, C' := by
      have h1 := hS4 ({C} : Set (Subgroup Q)) (Set.singleton_subset_iff.2 hC)
        (fun g hg C' hC' => by
          rw [Set.mem_singleton_iff.1 hC', hfix g hg]
          exact Set.mem_singleton C)
        (Set.singleton_nonempty C)
      simpa using h1
    have hKC : K ≤ C := by
      calc K ≤ ⨆ C' ∈ S, C' := hKX.trans (le_of_eq hS3)
        _ = C := hsing.symm
    have hKΓ : K ≤ gammaTwoIn p B C := by
      have hKeq := hI2710 Q p hp hp2 K B (Lemma137.type2710_of_fp hKJ) hB hKB hKsplit hKint hKrk hB4
      unfold gammaTwoIn
      refine le_trans (le_of_eq hKeq) (iSup_mono fun U => iSup_mono fun hU =>
        iSup_mono fun hr => ?_)
      exact inf_le_inf_right _ hKC
    have hΓle : gammaTwoIn p B C ≤ M' := by
      unfold gammaTwoIn
      exact iSup_le fun U => iSup_le fun hU => iSup_le fun hr =>
        (inf_le_right).trans (hΓM U hU hr)
    have hKsub : IsSubnormal K (gammaTwoIn p B C) := isSubnormal_of_le_of_le hKM hKΓ hΓle
    have hKcomp : IsComponentOf K (gammaTwoIn p B C) :=
      ⟨hKΓ, hKsub, isQuasisimple_of_simple_nonabelian hKnc⟩
    have hGam := hI2711 Q p hp hp2 C B (hKG C (hCtop C hC)) (hCtop C hC).2.2 hB hBC
      (fun A _ hA => hmax A hA) hB4 K hKcomp hKJ hKn3 ⟨Ft, hFB, hFi, hLK⟩
    exact hCM (hGam.le.trans hΓle)
  have hXM : (⨆ C ∈ S, C) ≤ M' := iSup₂_le fun C hC => hSM C hC
  have hKX' : K ≤ ⨆ C ∈ S, C := hKX.trans (le_of_eq hS3)
  have hKsubX : IsSubnormal K (⨆ C ∈ S, C) := isSubnormal_of_le_of_le hKM hKX' hXM
  have hXtop : IsSubnormal (⨆ C ∈ S, C) ⊤ := isSubnormal_iSup_components S hCtop
  exact ⟨le_top, isSubnormal_trans' hKsubX hXtop, isQuasisimple_of_simple_nonabelian hKnc⟩

end Lemma138

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
