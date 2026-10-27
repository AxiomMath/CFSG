module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUAlignMain

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply unitaryInvolution_involutive)

section Detect

variable {N : ℕ} {F : Type} [Field F] {σ : F ≃+* F}

theorem exists_ctua_heis_two (hσ : ∀ c, σ (σ c) = c) (p : Fin N) {a b : F}
    (hab : b + σ b + σ a * a = 0) :
    ∃ x : SU σ (2 * N + 1), (∀ R : Finset (Fin N), p ∉ R → x ∈ ctuBlock σ 1 R) ∧
      ((x : GL (Fin (2 * N + 1)) F) : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) F)
        (ctuCoord N 1 (Sum.inl (Sum.inl p))) (ctuCoord N 1 (Sum.inr 0)) = a ∧
      ((x : GL (Fin (2 * N + 1)) F) : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) F)
        (ctuCoord N 1 (Sum.inl (Sum.inl p))) (ctuCoord N 1 (Sum.inl (Sum.inr p))) = b := by
  set i := ctuCoord N 1 (Sum.inl (Sum.inl p)) with hi
  set k := ctuCoord N 1 (Sum.inr 0) with hk
  have hir : i ≠ Fin.rev i := ctuCoord_inl_ne_rev le_rfl _
  have hik : i ≠ k := by
    rw [hi, hk, Ne, (ctuCoord N 1).injective.eq_iff]
    simp
  have hkr : Fin.rev k = k := ctuCoord_inr_rev le_rfl 0
  have hri : Fin.rev i = ctuCoord N 1 (Sum.inl (Sum.inr p)) := by
    rw [hi, ctuCoord_rev le_rfl, ctuPar_inl, par_inl]
  have h1 : heisenbergMatrix σ i k a b * heisenbergMatrix σ i k (-a) (-b - a * σ a) = 1 := by
    rw [heisenbergMatrix_mul σ hir hik hkr, map_neg, add_neg_cancel,
      show b + (-b - a * σ a) - a * -σ a = 0 by ring, heisenbergMatrix_zero]
  have h2 : heisenbergMatrix σ i k (-a) (-b - a * σ a) * heisenbergMatrix σ i k a b = 1 := by
    rw [heisenbergMatrix_mul σ hir hik hkr, neg_add_cancel,
      show -b - a * σ a + b - -a * σ a = 0 by ring, heisenbergMatrix_zero]
  refine ⟨⟨⟨heisenbergMatrix σ i k a b, heisenbergMatrix σ i k (-a) (-b - a * σ a), h1, h2⟩,
    det_heisenbergMatrix σ hir hik hkr a b, heisenbergMatrix_isometry σ hσ hir hik hkr hab⟩,
    fun R hpR => ?_, ?_, ?_⟩
  · rw [mem_ctuBlock]
    intro c d hcd
    have hiR : i ∉ ctuPlanes 1 R := fun h => hpR (by simpa using ctuCoord_mem_ctuPlanes.1 h)
    have hirR : Fin.rev i ∉ ctuPlanes 1 R := by
      rw [hri]
      exact fun h => hpR (by simpa using ctuCoord_mem_ctuPlanes.1 h)
    have hkR : k ∉ ctuPlanes 1 R := fun h => not_inPlanes_inr R 0 (ctuCoord_mem_ctuPlanes.1 h)
    change heisenbergMatrix σ i k a b c d = _
    rw [heisenbergMatrix, Matrix.add_apply, Matrix.sub_apply, Matrix.add_apply,
      ctua_apply_of_plane hcd hiR hkR, ctua_apply_of_plane hcd hkR hirR,
      ctua_apply_of_plane hcd hiR hirR, add_zero, sub_zero, add_zero]
  · change heisenbergMatrix σ i k a b i k = a
    rw [heisenbergMatrix, Matrix.add_apply, Matrix.sub_apply, Matrix.add_apply, one_apply_ne hik,
      single_apply_same, single_apply_of_row_ne (Ne.symm hik),
      single_apply_of_col_ne _ _ (fun h => hik (by rw [← Fin.rev_rev i, h, hkr])), zero_add,
      sub_zero, add_zero]
  · change heisenbergMatrix σ i k a b i (ctuCoord N 1 (Sum.inl (Sum.inr p))) = b
    rw [← hri, heisenbergMatrix, Matrix.add_apply, Matrix.sub_apply, Matrix.add_apply,
      one_apply_ne hir, single_apply_of_col_ne _ _ (fun h => hik (by rw [← Fin.rev_rev i, ← h,
        hkr])), single_apply_of_row_ne (Ne.symm hik), single_apply_same, zero_add, sub_zero,
      zero_add]

theorem ctuaTwist_eq_one_of_fix_odd [CharP F 2] {hσ : ∀ c, σ (σ c) = c} {ν : Fˣ}
    (hν : σ ν * ν = 1) (b : Bool) (htr : ∃ c : F, c + σ c + 1 = 0) {R : Finset (Fin N)}
    (hR : 1 ≤ Rᶜ.card) (h : ∀ x ∈ ctuBlock σ 1 R, ctuaTwist le_rfl σ hσ ν hν b x = x) :
    ctuaTwist (N := N) le_rfl σ hσ ν hν b = 1 := by
  obtain ⟨p, hp⟩ := Finset.card_pos.1 (by omega : 0 < Rᶜ.card)
  have hpR : p ∉ R := Finset.mem_compl.1 hp
  obtain ⟨c, hc⟩ := htr
  obtain ⟨x, hxR, hx1, hx2⟩ := exists_ctua_heis_two hσ p (a := 1) (b := c)
    (by rw [map_one, one_mul]; exact hc)
  cases b
  · have h1 := congrArg (fun z : SU σ (2 * N + 1) => ((z : GL (Fin (2 * N + 1)) F) :
      Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) F) (ctuCoord N 1 (Sum.inl (Sum.inl p)))
        (ctuCoord N 1 (Sum.inr 0))) (h x (hxR R hpR))
    rw [ctuaTwist_apply_apply, Bool.cond_false, hx1, ctuaTorEntry_inl, ctuaTorEntry_inr, one_mul,
      one_mul] at h1
    have hν1 : ν = 1 := inv_eq_one.1 (Units.ext h1)
    subst hν1
    exact ctuaTwist_false_eq_one hν ctuaTorGL_one
  · exfalso
    have h1 := congrArg (fun z : SU σ (2 * N + 1) => ((z : GL (Fin (2 * N + 1)) F) :
      Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) F) (ctuCoord N 1 (Sum.inl (Sum.inl p)))
        (ctuCoord N 1 (Sum.inl (Sum.inr p)))) (h x (hxR R hpR))
    rw [ctuaTwist_apply_apply, Bool.cond_true, hx2, ctuaTorEntry_inl, ctuaTorEntry_inl, one_mul,
      mul_one] at h1
    rw [h1, CharTwo.add_self_eq_zero, zero_add] at hc
    exact one_ne_zero hc

end Detect

section Align

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {N ε : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} {hε : ε ≤ 1}
  {ι : K →+* F} {hι : ∀ c, unitaryInvolution F 2 f (ι c) = ι c} {e : L ≃* StatedSp N K}

theorem exists_ctuParamAgree_of_triv (hKc : Nat.card K = 2 ^ f) (hF : Nat.card F = (2 ^ f) ^ 2)
    (hf : 2 ≤ f) (hN : 4 ≤ N)
    (htriv : ∀ (ν : Fˣ) (hν : unitaryInvolution F 2 f ν * ν = 1) (b : Bool) (o k l : Fin N),
      (∀ y ∈ ctuBlock (unitaryInvolution F 2 f) ε ({o, k, l} : Finset (Fin N)),
        ctuaTwist hε (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) ν hν b y = y) →
      ctuaTwist (N := N) hε (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) ν hν b = 1)
    (P : ∀ k : Fin N, CtuParam ε hε (unitaryInvolution F 2 f) ι hι e k) :
    ∃ Q : ∀ k : Fin N, CtuParam ε hε (unitaryInvolution F 2 f) ι hι e k, CtuParamAgree Q := by
  classical
  obtain ⟨o⟩ : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  have hex : ∀ k : Fin N, ∃ R : CtuParam ε hε (unitaryInvolution F 2 f) ι hι e k,
      ∀ (x : SU (unitaryInvolution F 2 f) (2 * N + ε))
        (hx : x ∈ ctuBlock (unitaryInvolution F 2 f) ε ({k, o} : Finset (Fin N))),
        R.Φ ⟨x, ctuBlock_pair_le_left _ k o hx⟩ = (P o).Φ ⟨x, ctuBlock_pair_le_right _ k o hx⟩ := by
    intro k
    by_cases hko : k = o
    · subst hko
      exact ⟨P k, fun x hx => rfl⟩
    · obtain ⟨ν, hν, b, h1⟩ := (P k).exists_twist_of_overlap hKc hF hf hN hko (P o)
      have hT := ctuaTwist_admissible (N := N) (hε := hε) (ι := ι) (hι := hι)
        (hσ := unitaryInvolution_involutive hF) hν b
      refine ⟨(P k).twistBy hT.inv, fun x hx => ?_⟩
      rw [CtuParam.twistBy_Φ_apply]
      have hx' : (ctuaTwist hε (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) ν hν
          b)⁻¹ x ∈ ctuBlock (unitaryInvolution F 2 f) ε ({k, o} : Finset (Fin N)) :=
        (hT.inv.mem_iff _ x).2 hx
      refine (h1 _ hx').trans (congrArg (P o).Φ (Subtype.ext ?_))
      change (ctuaTwist hε (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) ν hν b)
        ((ctuaTwist hε (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) ν hν b)⁻¹ x) = x
      rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  choose Q hQ using hex
  refine ⟨Q, fun k l x hx hx' => ?_⟩
  by_cases hkl : k = l
  · subst hkl
    rfl
  have hxkl := mem_ctuBlock_pair hx hx'
  have hagreeo : ∀ {m : Fin N} (y : SU (unitaryInvolution F 2 f) (2 * N + ε))
      (hy : y ∈ ctuBlock (unitaryInvolution F 2 f) ε ({m} : Finset (Fin N)))
      (hy' : y ∈ ctuBlock (unitaryInvolution F 2 f) ε ({o} : Finset (Fin N))),
      (Q m).Φ ⟨y, hy⟩ = (P o).Φ ⟨y, hy'⟩ :=
    fun y hy hy' => hQ _ y (mem_ctuBlock_pair hy hy')
  by_cases hko : k = o
  · subst hko
    exact (hagreeo x hx hx).trans (hagreeo x hx' hx).symm
  by_cases hlo : l = o
  · subst hlo
    exact (hagreeo x hx hx').trans (hagreeo x hx' hx').symm
  obtain ⟨ν, hν, b, h1⟩ := (Q k).exists_twist_of_overlap hKc hF hf hN hkl (Q l)
  have hT := ctuaTwist_admissible (N := N) (hε := hε) (ι := ι) (hι := hι)
    (hσ := unitaryInvolution_involutive hF) hν b
  set T := ctuaTwist hε (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) ν hν b
    with hTdef
  have hsub : ∀ m ∈ ({o, k, l} : Finset (Fin N)),
      ctuBlock (unitaryInvolution F 2 f) ε ({o, k, l} : Finset (Fin N)) ≤
        ctuBlock (unitaryInvolution F 2 f) ε ({m} : Finset (Fin N)) :=
    fun m hm => ctuBlock_anti (Finset.singleton_subset_iff.2 hm)
  have hfix : ∀ y ∈ ctuBlock (unitaryInvolution F 2 f) ε ({o, k, l} : Finset (Fin N)), T y = y := by
    intro y hy
    have hTy : T y ∈ ctuBlock (unitaryInvolution F 2 f) ε ({o, k, l} : Finset (Fin N)) :=
      (hT.mem_iff _ y).2 hy
    have hyk := hsub k (by simp) hy
    have hyl := hsub l (by simp) hy
    have hyo := hsub o (by simp) hy
    have h2 := h1 y (mem_ctuBlock_pair hyk hyl)
    rw [hagreeo y hyk hyo, hagreeo (T y) (hsub l (by simp) hTy) (hsub o (by simp) hTy)] at h2
    have h3 := (P o).injOn_ctuBlock hF (by omega) (Ne.symm hko) (x := ⟨y, hyo⟩)
      (y := ⟨T y, hsub o (by simp) hTy⟩) hyk (hsub k (by simp) hTy) h2
    exact (congrArg (fun w : ctuBlock (unitaryInvolution F 2 f) ε ({o} : Finset (Fin N)) =>
      (w : SU (unitaryInvolution F 2 f) (2 * N + ε))) h3).symm
  have hT1 : T = 1 := htriv ν hν b o k l hfix
  have hTx : T x = x := by rw [hT1, MulAut.one_apply]
  exact (h1 x hxkl).trans (congrArg (Q l).Φ (Subtype.ext hTx))

theorem exists_ctuParamAgree_odd_four (hKc : Nat.card K = 2 ^ f)
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f) (hN : 4 ≤ N)
    (P : ∀ k : Fin N, CtuParam 1 le_rfl (unitaryInvolution F 2 f) ι hι e k) :
    ∃ Q : ∀ k : Fin N, CtuParam 1 le_rfl (unitaryInvolution F 2 f) ι hι e k, CtuParamAgree Q := by
  refine exists_ctuParamAgree_of_triv hKc hF hf hN (fun ν hν b o k l hfix => ?_) P
  have hcard : 1 ≤ ({o, k, l} : Finset (Fin N))ᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin]
    have := Finset.card_le_three (a := o) (b := k) (c := l)
    omega
  exact ctuaTwist_eq_one_of_fix_odd hν b (exists_add_unitaryInvolution_add_one_ctua hF) hcard hfix

end Align

end CFSG.SeitzReduction.SymplecticPilot
