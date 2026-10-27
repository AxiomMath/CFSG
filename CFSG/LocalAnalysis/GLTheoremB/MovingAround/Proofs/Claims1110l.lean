module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.ClassicalEA
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N5GammaOmega

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110l

open Module CFSG.Open
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.ClassicalEA

section Blocks

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open QuadraticMap

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem exists_blocks_of_isometry (hQ : (polarBilin Q).Nondegenerate) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) :
    ∀ (n : ℕ) (ℓ : V ≃ₗ[ZMod 2] V), finrank (ZMod 2) (commSp ℓ) = n →
      ℓ ∈ TauCeti.QuadraticMap.orthogonalGroup Q → ℓ ^ p = 1 →
      ∃ F : Subgroup (V ≃ₗ[ZMod 2] V), F ≤ TauCeti.QuadraticMap.orthogonalGroup Q ∧
        IsElemAbelian p F ∧ ℓ ∈ F ∧ HasBlocks (polarBilin Q) (commSp ℓ) F p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv
  have hBs := polarBilin_symm Q
  have hG := isRestrClosed_orthogonalGroup Q
  have hpo : Odd p := hp.odd_of_ne_two hp2
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ℓ hn hℓO hℓp
  have hℓiso : IsIsom (polarBilin Q) ℓ := isIsom_of_mem hℓO
  by_cases hℓ1 : ℓ = 1
  · subst hℓ1
    refine ⟨⊥, bot_le, CFSG.SectionRank.isElemAbelian_bot p, one_mem _, ?_⟩
    refine ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0, ?_, ?_⟩
    · rw [Set.range_eq_empty, Subgroup.closure_empty]
    · rw [Subgroup.card_bot, pow_zero]
  set U := commSp ℓ with hU
  have hUnd : Nondeg (polarBilin Q) U := nondeg_commSp hBs hQ hℓiso hpo hℓp
  have hU0 : U ≠ ⊥ := commSp_ne_bot hℓ1
  have hUℓ : ∀ u ∈ U, ℓ u ∈ U := fun u hu => commSp_invariant rfl hu
  have hUfix : ∀ u ∈ U, ℓ u = u → u = 0 := fun u hu h => commSp_fpf hpo hℓp hu h
  let InS : Submodule (ZMod 2) V → Prop := fun W => W ≤ U ∧ W ≠ ⊥ ∧ Nondeg (polarBilin Q) W ∧
    ∀ w ∈ W, ℓ w ∈ W
  have hex : ∃ d, ∃ W, InS W ∧ finrank (ZMod 2) W = d := ⟨_, U, ⟨le_rfl, hU0, hUnd, hUℓ⟩, rfl⟩
  obtain ⟨W, hWS, hWd⟩ := Nat.find_spec hex
  have hmin : ∀ W', InS W' → W' ≤ W → W' = W := fun W' hW' hle =>
    Submodule.eq_of_le_of_finrank_le hle (hWd ▸ Nat.find_min' hex ⟨W', hW', rfl⟩)
  obtain ⟨hWU, hW0, hWnd, hWℓ⟩ := hWS
  have hWc : IsCompl W (LinearMap.BilinForm.orthogonal (polarBilin Q) W) := isCompl_of_nondeg hBs hWnd
  have hWperpℓ : ∀ x ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) W, ℓ x ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) W :=
    fun x hx => apply_mem_orth_of_invariant hBs hℓiso hWℓ hx
  set b := glueE hWc ℓ hWℓ with hb
  have hbW : ∀ w ∈ W, b w = ℓ w := fun w hw => glueE_left hWc _ _ hw
  have hbW' : ∀ x ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) W, b x = x := fun x hx => glueE_right hWc _ _ hx
  have hbWmem : ∀ w ∈ W, b w ∈ W := fun w hw => (hbW w hw).symm ▸ hWℓ w hw
  have hbO : b ∈ TauCeti.QuadraticMap.orthogonalGroup Q := hG.2 ℓ hℓO W hWnd hWℓ b hbW hbW'
  have hbp : b ^ p = 1 := by
    rw [hb, glueE_pow]
    refine linearEquiv_ext_of_isCompl hWc (fun w hw => ?_) (fun x hx => ?_)
    · rw [glueE_left hWc _ _ hw, hℓp]
    · rw [glueE_right hWc _ _ hx]; rfl
  have hbℓ : b * ℓ = ℓ * b := by
    refine linearEquiv_ext_of_isCompl hWc (fun w hw => ?_) (fun x hx => ?_)
    · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hbW _ (hWℓ w hw), hbW w hw]
    · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hbW' _ (hWperpℓ x hx), hbW' x hx]
  have hblock : IsBlock (polarBilin Q) b W := by
    refine ⟨hWnd, hW0, hbWmem, hbW', fun w hw hbw => ?_,
      fun W' hle hW'0 hW'nd hW'b => ?_⟩
    · exact hUfix w (hWU hw) ((hbW w hw).symm.trans hbw)
    · refine hmin W' ⟨hle.trans hWU, hW'0, hW'nd, fun w hw => ?_⟩ hle
      rw [← hbW w (hle hw)]
      exact hW'b w hw
  have hbptw : b ∉ ptw W := fun h => by
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    exact hw0 (hUfix w (hWU hw) ((hbW w hw).symm.trans (h w hw)))
  have hb1 : b ≠ 1 := fun h => hbptw (h ▸ one_mem _)
  set ℓ' := b⁻¹ * ℓ with hℓ'
  have hℓ'O : ℓ' ∈ TauCeti.QuadraticMap.orthogonalGroup Q := mul_mem (inv_mem hbO) hℓO
  have hℓ'p : ℓ' ^ p = 1 := by
    have hc : Commute b⁻¹ ℓ := (Commute.inv_left hbℓ)
    rw [hℓ', hc.mul_pow, inv_pow, hbp, inv_one, one_mul, hℓp]
  have hℓ'W : ∀ w ∈ W, ℓ' w = w := fun w hw => by
    rw [hℓ', LinearEquiv.mul_apply]
    exact inv_apply_eq_of_apply_eq (hbW w hw)
  have hℓ'W' : ∀ x ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) W, ℓ' x = ℓ x := fun x hx => by
    rw [hℓ', LinearEquiv.mul_apply]
    exact inv_apply_eq_of_apply_eq (hbW' _ (hWperpℓ x hx))
  have hU'le : commSp ℓ' ≤ U ⊓ LinearMap.BilinForm.orthogonal (polarBilin Q) W := by
    intro y hy
    obtain ⟨v, rfl⟩ := mem_commSp_iff.1 hy
    obtain ⟨w, hw, x, hx, rfl⟩ := exists_add_of_isCompl hWc v
    have e1 : ℓ' (w + x) - (w + x) = ℓ x - x := by
      rw [map_add, hℓ'W w hw, hℓ'W' x hx]
      abel
    rw [e1]
    exact Submodule.mem_inf.2 ⟨mem_commSp_iff.2 ⟨x, rfl⟩, Submodule.sub_mem _ (hWperpℓ x hx) hx⟩
  have hlt : finrank (ZMod 2) (commSp ℓ') < n := by
    refine lt_of_le_of_lt (Submodule.finrank_mono hU'le) ?_
    rw [← hn]
    refine Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne inf_le_left fun h => hW0 ?_)
    rw [eq_bot_iff]
    intro w hw
    have hwU' : w ∈ U ⊓ LinearMap.BilinForm.orthogonal (polarBilin Q) W := by rw [h]; exact hWU hw
    exact (Submodule.disjoint_def.1 hWnd) w hw (Submodule.mem_inf.1 hwU').2
  obtain ⟨F', hF'O, hF'ea, hℓ'F', r, b', W', hb'F', hbl', hW'U', horth', hcl', hcard'⟩ :=
    ih _ hlt ℓ' rfl hℓ'O hℓ'p
  have hW'W : ∀ i, W' i ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) W := fun i =>
    (hW'U' i).trans (hU'le.trans inf_le_right)
  have hWW' : ∀ i, W ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) (W' i) := fun i w hw y hy => by
    show polarBilin Q y w = 0
    rw [hBs]
    exact hW'W i hy w hw
  have hF'ptw : F' ≤ ptw W := by
    rw [hcl', Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact fun w hw => (hbl' i).2.2.2.1 w (hWW' i hw)
  have hcomm : ∀ f ∈ F', ∀ d ∈ Subgroup.zpowers b, f * d = d * f := by
    intro f hf d hd
    have hfiso : IsIsom (polarBilin Q) f := hG.1 f (hF'O hf)
    have h1 : f * b = b * f := by
      refine linearEquiv_ext_of_isCompl hWc (fun w hw => ?_) (fun x hx => ?_)
      · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hF'ptw hf _ (hbWmem w hw), hF'ptw hf w hw]
      · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hbW' x hx,
          hbW' _ (apply_mem_orth_of_ptw hBs hfiso (hF'ptw hf) hx)]
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hd
    exact ((Commute.zpow_right h1) j).eq
  have hinf : F' ⊓ Subgroup.zpowers b = ⊥ := by
    rw [eq_bot_iff, ← zpowers_inf_ptw_eq_bot hp hbp hbptw]
    intro z hz
    obtain ⟨hz1, hz2⟩ := Subgroup.mem_inf.1 hz
    exact Subgroup.mem_inf.2 ⟨hz2, hF'ptw hz1⟩
  refine ⟨F' ⊔ Subgroup.zpowers b, sup_le hF'O (Subgroup.zpowers_le.2 hbO),
    IsElemAbelian.sup_of_commute hF'ea (OmegaFacts2.isElemAbelian_zpowers hbp) hcomm, ?_, ?_⟩
  · have e : ℓ = b * ℓ' := by rw [hℓ', mul_inv_cancel_left]
    rw [e]
    exact mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers b)) (Subgroup.mem_sup_left hℓ'F')
  refine ⟨r + 1, (Fin.cons b b' : Fin (r + 1) → V ≃ₗ[ZMod 2] V),
    (Fin.cons W W' : Fin (r + 1) → Submodule (ZMod 2) V), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
    · exact Subgroup.mem_sup_left (hb'F' i)
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact hblock
    · exact hbl' i
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact hWU
    · exact (hW'U' i).trans (hU'le.trans inf_le_left)
  · intro i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact absurd rfl hij
      | succ j => exact hWW' j
    | succ i =>
      induction j using Fin.cases with
      | zero => exact hW'W i
      | succ j => exact horth' i j fun h => hij (by rw [h])
  · rw [Fin.range_cons, Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
      ← hcl', sup_comm]
  · rw [card_sup_of_inf_eq_bot hcomm hinf, hcard', card_zpowers_of_prime hp hbp hb1, pow_succ]

theorem exists_conj_mem_of_maxEA (hQ : (polarBilin Q).Nondegenerate) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {ℓ : V ≃ₗ[ZMod 2] V} (hℓO : ℓ ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hℓp : ℓ ^ p = 1) (E₂ : Subgroup (V ≃ₗ[ZMod 2] V))
    (hE₂O : E₂ ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hE₂ : IsElemAbelian p E₂)
    (hm₂ : ∀ F : Subgroup (V ≃ₗ[ZMod 2] V), F ≤ TauCeti.QuadraticMap.orthogonalGroup Q →
      IsElemAbelian p F → Nat.card ↥F ≤ Nat.card ↥E₂) :
    ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, g * ℓ * g⁻¹ ∈ E₂ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv
  have hBs := polarBilin_symm Q
  have hG := isRestrClosed_orthogonalGroup Q
  have hsupp : TauCeti.QuadraticMap.orthogonalGroup Q ⊓
      ptw (LinearMap.BilinForm.orthogonal (polarBilin Q) ⊤) =
        TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [LinearMap.BilinForm.orthogonal_top_eq_bot hQ, inf_eq_left]
    intro g _ x hx
    rw [(Submodule.mem_bot _).1 hx, map_zero]
  obtain ⟨F, hFO, hFea, hℓF, s, b, W, hbF, hbl, -, horth, hcl, hcard⟩ :=
    exists_blocks_of_isometry hQ hp hp2 _ ℓ rfl hℓO hℓp
  obtain ⟨r, b', W', hb'E, hbl', -, horth', -, hcard'⟩ :=
    hasBlocks_of_max hBs hQ hp hp2 hG _ ⊤ rfl (nondeg_top hBs hQ) E₂ (hE₂O.trans hsupp.symm.le) hE₂
      (fun F hF hFa => hm₂ F (hF.trans hsupp.le) hFa)
  have hsr : s ≤ r := by
    have h1 := hm₂ F hFO hFea
    rw [hcard, hcard'] at h1
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h1
  set ι : Fin s → Fin r := Fin.castLE hsr with hι
  have hιinj : Function.Injective ι := Fin.castLE_injective hsr
  have hbO : ∀ i, b i ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun i => hFO (hbF i)
  have hbp : ∀ i, b i ^ p = 1 := fun i => hFea.2 _ (hbF i)
  have hb'O : ∀ i, b' i ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun i => hE₂O (hb'E i)
  have hb'p : ∀ i, b' i ^ p = 1 := fun i => hE₂.2 _ (hb'E i)
  choose k d u u' hu hu' hsu hsu' hQu hpu hint using fun i =>
    block_comparison hQ hp hp2 (hbO i) (hbp i) (hb'O (ι i)) (hb'p (ι i)) (hbl i) (hbl' (ι i))
  have humem : ∀ i j, u i j ∈ W i := fun i j => hsu i ▸ Submodule.subset_span ⟨j, rfl⟩
  have hu'mem : ∀ i j, u' i j ∈ W' (ι i) := fun i j => hsu' i ▸ Submodule.subset_span ⟨j, rfl⟩
  have horth'' : ∀ i j, i ≠ j → W' (ι i) ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) (W' (ι j)) :=
    fun i j hij => horth' (ι i) (ι j) (hιinj.ne hij)
  have hLI := linearIndependent_sigma_of_orth (fun i => (hbl i).1) horth hu humem
  have hLI' := linearIndependent_sigma_of_orth (W := fun i => W' (ι i)) (fun i => (hbl' (ι i)).1)
    horth'' hu' hu'mem
  let e := (Fintype.equivFin (Σ i, Fin (d i))).symm
  have hpol : ∀ x y : (Σ i, Fin (d i)), polar Q (u' x.1 x.2) (u' y.1 y.2) =
      polar Q (u x.1 x.2) (u y.1 y.2) := by
    rintro ⟨i, j⟩ ⟨i', j'⟩
    by_cases hii : i = i'
    · subst hii
      exact hpu i j j'
    · have h1 : polar Q (u' i j) (u' i' j') = 0 :=
        horth'' i' i (Ne.symm hii) (hu'mem i' j') _ (hu'mem i j)
      have h2 : polar Q (u i j) (u i' j') = 0 :=
        horth i' i (Ne.symm hii) (humem i' j') _ (humem i j)
      exact h1.trans h2.symm
  obtain ⟨g, hgO, hg⟩ := CFSG.RankThree.OrthogonalInvolutions.exists_mem_orthogonalGroup_apply_eq
    hQ (fun j => u (e j).1 (e j).2) (fun j => u' (e j).1 (e j).2) (hLI.comp e e.injective)
    (hLI'.comp e e.injective) (fun j => hQu _ _) (fun j j' => hpol _ _)
  have hgu : ∀ i j, g (u i j) = u' i j := fun i j => by
    have := hg (e.symm ⟨i, j⟩)
    rw [Equiv.apply_symm_apply] at this
    exact this
  have hgiso := isIsom_of_mem hgO
  have hmapW : ∀ i, (W i).map g.toLinearMap = W' (ι i) := fun i => by
    rw [← hsu i, ← hsu' i, Submodule.map_span, ← Set.range_comp]
    congr 2
    funext j
    exact hgu i j
  have hconj : ∀ i, g * b i * g⁻¹ = b' (ι i) ^ k i := by
    intro i
    have hWc := isCompl_of_nondeg hBs (hbl' (ι i)).1
    refine linearEquiv_ext_of_isCompl hWc (fun v hv => ?_) (fun x hx => ?_)
    · rw [← hmapW i] at hv
      obtain ⟨w, hw, rfl⟩ := hv
      have hw' : (g⁻¹ : V ≃ₗ[ZMod 2] V) (g w) = w := inv_apply_eq_of_apply_eq rfl
      show g (b i ((g⁻¹ : V ≃ₗ[ZMod 2] V) (g w))) = (b' (ι i) ^ k i) (g w)
      rw [hw']
      exact hint i g.toLinearMap (fun j => hgu i j) w hw
    · have hx' : (g⁻¹ : V ≃ₗ[ZMod 2] V) x ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) (W i) := by
        intro w hw
        have hgw : g w ∈ W' (ι i) := hmapW i ▸ Submodule.mem_map_of_mem hw
        show polarBilin Q w ((g⁻¹ : V ≃ₗ[ZMod 2] V) x) = 0
        rw [← hgiso w, apply_inv_apply]
        exact hx _ hgw
      show g (b i ((g⁻¹ : V ≃ₗ[ZMod 2] V) x)) = (b' (ι i) ^ k i) x
      rw [(hbl i).2.2.2.1 _ hx', apply_inv_apply, pow_apply_eq_self ((hbl' (ι i)).2.2.2.1 x hx)]
  refine ⟨g, hgO, ?_⟩
  have hmap : F.map (MulAut.conj g).toMonoidHom ≤ E₂ := by
    rw [hcl, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    show g * b i * g⁻¹ ∈ E₂
    rw [hconj i]
    exact pow_mem (hb'E (ι i)) _
  exact hmap ⟨ℓ, hℓF, rfl⟩

end Blocks

section Transport

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem exists_elemAbelian_mem_of_isom {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hnd : (polarBilin Q).Nondegenerate) (h6 : 6 ≤ finrank (ZMod 2) V)
    (hEQ : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    {X : Type} [Group X] [Finite X] (f : X ≃* ↥(elementaryGroup Q)) {ℓ : X} (hℓ : ℓ ^ p = 1)
    (S₀ : Subgroup X) (hS₀ : IsElemAbelian p S₀) :
    ∃ T : Subgroup X, IsElemAbelian p T ∧ ℓ ∈ T ∧ Nat.card ↥S₀ ≤ Nat.card ↥T := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  haveI : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv
  set O : Subgroup (V ≃ₗ[ZMod 2] V) := TauCeti.QuadraticMap.orthogonalGroup Q with hO
  let F : X →* (V ≃ₗ[ZMod 2] V) := (elementaryGroup Q).subtype.comp f.toMonoidHom
  have hFinj : Function.Injective F := Subtype.val_injective.comp f.injective
  have hFr : ∀ z ∈ elementaryGroup Q, ∃ x : X, F x = z := fun z hz =>
    ⟨f.symm ⟨z, hz⟩, by simp [F]⟩
  have hFE : ∀ x : X, F x ∈ elementaryGroup Q := fun x => (f x).2
  have hEO : elementaryGroup Q ≤ O := elementaryGroup_le_orthogonalGroup Q
  set H : Subgroup ↥O := (elementaryGroup Q).subgroupOf O with hH
  have hHidx : H.index = 2 := by
    have h1 := CFSG.RankThree.OrthogonalInvolutions.relIndex_omegaGroup Q hnd
    rw [← CFSG.RankThree.Literature.FSmith.commutator_orthogonalGroup_eq_omegaGroup hnd h6, hEQ]
      at h1
    exact h1
  have hmemH : ∀ (g : V ≃ₗ[ZMod 2] V) (hg : g ∈ O), (⟨g, hg⟩ : ↥O) ∈ H ↔ g ∈ elementaryGroup Q :=
    fun g hg => Subgroup.mem_subgroupOf
  have hodd : ∀ g ∈ O, g ^ p = 1 → g ∈ elementaryGroup Q := by
    intro g hg hgp
    obtain ⟨k, hk⟩ : Odd p := hp.odd_of_ne_two hp2
    set a : ↥O := ⟨g, hg⟩ with ha
    have hap : a ^ p = 1 := Subtype.ext (by simpa [ha] using hgp)
    have h2 : a ^ 2 ∈ H := Subgroup.sq_mem_of_index_two hHidx a
    have h3 : (a ^ 2) ^ (k + 1) = a := by
      rw [← pow_mul, show 2 * (k + 1) = p + 1 by omega, pow_succ, hap, one_mul]
    have h4 : a ∈ H := h3 ▸ pow_mem h2 (k + 1)
    exact (hmemH g hg).1 h4
  obtain ⟨E₂, hE₂O, hE₂, hE₂c⟩ := CFSG.SectionRank.exists_pRank hp.one_lt O
  have hm₂ : ∀ F' : Subgroup (V ≃ₗ[ZMod 2] V), F' ≤ O → IsElemAbelian p F' →
      Nat.card ↥F' ≤ Nat.card ↥E₂ := by
    intro F' hF'O hF'
    obtain ⟨j, hj⟩ := hF'.isPGroup.exists_card_eq
    rw [hE₂c, hj]
    exact Nat.pow_le_pow_right hp.pos (CFSG.SectionRank.le_pRank hp.one_lt hF'O hF' hj)
  have hℓO : F ℓ ∈ O := hEO (hFE ℓ)
  have hℓp : F ℓ ^ p = 1 := by rw [← map_pow, hℓ, map_one]
  obtain ⟨g, hgO, hgℓ⟩ := exists_conj_mem_of_maxEA hnd hp hp2 hℓO hℓp E₂ hE₂O hE₂ hm₂
  set E : Subgroup (V ≃ₗ[ZMod 2] V) := E₂.map (MulAut.conj g⁻¹).toMonoidHom with hE
  have hEO' : E ≤ O := by
    rintro _ ⟨y, hy, rfl⟩
    show g⁻¹ * y * g⁻¹⁻¹ ∈ O
    exact mul_mem (mul_mem (inv_mem hgO) (hE₂O hy)) (inv_mem (inv_mem hgO))
  have hEe : IsElemAbelian p E := CFSG.SectionRank.isElemAbelian_map hE₂ _
  have hEc : Nat.card ↥E = Nat.card ↥E₂ :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hFℓE : F ℓ ∈ E := ⟨g * F ℓ * g⁻¹, hgℓ, by
    show g⁻¹ * (g * F ℓ * g⁻¹) * g⁻¹⁻¹ = F ℓ
    group⟩
  have hEF : E ≤ F.range := fun z hz => hFr z (hodd z (hEO' hz) (hEe.2 z hz))
  refine ⟨E.comap F, OmegaFacts2.isElemAbelian_comap hFinj hEe, hFℓE, ?_⟩
  have h1 : Nat.card ↥(E.comap F) = Nat.card ↥E := by
    conv_rhs => rw [← Subgroup.map_comap_eq_self hEF]
    exact (Subgroup.card_map_of_injective hFinj).symm
  have h2 : Nat.card ↥S₀ ≤ Nat.card ↥E₂ := by
    have := hm₂ (S₀.map F) (by rintro _ ⟨x, -, rfl⟩; exact hEO (hFE x))
      (CFSG.SectionRank.isElemAbelian_map hS₀ F)
    rwa [Subgroup.card_map_of_injective hFinj] at this
  rw [h1, hEc]
  exact h2

end Transport

section Omega

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration (statedOmegaPlusEquiv statedOmegaMinusEquiv
  commutator_orthogonalGroup_eq_of_isometry_plus commutator_orthogonalGroup_eq_of_isometry_minus)

theorem center_eq_bot_of_mulEquiv_d4up {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : Subgroup.center Y = ⊥) : Subgroup.center X = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hz' : e z ∈ Subgroup.center Y := Subgroup.mem_center_iff.2 fun g => by
    have h1 := Subgroup.mem_center_iff.1 hz (e.symm g)
    have h2 := congrArg e h1
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
  rw [h, Subgroup.mem_bot] at hz'
  exact Subgroup.mem_bot.2 (e.injective (by rw [hz', map_one]))

theorem exists_elemAbelian_fixSub_of_equiv {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate) (h6 : 6 ≤ finrank (ZMod 2) V)
    (hEQ : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    {K : Type} [Group K] [Finite K] (f : K ≃* ↥(elementaryGroup Q)) (hZ : Subgroup.center K = ⊥)
    (hinner : ∀ σ : MulAut K, σ ^ 5 = 1 → ∃ y : K, σ = MulAut.conj y)
    {x : MulAut K} (hx : orderOf x = 5) {R : Subgroup (MulAut K)} (hR : 4 ≤ CFSG.Open.pRank 5 R) :
    ∃ T : Subgroup K, T ≤ Lemma1314.fixSub x ∧ IsElemAbelian 5 T ∧ 5 ^ 4 ≤ Nat.card ↥T := by
  have hp5 : Nat.Prime 5 := by norm_num
  have hx5 : x ^ 5 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hinj : Function.Injective (MulAut.conj : K →* MulAut K) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZ]
    intro a ha
    rw [MonoidHom.mem_ker] at ha
    refine Subgroup.mem_center_iff.2 fun g => ?_
    have h1 : a * g * a⁻¹ = g := by
      have := congrArg (fun φ : MulAut K => φ g) ha
      simpa [MulAut.conj_apply] using this
    calc g * a = a * g * a⁻¹ * a := by rw [h1]
      _ = a * g := by group
  obtain ⟨ℓ, rfl⟩ := hinner x hx5
  have hℓ5 : ℓ ^ 5 = 1 := hinj (by rw [map_pow, hx5, map_one])
  obtain ⟨E₀, -, hE₀, hE₀c⟩ := CFSG.SectionRank.exists_pRank hp5.one_lt R
  have hE₀inn : E₀ ≤ (MulAut.conj : K →* MulAut K).range := fun σ hσ => by
    obtain ⟨y, hy⟩ := hinner σ (hE₀.2 σ hσ)
    exact ⟨y, hy.symm⟩
  have hS₀ : IsElemAbelian 5 (E₀.comap (MulAut.conj : K →* MulAut K)) :=
    OmegaFacts2.isElemAbelian_comap hinj hE₀
  have hS₀c : Nat.card ↥(E₀.comap (MulAut.conj : K →* MulAut K)) = Nat.card ↥E₀ := by
    conv_rhs => rw [← Subgroup.map_comap_eq_self hE₀inn]
    exact (Subgroup.card_map_of_injective hinj).symm
  obtain ⟨T, hT, hℓT, hTc⟩ :=
    exists_elemAbelian_mem_of_isom hp5 (by norm_num) hnd h6 hEQ f hℓ5 _ hS₀
  refine ⟨T, fun t ht => ?_, hT, ?_⟩
  · show MulAut.conj ℓ t = t
    rw [MulAut.conj_apply, hT.comm hℓT ht, mul_inv_cancel_right]
  · calc 5 ^ 4 ≤ 5 ^ CFSG.Open.pRank 5 R := Nat.pow_le_pow_right (by norm_num) hR
      _ = Nat.card ↥E₀ := hE₀c.symm
      _ = Nat.card ↥(E₀.comap (MulAut.conj : K →* MulAut K)) := hS₀c.symm
      _ ≤ Nat.card ↥T := hTc

theorem exists_elemAbelian_fixSub_of_isOmegaTwo {ε : Bool} {m : ℕ} (hm : 4 ≤ m) {K : Type} [Group K]
    [Finite K] (hK : IsOmegaTwo ε m K) {x : MulAut K} (hx : orderOf x = 5) {R : Subgroup (MulAut K)}
    (hR : 4 ≤ CFSG.Open.pRank 5 R) :
    ∃ T : Subgroup K, T ≤ Lemma1314.fixSub x ∧ IsElemAbelian 5 T ∧ 5 ^ 4 ≤ Nat.card ↥T := by
  have hinner : ∀ σ : MulAut K, σ ^ 5 = 1 → ∃ y : K, σ = MulAut.conj y := fun σ hσ =>
    CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.n5_aut_omegaTwo_inner (by norm_num) le_rfl
      (by omega) hK σ hσ
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hc := CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.omegaCentreTrivial_holds n (by omega)
  cases ε with
  | true =>
    obtain ⟨φ⟩ := hK
    have h6 : 6 ≤ finrank (ZMod 2) (Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2) := by
      rw [finrank_fintype_fun_eq_card]
      simp [Fintype.card_sum]
      omega
    exact exists_elemAbelian_fixSub_of_equiv (nondegenerate_polarBilin_quadPlus (n + 1) (ZMod 2)) h6
      (commutator_orthogonalGroup_eq_of_isometry_plus (K := ZMod 2) (Q := quadPlus (n + 1) (ZMod 2))
        (by omega) (LinearEquiv.refl _ _) fun v => rfl)
      (φ.trans (statedOmegaPlusEquiv (by omega))) (center_eq_bot_of_mulEquiv_d4up φ hc.1) hinner hx hR
  | false =>
    obtain ⟨φ⟩ := hK
    have h6 : 6 ≤ finrank (ZMod 2) (Fin (n + 1 - 1) ⊕ Fin (n + 1 - 1) ⊕ Fin 2 → ZMod 2) := by
      rw [finrank_fintype_fun_eq_card]
      simp [Fintype.card_sum]
      omega
    exact exists_elemAbelian_fixSub_of_equiv
      (nondegenerate_polarBilin_quadMinus_of_finite (n + 1) (ZMod 2)
        (by decide : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0)) h6
      (commutator_orthogonalGroup_eq_of_isometry_minus (K := ZMod 2)
        (Q := quadMinus (n + 1) (ZMod 2) 1 1) (by omega) (LinearEquiv.refl _ _) fun v => rfl)
      (φ.trans (statedOmegaMinusEquiv (by omega))) (center_eq_bot_of_mulEquiv_d4up φ hc.2) hinner hx hR

end Omega

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110l
