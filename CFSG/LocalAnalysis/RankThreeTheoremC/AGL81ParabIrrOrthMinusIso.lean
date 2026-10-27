module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommOrthMinusModel

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr.OrthMinus

open Module QuadraticMap Matrix CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.AGLEmbedding.LeviBlock
  CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthMinus

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} {r s : ℕ} {d : Fin (s + 1) → ℕ}

local notation "𝕍" => (Fin r ⊕ Fin r → K) × (Fin 2 → K)

theorem isometry_unique (hr : 3 ≤ r) (hirr : ∀ t : K, t ^ 2 + b * t + c ≠ 0)
    {α : MulAut ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))} {f f' : 𝕍 ≃ₗ[K] 𝕍}
    (hf : ∀ v, quadTail r (minusTailForm K b c) (f v) = quadTail r (minusTailForm K b c) v)
    (hf' : ∀ v, quadTail r (minusTailForm K b c) (f' v) = quadTail r (minusTailForm K b c) v)
    (h : IsConjBy α f) (h' : IsConjBy α f') : f = f' := by
  set G : 𝕍 ≃ₗ[K] 𝕍 := f'⁻¹ * f with hG
  have hE := commutator_orthogonalGroup_quadTail_minus hr hirr
  have hcomm : ∀ g ∈ orthDerived (quadTail r (minusTailForm K b c)), ∀ v,
      G (g v) = g (G v) := by
    intro g hg v
    have hgE : g ∈ orthElementaryGroup (quadTail r (minusTailForm K b c)) := by
      rw [← hE]
      exact hg
    have h3 : f * g * f⁻¹ = f' * g * f'⁻¹ := (h ⟨g, hgE⟩).symm.trans (h' ⟨g, hgE⟩)
    have h4 : G * g = g * G := by
      calc G * g = f'⁻¹ * (f * g * f⁻¹) * f := by rw [hG]; group
        _ = f'⁻¹ * (f' * g * f'⁻¹) * f := by rw [h3]
        _ = g * G := by rw [hG]; group
    exact LinearEquiv.congr_fun h4 v
  have hGQ : ∀ v, quadTail r (minusTailForm K b c) (G v) = quadTail r (minusTailForm K b c) v := by
    intro v
    have h1 := hf' (f'⁻¹ (f v))
    have h2 : f' (f'⁻¹ (f v)) = f v := by
      rw [← LinearEquiv.mul_apply, mul_inv_cancel]
      rfl
    rw [h2, hf] at h1
    exact h1.symm
  obtain ⟨-, a, -, ha⟩ := schur_tail (m := r) (by omega) hirr G.toAddEquiv (RingEquiv.refl K)
    (fun a v => by simp) 1 (fun v => by simpa using hGQ v) hcomm
  obtain ⟨v₀, hv₀⟩ := exists_quadTail_ne_zero (r := r) (b := b) (c := c) hirr
  have hG1 : G = 1 :=
    scalar_eq_one_of_isometry (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 hGQ)
      (mem_scalars.2 ⟨a, fun v => ha v⟩) hv₀
  exact (inv_mul_eq_one.1 hG1).symm

section Smul

variable {V : Type} [AddCommGroup V] [Module K V]

@[expose] def smulEquiv (g : V ≃ₗ[K] V) {a : K} (ha : a ≠ 0) : V ≃ₗ[K] V where
  toFun v := a • g v
  map_add' x y := by rw [map_add, smul_add]
  map_smul' x v := by
    rw [map_smul, smul_comm]
    rfl
  invFun v := g.symm (a⁻¹ • v)
  left_inv v := by
    simp only [smul_smul, inv_mul_cancel₀ ha, one_smul, LinearEquiv.symm_apply_apply]
  right_inv v := by
    simp only [LinearEquiv.apply_symm_apply, map_smul, smul_smul, mul_inv_cancel₀ ha, one_smul]

theorem smulEquiv_apply (g : V ≃ₗ[K] V) {a : K} (ha : a ≠ 0) (v : V) :
    smulEquiv g ha v = a • g v :=
  rfl

theorem smulEquiv_conj (g x : V ≃ₗ[K] V) {a : K} (ha : a ≠ 0) :
    smulEquiv g ha * x * (smulEquiv g ha)⁻¹ = g * x * g⁻¹ := by
  refine LinearEquiv.ext fun v => ?_
  have h1 : ((smulEquiv g ha)⁻¹ : V ≃ₗ[K] V) v = g.symm (a⁻¹ • v) := rfl
  have h2 : ((g⁻¹ : V ≃ₗ[K] V)) v = g.symm v := rfl
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    h1, h2, smulEquiv_apply, map_smul, map_smul, map_smul, smul_smul, mul_inv_cancel₀ ha, one_smul]

theorem smul_mem_iff_of_ne_zero (T : Submodule K V) {a : K} (ha : a ≠ 0) {x : V} :
    a • x ∈ T ↔ x ∈ T :=
  ⟨fun h => by simpa [smul_smul, inv_mul_cancel₀ ha] using T.smul_mem a⁻¹ h,
    fun h => T.smul_mem a h⟩

end Smul

structure GoodIso (b c : K) (hd : OrthCuts r d) (f : 𝕍 ≃ₗ[K] 𝕍) : Prop where
  iso : ∀ v, quadTail r (minusTailForm K b c) (f v) = quadTail r (minusTailForm K b c) v
  flag : ∀ (i : Fin (s + 1)) (v : 𝕍), f v ∈ tailFlag K (Fin 2 → K) r (d i) ↔
    v ∈ tailFlag K (Fin 2 → K) r (d i)
  perp : ∀ v : 𝕍, IsResPerp hd.last (f v) ↔ IsResPerp hd.last v
  sec : ∀ l : Fin s, ∃ a : K, ScalarMod (tailFlag K (Fin 2 → K) r (d l.succ))
    (tailFlag K (Fin 2 → K) r (d l.castSucc)) f a
  res : 1 ≤ r - d (Fin.last s) → ∃ a : K, ScalarMod (perpSub (K := K) (r := r) hd.last)
    (tailFlag K (Fin 2 → K) r (d (Fin.last s))) f a

theorem exists_isometry (hr : 3 ≤ r) (hirr : ∀ t : K, t ^ 2 + b * t + c ≠ 0) (hd : OrthCuts r d)
    (hbig : (∃ l : Fin s, 2 ≤ d l.succ - d l.castSucc) ∨ 1 ≤ r - d (Fin.last s))
    {α : MulAut ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))}
    (hodd : Odd (orderOf α)) (hn : OmNormFix hr hirr hd α) :
    ∃ f : 𝕍 ≃ₗ[K] 𝕍, IsConjBy α f ∧ GoodIso b c hd f := by
  obtain ⟨Fl, μ, hμ, hc, hq, hf, hp, hb', hr', -⟩ := exists_data hr hirr hd hbig hodd hn
  obtain ⟨ν, hν⟩ := isSquare_of_charTwo' μ
  have hν0 : ν ≠ 0 := by
    rintro rfl
    exact hμ (by rw [hν, mul_zero])
  have hν' : ν⁻¹ ≠ 0 := inv_ne_zero hν0
  refine ⟨smulEquiv Fl hν', fun g => ?_, ⟨fun v => ?_, fun i v => ?_, fun v => ?_, fun l => ?_,
    fun hm => ?_⟩⟩
  · rw [hc g, smulEquiv_conj]
  · rw [smulEquiv_apply, QuadraticMap.map_smul, smul_eq_mul, hq, hν]
    field_simp
  · rw [smulEquiv_apply, smul_mem_iff_of_ne_zero _ hν']
    exact hf i v
  · have h1 : IsResPerp hd.last (ν⁻¹ • Fl v) ↔ IsResPerp hd.last (Fl v) := by
      simpa only [mem_perpSub] using
        smul_mem_iff_of_ne_zero (perpSub (K := K) (r := r) hd.last) hν' (x := Fl v)
    rw [smulEquiv_apply, h1]
    exact hp v
  · obtain ⟨a, -, ha⟩ := hb' l
    refine ⟨ν⁻¹ * a, fun v hv => ?_⟩
    have := (tailFlag K (Fin 2 → K) r (d l.castSucc)).smul_mem ν⁻¹ (ha v hv)
    rwa [smul_sub, smul_smul] at this
  · obtain ⟨a, -, ha⟩ := hr' hm
    refine ⟨ν⁻¹ * a, fun v hv => ?_⟩
    have := (tailFlag K (Fin 2 → K) r (d (Fin.last s))).smul_mem ν⁻¹ (ha v hv)
    rwa [smul_sub, smul_smul] at this

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr.OrthMinus
