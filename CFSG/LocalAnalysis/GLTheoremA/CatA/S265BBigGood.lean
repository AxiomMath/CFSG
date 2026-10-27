module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowXUnGood
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1UnAut

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.BBig

open CFSG.ComponentClassification.Burgoyne.U
open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie (IsGood)
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowXUn
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowXUn.Good

theorem exists_isGood_zpowers_of_diag {N : ℕ} (hN5 : 5 ≤ N) (A : Subgroup (MulAut (xunM N)))
    (hA : IsElemAbelian 3 A) (h4 : 3 ^ 4 ≤ Nat.card A)
    (hdiag : ∀ g : uU xunH N, xunConj N (by omega) g ∈ A →
      IsDiagU N (g : GL (Fin N) xunK)) :
    ∃ a ∈ A, a ≠ 1 ∧ IsGood 3 (Subgroup.zpowers a) := by
  have hN1 : 1 ≤ N := by omega
  have hN4 : 4 ≤ N := by omega
  have hN3 : 3 ≤ N := by omega
  set i0 : Fin N := ⟨0, by omega⟩ with hi0def
  set Pl : Subgroup (uU xunH N) := A.comap (xunConj N hN1) with hPl
  have hdiagPl : ∀ g : Pl, IsDiagU N ((g : uU xunH N) : GL (Fin N) xunK) :=
    fun g => hdiag g.1 g.2
  let idx : Fin 3 → Fin N := fun k => ⟨k.val + 1, by omega⟩
  let eU : Pl → Fin N → xunKˣ := fun g j => Units.mk0 (uEnt g.1 j) (uEnt_ne_zero (hdiagPl g) j)
  let ψf : Pl → (Fin 3 → xunKˣ) := fun g k => eU g (idx k) * (eU g i0)⁻¹
  have e1 : ∀ g h : Pl, ∀ j, eU (g * h) j = eU g j * eU h j := by
    intro g h j
    apply Units.ext
    change uEnt (g.1 * h.1) j = uEnt g.1 j * uEnt h.1 j
    exact uEnt_mul (hdiagPl g) (hdiagPl h) j
  have hψmul : ∀ g h : Pl, ψf (g * h) = ψf g * ψf h := by
    intro g h
    funext k
    simp only [ψf, Pi.mul_apply, e1, mul_inv]
    ac_rfl
  let ψ : Pl →* (Fin 3 → xunKˣ) := MonoidHom.mk' ψf hψmul
  set T : Subgroup (uU xunH N) := ψ.ker.map Pl.subtype with hT
  have hTmem : ∀ d ∈ T, ∃ g : Pl, ψ g = 1 ∧ (g : uU xunH N) = d := fun d hd => by
    obtain ⟨g, hg, hgd⟩ := Subgroup.mem_map.1 hd
    exact ⟨g, hg, hgd⟩
  have hTdiag : ∀ d ∈ T, IsDiagU N ((d : uU xunH N) : GL (Fin N) xunK) := by
    intro d hd
    obtain ⟨g, -, rfl⟩ := hTmem d hd
    exact hdiagPl g
  have hTfour : ∀ d ∈ T, ∀ j : Fin N, (j : ℕ) < 4 → dgl (d : GL (Fin N) xunK) j =
      dgl (d : GL (Fin N) xunK) i0 := by
    intro d hd j hj
    obtain ⟨g, hψ, rfl⟩ := hTmem d hd
    have hk : ∀ k : Fin 3, eU g (idx k) = eU g i0 := by
      intro k
      have := congrFun hψ k
      simp only [ψ, MonoidHom.mk'_apply, ψf, Pi.one_apply] at this
      exact mul_inv_eq_one.1 this
    rcases Nat.lt_or_ge (j : ℕ) 1 with h0 | h1
    · have hj0 : j = i0 := Fin.ext (by simp [i0, show (j : ℕ) = 0 by omega])
      rw [hj0]
    · let k : Fin 3 := ⟨j.val - 1, by omega⟩
      have hjk : idx k = j := Fin.ext (by simp [idx, k]; omega)
      have := congrArg Units.val (hk k)
      rw [hjk] at this
      exact this
  let s : Pl →* MulAut (xunM N) := (xunConj N hN1).comp Pl.subtype
  have hAle : A ≤ (xunConj N hN1).range := fun a ha =>
    KD264Lie.RowX1Un.le_range_xunConj_of_isElemAbelian4 (by omega) A hA a ha
  have hrange : s.range = A := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hPl, Subgroup.map_comap_eq]
    exact inf_eq_right.2 hAle
  have hrange_card : Nat.card ψ.range ≤ 27 := by
    have h1 := Nat.card_le_card_of_injective
      (Subtype.val : ψ.range → (Fin 3 → xunKˣ)) Subtype.val_injective
    have h2 : Nat.card (Fin 3 → xunKˣ) = Nat.card xunKˣ ^ 3 := by simp [Nat.card_fun]
    have h3 : Nat.card xunKˣ = 3 := by
      rw [Nat.card_units, xunK_card]
      norm_num
    rw [h3] at h2
    omega
  obtain ⟨t, hψt, hst⟩ : ∃ t : Pl, ψ t = 1 ∧ s t ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hle : ψ.ker ≤ s.ker := fun t ht =>
      MonoidHom.mem_ker.2 (hcon t (MonoidHom.mem_ker.1 ht))
    have hdvd := Subgroup.index_dvd_of_le hle
    rw [Subgroup.index_ker, Subgroup.index_ker, hrange] at hdvd
    have := Nat.le_of_dvd Nat.card_pos hdvd
    norm_num at h4
    omega
  set t' : uU xunH N := (t : uU xunH N) with ht'
  have ht'T : t' ∈ T := Subgroup.mem_map.2 ⟨t, hψt, rfl⟩
  have hdt : IsDiagU N (t' : GL (Fin N) xunK) := hTdiag t' ht'T
  have hsep : ∃ j : Fin N, dgl (t' : GL (Fin N) xunK) j ≠ dgl (t' : GL (Fin N) xunK) i0 := by
    by_contra hcon
    push Not at hcon
    apply hst
    refine (uConjAut_eq_one_iff xunH hN3 t').2
      ⟨Units.mk0 (uEnt t' i0) (uEnt_ne_zero hdt i0), Units.ext (Matrix.ext fun i j => ?_)⟩
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.diagonal_apply_eq, Units.val_mk0]
      exact hcon i
    · simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.diagonal_apply_ne _ hij]
      exact hdt i j hij
  have hzp : Subgroup.zpowers t' ≤ T := Subgroup.zpowers_le.2 ht'T
  obtain ⟨j, hj⟩ := hsep
  have hgood := isGood_of_torus hN1 hN4 i0 rfl (Subgroup.zpowers t')
    (fun d hd => hTdiag d (hzp hd)) (fun d hd j hj => hTfour d (hzp hd) j hj)
    ⟨t', Subgroup.mem_zpowers t', j, hj⟩
  refine ⟨xunConj N hN1 t', t.2, hst, ?_⟩
  rw [← MonoidHom.map_zpowers]
  exact hgood

end CFSG.LocalAnalysis.GLTheoremA.S265.BBig

end
