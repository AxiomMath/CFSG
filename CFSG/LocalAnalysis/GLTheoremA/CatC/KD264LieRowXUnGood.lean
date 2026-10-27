module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowXUnGoodTorus

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowXUn.Good

open CFSG.ComponentClassification.Burgoyne.U
open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.Burgoyne.Proj

abbrev uEnt {N : ℕ} (g : uU xunH N) (j : Fin N) : xunK :=
  ((g : GL (Fin N) xunK) : Matrix (Fin N) (Fin N) xunK) j j

theorem uEnt_mul {N : ℕ} {g h : uU xunH N} (hg : IsDiagU N (g : GL (Fin N) xunK))
    (hh : IsDiagU N (h : GL (Fin N) xunK)) (j : Fin N) :
    uEnt (g * h) j = uEnt g j * uEnt h j := by
  change (((g : GL (Fin N) xunK) * (h : GL (Fin N) xunK) : GL (Fin N) xunK) :
    Matrix (Fin N) (Fin N) xunK) j j = _
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single j]
  · intro k _ hk
    rw [hg j k (Ne.symm hk), zero_mul]
  · intro h'
    exact absurd (Finset.mem_univ j) h'

theorem uEnt_ne_zero {N : ℕ} {g : uU xunH N} (hg : IsDiagU N (g : GL (Fin N) xunK)) (j : Fin N) :
    uEnt g j ≠ 0 := by
  intro h0
  have h1 : ((g : GL (Fin N) xunK) : Matrix (Fin N) (Fin N) xunK) *
      (((g : GL (Fin N) xunK)⁻¹ : GL (Fin N) xunK) : Matrix (Fin N) (Fin N) xunK) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 := congrFun (congrFun h1 j) j
  rw [Matrix.mul_apply, Finset.sum_eq_single j] at h2
  · rw [Matrix.one_apply_eq] at h2
    change ((g : GL (Fin N) xunK) : Matrix (Fin N) (Fin N) xunK) j j = 0 at h0
    rw [h0, zero_mul] at h2
    exact zero_ne_one h2
  · intro k _ hk
    rw [hg j k (Ne.symm hk), zero_mul]
  · intro h'
    exact absurd (Finset.mem_univ j) h'

noncomputable def uUnit {N : ℕ} (g : uU xunH N) (hg : IsDiagU N (g : GL (Fin N) xunK))
    (j : Fin N) : xunKˣ :=
  Units.mk0 (uEnt g j) (uEnt_ne_zero hg j)

theorem eq_of_conj_one {N : ℕ} (hN : 3 ≤ N) (i0 : Fin N) (d e : uU xunH N)
    (hd : xunConj N (by omega) d = 1) (he : xunConj N (by omega) e = 1)
    (h : uEnt d i0 = uEnt e i0) : d = e := by
  have hd' : uConjAut xunH (by omega) d = 1 := hd
  have he' : uConjAut xunH (by omega) e = 1 := he
  obtain ⟨c, hc⟩ := (uConjAut_eq_one_iff xunH hN d).1 hd'
  obtain ⟨c', hc'⟩ := (uConjAut_eq_one_iff xunH hN e).1 he'
  have hcc : (c : xunK) = (c' : xunK) := by
    have h1 := h
    simp only [uEnt, hc, hc', Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq] at h1
    exact h1
  have hcc' : c = c' := Units.ext hcc
  apply Subtype.ext
  apply Units.ext
  rw [hc, hc', hcc']

theorem two_le_pRank_of_card {G : Type} [Group G] [Finite G] {E : Subgroup G}
    (hE : IsElemAbelian 3 E) (h9 : 9 ≤ Nat.card E) : 2 ≤ CFSG.Open.pRank 3 E := by
  have h := CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_three hE
  by_contra hlt
  simp only [not_le] at hlt
  have : Nat.card E ≤ 3 := by
    rw [h]
    calc 3 ^ CFSG.Open.pRank 3 E ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 3 := by norm_num
  omega

theorem card_eq_card_range_mul_card_ker {G H : Type} [Group G] [Group H] [Finite G]
    (φ : G →* H) : Nat.card G = Nat.card φ.range * Nat.card φ.ker := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]

theorem kd264XUnTorusGood_holds : KD264XUnTorusGood := by
  intro N hN _h3 A hA hrank hdiag
  have hN1 : 1 ≤ N := by omega
  have hN4 : 4 ≤ N := by omega
  have hN3 : 3 ≤ N := by omega
  set i0 : Fin N := ⟨0, by omega⟩ with hi0def
  have hi0 : (i0 : ℕ) = 0 := rfl
  set Pl : Subgroup (uU xunH N) := A.comap (xunConj N hN1) with hPl
  have hdiagPl : ∀ g : Pl, IsDiagU N ((g : uU xunH N) : GL (Fin N) xunK) :=
    fun g => hdiag g.1 g.2
  let idx : Fin 3 → Fin N := fun k => ⟨k.val + 1, by omega⟩
  let eU : Pl → Fin N → xunKˣ := fun g j => uUnit g.1 (hdiagPl g) j
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
  set Tp : Subgroup Pl := ψ.ker with hTp
  set T : Subgroup (uU xunH N) := Tp.map Pl.subtype with hT
  have hTle : T ≤ Pl := by
    intro d hd
    obtain ⟨g, -, rfl⟩ := Subgroup.mem_map.1 hd
    exact g.2
  have hTmem : ∀ d ∈ T, ∃ g : Pl, g ∈ Tp ∧ (g : uU xunH N) = d := by
    intro d hd
    obtain ⟨g, hg, hgd⟩ := Subgroup.mem_map.1 hd
    exact ⟨g, hg, hgd⟩
  have hTdiag : ∀ d ∈ T, IsDiagU N ((d : uU xunH N) : GL (Fin N) xunK) := by
    intro d hd
    obtain ⟨g, -, rfl⟩ := hTmem d hd
    exact hdiagPl g
  have hTfour : ∀ d ∈ T, ∀ j : Fin N, (j : ℕ) < 4 → dgl (d : GL (Fin N) xunK) j =
      dgl (d : GL (Fin N) xunK) i0 := by
    intro d hd j hj
    obtain ⟨g, hg, rfl⟩ := hTmem d hd
    have hψ : ψ g = 1 := hg
    have hk : ∀ k : Fin 3, eU g (idx k) = eU g i0 := by
      intro k
      have := congrFun hψ k
      simp only [ψ, MonoidHom.mk'_apply, ψf, Pi.one_apply] at this
      exact mul_inv_eq_one.1 this
    have hval : uEnt g.1 j = uEnt g.1 i0 := by
      rcases Nat.lt_or_ge (j : ℕ) 1 with h0 | h1
      · have hj0 : j = i0 := Fin.ext (by simp [hi0, show (j : ℕ) = 0 by omega])
        rw [hj0]
      · let k : Fin 3 := ⟨j.val - 1, by omega⟩
        have hjk : idx k = j := Fin.ext (by simp [idx, k]; omega)
        have := congrArg Units.val (hk k)
        rw [hjk] at this
        exact this
    exact hval
  have hAcard : 2187 ≤ Nat.card A := by
    rw [CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_three hA]
    calc 2187 = 3 ^ 7 := by norm_num
      _ ≤ 3 ^ (N - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ 3 ^ CFSG.Open.pRank 3 A := Nat.pow_le_pow_right (by norm_num) hrank
  have hPlcard : Nat.card A ≤ Nat.card Pl := by
    refine Nat.card_le_card_of_surjective
      (fun g : Pl => (⟨xunConj N hN1 g.1, g.2⟩ : A)) ?_
    intro a
    obtain ⟨g, hg⟩ := le_range_xunConj_of_isElemAbelian hN A hA a.1 a.2
    refine ⟨⟨g, ?_⟩, Subtype.ext hg⟩
    show xunConj N hN1 g ∈ A
    rw [hg]
    exact a.2
  have hK4 : Nat.card xunK = 4 := by
    rw [xunK_card]
    norm_num
  have hunit_card : Nat.card xunKˣ ≤ 4 := by
    rw [← hK4]
    exact Nat.card_le_card_of_injective (Units.val : xunKˣ → xunK) Units.val_injective
  have hrange_card : Nat.card ψ.range ≤ 64 := by
    have h1 := Nat.card_le_card_of_injective
      (Subtype.val : ψ.range → (Fin 3 → xunKˣ)) Subtype.val_injective
    have h2 : Nat.card (Fin 3 → xunKˣ) = Nat.card xunKˣ ^ 3 := by
      simp [Nat.card_fun]
    have h3 : Nat.card xunKˣ ^ 3 ≤ 4 ^ 3 := Nat.pow_le_pow_left hunit_card 3
    omega
  have hcardPl : Nat.card Pl = Nat.card ψ.range * Nat.card Tp :=
    card_eq_card_range_mul_card_ker ψ
  have hTpcard : 35 ≤ Nat.card Tp := by
    have h1 : Nat.card ψ.range * Nat.card Tp ≤ 64 * Nat.card Tp :=
      Nat.mul_le_mul_right _ hrange_card
    have h2 : 2187 ≤ 64 * Nat.card Tp := hAcard.trans (hPlcard.trans (hcardPl.le.trans h1))
    omega
  have hTcard : Nat.card T = Nat.card Tp :=
    Subgroup.card_map_of_injective Pl.subtype_injective
  have hTcard35 : 35 ≤ Nat.card T := by omega
  set F : Subgroup (MulAut (xunM N)) := T.map (xunConj N hN1) with hF
  set φT : T →* MulAut (xunM N) := (xunConj N hN1).comp T.subtype with hφT
  have hφTrange : φT.range = F := by
    rw [hφT, MonoidHom.range_comp, Subgroup.range_subtype]
  have hFcard : Nat.card F * Nat.card φT.ker = Nat.card T := by
    have := card_eq_card_range_mul_card_ker φT
    rw [hφTrange] at this
    exact this.symm
  have hkerφ : Nat.card φT.ker ≤ 4 := by
    rw [← hK4]
    refine Nat.card_le_card_of_injective
      (fun d : φT.ker => uEnt ((d.1 : T) : uU xunH N) i0) ?_
    intro d1 d2 hd
    have hd1 : xunConj N hN1 ((d1.1 : T) : uU xunH N) = 1 := MonoidHom.mem_ker.1 d1.2
    have hd2 : xunConj N hN1 ((d2.1 : T) : uU xunH N) = 1 := MonoidHom.mem_ker.1 d2.2
    exact Subtype.ext (Subtype.ext (eq_of_conj_one hN3 i0 _ _ hd1 hd2 hd))
  have hF9 : 9 ≤ Nat.card F := by
    have h1 : Nat.card F * Nat.card φT.ker ≤ Nat.card F * 4 :=
      Nat.mul_le_mul_left _ hkerφ
    have h2 : Nat.card T ≤ Nat.card F * 4 := hFcard ▸ h1
    omega
  have hsepT : ∃ d ∈ T, ∃ j : Fin N,
      dgl ((d : uU xunH N) : GL (Fin N) xunK) j ≠ dgl ((d : uU xunH N) : GL (Fin N) xunK) i0 := by
    by_contra hcon
    have hall : ∀ d ∈ T, ∀ j : Fin N,
        dgl ((d : uU xunH N) : GL (Fin N) xunK) j = dgl ((d : uU xunH N) : GL (Fin N) xunK) i0 := by
      intro d hd j
      by_contra hne
      exact hcon ⟨d, hd, j, hne⟩
    have hinj : Function.Injective
        (fun d : T => dgl ((d : uU xunH N) : GL (Fin N) xunK) i0) := by
      intro d1 d2 hd
      have hd' : dgl ((d1 : uU xunH N) : GL (Fin N) xunK) i0 =
          dgl ((d2 : uU xunH N) : GL (Fin N) xunK) i0 := hd
      apply Subtype.ext
      apply Subtype.ext
      apply Units.ext
      ext i j
      by_cases hij : i = j
      · subst hij
        show dgl ((d1 : uU xunH N) : GL (Fin N) xunK) i = dgl ((d2 : uU xunH N) : GL (Fin N) xunK) i
        rw [hall _ d1.2 i, hd', ← hall _ d2.2 i]
      · show ((((d1 : uU xunH N) : GL (Fin N) xunK)) : Matrix (Fin N) (Fin N) xunK) i j =
          ((((d2 : uU xunH N) : GL (Fin N) xunK)) : Matrix (Fin N) (Fin N) xunK) i j
        rw [hTdiag _ d1.2 i j hij, hTdiag _ d2.2 i j hij]
    have := Nat.card_le_card_of_injective _ hinj
    rw [hK4] at this
    omega
  have hgood := isGood_of_torus hN1 hN4 i0 rfl T hTdiag hTfour hsepT
  have hFA : F ≤ A := Subgroup.map_le_iff_le_comap.2 hTle
  have hFel : IsElemAbelian 3 F := isElemAbelian_mono hA hFA
  exact ⟨F, hFA, hFel, two_le_pRank_of_card hFel hF9, hgood⟩

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowXUn.Good

end
