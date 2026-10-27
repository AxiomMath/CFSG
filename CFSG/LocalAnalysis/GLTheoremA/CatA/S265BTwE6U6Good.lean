module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowXUnGoodTorus
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowXUnStruct

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.BTwE6

open CFSG.ComponentClassification.Burgoyne.U
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie (IsGood)
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowXUn
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowXUn.Good

private theorem exists_sparse (D : Subgroup (Fin 6 → xunKˣ)) (hD : 3 ^ 4 ≤ Nat.card D) :
    ∃ v ∈ D, v ≠ 1 ∧ ∃ k l : Fin 6, ∀ j, j ≠ k → j ≠ l → v j = 1 := by
  have h3 : Nat.card xunKˣ = 3 := Struct.card_units_eq_three xunK_card_four
  have hQ : Nat.card ((Fin 6 → xunKˣ) ⧸ D) ≤ 9 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup D
    rw [Nat.card_fun, h3, Nat.card_fin] at h1
    have h2 := Nat.mul_le_mul_left (Nat.card ((Fin 6 → xunKˣ) ⧸ D)) hD
    rw [← h1] at h2
    norm_num at h2
    omega
  obtain ⟨ζ, hζ⟩ : ∃ ζ : xunKˣ, ζ ≠ 1 := by
    haveI : Nontrivial xunKˣ := Finite.one_lt_card_iff_nontrivial.1 (by rw [h3]; norm_num)
    exact exists_ne 1
  have hζne : ζ⁻¹ ≠ ζ := by
    intro h
    apply hζ
    have h2 : ζ * ζ = 1 := by
      calc ζ * ζ = ζ * ζ⁻¹ := by rw [h]
        _ = 1 := mul_inv_cancel ζ
    calc ζ = ζ ^ 3 * (ζ * ζ)⁻¹ := by group
      _ = 1 := by rw [Struct.units_pow_three xunK_card_four ζ, h2, inv_one, one_mul (1 : xunKˣ)]
  let z : Bool → xunKˣ := fun b => cond b ζ ζ⁻¹
  have hz1 : ∀ b, z b ≠ 1 := fun b => by
    cases b
    · exact inv_ne_one.2 hζ
    · exact hζ
  have hzinj : ∀ b b', z b = z b' → b = b' := by
    intro b b' h
    cases b <;> cases b'
    · rfl
    · exact (hζne h).elim
    · exact (hζne h.symm).elim
    · rfl
  let F : Fin 6 × Bool → (Fin 6 → xunKˣ) ⧸ D := fun p =>
    QuotientGroup.mk (Pi.mulSingle p.1 (z p.2) : Fin 6 → xunKˣ)
  obtain ⟨⟨k, b⟩, ⟨l, b'⟩, hpp, hne⟩ : ∃ p p', F p = F p' ∧ p ≠ p' := by
    by_contra hcon
    push Not at hcon
    have h12 := Nat.card_le_card_of_injective F fun p p' h => hcon p p' h
    rw [Nat.card_eq_fintype_card (α := Fin 6 × Bool), Fintype.card_prod, Fintype.card_fin,
      Fintype.card_bool] at h12
    omega
  have hmem : ((Pi.mulSingle k (z b) : Fin 6 → xunKˣ))⁻¹ *
      (Pi.mulSingle l (z b') : Fin 6 → xunKˣ) ∈ D := QuotientGroup.eq.1 hpp
  refine ⟨_, hmem, fun h1 => ?_, k, l, fun j hj hj' => ?_⟩
  · have h2 := congrFun h1 k
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_eq_same, Pi.one_apply] at h2
    by_cases hlk : l = k
    · subst hlk
      rw [Pi.mulSingle_eq_same, inv_mul_eq_one] at h2
      exact hne (by rw [hzinj b b' h2])
    · rw [Pi.mulSingle_eq_of_ne' hlk, mul_one ((z b)⁻¹)] at h2
      exact hz1 b (inv_eq_one.1 h2)
  · simp only [Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_eq_of_ne hj, Pi.mulSingle_eq_of_ne hj',
      inv_one, one_mul]

private theorem permGL_mem (τ : Equiv.Perm (Fin 6)) :
    TauCeti.permutationGL (k := xunK) τ ∈ uU xunH 6 := by
  rw [mem_uU, TauCeti.permutationGL_coe]
  have hmap : (Equiv.Perm.permMatrix xunK τ⁻¹).map xunH.bar = Equiv.Perm.permMatrix xunK τ⁻¹ := by
    ext a b
    rw [Matrix.map_apply]
    simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
    split_ifs <;> simp
  rw [hmap, Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul, mul_inv_cancel,
    Matrix.permMatrix_one]

private theorem exists_perm_away (k l : Fin 6) :
    ∃ τ : Equiv.Perm (Fin 6), 4 ≤ (τ k : ℕ) ∧ 4 ≤ (τ l : ℕ) := by
  have key : ∀ k l : Fin 6, 4 ≤ ((Equiv.swap (Equiv.swap k 4 l) 5 * Equiv.swap k 4) k : ℕ) ∧
      4 ≤ ((Equiv.swap (Equiv.swap k 4 l) 5 * Equiv.swap k 4) l : ℕ) := by
    decide +kernel
  exact ⟨_, key k l⟩

theorem exists_good_of_diag_conj (P : Subgroup (uU xunH 6)) (c : uU xunH 6)
    (hc : ∀ g ∈ P, IsDiagU 6 ((c * g * c⁻¹ : uU xunH 6) : GL (Fin 6) xunK))
    (hcard : 3 ^ 4 ≤ Nat.card P) :
    ∃ g ∈ P, xunConj 6 (by norm_num) g ≠ 1 ∧
      IsGood 3 (Subgroup.zpowers (xunConj 6 (by norm_num) g)) := by
  have hN1 : 1 ≤ 6 := by norm_num
  obtain ⟨Q, hQ⟩ : ∃ Q : Subgroup (GL (Fin 6) xunK),
      Q = (P.map (MulAut.conj c).toMonoidHom).map (uU xunH 6).subtype := ⟨_, rfl⟩
  have hQle : Q ≤ (TauCeti.diagGL (k := xunK) (ι := Fin 6)).range := by
    rw [hQ]
    rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    exact MonoidHom.mem_range.2 (TauCeti.mem_diagonalTorus_iff_exists_diagGL.1
      (TauCeti.mem_diagonalTorus_iff.2 (by intro i j hij; exact hc g hg i j hij)))
  have hD : 3 ^ 4 ≤ Nat.card (Q.comap TauCeti.diagGL) := by
    have h1 : (Q.comap TauCeti.diagGL).map TauCeti.diagGL = Q := by
      rw [Subgroup.map_comap_eq]
      exact inf_eq_right.2 hQle
    have h2 := Subgroup.card_map_of_injective (K := Q.comap TauCeti.diagGL)
      TauCeti.diagGL_injective
    rw [h1] at h2
    rw [← h2, hQ, Subgroup.card_map_of_injective (uU xunH 6).subtype_injective,
      Subgroup.card_map_of_injective (MulAut.conj c).injective]
    exact hcard
  obtain ⟨v, hvD, hv1, k, l, hkl⟩ := exists_sparse _ hD
  have hvQ : TauCeti.diagGL v ∈ Q := hvD
  rw [hQ] at hvQ
  obtain ⟨_, ⟨g, hg, rfl⟩, hgv⟩ := hvQ
  have hgv' : ((c * g * c⁻¹ : uU xunH 6) : GL (Fin 6) xunK) = TauCeti.diagGL v := hgv
  obtain ⟨τ, hτk, hτl⟩ := exists_perm_away k l
  obtain ⟨π, hπ⟩ : ∃ π : uU xunH 6, (π : GL (Fin 6) xunK) = TauCeti.permutationGL τ :=
    ⟨⟨_, permGL_mem τ⟩, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : uU xunH 6, x = π * c := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : Fin 6 → xunKˣ, w = fun i => v (τ⁻¹ i) := ⟨_, rfl⟩
  have hd' : ((x * g * x⁻¹ : uU xunH 6) : GL (Fin 6) xunK) = TauCeti.diagGL w := by
    have h1 : x * g * x⁻¹ = π * (c * g * c⁻¹) * π⁻¹ := by rw [hx]; group
    rw [h1]
    change (π : GL (Fin 6) xunK) * ((c * g * c⁻¹ : uU xunH 6) : GL (Fin 6) xunK) *
      (π : GL (Fin 6) xunK)⁻¹ = _
    rw [hπ, hgv', hw]
    exact TauCeti.permutationGL_mul_diagGL_mul_inv τ v
  have hw4 : ∀ i : Fin 6, (i : ℕ) < 4 → w i = 1 := by
    intro i hi
    rw [hw]
    refine hkl _ (fun h => ?_) (fun h => ?_)
    · rw [Equiv.Perm.inv_eq_iff_eq] at h
      have := congrArg Fin.val h
      omega
    · rw [Equiv.Perm.inv_eq_iff_eq] at h
      have := congrArg Fin.val h
      omega
  obtain ⟨m, hm⟩ : ∃ m, v m ≠ 1 := by
    by_contra h
    push Not at h
    exact hv1 (funext h)
  have hjm : w (τ m) = v m := by simp only [hw, Equiv.Perm.coe_inv, Equiv.symm_apply_apply]
  have hpow : ∀ t ∈ Subgroup.zpowers (x * g * x⁻¹),
      ∃ n : ℤ, (t : GL (Fin 6) xunK) = TauCeti.diagGL (w ^ n) := by
    intro t ht
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
    exact ⟨n, by rw [Subgroup.coe_zpow, hd', map_zpow]⟩
  have hdiag : ∀ t ∈ Subgroup.zpowers (x * g * x⁻¹), IsDiagU 6 (t : GL (Fin 6) xunK) := by
    intro t ht i j hij
    obtain ⟨n, hn⟩ := hpow t ht
    rw [hn, TauCeti.diagGL_coe, Matrix.diagonal_apply_ne _ hij]
  have hfour : ∀ t ∈ Subgroup.zpowers (x * g * x⁻¹), ∀ j : Fin 6, (j : ℕ) < 4 →
      dgl (t : GL (Fin 6) xunK) j = dgl (t : GL (Fin 6) xunK) 0 := by
    intro t ht j hj
    obtain ⟨n, hn⟩ := hpow t ht
    simp only [dgl, hn, TauCeti.diagGL_coe, Matrix.diagonal_apply_eq, Pi.pow_apply, hw4 j hj,
      hw4 0 (by decide)]
  have hdgl : ∀ j, dgl ((x * g * x⁻¹ : uU xunH 6) : GL (Fin 6) xunK) j = (w j : xunK) := by
    intro j
    simp only [dgl, hd', TauCeti.diagGL_coe, Matrix.diagonal_apply_eq]
  have hgood := isGood_of_torus hN1 (by norm_num) (0 : Fin 6) rfl _ hdiag hfour
    ⟨x * g * x⁻¹, Subgroup.mem_zpowers _, τ m, by
      rw [hdgl, hdgl, hjm, hw4 0 (by decide)]
      exact fun h => hm (Units.ext h)⟩
  rw [MonoidHom.map_zpowers] at hgood
  refine ⟨g, hg, fun h1 => ?_, ?_⟩
  · have h2 : xunConj 6 hN1 (x * g * x⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, h1, mul_one (xunConj 6 hN1 x),
        mul_inv_cancel (xunConj 6 hN1 x)]
    obtain ⟨c', hc'⟩ := (uConjAut_eq_one_iff xunH (by norm_num) (x * g * x⁻¹)).1 h2
    rw [hd'] at hc'
    have e1 := congrArg (fun A : GL (Fin 6) xunK => (A : Matrix (Fin 6) (Fin 6) xunK) (τ m) (τ m))
      hc'
    have e0 := congrArg (fun A : GL (Fin 6) xunK => (A : Matrix (Fin 6) (Fin 6) xunK) 0 0) hc'
    simp only [TauCeti.diagGL_coe, Matrix.diagonal_apply_eq, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply] at e1 e0
    apply hm
    calc v m = w (τ m) := hjm.symm
      _ = w 0 := Units.ext (e1.trans e0.symm)
      _ = 1 := hw4 0 (by decide)
  · rw [isGood_iff_map_mulEquiv (xunConj 6 hN1 x), MonoidHom.map_zpowers]
    have h3 : (MulAut.congr (xunConj 6 hN1 x)).toMonoidHom (xunConj 6 hN1 g) =
        xunConj 6 hN1 (x * g * x⁻¹) := by
      rw [map_mul, map_mul, map_inv]
      exact mulAut_congr_eq_conj (xunConj 6 hN1 x) (xunConj 6 hN1 g)
    rw [h3]
    exact hgood

end CFSG.LocalAnalysis.GLTheoremA.S265.BTwE6

end
