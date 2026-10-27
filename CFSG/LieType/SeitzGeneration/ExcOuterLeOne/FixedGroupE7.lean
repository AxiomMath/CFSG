module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotUniqueFieldTorus

open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.SeitzReduction.E6Pilot

public section

namespace CFSG.LieType.SeitzGeneration.ExcOuterLeOne


section Square

theorem square_of_pow_eq {G : Type*} [CommGroup G] {b n : G} {p : ℕ} (hcop : Nat.Coprime p 2)
    (h : n ^ 2 = b ^ p) : ∃ y : G, b = y ^ 2 := by
  obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, u * p + v * 2 = 1 := by
    have := Nat.isCoprime_iff_coprime.2 hcop
    obtain ⟨u, v, h⟩ := this
    exact ⟨u, v, h⟩
  refine ⟨n ^ u * b ^ v, ?_⟩
  have e1 : b ^ (u * (p : ℤ)) = (n ^ u) ^ 2 := by
    calc b ^ (u * (p : ℤ)) = (b ^ p) ^ u := by rw [mul_comm, zpow_mul, zpow_natCast]
      _ = (n ^ 2) ^ u := by rw [h]
      _ = (n ^ u) ^ 2 := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
  have e2 : b ^ (v * (2 : ℤ)) = (b ^ v) ^ 2 := by
    rw [zpow_mul, zpow_ofNat]
  calc b = b ^ (u * (p : ℤ) + v * 2) := by rw [huv, zpow_one]
    _ = (n ^ u * b ^ v) ^ 2 := by rw [zpow_add, e1, e2, mul_pow]

variable {K : Type} [Field K]

theorem exists_square_of_pow_eq (σ : K ≃+* K) {p : ℕ} (hσp : σ ^ p = 1) (hcop : Nat.Coprime p 2)
    (b : (fixSubfield σ)ˣ) (d : Kˣ)
    (hbd : Units.map (fixSubfield σ).subtype.toMonoidHom b = d ^ 2) :
    ∃ y : (fixSubfield σ)ˣ, b = y ^ 2 := by
  classical
  set f : ℕ → K := fun i => (σ ^ i) (d : K) with hf
  have hfsucc : ∀ i, σ (f i) = f (i + 1) := fun i => by
    simp only [hf, pow_succ']
    rfl
  have hfp : f p = f 0 := by simp only [hf, hσp, pow_zero]
  set n : K := ∏ i ∈ Finset.range p, f i with hn
  have hd0 : f 0 ≠ 0 := by simp only [hf, pow_zero]; exact d.ne_zero
  have hσn : σ n = n := by
    rw [hn, map_prod]
    simp only [hfsucc]
    have h1 := Finset.prod_range_succ' f p
    have h2 := Finset.prod_range_succ f p
    rw [hfp] at h2
    exact mul_right_cancel₀ hd0 (h1.symm.trans h2)
  have hb : ((b : fixSubfield σ) : K) = (d : K) ^ 2 := by
    have := congrArg Units.val hbd
    simpa using this
  have hσb : σ ((b : fixSubfield σ) : K) = (b : fixSubfield σ) :=
    (mem_fixSubfield σ).1 (b : fixSubfield σ).2
  have hn2 : n ^ 2 = ((b : fixSubfield σ) : K) ^ p := by
    rw [hn, ← Finset.prod_pow]
    have : ∀ i, f i ^ 2 = ((b : fixSubfield σ) : K) := by
      intro i
      induction i with
      | zero => simp only [hf, pow_zero]; exact hb.symm
      | succ i ih => rw [← hfsucc, ← map_pow, ih, hσb]
    simp [this]
  have hn0 : n ≠ 0 := by
    rw [hn]
    exact Finset.prod_ne_zero_iff.2 fun i _ => by
      simp only [hf]
      exact fun h => d.ne_zero ((map_eq_zero _).1 h)
  set n' : fixSubfield σ := ⟨n, (mem_fixSubfield σ).2 hσn⟩ with hn'
  have hn'0 : n' ≠ 0 := fun h => hn0 (congrArg Subtype.val h)
  have hn2' : (Units.mk0 n' hn'0) ^ 2 = b ^ p := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0]
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, SubmonoidClass.coe_pow]
    exact hn2
  exact square_of_pow_eq hcop hn2'

end Square

section Descent

open CFSG.Timmesfeld.ExceptionalOrders (smithE7 smithE7P smithE7P' smithE7Q smithE7Q' smithE7D
  smithE7P'_mul smithE7Q_mul smithE7P_mul)

variable {K : Type} [Field K]

theorem smithE7Q'_mul : smithE7Q' * smithE7Q = 1 := by decide

@[expose] def nodeSevenE7 : Fin Tag.E7.rank := ⟨6, by decide⟩

theorem smithE7D_eq : ∀ i : Fin Tag.E7.rank, smithE7D i = if i = nodeSevenE7 then 2 else 1 := by
  decide

theorem cartan_transpose_E7 : Tag.E7.cartan.transpose =
    smithE7Q.transpose * Matrix.diagonal (fun i => (smithE7D i : ℤ)) * smithE7P.transpose := by
  rw [smithE7, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.diagonal_transpose,
    Matrix.mul_assoc]

theorem exists_monomial_eq_of_pow_E7 (σ : K ≃+* K) {p : ℕ} (hσp : σ ^ p = 1)
    (hcop : Nat.Coprime p 2)
    (a : Fin Tag.E7.rank → (fixSubfield σ)ˣ) (c : Fin Tag.E7.rank → Kˣ)
    (hac : (fun i => Units.map (fixSubfield σ).subtype.toMonoidHom (a i)) =
      monomialHom Tag.E7.cartan.transpose c) :
    ∃ s : Fin Tag.E7.rank → (fixSubfield σ)ˣ, monomialHom Tag.E7.cartan.transpose s = a := by
  set ι : (fixSubfield σ)ˣ →* Kˣ := Units.map (fixSubfield σ).subtype.toMonoidHom with hι
  set Dm : Matrix (Fin Tag.E7.rank) (Fin Tag.E7.rank) ℤ :=
    Matrix.diagonal (fun i => (smithE7D i : ℤ)) with hDm
  have hA := cartan_transpose_E7
  have hQQ : smithE7Q'.transpose * smithE7Q.transpose = 1 := by
    rw [← Matrix.transpose_mul, smithE7Q_mul, Matrix.transpose_one]
  have hQQ' : smithE7Q.transpose * smithE7Q'.transpose = 1 := by
    rw [← Matrix.transpose_mul, smithE7Q'_mul, Matrix.transpose_one]
  have hPP : smithE7P.transpose * smithE7P'.transpose = 1 := by
    rw [← Matrix.transpose_mul, smithE7P'_mul, Matrix.transpose_one]
  set b := monomialHom smithE7Q'.transpose a with hbdef
  have hb : (fun i => ι (b i)) = monomialHom Dm (monomialHom smithE7P.transpose c) := by
    rw [hbdef, map_monomialHom ι, hac, monomialHom_mul, hA, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, hQQ, Matrix.one_mul, ← monomialHom_mul]
  have h5 : ι (b nodeSevenE7) = (monomialHom smithE7P.transpose c nodeSevenE7) ^ 2 := by
    rw [show ι (b nodeSevenE7) = monomialHom Dm (monomialHom smithE7P.transpose c) nodeSevenE7 from
      congrFun hb nodeSevenE7, hDm, monomialHom_diagonal, smithE7D_eq]
    simp
  obtain ⟨y, hy⟩ := exists_square_of_pow_eq σ hσp hcop (b nodeSevenE7) _ h5
  set b' := Function.update b nodeSevenE7 y with hb'def
  have hb' : monomialHom Dm b' = b := by
    funext i
    rw [hDm, monomialHom_diagonal, smithE7D_eq]
    by_cases hi : i = nodeSevenE7
    · subst hi
      simp [hb'def, hy]
    · simp [hb'def, hi]
  refine ⟨monomialHom smithE7P'.transpose b', ?_⟩
  rw [monomialHom_mul, hA, Matrix.mul_assoc, hPP, Matrix.mul_one, ← monomialHom_mul, hb', hbdef,
    monomialHom_mul, hQQ', monomialHom_one]

end Descent

section Torus

variable {K : Type} [Field K]

theorem entrywiseFixedTorus_le_fixedFieldImage_E7_of_pow (σ : K ≃+* K) {p : ℕ}
    (hσp : σ ^ p = 1) (hcop : Nat.Coprime p 2) :
    entrywiseFixedTorus .E7 σ ≤ fixedFieldImage .E7 σ := by
  set k := fixSubfield σ with hk
  set ι : k →+* K := k.subtype with hι
  rintro h ⟨hT, hΓ⟩
  obtain ⟨c, rfl⟩ := torusGroup_le_range_rootDiagUnit_monomial (K := K) Tag.E7 hT
  set a := monomialHom Tag.E7.cartan.transpose c with ha
  have hh : ((rootDiagUnitHom Tag.E7 K).comp (monomialHom Tag.E7.cartan.transpose)) c =
      rootDiagUnit Tag.E7 a := rfl
  rw [hh] at hΓ ⊢
  have hσa : ∀ i, σ (a i : K) = a i := by
    have hF : Units.map (entrywiseHom σ.toRingHom) (rootDiagUnit Tag.E7 a) =
        rootDiagUnit Tag.E7 a := hΓ.2
    have h0 : Units.map (entrywiseHom σ.toRingHom) (rootDiagUnit Tag.E7 a) =
        rootDiagUnit Tag.E7 (fun i => Units.map σ.toRingHom.toMonoidHom (a i)) :=
      Units.ext (entrywise_rootDiag σ.toRingHom a)
    have h1 := rootDiagUnit_injective (h0.symm.trans hF)
    intro i
    exact congrArg Units.val (congrFun h1 i)
  set a' : Fin Tag.E7.rank → kˣ := fun i =>
    Units.mk0 ⟨a i, hσa i⟩ fun h0 => (a i).ne_zero (congrArg Subtype.val h0) with ha'def
  have ha' : (fun i => Units.map ι.toMonoidHom (a' i)) = a := funext fun i => Units.ext rfl
  obtain ⟨s, hs⟩ := exists_monomial_eq_of_pow_E7 σ hσp hcop a' c ha'
  rw [← ha', ← hs]
  have hprod : rootDiagUnit Tag.E7
      (fun i => Units.map ι.toMonoidHom (monomialHom Tag.E7.cartan.transpose s i)) =
      ((List.finRange Tag.E7.rank).map fun j =>
        torusElt Tag.E7 K j (Units.map ι.toMonoidHom (s j))).prod := by
    rw [list_prod_torusElt_eq_rootDiagUnit]
    congr 1
    funext l
    rw [monomialHom_apply, cartanChar, map_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [map_zpow, Matrix.transpose_apply]
  rw [hprod]
  have hmem : ((List.finRange Tag.E7.rank).map fun j => torusElt Tag.E7 k j (s j)).prod ∈
      adjointGroup Tag.E7 k := Subgroup.list_prod_mem _ fun g hg => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hg
    exact torusElt_mem_adjointGroup j _
  refine ⟨_, hmem, ?_⟩
  rw [map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left fun j _ => baseChangeGL_torusElt ι j (s j)

variable [Finite K]

theorem entrywiseFixedGroup_eq_fixedFieldImage_E7_of_pow (σ : K ≃+* K) {p : ℕ}
    (hσp : σ ^ p = 1) (hcop : Nat.Coprime p 2) :
    entrywiseFixedGroup .E7 σ = fixedFieldImage .E7 σ := by
  obtain ⟨-, -, -, hJΓ, hΓ, -⟩ := Chevalley_coordinate_field_fixed_normal_subgroup .E7 K σ
  refine le_antisymm (fun g hg => ?_) hJΓ
  have hg' : g ∈ (entrywiseFixedGroup .E7 σ : Set (ModGL .E7 K)) := hg
  rw [hΓ] at hg'
  obtain ⟨h, hh, j, hj, rfl⟩ := Set.mem_mul.1 hg'
  exact mul_mem (entrywiseFixedTorus_le_fixedFieldImage_E7_of_pow σ hσp hcop hh) hj

end Torus

theorem entrywiseFixedGroup_E7_eq_of_odd_pow {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hσp : σ ^ p = 1) :
    entrywiseFixedGroup Tag.E7 σ = fixedFieldImage Tag.E7 σ :=
  entrywiseFixedGroup_eq_fixedFieldImage_E7_of_pow σ hσp
    ((Nat.coprime_primes hp Nat.prime_two).2 hp2)

theorem entrywiseFixedGroup_E7_eq_of_pow {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hσp : σ ^ p = 1) :
    entrywiseFixedGroup Tag.E7 σ = fixedFieldImage Tag.E7 σ :=
  entrywiseFixedGroup_E7_eq_of_odd_pow σ hp (by omega) hσp

end CFSG.LieType.SeitzGeneration.ExcOuterLeOne
