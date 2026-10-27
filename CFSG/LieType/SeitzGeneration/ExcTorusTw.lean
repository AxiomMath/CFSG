module

public import CFSG.LieType.SeitzGeneration.ExcTorusTors
public import CFSG.LieType.SeitzGeneration.ExcTorusArithInt
public import CFSG.RankThree.PartOne.KE.CTTwisted

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2 Polynomial
open scoped Matrix Pointwise
open CFSG.RankThree.Lattice

theorem natAbs_neg_pow_sub_one_even (q : ℕ) (hq : 1 ≤ q) {d : ℕ} (hd : Even d) :
    ((-(q : ℤ)) ^ d - 1).natAbs = q ^ d - 1 := by
  rw [hd.neg_pow]
  have h : 1 ≤ q ^ d := Nat.one_le_pow _ _ hq
  have : ((q : ℤ) ^ d - 1) = ((q ^ d - 1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub h]
    push_cast
    ring
  rw [this, Int.natAbs_natCast]

theorem natAbs_neg_pow_sub_one_odd (q : ℕ) {d : ℕ} (hd : Odd d) :
    ((-(q : ℤ)) ^ d - 1).natAbs = q ^ d + 1 := by
  rw [hd.neg_pow]
  have : (-(q : ℤ) ^ d - 1) = -((q ^ d + 1 : ℕ) : ℤ) := by
    push_cast
    ring
  rw [this, Int.natAbs_neg, Int.natAbs_natCast]

theorem not_dvd_cyclotomic_eval_of_mem_small {p q e : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (he : orderOf (q : ZMod p) = e) (ds : List ℕ) (hso : ∀ d ∈ ds, d ≠ e → d ∈ [1, 2, 3, 4, 6]) :
    ¬ (p : ℤ) ∣ (((ds.filter fun d => d ≠ e).map fun d => cyclotomic d ℤ).prod).eval (q : ℤ) := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  rw [eval_list_prod, hpz.dvd_prod_iff]
  rintro ⟨a, ha, hpa⟩
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ha
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
  rw [List.mem_filter] at hd
  have hde : d ≠ e := by simpa using hd.2
  exact not_dvd_cyclotomic_eval_of_ne hp he hde (not_dvd_small hp h5 (hso d hd.1 hde)) hpa


@[expose] def twE6PermList : List (List ℤ) :=
  [[0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 1, 0, 0],
   [0, 0, 1, 0, 0, 0], [1, 0, 0, 0, 0, 0]]

theorem toMat_twE6PermList : toMat TwistTag.E6.tag.rank twE6PermList =
    Matrix.of (fun i j => if j = TwistTag.E6.perm.symm i then (1 : ℤ) else 0) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem permLattice_E6_eq (x : Fin TwistTag.E6.tag.rank → ℤ) :
    permLattice TwistTag.E6.perm x = toMat TwistTag.E6.tag.rank twE6PermList *ᵥ x := by
  rw [toMat_twE6PermList]
  funext i
  change x (TwistTag.E6.perm.symm i) =
    ∑ j : Fin TwistTag.E6.tag.rank, (if j = TwistTag.E6.perm.symm i then (1 : ℤ) else 0) * x j
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp

section Order


theorem ordProj_card_twistedE6 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpq : ¬ p ∣ ℓ ^ f) :
    p ^ (Nat.card (twistedE6RootGroup K σ)).factorization p =
      ((degreesE Tag.E6).map fun d =>
        p ^ ((((-((ℓ ^ f : ℕ) : ℤ)) ^ d - 1).natAbs).factorization p)).prod := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hK0 : Nat.card K ≠ 0 := by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero)
  have : Finite K := Nat.finite_of_card_ne_zero hK0
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  let L := AlgebraicClosure K
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  let Fr : L →+* L := iterateFrobenius L ℓ f
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  obtain ⟨-, -, -, -, -, hRcard, hpp⟩ :=
    twisted_E6_full_rational_fixed_group_order hℓ hf K hK σ.toRingHom hσ L Fr hFr
  have h1 := hpp p hp hp3
  have h2 : Nat.card ((graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map
      (baseChangeGL (algebraMap K L))) = Nat.card (twistedE6RootGroup K σ) :=
    Subgroup.card_map_of_injective (baseChangeGL_injective _)
  rw [h2, hRcard] at h1
  rw [h1]
  set q := ℓ ^ f with hq
  have hq2 : 2 ≤ q := Nat.one_lt_pow (by omega) hℓ.one_lt
  have hq1 : 1 ≤ q := by omega
  have hnz : ∀ d : ℕ, 0 < d → q ^ d - 1 ≠ 0 := fun d hd => by
    have : 1 < q ^ d := Nat.one_lt_pow hd.ne' (by omega)
    omega
  have hnz2 : ∀ d : ℕ, q ^ d + 1 ≠ 0 := fun d => by omega
  have hpq' : ¬ p ∣ q ^ 36 := fun h => hpq (hp.dvd_of_dvd_pow h)
  simp only [degreesE, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [natAbs_neg_pow_sub_one_even q hq1 (by decide : Even 2),
    natAbs_neg_pow_sub_one_odd q (by decide : Odd 5),
    natAbs_neg_pow_sub_one_even q hq1 (by decide : Even 6),
    natAbs_neg_pow_sub_one_even q hq1 (by decide : Even 8),
    natAbs_neg_pow_sub_one_odd q (by decide : Odd 9),
    natAbs_neg_pow_sub_one_even q hq1 (by decide : Even 12)]
  have hqne : q ^ 36 ≠ 0 := pow_ne_zero _ (by omega)
  rw [Nat.ordProj_mul p (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hqne
    (hnz 12 (by norm_num))) (hnz2 9)) (hnz 8 (by norm_num))) (hnz 6 (by norm_num)))
    (hnz2 5)) (hnz 2 (by norm_num)),
    Nat.ordProj_mul p (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hqne
    (hnz 12 (by norm_num))) (hnz2 9)) (hnz 8 (by norm_num))) (hnz 6 (by norm_num)))
    (hnz2 5),
    Nat.ordProj_mul p (mul_ne_zero (mul_ne_zero (mul_ne_zero hqne
    (hnz 12 (by norm_num))) (hnz2 9)) (hnz 8 (by norm_num))) (hnz 6 (by norm_num)),
    Nat.ordProj_mul p (mul_ne_zero (mul_ne_zero hqne (hnz 12 (by norm_num))) (hnz2 9))
    (hnz 8 (by norm_num)),
    Nat.ordProj_mul p (mul_ne_zero hqne (hnz 12 (by norm_num))) (hnz2 9),
    Nat.ordProj_mul p hqne (hnz 12 (by norm_num)), ordProj_eq_one_of_not_dvd' hpq', one_mul]
  ring

end Order

section Assembly


theorem exists_elemAbelian_twistedE6 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpq : ¬ p ∣ ℓ ^ f)
    {M : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ}
    (v : WeylGroup TwistTag.E6.tag)
    (hv : ∀ x, v • x = M *ᵥ permLattice TwistTag.E6.perm x) {n e m : ℕ} (R : ℤ[X])
    (hn0 : n ≠ 0) (hpow : M ^ n = 1) (hn : ¬ p ∣ n)
    (hchar : M.charpoly = cyclotomic e ℤ ^ m * R)
    (he : orderOf (((ℓ ^ f : ℕ)) : ZMod p) = e)
    (hR : ¬ (p : ℤ) ∣ R.eval ((ℓ ^ f : ℕ) : ℤ)) :
    ∃ E : Subgroup (twistedE6RootGroup K σ), IsElemAbelian p E ∧ Nat.card E = p ^ m := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fact p.Prime := ⟨hp⟩
  have hK0 : Nat.card K ≠ 0 := by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero)
  have : Finite K := Nat.finite_of_card_ne_zero hK0
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  let L := AlgebraicClosure K
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  let Fr : L →+* L := iterateFrobenius L ℓ f
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hq2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  have he0 : e ≠ 0 := he ▸ orderOf_natCast_ne_zero hp hpq
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator_twisted K (ℓ := ℓ) (f := f) hf L v
  obtain ⟨-, -, hder, ⟨k, hk⟩, -, hRcard, hpp⟩ :=
    twisted_E6_full_rational_fixed_group_order hℓ hf K hK σ.toRingHom hσ L Fr hFr
  set R' := twistedFixedGroup TwistTag.E6 L Fr with hR'
  set C' := (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map
    (baseChangeGL (algebraMap K L)) with hC'
  have hle : C' ≤ R' := by
    rw [← hder]
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hnormal : (C'.subgroupOf R').Normal := by
    have e : C'.subgroupOf R' = ⁅(⊤ : Subgroup R'), ⊤⁆ := by
      have h1 : ⁅R', R'⁆ = Subgroup.map R'.subtype ⁅(⊤ : Subgroup R'), ⊤⁆ := by
        rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map R'.subtype, Subgroup.range_subtype]
      rw [← hder, h1]
      exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
    rw [e]
    infer_instance
  let ι : twistedE6RootGroup K σ →* ModGL TwistTag.E6.tag L :=
    (baseChangeGL (algebraMap K L)).comp (twistedE6RootGroup K σ).subtype
  have hrange : ι.range = C' := by
    change ((baseChangeGL (algebraMap K L)).comp (twistedE6RootGroup K σ).subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hι : Function.Injective ι :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  have hrat : ∀ (X : Subgroup (ModGL TwistTag.E6.tag L)) [Finite X],
      X ≤ adjointGroup TwistTag.E6.tag L → (∀ x ∈ X, twistHom TwistTag.E6 L Fr x = x) →
      ∀ P : Subgroup (ModGL TwistTag.E6.tag L), P ≤ X → IsPGroup p P → P ≤ ι.range := by
    intro X _ hXC hXF P hPX hP
    have hXR : X ≤ R' := fun x hx =>
      (mem_twistedFixedGroup_iff_twistHom _ _ _).2 ⟨hXC hx, hXF x hx⟩
    rw [hrange]
    have : Finite P :=
      Finite.of_injective (Subgroup.inclusion hPX) (Subgroup.inclusion_injective hPX)
    exact le_of_isPGroup_of_index_eq_pow (hPX.trans hXR) hp Nat.prime_three (by omega) hk hP
  have hT0 := twistedTorus_E6_eq_map (L := L) Fr v M hv
  have hcomm : IsMulCommutative (twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) L v)
      (twistHom TwistTag.E6 L Fr)) := by
    rw [hT0]
    exact isMulCommutative_map _ inferInstance
  set B : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ :=
    M - ((ℓ ^ f : ℕ) : ℤ) • (1 : Matrix _ _ ℤ) with hB
  have hdetB : B.det.natAbs = (M.charpoly.eval ((ℓ ^ f : ℕ) : ℤ)).natAbs :=
    (natAbs_eval_charpoly M _).symm
  have hpos : 0 < (cyclotomic e ℤ).eval ((ℓ ^ f : ℕ) : ℤ) :=
    cyclotomic_pos' e (by exact_mod_cast hq2)
  have hRne : R.eval ((ℓ ^ f : ℕ) : ℤ) ≠ 0 := fun h => hR (by rw [h]; exact dvd_zero _)
  have hev : M.charpoly.eval ((ℓ ^ f : ℕ) : ℤ) ≠ 0 := by
    rw [hchar, eval_mul, eval_pow]
    exact mul_ne_zero (pow_ne_zero m hpos.ne') hRne
  have hBne : B.det ≠ 0 := fun h => hev (Int.natAbs_eq_zero.1 (hdetB ▸ by rw [h]; rfl))
  have hcop := not_dvd_natAbs_det_sub hℓ (dvd_pow_self ℓ (by omega) : ℓ ∣ ℓ ^ f) M hn0 hpow
  have hcard : Nat.card (twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) L v)
      (twistHom TwistTag.E6 L Fr)) = (M.charpoly.eval ((ℓ ^ f : ℕ) : ℤ)).natAbs := by
    rw [hT0, Subgroup.card_map_of_injective rootDiagUnit_injective,
      natCard_fixedCharTuples M Fr hFr hBne hcop, hdetB]
  have hpℓ : p ≠ ℓ := fun h => hpq (by rw [h]; exact dvd_pow_self ℓ (by omega))
  have htors : Nat.card (torsionSubgroup (twistedTorusOf
      (canonicalRep (coxeterSystem TwistTag.E6.tag) L v) (twistHom TwistTag.E6 L Fr)) hcomm p) =
      p ^ m := by
    rw [natCard_torsion_eq (fixedCharTuples M Fr) _ hT0 hcomm p,
      natCard_fixedTorsion M Fr hℓ hFr hp hpℓ,
      natCard_solutions_modMat hp M R hpow hn hchar hpq he hR]
  exact exists_elemAbelian_of_twisted_torus ι hι (twistHom TwistTag.E6 L Fr)
    (canonicalRep (coxeterSystem TwistTag.E6.tag) L v) g0 hg0C hg0 hp (Int.natAbs_ne_zero.2 hev)
    hrat hcomm hcard htors

theorem sylowTorus_twistedE6 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpq : ¬ p ∣ ℓ ^ f)
    {M : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ}
    (v : WeylGroup TwistTag.E6.tag)
    (hv : ∀ x, v • x = M *ᵥ permLattice TwistTag.E6.perm x) {n e m : ℕ} (R : ℤ[X])
    (hn0 : n ≠ 0) (hpow : M ^ n = 1) (hn : ¬ p ∣ n)
    (hchar : M.charpoly = cyclotomic e ℤ ^ m * R)
    (he : orderOf (((ℓ ^ f : ℕ)) : ZMod p) = e)
    (hR : ¬ (p : ℤ) ∣ R.eval ((ℓ ^ f : ℕ) : ℤ))
    (hord : p ^ (Nat.card (twistedE6RootGroup K σ)).factorization p =
      (p ^ ((ℓ ^ f) ^ e - 1).factorization p) ^ m) :
    SylowTorus (twistedE6RootGroup K σ) p m := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fact p.Prime := ⟨hp⟩
  have hK0 : Nat.card K ≠ 0 := by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero)
  have : Finite K := Nat.finite_of_card_ne_zero hK0
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  let L := AlgebraicClosure K
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  let Fr : L →+* L := iterateFrobenius L ℓ f
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hq2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  have he0 : e ≠ 0 := he ▸ orderOf_natCast_ne_zero hp hpq
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator_twisted K (ℓ := ℓ) (f := f) hf L v
  obtain ⟨-, -, hder, ⟨k, hk⟩, -, hRcard, hpp⟩ :=
    twisted_E6_full_rational_fixed_group_order hℓ hf K hK σ.toRingHom hσ L Fr hFr
  set R' := twistedFixedGroup TwistTag.E6 L Fr with hR'
  set C' := (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map
    (baseChangeGL (algebraMap K L)) with hC'
  have hle : C' ≤ R' := by
    rw [← hder]
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hnormal : (C'.subgroupOf R').Normal := by
    have e : C'.subgroupOf R' = ⁅(⊤ : Subgroup R'), ⊤⁆ := by
      have h1 : ⁅R', R'⁆ = Subgroup.map R'.subtype ⁅(⊤ : Subgroup R'), ⊤⁆ := by
        rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map R'.subtype, Subgroup.range_subtype]
      rw [← hder, h1]
      exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
    rw [e]
    infer_instance
  let ι : twistedE6RootGroup K σ →* ModGL TwistTag.E6.tag L :=
    (baseChangeGL (algebraMap K L)).comp (twistedE6RootGroup K σ).subtype
  have hrange : ι.range = C' := by
    change ((baseChangeGL (algebraMap K L)).comp (twistedE6RootGroup K σ).subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hι : Function.Injective ι :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  have hrat : ∀ (X : Subgroup (ModGL TwistTag.E6.tag L)) [Finite X],
      X ≤ adjointGroup TwistTag.E6.tag L → (∀ x ∈ X, twistHom TwistTag.E6 L Fr x = x) →
      ∀ P : Subgroup (ModGL TwistTag.E6.tag L), P ≤ X → IsPGroup p P → P ≤ ι.range := by
    intro X _ hXC hXF P hPX hP
    have hXR : X ≤ R' := fun x hx =>
      (mem_twistedFixedGroup_iff_twistHom _ _ _).2 ⟨hXC hx, hXF x hx⟩
    rw [hrange]
    have : Finite P :=
      Finite.of_injective (Subgroup.inclusion hPX) (Subgroup.inclusion_injective hPX)
    exact le_of_isPGroup_of_index_eq_pow (hPX.trans hXR) hp Nat.prime_three (by omega) hk hP
  have hT0 := twistedTorus_E6_eq_map (L := L) Fr v M hv
  have hcomm : IsMulCommutative (twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) L v)
      (twistHom TwistTag.E6 L Fr)) := by
    rw [hT0]
    exact isMulCommutative_map _ inferInstance
  set B : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ :=
    M - ((ℓ ^ f : ℕ) : ℤ) • (1 : Matrix _ _ ℤ) with hB
  have hdetB : B.det.natAbs = (M.charpoly.eval ((ℓ ^ f : ℕ) : ℤ)).natAbs :=
    (natAbs_eval_charpoly M _).symm
  have hpos : 0 < (cyclotomic e ℤ).eval ((ℓ ^ f : ℕ) : ℤ) :=
    cyclotomic_pos' e (by exact_mod_cast hq2)
  have hRne : R.eval ((ℓ ^ f : ℕ) : ℤ) ≠ 0 := fun h => hR (by rw [h]; exact dvd_zero _)
  have hev : M.charpoly.eval ((ℓ ^ f : ℕ) : ℤ) ≠ 0 := by
    rw [hchar, eval_mul, eval_pow]
    exact mul_ne_zero (pow_ne_zero m hpos.ne') hRne
  have hBne : B.det ≠ 0 := fun h => hev (Int.natAbs_eq_zero.1 (hdetB ▸ by rw [h]; rfl))
  have hcop := not_dvd_natAbs_det_sub hℓ (dvd_pow_self ℓ (by omega) : ℓ ∣ ℓ ^ f) M hn0 hpow
  have hcard : Nat.card (twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) L v)
      (twistHom TwistTag.E6 L Fr)) = (M.charpoly.eval ((ℓ ^ f : ℕ) : ℤ)).natAbs := by
    rw [hT0, Subgroup.card_map_of_injective rootDiagUnit_injective,
      natCard_fixedCharTuples M Fr hFr hBne hcop, hdetB]
  have hpℓ : p ≠ ℓ := fun h => hpq (by rw [h]; exact dvd_pow_self ℓ (by omega))
  have htors : Nat.card (torsionSubgroup (twistedTorusOf
      (canonicalRep (coxeterSystem TwistTag.E6.tag) L v) (twistHom TwistTag.E6 L Fr)) hcomm p) =
      p ^ m := by
    rw [natCard_torsion_eq (fixedCharTuples M Fr) _ hT0 hcomm p,
      natCard_fixedTorsion M Fr hℓ hFr hp hpℓ,
      natCard_solutions_modMat hp M R hpow hn hchar hpq he hR]
  have hordN : p ^ (Nat.card (twistedE6RootGroup K σ)).factorization p =
      p ^ ((M.charpoly.eval ((ℓ ^ f : ℕ) : ℤ)).natAbs).factorization p := by
    rw [hord, hchar, ordProj_cyclotomic_pow_mul_eval hp hq2 he he0 hR]
  exact sylowTorus_of_twisted_torus ι hι (twistHom TwistTag.E6 L Fr)
    (canonicalRep (coxeterSystem TwistTag.E6.tag) L v) g0 hg0C hg0 hp (Int.natAbs_ne_zero.2 hev)
    hrat hcomm hcard htors hordN

end Assembly

section Blocks


theorem exists_elemAbelian_twistedE6_of_blocks {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    {M : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ}
    (v : WeylGroup TwistTag.E6.tag) (hv : ∀ x, v • x = M *ᵥ permLattice TwistTag.E6.perm x)
    (ds : List ℕ) {n e : ℕ} (hchar : M.charpoly = (ds.map fun d => cyclotomic d ℤ).prod)
    (hn0 : n ≠ 0) (hpow : M ^ n = 1) (hnd : n = e ∨ n ∈ [1, 2, 3, 4, 6])
    (he : orderOf (((ℓ ^ f : ℕ)) : ZMod p) = e) (he0 : e ≠ 0)
    (hso : ∀ d ∈ ds, d ≠ e → d ∈ [1, 2, 3, 4, 6]) :
    ∃ E : Subgroup (twistedE6RootGroup K σ), IsElemAbelian p E ∧ Nat.card E = p ^ ds.count e := by
  have hpq : ¬ p ∣ ℓ ^ f := not_dvd_of_orderOf_pos hp he he0
  have h5 := five_le_of_three_lt hp hp3
  have hn : ¬ p ∣ n := by
    rcases hnd with rfl | hn
    · exact not_dvd_of_orderOf hp hpq he
    · exact not_dvd_small hp h5 hn
  have hchar' : M.charpoly = cyclotomic e ℤ ^ ds.count e *
      ((ds.filter fun d => d ≠ e).map fun d => cyclotomic d ℤ).prod := by
    rw [hchar, prod_cyclotomic_split e ds]
  exact exists_elemAbelian_twistedE6 hℓ hf K hK σ hσ hp hp3 hpq v hv _ hn0 hpow hn hchar' he
    (not_dvd_cyclotomic_eval_of_mem_small hp h5 he ds hso)

theorem sylowTorus_twistedE6_of_blocks {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime)
    {M : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ}
    (v : WeylGroup TwistTag.E6.tag) (hv : ∀ x, v • x = M *ᵥ permLattice TwistTag.E6.perm x)
    (ds : List ℕ) {n e e' : ℕ} (hchar : M.charpoly = (ds.map fun d => cyclotomic d ℤ).prod)
    (hn0 : n ≠ 0) (hpow : M ^ n = 1) (hnd : n = e ∨ n ∈ [1, 2, 3, 4, 6])
    (he : orderOf (((ℓ ^ f : ℕ)) : ZMod p) = e) (he3 : 3 ≤ e)
    (he' : orderOf (((-((ℓ ^ f : ℕ) : ℤ) : ℤ)) : ZMod p) = e')
    (hΦ : ∀ x : ℤ, ((cyclotomic e' ℤ).eval (-x)).natAbs = ((cyclotomic e ℤ).eval x).natAbs)
    (hso : ∀ d ∈ ds, d ≠ e → d ∈ [1, 2, 3, 4, 6])
    (hQ : ∀ d ∈ degreesE Tag.E6, e' ∣ d → d / e' ∈ [1, 2, 3, 4, 6])
    (hcount : ((degreesE Tag.E6).filter fun d => e' ∣ d).length = ds.count e) :
    SylowTorus (twistedE6RootGroup K σ) p (ds.count e) := by
  have he0 : e ≠ 0 := by omega
  have hpq : ¬ p ∣ ℓ ^ f := not_dvd_of_orderOf_pos hp he he0
  have hlt : e < p := orderOf_lt_prime hp hpq he
  have hp3 : 3 < p := by omega
  have h5 := five_le_of_three_lt hp hp3
  have hn : ¬ p ∣ n := by
    rcases hnd with rfl | hn
    · exact not_dvd_of_orderOf hp hpq he
    · exact not_dvd_small hp h5 hn
  have hchar' : M.charpoly = cyclotomic e ℤ ^ ds.count e *
      ((ds.filter fun d => d ≠ e).map fun d => cyclotomic d ℤ).prod := by
    rw [hchar, prod_cyclotomic_split e ds]
  have hq2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  set Q : ℤ := -((ℓ ^ f : ℕ) : ℤ) with hQdef
  have hQ2 : 2 ≤ Q.natAbs := by simpa [hQdef] using hq2
  have hpQ : ¬ (p : ℤ) ∣ Q := fun h => hpq (Int.natCast_dvd_natCast.1 (by simpa [hQdef] using h))
  have he'0 : e' ≠ 0 := by
    have hQ0 : (Q : ZMod p) ≠ 0 := fun h => hpQ ((ZMod.intCast_zmod_eq_zero_iff_dvd Q p).1 h)
    have : Fact p.Prime := ⟨hp⟩
    intro h0
    have hdvd := he' ▸ ZMod.orderOf_dvd_card_sub_one hQ0
    rw [h0, zero_dvd_iff] at hdvd
    have := hp.one_lt
    omega
  have hord : p ^ (Nat.card (twistedE6RootGroup K σ)).factorization p =
      (p ^ ((ℓ ^ f) ^ e - 1).factorization p) ^ ds.count e := by
    have hD : ∀ d ∈ degreesE Tag.E6, e' ∣ d → d ≠ 0 ∧ ¬ p ∣ d / e' := fun d hd hed =>
      ⟨by have : ∀ d ∈ degreesE Tag.E6, 0 < d := by decide
          exact (this d hd).ne', not_dvd_small hp h5 (hQ d hd hed)⟩
    rw [ordProj_card_twistedE6 hℓ hf K hK σ hσ hp hp3 hpq,
      prod_ordProj_int_pow_sub_one hp (by omega) hQ2 hpQ he' (degreesE Tag.E6) hD, hcount,
      ← ordProj_cyclotomic_int_eval hp hQ2 he' he'0]
    have h1 := ordProj_cyclotomic_eval hp hq2 he he0
    have h2 : ((cyclotomic e' ℤ).eval Q).natAbs =
        ((cyclotomic e ℤ).eval ((ℓ ^ f : ℕ) : ℤ)).natAbs := by
      have := hΦ ((ℓ ^ f : ℕ) : ℤ)
      simpa [hQdef] using this
    rw [h2, h1]
  have hR := not_dvd_cyclotomic_eval_of_mem_small hp h5 he ds hso
  exact sylowTorus_twistedE6 hℓ hf K hK σ hσ hp hp3 hpq v hv _ hn0 hpow hn hchar' he hR hord

end Blocks

end CFSG.LieType.SeitzGeneration
