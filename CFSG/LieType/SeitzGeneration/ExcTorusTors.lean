module

public import CFSG.LieType.SeitzGeneration.ExcTorusFam
public import CFSG.RankThree.Chevalley.G2F4FiniteFieldFixedMatrices

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice Polynomial
open scoped Pointwise Matrix

section Abstract


theorem exists_elemAbelian_of_twisted_torus {τ : Tag} {C : Type} [Group C] {L : Type} [Field L]
    (ι : C →* ModGL τ L) (hι : Function.Injective ι) (Φ : ModGL τ L →* ModGL τ L)
    (n g0 : ModGL τ L) (hg0C : g0 ∈ adjointGroup τ L) (hg0 : Φ g0 = g0 * n) {p : ℕ}
    (hp : p.Prime) {N m : ℕ} (hN : N ≠ 0)
    (hrat : ∀ (X : Subgroup (ModGL τ L)) [Finite X], X ≤ adjointGroup τ L →
      (∀ x ∈ X, Φ x = x) → ∀ P : Subgroup (ModGL τ L), P ≤ X → IsPGroup p P → P ≤ ι.range)
    (hcomm : IsMulCommutative (twistedTorusOf n Φ))
    (hcard : Nat.card (twistedTorusOf n Φ) = N)
    (htors : Nat.card (torsionSubgroup (twistedTorusOf n Φ) hcomm p) = p ^ m) :
    ∃ E : Subgroup C, IsElemAbelian p E ∧ Nat.card E = p ^ m := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hT0fin : Finite (twistedTorusOf n Φ) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact hN)
  let cg : ModGL τ L →* ModGL τ L := (MulAut.conj g0).toMonoidHom
  have hcg : Function.Injective cg := (MulAut.conj g0).injective
  have hcg_apply : ∀ x, cg x = g0 * x * g0⁻¹ := fun x => rfl
  have hT0C := twistedTorusOf_le_adjointGroup n Φ
  set X : Subgroup (ModGL τ L) := (twistedTorusOf n Φ).map cg with hX
  have hXfin : Finite X :=
    Finite.of_surjective (cg.subgroupMap (twistedTorusOf n Φ))
      (cg.subgroupMap_surjective (twistedTorusOf n Φ))
  have hXC : X ≤ adjointGroup τ L := by
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem hg0C (hT0C hx)) (inv_mem hg0C)
  have hXF : ∀ x ∈ X, Φ x = x := by
    rintro _ ⟨x, hx, rfl⟩
    have hxfix := (mem_twistedTorusOf.1 hx).2
    rw [hcg_apply, map_mul, map_mul, map_inv, hg0]
    calc g0 * n * Φ x * (g0 * n)⁻¹ = g0 * (n * Φ x * n⁻¹) * g0⁻¹ := by group
      _ = g0 * x * g0⁻¹ := by rw [hxfix]
  have hXcomm : IsMulCommutative X := isMulCommutative_map cg hcomm
  have hpg := hrat X hXC hXF
  set V : Subgroup (ModGL τ L) := torsionSubgroup X hXcomm p with hV
  have hVX : V ≤ X := fun x hx => hx.1
  have hVp : IsPGroup p V := fun x => ⟨1, by
    have : (x : ModGL τ L) ^ p = 1 := x.2.2
    apply Subtype.ext
    simpa using this⟩
  have hVrange : V ≤ ι.range := hpg V hVX hVp
  have hVcard : Nat.card V = p ^ m := by
    have hVmap : V = (torsionSubgroup (twistedTorusOf n Φ) hcomm p).map cg := by
      ext x
      constructor
      · rintro ⟨⟨y, hy, rfl⟩, hxp⟩
        refine ⟨y, ⟨hy, hcg ?_⟩, rfl⟩
        rw [map_pow, hxp, map_one]
      · rintro ⟨y, ⟨hy, hyp⟩, rfl⟩
        refine ⟨⟨y, hy, rfl⟩, ?_⟩
        rw [← map_pow, hyp, map_one]
    rw [hVmap, Subgroup.card_map_of_injective hcg, htors]
  have hcommE : IsMulCommutative (V.comap ι) := by
    refine IsMulCommutative.of_comm fun a b => ?_
    apply Subtype.ext
    apply hι
    have := hXcomm
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact setLike_mul_comm (hVX a.2) (hVX b.2)
  have hexpE : ∀ x ∈ V.comap ι, x ^ p = 1 := fun x hx => by
    apply hι
    rw [map_pow, map_one]
    exact hx.2
  have hmap : (V.comap ι).map ι = V := by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.2 hVrange
  exact ⟨V.comap ι, ⟨hcommE, hexpE⟩, by
    rw [← Subgroup.card_map_of_injective hι, hmap, hVcard]⟩

end Abstract

section Untwisted


theorem exists_elemAbelian_untwisted {τ : Tag} (K : Type) [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hpq : ¬ p ∣ Nat.card K)
    (hrat : ∀ (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] (Fr : L →+* L),
      (∀ c, Fr c = c ^ Nat.card K) → ∀ (X : Subgroup (ModGL τ L)) [Finite X],
        X ≤ adjointGroup τ L → (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) →
        ∀ P : Subgroup (ModGL τ L), P ≤ X → IsPGroup p P →
          P ≤ (adjointGroup τ K).map (baseChangeGL (algebraMap K L)))
    {M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ}
    (hM : CFSG.RankThree.PartOne.KE.IsWeylMatrix τ M) {n e m : ℕ} (R : ℤ[X]) (hn0 : n ≠ 0)
    (hpow : M ^ n = 1) (hn : ¬ p ∣ n) (hchar : M.charpoly = cyclotomic e ℤ ^ m * R)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = e) (hR : ¬ (p : ℤ) ∣ R.eval (Nat.card K : ℤ)) :
    ∃ E : Subgroup (adjointGroup τ K), IsElemAbelian p E ∧ Nat.card E = p ^ m := by
  classical
  obtain ⟨w, hw⟩ := hM
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have : Finite (ModGL τ K) := finite_modGL
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hq : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  have : CharP K (ringChar K) := ringChar.charP K
  let L := AlgebraicClosure K
  have : CharP L (ringChar K) := charP_of_injective_algebraMap (algebraMap K L).injective _
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  let Fr : L →+* L := iterateFrobenius L (ringChar K) (f : ℕ)
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hq]
    exact iterateFrobenius_def (ringChar K) (f : ℕ) c
  have hℓq : ringChar K ∣ Nat.card K := by
    rw [hq]
    exact dvd_pow_self _ f.ne_zero
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have he0 : e ≠ 0 := he ▸ orderOf_natCast_ne_zero hp hpq
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator τ K (ℓ := ringChar K) (f := (f : ℕ)) f.pos L w
  let ι : adjointGroup τ K →* ModGL τ L :=
    (baseChangeGL (algebraMap K L)).comp (adjointGroup τ K).subtype
  have hrange : ι.range = (adjointGroup τ K).map (baseChangeGL (algebraMap K L)) := by
    change ((baseChangeGL (algebraMap K L)).comp (adjointGroup τ K).subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hι : Function.Injective ι :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  have hT0 : twistedTorus (canonicalRep (coxeterSystem τ) L w) Fr =
      (fixedCharTuples M Fr).map (rootDiagUnitHom τ L) := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorus.1 hx).1
      refine ⟨a, ?_, rfl⟩
      rw [← twistedFixedTuples_eq_fixedCharTuples hw Fr]
      exact mem_twistedFixedTuples_iff_conj.2 (mem_twistedTorus.1 hx).2
    · rintro ⟨a, ha, rfl⟩
      rw [← twistedFixedTuples_eq_fixedCharTuples hw Fr] at ha
      exact mem_twistedTorus.2 ⟨rootDiagUnit_mem_torusGroup a, mem_twistedFixedTuples_iff_conj.1 ha⟩
  have hcomm : IsMulCommutative (twistedTorusOf (canonicalRep (coxeterSystem τ) L w)
      (Units.map (entrywiseHom Fr))) := by
    show IsMulCommutative (twistedTorus (canonicalRep (coxeterSystem τ) L w) Fr)
    rw [hT0]
    exact isMulCommutative_map _ inferInstance
  set B : Matrix (Fin τ.rank) (Fin τ.rank) ℤ :=
    M - (Nat.card K : ℤ) • (1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) with hB
  have hdetB : B.det.natAbs = (M.charpoly.eval (Nat.card K : ℤ)).natAbs :=
    (natAbs_eval_charpoly M _).symm
  have hpos : 0 < (cyclotomic e ℤ).eval (Nat.card K : ℤ) :=
    cyclotomic_pos' e (by exact_mod_cast hq2)
  have hRne : R.eval (Nat.card K : ℤ) ≠ 0 := fun h => hR (by rw [h]; exact dvd_zero _)
  have hev : M.charpoly.eval (Nat.card K : ℤ) ≠ 0 := by
    rw [hchar, eval_mul, eval_pow]
    exact mul_ne_zero (pow_ne_zero m hpos.ne') hRne
  have hBne : B.det ≠ 0 := fun h => hev (Int.natAbs_eq_zero.1 (hdetB ▸ by rw [h]; rfl))
  have hcop := not_dvd_natAbs_det_sub hℓ hℓq M hn0 hpow
  have hcard : Nat.card (twistedTorusOf (canonicalRep (coxeterSystem τ) L w)
      (Units.map (entrywiseHom Fr))) = (M.charpoly.eval (Nat.card K : ℤ)).natAbs := by
    show Nat.card (twistedTorus (canonicalRep (coxeterSystem τ) L w) Fr) = _
    rw [hT0, Subgroup.card_map_of_injective rootDiagUnit_injective,
      natCard_fixedCharTuples M Fr hFr hBne hcop, hdetB]
  have hpℓ : p ≠ ringChar K := fun h => hpq (h ▸ hℓq)
  have htors : Nat.card (torsionSubgroup (twistedTorusOf (canonicalRep (coxeterSystem τ) L w)
      (Units.map (entrywiseHom Fr))) hcomm p) = p ^ m := by
    rw [natCard_torsion_eq (fixedCharTuples M Fr) _ hT0 hcomm p,
      natCard_fixedTorsion M Fr hℓ hFr hp hpℓ,
      natCard_solutions_modMat hp M R hpow hn hchar hpq he hR]
  have hrat' : ∀ (X : Subgroup (ModGL τ L)) [Finite X], X ≤ adjointGroup τ L →
      (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) → ∀ P : Subgroup (ModGL τ L), P ≤ X →
        IsPGroup p P → P ≤ ι.range := by
    intro X _ hXC hXF P hPX hPp
    rw [hrange]
    exact hrat L Fr hFr X hXC hXF P hPX hPp
  exact exists_elemAbelian_of_twisted_torus ι hι (Units.map (entrywiseHom Fr))
    (canonicalRep (coxeterSystem τ) L w) g0 hg0C hg0 hp (Int.natAbs_ne_zero.2 hev) hrat' hcomm
    hcard htors

end Untwisted

theorem five_le_of_three_lt {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) : 5 ≤ p := by
  by_contra h
  have : p = 4 := by omega
  subst this
  exact absurd hp (by norm_num)

section Family


theorem exists_elemAbelian_of_blocks {τ : Tag} (d : ℕ)
    (hτ : (τ = .E6 ∧ d = 3) ∨ (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1))
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    {M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} (hM : IsWeylMatrix τ M) (ds : List ℕ) {e : ℕ}
    (hchar : M.charpoly = (ds.map fun d => cyclotomic d ℤ).prod) (hpow : M ^ e = 1)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = e) (he0 : e ≠ 0)
    (hso : ∀ d ∈ ds, d ≠ e → d ∈ [1, 2, 3]) :
    ∃ E : Subgroup (adjointGroup τ K), IsElemAbelian p E ∧ Nat.card E = p ^ ds.count e := by
  have hpq : ¬ p ∣ Nat.card K := not_dvd_of_orderOf_pos hp he he0
  have hn : ¬ p ∣ e := not_dvd_of_orderOf hp hpq he
  have h5 := five_le_of_three_lt hp hp3
  have hchar' : M.charpoly = cyclotomic e ℤ ^ ds.count e *
      ((ds.filter fun d => d ≠ e).map fun d => cyclotomic d ℤ).prod := by
    rw [hchar, prod_cyclotomic_split e ds]
  have hR : ¬ (p : ℤ) ∣ (((ds.filter fun d => d ≠ e).map fun d => cyclotomic d ℤ).prod).eval
      (Nat.card K : ℤ) := by
    have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
    rw [eval_list_prod, hpz.dvd_prod_iff]
    rintro ⟨a, ha, hpa⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ha
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    rw [List.mem_filter] at hd
    have hde : d ≠ e := by simpa using hd.2
    have hd3 := hso d hd.1 hde
    refine not_dvd_cyclotomic_eval_of_ne hp he hde (fun hdvd => ?_) hpa
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd3
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  refine exists_elemAbelian_untwisted K hp hpq ?_ hM _ he0 hpow hn hchar' he hR
  intro L _ _ _ Fr hFr X _ hXC hXF P hPX hPp
  exact (finite_fixed_subgroup_rational d hτ Fr hFr X hXC hXF).2 p hp hp3 P hPX hPp

theorem exists_elemAbelian_of_blocks_F4 (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) {M : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ}
    (hM : IsWeylMatrix Tag.F4 M) (ds : List ℕ) {e : ℕ}
    (hchar : M.charpoly = (ds.map fun d => cyclotomic d ℤ).prod) (hpow : M ^ e = 1)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = e) (he0 : e ≠ 0)
    (hso : ∀ d ∈ ds, d ≠ e → d ∈ [1, 2, 3]) :
    ∃ E : Subgroup (adjointGroup Tag.F4 K), IsElemAbelian p E ∧ Nat.card E = p ^ ds.count e := by
  have hpq : ¬ p ∣ Nat.card K := not_dvd_of_orderOf_pos hp he he0
  have hn : ¬ p ∣ e := not_dvd_of_orderOf hp hpq he
  have h5 := five_le_of_three_lt hp hp3
  have hchar' : M.charpoly = cyclotomic e ℤ ^ ds.count e *
      ((ds.filter fun d => d ≠ e).map fun d => cyclotomic d ℤ).prod := by
    rw [hchar, prod_cyclotomic_split e ds]
  have hR : ¬ (p : ℤ) ∣ (((ds.filter fun d => d ≠ e).map fun d => cyclotomic d ℤ).prod).eval
      (Nat.card K : ℤ) := by
    have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
    rw [eval_list_prod, hpz.dvd_prod_iff]
    rintro ⟨a, ha, hpa⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ha
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    rw [List.mem_filter] at hd
    have hde : d ≠ e := by simpa using hd.2
    have hd3 := hso d hd.1 hde
    refine not_dvd_cyclotomic_eval_of_ne hp he hde (fun hdvd => ?_) hpa
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd3
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  refine exists_elemAbelian_untwisted K hp hpq ?_ hM _ he0 hpow hn hchar' he hR
  intro L _ _ _ Fr hFr X _ hXC hXF P hPX _ x hx
  have hXle : X ≤ (adjointGroup Tag.F4 K).map (baseChangeGL (algebraMap K L)) := by
    intro y hy
    rw [← (CFSG.RankThree.Chevalley.G2_F4_exact_finite_field_fixed_root_matrices Tag.F4
      (Or.inr rfl) K L Fr hFr).1]
    exact ⟨hXC hy, hXF y hy⟩
  exact hXle (hPX hx)

end Family

end CFSG.LieType.SeitzGeneration
