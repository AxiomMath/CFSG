module

public import CFSG.LieType.SeitzGeneration.ExcTorusThree
public import CFSG.RankThree.PartOne.KE.CTTwisted

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2 CFSG.Timmesfeld.ExceptionalOrders Polynomial
open scoped Matrix Pointwise
open CFSG.RankThree.Lattice

section Assembly


theorem twisted_E6_relIndex_dvd_three {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (Fr : Ω →+* Ω)
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {X : Subgroup (ModGL TwistTag.E6.tag Ω)}
    (hX : X ≤ twistedFixedGroup TwistTag.E6 Ω Fr) :
    ((graphFixedRootGroup TwistTag.E6 K σ).map (baseChangeGL (algebraMap K Ω))).relIndex X ∣ 3 := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have : CharP Ω ℓ := charP_of_injective_algebraMap (algebraMap K Ω).injective ℓ
  have : Finite (Module.End K (RootModule TwistTag.E6.tag K)) := Module.finite_of_finite K
  have : Finite (ModGL TwistTag.E6.tag K) := inferInstance
  have : Fintype (WeylGroup TwistTag.E6.tag) := Fintype.ofFinite _
  have hσsurj : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  obtain ⟨hmul, hle, hnormal, -⟩ :=
    exceptional_ambient_twisted_Frobenius_fixed_normalizer TwistTag.E6 hℓ hf K hK σ hσ Ω Fr hFr
  have hTC := inf_graphFixedTorus_map_eq (algebraMap K Ω) σ Fr hle
  have hTcard := natCard_graphFixedTorus_E6 (by omega : f ≠ 0) hFr
  have hcompat := natCard_compatTorus_E6_mul hℓ hf hK hσ
  set R := twistedFixedGroup TwistTag.E6 Ω Fr
  set T := graphFixedTorus TwistTag.E6 Ω Fr
  set C := (graphFixedRootGroup TwistTag.E6 K σ).map (baseChangeGL (algebraMap K Ω))
  have hTCcard : Nat.card ↥(T ⊓ C) = Nat.card (compatTorus (t := TwistTag.E6) σ) := by
    rw [hTC, Subgroup.card_map_of_injective (baseChangeGL_injective _),
      graphFixedRootTorus_eq_compatTorus hσsurj]
  have hTR : T ≤ R := graphFixedTorus_le TwistTag.E6 Ω Fr
  have hsup : T.subgroupOf R ⊔ C.subgroupOf R = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    have hx' : x ∈ (T : Set (ModGL TwistTag.E6.tag Ω)) *
        (C : Set (ModGL TwistTag.E6.tag Ω)) := by
      rw [← hmul]
      exact hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx'
    have e : (⟨a * b, hx⟩ : R) = ⟨a, hTR ha⟩ * ⟨b, hle hb⟩ := rfl
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.2 ha))
      (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.2 hb))
  have hindex : (C.subgroupOf R).index * Nat.card ↥(T ⊓ C) = Nat.card T := by
    have := hnormal
    have h1 := Subgroup.relIndex_sup_right (H := T.subgroupOf R) (K := C.subgroupOf R)
    rw [hsup, Subgroup.relIndex_top_right] at h1
    have h2 := Subgroup.relIndex_mul_card (H := C.subgroupOf R) (K := T.subgroupOf R)
    rw [← h1] at h2
    have e : C.subgroupOf R ⊓ T.subgroupOf R = (T ⊓ C).subgroupOf R := by
      ext x
      rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
        Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact and_comm
    rw [e, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hTR)).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTR).toEquiv] at h2
    exact h2
  have hidx : (C.subgroupOf R).index = Nat.gcd 3 (ℓ ^ f + 1) := by
    have hpos : 0 < Nat.card (compatTorus (t := TwistTag.E6) σ) := Nat.card_pos
    rw [hTCcard, hTcard, ← hcompat] at hindex
    exact Nat.eq_of_mul_eq_mul_right hpos (hindex.trans (mul_comm _ _))
  have := hnormal
  exact relIndex_dvd_of_le_of_index_dvd hX (hidx ▸ Nat.gcd_dvd_left 3 (ℓ ^ f + 1))

theorem exists_elemAbelian_ge_twistedE6 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ}
    (hp : p.Prime) (hpq : ¬ p ∣ ℓ ^ f)
    {M : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ}
    (v : WeylGroup TwistTag.E6.tag)
    (hv : ∀ x, v • x = M *ᵥ permLattice TwistTag.E6.perm x) {n e m : ℕ} (R : ℤ[X])
    (hn0 : n ≠ 0) (hpow : M ^ n = 1) (hn : ¬ p ∣ n)
    (hchar : M.charpoly = cyclotomic e ℤ ^ m * R)
    (he : orderOf (((ℓ ^ f : ℕ)) : ZMod p) = e)
    (hR : ¬ (p : ℤ) ∣ R.eval ((ℓ ^ f : ℕ) : ℤ)) :
    ∃ E : Subgroup (twistedE6RootGroup K σ), IsElemAbelian p E ∧ p ^ m ≤ 3 * Nat.card E := by
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
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator_twisted K (ℓ := ℓ) (f := f) hf L v
  let ι : twistedE6RootGroup K σ →* ModGL TwistTag.E6.tag L :=
    (baseChangeGL (algebraMap K L)).comp (twistedE6RootGroup K σ).subtype
  have hrange : ι.range = (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map
      (baseChangeGL (algebraMap K L)) := by
    change ((baseChangeGL (algebraMap K L)).comp (twistedE6RootGroup K σ).subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hι : Function.Injective ι :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  have hrat : ∀ (X : Subgroup (ModGL TwistTag.E6.tag L)) [Finite X],
      X ≤ adjointGroup TwistTag.E6.tag L → (∀ x ∈ X, twistHom TwistTag.E6 L Fr x = x) →
      ι.range.relIndex X ∣ 3 := by
    intro X _ hXC hXF
    rw [hrange]
    exact twisted_E6_relIndex_dvd_three hℓ hf K hK σ.toRingHom hσ L Fr hFr fun x hx =>
      (mem_twistedFixedGroup_iff_twistHom _ _ _).2 ⟨hXC hx, hXF x hx⟩
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
  exact exists_elemAbelian_ge_of_twisted_torus ι hι (twistHom TwistTag.E6 L Fr)
    (canonicalRep (coxeterSystem TwistTag.E6.tag) L v) g0 hg0C hg0 hp (Int.natAbs_ne_zero.2 hev)
    (by norm_num) hrat hcomm hcard htors

theorem exists_elemAbelian_ge_twistedE6_three_of_blocks {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {M : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ}
    (v : WeylGroup TwistTag.E6.tag) (hv : ∀ x, v • x = M *ᵥ permLattice TwistTag.E6.perm x)
    (ds : List ℕ) {n e : ℕ} (hchar : M.charpoly = (ds.map fun d => cyclotomic d ℤ).prod)
    (hn0 : n ≠ 0) (hpow : M ^ n = 1) (hn : ¬ 3 ∣ n)
    (he : orderOf (((ℓ ^ f : ℕ)) : ZMod 3) = e) (he0 : e ≠ 0)
    (hso : ∀ d ∈ ds, d ≠ e → d ∈ [1, 2]) :
    ∃ E : Subgroup (twistedE6RootGroup K σ), IsElemAbelian 3 E ∧
      3 ^ ds.count e ≤ 3 * Nat.card E := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hpq : ¬ 3 ∣ ℓ ^ f := not_dvd_of_orderOf_pos hp he he0
  have hchar' : M.charpoly = cyclotomic e ℤ ^ ds.count e *
      ((ds.filter fun d => d ≠ e).map fun d => cyclotomic d ℤ).prod := by
    rw [hchar, prod_cyclotomic_split e ds]
  have hR : ¬ ((3 : ℕ) : ℤ) ∣ (((ds.filter fun d => d ≠ e).map fun d => cyclotomic d ℤ).prod).eval
      ((ℓ ^ f : ℕ) : ℤ) := by
    have hpz : Prime ((3 : ℕ) : ℤ) := Nat.prime_iff_prime_int.1 hp
    rw [eval_list_prod, hpz.dvd_prod_iff]
    rintro ⟨a, ha, hpa⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ha
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    rw [List.mem_filter] at hd
    have hde : d ≠ e := by simpa using hd.2
    have hd2 := hso d hd.1 hde
    refine not_dvd_cyclotomic_eval_of_ne hp he hde (fun hdvd => ?_) hpa
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd2
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  exact exists_elemAbelian_ge_twistedE6 hℓ hf K hK σ hσ hp hpq v hv _ hn0 hpow hn hchar' he hR

end Assembly

end CFSG.LieType.SeitzGeneration
