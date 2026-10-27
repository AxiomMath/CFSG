module

public import CFSG.Foundations.Basic
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.Adjoin.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization

public section

namespace CFSG.LinearAlgebra

open Polynomial Module
open scoped commutatorElement

section Irreducible

variable {F : Type*} [Field F]

theorem isCoprime_of_natDegree_lt {P h : F[X]} (hP : Irreducible P) (h0 : h ≠ 0)
    (hdeg : h.natDegree < P.natDegree) : IsCoprime P h :=
  hP.coprime_iff_not_dvd.2 fun hd => (natDegree_le_of_dvd hd h0).not_gt hdeg

variable {M : Type*} [AddCommGroup M] [Module F M]

theorem eq_zero_of_aeval_apply_eq_zero {P : F[X]} (hP : Irreducible P) (T : Module.End F M)
    {v : M} (hPv : aeval T P v = 0) (hv : v ≠ 0) {h : F[X]} (hdeg : h.natDegree < P.natDegree)
    (hh : aeval T h v = 0) : h = 0 := by
  by_contra h0
  obtain ⟨a, b, hab⟩ := isCoprime_of_natDegree_lt hP h0 hdeg
  apply hv
  have e := congrArg (fun q : F[X] => aeval T q v) hab
  simp only [map_add, map_mul, map_one, LinearMap.add_apply, Module.End.mul_apply, hPv, hh,
    map_zero, add_zero, Module.End.one_apply] at e
  exact e.symm

theorem natDegree_le_finrank_of_aeval_eq_zero [FiniteDimensional F M] (N : Submodule F M)
    (T : Module.End F M) (hT : ∀ m ∈ N, T m ∈ N) {P : F[X]} (hP : Irreducible P)
    (hPN : ∀ m ∈ N, aeval T P m = 0) {v : M} (hv : v ∈ N) (hv0 : v ≠ 0) :
    P.natDegree ≤ finrank F N := by
  have hpow : ∀ i : ℕ, (T ^ i) v ∈ N := by
    intro i
    induction i with
    | zero => exact hv
    | succ i ih => rw [pow_succ', Module.End.mul_apply]; exact hT _ ih
  let f : Fin P.natDegree → N := fun i => ⟨(T ^ (i : ℕ)) v, hpow i⟩
  have hli : LinearIndependent F f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hc' : ∑ i, c i • (T ^ (i : ℕ)) v = 0 := by
      have := congrArg Subtype.val hc
      simpa [f] using this
    set h : F[X] := ∑ i : Fin P.natDegree, C (c i) * X ^ (i : ℕ) with hhdef
    have hdeg : h.natDegree < P.natDegree := by
      have hP0 : 0 < P.natDegree := Irreducible.natDegree_pos hP
      refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := P.natDegree - 1)
        fun i _ => (natDegree_C_mul_X_pow_le _ _).trans (by omega)) (by omega)
    have hh : aeval T h v = 0 := by
      simp only [hhdef, map_sum, map_mul, aeval_C, aeval_X_pow, LinearMap.sum_apply,
        Module.End.mul_apply, Module.algebraMap_end_apply]
      exact hc'
    have h0 := eq_zero_of_aeval_apply_eq_zero hP T (hPN v hv) hv0 hdeg hh
    intro i
    have := congrArg (fun q : F[X] => q.coeff i) h0
    simpa [hhdef, finsetSum_coeff, coeff_C_mul_X_pow, Fin.val_inj] using this
  simpa using hli.fintype_card_le_finrank

theorem coe_aeval_restrict_apply {A : Module.End F M} {N : Submodule F M}
    (hA : ∀ x ∈ N, A x ∈ N) (q : F[X]) (x : N) :
    ((aeval (A.restrict hA) q x : N) : M) = aeval A q x := by
  induction q using Polynomial.induction_on' with
  | add q r hq hr => simp only [map_add, LinearMap.add_apply, Submodule.coe_add, hq, hr]
  | monomial n a =>
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      Submodule.coe_smul]
    rw [Module.End.pow_restrict n hA, LinearMap.coe_restrict_apply]

theorem commute_aeval_of_commute {A B : Module.End F M} (h : Commute A B) (q : F[X]) :
    Commute A (aeval B q) := by
  induction q using Polynomial.induction_on' with
  | add q r hq hr => rw [map_add]; exact hq.add_right hr
  | monomial n a =>
    rw [aeval_monomial]
    exact (Algebra.commute_algebraMap_right a A).mul_right (h.pow_right n)

variable [Nontrivial M]

theorem isField_adjoin_singleton_of_aeval_eq_zero {P : F[X]} (hP : Irreducible P)
    (t : Module.End F M) (htP : aeval t P = 0) : IsField (Algebra.adjoin F {t}) := by
  refine ⟨⟨0, 1, fun h => zero_ne_one (congrArg Subtype.val h)⟩,
    fun a b => (Algebra.isMulCommutative_adjoin F (Set.pairwise_singleton _ _)).is_comm.comm a b,
    fun {a} ha => ?_⟩
  have hmem : (a : Module.End F M) ∈ (aeval (R := F) t).range := by
    rw [← Algebra.adjoin_singleton_eq_range_aeval]
    exact a.2
  obtain ⟨h, hh⟩ := (AlgHom.mem_range _).1 hmem
  have hnd : ¬ P ∣ h := by
    rintro ⟨q, rfl⟩
    apply ha
    apply Subtype.ext
    change _ = (0 : Module.End F M)
    rw [← hh, map_mul, htP, zero_mul]
  obtain ⟨u, w, huw⟩ := hP.coprime_iff_not_dvd.2 hnd
  refine ⟨⟨aeval t w, ?_⟩, Subtype.ext ?_⟩
  · rw [Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨w, rfl⟩
  · change (a : Module.End F M) * aeval t w = 1
    have e := congrArg (aeval t) huw
    rw [map_add, map_mul, map_mul, htP, mul_zero, zero_add, map_one] at e
    rw [← hh, ← map_mul, mul_comm, map_mul, e]

theorem finrank_adjoin_singleton_of_aeval_eq_zero {P : F[X]} (hP : Irreducible P) (hPm : P.Monic)
    (t : Module.End F M) (htP : aeval t P = 0) :
    finrank F (Algebra.adjoin F {t}) = P.natDegree := by
  set d := P.natDegree
  let L : degreeLT F d →ₗ[F] Module.End F M :=
    (aeval t).toLinearMap.comp (degreeLT F d).subtype
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    rintro ⟨h, hh⟩ hL
    rw [LinearMap.mem_ker] at hL
    rw [Submodule.mem_bot]
    apply Subtype.ext
    change h = 0
    obtain ⟨v, hv⟩ := exists_ne (0 : M)
    have hPv : aeval t P v = 0 := by rw [htP]; rfl
    refine eq_zero_of_aeval_apply_eq_zero hP t hPv hv ?_ ?_
    · by_cases h0 : h = 0
      · rw [h0, natDegree_zero]
        exact Irreducible.natDegree_pos hP
      · rw [mem_degreeLT] at hh
        rwa [degree_eq_natDegree h0, Nat.cast_lt] at hh
    · rw [show aeval t h = L ⟨h, hh⟩ from rfl, hL]
      rfl
  have hrange : LinearMap.range L = Subalgebra.toSubmodule (Algebra.adjoin F {t}) := by
    ext c
    rw [LinearMap.mem_range, Subalgebra.mem_toSubmodule, Algebra.adjoin_singleton_eq_range_aeval]
    constructor
    · rintro ⟨⟨h, -⟩, rfl⟩
      exact ⟨h, rfl⟩
    · rintro ⟨h, rfl⟩
      refine ⟨⟨h %ₘ P, ?_⟩, ?_⟩
      · rw [mem_degreeLT]
        calc degree (h %ₘ P) < degree P := degree_modByMonic_lt h hPm
          _ = d := degree_eq_natDegree hP.ne_zero
      · exact aeval_modByMonic_eq_self_of_root htP
  have h1 := LinearMap.finrank_range_of_inj hinj
  rw [hrange, Subalgebra.finrank_toSubmodule] at h1
  rw [h1, (degreeLTEquiv F d).finrank_eq, finrank_fin_fun]

end Irreducible

section Cyclotomic

variable {p : ℕ} [hp : Fact p.Prime]

theorem irreducible_cyclotomic_two (hp2 : p ≠ 2) (hord : orderOf (2 : ZMod p) = p - 1) :
    Irreducible (cyclotomic p (ZMod 2)) := by
  have h2p : ¬ 2 ∣ p := fun h =>
    hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp.out).1 h).symm
  refine ZMod.irreducible_of_dvd_cyclotomic_of_natDegree (p := 2) (n := p) h2p dvd_rfl ?_
  rw [natDegree_cyclotomic, Nat.totient_prime hp.out, ← hord, ← orderOf_units]
  rfl

theorem natDegree_cyclotomic_two : (cyclotomic p (ZMod 2)).natDegree = p - 1 := by
  rw [natDegree_cyclotomic, Nat.totient_prime hp.out]

theorem isCoprime_X_sub_one_cyclotomic_two (hp2 : p ≠ 2) :
    IsCoprime (X - C 1 : (ZMod 2)[X]) (cyclotomic p (ZMod 2)) := by
  rw [(irreducible_X_sub_C (1 : ZMod 2)).coprime_iff_not_dvd, dvd_iff_isRoot, IsRoot.def,
    eval_one_cyclotomic_prime, ZMod.natCast_eq_one_iff_odd.2 (hp.out.odd_of_ne_two hp2)]
  exact one_ne_zero

theorem odd_nsmul_eq_self_two {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (hp2 : p ≠ 2)
    (v : V) : p • v = v := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod 2), ZMod.natCast_eq_one_iff_odd.2 (hp.out.odd_of_ne_two hp2),
    one_smul]

end Cyclotomic

section Setting

variable {Q : Type*} [Group Q] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) Q V) (z : Q)

@[expose] def centralFixed : Submodule (ZMod 2) V := LinearMap.ker (ρ z - 1)

@[expose] def centralImage : Submodule (ZMod 2) V := LinearMap.range (ρ z - 1)

variable {ρ z} in
theorem mapsTo_centralImage {A : Module.End (ZMod 2) V} (hA : Commute A (ρ z)) :
    ∀ w ∈ centralImage ρ z, A w ∈ centralImage ρ z := by
  rintro _ ⟨v, rfl⟩
  refine ⟨A v, ?_⟩
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, mul_sub, sub_mul, mul_one, one_mul,
    hA.eq]

variable {ρ z} in
theorem mapsTo_centralFixed {A : Module.End (ZMod 2) V} (hA : Commute A (ρ z)) :
    ∀ u ∈ centralFixed ρ z, A u ∈ centralFixed ρ z := by
  intro u hu
  simp only [centralFixed, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
    sub_eq_zero] at hu ⊢
  rw [← Module.End.mul_apply, ← hA.eq, Module.End.mul_apply, hu]

@[expose] noncomputable def centralImageOp : Module.End (ZMod 2) (centralImage ρ z) :=
  (ρ z).restrict (mapsTo_centralImage (Commute.refl _))

@[expose] noncomputable def centralImageAlgebra :
    Subalgebra (ZMod 2) (Module.End (ZMod 2) (centralImage ρ z)) :=
  Algebra.adjoin (ZMod 2) {centralImageOp ρ z}

end Setting

section Decomposition

variable {p : ℕ} [hp : Fact p.Prime] {Q : Type*} [Group Q] {V : Type*} [AddCommGroup V]
  [Module (ZMod 2) V] {ρ : Representation (ZMod 2) Q V} {z : Q}

theorem aeval_X_sub_one (A : Module.End (ZMod 2) V) :
    aeval A (X - C 1 : (ZMod 2)[X]) = A - 1 := by
  simp

theorem aeval_cyclotomic_mul_sub_one (A : Module.End (ZMod 2) V) :
    aeval A (cyclotomic p (ZMod 2)) * (A - 1) = A ^ p - 1 := by
  rw [← aeval_X_sub_one, ← map_mul, C_1, cyclotomic_prime_mul_X_sub_one, map_sub, map_pow,
    aeval_X, map_one]

theorem centralImage_eq_ker_cyclotomic (hp2 : p ≠ 2) (hTp : ρ z ^ p = 1) :
    centralImage ρ z = LinearMap.ker (aeval (ρ z) (cyclotomic p (ZMod 2))) := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    rw [LinearMap.mem_ker, ← Module.End.mul_apply, aeval_cyclotomic_mul_sub_one, hTp, sub_self,
      LinearMap.zero_apply]
  · intro v hv
    rw [LinearMap.mem_ker] at hv
    obtain ⟨a, b, hab⟩ := isCoprime_X_sub_one_cyclotomic_two (p := p) hp2
    have e := congrArg (fun q : (ZMod 2)[X] => aeval (ρ z) q v) hab
    simp only [map_add, map_mul, LinearMap.add_apply, Module.End.mul_apply, hv, map_zero,
      add_zero, map_one, Module.End.one_apply] at e
    refine ⟨aeval (ρ z) a v, ?_⟩
    have hc : Commute (ρ z - 1) (aeval (ρ z) a) :=
      commute_aeval_of_commute ((Commute.refl (ρ z)).sub_left (Commute.one_left (ρ z))) a
    rw [← Module.End.mul_apply, hc.eq, Module.End.mul_apply]
    simpa only [map_sub, aeval_X, map_one] using e

theorem isCompl_centralFixed_centralImage (hp2 : p ≠ 2) (hTp : ρ z ^ p = 1) :
    IsCompl (centralFixed ρ z) (centralImage ρ z) := by
  rw [centralImage_eq_ker_cyclotomic hp2 hTp]
  have hU : centralFixed ρ z = LinearMap.ker (aeval (ρ z) (X - C 1 : (ZMod 2)[X])) := by
    rw [aeval_X_sub_one]
    rfl
  rw [hU]
  have hcop := isCoprime_X_sub_one_cyclotomic_two (p := p) hp2
  refine ⟨disjoint_ker_aeval_of_isCoprime _ hcop, codisjoint_iff.2 ?_⟩
  rw [sup_ker_aeval_eq_ker_aeval_mul_of_coprime _ hcop, mul_comm, map_mul, aeval_X_sub_one,
    aeval_cyclotomic_mul_sub_one, hTp, sub_self, LinearMap.ker_zero]

theorem exists_pow_pow_eq_self {G : Type*} [Monoid G] {g : G} (hg : g ^ p = 1) {m : ℕ}
    (hm : ¬ p ∣ m) : ∃ n : ℕ, (g ^ m) ^ n = g := by
  have hcop : Nat.Coprime m p :=
    Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hm)
  obtain ⟨n, -, hn⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.out.one_lt
  refine ⟨n, ?_⟩
  rw [← pow_mul, ← Nat.div_add_mod (m * n) p, hn, pow_add, pow_mul, hg, one_pow, one_mul,
    pow_one]

theorem sum_pow_apply_eq_zero (hp2 : p ≠ 2) (hTp : ρ z ^ p = 1) {u : Q} (hu : Commute u z)
    (hup : u ^ p = 1) (hzu : ∃ n : ℕ, u ^ n = z) {w : V} (hw : w ∈ centralImage ρ z) :
    ∑ i ∈ Finset.range p, (ρ u ^ i) w = 0 := by
  set t := ∑ i ∈ Finset.range p, (ρ u ^ i) w with htdef
  have hcomm : Commute (ρ u) (ρ z) := hu.map ρ
  have htW : t ∈ centralImage ρ z := Submodule.sum_mem _ fun i _ =>
    mapsTo_centralImage (hcomm.pow_left i) w hw
  have hfix : ρ u t = t := by
    have h := congrArg (fun A : Module.End (ZMod 2) V => A w) (mul_geom_sum (ρ u) p)
    simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
      LinearMap.sum_apply, ← map_pow, hup, map_one, sub_self, LinearMap.zero_apply] at h
    rw [sub_eq_zero] at h
    simpa only [htdef, map_pow] using h
  have key : ∀ m : ℕ, (ρ u ^ m) t = t := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [pow_succ, Module.End.mul_apply, hfix, ih]
  have hzt : ρ z t = t := by
    obtain ⟨n, hn⟩ := hzu
    rw [← hn, map_pow]
    exact key n
  have hmem : t ∈ centralFixed ρ z ⊓ centralImage ρ z := by
    refine Submodule.mem_inf.2 ⟨?_, htW⟩
    simp only [centralFixed, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, hzt,
      sub_self]
  rw [(isCompl_centralFixed_centralImage hp2 hTp).inf_eq_bot, Submodule.mem_bot] at hmem
  exact hmem

theorem apply_eq_self_of_mem_centralFixed [FiniteDimensional (ZMod 2) V]
    (hΦ : Irreducible (cyclotomic p (ZMod 2))) (hr : finrank (ZMod 2) (centralFixed ρ z) < p - 1)
    {g : Q} (hg : Commute g z) (hgp : g ^ p = 1) {u : V} (hu : u ∈ centralFixed ρ z) :
    ρ g u = u := by
  set A := ρ g with hAdef
  have hAU : ∀ v ∈ centralFixed ρ z, A v ∈ centralFixed ρ z := mapsTo_centralFixed (hg.map ρ)
  set N := centralFixed ρ z ⊓ LinearMap.ker (aeval A (cyclotomic p (ZMod 2))) with hNdef
  have hN : N = ⊥ := by
    by_contra hne
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hNinv : ∀ m ∈ N, A m ∈ N := by
      intro m hm
      obtain ⟨hmU, hmK⟩ := Submodule.mem_inf.1 hm
      refine Submodule.mem_inf.2 ⟨hAU m hmU, ?_⟩
      rw [LinearMap.mem_ker] at hmK ⊢
      rw [← Module.End.mul_apply, ← (commute_aeval_of_commute (Commute.refl A) _).eq,
        Module.End.mul_apply, hmK, map_zero]
    have h := natDegree_le_finrank_of_aeval_eq_zero N A hNinv hΦ
      (fun m hm => (Submodule.mem_inf.1 hm).2) hv hv0
    rw [natDegree_cyclotomic_two] at h
    have hle : finrank (ZMod 2) N ≤ finrank (ZMod 2) (centralFixed ρ z) :=
      Submodule.finrank_mono inf_le_left
    omega
  have hw : (A - 1) u ∈ N := by
    refine Submodule.mem_inf.2 ⟨Submodule.sub_mem _ (hAU u hu) hu, ?_⟩
    rw [LinearMap.mem_ker, ← Module.End.mul_apply, aeval_cyclotomic_mul_sub_one, hAdef,
      ← map_pow, hgp, map_one, sub_self, LinearMap.zero_apply]
  rw [hN, Submodule.mem_bot, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hw
  exact hw

end Decomposition

section FieldK

variable {p : ℕ} [hp : Fact p.Prime] {Q : Type*} [Group Q] {V : Type*} [AddCommGroup V]
  [Module (ZMod 2) V] {ρ : Representation (ZMod 2) Q V} {z : Q}

theorem coe_centralImageOp_apply (w : centralImage ρ z) :
    ((centralImageOp ρ z w : centralImage ρ z) : V) = ρ z w := rfl

theorem aeval_centralImageOp_cyclotomic (hp2 : p ≠ 2) (hTp : ρ z ^ p = 1) :
    aeval (centralImageOp ρ z) (cyclotomic p (ZMod 2)) = 0 := by
  refine LinearMap.ext fun w => Subtype.ext ?_
  have h := coe_aeval_restrict_apply (mapsTo_centralImage (Commute.refl (ρ z)))
    (cyclotomic p (ZMod 2)) w
  have hw : (w : V) ∈ LinearMap.ker (aeval (ρ z) (cyclotomic p (ZMod 2))) := by
    rw [← centralImage_eq_ker_cyclotomic hp2 hTp]
    exact w.2
  exact h.trans (LinearMap.mem_ker.1 hw)

theorem commute_of_mem_centralImageAlgebra {A c : Module.End (ZMod 2) (centralImage ρ z)}
    (hA : Commute A (centralImageOp ρ z)) (hc : c ∈ centralImageAlgebra ρ z) : Commute A c := by
  have hle : centralImageAlgebra ρ z ≤ Subalgebra.centralizer (ZMod 2) {A} := by
    rw [centralImageAlgebra, Algebra.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe,
      Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    exact hA.eq
  exact ((Subalgebra.mem_centralizer_iff _).1 (hle hc) A rfl)

theorem apply_mem_of_mem_centralImageAlgebra {S : Submodule (ZMod 2) V}
    (hS : ∀ s ∈ S, ρ z s ∈ S) {c : Module.End (ZMod 2) (centralImage ρ z)}
    (hc : c ∈ centralImageAlgebra ρ z) {w : centralImage ρ z} (hw : (w : V) ∈ S) :
    ((c w : centralImage ρ z) : V) ∈ S := by
  induction hc using Algebra.adjoin_induction generalizing w with
  | mem a ha =>
    rw [Set.mem_singleton_iff] at ha
    rw [ha, coe_centralImageOp_apply]
    exact hS _ hw
  | algebraMap r =>
    rw [Module.algebraMap_end_apply, Submodule.coe_smul]
    exact S.smul_mem r hw
  | add a b _ _ ha hb =>
    rw [LinearMap.add_apply, Submodule.coe_add]
    exact S.add_mem (ha hw) (hb hw)
  | mul a b _ _ ha hb =>
    rw [Module.End.mul_apply]
    exact ha (hb hw)

end FieldK

section Eigen

variable {p : ℕ} [hp : Fact p.Prime] {Q : Type*} [Group Q] {V : Type*} [AddCommGroup V]
  [Module (ZMod 2) V] (ρ : Representation (ZMod 2) Q V) (z x : Q)

@[expose] def cosetFixed (j : ℕ) : Submodule (ZMod 2) V :=
  centralImage ρ z ⊓ LinearMap.ker (ρ (x * z ^ j) - 1)

variable (p) in
@[expose] def cosetAverage (j : ℕ) : Module.End (ZMod 2) V :=
  ∑ i ∈ Finset.range p, ρ (x * z ^ j) ^ i

variable {ρ z x}

theorem mem_cosetFixed {j : ℕ} {w : V} :
    w ∈ cosetFixed ρ z x j ↔ w ∈ centralImage ρ z ∧ ρ (x * z ^ j) w = w := by
  rw [cosetFixed, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
    sub_eq_zero]

omit hp in
theorem cosetAverage_mem_cosetFixed (hzc : ∀ g : Q, Commute g z) (hexp : ∀ g : Q, g ^ p = 1)
    (j : ℕ) {w : V} (hw : w ∈ centralImage ρ z) :
    cosetAverage p ρ z x j w ∈ cosetFixed ρ z x j := by
  rw [mem_cosetFixed]
  constructor
  · rw [cosetAverage, LinearMap.sum_apply]
    exact Submodule.sum_mem _ fun i _ =>
      mapsTo_centralImage (((hzc (x * z ^ j)).map ρ).pow_left i) w hw
  · have h := congrArg (fun A : Module.End (ZMod 2) V => A w)
      (mul_geom_sum (ρ (x * z ^ j)) p)
    simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply, ← map_pow,
      hexp, map_one, sub_self, LinearMap.zero_apply, sub_eq_zero] at h
    simpa only [cosetAverage, map_pow] using h

omit hp in
theorem cosetAverage_mem {S : Submodule (ZMod 2) V} (hS : ∀ g : Q, ∀ s ∈ S, ρ g s ∈ S) (j : ℕ)
    {s : V} (hs : s ∈ S) : cosetAverage p ρ z x j s ∈ S := by
  rw [cosetAverage, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [← map_pow]
  exact hS _ s hs

theorem sum_cosetAverage_apply (hp2 : p ≠ 2) (hzc : ∀ g : Q, Commute g z)
    (hexp : ∀ g : Q, g ^ p = 1) {w : V} (hw : w ∈ centralImage ρ z) :
    ∑ j ∈ Finset.range p, cosetAverage p ρ z x j w = w := by
  have hTp : ρ z ^ p = 1 := by rw [← map_pow, hexp, map_one]
  have hterm : ∀ j i : ℕ, (ρ (x * z ^ j) ^ i) w = ρ (x ^ i) ((ρ (z ^ i) ^ j) w) := by
    intro j i
    rw [← map_pow, ← map_pow, ← Module.End.mul_apply, ← map_mul, ((hzc x).pow_right j).mul_pow,
      ← pow_mul, ← pow_mul, mul_comm j i]
  simp only [cosetAverage, LinearMap.sum_apply, hterm]
  rw [Finset.sum_comm, Finset.sum_eq_single_of_mem 0 (Finset.mem_range.2 hp.out.pos)]
  · simp only [pow_zero, map_one, one_pow, Module.End.one_apply, Finset.sum_const,
      Finset.card_range]
    exact odd_nsmul_eq_self_two hp2 w
  · intro i hi hi0
    rw [← map_sum]
    have hsum := sum_pow_apply_eq_zero hp2 hTp (u := z ^ i) ((Commute.refl z).pow_left i)
      (by rw [← pow_mul, mul_comm, pow_mul, hexp, one_pow])
      (exists_pow_pow_eq_self (hexp z) fun hd =>
        (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hi0) (Finset.mem_range.1 hi)) hd) hw
    rw [hsum, map_zero]

theorem cosetAverage_apply_of_mem (hp2 : p ≠ 2) (hzc : ∀ g : Q, Commute g z)
    (hexp : ∀ g : Q, g ^ p = 1) {j k : ℕ} (hj : j < p) (hk : k < p) {w : V}
    (hw : w ∈ cosetFixed ρ z x k) :
    cosetAverage p ρ z x j w = if j = k then w else 0 := by
  have hTp : ρ z ^ p = 1 := by rw [← map_pow, hexp, map_one]
  rw [mem_cosetFixed] at hw
  have hg : x * z ^ j = z ^ (j + p - k) * (x * z ^ k) := by
    rw [← mul_assoc, ((hzc x).pow_right (j + p - k)).symm.eq, mul_assoc, ← pow_add,
      show j + p - k + k = j + p by omega, pow_add, hexp, mul_one]
  have hfix : ∀ i : ℕ, ρ ((x * z ^ k) ^ i) w = w := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ, map_mul, Module.End.mul_apply, hw.2, ih]
  have hpow : ∀ i : ℕ, (ρ (x * z ^ j) ^ i) w = (ρ (z ^ (j + p - k)) ^ i) w := by
    intro i
    rw [← map_pow, hg, ((hzc (x * z ^ k)).pow_right (j + p - k)).symm.mul_pow, map_mul,
      Module.End.mul_apply, hfix, map_pow]
  simp only [cosetAverage, LinearMap.sum_apply, hpow]
  split_ifs with hjk
  · subst hjk
    simp only [Nat.add_sub_cancel_left, hexp, map_one, one_pow, Module.End.one_apply,
      Finset.sum_const, Finset.card_range]
    exact odd_nsmul_eq_self_two hp2 w
  · have hnd : ¬ p ∣ j + p - k := by
      rintro ⟨c, hc⟩
      have h1 : c ≤ 1 := by
        by_contra h
        have : p * 2 ≤ p * c := Nat.mul_le_mul_left p (by omega)
        omega
      interval_cases c <;> omega
    exact sum_pow_apply_eq_zero hp2 hTp (u := z ^ (j + p - k)) (hzc _)
      (by rw [← pow_mul, mul_comm, pow_mul, hexp, one_pow])
      (exists_pow_pow_eq_self (hexp z) hnd) hw.1

theorem mem_cosetFixed_succ (hzc : ∀ g : Q, Commute g z) {y : Q} (hyx : y⁻¹ * x * y = x * z)
    {j : ℕ} {w : V} (hw : w ∈ cosetFixed ρ z x j) : ρ y⁻¹ w ∈ cosetFixed ρ z x (j + 1) := by
  rw [mem_cosetFixed] at hw ⊢
  refine ⟨mapsTo_centralImage ((hzc y⁻¹).map ρ) w hw.1, ?_⟩
  have hconj : x * z ^ (j + 1) * y⁻¹ = y⁻¹ * (x * z ^ j) := by
    have hzj : y * z ^ j * y⁻¹ = z ^ j := by
      rw [((hzc y).pow_right j).eq, mul_inv_cancel_right]
    calc x * z ^ (j + 1) * y⁻¹ = x * z * z ^ j * y⁻¹ := by rw [pow_succ', ← mul_assoc]
      _ = y⁻¹ * x * y * z ^ j * y⁻¹ := by rw [hyx]
      _ = y⁻¹ * x * (y * z ^ j * y⁻¹) := by group
      _ = y⁻¹ * (x * z ^ j) := by rw [hzj, mul_assoc]
  rw [← Module.End.mul_apply, ← map_mul, hconj, map_mul, Module.End.mul_apply, hw.2]

omit hp in
theorem cosetFixed_add_self (hexp : ∀ g : Q, g ^ p = 1) (j : ℕ) :
    cosetFixed ρ z x (j + p) = cosetFixed ρ z x j := by
  rw [cosetFixed, cosetFixed, pow_add, hexp, mul_one]

end Eigen

section Dimension

variable {p : ℕ} [hp : Fact p.Prime] {Q : Type*} [Group Q] {V : Type*} [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] {ρ : Representation (ZMod 2) Q V}
  {z x : Q}

theorem sum_finrank_inf_cosetFixed_le (hp2 : p ≠ 2) (hzc : ∀ g : Q, Commute g z)
    (hexp : ∀ g : Q, g ^ p = 1) {S : Submodule (ZMod 2) V} :
    ∑ j : Fin p, finrank (ZMod 2) ↥(S ⊓ cosetFixed ρ z x j) ≤ finrank (ZMod 2) S := by
  classical
  let Ψ : (∀ j : Fin p, ↥(S ⊓ cosetFixed ρ z x j)) →ₗ[ZMod 2] V :=
    ∑ j : Fin p, (S ⊓ cosetFixed ρ z x j).subtype.comp (LinearMap.proj j)
  have hΨ : ∀ s, Ψ s = ∑ j : Fin p, ((s j : ↥(S ⊓ cosetFixed ρ z x j)) : V) := fun s => by
    simp [Ψ, LinearMap.sum_apply]
  have hΨS : ∀ s, Ψ s ∈ S := fun s => by
    rw [hΨ]
    exact S.sum_mem fun j _ => (Submodule.mem_inf.1 (s j).2).1
  let Ψ' := LinearMap.codRestrict S Ψ hΨS
  have hinj : Function.Injective Ψ' := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro s hs
    rw [LinearMap.mem_ker] at hs
    have hs' : Ψ s = 0 := congrArg Subtype.val hs
    rw [Submodule.mem_bot]
    funext k
    have h := congrArg (cosetAverage p ρ z x k) hs'
    rw [map_zero, hΨ, map_sum] at h
    have hterm : ∀ j : Fin p, cosetAverage p ρ z x k ((s j : ↥(S ⊓ cosetFixed ρ z x j)) : V) =
        if (k : ℕ) = j then ((s j : ↥(S ⊓ cosetFixed ρ z x j)) : V) else 0 := fun j =>
      cosetAverage_apply_of_mem hp2 hzc hexp k.2 j.2 (Submodule.mem_inf.1 (s j).2).2
    simp only [hterm, Fin.val_inj, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at h
    exact Subtype.ext h
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_pi_fintype] at h

theorem finrank_centralImageAlgebra_le (hK : IsField (centralImageAlgebra ρ z))
    {T : Submodule (ZMod 2) V} (hTW : T ≤ centralImage ρ z) (hT : ∀ t ∈ T, ρ z t ∈ T) {w : V}
    (hw : w ∈ T) (hw0 : w ≠ 0) :
    finrank (ZMod 2) (centralImageAlgebra ρ z) ≤ finrank (ZMod 2) T := by
  let w' : centralImage ρ z := ⟨w, hTW hw⟩
  let Λ : centralImageAlgebra ρ z →ₗ[ZMod 2] T :=
    { toFun := fun c => ⟨((c : Module.End (ZMod 2) (centralImage ρ z)) w' : V),
        apply_mem_of_mem_centralImageAlgebra hT c.2 hw⟩
      map_add' := fun c d => Subtype.ext (by simp)
      map_smul' := fun r c => Subtype.ext (by simp) }
  have hzero : ∀ c, Λ c = 0 → c = 0 := by
    intro c hc
    by_contra hc0
    obtain ⟨d, hd⟩ := hK.mul_inv_cancel hc0
    have hcw : ((c : Module.End (ZMod 2) (centralImage ρ z)) w' : V) = 0 :=
      congrArg Subtype.val hc
    apply hw0
    have hd' : (d : Module.End (ZMod 2) (centralImage ρ z)) *
        (c : Module.End (ZMod 2) (centralImage ρ z)) = 1 := by
      rw [← Subalgebra.coe_mul, hK.mul_comm, hd, Subalgebra.coe_one]
    have := congrArg (fun A : Module.End (ZMod 2) (centralImage ρ z) => ((A w' : _) : V)) hd'
    simp only [Module.End.mul_apply, Module.End.one_apply] at this
    have hcw' : (c : Module.End (ZMod 2) (centralImage ρ z)) w' = 0 := Subtype.ext hcw
    rw [hcw', map_zero] at this
    exact this.symm
  have hinj : Function.Injective Λ := by
    intro c d hcd
    rw [← sub_eq_zero]
    exact hzero _ (by rw [map_sub, hcd, sub_self])
  exact LinearMap.finrank_le_finrank_of_injective hinj

omit [FiniteDimensional (ZMod 2) V] in
theorem inf_cosetFixed_ne_bot_add (hzc : ∀ g : Q, Commute g z) {y : Q}
    (hyx : y⁻¹ * x * y = x * z) {S : Submodule (ZMod 2) V} (hS : ∀ g : Q, ∀ s ∈ S, ρ g s ∈ S)
    {j : ℕ} (h : S ⊓ cosetFixed ρ z x j ≠ ⊥) (m : ℕ) : S ⊓ cosetFixed ρ z x (j + m) ≠ ⊥ := by
  induction m with
  | zero => exact h
  | succ m ih =>
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ih
    obtain ⟨hwS, hwE⟩ := Submodule.mem_inf.1 hw
    intro hbot
    have hmem : ρ y⁻¹ w ∈ S ⊓ cosetFixed ρ z x (j + (m + 1)) :=
      Submodule.mem_inf.2 ⟨hS _ _ hwS, mem_cosetFixed_succ hzc hyx hwE⟩
    rw [hbot, Submodule.mem_bot] at hmem
    apply hw0
    have := congrArg (ρ y) hmem
    rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply,
      map_zero] at this

omit [FiniteDimensional (ZMod 2) V] in
theorem exists_inf_cosetFixed_ne_bot (hp2 : p ≠ 2) (hzc : ∀ g : Q, Commute g z)
    (hexp : ∀ g : Q, g ^ p = 1) {S : Submodule (ZMod 2) V} (hSW : S ≤ centralImage ρ z)
    (hS : ∀ g : Q, ∀ s ∈ S, ρ g s ∈ S) (hS0 : S ≠ ⊥) :
    ∃ j < p, S ⊓ cosetFixed ρ z x j ≠ ⊥ := by
  obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
  by_contra hall
  push Not at hall
  apply hs0
  rw [← sum_cosetAverage_apply (x := x) hp2 hzc hexp (hSW hs)]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hmem : cosetAverage p ρ z x j s ∈ S ⊓ cosetFixed ρ z x j :=
    Submodule.mem_inf.2 ⟨cosetAverage_mem hS j hs,
      cosetAverage_mem_cosetFixed hzc hexp j (hSW hs)⟩
  rw [hall j (Finset.mem_range.1 hj), Submodule.mem_bot] at hmem
  exact hmem

omit [FiniteDimensional (ZMod 2) V] in
theorem inf_cosetFixed_ne_bot (hp2 : p ≠ 2) (hzc : ∀ g : Q, Commute g z)
    (hexp : ∀ g : Q, g ^ p = 1) {y : Q} (hyx : y⁻¹ * x * y = x * z)
    {S : Submodule (ZMod 2) V} (hSW : S ≤ centralImage ρ z) (hS : ∀ g : Q, ∀ s ∈ S, ρ g s ∈ S)
    (hS0 : S ≠ ⊥) (k : ℕ) : S ⊓ cosetFixed ρ z x k ≠ ⊥ := by
  obtain ⟨j, hj, hne⟩ := exists_inf_cosetFixed_ne_bot (x := x) hp2 hzc hexp hSW hS hS0
  have h := inf_cosetFixed_ne_bot_add hzc hyx hS hne (k + p - j)
  rwa [show j + (k + p - j) = k + p by omega, cosetFixed_add_self hexp] at h

omit [FiniteDimensional (ZMod 2) V] in
theorem inf_cosetFixed_invariant (hzc : ∀ g : Q, Commute g z) {S : Submodule (ZMod 2) V}
    (hS : ∀ g : Q, ∀ s ∈ S, ρ g s ∈ S) (j : ℕ) :
    ∀ t ∈ S ⊓ cosetFixed ρ z x j, ρ z t ∈ S ⊓ cosetFixed ρ z x j := by
  intro t ht
  obtain ⟨htS, htE⟩ := Submodule.mem_inf.1 ht
  rw [mem_cosetFixed] at htE
  refine Submodule.mem_inf.2 ⟨hS z t htS, mem_cosetFixed.2 ⟨mapsTo_centralImage
    (Commute.refl _) t htE.1, ?_⟩⟩
  rw [← Module.End.mul_apply, ← map_mul, (hzc (x * z ^ j)).eq, map_mul,
    Module.End.mul_apply, htE.2]

theorem eq_bot_or_eq_centralImage (hp2 : p ≠ 2) (hzc : ∀ g : Q, Commute g z)
    (hexp : ∀ g : Q, g ^ p = 1) {y : Q} (hyx : y⁻¹ * x * y = x * z)
    (hK : IsField (centralImageAlgebra ρ z))
    (hKdim : finrank (ZMod 2) (centralImageAlgebra ρ z) = p - 1)
    (hWdim : finrank (ZMod 2) (centralImage ρ z) = p * (p - 1)) {S : Submodule (ZMod 2) V}
    (hSW : S ≤ centralImage ρ z) (hS : ∀ g : Q, ∀ s ∈ S, ρ g s ∈ S) :
    S = ⊥ ∨ S = centralImage ρ z := by
  by_cases hS0 : S = ⊥
  · exact Or.inl hS0
  refine Or.inr (Submodule.eq_of_le_of_finrank_le hSW ?_)
  have hlow : ∀ k : Fin p, p - 1 ≤ finrank (ZMod 2) ↥(S ⊓ cosetFixed ρ z x k) := by
    intro k
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (inf_cosetFixed_ne_bot hp2 hzc hexp hyx hSW hS hS0 k)
    rw [← hKdim]
    exact finrank_centralImageAlgebra_le hK (inf_le_left.trans hSW)
      (inf_cosetFixed_invariant hzc hS k) hw hw0
  have hsum := sum_finrank_inf_cosetFixed_le (ρ := ρ) (x := x) hp2 hzc hexp (S := S)
  have h2 : ∑ _k : Fin p, (p - 1) ≤ ∑ k : Fin p, finrank (ZMod 2) ↥(S ⊓ cosetFixed ρ z x k) :=
    Finset.sum_le_sum fun k _ => hlow k
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h2
  rw [hWdim]
  omega

theorem finrank_inf_cosetFixed (hp2 : p ≠ 2) (hzc : ∀ g : Q, Commute g z)
    (hexp : ∀ g : Q, g ^ p = 1) {y : Q} (hyx : y⁻¹ * x * y = x * z)
    (hK : IsField (centralImageAlgebra ρ z))
    (hKdim : finrank (ZMod 2) (centralImageAlgebra ρ z) = p - 1)
    (hWdim : finrank (ZMod 2) (centralImage ρ z) = p * (p - 1)) (k : Fin p) :
    finrank (ZMod 2) ↥(centralImage ρ z ⊓ cosetFixed ρ z x k) = p - 1 := by
  have hWinv : ∀ g : Q, ∀ s ∈ centralImage ρ z, ρ g s ∈ centralImage ρ z :=
    fun g => mapsTo_centralImage ((hzc g).map ρ)
  have hW0 : centralImage ρ z ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hWdim
    have h1 : 1 ≤ p - 1 := by have := hp.out.two_le; omega
    have : 0 < p * (p - 1) := Nat.mul_pos hp.out.pos h1
    omega
  set f : Fin p → ℕ := fun k => finrank (ZMod 2) ↥(centralImage ρ z ⊓ cosetFixed ρ z x k)
  have hlow : ∀ k : Fin p, p - 1 ≤ f k := by
    intro k
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (inf_cosetFixed_ne_bot hp2 hzc hexp hyx le_rfl hWinv hW0 k)
    rw [← hKdim]
    exact finrank_centralImageAlgebra_le hK inf_le_left (inf_cosetFixed_invariant hzc hWinv k)
      hw hw0
  have hsum : ∑ k, f k ≤ p * (p - 1) :=
    hWdim ▸ sum_finrank_inf_cosetFixed_le (ρ := ρ) (x := x) hp2 hzc hexp
  have hsplit : ∑ k, (f k - (p - 1)) + ∑ _k : Fin p, (p - 1) = ∑ k, f k := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => Nat.sub_add_cancel (hlow k)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsplit
  have hzero : ∑ k, (f k - (p - 1)) = 0 := by omega
  have hk := (Finset.sum_eq_zero_iff.1 hzero) k (Finset.mem_univ k)
  have := hlow k
  change f k = p - 1
  omega

end Dimension

section Endomorphisms

variable {p : ℕ} [hp : Fact p.Prime] {Q : Type*} [Group Q] {V : Type*} [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] {ρ : Representation (ZMod 2) Q V}
  {z x : Q}

local notation "W" => centralImage ρ z

theorem mem_centralImageAlgebra_iff (hp2 : p ≠ 2) (hzc : ∀ g : Q, Commute g z)
    (hexp : ∀ g : Q, g ^ p = 1) {y : Q} (hyx : y⁻¹ * x * y = x * z)
    (hK : IsField (centralImageAlgebra ρ z))
    (hKdim : finrank (ZMod 2) (centralImageAlgebra ρ z) = p - 1)
    (hWdim : finrank (ZMod 2) (centralImage ρ z) = p * (p - 1))
    (hW : ∀ g : Q, centralImage ρ z ≤ (centralImage ρ z).comap (ρ g))
    (φ : Module.End (ZMod 2) (centralImage ρ z)) :
    φ ∈ centralImageAlgebra ρ z ↔
      ∀ g : Q, φ * ρ.subrepresentation (centralImage ρ z) hW g =
        ρ.subrepresentation (centralImage ρ z) hW g * φ := by
  set σ := ρ.subrepresentation W hW with hσdef
  have hσ : ∀ (g : Q) (w : W), ((σ g w : W) : V) = ρ g w := fun g w => rfl
  have hσz : ∀ g : Q, Commute (σ g) (centralImageOp ρ z) := by
    intro g
    refine LinearMap.ext fun w => Subtype.ext ?_
    change ρ g (ρ z w) = ρ z (ρ g w)
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ((hzc g).map ρ).eq]
  constructor
  · intro hφ g
    exact (commute_of_mem_centralImageAlgebra (hσz g) hφ).symm.eq
  · intro hφ
    have hWinv : ∀ g : Q, ∀ s ∈ W, ρ g s ∈ W := fun g s hs => hW g hs
    have hW0 : W ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hWdim
      have h1 : 1 ≤ p - 1 := by have := hp.out.two_le; omega
      have : 0 < p * (p - 1) := Nat.mul_pos hp.out.pos h1
      omega
    obtain ⟨w₀, hw₀, hw₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (inf_cosetFixed_ne_bot (x := x) hp2 hzc hexp hyx le_rfl hWinv hW0 0)
    have hw₀W : w₀ ∈ W := (Submodule.mem_inf.1 hw₀).1
    set w₀' : W := ⟨w₀, hw₀W⟩ with hw₀'def
    let Λ : centralImageAlgebra ρ z →ₗ[ZMod 2] ↥(W ⊓ cosetFixed ρ z x 0) :=
      { toFun := fun c => ⟨((c : Module.End (ZMod 2) W) w₀' : V),
          apply_mem_of_mem_centralImageAlgebra (inf_cosetFixed_invariant hzc hWinv 0) c.2 hw₀⟩
        map_add' := fun c d => Subtype.ext (by simp)
        map_smul' := fun r c => Subtype.ext (by simp) }
    have hdim := finrank_inf_cosetFixed (x := x) hp2 hzc hexp hyx hK hKdim hWdim
      ⟨0, hp.out.pos⟩
    have hΛinj : Function.Injective Λ := by
      intro c d hcd
      rw [← sub_eq_zero]
      by_contra hc0
      obtain ⟨e, he⟩ := hK.mul_inv_cancel hc0
      have hcw : (((c - d : centralImageAlgebra ρ z) : Module.End (ZMod 2) W) w₀' : V) = 0 := by
        have h := congrArg Subtype.val hcd
        simp only [Λ, LinearMap.coe_mk, AddHom.coe_mk] at h
        simp [LinearMap.sub_apply, h]
      have he' : (e : Module.End (ZMod 2) W) * ((c - d : centralImageAlgebra ρ z) :
          Module.End (ZMod 2) W) = 1 := by
        rw [← Subalgebra.coe_mul, hK.mul_comm, he, Subalgebra.coe_one]
      apply hw₀0
      have h := congrArg (fun A : Module.End (ZMod 2) W => ((A w₀' : W) : V)) he'
      simp only [Module.End.mul_apply, Module.End.one_apply] at h
      have hcw' : ((c - d : centralImageAlgebra ρ z) : Module.End (ZMod 2) W) w₀' = 0 :=
        Subtype.ext hcw
      rw [hcw', map_zero] at h
      exact h.symm
    have hΛsurj : Function.Surjective Λ := by
      rw [← LinearMap.range_eq_top]
      apply Submodule.eq_top_of_finrank_eq
      rw [LinearMap.finrank_range_of_inj hΛinj, hKdim, hdim]
    have hφw₀ : ((φ w₀' : W) : V) ∈ W ⊓ cosetFixed ρ z x 0 := by
      refine Submodule.mem_inf.2 ⟨(φ w₀').2, mem_cosetFixed.2 ⟨(φ w₀').2, ?_⟩⟩
      have h := congrArg (fun A : Module.End (ZMod 2) W => ((A w₀' : W) : V)) (hφ (x * z ^ 0))
      simp only [Module.End.mul_apply] at h
      rw [← hσ, ← h]
      have hfix : σ (x * z ^ 0) w₀' = w₀' :=
        Subtype.ext (mem_cosetFixed.1 (Submodule.mem_inf.1 hw₀).2).2
      rw [hfix]
    obtain ⟨c, hc⟩ := hΛsurj ⟨_, hφw₀⟩
    have hcw₀ : (c : Module.End (ZMod 2) W) w₀' = φ w₀' := by
      have h := congrArg Subtype.val hc
      exact Subtype.ext h
    set D : Module.End (ZMod 2) W := φ - c with hDdef
    have hcσ : ∀ g : Q, Commute (σ g) (c : Module.End (ZMod 2) W) :=
      fun g => commute_of_mem_centralImageAlgebra (hσz g) c.2
    have hDσ : ∀ g : Q, D * σ g = σ g * D := by
      intro g
      rw [hDdef, sub_mul, mul_sub, hφ g, (hcσ g).eq]
    have hφz : Commute φ (centralImageOp ρ z) := by
      have h := hφ z
      exact h
    have hDK : ∀ k ∈ centralImageAlgebra ρ z, Commute D k := by
      intro k hk
      refine Commute.sub_left ?_ ?_
      · exact commute_of_mem_centralImageAlgebra hφz hk
      · exact (Algebra.isMulCommutative_adjoin (ZMod 2) (Set.pairwise_singleton _ _)).is_comm.comm
          c ⟨k, hk⟩ |> congrArg Subtype.val
    have hDE : ∀ v : W, (v : V) ∈ W ⊓ cosetFixed ρ z x 0 → D v = 0 := by
      intro v hv
      obtain ⟨k, hk⟩ := hΛsurj ⟨v, hv⟩
      have hkv : (k : Module.End (ZMod 2) W) w₀' = v := by
        have h := congrArg Subtype.val hk
        exact Subtype.ext h
      rw [← hkv, ← Module.End.mul_apply, (hDK k k.2).eq, Module.End.mul_apply, hDdef,
        LinearMap.sub_apply, hcw₀, sub_self, map_zero]
    set S := (LinearMap.ker D).map (centralImage ρ z).subtype with hSdef
    have hSW : S ≤ W := by
      rintro _ ⟨v, -, rfl⟩
      exact v.2
    have hSinv : ∀ g : Q, ∀ s ∈ S, ρ g s ∈ S := by
      rintro g _ ⟨v, hv, rfl⟩
      refine ⟨σ g v, ?_, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker] at hv ⊢
      rw [← Module.End.mul_apply, hDσ g, Module.End.mul_apply, hv, map_zero]
    have hS0 : S ≠ ⊥ := by
      intro h
      have hmem : w₀ ∈ S := ⟨w₀', hDE w₀' hw₀, rfl⟩
      rw [h, Submodule.mem_bot] at hmem
      exact hw₀0 hmem
    rcases eq_bot_or_eq_centralImage hp2 hzc hexp hyx hK hKdim hWdim hSW hSinv with h | h
    · exact absurd h hS0
    · have hD : D = 0 := by
        refine LinearMap.ext fun v => ?_
        have hv : (v : V) ∈ S := by rw [h]; exact v.2
        obtain ⟨v', hv', hvv'⟩ := hv
        have : v' = v := Subtype.ext hvv'
        rw [← this]
        exact hv'
      have hφc : φ = c := by
        rw [← sub_eq_zero]
        exact hD
      rw [hφc]
      exact c.2

end Endomorphisms

section Centralizer

variable {Q : Type*} [Group Q] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) Q V} {z : Q}

local notation "U" => centralFixed ρ z
local notation "W" => centralImage ρ z
local notation "K" => centralImageAlgebra ρ z

omit [Group Q] in
theorem endomorphism_eq_of_isCompl {A B : Submodule (ZMod 2) V} (h : IsCompl A B)
    {f g : Module.End (ZMod 2) V} (hA : ∀ a ∈ A, f a = g a) (hB : ∀ b ∈ B, f b = g b) : f = g := by
  refine LinearMap.ext fun v => ?_
  have hv : v ∈ A ⊔ B := by rw [h.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
  rw [map_add, map_add, hA a ha, hB b hb]

theorem commute_of_mem_centralizer {a : LinearMap.GeneralLinearGroup (ZMod 2) V}
    (ha : a ∈ Subgroup.centralizer (Set.range ρ.asGroupHom)) (g : Q) :
    Commute (a : Module.End (ZMod 2) V) (ρ g) := by
  have h := congrArg Units.val (Subgroup.mem_centralizer_iff.1 ha (ρ.asGroupHom g) ⟨g, rfl⟩)
  simp only [Units.val_mul, Representation.asGroupHom_apply] at h
  exact h.symm

theorem exists_centralizer_mulEquiv (hUW : IsCompl U W) (hUtriv : ∀ g : Q, ∀ u ∈ U, ρ g u = u)
    (hW : ∀ g : Q, centralImage ρ z ≤ (centralImage ρ z).comap (ρ g))
    (hEnd : ∀ φ : Module.End (ZMod 2) W, φ ∈ K ↔
      ∀ g : Q, φ * ρ.subrepresentation W hW g = ρ.subrepresentation W hW g * φ) :
    ∃ e : Subgroup.centralizer (Set.range ρ.asGroupHom) ≃*
        LinearMap.GeneralLinearGroup (ZMod 2) U × Kˣ,
      ∀ a : Subgroup.centralizer (Set.range ρ.asGroupHom),
        (∀ u : U, ((((e a).1 : LinearMap.GeneralLinearGroup (ZMod 2) U) :
          U →ₗ[ZMod 2] U) u : V) = ((a : LinearMap.GeneralLinearGroup (ZMod 2) V) :
            V →ₗ[ZMod 2] V) u) ∧
        ∀ w : W, (((((e a).2 : Kˣ) : K) : Module.End (ZMod 2) W) w : V) =
          ((a : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) w := by
  classical
  set C := Subgroup.centralizer (Set.range ρ.asGroupHom) with hCdef
  set σ := ρ.subrepresentation W hW with hσdef
  have hcz : ∀ a ∈ C, Commute (a : Module.End (ZMod 2) V) (ρ z) :=
    fun a ha => commute_of_mem_centralizer ha z
  let rU : ∀ a ∈ C, Module.End (ZMod 2) U := fun a ha =>
    (a : Module.End (ZMod 2) V).restrict (mapsTo_centralFixed (hcz a ha))
  let rW : ∀ a ∈ C, Module.End (ZMod 2) W := fun a ha =>
    (a : Module.End (ZMod 2) V).restrict (mapsTo_centralImage (hcz a ha))
  have hrU : ∀ a (ha : a ∈ C) (u : U), ((rU a ha u : U) : V) = (a : Module.End (ZMod 2) V) u :=
    fun _ _ _ => rfl
  have hrW : ∀ a (ha : a ∈ C) (w : W), ((rW a ha w : W) : V) = (a : Module.End (ZMod 2) V) w :=
    fun _ _ _ => rfl
  have hrWK : ∀ a (ha : a ∈ C), rW a ha ∈ K := by
    intro a ha
    rw [hEnd]
    intro g
    refine LinearMap.ext fun w => Subtype.ext ?_
    change (a : Module.End (ZMod 2) V) (ρ g w) = ρ g ((a : Module.End (ZMod 2) V) w)
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, (commute_of_mem_centralizer ha g).eq]
  have hinvU : ∀ a (ha : a ∈ C), rU a ha * rU a⁻¹ (inv_mem ha) = 1 := by
    intro a ha
    refine LinearMap.ext fun u => Subtype.ext ?_
    change (a : Module.End (ZMod 2) V) (((a⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) :
      Module.End (ZMod 2) V) u) = u
    rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Module.End.one_apply]
  have hinvU' : ∀ a (ha : a ∈ C), rU a⁻¹ (inv_mem ha) * rU a ha = 1 := by
    intro a ha
    refine LinearMap.ext fun u => Subtype.ext ?_
    change ((a⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : Module.End (ZMod 2) V)
      ((a : Module.End (ZMod 2) V) u) = u
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Module.End.one_apply]
  have hinvW : ∀ a (ha : a ∈ C), rW a ha * rW a⁻¹ (inv_mem ha) = 1 := by
    intro a ha
    refine LinearMap.ext fun w => Subtype.ext ?_
    change (a : Module.End (ZMod 2) V) (((a⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) :
      Module.End (ZMod 2) V) w) = w
    rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Module.End.one_apply]
  have hinvW' : ∀ a (ha : a ∈ C), rW a⁻¹ (inv_mem ha) * rW a ha = 1 := by
    intro a ha
    refine LinearMap.ext fun w => Subtype.ext ?_
    change ((a⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : Module.End (ZMod 2) V)
      ((a : Module.End (ZMod 2) V) w) = w
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Module.End.one_apply]
  let F : C →* LinearMap.GeneralLinearGroup (ZMod 2) U × Kˣ :=
    { toFun := fun a => (⟨rU a a.2, rU a⁻¹ (inv_mem a.2), hinvU a a.2, hinvU' a a.2⟩,
        ⟨⟨rW a a.2, hrWK a a.2⟩, ⟨rW a⁻¹ (inv_mem a.2), hrWK _ (inv_mem a.2)⟩,
          Subtype.ext (hinvW a a.2), Subtype.ext (hinvW' a a.2)⟩)
      map_one' := by
        refine Prod.ext (Units.ext (LinearMap.ext fun u => Subtype.ext ?_))
          (Units.ext (Subtype.ext (LinearMap.ext fun w => Subtype.ext ?_)))
        · rfl
        · rfl
      map_mul' := fun a b => by
        refine Prod.ext (Units.ext (LinearMap.ext fun u => Subtype.ext ?_))
          (Units.ext (Subtype.ext (LinearMap.ext fun w => Subtype.ext ?_)))
        · rfl
        · rfl }
  have hF1 : ∀ a (u : U), (((F a).1 : U →ₗ[ZMod 2] U) u : V) =
      ((a : LinearMap.GeneralLinearGroup (ZMod 2) V) : Module.End (ZMod 2) V) u :=
    fun _ _ => rfl
  have hF2 : ∀ a (w : W), (((((F a).2 : Kˣ) : K) : Module.End (ZMod 2) W) w : V) =
      ((a : LinearMap.GeneralLinearGroup (ZMod 2) V) : Module.End (ZMod 2) V) w :=
    fun _ _ => rfl
  have hinj : Function.Injective F := by
    intro a b hab
    apply Subtype.ext
    apply Units.ext
    refine endomorphism_eq_of_isCompl hUW (fun u hu => ?_) (fun w hw => ?_)
    · have := congrArg (fun e : LinearMap.GeneralLinearGroup (ZMod 2) U × Kˣ =>
        (((e.1 : U →ₗ[ZMod 2] U) ⟨u, hu⟩ : U) : V)) hab
      exact this
    · have := congrArg (fun e : LinearMap.GeneralLinearGroup (ZMod 2) U × Kˣ =>
        ((((e.2 : Kˣ) : K) : Module.End (ZMod 2) W) ⟨w, hw⟩ : V)) hab
      exact this
  have hsurj : Function.Surjective F := by
    rintro ⟨α, c⟩
    let B : Module.End (ZMod 2) V := LinearMap.ofIsCompl hUW
      ((centralFixed ρ z).subtype ∘ₗ (α : U →ₗ[ZMod 2] U))
      ((centralImage ρ z).subtype ∘ₗ ((c : K) : Module.End (ZMod 2) W))
    let B' : Module.End (ZMod 2) V := LinearMap.ofIsCompl hUW
      ((centralFixed ρ z).subtype ∘ₗ ((α⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) U) :
        U →ₗ[ZMod 2] U))
      ((centralImage ρ z).subtype ∘ₗ (((c⁻¹ : Kˣ) : K) : Module.End (ZMod 2) W))
    have hBu : ∀ u : U, B u = ((α : U →ₗ[ZMod 2] U) u : V) := fun u =>
      LinearMap.ofIsCompl_apply_left hUW u
    have hBw : ∀ w : W, B w = (((c : K) : Module.End (ZMod 2) W) w : V) := fun w =>
      LinearMap.ofIsCompl_apply_right hUW w
    have hB'u : ∀ u : U, B' u = ((((α⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) U) :
        U →ₗ[ZMod 2] U)) u : V) := fun u => LinearMap.ofIsCompl_apply_left hUW u
    have hB'w : ∀ w : W, B' w = (((((c⁻¹ : Kˣ) : K) : Module.End (ZMod 2) W)) w : V) :=
      fun w => LinearMap.ofIsCompl_apply_right hUW w
    have hαinv : ∀ u : U, (α : U →ₗ[ZMod 2] U) (((α⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) U) :
        U →ₗ[ZMod 2] U) u) = u := fun u => by
      rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Module.End.one_apply]
    have hαinv' : ∀ u : U, (((α⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) U) :
        U →ₗ[ZMod 2] U)) ((α : U →ₗ[ZMod 2] U) u) = u := fun u => by
      rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Module.End.one_apply]
    have hcinv : ∀ w : W, ((c : K) : Module.End (ZMod 2) W) ((((c⁻¹ : Kˣ) : K) :
        Module.End (ZMod 2) W) w) = w := fun w => by
      rw [← Module.End.mul_apply, ← Subalgebra.coe_mul, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, Subalgebra.coe_one, Module.End.one_apply]
    have hcinv' : ∀ w : W, ((((c⁻¹ : Kˣ) : K) : Module.End (ZMod 2) W))
        (((c : K) : Module.End (ZMod 2) W) w) = w := fun w => by
      rw [← Module.End.mul_apply, ← Subalgebra.coe_mul, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, Subalgebra.coe_one, Module.End.one_apply]
    have hBB' : B * B' = 1 := endomorphism_eq_of_isCompl hUW
      (fun u hu => by
        rw [Module.End.mul_apply, Module.End.one_apply, hB'u ⟨u, hu⟩, hBu, hαinv])
      (fun w hw => by
        rw [Module.End.mul_apply, Module.End.one_apply, hB'w ⟨w, hw⟩, hBw, hcinv])
    have hB'B : B' * B = 1 := endomorphism_eq_of_isCompl hUW
      (fun u hu => by
        rw [Module.End.mul_apply, Module.End.one_apply, hBu ⟨u, hu⟩, hB'u, hαinv'])
      (fun w hw => by
        rw [Module.End.mul_apply, Module.End.one_apply, hBw ⟨w, hw⟩, hB'w, hcinv'])
    let b : LinearMap.GeneralLinearGroup (ZMod 2) V := ⟨B, B', hBB', hB'B⟩
    have hbC : b ∈ C := by
      rw [hCdef, Subgroup.mem_centralizer_iff]
      rintro _ ⟨g, rfl⟩
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, Representation.asGroupHom_apply]
      change ρ g * B = B * ρ g
      refine endomorphism_eq_of_isCompl hUW (fun u hu => ?_) (fun w hw => ?_)
      · rw [Module.End.mul_apply, Module.End.mul_apply, hBu ⟨u, hu⟩, hUtriv g u hu,
          hUtriv g _ ((α : U →ₗ[ZMod 2] U) ⟨u, hu⟩).2]
        exact (hBu ⟨u, hu⟩).symm
      · have hgw : ρ g w ∈ W := hW g hw
        rw [Module.End.mul_apply, Module.End.mul_apply, hBw ⟨w, hw⟩,
          show ρ g w = ((⟨ρ g w, hgw⟩ : W) : V) from rfl, hBw ⟨ρ g w, hgw⟩]
        have hcomm := (hEnd ((c : K) : Module.End (ZMod 2) W)).1 (c : K).2 g
        have h := congrArg (fun A : Module.End (ZMod 2) W => ((A ⟨w, hw⟩ : W) : V)) hcomm
        exact h.symm
    refine ⟨⟨b, hbC⟩, Prod.ext (Units.ext (LinearMap.ext fun u => Subtype.ext ?_))
      (Units.ext (Subtype.ext (LinearMap.ext fun w => Subtype.ext ?_)))⟩
    · exact hBu u
    · exact hBw w
  exact ⟨MulEquiv.ofBijective F ⟨hinj, hsurj⟩, fun a => ⟨hF1 a, hF2 a⟩⟩

end Centralizer

theorem extraspecial_prime_cyclotomic_minimal_module {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hord : orderOf (2 : ZMod p) = p - 1) {Q : Type*} [Group Q] (hQ : IsExtraspecialPGroup p Q)
    (_hcard : Nat.card Q = p ^ 3) (hexp : Monoid.exponent Q = p) {x y z : Q}
    (_hgen : Subgroup.closure {x, y} = ⊤) (hz : z = ⁅x, y⁆) {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) Q V)
    {r : ℕ} (hr : r < p - 1) (hV : finrank (ZMod 2) V = p * (p - 1) + r)
    (hU : finrank (ZMod 2) (centralFixed ρ z) = r) :
    IsCompl (centralFixed ρ z) (centralImage ρ z) ∧
    (∀ g : Q, ∀ u ∈ centralFixed ρ z, ρ g u = u) ∧
    IsField (centralImageAlgebra ρ z) ∧ Nat.card (centralImageAlgebra ρ z) = 2 ^ (p - 1) ∧
    finrank (centralImageAlgebra ρ z) (centralImage ρ z) = p ∧
    (centralImage ρ z ≠ ⊥ ∧ ∀ S : Submodule (ZMod 2) V, S ≤ centralImage ρ z →
      (∀ g : Q, ∀ s ∈ S, ρ g s ∈ S) → S = ⊥ ∨ S = centralImage ρ z) ∧
    ∃ hW : ∀ g : Q, centralImage ρ z ≤ (centralImage ρ z).comap (ρ g),
      (∀ φ : Module.End (ZMod 2) (centralImage ρ z), φ ∈ centralImageAlgebra ρ z ↔
        ∀ g : Q, φ * ρ.subrepresentation (centralImage ρ z) hW g =
          ρ.subrepresentation (centralImage ρ z) hW g * φ) ∧
      ∃ e : Subgroup.centralizer (Set.range ρ.asGroupHom) ≃*
          LinearMap.GeneralLinearGroup (ZMod 2) (centralFixed ρ z) × (centralImageAlgebra ρ z)ˣ,
        ∀ a : Subgroup.centralizer (Set.range ρ.asGroupHom),
          (∀ u : centralFixed ρ z, ((((e a).1 : LinearMap.GeneralLinearGroup (ZMod 2)
            (centralFixed ρ z)) : centralFixed ρ z →ₗ[ZMod 2] centralFixed ρ z) u : V) =
              ((a : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) u) ∧
          ∀ w : centralImage ρ z, (((((e a).2 : (centralImageAlgebra ρ z)ˣ) :
            centralImageAlgebra ρ z) : Module.End (ZMod 2) (centralImage ρ z)) w : V) =
              ((a : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) w := by
  have hzc : ∀ g : Q, Commute g z := by
    intro g
    have hmem : z ∈ Subgroup.center Q := by
      rw [← hQ.2.1, hz, _root_.commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
    exact ((Subgroup.mem_center_iff.1 hmem) g)
  have hexp' : ∀ g : Q, g ^ p = 1 := fun g => by
    rw [← hexp]
    exact Monoid.pow_exponent_eq_one g
  have hTp : ρ z ^ p = 1 := by rw [← map_pow, hexp', map_one]
  have hyx : y⁻¹ * x * y = x * z := by
    have hzy : y⁻¹ * z * y = z := by
      rw [mul_assoc, ← (hzc y).eq, ← mul_assoc, inv_mul_cancel, one_mul]
    calc y⁻¹ * x * y = y⁻¹ * (x * y * x⁻¹ * y⁻¹) * y * x := by group
      _ = y⁻¹ * z * y * x := by rw [hz, commutatorElement_def]
      _ = z * x := by rw [hzy]
      _ = x * z := ((hzc x).eq).symm
  have hΦ := irreducible_cyclotomic_two hp2 hord
  have hUW := isCompl_centralFixed_centralImage hp2 hTp
  have hWdim : finrank (ZMod 2) (centralImage ρ z) = p * (p - 1) := by
    have := Submodule.finrank_add_eq_of_isCompl hUW
    omega
  have hp1 : 0 < p - 1 := by have := hp.out.two_le; omega
  have : Nontrivial (centralImage ρ z) :=
    Module.nontrivial_of_finrank_pos (R := ZMod 2) (by rw [hWdim]; exact Nat.mul_pos hp.out.pos hp1)
  have hKzero := aeval_centralImageOp_cyclotomic hp2 hTp
  have hK : IsField (centralImageAlgebra ρ z) :=
    isField_adjoin_singleton_of_aeval_eq_zero hΦ _ hKzero
  have hKdim : finrank (ZMod 2) (centralImageAlgebra ρ z) = p - 1 := by
    rw [centralImageAlgebra, finrank_adjoin_singleton_of_aeval_eq_zero hΦ
      (cyclotomic.monic p (ZMod 2)) _ hKzero, natDegree_cyclotomic_two]
  have : Finite (centralImage ρ z) := Module.finite_of_finite (ZMod 2)
  have : Finite (Module.End (ZMod 2) (centralImage ρ z)) :=
    Finite.of_injective _ (DFunLike.coe_injective (F := centralImage ρ z →ₗ[ZMod 2] _))
  have : Finite (centralImageAlgebra ρ z) := Subtype.finite
  have : Module.Finite (ZMod 2) (centralImageAlgebra ρ z) := Module.Finite.of_finite
  have hKcard : Nat.card (centralImageAlgebra ρ z) = 2 ^ (p - 1) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hKdim, Nat.card_zmod]
  have hKW : finrank (centralImageAlgebra ρ z) (centralImage ρ z) = p := by
    let _ : Field (centralImageAlgebra ρ z) := hK.toField
    have h := Module.finrank_mul_finrank (ZMod 2) (centralImageAlgebra ρ z) (centralImage ρ z)
    rw [hKdim, hWdim, mul_comm p] at h
    exact Nat.eq_of_mul_eq_mul_left hp1 h
  have hUtriv : ∀ g : Q, ∀ u ∈ centralFixed ρ z, ρ g u = u := fun g u hu =>
    apply_eq_self_of_mem_centralFixed hΦ (hU ▸ hr) (hzc g) (hexp' g) hu
  have hW0 : centralImage ρ z ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hWdim
    have := Nat.mul_pos hp.out.pos hp1
    omega
  have hW : ∀ g : Q, centralImage ρ z ≤ (centralImage ρ z).comap (ρ g) :=
    fun g w hw => mapsTo_centralImage ((hzc g).map ρ) w hw
  have hEnd := mem_centralImageAlgebra_iff hp2 hzc hexp' hyx hK hKdim hWdim hW
  refine ⟨hUW, hUtriv, hK, hKcard, hKW, ⟨hW0, fun S hSW hS =>
    eq_bot_or_eq_centralImage hp2 hzc hexp' hyx hK hKdim hWdim hSW hS⟩, hW, hEnd, ?_⟩
  exact exists_centralizer_mulEquiv hUW hUtriv hW hEnd

end CFSG.LinearAlgebra
