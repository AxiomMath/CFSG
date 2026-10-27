module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Separation
public import TauCeti.RingTheory.FiniteType.FiniteRange
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Data.EReal.Operations
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.Sheaves.Init
public import TauCeti.Algebra.AlgebraicGroup.Representation.JordanDecomposition.Basic
public import TauCeti.Algebra.AlgebraicGroup.Representation.SemisimplePoint

public noncomputable section

open WithConv
open scoped TensorProduct
open TauCeti

namespace CFSG.LieType.AlgebraicGroups.ReductiveDescent

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

theorem pow_finrank_eq_zero_of_isNilpotent {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {f : Module.End K V} (hf : IsNilpotent f) :
    f ^ Module.finrank K V = 0 := by
  have : Module.Free K V := Module.Free.of_divisionRing K V
  have hchar : LinearMap.charpoly f = Polynomial.X ^ Module.finrank K V :=
    (LinearMap.isNilpotent_iff_charpoly f).mp hf
  have h := LinearMap.aeval_self_charpoly f
  rw [hchar, map_pow, Polynomial.aeval_X] at h
  exact h

theorem pow_prime_pow_eq_one_of_sub_one_pow_eq_zero {R : Type*} [Ring R] {p E d : ℕ}
    [Fact p.Prime] [CharP R p] {f : R} (h : (f - 1) ^ d = 0) (hd : d ≤ p ^ E) :
    f ^ (p ^ E) = 1 := by
  have hf : f = (f - 1) + 1 := (sub_add_cancel f 1).symm
  rw [hf, add_pow_char_pow_of_commute p E (Commute.one_right _), one_pow]
  have hzero : (f - 1) ^ p ^ E = 0 := by
    rw [show p ^ E = d + (p ^ E - d) from (Nat.add_sub_cancel' hd).symm, pow_add, h, zero_mul]
  rw [hzero, zero_add]

theorem mk_one_tmul_basePointsRepresentation {K H M : Type*} [Field K] [CommRing H]
    [_root_.HopfAlgebra K H] [AddCommMonoid M] [Module K M] [Comodule K H M]
    (g : WithConv (H →ₐ[K] K)) (m : M) :
    ((TensorProduct.mk K K M) (1 : K)) (Comodule.basePointsRepresentation (H := H) M g m) =
      Comodule.endOfPoint M g.ofConv (((TensorProduct.mk K K M) (1 : K)) m) := by
  rw [TensorProduct.mk_apply, TensorProduct.mk_apply, Comodule.endOfPoint_tmul, one_smul,
    Comodule.endOfPoint_one_tmul_eq_one_tmul_basePointsRepresentation]

theorem mk_one_tmul_injective {K M : Type*} [CommSemiring K] [AddCommMonoid M] [Module K M] :
    Function.Injective ((TensorProduct.mk K K M) (1 : K)) := by
  intro a b hab
  have := congrArg (TensorProduct.lid K M) hab
  simpa [TensorProduct.mk_apply, TensorProduct.lid_tmul] using this

theorem endOfPoint_pow {K H M : Type*} [CommSemiring K] [Semiring H] [Bialgebra K H]
    [AddCommMonoid M] [Module K M] [Comodule K H M] {A : Type*} [CommSemiring A] [Algebra K A]
    (g : WithConv (H →ₐ[K] A)) (n : ℕ) :
    Comodule.endOfPoint M ((g ^ n).ofConv) = Comodule.endOfPoint M g.ofConv ^ n := by
  induction n with
  | zero =>
      rw [pow_zero, pow_zero,
        Comodule.endOfPoint_convOne (R := K) (H := H) (V := M) (A := A)]
      apply LinearMap.ext
      intro x
      rw [Module.End.one_apply]
      rfl
  | succ n ih =>
      rw [show g ^ (n + 1) = g ^ n * g from pow_succ g n]
      rw [Comodule.endOfPoint_convMul (R := K) (H := H) (V := M) (A := A)]
      rw [ih]
      apply LinearMap.ext
      intro x
      rfl

theorem endOfPoint_pow_prime_pow_eq_one {K H M : Type*} [Field K] [CommRing H]
    [_root_.HopfAlgebra K H] [AddCommMonoid M] [Module K M] [Comodule K H M]
    [Module.Finite K M] {p : ℕ} [CharP K p] (hp : p.Prime) (E : ℕ)
    (hE : Module.finrank K (K ⊗[K] M) ≤ p ^ E) (g : WithConv (H →ₐ[K] K))
    (hunip : IsNilpotent (Comodule.endOfPoint M g.ofConv - 1)) :
    Comodule.endOfPoint M g.ofConv ^ (p ^ E) = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have : Module.Finite K (K ⊗[K] M) := Module.Finite.equiv (TensorProduct.lid K M).symm
  have hpow : (Comodule.endOfPoint M g.ofConv - 1) ^ Module.finrank K (K ⊗[K] M) = 0 :=
    pow_finrank_eq_zero_of_isNilpotent hunip
  rcases subsingleton_or_nontrivial (K ⊗[K] M) with hW | hW
  · have := hW
    have : Subsingleton (Module.End K (K ⊗[K] M)) :=
      ⟨fun a b => LinearMap.ext fun m => Subsingleton.elim _ _⟩
    exact Subsingleton.elim _ _
  · have : FaithfulSMul K (Module.End K (K ⊗[K] M)) := inferInstance
    have : CharP (Module.End K (K ⊗[K] M)) p :=
      charP_of_injective_algebraMap' (A := Module.End K (K ⊗[K] M)) K p
    exact pow_prime_pow_eq_one_of_sub_one_pow_eq_zero (R := Module.End K (K ⊗[K] M))
      (f := Comodule.endOfPoint M g.ofConv) (p := p) (E := E)
      (d := Module.finrank K (K ⊗[K] M)) hpow hE

theorem unipotentPoint_eq_one_of_pow_eq_one_of_charZero {K H : Type u} [Field K] [CharZero K]
    [CommRing H] [_root_.HopfAlgebra K H] (g : WithConv (H →ₐ[K] K)) {m : ℕ}
    (hm : (m : K) ≠ 0) (hpow : g ^ m = 1)
    (hunip : TauCeti.HopfAlgebra.IsUnipotentPoint g) : g = 1 := by
  have : PerfectField K := PerfectField.ofCharZero
  have hss : TauCeti.HopfAlgebra.IsSemisimplePoint g := by
    rw [TauCeti.HopfAlgebra.isSemisimplePoint_def]
    intro M
    rw [LinearMap.GeneralLinearGroup.isSemisimple_def]
    have hpowM : (TauCeti.Comodule.pointsAction (M : Type u) g) ^ m = 1 := by
      rw [← map_pow (TauCeti.Comodule.pointsAction (M : Type u)) g m, hpow, map_one]
    have hgm : (LinearMap.GeneralLinearGroup.ofLinearEquiv
        (TauCeti.Comodule.pointsAction (M : Type u) g)) ^ m = 1 := by
      change (LinearMap.GeneralLinearGroup.generalLinearEquiv K ((K ⊗[K] M))).symm
        (TauCeti.Comodule.pointsAction (M : Type u) g) ^ m = 1
      rw [← map_pow (LinearMap.GeneralLinearGroup.generalLinearEquiv K ((K ⊗[K] M))).symm
        (TauCeti.Comodule.pointsAction (M : Type u) g) m, hpowM, map_one]
    have hval : ((LinearMap.GeneralLinearGroup.ofLinearEquiv
        (TauCeti.Comodule.pointsAction (M : Type u) g) : LinearMap.GeneralLinearGroup K
          (K ⊗[K] M)) : Module.End K (K ⊗[K] M)) ^ m = 1 := by
      have := congrArg (fun q : LinearMap.GeneralLinearGroup K (K ⊗[K] M) =>
        (q : Module.End K (K ⊗[K] M))) hgm
      simpa using this
    refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero
      (p := Polynomial.X ^ m - 1) ?_ ?_
    · simpa using (Polynomial.separable_X_pow_sub_C (1 : K) hm one_ne_zero).squarefree
    · rw [map_sub, map_pow, Polynomial.aeval_X, map_one, hval, sub_self]
  rw [TauCeti.HopfAlgebra.isSemisimplePoint_def] at hss
  have h1 : TauCeti.HopfAlgebra.Point.unipotentPart K H K g = g :=
    TauCeti.HopfAlgebra.Point.unipotentPart_eq_self K H K hunip
  have h2 : TauCeti.HopfAlgebra.Point.unipotentPart K H K g = 1 :=
    TauCeti.HopfAlgebra.Point.unipotentPart_eq_one_of_isSemisimple K H K hss
  exact h1.symm.trans h2

theorem eq_one_of_eq_counit_on_adjoin_eq_top {K H : Type*} [Field K] [CommRing H]
    [_root_.HopfAlgebra K H] {s : Set H} (hs : Algebra.adjoin K s = ⊤)
    (g : WithConv (H →ₐ[K] K)) (h : ∀ x ∈ s, g.ofConv x = Coalgebra.counit x) : g = 1 := by
  have hcounit : g.ofConv = Bialgebra.counitAlgHom K H :=
    AlgHom.ext_of_adjoin_eq_top hs fun x hx => by simpa using h x hx
  apply WithConv.ofConv_injective
  rw [hcounit]
  apply AlgHom.ext
  intro x
  rw [AlgHom.convOne_apply]
  simp

theorem ofConv_pow_apply_eq_counit_of_endOfPoint_pow_eq_one
    {K H : Type*} [Field K] [CommRing H] [_root_.HopfAlgebra K H] (N : Subcomodule K H H)
    (g : WithConv (H →ₐ[K] K)) (n : ℕ)
    (h : Comodule.endOfPoint (↥N) g.ofConv ^ n = 1) :
    ∀ x ∈ N, (g ^ n).ofConv x = Coalgebra.counit x := by
  intro x hx
  let m : ↥N := ⟨x, hx⟩
  let φ : Module.Dual K ↥N :=
    (Coalgebra.counit (R := K) (A := H)).comp (SMulMemClass.subtype N)
  have h2 : Comodule.matrixCoefficient (R := K) (C := H) (M := ↥N) φ m = x :=
    (Comodule.matrixCoefficient_counit_comp_subtype (R := K) (C := H) N m).trans rfl
  have hbpr : Comodule.basePointsRepresentation (H := H) (↥N) (g ^ n) m = m := by
    apply mk_one_tmul_injective (K := K) (M := ↥N)
    rw [mk_one_tmul_basePointsRepresentation, endOfPoint_pow, h]
    rfl
  have h1 := Comodule.apply_matrixCoefficient (R := K) (H := H) (M := ↥N) (g ^ n) φ m
  rw [h2, hbpr] at h1
  exact h1

omit [IsAlgClosed k] in
theorem finite_of_finite_pow_of_forall_isUnipotentPoint
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (N : Subgroup (WithConv (H →ₐ[k] k)))
    (hN : ∀ n ∈ N, TauCeti.HopfAlgebra.IsUnipotentPoint n)
    (m : ℕ) (hm : (m : k) ≠ 0)
    (hfin : ((fun n : WithConv (H →ₐ[k] k) => n ^ m) '' (N : Set (WithConv (H →ₐ[k] k)))).Finite) :
    (N : Set (WithConv (H →ₐ[k] k))).Finite := by
  classical
  by_cases hchar : CharZero k
  ·
    have := hchar
    have htriv : ∀ n ∈ N, n = 1 := by
      intro n hn
      by_contra hne
      have hnotfin : ¬ IsOfFinOrder n := by
        intro hfo
        obtain ⟨r, hrpos, hpowr⟩ := isOfFinOrder_iff_pow_eq_one.mp hfo
        exact hne (unipotentPoint_eq_one_of_pow_eq_one_of_charZero n
          (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hrpos)) hpowr (hN n hn))
      have hinjpow : Function.Injective (fun j : ℕ => n ^ j) :=
        injective_pow_iff_not_isOfFinOrder.mpr hnotfin
      have hmpos : 0 < m := Nat.pos_of_ne_zero fun h => hm (by rw [h]; simp)
      have hinj : Function.Injective (fun j : ℕ => n ^ (m * j)) := by
        intro j j' h
        exact Nat.mul_left_cancel hmpos (hinjpow h)
      have hmem : ∀ j : ℕ,
          n ^ (m * j) ∈ (fun x : WithConv (H →ₐ[k] k) => x ^ m) '' (N : Set _) := by
        intro j
        refine ⟨n ^ j, N.pow_mem hn j, ?_⟩
        change (n ^ j) ^ m = n ^ (m * j)
        rw [← pow_mul, mul_comm j m]
      exact (Set.infinite_of_injective_forall_mem hinj hmem) hfin
    refine Set.Finite.subset (Set.finite_singleton (1 : WithConv (H →ₐ[k] k))) ?_
    intro x hx
    simp only [Set.mem_singleton_iff]
    exact htriv x hx
  ·
    have hp0 : ringChar k ≠ 0 := fun h => hchar ((CharP.ringChar_zero_iff_CharZero k).mp h)
    have hp : (ringChar k).Prime :=
      (CharP.char_is_prime_or_zero k (ringChar k)).resolve_right hp0
    have hfree : Module.Free k H := Module.Free.of_divisionRing k H
    obtain ⟨t, htfin, htadjoin⟩ :=
      Subalgebra.fg_def.mp (Algebra.FiniteType.out (R := k) (A := H))
    obtain ⟨M, hMfin, htM⟩ :=
      Subcomodule.exists_finite_subcomodule_of_setFinite (R := k) (C := H) (M := H) htfin
    have hMfinite : Module.Finite k ↥M := hMfin
    let E := Nat.log (ringChar k) (Module.finrank k (k ⊗[k] ↥M)) + 1
    have hE : Module.finrank k (k ⊗[k] ↥M) ≤ (ringChar k) ^ E :=
      le_of_lt (Nat.lt_pow_succ_log_self hp.one_lt (Module.finrank k (k ⊗[k] ↥M)))
    have huniform : ∀ n ∈ N, n ^ (ringChar k) ^ E = 1 := by
      intro n hn
      refine eq_one_of_eq_counit_on_adjoin_eq_top (K := k) htadjoin (n ^ (ringChar k) ^ E) ?_
      intro x hx
      have hxM : x ∈ M := htM hx
      have hnil : IsNilpotent (Comodule.endOfPoint (↥M) n.ofConv - 1) := by
        have h := (TauCeti.HopfAlgebra.isUnipotentPoint_iff_forall_isNilpotent_endOfPoint_sub_one
          n).mp (hN n hn)
        exact h (TauCeti.FGComoduleCat.of (R := k) (C := H) (M := ↥M))
      have hend : Comodule.endOfPoint (↥M) n.ofConv ^ (ringChar k) ^ E = 1 :=
        endOfPoint_pow_prime_pow_eq_one (K := k) (H := H) (M := ↥M) hp E hE n hnil
      exact ofConv_pow_apply_eq_counit_of_endOfPoint_pow_eq_one
        M n ((ringChar k) ^ E) hend x hxM
    have hcop : Nat.Coprime m ((ringChar k) ^ E) := by
      refine Nat.Prime.coprime_pow_of_not_dvd hp ?_
      intro hdiv
      exact hm ((CharP.cast_eq_zero_iff k (ringChar k) m).mpr hdiv)
    have hpE : 1 < (ringChar k) ^ E :=
      show 1 < (ringChar k) ^ (Nat.log (ringChar k) (Module.finrank k (k ⊗[k] ↥M)) + 1) from
        Nat.one_lt_pow (Nat.succ_ne_zero _) hp.one_lt
    obtain ⟨c, -, hc⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hpE
    have hmc : m * c = 1 + (m * c / (ringChar k) ^ E) * (ringChar k) ^ E :=
      calc m * c = (ringChar k) ^ E * (m * c / (ringChar k) ^ E) + m * c % (ringChar k) ^ E :=
            (Nat.div_add_mod (m * c) ((ringChar k) ^ E)).symm
        _ = 1 + (m * c / (ringChar k) ^ E) * (ringChar k) ^ E := by
            rw [hc, mul_comm ((ringChar k) ^ E) (m * c / (ringChar k) ^ E), Nat.add_comm]
    have key : ∀ n ∈ N, n = (n ^ m) ^ c := by
      intro n hn
      have hexp : n ^ (ringChar k) ^ E = 1 := huniform n hn
      calc n = n ^ (m * c) := by
            rw [hmc, pow_add, pow_one, mul_comm (m * c / (ringChar k) ^ E) ((ringChar k) ^ E),
              pow_mul, hexp, one_pow, mul_one]
        _ = (n ^ m) ^ c := pow_mul n m c
    refine Set.finite_coe_iff.mp ?_
    have hfin' : (Set.range (fun n : N => ((n : WithConv (H →ₐ[k] k)) ^ m))).Finite := by
      refine hfin.subset ?_
      rintro _ ⟨n, rfl⟩
      exact ⟨(n : WithConv (H →ₐ[k] k)), n.2, rfl⟩
    have : Finite (Set.range (fun n : N => ((n : WithConv (H →ₐ[k] k)) ^ m))) :=
      Set.finite_coe_iff.mpr hfin'
    have hinj : Function.Injective (fun n : N => ((n : WithConv (H →ₐ[k] k)) ^ m)) := by
      intro a b hab
      have hab' : ((a : WithConv (H →ₐ[k] k)) ^ m) = ((b : WithConv (H →ₐ[k] k)) ^ m) := hab
      apply Subtype.ext
      calc (a : WithConv (H →ₐ[k] k)) = (((a : WithConv (H →ₐ[k] k)) ^ m) ^ c) := key a a.2
        _ = (((b : WithConv (H →ₐ[k] k)) ^ m) ^ c) := by rw [hab']
        _ = (b : WithConv (H →ₐ[k] k)) := (key b b.2).symm
    exact Finite.of_injective (fun n : N => (⟨_, Set.mem_range_self n⟩ : Set.range _))
      (fun a b h => hinj (Subtype.ext_iff.mp h))

theorem eq_augmentation_of_finite_quotientPoints (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (I : TauCeti.HopfIdeal k H)
    (hconn : ConnectedSpace (PrimeSpectrum (TauCeti.FiniteTypeCommHopfAlgCat.quotient H I)))
    (hred : IsReduced (TauCeti.FiniteTypeCommHopfAlgCat.quotient H I))
    (hfin : (TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj I
      (CommAlgCat.of k k) : Set (WithConv (H →ₐ[k] k))).Finite) :
    I = TauCeti.HopfIdeal.augmentation k H := by
  classical
  let Q := TauCeti.FiniteTypeCommHopfAlgCat.quotient H I
  have : IsReduced Q := hred
  have : ConnectedSpace (PrimeSpectrum Q) := hconn
  have : Algebra.FiniteType k (TauCeti.CommHopfAlgCat.quotient H.obj I) :=
    TauCeti.FiniteTypeCommHopfAlgCat.finiteType Q
  have : IsReduced (TauCeti.CommHopfAlgCat.quotient H.obj I) := hred
  have hfin' : (Set.range (TauCeti.CommHopfAlgCat.quotientPointsHom H.obj I
      (CommAlgCat.of k k))).Finite := by
    simpa [TauCeti.CommHopfAlgCat.quotientPointsSubgroup] using hfin
  have : Finite (Set.range (TauCeti.CommHopfAlgCat.quotientPointsHom H.obj I
      (CommAlgCat.of k k))) := Set.finite_coe_iff.mpr hfin'
  have hfinQ : Finite (WithConv (Q →ₐ[k] k)) := by
    refine Finite.of_injective
      (fun f : WithConv (Q →ₐ[k] k) =>
        (⟨TauCeti.CommHopfAlgCat.quotientPointsHom H.obj I (CommAlgCat.of k k) f,
          Set.mem_range_self f⟩ :
          Set.range (TauCeti.CommHopfAlgCat.quotientPointsHom H.obj I (CommAlgCat.of k k))))
      ?_
    intro a b hab
    exact TauCeti.CommHopfAlgCat.quotientPointsHom_injective H.obj I (CommAlgCat.of k k)
      (Subtype.ext_iff.mp hab)
  have : Finite (Q →ₐ[k] k) :=
    Finite.of_injective WithConv.toConv (fun a b h => by
      simpa using congrArg WithConv.ofConv h)
  have hpoint : ∀ f : Q →ₐ[k] k, f = Bialgebra.counitAlgHom k Q := by
    intro f
    apply AlgHom.ext
    intro a
    have hscalar : a = algebraMap k Q (Bialgebra.counitAlgHom k Q a) :=
      TauCeti.eq_algebraMap_of_finite_range_eval (k := k) (A := Q) a
        (Set.finite_range (fun f : Q →ₐ[k] k => f a)) (Bialgebra.counitAlgHom k Q)
    conv_lhs => rw [hscalar]
    exact (f.commutes (Bialgebra.counitAlgHom k Q a)).trans (by simp)
  have hQPS : ∀ g ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj I
      (CommAlgCat.of k k), g = 1 := by
    intro g hg
    obtain ⟨f, rfl⟩ := hg
    have hf : f = 1 := by
      apply WithConv.ofConv_injective
      apply AlgHom.ext
      intro a
      rw [AlgHom.convOne_apply]
      have h := congrArg (fun g : Q →ₐ[k] k => g a) (hpoint (f.ofConv : Q →ₐ[k] k))
      simpa using h
    rw [hf, map_one]
  refine le_antisymm ?_ ?_
  · exact TauCeti.HopfIdeal.le_augmentation k H I
  · refine TauCeti.HopfIdeal.le_of_quotientPointsSubgroup_le (K := k) (H := H.obj)
      (I := TauCeti.HopfIdeal.augmentation k H) (J := I) ?_
    intro g hg
    rw [TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_augmentation_iff]
    exact hQPS g hg

end CFSG.LieType.AlgebraicGroups.ReductiveDescent
