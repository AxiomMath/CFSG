module

public import Mathlib.LinearAlgebra.Projectivization.Action
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.Defs
import CFSG.LocalAnalysis.SignalizerFunctor.CoprimeElementaryProjectiveRank
import CFSG.LocalAnalysis.SignalizerFunctor.QuadraticEndomorphisms
import CFSG.LocalAnalysis.SignalizerFunctor.SurjectiveSylowLifting
import Mathlib.Algebra.CharP.LinearMaps
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.TotallySplit

public section

namespace CFSG

open scoped MatrixGroups
open SignalizerFunctor.Helpers

abbrev PGL2 (K : Type*) [Field K] := Matrix.ProjGenLinGroup (Fin 2) K

abbrev ProjectiveLine (K : Type*) [Field K] := Projectivization K (Fin 2 → K)

private theorem exists_normal_isElementaryAbelian (G : Type*) [Group G] [Finite G]
    [Group.IsSolvable G] [Nontrivial G] :
    ∃ r : ℕ, r.Prime ∧ ∃ R : Subgroup G,
      R.Normal ∧ R ≠ ⊥ ∧ IsElementaryAbelian r R := by
  classical
  have hex : ∃ n, derivedSeries G n = ⊥ := Group.IsSolvable.solvable
  have hi : Nat.find hex ≠ 0 := by
    rw [Ne, Nat.find_eq_zero, derivedSeries_zero]
    exact top_ne_bot
  let N := derivedSeries G (Nat.find hex - 1)
  have hNbot : N ≠ ⊥ := Nat.find_min hex (Nat.sub_one_lt hi)
  have : IsMulCommutative N := by
    apply Subgroup.le_centralizer_iff_isMulCommutative.mp
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    rw [← derivedSeries_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hi)]
    exact Nat.find_spec hex
  let : CommGroup N := { N.toGroup with mul_comm := mul_comm' }
  obtain ⟨r, hr, hrdvd⟩ :=
    Nat.exists_prime_and_dvd fun hc => hNbot (Subgroup.card_eq_one.mp hc)
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := N) r hrdvd
  let T := (powMonoidHom (α := N) r).ker
  have : T.Characteristic := by
    refine Subgroup.characteristic_iff_le_comap.mpr fun f y (hy : y ^ r = 1) => ?_
    change f y ^ r = 1
    rw [← map_pow, hy, map_one]
  have : (derivedSeries G (Nat.find hex - 1)).Normal := derivedSeries_normal G _
  let R := T.map N.subtype
  have hxT : x ∈ T := by
    change x ^ r = 1
    rw [← hx]
    exact pow_orderOf_eq_one x
  have hRbot : R ≠ ⊥ := by
    intro hzero
    have hm : x.val ∈ R := Subgroup.mem_map_of_mem N.subtype hxT
    rw [hzero, Subgroup.mem_bot] at hm
    exact hr.ne_one (hx.symm.trans (orderOf_eq_one_iff.mpr (Subtype.ext hm)))
  refine ⟨r, hr, R, inferInstance, hRbot,
    { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }⟩
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun y => Subtype.ext ?_
  obtain ⟨z, hz, hzy⟩ := y.property
  have hp : (z : G) ^ r = 1 := congrArg Subtype.val (show z ^ r = 1 from hz)
  change (y : G) ^ r = 1
  rw [← hzy]
  exact hp

private theorem conj_eq_of_card_eq_four (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    {G : Type*} [Group G] (R : Subgroup G) [R.Normal] [Finite R] (hc : Nat.card R = 4)
    (hgen : Subgroup.closure {h : G | IsPElement p h} = ⊤) (h : G) (a : R) :
    h * (a : G) * h⁻¹ = a := by
  let f : G →* Equiv.Perm R := (MulAut.toPerm R).comp MulAut.conjNormal
  have hker : Subgroup.closure {h : G | IsPElement p h} ≤ f.ker := by
    rw [Subgroup.closure_le]
    rintro g hg
    obtain ⟨k, hk⟩ := exists_orderOf_eq_prime_pow_iff.mp hg
    have hcop : (p ^ k).Coprime (Nat.card (Equiv.Perm R)) := by
      rw [Nat.card_perm, hc]
      exact ((Fact.out : p.Prime).coprime_factorial_of_lt (by omega)).pow_left k
    refine (pow_eq_one_iff_of_coprime hcop).mp ⟨by simpa using congrArg f hk, ?_⟩
    have := Fintype.ofFinite (Equiv.Perm R)
    simp [Nat.card_eq_fintype_card]
  have hf : f h = 1 := hker (hgen ▸ Subgroup.mem_top h)
  have ha : MulAut.conjNormal h a = a := congrArg (fun e : Equiv.Perm R => e a) hf
  simpa [MulAut.conjNormal_apply] using congrArg Subtype.val ha

section PGL2

variable {K : Type*} [Field K]

private noncomputable def glLinearEquiv :
    GL (Fin 2) K ≃* ((Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) :=
  Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv K _)

private theorem mk_smul_eq (A : GL (Fin 2) K) (x : ProjectiveLine K) :
    Matrix.ProjGenLinGroup.mk A • x = projectiveLinearAction (glLinearEquiv A) x := by
  induction x using Projectivization.ind with
  | h v hv => rw [Projectivization.PGL.mk_smul_mk, projective_linear_action_mk]; rfl

private theorem toPGL_smul (g : SL(2, K)) (x : ProjectiveLine K) :
    Matrix.SpecialLinearGroup.toPGL g • x =
      projectiveLinearAction (Matrix.SpecialLinearGroup.toLin' g) x := by
  induction x using Projectivization.ind with
  | h v hv => rw [projective_linear_action_mk]; rfl

section IsAlgClosed

variable [IsAlgClosed K]

private theorem toPGL_surjective :
    Function.Surjective (Matrix.SpecialLinearGroup.toPGL : SL(2, K) →* PGL2 K) := by
  intro h
  obtain ⟨q, hq⟩ := (Matrix.ProjectiveSpecialLinearGroup.isoPSLOfAlgClosedOfNonempty
    (n := Fin 2) (F := K)).symm.surjective h
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(2, K)) q
  exact ⟨g, hq⟩

private instance : FaithfulSMul (PGL2 K) (ProjectiveLine K) :=
  faithfulSMul_iff.mpr fun h hh => by
    obtain ⟨g, rfl⟩ := toPGL_surjective h
    have hg : g ∈ (MulAction.toPermHom SL(2, K) (ProjectiveLine K)).ker := by
      refine Equiv.ext fun x => ?_
      induction x using Projectivization.ind with
      | h v hv => exact hh (Projectivization.mk K v hv)
    rw [Projectivization.SL_mulAction_ker, ← Matrix.SpecialLinearGroup.toPGL_ker] at hg
    exact MonoidHom.mem_ker.mp hg

private theorem exists_mk_eq_of_pow_eq_one (h : PGL2 K) {n : ℕ} (hn : n ≠ 0) (hh : h ^ n = 1) :
    ∃ A : GL (Fin 2) K, Matrix.ProjGenLinGroup.mk A = h ∧ A ^ n = 1 := by
  obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective h
  rw [← map_pow, Matrix.ProjGenLinGroup.mk_eq_one,
    Matrix.GeneralLinearGroup.center_eq_range_scalar] at hh
  obtain ⟨u, hu⟩ := hh
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq (u : K) (Nat.pos_of_ne_zero hn)
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact u.ne_zero (by rw [← hd, zero_pow hn])
  let s := Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 d hd0)
  have hs : s ^ n = A ^ n := by
    rw [← map_pow, ← hu]
    congr 1
    exact Units.ext (by simp [hd])
  have hsc : s⁻¹ ∈ Subgroup.center (GL (Fin 2) K) := Subgroup.inv_mem _ <| by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨_, rfl⟩
  refine ⟨s⁻¹ * A, ?_, ?_⟩
  · rw [map_mul, map_inv, Matrix.ProjGenLinGroup.mk_scalar, inv_one, one_mul]
  · rw [(show Commute s⁻¹ A from (Subgroup.mem_center_iff.mp hsc A).symm).mul_pow, inv_pow, hs,
      inv_mul_cancel]

variable (p : ℕ) [Fact p.Prime] [CharP K p]

private theorem orderOf_eq_and_existsUnique_fixed (h : PGL2 K) (hne : h ≠ 1)
    (hp : IsPElement p h) : orderOf h = p ∧ ∃! x : ProjectiveLine K, h • x = x := by
  obtain ⟨k, hk⟩ := exists_orderOf_eq_prime_pow_iff.mp hp
  obtain ⟨A, rfl, hA⟩ :=
    exists_mk_eq_of_pow_eq_one h (pow_ne_zero k (Fact.out : p.Prime).ne_zero) hk
  let T := glLinearEquiv A
  have hT : T ^ p ^ k = 1 := by rw [← map_pow, hA, map_one]
  have hT1 : T ≠ 1 := fun h1 => hne (by rw [glLinearEquiv.map_eq_one_iff.mp h1, map_one])
  refine ⟨orderOf_eq_prime ?_ hne, ?_⟩
  ·
    have : CharP (Module.End K (Fin 2 → K)) p := Module.charP_end (R := K) (p := p)
      ⟨1, by rw [Ideal.torsionOf_eq_bot_iff_of_isTorsionFree]; exact one_ne_zero⟩
    let toEnd := LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := K) (M := Fin 2 → K)
    have hpk : (toEnd T - 1) ^ p ^ k = 0 := by
      rw [sub_pow_char_pow_of_commute (p := p) (n := k) (Commute.one_right _), ← map_pow, hT,
        map_one, one_pow, sub_self]
    have hsq : (toEnd T - 1) ^ 2 = 0 := by
      have haev := (toEnd T - 1).aeval_self_charpoly
      rw [IsNilpotent.charpoly_eq_X_pow_finrank (show IsNilpotent (toEnd T - 1) from ⟨_, hpk⟩),
        Module.finrank_fin_fun] at haev
      simpa using haev
    have hTp : T ^ p = 1 := by
      have := quadratic_ring_element_prime_power p (toEnd T) hsq
      rw [← map_pow, ← map_one toEnd] at this
      exact LinearEquiv.toLinearMap_injective this
    have hAp : A ^ p = 1 := glLinearEquiv.injective (by rw [map_pow, map_one]; exact hTp)
    rw [← map_pow, hAp, map_one]
  · obtain ⟨x, hx, hu⟩ := prime_power_projective_unique_fixed (Module.finrank_fin_fun K) p
      Fact.out T hT1 k hT
    exact ⟨x, (mk_smul_eq A x).trans hx, fun y hy => hu y ((mk_smul_eq A y).symm.trans hy)⟩

private theorem eq_one_of_fixed_of_fixed (h : PGL2 K) (hp : IsPElement p h)
    {x y : ProjectiveLine K} (hxy : x ≠ y) (hx : h • x = x) (hy : h • y = y) : h = 1 := by
  obtain ⟨k, hk⟩ := exists_orderOf_eq_prime_pow_iff.mp hp
  obtain ⟨A, rfl, hA⟩ :=
    exists_mk_eq_of_pow_eq_one h (pow_ne_zero k (Fact.out : p.Prime).ne_zero) hk
  rw [mk_smul_eq] at hx hy
  have hT := prime_power_projective_two_fixed_identity (Module.finrank_fin_fun K) p Fact.out
    (glLinearEquiv A) k (by rw [← map_pow, hA, map_one]) x y hxy hx hy
  rw [glLinearEquiv.map_eq_one_iff.mp hT, map_one]

private theorem eq_one_of_smul_mem_pair (hpodd : Odd p) (h : PGL2 K) (hp : IsPElement p h)
    {x y : ProjectiveLine K} (hxy : x ≠ y) (hx : h • x ∈ ({x, y} : Set (ProjectiveLine K)))
    (hy : h • y ∈ ({x, y} : Set (ProjectiveLine K))) : h = 1 := by
  have hne : h • x ≠ h • y := (MulAction.injective h).ne hxy
  have h2 : h ^ 2 • x = x ∧ h ^ 2 • y = y := by
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact absurd (hx.trans hy.symm) hne
    · exact ⟨by rw [pow_two, mul_smul, hx, hx], by rw [pow_two, mul_smul, hy, hy]⟩
    · exact ⟨by rw [pow_two, mul_smul, hx, hy], by rw [pow_two, mul_smul, hy, hx]⟩
    · exact absurd (hx.trans hy.symm) hne
  obtain ⟨k, hk⟩ := exists_orderOf_eq_prime_pow_iff.mp hp
  have hsq : h ^ 2 = 1 := eq_one_of_fixed_of_fixed p (h ^ 2)
    (exists_orderOf_eq_prime_pow_iff.mpr ⟨k, by rw [← pow_mul, mul_comm, pow_mul, hk, one_pow]⟩)
    hxy h2.1 h2.2
  exact (pow_eq_one_iff_of_coprime ((Nat.coprime_two_left.mpr hpodd).pow_right k)).mp ⟨hsq, hk⟩

private theorem exists_fixed_iff_of_orderOf_eq {r : ℕ} [Fact r.Prime] (hpr : p ≠ r)
    (h : PGL2 K) (horder : orderOf h = r) :
    ∃ x y : ProjectiveLine K, x ≠ y ∧ ∀ z, h • z = z ↔ z = x ∨ z = y := by
  obtain ⟨A, rfl, hA⟩ := exists_mk_eq_of_pow_eq_one h (Fact.out : r.Prime).ne_zero
    (horder ▸ pow_orderOf_eq_one h)
  have hne : projectiveLinearAction (glLinearEquiv A) ≠ 1 := by
    intro h1
    have : Matrix.ProjGenLinGroup.mk A = 1 :=
      eq_of_smul_eq_smul (α := ProjectiveLine K) fun x => by simp [mk_smul_eq, h1]
    rw [this, orderOf_one] at horder
    exact (Fact.out : r.Prime).one_lt.ne horder
  obtain ⟨x, y, hxy, hfix⟩ := coprime_order_projective_fixed_exactly_two
    (Module.finrank_fin_fun K) p (glLinearEquiv A) r
    (fun hd => hpr ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).mp hd))
    (by rw [← map_pow, hA, map_one]) hne
  exact ⟨x, y, hxy, fun z => by rw [mk_smul_eq]; exact hfix z⟩

private theorem card_eq_of_isElementaryAbelian {r : ℕ} [Fact r.Prime] (hpr : p ≠ r)
    (R : Subgroup (PGL2 K)) [Finite R] [IsElementaryAbelian r R] (hR : R ≠ ⊥) :
    Nat.card R = r ∨ (r = 2 ∧ Nat.card R = 4) := by
  classical
  let S := R.comap (Matrix.SpecialLinearGroup.toPGL : SL(2, K) →* PGL2 K)
  let π : S →* R := Matrix.SpecialLinearGroup.toPGL.subgroupComap R
  have hπ : Function.Surjective π := fun x => by
    obtain ⟨g, hg⟩ := toPGL_surjective x.val
    exact ⟨⟨g, by rw [Subgroup.mem_comap, hg]; exact x.property⟩, Subtype.ext hg⟩
  have : Finite S := by
    have : Finite (Subgroup.center SL(2, K)) := Finite.of_equiv _
      (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (R := K) (0 : Fin 2)).symm.toEquiv
    have : Finite π.ker := Finite.of_injective
      (fun g : π.ker => (⟨g.val.val, by
        rw [← Matrix.SpecialLinearGroup.toPGL_ker]
        exact congrArg Subtype.val g.property⟩ : Subgroup.center SL(2, K)))
      fun a b hab => Subtype.ext <| Subtype.ext <|
        congrArg (fun z : Subgroup.center SL(2, K) => z.val) hab
    exact π.finite_iff_finite_ker_range.mpr
      ⟨inferInstance, Finite.of_injective _ Subtype.val_injective⟩
  obtain ⟨P, hP⟩ :=
    surjective_pgroup_sylow_lift r Fact.out π hπ (IsElementaryAbelian.isPGroup r R)
  let πP : P →* R := π.comp (P : Subgroup S).subtype
  have hπP : Function.Surjective πP := fun x => by
    obtain ⟨g, hg, hx⟩ : x ∈ (P : Subgroup S).map π := by rw [hP]; exact Subgroup.mem_top x
    exact ⟨⟨g, hg⟩, hx⟩
  let ρ : P →* ((Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) :=
    Matrix.SpecialLinearGroup.toLin'.comp (S.subtype.comp (P : Subgroup S).subtype)
  let φ : R →* Equiv.Perm (ProjectiveLine K) :=
    (MulAction.toPermHom (PGL2 K) (ProjectiveLine K)).comp R.subtype
  have hφ : Function.Injective φ := fun a b hab => Subtype.ext <|
    eq_of_smul_eq_smul fun x => congrArg (fun e : Equiv.Perm (ProjectiveLine K) => e x) hab
  have heq (g : P) : projectiveLinearAction (ρ g) = φ (πP g) :=
    Equiv.ext fun x => (toPGL_smul g.val.val x).symm
  have hab (a b : P) : Commute (projectiveLinearAction (ρ a)) (projectiveLinearAction (ρ b)) := by
    rw [heq, heq]
    exact (show Commute (πP a) (πP b) from mul_comm' _ _).map φ
  have hexp (a : P) : projectiveLinearAction (ρ a) ^ r = 1 := by
    rw [heq, ← map_pow, Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p r R), map_one]
  have hnon : ∃ a : P, projectiveLinearAction (ρ a) ≠ 1 := by
    obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hR
    obtain ⟨a, rfl⟩ := hπP x
    exact ⟨a, fun h1 => hx (hφ ((heq a).symm.trans (h1.trans φ.map_one.symm)))⟩
  have hrank := coprime_elementary_projective_rank_bound (Module.finrank_fin_fun K) p Fact.out
    r Fact.out hpr.symm ρ P.isPGroup' hab hexp hnon
  have hrange : (projectiveLinearAction.comp ρ).range = φ.range := by
    rw [show projectiveLinearAction.comp ρ = φ.comp πP from MonoidHom.ext heq,
      MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hπP, Subgroup.map_top]
  have hcard : Nat.card (projectiveLinearAction.comp ρ).range = Nat.card R := by
    rw [hrange]
    exact Nat.card_congr (Equiv.ofBijective φ.rangeRestrict
      ⟨MonoidHom.rangeRestrict_injective_iff.mpr hφ, φ.rangeRestrict_surjective⟩).symm
  simpa only [hcard] using hrank

private theorem eq_one_of_forall_smul_mem_pair (hpodd : Odd p) (H : Subgroup (PGL2 K))
    (hgen : Subgroup.closure {h : H | IsPElement p h} = ⊤) {x y : ProjectiveLine K}
    (hxy : x ≠ y) (hpair : ∀ h : H, (h : PGL2 K) • x ∈ ({x, y} : Set (ProjectiveLine K)) ∧
      (h : PGL2 K) • y ∈ ({x, y} : Set (ProjectiveLine K))) (h : H) : h = 1 := by
  have hle : Subgroup.closure {h : H | IsPElement p h} ≤ ⊥ := by
    rw [Subgroup.closure_le]
    rintro g hg
    exact Subgroup.mem_bot.mpr <| OneMemClass.coe_eq_one.mp <| eq_one_of_smul_mem_pair p hpodd _
      (hg.imp fun _ hk => (Subgroup.orderOf_coe g).trans hk) hxy (hpair g).1 (hpair g).2
  exact Subgroup.mem_bot.mp (hle (hgen ▸ Subgroup.mem_top h))

private theorem eq_one_of_conj_fixed (hpodd : Odd p) {r : ℕ} [Fact r.Prime] (hpr : p ≠ r)
    (H : Subgroup (PGL2 K)) (hgen : Subgroup.closure {h : H | IsPElement p h} = ⊤)
    (a : PGL2 K) (ha : orderOf a = r)
    (hconj : ∀ (g : H) (z : ProjectiveLine K), a • z = z →
      ((g : PGL2 K)⁻¹ * a * g) • z = z)
    (h : H) : h = 1 := by
  obtain ⟨x, y, hxy, hfix⟩ := exists_fixed_iff_of_orderOf_eq p hpr a ha
  have hmem (g : H) (z : ProjectiveLine K) (hz : a • z = z) :
      (g : PGL2 K) • z ∈ ({x, y} : Set (ProjectiveLine K)) := by
    refine (hfix _).mp ?_
    calc a • (g : PGL2 K) • z = (g : PGL2 K) • ((g : PGL2 K)⁻¹ * a * g) • z := by
          simp [mul_smul]
      _ = (g : PGL2 K) • z := by rw [hconj g z hz]
  exact eq_one_of_forall_smul_mem_pair p hpodd H hgen hxy (fun g =>
    ⟨hmem g x ((hfix x).mpr (Or.inl rfl)), hmem g y ((hfix y).mpr (Or.inr rfl))⟩) h

private theorem exists_fixed_of_normal_isElementaryAbelian_self (H : Subgroup (PGL2 K))
    (R : Subgroup H) [R.Normal] [IsElementaryAbelian p R] (hR : R ≠ ⊥) :
    ∃ x : ProjectiveLine K, ∀ h : H, (h : PGL2 K) • x = x := by
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hR
  let f : R →* PGL2 K := H.subtype.comp R.subtype
  have hpow (b : R) : b ^ p = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p R) b
  have hfa : f a ≠ 1 := fun he => ha (Subtype.ext (Subtype.ext he))
  obtain ⟨_, x, hx, hu⟩ := orderOf_eq_and_existsUnique_fixed p (f a) hfa
    (exists_orderOf_eq_prime_pow_iff.mpr ⟨1, by simpa using congrArg f (hpow a)⟩)
  have hfixed (b : R) : f b • x = x := by
    refine hu _ ?_
    show f a • f b • x = f b • x
    rw [smul_smul, ← map_mul, mul_comm' a b, map_mul, mul_smul, hx]
  refine ⟨x, fun h => hu _ ?_⟩
  have hc : ((h : PGL2 K)⁻¹ * f a * h) • x = x := by
    simpa [f, MulAut.conjNormal_apply] using hfixed (MulAut.conjNormal h⁻¹ a)
  calc f a • (h : PGL2 K) • x = (h : PGL2 K) • ((h : PGL2 K)⁻¹ * f a * h) • x := by
        simp [mul_smul]
    _ = (h : PGL2 K) • x := by rw [hc]

private theorem exists_fixed_of_normal_isElementaryAbelian (hpodd : Odd p)
    (H : Subgroup (PGL2 K)) [Finite H] (hgen : Subgroup.closure {h : H | IsPElement p h} = ⊤)
    (hrange : 5 ≤ p ∨ Odd (Nat.card H)) {r : ℕ} [Fact r.Prime]
    (R : Subgroup H) [R.Normal] [IsElementaryAbelian r R] (hR : R ≠ ⊥) :
    ∃ x : ProjectiveLine K, ∀ h : H, (h : PGL2 K) • x = x := by
  classical
  by_cases hpr : p = r
  · subst hpr
    exact exists_fixed_of_normal_isElementaryAbelian_self p H R hR
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hR
  have hne : R.map H.subtype ≠ ⊥ :=
    fun he => hR ((R.map_eq_bot_iff_of_injective Subtype.val_injective).mp he)
  let e := R.equivMapOfInjective H.subtype Subtype.val_injective
  have : Finite (R.map H.subtype) := Finite.of_equiv R e.toEquiv
  have : IsElementaryAbelian r (R.map H.subtype) := IsElementaryAbelian.map_subtype
  have hbound := card_eq_of_isElementaryAbelian p hpr (R.map H.subtype) hne
  rw [← Nat.card_congr e.toEquiv] at hbound
  have hpow : a ^ r = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p r R) a
  have ha' : orderOf ((a : H) : PGL2 K) = r :=
    orderOf_eq_prime (by simpa using congrArg (fun b : R => ((b : H) : PGL2 K)) hpow)
      fun he => ha (Subtype.ext (Subtype.ext he))
  have htriv : ∀ h : H, h = 1 := by
    rcases hbound with hcyc | ⟨hr, hfour⟩
    ·
      have hzp : Subgroup.zpowers a = ⊤ := zpowers_eq_top_of_prime_card hcyc ha
      refine eq_one_of_conj_fixed p hpodd hpr H hgen _ ha' fun g z hz => ?_
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp
        (hzp ▸ Subgroup.mem_top (MulAut.conjNormal g⁻¹ a))
      have hn' := congrArg (fun b : R => ((b : H) : PGL2 K)) hn
      simp at hn'
      rw [← hn']
      exact (MulAction.stabilizer (PGL2 K) z).zpow_mem hz n
    ·
      have hp5 : 5 ≤ p := hrange.resolve_right fun hodd => hodd.not_two_dvd_nat <|
        (show 2 ∣ Nat.card R by rw [hfour]; norm_num).trans R.card_subgroup_dvd_card
      refine eq_one_of_conj_fixed p hpodd hpr H hgen _ ha' fun g z hz => ?_
      have hc := congrArg Subtype.val (conj_eq_of_card_eq_four p hp5 R hfour hgen g⁻¹ a)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] at hc
      rwa [hc]
  exact ⟨Classical.arbitrary _, fun h => by simp [htriv h]⟩

end IsAlgClosed

end PGL2

theorem solvable_projective_p_generated_fixed_point
    (p : ℕ) [Fact p.Prime] (hpodd : Odd p)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K p]
    (H : Subgroup (PGL2 K)) [Finite H] [Group.IsSolvable H]
    (hgen : Subgroup.closure {h : H | IsPElement p h} = ⊤)
    (hrange : 5 ≤ p ∨ Odd (Nat.card H)) :
    ∃ x : ProjectiveLine K, ∀ h : H, (h : PGL2 K) • x = x := by
  cases subsingleton_or_nontrivial H with
  | inl _ => exact ⟨Classical.arbitrary _, fun h => by simp [Subsingleton.elim h 1]⟩
  | inr _ =>
    obtain ⟨r, hr, R, _, hR, _⟩ := exists_normal_isElementaryAbelian H
    have : Fact r.Prime := ⟨hr⟩
    exact exists_fixed_of_normal_isElementaryAbelian p hpodd H hgen hrange (r := r) R hR

end CFSG
