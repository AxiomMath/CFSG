module

public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.Complement
public import CFSG.FeitThompson.Local.ElementaryAbelianCubeInvariantPlane
public import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank
public import CFSG.FeitThompson.Foundations.HallContainsNormalPrimeSupport
import CFSG.FeitThompson.Local.FixedOrderElementaryAbelianCover
import CFSG.FeitThompson.Representations.OddLinearGroupsDimTwoPrimeField
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Local.ControlledNormalElementaryPlane
import CFSG.FeitThompson.OddOrder.ScalarFreePlaneGroupOrderDividesPPlusOne
import CFSG.FeitThompson.OddOrder.ControlledPrimeLineExcludesScalars
import CFSG.FeitThompson.OddOrder.ControlledWitnessCentralTorsion
import CFSG.FeitThompson.Foundations.SolvableHallExistence
public import Mathlib.FieldTheory.Finite.Basic

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Module Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Linear

variable {p : ℕ} {W : Type*} [AddCommGroup W] [Module (ZMod p) W] {X : Type*} [Group X]

theorem isCyclic_and_natCard_dvd_sub_one_of_invariant_line (hp : p.Prime) [Finite X]
    (ρ : X →* (W ≃ₗ[ZMod p] W)) {u : W} (hu : u ≠ 0)
    (hinv : ∀ e : X, ρ e u ∈ Submodule.span (ZMod p) {u})
    (hfree : ∀ e : X, ρ e u = u → e = 1) :
    IsCyclic X ∧ Nat.card X ∣ p - 1 := by
  have hfp : Fact p.Prime := ⟨hp⟩
  have hcancel : ∀ a b : ZMod p, a • u = b • u → a = b := by
    intro a b h
    have h0 : (a - b) • u = 0 := by rw [sub_smul, h, sub_self]
    rcases smul_eq_zero.1 h0 with h1 | h1
    · exact sub_eq_zero.1 h1
    · exact absurd h1 hu
  choose c hc using fun e => Submodule.mem_span_singleton.1 (hinv e)
  have hne : ∀ e : X, c e ≠ 0 := by
    intro e h0
    have h := hc e
    rw [h0, zero_smul] at h
    exact hu ((ρ e).injective (h.symm.trans (map_zero (ρ e)).symm))
  have hone : c 1 = 1 := hcancel _ _ (by rw [hc 1, one_smul, map_one]; rfl)
  have hmul : ∀ e e' : X, c (e * e') = c e * c e' := by
    intro e e'
    refine hcancel _ _ ?_
    rw [hc (e * e'), map_mul]
    change (ρ e) ((ρ e') u) = _
    rw [← hc e', map_smul, ← hc e, smul_smul, mul_comm]
  let f : X →* (ZMod p)ˣ :=
    { toFun := fun e => Units.mk0 (c e) (hne e)
      map_one' := Units.ext (by simpa using hone)
      map_mul' := fun e e' => Units.ext (by simpa using hmul e e') }
  have hinj : Function.Injective f := by
    refine (injective_iff_map_eq_one f).2 fun e he => hfree e ?_
    have h1 : c e = 1 := by simpa [f, Units.ext_iff] using he
    rw [← hc e, h1, one_smul]
  have : IsCyclic (ZMod p)ˣ := isCyclic_units_of_finite_field (ZMod p)
  refine ⟨isCyclic_of_injective f hinj, ?_⟩
  have h1 : Nat.card X = Nat.card f.range := Nat.card_congr (Equiv.ofInjective _ hinj)
  have h2 : Nat.card ((ZMod p)ˣ) = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  rw [h1, ← h2]
  exact Subgroup.card_subgroup_dvd_card _

theorem isCyclic_and_natCard_dvd_add_one_of_irreducible_plane [Fact p.Prime] [Finite X]
    (hW : finrank (ZMod p) W = 2) (ρ : X →* (W ≃ₗ[ZMod p] W)) (hinj : Function.Injective ρ)
    (hodd : Odd (Nat.card X)) (hnd : ¬ p ∣ Nat.card X)
    (hirr : ∀ U : Submodule (ZMod p) W, (∀ y : X, ∀ w ∈ U, ρ y w ∈ U) → U = ⊥ ∨ U = ⊤)
    (hscal : ∀ y : X, (∃ c : ZMod p, ∀ w : W, ρ y w = c • w) → y = 1) :
    IsCyclic X ∧ Nat.card X ∣ p + 1 := by
  have hfd : FiniteDimensional (ZMod p) W := FiniteDimensional.of_finrank_pos (by omega)
  have hnt : Nontrivial W := Module.nontrivial_of_finrank_pos (R := ZMod p) (by omega)
  set A : Subgroup (W ≃ₗ[ZMod p] W) := ρ.range with hA
  have hXA : X ≃* A := MonoidHom.ofInjective hinj
  have hcard : Nat.card A = Nat.card X := (Nat.card_congr hXA.toEquiv).symm
  let hbasis : Basis (Fin 2) (ZMod p) W := Module.finBasisOfFinrankEq (ZMod p) W hW
  let hE₀ : GL (Fin 2) (ZMod p) ≃* (W ≃ₗ[ZMod p] W) :=
    (Matrix.GeneralLinearGroup.toLin' hbasis).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _)
  have hXcomm : IsMulCommutative X := by
    let σ : X →* GL (Fin 2) (ZMod p) := hE₀.symm.toMonoidHom.comp ρ
    have hσinj : Function.Injective σ := hE₀.symm.injective.comp hinj
    have hXσ : X ≃* σ.range := MonoidHom.ofInjective hσinj
    have hcard' : Nat.card σ.range = Nat.card X := (Nat.card_congr hXσ.toEquiv).symm
    have : IsMulCommutative σ.range :=
      isMulCommutative_of_odd_of_not_dvd_prime_field Fact.out (by rw [hcard']; exact hodd)
        (by rw [hcard']; exact hnd)
    exact isMulCommutative_of_mulEquiv hXσ
  have hAcomm : IsMulCommutative A := isMulCommutative_of_mulEquiv hXA.symm
  have hAirr : (linearGroupRep A).IsIrreducible :=
    isIrreducible_linearGroupRep_iff.2 ⟨hnt, fun U hU => hirr U
      fun y w hw => hU (ρ y) ⟨y, rfl⟩ w hw⟩
  have hAscal : A ⊓ scalarSubgroup (ZMod p) W = ⊥ := by
    refine inf_scalarSubgroup_eq_bot_iff.2 ?_
    rintro a ⟨y, rfl⟩ ⟨c, hc⟩
    have hy : y = 1 := hscal y ⟨(c : ZMod p), hc⟩
    rw [hy, map_one]
  obtain ⟨hAcyc, hdvd⟩ := isCyclic_and_natCard_dvd_add_one_zmod (A := A) hW hAscal
  exact ⟨isCyclic_of_injective hXA.toMonoidHom hXA.injective, by rwa [hcard] at hdvd⟩

end Linear

variable {G : Type*} [Group G] [Finite G] {p k : ℕ} {M L H E P T : Subgroup G} {x : G}

theorem mem_of_natCard_eq_sq (hp : p.Prime) [IsMulCommutative P]
    (hPcard : Nat.card P = p ^ k) (hrank : elementaryAbelianPRank p P = 2)
    (hTP : T ≤ P) (hTexp : ∀ t ∈ T, t ^ p = 1) (hTcard : Nat.card T = p ^ 2)
    (hxP : x ∈ P) (hxp : x ^ p = 1) : x ∈ T := by
  set Ω := omega1Subgroup p P with hΩ
  have hΩP : Ω ≤ P := omega1Subgroup_le_self P
  have hΩmem : ∀ y : G, y ∈ Ω ↔ y ∈ P ∧ y ^ p = 1 := fun y =>
    mem_omega1Subgroup_iff_of_isMulCommutative (p := p) ‹IsMulCommutative P›
  have hΩcomm : IsMulCommutative Ω := isMulCommutative_of_le hΩP
  have hΩexp : ∀ y ∈ Ω, y ^ p = 1 := fun y hy => ((hΩmem y).1 hy).2
  obtain ⟨d, hd⟩ : ∃ d, Nat.card Ω = p ^ d := by
    have hdvd : Nat.card Ω ∣ p ^ k := hPcard ▸ Subgroup.card_dvd_of_le hΩP
    exact ((Nat.dvd_prime_pow hp).1 hdvd).imp fun d hd => hd.2
  have hrΩ : elementaryAbelianPRank p Ω = d := elementaryAbelianPRank_eq_of_card_eq hp hΩexp hd
  have hdle : d ≤ 2 := by
    rw [← hrΩ, ← hrank]; exact elementaryAbelianPRank_le_of_le hp.one_lt hΩP
  have hTΩ : T ≤ Ω := fun t ht => (hΩmem t).2 ⟨hTP ht, hTexp t ht⟩
  have hdge : 2 ≤ d := by
    have h := Subgroup.card_dvd_of_le hTΩ
    rw [hTcard, hd] at h
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 h
  have hTΩeq : T = Ω := Subgroup.eq_of_le_of_card_ge hTΩ (by rw [hTcard, hd, show d = 2 by omega])
  exact hTΩeq ▸ (hΩmem x).2 ⟨hxP, hxp⟩

theorem two_mul_le_add_one_of_dvd (hEodd : Odd (Nat.card E)) (hpodd : Odd p) (hp : p.Prime)
    (h : Nat.card E ∣ p - 1 ∨ Nat.card E ∣ p + 1) : 2 * Nat.card E ≤ p + 1 := by
  have hEpos : 0 < Nat.card E := Nat.card_pos
  obtain ⟨t, ht⟩ := hEodd
  obtain ⟨s, hs⟩ := hpodd
  have hp2 : 2 ≤ p := hp.two_le
  obtain ⟨j, hj⟩ | ⟨j, hj⟩ := h
  · have h2j : 2 ≤ j := by
      rcases Nat.lt_or_ge j 2 with hlt | hge
      · interval_cases j <;> omega
      · exact hge
    calc 2 * Nat.card E ≤ j * Nat.card E := Nat.mul_le_mul_right _ h2j
      _ = p - 1 := by rw [hj]; ring
      _ ≤ p + 1 := by omega
  · have h2j : 2 ≤ j := by
      rcases Nat.lt_or_ge j 2 with hlt | hge
      · interval_cases j <;> omega
      · exact hge
    calc 2 * Nat.card E ≤ j * Nat.card E := Nat.mul_le_mul_right _ h2j
      _ = p + 1 := by rw [hj]; ring

theorem isCyclic_and_natCard_dvd_sub_one_or_add_one (hGodd : Odd (Nat.card G)) (hp : p.Prime)
    (hHnil : Group.IsNilpotent H) (hHL : H ≤ L) (hHnorm : (H.subgroupOf L).Normal)
    (hHcop : (Nat.card H).Coprime (H.subgroupOf L).index)
    (hEL : E ≤ L) (hcompl : (H.subgroupOf L).IsComplement' (E.subgroupOf L))
    (hfixfree : ∀ y ∈ E, y ≠ 1 → H ⊓ centralizer {y} = ⊥) (hML : M ⊓ L ≤ H)
    [IsMulCommutative P] (hPM : P ≤ M)
    (hPcard : Nat.card P = p ^ (Nat.card M).factorization p) (hPH : P ≤ H)
    (hrank : elementaryAbelianPRank p P = 2)
    (hxP : x ∈ P) (hxord : orderOf x = p)
    (hNx : normalizer ((zpowers x : Subgroup G) : Set G) ≤ M) :
    IsCyclic E ∧ (Nat.card E ∣ p - 1 ∨ Nat.card E ∣ p + 1) := by
  have hfp : Fact p.Prime := ⟨hp⟩
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hxord
    exact hp.one_lt.ne hxord
  have hxp : x ^ p = 1 := by rw [← hxord]; exact pow_orderOf_eq_one x
  have hpP : p ∣ Nat.card P := by
    have h := orderOf_dvd_natCard (⟨x, hxP⟩ : ↥P)
    rwa [Subgroup.orderOf_mk, hxord] at h
  have hpH : p ∣ Nat.card H := hpP.trans (Subgroup.card_dvd_of_le hPH)
  have hEidx : (H.subgroupOf L).index = Nat.card E := by
    rw [hcompl.symm.index_eq_card, natCard_subgroupOf_of_le hEL]
  have hnd : ¬ p ∣ Nat.card E := by
    intro hpE
    rw [hEidx] at hHcop
    have h := (hHcop.coprime_dvd_left hpH).coprime_dvd_right hpE
    exact hp.ne_one (Nat.Coprime.eq_one_of_dvd h (dvd_refl p))
  have hEodd : Odd (Nat.card E) := hGodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card E)
  obtain ⟨Q, ⟨hQH, hQcard⟩, -⟩ := existsUnique_le_natCard_eq_pow_factorization (p := p) hHnil
  obtain ⟨-, hTne, -, hTP, hTea, hTrank, hTnorm⟩ :=
    controlled_witness_central_torsion (M := M) (L := L) (Q := Q) hHnil hHL hHnorm hPM hPcard hPH
      (by omega) hQH hQcard hxP hx1 hNx
  set T := subgroupCenterTorsionBy Q p with hT
  have hET : E ≤ normalizer ((T : Subgroup G) : Set G) := hTnorm E hEL
  have hTcomm : IsMulCommutative T := hTea.isMulCommutative
  have hTexp : ∀ t ∈ T, t ^ p = 1 := hTea.pow_eq_one
  obtain ⟨m, hTm⟩ : ∃ m, Nat.card T = p ^ m := by
    have hdvd : Nat.card T ∣ Nat.card P := Subgroup.card_dvd_of_le hTP
    rw [hPcard] at hdvd
    exact ((Nat.dvd_prime_pow hp).1 hdvd).imp fun m hm => hm.2
  have hm12 : m = 1 ∨ m = 2 := by
    have h : elementaryAbelianPRank p T = m := elementaryAbelianPRank_eq_of_card_eq hp hTexp hTm
    rwa [h] at hTrank
  let _ : CommGroup ↥T := IsMulCommutative.instCommGroup
  obtain ⟨e₀⟩ := nonempty_mulEquiv_pi_of_exponent (G := ↥T) (d := m) hp
    (fun t => Subtype.ext (hTexp _ t.2)) hTm
  let e : ↥T ≃* Multiplicative (Fin m → ZMod p) :=
    e₀.trans (MulEquiv.piMultiplicative _).symm
  let ρ : ↥E →* ((Fin m → ZMod p) ≃ₗ[ZMod p] (Fin m → ZMod p)) :=
    (mulAutMulEquivLinearEquiv ↥T e).toMonoidHom.comp (conjOnNormalized T hET)
  let f : Multiplicative (Fin m → ZMod p) →* G := T.subtype.comp e.symm.toMonoidHom
  have hfinj : Function.Injective f := T.subtype_injective.comp e.symm.injective
  have hfmem : ∀ w, f w ∈ T := fun w => (e.symm w).2
  have key : ∀ (y : ↥E) (w : Fin m → ZMod p),
      f (Multiplicative.ofAdd (ρ y w)) = (y : G) * f (Multiplicative.ofAdd w) * (y : G)⁻¹ := by
    intro y w
    change ((e.symm (Multiplicative.ofAdd (ρ y w)) : ↥T) : G) = _
    have h1 : ρ y w = Multiplicative.toAdd
        (e (conjOnNormalized T hET y (e.symm (Multiplicative.ofAdd w)))) := by
      simp [ρ]
    rw [h1, ofAdd_toAdd, MulEquiv.symm_apply_apply]
    exact conjOnNormalized_apply_coe hET y _
  have hfrank : finrank (ZMod p) (Fin m → ZMod p) = m := by simp
  have hfixed : ∀ y : ↥E, y ≠ 1 → ∀ w : Fin m → ZMod p, ρ y w = w → w = 0 := by
    intro y hy w hw
    have hy1 : (y : G) ≠ 1 := fun h => hy (Subtype.ext h)
    have h := key y w
    rw [hw] at h
    have hcomm : (y : G) * f (Multiplicative.ofAdd w) = f (Multiplicative.ofAdd w) * (y : G) :=
      mul_inv_eq_iff_eq_mul.1 h.symm
    have hmem : f (Multiplicative.ofAdd w) ∈ H ⊓ centralizer ({(y : G)} : Set G) :=
      mem_inf.2 ⟨hPH (hTP (hfmem _)), mem_centralizer_iff.2 fun g hg => by
        rw [Set.mem_singleton_iff] at hg; rw [hg]; exact hcomm⟩
    rw [hfixfree (y : G) y.2 hy1, mem_bot] at hmem
    have h2 : Multiplicative.ofAdd w = 1 := hfinj (by rw [hmem, map_one])
    simpa using h2
  by_cases hline : ∃ u : Fin m → ZMod p, u ≠ 0 ∧
      ∀ y : ↥E, ρ y u ∈ Submodule.span (ZMod p) {u}
  ·
    obtain ⟨u, hu, hinv⟩ := hline
    obtain ⟨hcyc, hdvd⟩ :=
      isCyclic_and_natCard_dvd_sub_one_of_invariant_line hp ρ hu hinv
        (fun y hy => by
          by_contra hy1
          exact hu (hfixed y hy1 u hy))
    exact ⟨hcyc, Or.inl hdvd⟩
  ·
    have hm2 : m = 2 := by
      rcases hm12 with h | h
      · exfalso
        have hr1 : finrank (ZMod p) (Fin m → ZMod p) = 1 := by rw [hfrank, h]
        have hnt : Nontrivial (Fin m → ZMod p) :=
          Module.nontrivial_of_finrank_pos (R := ZMod p) (by omega)
        obtain ⟨u, hu⟩ := exists_ne (0 : Fin m → ZMod p)
        refine hline ⟨u, hu, fun y => ?_⟩
        have htop : Submodule.span (ZMod p) {u} = ⊤ :=
          Submodule.eq_top_of_finrank_eq (by rw [finrank_span_singleton hu, hr1])
        rw [htop]
        exact Submodule.mem_top
      · exact h
    have hr2 : finrank (ZMod p) (Fin m → ZMod p) = 2 := by rw [hfrank, hm2]
    have hntW : Nontrivial (Fin m → ZMod p) :=
      Module.nontrivial_of_finrank_pos (R := ZMod p) (by omega)
    have hρinj : Function.Injective ρ := by
      refine (injective_iff_map_eq_one ρ).2 fun y hy => ?_
      by_contra hy1
      obtain ⟨u, hu⟩ := exists_ne (0 : Fin m → ZMod p)
      exact hu (hfixed y hy1 u (by rw [hy]; rfl))
    have hirr : ∀ U : Submodule (ZMod p) (Fin m → ZMod p),
        (∀ y : ↥E, ∀ w ∈ U, ρ y w ∈ U) → U = ⊥ ∨ U = ⊤ := by
      intro U hU
      by_cases hU0 : U = ⊥
      · exact Or.inl hU0
      refine Or.inr ?_
      obtain ⟨u, huU, hu⟩ := (Submodule.ne_bot_iff U).1 hU0
      have hspan : Submodule.span (ZMod p) {u} ≤ U := by
        rw [Submodule.span_le, Set.singleton_subset_iff]; exact huU
      have hUle : finrank (ZMod p) U ≤ finrank (ZMod p) (Fin m → ZMod p) := Submodule.finrank_le U
      have h1 : 1 ≤ finrank (ZMod p) U := by
        have h := Submodule.finrank_mono hspan
        rwa [finrank_span_singleton hu] at h
      rcases Nat.lt_or_ge (finrank (ZMod p) U) 2 with hlt | hge
      · exfalso
        have heq : Submodule.span (ZMod p) {u} = U :=
          Submodule.eq_of_le_of_finrank_le hspan (by rw [finrank_span_singleton hu]; omega)
        exact hline ⟨u, hu, fun y => heq ▸ hU y u huU⟩
      · exact Submodule.eq_top_of_finrank_eq (by omega)
    have hTcard : Nat.card T = p ^ 2 := by rw [hTm, hm2]
    have hxT : x ∈ T := mem_of_natCard_eq_sq hp hPcard hrank hTP hTexp hTcard hxP hxp
    set u₀ : Fin m → ZMod p := Multiplicative.toAdd (e ⟨x, hxT⟩) with hu₀
    have hfu₀ : f (Multiplicative.ofAdd u₀) = x := by
      change ((e.symm (Multiplicative.ofAdd u₀) : ↥T) : G) = x
      rw [hu₀, ofAdd_toAdd, MulEquiv.symm_apply_apply]
    have hscal : ∀ y : ↥E, (∃ c : ZMod p, ∀ w : Fin m → ZMod p, ρ y w = c • w) → y = 1 := by
      intro y hy
      obtain ⟨c, hc⟩ := hy
      by_contra hy1
      have hy1' : ((y : G))⁻¹ ≠ 1 := by simpa using fun h => hy1 (Subtype.ext h)
      refine not_exists_smul_eq_conj hp (H := H) (E := E) (L := L) (M := M) f hEL hcompl hML
        (y := u₀) (by rw [hfu₀]; exact hx1) (by rw [hfu₀]; exact hNx)
        (inv_mem y.2) hy1' ⟨c, fun w => ?_⟩
      have h := key y w
      rw [hc w] at h
      rw [inv_inv]
      exact h.symm
    obtain ⟨hcyc, hdvd⟩ :=
      isCyclic_and_natCard_dvd_add_one_of_irreducible_plane hr2 ρ hρinj hEodd hnd hirr hscal
    exact ⟨hcyc, Or.inr hdvd⟩

theorem isCyclic_and_natCard_dvd_sub_one_or_add_one_of_isHallSubgroup {π : Set ℕ}
    (hGodd : Odd (Nat.card G)) (hp : p.Prime)
    (hHnil : Group.IsNilpotent H) (hHL : H ≤ L) (hHnorm : (H.subgroupOf L).Normal)
    (hHall : IsHallSubgroup π (H.subgroupOf L))
    (hEL : E ≤ L) (hcompl : (H.subgroupOf L).IsComplement' (E.subgroupOf L))
    (hfixfree : ∀ y ∈ E, y ≠ 1 → H ⊓ centralizer {y} = ⊥) (hML : M ⊓ L ≤ H)
    [IsMulCommutative P] (hPM : P ≤ M)
    (hPcard : Nat.card P = p ^ (Nat.card M).factorization p) (hPH : P ≤ H)
    (hrank : elementaryAbelianPRank p P = 2)
    (hxP : x ∈ P) (hxord : orderOf x = p)
    (hNx : normalizer ((zpowers x : Subgroup G) : Set G) ≤ M) :
    IsCyclic E ∧ (Nat.card E ∣ p - 1 ∨ Nat.card E ∣ p + 1) := by
  have hcop : (Nat.card H).Coprime (H.subgroupOf L).index := by
    have h := hHall.coprime_natCard_index
    rwa [natCard_subgroupOf_of_le hHL] at h
  exact isCyclic_and_natCard_dvd_sub_one_or_add_one hGodd hp hHnil hHL hHnorm hcop hEL hcompl
    hfixfree hML hPM hPcard hPH hrank hxP hxord hNx

theorem frobenius_complement_isCyclic_and_two_mul_natCard_le {π : Set ℕ}
    (hGodd : Odd (Nat.card G)) (hp : p.Prime)
    (hHnil : Group.IsNilpotent H) (hHL : H ≤ L) (hHnorm : (H.subgroupOf L).Normal)
    (hHall : IsHallSubgroup π (H.subgroupOf L))
    (hEL : E ≤ L) (hcompl : (H.subgroupOf L).IsComplement' (E.subgroupOf L))
    (hfixfree : ∀ y ∈ E, y ≠ 1 → H ⊓ centralizer {y} = ⊥) (hML : M ⊓ L ≤ H)
    [IsMulCommutative P] (hPM : P ≤ M)
    (hPcard : Nat.card P = p ^ (Nat.card M).factorization p) (hPH : P ≤ H)
    (hrank : elementaryAbelianPRank p P = 2)
    (hxP : x ∈ P) (hxord : orderOf x = p)
    (hNx : normalizer ((zpowers x : Subgroup G) : Set G) ≤ M) :
    IsCyclic E ∧ (Nat.card E ∣ p - 1 ∨ Nat.card E ∣ p + 1) ∧ 2 * Nat.card E ≤ p + 1 := by
  obtain ⟨hcyc, hdvd⟩ := isCyclic_and_natCard_dvd_sub_one_or_add_one_of_isHallSubgroup hGodd hp
    hHnil hHL hHnorm hHall hEL hcompl hfixfree hML hPM hPcard hPH hrank hxP hxord hNx
  have hEodd : Odd (Nat.card E) := hGodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card E)
  have hpodd : Odd p := by
    have hpP : p ∣ Nat.card P := by
      have h := orderOf_dvd_natCard (⟨x, hxP⟩ : ↥P)
      rwa [Subgroup.orderOf_mk, hxord] at h
    have hpG : p ∣ Nat.card G := hpP.trans (Subgroup.card_subgroup_dvd_card P)
    rcases hp.eq_two_or_odd' with rfl | h
    · exact absurd hpG (by simpa [Nat.two_dvd_ne_zero, Nat.odd_iff] using hGodd)
    · exact h
  exact ⟨hcyc, hdvd, two_mul_le_add_one_of_dvd hEodd hpodd hp hdvd⟩

end

end CFSG.FeitThompson
