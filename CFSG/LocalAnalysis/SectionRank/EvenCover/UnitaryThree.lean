module

public import CFSG.LocalAnalysis.SectionRank.EvenCover.Unitary
public import CFSG.LocalAnalysis.SectionRank.OddCover.CoverTools
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralSylowTransfer
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import CFSG.GroupTheory.LocalCores.Fitting

public section

namespace CFSG.SectionRank.EvenCover

open scoped commutatorElement

section FaithfulLift

variable {E S : Type*} [Group E] [Finite E] [Group S] [Finite S]

theorem sylow_kernel_eq_bot_of_inf_ker_eq_bot [Group.IsPerfect E] (π : E →* S)
    (hC : π.ker ≤ Subgroup.center E) {r : ℕ} [hr : Fact r.Prime] (Q : Subgroup E)
    (hQ : Q ⊓ π.ker = ⊥) (hcard : (Nat.card S).factorization r ≤ (Nat.card Q).factorization r)
    (Cp : Sylow r π.ker) : (Cp : Subgroup π.ker) = ⊥ := by
  obtain ⟨R⟩ := (inferInstance : Nonempty (Sylow r Q))
  set R' : Subgroup E := (R : Subgroup Q).map Q.subtype with hR'
  have hR'Q : R' ≤ Q := Subgroup.map_subtype_le _
  have hinj : ∀ x ∈ R', ∀ y ∈ R', π x = π y → x = y := by
    intro x hx y hy hxy
    have h1 : x * y⁻¹ ∈ Q ⊓ π.ker :=
      Subgroup.mem_inf.2 ⟨Q.mul_mem (hR'Q hx) (Q.inv_mem (hR'Q hy)),
        MonoidHom.mem_ker.2 (by rw [map_mul, map_inv, hxy, mul_inv_cancel])⟩
    rw [hQ, Subgroup.mem_bot] at h1
    exact mul_inv_eq_one.1 h1
  have hR'p : IsPGroup r R' := R.isPGroup'.map Q.subtype
  have hcardR' : Nat.card R' = r ^ (Nat.card Q).factorization r := by
    rw [hR', Subgroup.card_map_of_injective Q.subtype_injective, Sylow.card_eq_multiplicity]
  have hcardπR' : Nat.card (R'.map π) = Nat.card R' := by
    have hi : Function.Injective (π.comp R'.subtype) := fun a b h =>
      Subtype.ext (hinj a a.2 b b.2 h)
    have hr : R'.map π = (π.comp R'.subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hr, ← Nat.card_congr (MonoidHom.ofInjective hi).toEquiv]
  obtain ⟨P, hRP⟩ := hR'p.exists_le_sylow
  have hπP : (P : Subgroup E).map π = R'.map π := by
    have hle : R'.map π ≤ (P : Subgroup E).map π := Subgroup.map_mono hRP
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    obtain ⟨T, hT⟩ := (P.isPGroup'.map π).exists_le_sylow
    calc Nat.card ((P : Subgroup E).map π) ≤ Nat.card (T : Subgroup S) :=
          Subgroup.card_le_of_le hT
      _ = r ^ (Nat.card S).factorization r := Sylow.card_eq_multiplicity T
      _ ≤ r ^ (Nat.card Q).factorization r := Nat.pow_le_pow_right hr.out.pos hcard
      _ = Nat.card (R'.map π) := by rw [hcardπR', hcardR']
  have hdecomp : ∀ g ∈ (P : Subgroup E), ∃ c ∈ Subgroup.center E, ∃ x ∈ R', g = c * x := by
    intro g hg
    have : π g ∈ R'.map π := hπP ▸ Subgroup.mem_map_of_mem π hg
    obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.1 this
    refine ⟨g * x⁻¹, hC ?_, x, hx, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxg, mul_inv_cancel]
  have hcomm : ∀ a ∈ commutator (P : Subgroup E), (a : E) ∈ R' := by
    intro a ha
    have hle : commutator (P : Subgroup E) ≤ R'.subgroupOf P := by
      rw [_root_.commutator_def]
      refine Subgroup.commutator_le.2 fun g₁ _ g₂ _ => ?_
      obtain ⟨c₁, hc₁, x₁, hx₁, h₁⟩ := hdecomp g₁ g₁.2
      obtain ⟨c₂, hc₂, x₂, hx₂, h₂⟩ := hdecomp g₂ g₂.2
      rw [Subgroup.mem_subgroupOf]
      change ⁅(g₁ : E), (g₂ : E)⁆ ∈ R'
      rw [h₁, h₂, CFSG.LieType.Steinberg.commutatorElement_mul_mul_of_mem_center hc₁ hc₂]
      rw [commutatorElement_def]
      exact R'.mul_mem (R'.mul_mem (R'.mul_mem hx₁ hx₂) (R'.inv_mem hx₁)) (R'.inv_mem hx₂)
    exact hle ha
  rw [eq_bot_iff]
  intro c hc
  have hcZ : (c : E) ∈ Subgroup.center E := hC c.2
  have hcP : (c : E) ∈ (P : Subgroup E) :=
    CFSG.ShultStronglyClosedTI.central_pSubgroup_le_sylow P
      ((Cp : Subgroup π.ker).map π.ker.subtype) ((Subgroup.map_subtype_le _).trans hC)
      (Cp.isPGroup'.map π.ker.subtype) (Subgroup.mem_map.2 ⟨c, hc, rfl⟩)
  have h1 := hcomm _ (CFSG.ShultStronglyClosedTI.central_element_mem_sylow_derived P
    ⟨(c : E), hcP⟩ hcZ)
  have h2 : (c : E) = 1 := hinj _ h1 1 R'.one_mem (by rw [map_one]; exact c.2)
  exact Subgroup.mem_bot.2 (Subtype.ext h2)

end FaithfulLift

theorem isCyclic_of_isPGroup_GL_three {k : Type} [Field k] [Fintype k] {p : ℕ} [Fact p.Prime]
    [CharP k p] {r : ℕ} [hr : Fact r.Prime] (h0 : ¬ r ∣ Fintype.card k)
    (h1 : ¬ r ∣ Fintype.card k - 1) (h2 : ¬ r ∣ Fintype.card k ^ 2 - 1)
    (P : Subgroup (GL (Fin 3) k)) (hP : IsPGroup r P) : IsCyclic P := by
  classical
  set q := Fintype.card k with hq
  have hq1 : 1 ≤ q := Fintype.card_pos
  let L := FiniteField.Extension k p 3
  have : Fintype L := Fintype.ofFinite L
  let b : Module.Basis (Fin 3) k L :=
    Module.finBasisOfFinrankEq k L (FiniteField.finrank_extension k p 3)
  let ψ : Lˣ →* GL (Fin 3) k := Units.map (Algebra.leftMulMatrix b).toMonoidHom
  have hψ : Function.Injective ψ := fun x y h => Units.ext
    (Algebra.leftMulMatrix_injective b (congrArg Units.val h))
  set S := ψ.range with hSdef
  have hScyc : IsCyclic S := isCyclic_of_surjective (MonoidHom.ofInjective hψ).toMonoidHom
    (MonoidHom.ofInjective hψ).surjective
  have hcardL : Fintype.card L = q ^ 3 := by
    rw [Module.card_eq_pow_finrank (K := k), FiniteField.finrank_extension k p 3]
  have hcardS : Nat.card S = q ^ 3 - 1 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv, Nat.card_units,
      Nat.card_eq_fintype_card, hcardL]
  have hGL : Nat.card (GL (Fin 3) k) = (q ^ 3 - 1) * ((q ^ 3 - q) * (q ^ 3 - q ^ 2)) := by
    rw [Matrix.card_GL_field, Fin.prod_univ_three]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
    ring
  have hfac : ∀ i, i ≤ 2 → q ^ 3 - q ^ i = q ^ i * (q ^ (3 - i) - 1) := by
    intro i hi
    rw [Nat.mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' (by omega)]
  have hcopM : Nat.Coprime r ((q ^ 3 - q) * (q ^ 3 - q ^ 2)) := by
    have hcq : ∀ i, Nat.Coprime r (q ^ i) := fun i =>
      Nat.Coprime.pow_right i ((Nat.Prime.coprime_iff_not_dvd hr.out).2 h0)
    rw [show q ^ 3 - q = q ^ 3 - q ^ 1 by rw [pow_one], hfac 1 (by norm_num),
      hfac 2 (by norm_num)]
    refine Nat.Coprime.mul_right ?_ ?_
    · exact Nat.Coprime.mul_right (hcq 1) ((Nat.Prime.coprime_iff_not_dvd hr.out).2 h2)
    · refine Nat.Coprime.mul_right (hcq 2) ?_
      rw [show 3 - 2 = 1 by rfl, pow_one]
      exact (Nat.Prime.coprime_iff_not_dvd hr.out).2 h1
  obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow r S))
  set T' : Subgroup (GL (Fin 3) k) := (T : Subgroup S).map S.subtype with hT'
  have hT'p : IsPGroup r T' := T.isPGroup'.map S.subtype
  obtain ⟨R₀, hR₀⟩ := hT'p.exists_le_sylow
  have hq3 : q ^ 3 - 1 ≠ 0 := by
    have : 2 ≤ q := Fintype.one_lt_card
    have : 2 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left this 3
    omega
  have hR₀eq : (R₀ : Subgroup (GL (Fin 3) k)) = T' := by
    refine (Subgroup.eq_of_le_of_card_ge hR₀ ?_).symm
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 R₀.isPGroup'
    have hdvd : r ^ j ∣ q ^ 3 - 1 := by
      have h := hj ▸ Subgroup.card_subgroup_dvd_card (R₀ : Subgroup (GL (Fin 3) k))
      rw [hGL] at h
      exact (Nat.Coprime.pow_left j hcopM).dvd_of_dvd_mul_right h
    have hTcard : Nat.card (T : Subgroup S) = r ^ (Nat.card S).factorization r :=
      Sylow.card_eq_multiplicity T
    rw [hT', Subgroup.card_map_of_injective S.subtype_injective, hTcard, hcardS, hj]
    exact Nat.pow_le_pow_right hr.out.pos
      ((Nat.Prime.pow_dvd_iff_le_factorization hr.out hq3).1 hdvd)
  have hR₀cyc : IsCyclic (R₀ : Subgroup (GL (Fin 3) k)) := by
    rw [hR₀eq, hT']
    have : IsCyclic (T : Subgroup S) := Subgroup.isCyclic_of_le le_top
    exact isCyclic_of_surjective
      ((T : Subgroup S).equivMapOfInjective S.subtype S.subtype_injective).toMonoidHom
      ((T : Subgroup S).equivMapOfInjective S.subtype S.subtype_injective).surjective
  obtain ⟨R, hPR⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (GL (Fin 3) k) R₀ R
  have hRcyc : IsCyclic (R : Subgroup (GL (Fin 3) k)) := by
    rw [← hg]
    exact isCyclic_of_surjective (R₀.equivSMul g).toMonoidHom (R₀.equivSMul g).surjective
  exact Subgroup.isCyclic_of_le hPR

section TorusLift

open CFSG.SectionRank.OddCover

variable {E G M : Type*} [Group E] [Group G] [CommGroup M]

theorem torus_lift_relations [IsCyclic M] (φ : E →* G) [Finite φ.ker]
    (hC : φ.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card φ.ker)) (x : M →* E) {u w : E}
    (hw3 : w ^ 3 = 1) (huw : u * w * u⁻¹ = w⁻¹) (hux : ∀ a, u * x a * u⁻¹ = (x a)⁻¹)
    (hcomm : ∀ a b, Commute (φ (w * x a * w⁻¹)) (φ (w⁻¹ * x b * w)))
    (hprod : ∀ a, φ (x a * (w * x a * w⁻¹) * (w⁻¹ * x a * w)) = 1) :
    (∀ a b, Commute (x a) (w * x b * w⁻¹)) ∧
      ∀ a, x a * (w * x a * w⁻¹) * (w⁻¹ * x a * w) = 1 := by
  have hw3' : w * w * w = 1 := by rw [← pow_three']; exact hw3
  have hw2' : w * w = w⁻¹ := by
    calc w * w = w * w * w * w⁻¹ := by group
      _ = w⁻¹ := by rw [hw3', one_mul]
  have hw2 : w⁻¹ * w⁻¹ = w := by
    calc w⁻¹ * w⁻¹ = (w * w)⁻¹ := by group
      _ = w := by rw [hw2', inv_inv]
  have huwi : u * w⁻¹ * u⁻¹ = w := by
    rw [show u * w⁻¹ * u⁻¹ = (u * w * u⁻¹)⁻¹ by group, huw, inv_inv]
  have I1 : ∀ e : E, w⁻¹ * (w * e * w⁻¹) * w = e := fun e => by group
  have I2 : ∀ e : E, w⁻¹ * (w⁻¹ * e * w) * w = w * e * w⁻¹ := fun e => by
    rw [show w⁻¹ * (w⁻¹ * e * w) * w = (w⁻¹ * w⁻¹) * e * (w * w) by group, hw2, hw2']
  have I3 : ∀ e : E, w * (w * e * w⁻¹) * w⁻¹ = w⁻¹ * e * w := fun e => by
    rw [show w * (w * e * w⁻¹) * w⁻¹ = (w * w) * e * (w⁻¹ * w⁻¹) by group, hw2, hw2']
  have I4 : ∀ e : E, w * (w⁻¹ * e * w) * w⁻¹ = e := fun e => by group
  have huy : ∀ a, u * (w * x a * w⁻¹) * u⁻¹ = (w⁻¹ * x a * w)⁻¹ := fun a => by
    calc u * (w * x a * w⁻¹) * u⁻¹
        = (u * w * u⁻¹) * (u * x a * u⁻¹) * (u * w⁻¹ * u⁻¹) := by group
      _ = (w⁻¹ * x a * w)⁻¹ := by rw [huw, hux, huwi]; group
  have huz : ∀ a, u * (w⁻¹ * x a * w) * u⁻¹ = (w * x a * w⁻¹)⁻¹ := fun a => by
    calc u * (w⁻¹ * x a * w) * u⁻¹
        = (u * w⁻¹ * u⁻¹) * (u * x a * u⁻¹) * (u * w * u⁻¹) := by group
      _ = (w * x a * w⁻¹)⁻¹ := by rw [huw, hux, huwi]; group
  have hconj : ∀ g e e' : E, g * ⁅e, e'⁆ * g⁻¹ = ⁅g * e * g⁻¹, g * e' * g⁻¹⁆ := fun g e e' => by
    rw [commutatorElement_def, commutatorElement_def]; group
  have hyz : ∀ a, ⁅w * x a * w⁻¹, w⁻¹ * x a * w⁆ = 1 := by
    intro a
    set c := ⁅w * x a * w⁻¹, w⁻¹ * x a * w⁆ with hc
    have hck : c ∈ φ.ker := by
      rw [MonoidHom.mem_ker, hc, map_commutatorElement, (hcomm a a).commutator_eq]
    have hcZ := hC hck
    have hc' : ⁅w⁻¹ * x a * w, w * x a * w⁻¹⁆ ∈ Subgroup.center E := by
      rw [← commutatorElement_inv, ← hc]
      exact Subgroup.inv_mem _ hcZ
    have hinv : u * c * u⁻¹ = c⁻¹ := by
      calc u * c * u⁻¹ = ⁅u * (w * x a * w⁻¹) * u⁻¹, u * (w⁻¹ * x a * w) * u⁻¹⁆ := hconj _ _ _
        _ = ⁅(w⁻¹ * x a * w)⁻¹, (w * x a * w⁻¹)⁻¹⁆ := by rw [huy, huz]
        _ = ⁅w⁻¹ * x a * w, w * x a * w⁻¹⁆ := commutatorElement_inv_inv_of_mem_center hc'
        _ = c⁻¹ := by rw [hc, commutatorElement_inv]
    exact eq_one_of_sq_eq_one_of_odd (sq_eq_one_of_conj_eq_inv hcZ hinv)
      (odd_orderOf_of_mem hodd hck)
  have hxy : ∀ a, Commute (x a) (w * x a * w⁻¹) := by
    intro a
    have h := hconj w⁻¹ (w * x a * w⁻¹) (w⁻¹ * x a * w)
    rw [hyz a, inv_inv, mul_one, inv_mul_cancel, I1, I2] at h
    exact commutatorElement_eq_one_iff_commute.1 h.symm
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := M)
  have hall : ∀ a b, Commute (x a) (w * x b * w⁻¹) := by
    intro a b
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg a)
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg b)
    rw [map_zpow, map_zpow, ← conj_zpow]
    exact (hxy g).zpow_zpow i j
  refine ⟨hall, fun a => ?_⟩
  have hconjw : ∀ e e' : E, Commute e e' → Commute (w * e * w⁻¹) (w * e' * w⁻¹) :=
    fun e e' h => h.map (MulAut.conj w).toMonoidHom
  have hyz' : Commute (w * x a * w⁻¹) (w⁻¹ * x a * w) := by
    have := hconjw _ _ (hall a a)
    rwa [I3] at this
  have hzx : Commute (w⁻¹ * x a * w) (x a) := by
    have := hconjw _ _ hyz'
    rwa [I3, I4] at this
  set k := x a * (w * x a * w⁻¹) * (w⁻¹ * x a * w) with hk
  have hkk : k ∈ φ.ker := hprod a
  have hinv : u * k * u⁻¹ = k⁻¹ := by
    calc u * k * u⁻¹ = (u * x a * u⁻¹) * (u * (w * x a * w⁻¹) * u⁻¹) *
          (u * (w⁻¹ * x a * w) * u⁻¹) := by rw [hk]; group
      _ = (x a)⁻¹ * (w⁻¹ * x a * w)⁻¹ * (w * x a * w⁻¹)⁻¹ := by rw [hux, huy, huz]
      _ = (w⁻¹ * x a * w)⁻¹ * (x a)⁻¹ * (w * x a * w⁻¹)⁻¹ := by rw [hzx.inv_inv.eq]
      _ = (w⁻¹ * x a * w)⁻¹ * (w * x a * w⁻¹)⁻¹ * (x a)⁻¹ := by
        rw [mul_assoc, (hall a a).inv_inv.eq, ← mul_assoc]
      _ = k⁻¹ := by simp only [hk, mul_inv_rev, mul_assoc]
  exact eq_one_of_sq_eq_one_of_odd (sq_eq_one_of_conj_eq_inv (hC hkk) hinv)
    (odd_orderOf_of_mem hodd hkk)

theorem exists_monomial_lift [Finite E] [Finite M] (φ : E →* G) (x : M →* E) {w : E}
    (hw3 : w ^ 3 = 1) (hxy : ∀ a b, Commute (x a) (w * x b * w⁻¹))
    (hxyz : ∀ a, x a * (w * x a * w⁻¹) * (w⁻¹ * x a * w) = 1) (T : M × M →* G)
    (hT : Function.Injective T) (hφ : ∀ a b, φ (x a * (w * x (a * b) * w⁻¹)) = T (a, b))
    (hw1 : ∀ k : ℕ, φ w ^ k ∈ T.range → φ w ^ k = 1) (hw0 : φ w ≠ 1) :
    ∃ N : Subgroup E, N ⊓ φ.ker = ⊥ ∧ Nat.card N = 3 * Nat.card (M × M) := by
  have hw3' : w * w * w = 1 := by rw [← pow_three']; exact hw3
  have hw2' : w * w = w⁻¹ := by
    calc w * w = w * w * w * w⁻¹ := by group
      _ = w⁻¹ := by rw [hw3', one_mul]
  have hw2 : w⁻¹ * w⁻¹ = w := by
    calc w⁻¹ * w⁻¹ = (w * w)⁻¹ := by group
      _ = w := by rw [hw2', inv_inv]
  set y : M →* E := (MulAut.conj w).toMonoidHom.comp x with hy
  have hyapp : ∀ a, y a = w * x a * w⁻¹ := fun a => rfl
  have hxy' : ∀ a b, Commute (x a) (y b) := fun a b => by rw [hyapp]; exact hxy a b
  have hz : ∀ a, w⁻¹ * x a * w = (x a * y a)⁻¹ := fun a => by
    rw [eq_inv_iff_mul_eq_one, hyapp, ← mul_assoc]
    rw [mul_assoc, (show (w⁻¹ * x a * w) * (x a * (w * x a * w⁻¹)) =
      (w⁻¹ * x a * w) * (x a * (w * x a * w⁻¹)) from rfl)]
    have h := hxyz a
    have : (x a * (w * x a * w⁻¹)) * (w⁻¹ * x a * w) = 1 := h
    calc (w⁻¹ * x a * w) * (x a * (w * x a * w⁻¹))
        = (x a * (w * x a * w⁻¹))⁻¹ * ((x a * (w * x a * w⁻¹)) * (w⁻¹ * x a * w)) *
            (x a * (w * x a * w⁻¹)) := by group
      _ = 1 := by rw [this, mul_one, inv_mul_cancel]
  let τ : M × M →* E :=
    { toFun := fun p => x p.1 * y (p.1 * p.2)
      map_one' := by simp
      map_mul' := fun p p' => by
        change x (p.1 * p'.1) * y (p.1 * p'.1 * (p.2 * p'.2)) =
          x p.1 * y (p.1 * p.2) * (x p'.1 * y (p'.1 * p'.2))
        rw [show p.1 * p'.1 * (p.2 * p'.2) = (p.1 * p.2) * (p'.1 * p'.2) by
          rw [mul_mul_mul_comm], map_mul, map_mul]
        calc x p.1 * x p'.1 * (y (p.1 * p.2) * y (p'.1 * p'.2))
            = x p.1 * (x p'.1 * y (p.1 * p.2)) * y (p'.1 * p'.2) := by group
          _ = x p.1 * (y (p.1 * p.2) * x p'.1) * y (p'.1 * p'.2) := by
            rw [(hxy' p'.1 (p.1 * p.2)).eq]
          _ = x p.1 * y (p.1 * p.2) * (x p'.1 * y (p'.1 * p'.2)) := by group }
  have hτ : ∀ p, τ p = x p.1 * y (p.1 * p.2) := fun _ => rfl
  have hφτ : φ.comp τ = T := by
    ext p
    rw [MonoidHom.comp_apply, hτ, hyapp]
    exact hφ p.1 p.2
  have hτinj : Function.Injective τ := fun p p' h => hT (by
    rw [← hφτ, MonoidHom.comp_apply, MonoidHom.comp_apply, h])
  have hwτ : ∀ p, w * τ p * w⁻¹ = τ ((p.1 * p.2)⁻¹, p.1) := by
    rintro ⟨a, b⟩
    simp only [hτ]
    have e1 : w * (x a * y (a * b)) * w⁻¹ = y a * (w⁻¹ * x (a * b) * w) := by
      rw [hyapp, hyapp]
      calc w * (x a * (w * x (a * b) * w⁻¹)) * w⁻¹
          = (w * x a * w⁻¹) * ((w * w) * x (a * b) * (w⁻¹ * w⁻¹)) := by group
        _ = (w * x a * w⁻¹) * (w⁻¹ * x (a * b) * w) := by rw [hw2', hw2]
    rw [e1, hz]
    calc y a * (x (a * b) * y (a * b))⁻¹ = y a * (y (a * b))⁻¹ * (x (a * b))⁻¹ := by group
      _ = y (a * (a * b)⁻¹) * x ((a * b)⁻¹) := by rw [← map_inv, ← map_inv, ← map_mul]
      _ = x ((a * b)⁻¹) * y (a * (a * b)⁻¹) := (hxy' _ _).symm.eq
      _ = x ((a * b)⁻¹) * y ((a * b)⁻¹ * a) := by rw [mul_comm a (a * b)⁻¹]
  have hfwd : ∀ g ∈ τ.range, w * g * w⁻¹ ∈ τ.range := by
    rintro _ ⟨p, rfl⟩
    exact ⟨_, (hwτ p).symm⟩
  have hnorm : w ∈ Subgroup.normalizer (τ.range : Set E) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨hfwd g, fun hg => ?_⟩
    have h := hfwd _ (hfwd _ hg)
    have h3 : w * (w * (w * g * w⁻¹) * w⁻¹) * w⁻¹ = g := by
      calc w * (w * (w * g * w⁻¹) * w⁻¹) * w⁻¹ = (w * w * w) * g * (w * w * w)⁻¹ := by group
        _ = g := by rw [hw3', one_mul, inv_one, mul_one]
    rwa [h3] at h
  have hφw3 : φ w ^ 3 = 1 := by rw [← map_pow, hw3, map_one]
  have hordφ : orderOf (φ w) = 3 := orderOf_eq_prime hφw3 hw0
  have hordw : orderOf w = 3 := orderOf_eq_prime hw3 fun h => hw0 (by rw [h, map_one])
  have hdisj : ∀ k : ℤ, w ^ k ∈ τ.range → w ^ k = 1 := by
    intro k hk
    have hk' : w ^ k = w ^ (k % 3).toNat := by
      rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num))]
      have h := zpow_mod_orderOf w k
      rw [hordw] at h
      exact h.symm
    rw [hk'] at hk ⊢
    obtain ⟨p, hp⟩ := hk
    have h1 : φ w ^ (k % 3).toNat ∈ T.range := ⟨p, by rw [← hφτ, MonoidHom.comp_apply, hp,
      map_pow]⟩
    have h2 := hw1 _ h1
    have h3 : T p = 1 := by rw [← hφτ, MonoidHom.comp_apply, hp, map_pow, h2]
    have h4 : p = 1 := hT (h3.trans (map_one T).symm)
    rw [← hp, h4, map_one]
  refine ⟨τ.range ⊔ Subgroup.zpowers w, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro n ⟨hn, hnk⟩
    obtain ⟨l, ⟨p, rfl⟩, j, hj, rfl⟩ :=
      CFSG.SectionRank.OddCover.exists_mul_pow_of_mem_sup_zpowers hnorm hn
    rw [hordw] at hj
    replace hnk : φ (τ p) * φ w ^ j = 1 := by rw [← map_pow, ← map_mul]; exact hnk
    have h1 : φ w ^ j ∈ T.range := ⟨p⁻¹, by
      rw [map_inv, ← hφτ, MonoidHom.comp_apply, inv_eq_of_mul_eq_one_right hnk]⟩
    have h2 := hw1 j h1
    have hj0 : j = 0 := by
      have := orderOf_dvd_of_pow_eq_one h2
      rw [hordφ] at this
      omega
    subst hj0
    rw [pow_zero, mul_one] at hnk ⊢
    have h3 : T p = 1 := by rw [← hφτ, MonoidHom.comp_apply, hnk]
    rw [hT (h3.trans (map_one T).symm), map_one]
    exact Subgroup.one_mem _
  · rw [CFSG.SectionRank.OddCover.card_sup_zpowers_of_normalizer hnorm hdisj, hordw,
      ← Nat.card_congr (MonoidHom.ofInjective hτinj).toEquiv, mul_comm]

end TorusLift

section Mat

open Matrix

variable {K : Type} [Field K]

theorem blockMat_two_one (A : Matrix (Fin 2) (Fin 2) K) :
    (blockMat (m := 1) A : Matrix (Fin 3) (Fin 3) K) =
      !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

@[expose] def swapMat : Matrix (Fin 2) (Fin 2) K := !![0, 1; 1, 0]

theorem swapMat_mul_self : swapMat (K := K) * swapMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapMat, Matrix.mul_apply, Fin.sum_univ_two]

@[expose] def swapGL : GL (Fin 2) K := ⟨swapMat, swapMat, swapMat_mul_self, swapMat_mul_self⟩

end Mat

section SUThree

open Matrix CFSG.LieType.Steinberg CFSG.LieType.CentralExt CFSG.LieType.BorelTits
  CFSG.LieType.Universal.Unitary CFSG.Assembly.LowTwoRank CFSG.SectionRank.OddCover

variable {K : Type} [Field K] [Finite K] {f : ℕ} [Fact (Nat.Prime 2)] [CharP K 2]

local notation "σ₀" => unitaryInvolution K 2 f

theorem nonempty_sl2_mulEquiv_SUid_two (hK : Nat.card K = (2 ^ f) ^ 2) :
    Nonempty (SpecialLinearGroup (Fin 2) (fixedSubfield K 2 f) ≃* SUid σ₀ 2) := by
  obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hK
  obtain ⟨P, hP⟩ := exists_wittMatrix hK 2
  exact ⟨(hypEquiv hζ0 hζ).trans (conjEquiv P hP)⟩

theorem suidTwo_existsUnique_lift
    (hK : Nat.card K = (2 ^ f) ^ 2) {E G : Type*} [Group E]
    [Group G] [Finite E] {π : E →* G} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card π.ker)) (α : SUid σ₀ 2 →* G) :
    ∃! α' : SUid σ₀ 2 →* E, π.comp α' = α := by
  obtain ⟨Ψ⟩ := nonempty_sl2_mulEquiv_SUid_two hK
  obtain ⟨β, hβ, huniq⟩ := sl2_existsUnique_lift (p := 2) hπ hcen (not_two_dvd_of_odd hodd)
    (α.comp Ψ.toMonoidHom)
  refine ⟨β.comp Ψ.symm.toMonoidHom, ?_, fun γ hγ => ?_⟩
  · ext g
    have := congrArg (· (Ψ.symm g)) hβ
    simpa using this
  · have hγ' : π.comp γ = α := hγ
    have h := huniq (γ.comp Ψ.toMonoidHom) (show π.comp (γ.comp Ψ.toMonoidHom) = _ by
      rw [← MonoidHom.comp_assoc, hγ'])
    ext g
    have := congrArg (· (Ψ.symm g)) h
    simpa using this

@[expose] noncomputable def suTwoEmb (hK : Nat.card K = (2 ^ f) ^ 2) :
    SUid σ₀ 2 →* StatedSU 3 (2 ^ f) K :=
  (MulEquiv.subgroupCongr (SUid_eq_statedSU hK 3)).toMonoidHom.comp (blockSUid (m := 1) σ₀)

theorem coe_suTwoEmb (hK : Nat.card K = (2 ^ f) ^ 2) (g : SUid σ₀ 2) :
    ((suTwoEmb hK g : StatedSU 3 (2 ^ f) K) : GL (Fin 3) K) = blockGL (m := 1) (g : GL (Fin 2) K) :=
  rfl

theorem suTwoEmb_injective (hK : Nat.card K = (2 ^ f) ^ 2) :
    Function.Injective (suTwoEmb hK) := by
  intro g h hgh
  have e := congrArg (fun x : StatedSU 3 (2 ^ f) K =>
    ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hgh
  simp only [coe_suTwoEmb, coe_blockGL] at e
  apply Subtype.ext
  apply Units.ext
  ext i j
  have := congrFun (congrFun e (Fin.castAdd 1 i)) (Fin.castAdd 1 j)
  rwa [blockMat_apply_castAdd, blockMat_apply_castAdd] at this

theorem swapGL_mem : swapGL ∈ SUid σ₀ 2 := by
  rw [mem_SUid]
  refine ⟨?_, ?_⟩
  · change (swapMat (K := K)).det = 1
    rw [swapMat, det_fin_two_of]
    simp [CharTwo.neg_eq]
  · change conjTr σ₀ swapMat * swapMat = 1
    have : conjTr σ₀ (swapMat (K := K)) = swapMat := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [conjTr, swapMat]
    rw [this, swapMat_mul_self]

omit [Finite K] [Fact (Nat.Prime 2)] in
theorem blockGL_swapGL : blockGL (m := 1) (swapGL : GL (Fin 2) K) = s01GL := by
  apply Units.ext
  rw [coe_blockGL, coe_s01GL]
  change (blockMat (m := 1) swapMat : Matrix (Fin 3) (Fin 3) K) = s01Mat
  rw [blockMat_two_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapMat, s01Mat, CharTwo.neg_eq]

theorem diagHom_two_mem {a : Kˣ} (ha : a ∈ normOne K (2 ^ f)) :
    diagHom 2 ![a, a⁻¹] ∈ SUid σ₀ 2 := by
  rw [mem_SUid, det_diagHom, Fin.prod_univ_two]
  refine ⟨by simp, ?_⟩
  have ha' := mem_normOne.1 ha
  rw [coe_diagHom, conjTr, diagonal_map (map_zero _), diagonal_transpose, diagonal_mul_diagonal,
    ← diagonal_one]
  congr 1
  funext i
  have hpow : ∀ c : Kˣ, c ^ (2 ^ f + 1) = 1 → σ₀ (c : K) * c = 1 := fun c hc => by
    rw [unitaryInvolution_apply, ← pow_succ, ← Units.val_pow_eq_pow_val, hc, Units.val_one]
  fin_cases i
  · exact hpow a ha'
  · exact hpow a⁻¹ (by rw [inv_pow, ha', inv_one])

@[expose] noncomputable def normDiag : normOne K (2 ^ f) →* SUid σ₀ 2 where
  toFun a := ⟨diagHom 2 ![(a : Kˣ), (a : Kˣ)⁻¹], diagHom_two_mem a.2⟩
  map_one' := Subtype.ext (by
    change diagHom 2 ![((1 : normOne K (2 ^ f)) : Kˣ), ((1 : normOne K (2 ^ f)) : Kˣ)⁻¹] = 1
    rw [← map_one (diagHom (K := K) 2)]
    congr 1
    funext i
    fin_cases i <;> simp)
  map_mul' a b := Subtype.ext (by
    change diagHom 2 ![((a * b : normOne K (2 ^ f)) : Kˣ), ((a * b : normOne K (2 ^ f)) : Kˣ)⁻¹] =
      diagHom 2 ![(a : Kˣ), (a : Kˣ)⁻¹] * diagHom 2 ![(b : Kˣ), (b : Kˣ)⁻¹]
    rw [← map_mul]
    congr 1
    funext i
    fin_cases i <;> simp [mul_comm])

theorem coe_normDiag (a : normOne K (2 ^ f)) :
    ((normDiag a : SUid σ₀ 2) : GL (Fin 2) K) = diagHom 2 ![(a : Kˣ), (a : Kˣ)⁻¹] :=
  rfl

omit [Finite K] [Fact (Nat.Prime 2)] [CharP K 2] in
theorem blockGL_diagHom_two (d : Fin 2 → Kˣ) :
    blockGL (m := 1) (diagHom 2 d : GL (Fin 2) K) = diagHom 3 ![d 0, d 1, 1] := by
  apply Units.ext
  rw [coe_blockGL, coe_diagHom, coe_diagHom, blockMat_two_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

@[expose] def swapSU : SUid σ₀ 2 := ⟨swapGL, swapGL_mem⟩

theorem swapSU_mul_self : (swapSU (K := K) (f := f)) * swapSU = 1 :=
  Subtype.ext (Units.ext swapMat_mul_self)

theorem swapSU_conj_normDiag (a : normOne K (2 ^ f)) :
    swapSU * normDiag a * swapSU⁻¹ = (normDiag a)⁻¹ := by
  apply Subtype.ext
  apply Units.ext
  have hinv : (swapSU (K := K) (f := f))⁻¹ = swapSU := inv_eq_of_mul_eq_one_right swapSU_mul_self
  rw [hinv, ← map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul,
    coe_normDiag, coe_normDiag]
  change swapMat * _ * swapMat = _
  rw [coe_diagHom, coe_diagHom]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swapMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, Matrix.vecMul,
      dotProduct]

theorem exists_monomial_lift_SU_three
    (hK : Nat.card K = (2 ^ f) ^ 2) {E : Type*} [Group E]
    [Finite E] {π : E →* StatedSU 3 (2 ^ f) K} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card π.ker)) :
    ∃ N : Subgroup E, N ⊓ π.ker = ⊥ ∧ Nat.card N = 3 * (2 ^ f + 1) ^ 2 := by
  set M := normOne K (2 ^ f)
  obtain ⟨ρ, hρ, -⟩ := suidTwo_existsUnique_lift hK hπ hcen hodd (suTwoEmb hK)
  have hρ' : ∀ g, π (ρ g) = suTwoEmb hK g := fun g => DFunLike.congr_fun hρ g
  set φ : E →* GL (Fin 3) K := (StatedSU 3 (2 ^ f) K).subtype.comp π with hφdef
  have hφker : φ.ker = π.ker := by
    ext e
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hφdef, MonoidHom.comp_apply,
      Subgroup.coe_subtype, OneMemClass.coe_eq_one]
  have hcenφ : φ.ker ≤ Subgroup.center E := hφker ▸ hcen
  have hoddφ : Odd (Nat.card φ.ker) := hφker ▸ hodd
  have hφρ : ∀ g, φ (ρ g) = blockGL (m := 1) (g : GL (Fin 2) K) := fun g => by
    rw [hφdef, MonoidHom.comp_apply, hρ']
    rfl
  set u := ρ swapSU with hu
  have hu2 : u * u = 1 := by rw [hu, ← map_mul, swapSU_mul_self, map_one]
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  obtain ⟨v, ⟨hv2, hv⟩, -⟩ := existsUnique_involution_lift hπ hcen hodd
    (s := ⟨s12GL, monomialData_statedSU.s12_mem⟩) (Subtype.ext s12GL_sq)
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hv2)
  set w := u * v with hw
  have hφu : φ u = s01GL := by rw [hu, hφρ]; exact blockGL_swapGL
  have hφv : φ v = s12GL := by rw [hφdef, MonoidHom.comp_apply, hv]; rfl
  have hφw : φ w = cycGL := by rw [hw, map_mul, hφu, hφv, s01GL_mul_s12GL]
  have huw : u * w * u⁻¹ = w⁻¹ := by
    rw [hw, huinv, _root_.mul_inv_rev, huinv, hvinv, ← mul_assoc, hu2, one_mul]
  have hw3 : w ^ 3 = 1 := by
    have hk : w ^ 3 ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_pow, hφw, cycGL_pow_three]
    have hinv : u * w ^ 3 * u⁻¹ = (w ^ 3)⁻¹ := by
      rw [← conj_pow, huw, inv_pow]
    exact eq_one_of_sq_eq_one_of_odd (sq_eq_one_of_conj_eq_inv (hcenφ hk) hinv)
      (odd_orderOf_of_mem hoddφ hk)
  set x : M →* E := ρ.comp normDiag with hx
  have hux : ∀ a, u * x a * u⁻¹ = (x a)⁻¹ := fun a => by
    show u * ρ (normDiag a) * u⁻¹ = (ρ (normDiag a))⁻¹
    rw [hu, ← map_inv ρ swapSU, ← map_mul, ← map_mul, swapSU_conj_normDiag, map_inv]
  have hφx : ∀ a : M, φ (x a) = diagHom 3 ![(a : Kˣ), (a : Kˣ)⁻¹, 1] := fun a => by
    show φ (ρ (normDiag a)) = _
    rw [hφρ, coe_normDiag, blockGL_diagHom_two]
    rfl
  have hφy : ∀ a : M, φ (w * x a * w⁻¹) = diagHom 3 ![1, (a : Kˣ), (a : Kˣ)⁻¹] := fun a => by
    rw [map_mul, map_mul, map_inv, hφw, hφx, cycGL_conj_diagHom]
    rfl
  have hφz : ∀ a : M, φ (w⁻¹ * x a * w) = diagHom 3 ![(a : Kˣ)⁻¹, 1, (a : Kˣ)] := fun a => by
    rw [map_mul, map_mul, map_inv, hφw, hφx]
    have h := cycGL_conj_diagHom (K := K) ![(a : Kˣ)⁻¹, 1, (a : Kˣ)]
    have e : ![(![(a : Kˣ)⁻¹, 1, (a : Kˣ)] : Fin 3 → Kˣ) 2, ![(a : Kˣ)⁻¹, 1, (a : Kˣ)] 0,
        ![(a : Kˣ)⁻¹, 1, (a : Kˣ)] 1] = ![(a : Kˣ), (a : Kˣ)⁻¹, 1] := by
      funext i
      fin_cases i <;> rfl
    rw [e] at h
    rw [← h]
    group
  have hcomm : ∀ a b : M, Commute (φ (w * x a * w⁻¹)) (φ (w⁻¹ * x b * w)) := fun a b => by
    rw [hφy, hφz]
    exact (Commute.all _ _).map (diagHom 3)
  have hprod : ∀ a : M, φ (x a * (w * x a * w⁻¹) * (w⁻¹ * x a * w)) = 1 := fun a => by
    rw [map_mul, map_mul, hφx, hφy, hφz, ← map_mul, ← map_mul, ← map_one (diagHom (K := K) 3)]
    congr 1
    funext i
    fin_cases i <;> simp
  obtain ⟨hxy, hxyz⟩ := torus_lift_relations φ hcenφ hoddφ x hw3 huw hux hcomm hprod
  have hφτ : ∀ a b : M, φ (x a * (w * x (a * b) * w⁻¹)) = torusHom M (a, b) := fun a b => by
    rw [map_mul, hφx, hφy, torusHom_apply, ← map_mul]
    congr 1
    funext i
    fin_cases i <;> simp [mul_comm]
  have hw1 : ∀ k : ℕ, φ w ^ k ∈ (torusHom M).range → φ w ^ k = 1 := fun k hk => by
    rw [hφw] at hk ⊢
    have := zpow_cycGL_mem_torus3 M (k := k) (by rw [zpow_natCast]; exact hk)
    rwa [zpow_natCast] at this
  have hw0 : φ w ≠ 1 := by rw [hφw]; exact cycGL_ne_one
  obtain ⟨N, hN, hcard⟩ := exists_monomial_lift φ x hw3 hxy hxyz (torusHom M)
    (torusHom_injective M) hφτ hw1 hw0
  refine ⟨N, hφker ▸ hN, ?_⟩
  rw [hcard, Nat.card_prod, card_normOne hK, sq]

theorem exists_suTwo_lift_SU_three
    (hK : Nat.card K = (2 ^ f) ^ 2) {E : Type*} [Group E]
    [Finite E] {π : E →* StatedSU 3 (2 ^ f) K} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card π.ker)) :
    ∃ Q : Subgroup E, Q ⊓ π.ker = ⊥ ∧ Nat.card Q = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
  obtain ⟨ρ, hρ, -⟩ := suidTwo_existsUnique_lift hK hπ hcen hodd (suTwoEmb hK)
  have hρ' : ∀ g, π (ρ g) = suTwoEmb hK g := fun g => DFunLike.congr_fun hρ g
  have hinj : Function.Injective ρ := fun a b h => suTwoEmb_injective hK (by
    rw [← hρ', ← hρ', h])
  refine ⟨ρ.range, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro _ ⟨⟨g, rfl⟩, hg⟩
    have h1 : suTwoEmb hK g = 1 := by rw [← hρ']; exact hg
    have h2 : g = 1 := suTwoEmb_injective hK (h1.trans (map_one _).symm)
    rw [h2, map_one]
    exact Subgroup.one_mem _
  · obtain ⟨Ψ⟩ := nonempty_sl2_mulEquiv_SUid_two hK
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, ← Nat.card_congr Ψ.toEquiv,
      card_specialLinearGroup_fin_two, card_fixedSubfield hK]

omit [Finite K] [Fact (Nat.Prime 2)] [CharP K 2] in
theorem not_dvd_two_pow {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (n : ℕ) : ¬ r ∣ 2 ^ n := fun h =>
  hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h))

section Arith

omit [Finite K] [Fact (Nat.Prime 2)] [CharP K 2]

variable {q r : ℕ}

theorem sq_sub_one_eq_mul (hq1 : 1 ≤ q) : q ^ 2 - 1 = (q + 1) * (q - 1) := by
  zify [hq1, Nat.one_le_pow 2 q hq1]
  ring

theorem pow_three_add_one_eq_mul : q ^ 3 + 1 = (q + 1) * (q ^ 2 - q + 1) := by
  have hqq : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  zify [hqq]
  ring

theorem factorization_SU_three_le_monomial (hr : r.Prime) (hr2 : r ≠ 2) (hrq : ¬ r ∣ q)
    (hq2 : 2 ≤ q) (hr1 : r ∣ q + 1) :
    (q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1)).factorization r ≤ (3 * (q + 1) ^ 2).factorization r := by
  have hre' : ¬ r ∣ q - 1 := fun h => hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1
    (by have := Nat.dvd_sub hr1 h; rwa [show q + 1 - (q - 1) = 2 by omega] at this))
  have hq0 : q ≠ 0 := by omega
  have hqq : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  rw [sq_sub_one_eq_mul (by omega), pow_three_add_one_eq_mul,
    factorization_order_eq hr hr2 hq0 (by omega) (by omega) (by omega) hrq hre'
      (factorization_sq_sub_add_one hr hr1), show (6 : ℕ) = 2 * 3 by norm_num, mul_assoc,
    Nat.factorization_mul (by norm_num) (by positivity), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (fun h => hr2
      ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h)), zero_add]

theorem factorization_SU_three_le_SU_two (hr : r.Prime) (hr2 : r ≠ 2) (hrq : ¬ r ∣ q)
    (hq2 : 2 ≤ q) (hr1 : r ∣ q - 1) :
    (q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1)).factorization r ≤ (q * (q ^ 2 - 1)).factorization r := by
  have hr3 : ¬ r ∣ q ^ 3 + 1 := by
    intro h
    have h0 : q - 1 ∣ q ^ 3 - 1 := by
      simpa using Nat.sub_dvd_pow_sub_pow (x := q) (y := 1) (n := 3)
    have h3 : r ∣ q ^ 3 - 1 := hr1.trans h0
    have h4 := Nat.dvd_sub h h3
    rw [show q ^ 3 + 1 - (q ^ 3 - 1) = 2 by
      have : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
      omega] at h4
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h4)
  have h21 : q ^ 2 - 1 ≠ 0 := by
    have : 4 ≤ q ^ 2 := by nlinarith
    omega
  rw [Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) h21,
    Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply,
    Finsupp.add_apply, Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hr3,
    Nat.factorization_eq_zero_of_not_dvd (fun h => hrq (hr.dvd_of_dvd_pow h)),
    Nat.factorization_eq_zero_of_not_dvd hrq]
  omega

end Arith

theorem even_unitary_three_perfect_odd_extension_trivial
    (hK : Nat.card K = (2 ^ f) ^ 2)
    (hf : 1 ≤ f) {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    {π : E →* StatedSU 3 (2 ^ f) K} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card π.ker)) : π.ker = ⊥ := by
  have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have hq2 : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hS := card_statedSU_three (p := 2) hK
  refine eq_bot_of_forall_sylow_eq_bot _ fun r hr _ Cp => ?_
  by_cases hr2 : r = 2
  · subst hr2
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 Cp.isPGroup'
    have h1 : Nat.card (Cp : Subgroup π.ker) ∣ Nat.card π.ker := Subgroup.card_subgroup_dvd_card _
    have hk0 : k = 0 := by
      by_contra hk0
      exact (Nat.not_even_iff_odd.2 hodd)
        (even_iff_two_dvd.2 ((dvd_pow_self 2 hk0).trans (hk ▸ h1)))
    rw [hk0, pow_zero] at hk
    exact Subgroup.eq_bot_of_card_eq _ hk
  have hrq : ¬ r ∣ 2 ^ f := not_dvd_two_pow hr hr2 f
  by_cases hr1 : r ∣ 2 ^ f + 1
  · obtain ⟨N, hN, hcard⟩ := exists_monomial_lift_SU_three hK hπ hcen hodd
    refine sylow_kernel_eq_bot_of_inf_ker_eq_bot π hcen N hN ?_ Cp
    rw [hcard, hS]
    exact factorization_SU_three_le_monomial hr hr2 hrq hq2 hr1
  by_cases hr1' : r ∣ 2 ^ f - 1
  · obtain ⟨Q, hQ, hcard⟩ := exists_suTwo_lift_SU_three hK hπ hcen hodd
    refine sylow_kernel_eq_bot_of_inf_ker_eq_bot π hcen Q hQ ?_ Cp
    rw [hcard, hS]
    exact factorization_SU_three_le_SU_two hr hr2 hrq hq2 hr1'
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow r (StatedSU 3 (2 ^ f) K)))
  refine CFSG.ShultStronglyClosedTI.central_cover_cyclic_sylow_kernel_eq_bot π hπ hcen Cp T ?_
  set T' : Subgroup (GL (Fin 3) K) :=
    (T : Subgroup (StatedSU 3 (2 ^ f) K)).map (StatedSU 3 (2 ^ f) K).subtype with hT'def
  have hT' : IsPGroup r T' := T.isPGroup'.map _
  suffices IsCyclic T' from isCyclic_of_surjective
    ((T : Subgroup (StatedSU 3 (2 ^ f) K)).equivMapOfInjective _
      (StatedSU 3 (2 ^ f) K).subtype_injective).symm.toMonoidHom
    ((T : Subgroup (StatedSU 3 (2 ^ f) K)).equivMapOfInjective _
      (StatedSU 3 (2 ^ f) K).subtype_injective).symm.surjective
  have hKc : Fintype.card K = (2 ^ f) ^ 2 := by rw [← Nat.card_eq_fintype_card, hK]
  have hr12 : ¬ r ∣ (2 ^ f) ^ 2 - 1 := by
    rw [sq_sub_one_eq_mul hq1]
    intro h
    rcases (Nat.Prime.dvd_mul hr).1 h with h | h
    · exact hr1 h
    · exact hr1' h
  by_cases hrS : r ∣ Nat.card (StatedSU 3 (2 ^ f) K)
  · have h31 : r ∣ (2 ^ f) ^ 3 + 1 := by
      rw [hS] at hrS
      rcases (Nat.Prime.dvd_mul hr).1 hrS with h | h
      · rcases (Nat.Prime.dvd_mul hr).1 h with h | h
        · exact absurd (hr.dvd_of_dvd_pow h) hrq
        · exact absurd h hr12
      · exact h
    have hm : r ∣ (2 ^ f) ^ 2 - 2 ^ f + 1 := by
      rw [pow_three_add_one_eq_mul] at h31
      rcases (Nat.Prime.dvd_mul hr).1 h31 with h | h
      · exact absurd h hr1
      · exact h
    have hqq : 2 ^ f ≤ (2 ^ f) ^ 2 := Nat.le_self_pow (by norm_num) _
    have hr21 : ¬ r ∣ (2 ^ f) ^ 2 + 1 := fun h => hrq (by
      have := Nat.dvd_sub h hm
      rwa [show (2 ^ f) ^ 2 + 1 - ((2 ^ f) ^ 2 - 2 ^ f + 1) = 2 ^ f by omega] at this)
    refine isCyclic_of_isPGroup_GL_three (p := 2) ?_ ?_ ?_ T' hT'
    · rw [hKc]; exact fun h => hrq (hr.dvd_of_dvd_pow h)
    · rw [hKc]; exact hr12
    · rw [hKc, show ((2 ^ f) ^ 2) ^ 2 - 1 = ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 2 + 1) by
        have h1 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by omega)
        zify [h1, Nat.one_le_pow 2 ((2 ^ f) ^ 2) (by omega)]
        ring]
      intro h
      rcases (Nat.Prime.dvd_mul hr).1 h with h | h
      · exact hr12 h
      · exact hr21 h
  ·
    have h1 : Nat.card T' = 1 := by
      rw [hT'def, Subgroup.card_map_of_injective (StatedSU 3 (2 ^ f) K).subtype_injective,
        Sylow.card_eq_multiplicity, Nat.factorization_eq_zero_of_not_dvd hrS, pow_zero]
    have : Subsingleton T' := (Nat.card_eq_one_iff_unique.1 h1).1
    exact isCyclic_of_subsingleton

theorem even_unitary_three_central_odd_extension_splitting
    (hK : Nat.card K = (2 ^ f) ^ 2)
    (hf : 2 ≤ f) {E : Type*} [Group E] [Finite E] {π : E →* StatedSU 3 (2 ^ f) K}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hodd : Odd (Nat.card π.ker)) :
    ∃ σ : StatedSU 3 (2 ^ f) K →* E, (∀ x, π (σ x) = x) ∧
      (∀ τ : StatedSU 3 (2 ^ f) K →* E, (∀ x, π (τ x) = x) → τ = σ) ∧
      σ.range = commutator E ∧ ∃ e : π.ker × σ.range ≃* E, ∀ a, e a = (a.1 : E) * a.2 := by
  have h4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hS : Group.IsPerfect (StatedSU 3 (2 ^ f) K) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hK le_rfl fun h => by
      have := congrArg Prod.snd h
      simp only at this
      omega
  obtain ⟨-, hE', hsurj⟩ := CFSG.LocalCores.central_extension_derived_of_surjective π hπ hcen hS
  set E' := commutator E with hE'def
  have : Group.IsPerfect E' := hE'
  set π' : E' →* StatedSU 3 (2 ^ f) K := π.comp E'.subtype with hπ'
  have hcen' : π'.ker ≤ Subgroup.center E' := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hcen hx) y)
  have hodd' : Odd (Nat.card π'.ker) := by
    let g : π'.ker →* π.ker :=
      { toFun := fun x => ⟨((x : E') : E), x.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_injective g fun a b h => ?_)
    have h' : ((a : E') : E) = ((b : E') : E) := congrArg (fun x : π.ker => (x : E)) h
    exact Subtype.ext (Subtype.ext h')
  have hker' := even_unitary_three_perfect_odd_extension_trivial hK (by omega) hsurj hcen' hodd'
  have hbij : Function.Bijective π' := ⟨(MonoidHom.ker_eq_bot_iff _).1 hker', hsurj⟩
  set σ : StatedSU 3 (2 ^ f) K →* E :=
    E'.subtype.comp (MulEquiv.ofBijective π' hbij).symm.toMonoidHom with hσdef
  have hσ : ∀ x, π (σ x) = x := fun x => (MulEquiv.ofBijective π' hbij).apply_symm_apply x
  have huniq : ∀ τ : StatedSU 3 (2 ^ f) K →* E, (∀ x, π (τ x) = x) → τ = σ := by
    intro τ hτ
    have hmem : ∀ x, τ x * (σ x)⁻¹ ∈ Subgroup.center E := fun x => hcen (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hτ, hσ, mul_inv_cancel])
    let d : StatedSU 3 (2 ^ f) K →* Subgroup.center E :=
      { toFun := fun x => ⟨τ x * (σ x)⁻¹, hmem x⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun x y => Subtype.ext (by
          change τ (x * y) * (σ (x * y))⁻¹ = τ x * (σ x)⁻¹ * (τ y * (σ y)⁻¹)
          have hc := Subgroup.mem_center_iff.1 (hmem y) (σ x)⁻¹
          rw [map_mul, map_mul, _root_.mul_inv_rev, mul_assoc, ← mul_assoc (τ y), ← hc]
          group) }
    have hd := CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_one_of_commutative d
    ext x
    have := congrArg (fun g : StatedSU 3 (2 ^ f) K →* Subgroup.center E =>
      ((g x : Subgroup.center E) : E)) hd
    exact mul_inv_eq_one.1 this
  refine ⟨σ, hσ, huniq, ?_, kerProdRangeEquiv hcen hσ, kerProdRangeEquiv_apply hcen hσ⟩
  rw [hσdef, MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulEquiv.surjective _),
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]

omit [Fact (Nat.Prime 2)] in
theorem even_unitary_three_odd_cover_catalog_step
    {L : Type} [Group L] [Finite L]
    (hL : IsQuasisimple L) (hSQT : IsStronglyQuasithin L)
    (hodd : Odd (Nat.card (Subgroup.center L))) {f : ℕ}
    (h : StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 3 2 f) : CatalogStepConclusion L := by
  obtain ⟨⟨-, hf, -, hnq⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hf2 : 2 ≤ f := by
    by_contra hlt
    obtain rfl : f = 1 := by omega
    exact hnq (by norm_num)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := ClassicalOdd.charP_of_card (f := f * 2) (by rw [hK, pow_mul])
  have : Group.IsPerfect L := hL.1
  obtain ⟨hsurj, hcen, hdvd⟩ := pullbackFst_centralQuotientMap e
  obtain ⟨σ, hσ, -⟩ := even_unitary_three_central_odd_extension_splitting hK hf2 hsurj hcen
    (Odd.of_dvd_nat hodd hdvd)
  obtain ⟨φ, hφ, hker, hD⟩ := perfect_cover_map_of_section e σ hσ
  exact OddCover.classical_scalar_cover_step Nat.prime_two hf (by norm_num) (Or.inr ⟨hK, rfl⟩)
    hSQT hodd φ hφ hker hD

end SUThree

end CFSG.SectionRank.EvenCover
