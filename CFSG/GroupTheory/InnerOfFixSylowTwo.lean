module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.GroupTheory

open Subgroup

open scoped IsMulCommutative


theorem exists_coboundary_of_odd_index_of_isPGroup {X : Type*} [Group X] [Finite X]
    {M : Type*} [CommGroup M] [Finite M] (hM : IsPGroup 2 M) (ρ : X →* MulAut M)
    {δ : X → M} (hδ : ∀ x y : X, δ (x * y) = δ x * ρ x (δ y))
    {T : Subgroup X} (hT : Odd T.index) (hδT : ∀ t ∈ T, δ t = 1) :
    ∃ y : M, ∀ x : X, δ x = ρ x y * y⁻¹ := by
  classical
  letI := Fintype.ofFinite X
  haveI : Fintype (X ⧸ T) := Fintype.ofFinite _
  have hconst : ∀ (a : X) (t : T), δ (a * t) = δ a := by
    intro a t
    rw [hδ, hδT t t.2, map_one, mul_one]
  set w : M := ∏ c : X ⧸ T, δ c.out with hw
  have hcard : Fintype.card (X ⧸ T) = T.index := by
    rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  have hout : ∀ (g : X) (c : X ⧸ T), δ (g * c.out) = δ (g • c).out := by
    intro g c
    have h1 : (QuotientGroup.mk (g * c.out) : X ⧸ T) = g • c := by
      conv_rhs => rw [← QuotientGroup.out_eq' c]
      rfl
    obtain ⟨p, hp⟩ := QuotientGroup.mk_out_eq_mul T (g * c.out)
    rw [h1] at hp
    rw [hp, hconst _ p]
  have hρ : ∀ (g : X) (c : X ⧸ T), ρ g (δ c.out) = (δ g)⁻¹ * δ (g • c).out := by
    intro g c
    rw [← hout, hδ, inv_mul_cancel_left]
  have hprod : ∀ g : X, ∏ c : X ⧸ T, δ (g • c).out = w := by
    intro g
    rw [hw]
    simpa only [MulAction.toPerm_apply] using
      Equiv.prod_comp (MulAction.toPerm g) (fun c : X ⧸ T => δ c.out)
  have hρw : ∀ g : X, ρ g w = (δ g)⁻¹ ^ T.index * w := by
    intro g
    calc ρ g w = ∏ c : X ⧸ T, ρ g (δ c.out) := by rw [hw, map_prod]
      _ = ∏ c : X ⧸ T, ((δ g)⁻¹ * δ (g • c).out) :=
        Finset.prod_congr rfl fun c _ => hρ g c
      _ = (δ g)⁻¹ ^ T.index * w := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcard, hprod g]
  have hpow : ∀ g : X, (δ g) ^ T.index = w * (ρ g w)⁻¹ := by
    intro g
    have h1 : ((δ g) ^ T.index)⁻¹ = ρ g w * w⁻¹ := by
      rw [← inv_pow, hρw g]
      group
    calc (δ g) ^ T.index = (((δ g) ^ T.index)⁻¹)⁻¹ := (inv_inv _).symm
      _ = (ρ g w * w⁻¹)⁻¹ := by rw [h1]
      _ = w * (ρ g w)⁻¹ := by rw [mul_inv_rev, inv_inv]
  have hcop2 : T.index.Coprime 2 := Nat.coprime_two_right.mpr hT
  obtain ⟨a, ha⟩ := hM.exists_exponent_eq_pow
  have hcop : T.index.Coprime (Monoid.exponent M) := by
    rw [ha]
    exact hcop2.pow_right a
  by_cases hexp : Monoid.exponent M = 1
  · haveI : Subsingleton M := Monoid.exp_eq_one_iff.mp hexp
    exact ⟨1, fun x => Subsingleton.elim _ _⟩
  · have hexp1 : 1 < Monoid.exponent M := by
      have hpos : 0 < Monoid.exponent M :=
        Monoid.exponent_pos.mpr (Monoid.ExponentExists.of_finite (G := M))
      exact Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨Nat.pos_iff_ne_zero.mp hpos, hexp⟩
    obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hexp1
    refine ⟨(w ^ k)⁻¹, fun x => ?_⟩
    have hnk : (δ x) ^ (T.index * k) = δ x := by
      rw [Monoid.pow_eq_mod_exponent, hk, pow_one]
    have hA : (w * (ρ x w)⁻¹) ^ k = δ x := by
      calc (w * (ρ x w)⁻¹) ^ k = ((δ x) ^ T.index) ^ k := by rw [hpow x]
        _ = (δ x) ^ (T.index * k) := by rw [pow_mul]
        _ = δ x := hnk
    have hcomm : (w * (ρ x w)⁻¹) ^ k =
        ρ x ((w ^ k)⁻¹) * ((w ^ k)⁻¹)⁻¹ := by
      calc (w * (ρ x w)⁻¹) ^ k = w ^ k * ((ρ x w) ^ k)⁻¹ := by
            rw [mul_pow, inv_pow]
        _ = w ^ k * (ρ x (w ^ k))⁻¹ := by rw [map_pow]
        _ = ρ x ((w ^ k)⁻¹) * ((w ^ k)⁻¹)⁻¹ := by
            rw [map_inv, inv_inv]
            exact mul_comm _ _
    exact hA.symm.trans hcomm

theorem exists_mem_center_sylow_two_conj_eq {Y : Type*} [Group Y] {X Q T : Subgroup Y}
    [Finite X] (hQX : Q ≤ X) (hQn : (Q.subgroupOf X).Normal) (hQ2 : IsPGroup 2 Q)
    (hCQ : X ⊓ Subgroup.centralizer (Q : Set Y) ≤ Q)
    (hTX : T ≤ X) (hT2 : IsPGroup 2 T) (hTodd : Odd (T.subgroupOf X).index)
    {g : Y} (hgX : g ∈ Subgroup.normalizer (X : Set Y))
    (hgT : ∀ t ∈ T, g * t = t * g) :
    ∃ z ∈ T ⊓ Subgroup.centralizer (T : Set Y),
      ∀ x ∈ X, g * x * g⁻¹ = z * x * z⁻¹ := by
  classical
  let Q' : Subgroup X := Q.subgroupOf X
  let M' : Subgroup X := Q' ⊓ Subgroup.centralizer (Q' : Set X)
  haveI : Q'.Normal := hQn
  have hM'n : M'.Normal := inferInstance
  have hQ'2 : IsPGroup 2 Q' := hQ2.comap_subtype
  have hM'2 : IsPGroup 2 M' := hQ'2.to_inf_left
  have hT'2 : IsPGroup 2 (T.subgroupOf X) := hT2.comap_subtype
  have hT'not : ¬ 2 ∣ (T.subgroupOf X).index := fun h =>
    (Nat.not_even_iff_odd.mpr hTodd) (even_iff_two_dvd.mpr h)
  let TS : Sylow 2 X := hT'2.toSylow hT'not
  have hQT : Q ≤ T := by
    have hle : Q' ≤ (TS : Subgroup X) := hQ'2.le_sylow_of_normal TS
    intro q hq
    have hq' : (⟨q, hQX hq⟩ : X) ∈ Q' := Subgroup.mem_subgroupOf.mpr hq
    have hqT : (⟨q, hQX hq⟩ : X) ∈ (TS : Subgroup X) := hle hq'
    have hqT' : (⟨q, hQX hq⟩ : X) ∈ T.subgroupOf X := by
      simpa [TS] using hqT
    exact Subgroup.mem_subgroupOf.mp hqT'
  haveI : Finite M' :=
    Finite.of_injective (fun m : M' => (m : X)) Subtype.coe_injective
  have hM'comm : IsMulCommutative M' :=
    ⟨⟨fun a b => Subtype.ext <|
      (Subgroup.mem_centralizer_iff.mp b.2.2 (a : X) a.2.1)⟩⟩
  haveI : IsMulCommutative M' := hM'comm
  have hconj_mem : ∀ x : X, g * (x : Y) * g⁻¹ ∈ X := fun x =>
    (Subgroup.mem_normalizer_iff.mp hgX (x : Y)).mp x.2
  let δX : X → X := fun x => ⟨g * (x : Y) * g⁻¹, hconj_mem x⟩ * x⁻¹
  have hδXcoe : ∀ x : X, ((δX x : X) : Y) = g * (x : Y) * g⁻¹ * (x : Y)⁻¹ :=
    fun x => rfl
  have hδcent : ∀ x : X, δX x ∈ Subgroup.centralizer (Q' : Set X) := by
    intro x
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hqQ : (q : Y) ∈ Q := Subgroup.mem_subgroupOf.mp hq
    have haQ' : (x : X)⁻¹ * q * x ∈ Q' := hQn.conj_mem' q hq x
    have haQ : (x : Y)⁻¹ * (q : Y) * (x : Y) ∈ Q := by
      simpa using Subgroup.mem_subgroupOf.mp haQ'
    have hga : g⁻¹ * ((x : Y)⁻¹ * (q : Y) * (x : Y)) * g =
        (x : Y)⁻¹ * (q : Y) * (x : Y) := by
      have hcomm := hgT _ (hQT haQ)
      calc g⁻¹ * ((x : Y)⁻¹ * (q : Y) * (x : Y)) * g
          = g⁻¹ * (((x : Y)⁻¹ * (q : Y) * (x : Y)) * g) := by group
        _ = g⁻¹ * (g * ((x : Y)⁻¹ * (q : Y) * (x : Y))) := by rw [← hcomm]
        _ = (x : Y)⁻¹ * (q : Y) * (x : Y) := by group
    have hgq : g * (q : Y) * g⁻¹ = (q : Y) := by
      rw [hgT _ (hQT hqQ)]
      group
    have hconj : ((δX x : X) : Y) * (q : Y) * ((δX x : X) : Y)⁻¹ = (q : Y) := by
      rw [hδXcoe]
      calc g * (x : Y) * g⁻¹ * (x : Y)⁻¹ * (q : Y) *
            (g * (x : Y) * g⁻¹ * (x : Y)⁻¹)⁻¹
          = g * (x : Y) * (g⁻¹ * ((x : Y)⁻¹ * (q : Y) * (x : Y)) * g) *
              (x : Y)⁻¹ * g⁻¹ := by group
        _ = g * (x : Y) * ((x : Y)⁻¹ * (q : Y) * (x : Y)) * (x : Y)⁻¹ * g⁻¹ := by
              rw [hga]
        _ = g * (q : Y) * g⁻¹ := by group
        _ = (q : Y) := hgq
    have hcommY : ((δX x : X) : Y) * (q : Y) = (q : Y) * ((δX x : X) : Y) :=
      mul_inv_eq_iff_eq_mul.mp hconj
    exact Subtype.ext hcommY.symm
  have hδQ' : ∀ x : X, δX x ∈ Q' := by
    intro x
    refine hCQ (Subgroup.mem_inf.mpr ⟨(δX x).2, ?_⟩)
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hqX : q ∈ X := hTX (hQT hq)
    let q' : Q' := ⟨⟨q, hqX⟩, Subgroup.mem_subgroupOf.mpr hq⟩
    have hcomm := Subgroup.mem_centralizer_iff.mp (hδcent x) q' q'.2
    exact congrArg (fun z : X => (z : Y)) hcomm
  have hδM : ∀ x : X, δX x ∈ M' := fun x =>
    Subgroup.mem_inf.mpr ⟨hδQ' x, hδcent x⟩
  let δ : X → M' := fun x => ⟨δX x, hδM x⟩
  let ρ : X →* MulAut M' := MulAut.conjNormal
  have hδcocycle : ∀ x y : X, δ (x * y) = δ x * ρ x (δ y) := by
    intro x y
    apply Subtype.ext
    apply Subtype.ext
    change ((δX (x * y) : X) : Y) =
      ((δX x * ((ρ x (δ y) : M') : X) : X) : Y)
    simp only [δ, δX, ρ, Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply]
    group
  have hδT : ∀ t ∈ T.subgroupOf X, δ t = 1 := by
    intro t ht
    apply Subtype.ext
    apply Subtype.ext
    have htT : (t : Y) ∈ T := Subgroup.mem_subgroupOf.mp ht
    simp only [δ, δX, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one, Subtype.coe_mk]
    have hgt : g * (t : Y) * g⁻¹ = (t : Y) := by
      rw [hgT (t : Y) htT]
      group
    rw [hgt]
    group
  obtain ⟨y, hy⟩ := exists_coboundary_of_odd_index_of_isPGroup (hM := hM'2) (ρ := ρ)
    (δ := δ) (hδ := hδcocycle) (T := T.subgroupOf X) hTodd hδT
  have hyQ' : (y : X) ∈ Q' := y.2.1
  have hyQ : ((y : X) : Y) ∈ Q := Subgroup.mem_subgroupOf.mp hyQ'
  have hyT : ((y : X) : Y) ∈ T := hQT hyQ
  have hy_comm_T : ∀ t ∈ T, t * ((y : X) : Y) = ((y : X) : Y) * t := by
    intro t ht
    let t' : T.subgroupOf X := ⟨⟨t, hTX ht⟩, Subgroup.mem_subgroupOf.mpr ht⟩
    have h1 : δ t' = 1 := hδT t' t'.2
    have h2 : ρ t' y = y := by
      have h := hy t'
      rw [h1] at h
      have h' := congrArg (fun z : M' => z * y) h
      simpa [mul_assoc] using h'.symm
    have h4 : (((ρ t' y : M') : X) : Y) = (((y : M') : X) : Y) :=
      congrArg (fun m : M' => ((m : X) : Y)) h2
    have h5 : (((ρ t' y : M') : X) : Y) = (t : Y) * ((y : X) : Y) * (t : Y)⁻¹ := by
      simp only [ρ, MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_inv]
      rfl
    rw [h5] at h4
    calc (t : Y) * ((y : X) : Y)
        = ((t : Y) * ((y : X) : Y) * (t : Y)⁻¹) * (t : Y) := by group
      _ = ((y : X) : Y) * (t : Y) := by rw [h4]
  have hzT : ((y : X) : Y)⁻¹ ∈ T := T.inv_mem hyT
  have hzcent : ((y : X) : Y)⁻¹ ∈ Subgroup.centralizer (T : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have hc : Commute t ((y : X) : Y) := hy_comm_T t ht
    exact hc.inv_right
  refine ⟨((y : X) : Y)⁻¹, Subgroup.mem_inf.mpr ⟨hzT, hzcent⟩, ?_⟩
  intro x hx
  let x' : X := ⟨x, hx⟩
  have h := hy x'
  have hxy : g * (x' : Y) * g⁻¹ * (x' : Y)⁻¹ =
      (x' : Y) * ((y : X) : Y) * (x' : Y)⁻¹ * ((y : X) : Y)⁻¹ := by
    simpa only [δ, δX, ρ, Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply] using
      congrArg (fun m : M' => ((m : X) : Y)) h
  have haM' : (x' : X) * y * (x' : X)⁻¹ ∈ M' := hM'n.conj_mem (y : X) y.2 x'
  have hyQ'inv : (y : X)⁻¹ ∈ Q' := Q'.inv_mem hyQ'
  have hcommY : (x' : Y) * ((y : X) : Y) * (x' : Y)⁻¹ * ((y : X) : Y)⁻¹ =
      ((y : X) : Y)⁻¹ * ((x' : Y) * ((y : X) : Y) * (x' : Y)⁻¹) := by
    have hcommX : ((⟨(x' : X) * y * (x' : X)⁻¹, haM'⟩ : M') : X) * (y : X)⁻¹ =
        (y : X)⁻¹ * ((⟨(x' : X) * y * (x' : X)⁻¹, haM'⟩ : M') : X) := by
      exact (Subgroup.mem_centralizer_iff.mp
        (⟨(x' : X) * y * (x' : X)⁻¹, haM'⟩ : M').2.2 (y : X)⁻¹ hyQ'inv).symm
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
      congrArg (fun z : X => (z : Y)) hcommX
  calc g * (x' : Y) * g⁻¹
      = (g * (x' : Y) * g⁻¹ * (x' : Y)⁻¹) * (x' : Y) := by group
    _ = ((x' : Y) * ((y : X) : Y) * (x' : Y)⁻¹ * ((y : X) : Y)⁻¹) * (x' : Y) := by
          rw [hxy]
    _ = (((y : X) : Y)⁻¹ * ((x' : Y) * ((y : X) : Y) * (x' : Y)⁻¹)) * (x' : Y) := by
          rw [hcommY]
    _ = ((y : X) : Y)⁻¹ * (x' : Y) * (((y : X) : Y)⁻¹)⁻¹ := by group

end CFSG.GroupTheory
