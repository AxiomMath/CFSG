module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47FldStmt
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47FldLift
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47FldComp
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SubSecClosure
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47FldSec

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Matrix Subgroup CFSG CFSG.Blueprint CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace P47Fld

section Aux

variable {Y : Type} [Group Y]

theorem mem_normalizer_map_subtype {K : Subgroup Y} {J : Subgroup ↥K} {k : ↥K}
    (hk : k ∈ normalizer (J : Set ↥K)) :
    (k : Y) ∈ normalizer ((J.map K.subtype : Subgroup Y) : Set Y) := by
  rw [Subgroup.mem_normalizer_iff] at hk ⊢
  intro y
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨k * j * k⁻¹, (hk j).1 hj, by simp⟩
  · rintro ⟨j, hj, hjy⟩
    refine ⟨k⁻¹ * j * k, (hk (k⁻¹ * j * k)).2 ?_, ?_⟩
    · have e1 : k * (k⁻¹ * j * k) * k⁻¹ = j := by group
      rw [e1]
      exact hj
    have : (k : Y) * y * (k : Y)⁻¹ = (j : Y) := hjy.symm
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← this]
    group

end Aux

end P47Fld

open P47Fld

theorem p47FieldCase_thm : P47FieldCase := by
  intro G _ z k F4 Y _ _ b hY p hp hp2 K _ hKperf F _ _ hF φ hφs hφk hodd hbK e he2 he1 heK hbe α hα
    A σ hσ hαeq
  obtain ⟨n1, hn1, hFcard⟩ := hF
  have he' : e⁻¹ = e := inv_eq_of_mul_eq_one_right he2
  let E : MulAut ↥K := MulAut.conjNormal e
  have hE : ∀ x : ↥K, ((E x : ↥K) : Y) = e * x * e⁻¹ := fun x => MulAut.conjNormal_apply e x
  have hEE : ∀ x : ↥K, E (E x) = x := by
    intro x
    apply Subtype.ext
    rw [hE, hE, he']
    calc e * (e * (x : Y) * e) * e = (e * e) * x * (e * e) := by group
      _ = x := by rw [he2]; group
  have hαE : ∀ x : ↥K, α (φ x) = φ (E x) := by
    intro x
    have h1 := hα x (heK x)
    have h2 : E x = ⟨e * (x : Y) * e⁻¹, heK x⟩ := Subtype.ext (hE x)
    rw [h2]
    exact h1
  have hαα : α * α = 1 := by
    ext x
    obtain ⟨x', rfl⟩ := hφs x
    rw [MulAut.mul_apply, hαE, hαE, hEE]
    rfl
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨F0, _, _, hchar, n0, hn0, hF0card, Q, ⟨e0⟩, hQp, hQα, hQn⟩ :=
    field_section hp hn1 hFcard α hαα A σ hσ hαeq
  have h2F0 : (2 : F0) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : F0) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff F0 p] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h')
  have hkerodd : Odd (Nat.card φ.ker) := by rw [hφk]; exact hodd
  have hbfix : E ⟨b, hbK⟩ = ⟨b, hbK⟩ := by
    apply Subtype.ext
    rw [hE]
    exact mul_inv_eq_iff_eq_mul.2 hbe
  obtain ⟨J, hJp, hJfix, hJφ, hbJ⟩ :=
    exists_perfect_fixed_lift φ hφs hkerodd E hEE α hαE Q hQp hQα hQn hbfix
  set JY : Subgroup Y := J.map K.subtype with hJY
  have hJe : ∀ j ∈ JY, e * j = j * e := by
    rintro _ ⟨j, hj, rfl⟩
    have h1 := congrArg Subtype.val (hJfix j hj)
    rw [hE] at h1
    exact mul_inv_eq_iff_eq_mul.1 h1
  have hcentJ : ∀ g : Y, (∀ j ∈ JY, g * j = j * g) → g ∈ normalizer (JY : Set Y) := fun g hg =>
    Subgroup.centralizer_le_normalizer (JY : Set Y)
      (Subgroup.mem_centralizer_iff.2 fun h hh => (hg h hh).symm)
  let B' : Subgroup Y := centralizer ({e} : Set Y) ⊓ normalizer (JY : Set Y)
  have heB : e ∈ B' :=
    ⟨Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      rw [hh], hcentJ e hJe⟩
  have hbB : b ∈ B' :=
    ⟨Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact hbe, mem_normalizer_map_subtype hbJ⟩
  have hJB : JY ≤ B' := fun x hx =>
    ⟨Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact hJe x hx, Subgroup.le_normalizer hx⟩
  have hsec : SecOfG G z ↥B' ⟨b, hbB⟩ := SecOfG.sub hY B' hbB
  let J' : Subgroup ↥B' := JY.subgroupOf B'
  have hJ'n : J'.Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have := (Subgroup.mem_normalizer_iff.1 g.2.2 (x : Y)).1 hx
    simpa using this⟩
  let θ : ↥J' ≃* ↥J :=
    (Subgroup.subgroupOfEquivOfLe hJB).trans
      (J.equivMapOfInjective K.subtype K.subtype_injective).symm
  have hmem : ∀ x : ↥J, (φ.comp J.subtype) x ∈ Q := fun x => by
    rw [← hJφ]
    exact Subgroup.mem_map_of_mem φ x.2
  let ψ0 : ↥J →* ↥Q := (φ.comp J.subtype).codRestrict Q hmem
  let ψJ : ↥J →* projectiveSL 3 F0 := e0.symm.toMonoidHom.comp ψ0
  have hψJs : Function.Surjective ψJ := by
    intro s
    have hs : ((e0 s : ↥Q) : projectiveSL 3 F) ∈ J.map φ := by
      rw [hJφ]
      exact (e0 s).2
    obtain ⟨x, hx, hxs⟩ := hs
    refine ⟨⟨x, hx⟩, ?_⟩
    have : ψ0 ⟨x, hx⟩ = e0 s := Subtype.ext hxs
    change e0.symm (ψ0 ⟨x, hx⟩) = s
    rw [this]
    exact e0.symm_apply_apply s
  have hψJk : ∀ x : ↥J, ψJ x = 1 → φ ((x : ↥J) : ↥K) = 1 := by
    intro x hx
    have h1 : ψ0 x = 1 := by
      have : e0.symm (ψ0 x) = 1 := hx
      exact (MulEquiv.map_eq_one_iff e0.symm).1 this
    exact congrArg Subtype.val h1
  let ψ' : ↥J' →* projectiveSL 3 F0 := ψJ.comp θ.toMonoidHom
  have hψ's : Function.Surjective ψ' := hψJs.comp θ.surjective
  have hker' : ψ'.ker ≤ center ↥J' := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 : φ (((θ x : ↥J)) : ↥K) = 1 := hψJk (θ x) hx
    have hc : (((θ x : ↥J)) : ↥K) ∈ center ↥K := by
      rw [← hφk]
      exact h1
    have := Subgroup.mem_center_iff.1 hc (((θ y : ↥J)) : ↥K)
    apply θ.injective
    rw [map_mul, map_mul]
    exact Subtype.ext this
  have hodd' : Odd (Nat.card ψ'.ker) := by
    let ι : ↥ψ'.ker →* ↥φ.ker :=
      ((J.subtype.comp θ.toMonoidHom).comp ψ'.ker.subtype).codRestrict φ.ker (fun x => by
        exact hψJk (θ x.1) x.2)
    have hι : Function.Injective ι := by
      intro x y hxy
      have h1 := congrArg Subtype.val hxy
      have h2 : θ x.1 = θ y.1 := Subtype.ext h1
      exact Subtype.ext (θ.injective h2)
    exact Odd.of_dvd_nat hkerodd (Subgroup.card_dvd_of_injective ι hι)
  have hperfJ : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.2 hJp
  have hperf' : Group.IsPerfect ↥J' :=
    Group.IsPerfect.ofSurjective (f := θ.symm.toMonoidHom) θ.symm.surjective
  have hquasi : IsQuasisimple ↥J' := isQuasisimple_of_cover ψ' hperf' hψ's hker'
  have hcomp : IsComponent J' := ⟨hquasi, hJ'n.isSubnormal⟩
  have hLie : LieModel (Hat J') .PSL 3 p n0 :=
    lieModel_hat_of_cover ψ' hp hn0 hF0card h2F0 hψ's hodd'
  have hodd'' : Odd (p ^ n0) := (hp.odd_of_ne_two hp2).pow
  have hord : orderOf (⟨e, heB⟩ : ↥B') = 2 :=
    orderOf_eq_prime (by apply Subtype.ext; simpa [pow_two] using he2)
      (fun h => he1 (congrArg Subtype.val h))
  have hcent : (⟨e, heB⟩ : ↥B') ∈ centralizer (J' : Set ↥B') := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    apply Subtype.ext
    exact (hJe (h : Y) (Subgroup.mem_subgroupOf.1 hh)).symm
  exact F4.f3 ↥B' ⟨b, hbB⟩ hsec J' hcomp p n0 hp hn0 (Or.inl hodd'') hLie ⟨e, heB⟩ hord hcent

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
