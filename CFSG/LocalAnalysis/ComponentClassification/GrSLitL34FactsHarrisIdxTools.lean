module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKGField
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKG
public import CFSG.Sporadic.SmallOddCore.Assembly
public import CFSG.Sporadic.SmallOddCore.CentSpec

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup
open CFSG.ComponentClassification.HarrisLit (fixedPoints innAut twoPart mem_fixedPoints)

theorem twoPart_le_of_dvd_mul {X : Type} [Group X] [Finite X] {H : Subgroup X} {k m : ℕ}
    (hm : Odd m) (h : Nat.card H ∣ 2 ^ k * m) : twoPart H ≤ 2 ^ k := by
  have hm0 : m ≠ 0 := by rintro rfl; exact absurd hm (by decide)
  have hn0 : 2 ^ k * m ≠ 0 := mul_ne_zero (pow_ne_zero _ two_ne_zero) hm0
  have hH0 : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have hle := ((Nat.factorization_le_iff_dvd hH0 hn0).2 h) 2
  have hk : (2 ^ k * m).factorization 2 = k := by
    rw [Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hm0, Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (fun h2 => (Nat.not_even_iff_odd.2 hm)
        (even_iff_two_dvd.2 h2)), add_zero]
  rw [hk] at hle
  exact Nat.pow_le_pow_right (by norm_num) hle

theorem twoPart_top_eq {X : Type} [Group X] {k m : ℕ} (hm : Odd m)
    (h : Nat.card X = 2 ^ k * m) : twoPart (⊤ : Subgroup X) = 2 ^ k := by
  have hm0 : m ≠ 0 := by rintro rfl; exact absurd hm (by decide)
  show 2 ^ (Nat.card (⊤ : Subgroup X)).factorization 2 = 2 ^ k
  rw [Subgroup.card_top, h, Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hm0,
    Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (fun h2 => (Nat.not_even_iff_odd.2 hm)
      (even_iff_two_dvd.2 h2)), add_zero]

section Transport

variable {Y P : Type} [Group Y] [Group P] (e : Y ≃* P)

theorem congr_apply' (τ : MulAut Y) (p : P) : MulAut.congr e τ p = e (τ (e.symm p)) := rfl

theorem card_fixedPoints_congr (τ : MulAut Y) :
    Nat.card (fixedPoints (MulAut.congr e τ)) = Nat.card (fixedPoints τ) := by
  have h : fixedPoints (MulAut.congr e τ) = (fixedPoints τ).map e.toMonoidHom := by
    ext p
    rw [mem_fixedPoints, congr_apply', Subgroup.mem_map]
    constructor
    · intro hp
      refine ⟨e.symm p, ?_, by simp⟩
      rw [mem_fixedPoints]
      apply e.injective
      rw [hp, MulEquiv.apply_symm_apply]
    · rintro ⟨y, hy, rfl⟩
      rw [mem_fixedPoints] at hy
      simp [hy]
  rw [h, Subgroup.card_map_of_injective e.injective]

theorem congr_conj (y : Y) : MulAut.congr e (MulAut.conj y) = MulAut.conj (e y) := by
  ext p
  rw [congr_apply']
  simp

theorem congr_mem_innAut_iff (τ : MulAut Y) :
    MulAut.congr e τ ∈ innAut P ↔ τ ∈ innAut Y := by
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨e.symm p, ?_⟩
    apply (MulAut.congr e).injective
    rw [congr_conj, MulEquiv.apply_symm_apply]
    exact hp
  · rintro ⟨y, rfl⟩
    exact ⟨e y, (congr_conj e y).symm⟩

theorem orderOf_congr (τ : MulAut Y) : orderOf (MulAut.congr e τ) = orderOf τ :=
  MulEquiv.orderOf_eq _ τ

end Transport

section Model

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th.Native

theorem inf_centralizer_conj_eq' {M : Type*} [Group M] {P : Subgroup M} {g : M}
    (hg : ∀ p ∈ P, g * p * g⁻¹ ∈ P) (hg' : ∀ p ∈ P, g⁻¹ * p * g ∈ P) (t : M) :
    P ⊓ centralizer ({g * t * g⁻¹} : Set M) =
      (P ⊓ centralizer ({t} : Set M)).map (MulAut.conj g).toMonoidHom := by
  ext x
  simp only [mem_inf, mem_centralizer_singleton_iff, mem_map, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · rintro ⟨hxP, hx⟩
    refine ⟨g⁻¹ * x * g, ⟨hg' x hxP, ?_⟩, by group⟩
    calc g⁻¹ * x * g * t = g⁻¹ * (x * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * x) * g := by rw [hx]
      _ = t * (g⁻¹ * x * g) := by group
  · rintro ⟨y, ⟨hyP, hy⟩, rfl⟩
    refine ⟨hg y hyP, ?_⟩
    calc g * y * g⁻¹ * (g * t * g⁻¹) = g * (y * t) * g⁻¹ := by group
      _ = g * (t * y) * g⁻¹ := by rw [hy]
      _ = g * t * g⁻¹ * (g * y * g⁻¹) := by group

theorem card_fixedPoints_eq_inf_centralizer {M : Type} [Group M] {P : Subgroup M}
    {σ : MulAut ↥P} {x : M} (hσ : ∀ p : P, ((σ p : P) : M) = x * p * x⁻¹) :
    Nat.card (fixedPoints σ) = Nat.card ↥(P ⊓ centralizer ({x} : Set M)) := by
  have hmap : (fixedPoints σ).map P.subtype = P ⊓ centralizer ({x} : Set M) := by
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      have hp : σ p = p := hp
      refine ⟨p.2, mem_centralizer_singleton_iff.mpr ?_⟩
      have h1 := hσ p
      rw [hp] at h1
      calc (p : M) * x = x * p * x⁻¹ * x := by rw [← h1]
        _ = x * p := by group
    · rintro ⟨hqP, hqx⟩
      refine ⟨⟨q, hqP⟩, ?_, rfl⟩
      show σ ⟨q, hqP⟩ = ⟨q, hqP⟩
      apply Subtype.ext
      rw [hσ]
      have hqx' : q * x = x * q := mem_centralizer_singleton_iff.mp hqx
      show x * q * x⁻¹ = q
      rw [← hqx']
      group
  rw [← Subgroup.card_map_of_injective P.subtype_injective, hmap]

theorem inf_centralizer_conj_eq {M : Type*} [Group M] {P : Subgroup M} {g : M} (hg : g ∈ P)
    (t : M) : P ⊓ centralizer ({g * t * g⁻¹} : Set M) =
      (P ⊓ centralizer ({t} : Set M)).map (MulAut.conj g).toMonoidHom := by
  ext x
  simp only [mem_inf, mem_centralizer_singleton_iff, mem_map, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · rintro ⟨hxP, hx⟩
    refine ⟨g⁻¹ * x * g, ⟨P.mul_mem (P.mul_mem (P.inv_mem hg) hxP) hg, ?_⟩, by group⟩
    calc g⁻¹ * x * g * t = g⁻¹ * (x * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * x) * g := by rw [hx]
      _ = t * (g⁻¹ * x * g) := by group
  · rintro ⟨y, ⟨hyP, hy⟩, rfl⟩
    refine ⟨P.mul_mem (P.mul_mem hg hyP) (P.inv_mem hg), ?_⟩
    calc g * y * g⁻¹ * (g * t * g⁻¹) = g * (y * t) * g⁻¹ := by group
      _ = g * (t * y) * g⁻¹ := by rw [hy]
      _ = g * t * g⁻¹ * (g * y * g⁻¹) := by group

theorem exists_row_of_autModel {n : ℕ} {P R : Subgroup (Equiv.Perm (Fin n))}
    (h : AutModel P R) {rows : List ClassRow}
    (hrows : ∀ r ∈ rows, tp n r.rep ∈ R ∧ (r.outer = true ↔ tp n r.rep ∉ P) ∧
      Nat.card ↥(P ⊓ centralizer ({tp n r.rep} : Set (Equiv.Perm (Fin n)))) = r.centOrder)
    (hcover : ∀ t ∈ R, orderOf t = 2 → ∃ r ∈ rows, ∃ g ∈ P, t = g * tp n r.rep * g⁻¹)
    {σ : MulAut ↥P} (hσ : orderOf σ = 2) :
    ∃ r ∈ rows, Nat.card (fixedPoints σ) = r.centOrder ∧ (σ ∈ innAut ↥P ↔ r.outer = false) := by
  set x := h.elt σ with hxdef
  have hxR : x ∈ R := h.elt_mem σ
  have hx2 : orderOf x = 2 := by
    rw [hxdef, ← h.hom_apply, orderOf_injective h.hom h.hom_injective, hσ]
  obtain ⟨r, hr, g, hg, hxg⟩ := hcover x hxR hx2
  obtain ⟨-, hout, hcard⟩ := hrows r hr
  refine ⟨r, hr, ?_, ?_⟩
  ·
    have hconj : P ⊓ centralizer ({x} : Set (Equiv.Perm (Fin n))) =
        (P ⊓ centralizer ({tp n r.rep} : Set _)).map (MulAut.conj g).toMonoidHom := by
      rw [hxg]
      exact inf_centralizer_conj_eq hg _
    rw [card_fixedPoints_eq_inf_centralizer (h.elt_spec σ), ← hxdef, hconj,
      Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard]
  ·
    have hxP : σ ∈ innAut ↥P ↔ x ∈ P := by
      constructor
      · rintro ⟨p, hp⟩
        have hx : x = p := h.elt_eq (h.le p.2) fun q => by
          rw [← hp, MulAut.conj_apply]
          rfl
        rw [hx]
        exact p.2
      · intro hx
        refine ⟨⟨x, hx⟩, ?_⟩
        ext q
        rw [MulAut.conj_apply, h.elt_spec σ q, ← hxdef]
        rfl
    have htP : x ∈ P ↔ tp n r.rep ∈ P := by
      rw [hxg]
      constructor
      · intro hm
        have := P.mul_mem (P.mul_mem (P.inv_mem hg) hm) hg
        rwa [show g⁻¹ * (g * tp n r.rep * g⁻¹) * g = tp n r.rep by group] at this
      · intro hm
        exact P.mul_mem (P.mul_mem hg hm) (P.inv_mem hg)
    rw [hxP, htP]
    cases hro : r.outer
    · rw [hro, Bool.false_eq_true, false_iff, not_not] at hout
      simp [hout]
    · rw [hro] at hout
      simp [hout.1 rfl]

end Model

section Quotient

variable {Y : Type} [Group Y]

theorem map_center_eq (τ : MulAut Y) : (center Y).map (τ : Y →* Y) = center Y := by
  have key : ∀ (α : MulAut Y) (z : Y), z ∈ center Y → α z ∈ center Y := by
    intro α z hz
    rw [mem_center_iff] at hz ⊢
    intro w
    calc w * α z = α (α.symm w * z) := by rw [map_mul, MulEquiv.apply_symm_apply]
      _ = α (z * α.symm w) := by rw [hz]
      _ = α z * w := by rw [map_mul, MulEquiv.apply_symm_apply]
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact key τ z hz
  · intro z hz
    exact ⟨τ.symm z, key τ.symm z hz, by simp⟩

@[expose] noncomputable def quotAut (τ : MulAut Y) : MulAut (Y ⧸ center Y) :=
  QuotientGroup.congr (center Y) (center Y) τ (map_center_eq τ)

theorem quotAut_mk (τ : MulAut Y) (y : Y) :
    quotAut τ (QuotientGroup.mk y) = QuotientGroup.mk (τ y) :=
  QuotientGroup.congr_mk _ _ _ _ y

theorem quotAut_mul (τ τ' : MulAut Y) : quotAut (τ * τ') = quotAut τ * quotAut τ' := by
  ext q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  simp only [MulAut.mul_apply, quotAut_mk]

theorem quotAut_one : quotAut (1 : MulAut Y) = 1 := by
  ext q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  simp only [MulAut.one_apply, quotAut_mk]

theorem quotAut_conj (y : Y) : quotAut (MulAut.conj y) = MulAut.conj (QuotientGroup.mk y) := by
  ext q
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
  simp only [quotAut_mk, MulAut.conj_apply, QuotientGroup.mk_mul, QuotientGroup.mk_inv]

theorem card_fixedPoints_dvd [Finite Y] (τ : MulAut Y) :
    Nat.card (fixedPoints τ) ∣ Nat.card (fixedPoints (quotAut τ)) * Nat.card (center Y) := by
  let f : fixedPoints τ →* fixedPoints (quotAut τ) :=
    { toFun := fun y => ⟨QuotientGroup.mk (y : Y), by
        rw [mem_fixedPoints, quotAut_mk, (mem_fixedPoints.1 y.2)]⟩
      map_one' := rfl
      map_mul' := fun a b => rfl }
  have h1 : Nat.card (fixedPoints τ) = Nat.card f.range * Nat.card f.ker := by
    rw [f.ker.card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  have h2 : Nat.card f.range ∣ Nat.card (fixedPoints (quotAut τ)) :=
    Subgroup.card_subgroup_dvd_card _
  let g : f.ker →* center Y :=
    { toFun := fun k => ⟨((k : fixedPoints τ) : Y), by
        have hk : f (k : fixedPoints τ) = 1 := k.2
        have hk' : (QuotientGroup.mk ((k : fixedPoints τ) : Y) : Y ⧸ center Y) = 1 :=
          congrArg Subtype.val hk
        exact (QuotientGroup.eq_one_iff _).1 hk'⟩
      map_one' := rfl
      map_mul' := fun a b => rfl }
  have hg : Function.Injective g := fun a b hab => by
    have h' := congrArg (fun w : center Y => (w : Y)) hab
    exact Subtype.ext (Subtype.ext h')
  have h3 : Nat.card f.ker ∣ Nat.card (center Y) := Subgroup.card_dvd_of_injective g hg
  rw [h1]
  exact Nat.mul_dvd_mul h2 h3

theorem eq_one_of_mul_inv_mem_center [Group.IsPerfect Y] {α : MulAut Y}
    (h : ∀ y, α y * y⁻¹ ∈ center Y) : α = 1 := by
  let c : Y →* center Y :=
    { toFun := fun y => ⟨α y * y⁻¹, h y⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        show α (a * b) * (a * b)⁻¹ = α a * a⁻¹ * (α b * b⁻¹)
        have hb := mem_center_iff.mp (h b) (α a * a⁻¹)
        rw [map_mul, mul_inv_rev]
        calc α a * α b * (b⁻¹ * a⁻¹) = α a * (α b * b⁻¹) * a⁻¹ := by group
          _ = α a * ((α b * b⁻¹) * a⁻¹) := by group
          _ = α a * (a⁻¹ * (α b * b⁻¹)) := by
              rw [(mem_center_iff.mp (h b) a⁻¹).symm]
          _ = α a * a⁻¹ * (α b * b⁻¹) := by group) }
  have hker : commutator Y ≤ c.ker := Abelianization.commutator_subset_ker c
  rw [Group.IsPerfect.commutator_eq_top] at hker
  ext y
  have hy : c y = 1 := hker (mem_top y)
  have hy' : α y * y⁻¹ = 1 := congrArg Subtype.val hy
  rw [MulAut.one_apply]
  exact mul_inv_eq_one.mp hy'

theorem mem_innAut_of_quotAut [Group.IsPerfect Y] {τ : MulAut Y}
    (h : quotAut τ ∈ innAut (Y ⧸ center Y)) : τ ∈ innAut Y := by
  obtain ⟨q, hq⟩ := h
  obtain ⟨y₀, rfl⟩ := QuotientGroup.mk_surjective q
  have h1 : (MulAut.conj y₀)⁻¹ * τ = 1 := by
    apply eq_one_of_mul_inv_mem_center
    intro y
    have key : (QuotientGroup.mk (τ y) : Y ⧸ center Y) =
        QuotientGroup.mk y₀ * QuotientGroup.mk y * (QuotientGroup.mk y₀)⁻¹ := by
      rw [← quotAut_mk, ← hq, MulAut.conj_apply]
    have e1 : ((MulAut.conj y₀)⁻¹ * τ) y = y₀⁻¹ * τ y * y₀⁻¹⁻¹ := by
      rw [MulAut.mul_apply, ← map_inv MulAut.conj y₀, MulAut.conj_apply]
    rw [← QuotientGroup.eq_one_iff, e1]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, key]
    group
  exact ⟨y₀, eq_of_inv_mul_eq_one h1⟩

end Quotient

end CFSG.ComponentClassification.GrSLit.L34Facts
