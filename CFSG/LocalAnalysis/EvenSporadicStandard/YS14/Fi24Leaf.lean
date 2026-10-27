module

public import CFSG.Sporadic.Fi24.Involutions
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Fi23

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.YS14

open CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Fi24

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Transport

theorem comm_of_mem_centralizer_singleton {G : Type*} [Group G] {g k : G}
    (h : k ∈ Subgroup.centralizer ({g} : Set G)) : k * g = g * k := by
  have h' := Subgroup.mem_centralizer_singleton_iff.1 h
  exact h'

theorem mem_centralizer_singleton_of_comm {G : Type*} [Group G] {g k : G}
    (h : k * g = g * k) : k ∈ Subgroup.centralizer ({g} : Set G) := by
  have h' := Subgroup.mem_centralizer_singleton_iff.2 h
  exact h'

theorem comm_of_mem_centralizer_val {G : Type*} [Group G] {K : Subgroup G} {a b : K}
    (h : a ∈ Subgroup.centralizer ({b} : Set K)) : (a : G) * (b : G) = (b : G) * (a : G) := by
  have h' := Subgroup.mem_centralizer_singleton_iff.1 h
  have h'' := congrArg Subtype.val h'
  exact h''

theorem mem_centralizer_of_val_comm {G : Type*} [Group G] {K : Subgroup G} {a b : K}
    (h : (a : G) * (b : G) = (b : G) * (a : G)) : a ∈ Subgroup.centralizer ({b} : Set K) := by
  have h' : a * b = b * a := Subtype.ext h
  have h'' := Subgroup.mem_centralizer_singleton_iff.2 h'
  exact h''

theorem fourClassesLarge_of_surjective_hom {L H : Type*} [Group L] [Finite L] [Group H]
    (ψ : L →* H) (hψ : Function.Surjective ψ) (hH : FourClassesLarge H)
    (hker : ∀ x : L, x ^ 4 = 1 → x ^ 2 ≠ 1 → ψ x ^ 2 ≠ 1) : FourClassesLarge L := by
  intro x hx4 hx2
  have h5 := hH (ψ x) (by rw [← map_pow, hx4, map_one]) (hker x hx4 hx2)
  refine le_trans h5 (Nat.card_le_card_of_surjective
    (fun y : {y : L // IsConj x y} => (⟨ψ y.1, ψ.map_isConj y.2⟩ : {h : H // IsConj (ψ x) h})) ?_)
  rintro ⟨h, hh⟩
  obtain ⟨c, hc⟩ := isConj_iff.1 hh
  obtain ⟨g, rfl⟩ := hψ c
  refine ⟨⟨g * x * g⁻¹, isConj_iff.2 ⟨g, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  show ψ (g * x * g⁻¹) = h
  simpa only [map_mul, map_inv] using hc

theorem map_centralizer_singleton_conj {G : Type*} [Group G] (c s : G) :
    (Subgroup.centralizer ({s} : Set G)).map (MulAut.conj c).toMonoidHom =
      Subgroup.centralizer ({c * s * c⁻¹} : Set G) := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    show c * y * c⁻¹ * (c * s * c⁻¹) = c * s * c⁻¹ * (c * y * c⁻¹)
    calc c * y * c⁻¹ * (c * s * c⁻¹) = c * (y * s) * c⁻¹ := by group
      _ = c * (s * y) * c⁻¹ := by rw [hy]
      _ = c * s * c⁻¹ * (c * y * c⁻¹) := by group
  · intro hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    refine Subgroup.mem_map.2 ⟨c⁻¹ * x * c, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc c⁻¹ * x * c * s = c⁻¹ * (x * (c * s * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * s * c⁻¹) * x) * c := by rw [hx]
        _ = s * (c⁻¹ * x * c) := by group
    · show c * (c⁻¹ * x * c) * c⁻¹ = x
      group

theorem fourClassesLarge_of_map_conj {G : Type*} [Group G] (c : G) (K K' : Subgroup G)
    (h : K.map (MulAut.conj c).toMonoidHom = K') (hK' : FourClassesLarge ↥K') :
    FourClassesLarge ↥K := by
  subst h
  exact FourClassesLarge.of_mulEquiv (MulEquiv.subgroupMap (MulAut.conj c) K) hK'

theorem map_conj_of_normal {G : Type*} [Group G] (N : Subgroup G) (hN : N.Normal) (c : G) :
    N.map (MulAut.conj c).toMonoidHom = N := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    exact hN.conj_mem y hy c
  · intro hx
    refine Subgroup.mem_map.2 ⟨c⁻¹ * x * c, ?_, ?_⟩
    · have h := hN.conj_mem x hx c⁻¹
      rwa [inv_inv] at h
    · show c * (c⁻¹ * x * c) * c⁻¹ = x
      group

end Transport

section Projection


open scoped Classical in
noncomputable def tProj (x : R) : R := if x ∈ MR then x else x * tR

theorem tProj_of_mem {x : R} (h : x ∈ MR) : tProj x = x := by
  rw [tProj, if_pos h]

theorem tProj_of_not_mem {x : R} (h : x ∉ MR) : tProj x = x * tR := by
  rw [tProj, if_neg h]

theorem tProj_mem {x : R} (hx : x * tR = tR * x) : tProj x ∈ MR := by
  by_cases h : x ∈ MR
  · rw [tProj_of_mem h]
    exact h
  · rw [tProj_of_not_mem h]
    exact (mem_MR_or_of_commute (mem_centralizer_singleton_of_comm hx)).resolve_left h

theorem tProj_eq_or {x : R} : x = tProj x ∨ x = tProj x * tR := by
  by_cases h : x ∈ MR
  · exact Or.inl (tProj_of_mem h).symm
  · right
    rw [tProj_of_not_mem h, mul_assoc, tR_mul_tR, mul_one]

theorem sq_mul_tR_of_commute {p : R} (hc : p * tR = tR * p) : (p * tR) ^ 2 = p ^ 2 := by
  rw [sq, sq]
  calc p * tR * (p * tR) = p * (tR * p) * tR := by simp only [mul_assoc]
    _ = p * (p * tR) * tR := by rw [← hc]
    _ = p * p * (tR * tR) := by simp only [mul_assoc]
    _ = p * p := by rw [tR_mul_tR, mul_one]

theorem tProj_sq {x : R} (hx : x * tR = tR * x) : tProj x ^ 2 = x ^ 2 := by
  have hc : tProj x * tR = tR * tProj x := commute_tR_of_mem_MR (tProj_mem hx)
  rcases tProj_eq_or (x := x) with h | h
  · rw [← h]
  · conv_rhs => rw [h]
    exact (sq_mul_tR_of_commute hc).symm

theorem tProj_mul {x y : R} (hx : x * tR = tR * x) (hy : y * tR = tR * y) :
    tProj (x * y) = tProj x * tProj y := by
  by_cases hxM : x ∈ MR <;> by_cases hyM : y ∈ MR
  · rw [tProj_of_mem hxM, tProj_of_mem hyM, tProj_of_mem (MR.mul_mem hxM hyM)]
  · have hxy : x * y ∉ MR := fun h => hyM (by
      have h' := MR.mul_mem (MR.inv_mem hxM) h
      rwa [inv_mul_cancel_left] at h')
    rw [tProj_of_not_mem hxy, tProj_of_mem hxM, tProj_of_not_mem hyM, mul_assoc]
  · have hcy : y * tR = tR * y := commute_tR_of_mem_MR hyM
    have hxy : x * y ∉ MR := fun h => hxM (by
      have h' := MR.mul_mem h (MR.inv_mem hyM)
      rwa [mul_inv_cancel_right] at h')
    rw [tProj_of_not_mem hxy, tProj_of_not_mem hxM, tProj_of_mem hyM, mul_assoc x tR y,
      ← hcy, mul_assoc]
  · have hxt : x * tR ∈ MR :=
      (mem_MR_or_of_commute (mem_centralizer_singleton_of_comm hx)).resolve_left hxM
    have hyt : y * tR ∈ MR :=
      (mem_MR_or_of_commute (mem_centralizer_singleton_of_comm hy)).resolve_left hyM
    have hxy : x * tR * (y * tR) = x * y := by
      calc x * tR * (y * tR) = x * (tR * y) * tR := by simp only [mul_assoc]
        _ = x * (y * tR) * tR := by rw [← hy]
        _ = x * y * (tR * tR) := by simp only [mul_assoc]
        _ = x * y := by rw [tR_mul_tR, mul_one]
    have hxyM : x * y ∈ MR := by
      rw [← hxy]
      exact MR.mul_mem hxt hyt
    rw [tProj_of_mem hxyM, tProj_of_not_mem hxM, tProj_of_not_mem hyM, hxy]

theorem tProj_comm {x r : R} (hx : x * tR = tR * x) (hr : r * tR = tR * r) (hxr : x * r = r * x) :
    tProj x * tProj r = tProj r * tProj x := by
  rw [← tProj_mul hx hr, ← tProj_mul hr hx, hxr]

theorem mem_MR_of_JR_of_commute {x : R} (hxJ : x ∈ JR) (hxT : x * tR = tR * x) : x ∈ MR := by
  rcases mem_MR_or_of_commute (mem_centralizer_singleton_of_comm hxT) with h | h
  · exact h
  · exfalso
    apply tR_not_mem_JR
    rw [← inv_mul_cancel_left x tR]
    exact JR.mul_mem (JR.inv_mem hxJ) (MR_le_JR h)

end Projection

section Leaf


theorem fourClassesLarge_centralizer_MR {ρ : MR} (h2 : ρ ^ 2 = 1) (h1 : ρ ≠ 1) :
    FourClassesLarge ↥(Subgroup.centralizer ({ρ} : Set MR)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hv : orderOf (fi23EquivJMR ρ) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime h2 h1
  have e := @centralizerEquiv ↥MR ↥CFSG.Sporadic.Fi23.J (Subgroup.toGroup MR)
    (Subgroup.toGroup CFSG.Sporadic.Fi23.J) fi23EquivJMR ρ
  have hF := CFSG.EvenSporadicStandard.HypOne.Fi23.fourClassesLarge_J (fi23EquivJMR ρ) hv
  have hL := @FourClassesLarge.of_mulEquiv _ _
    (Subgroup.toGroup (Subgroup.centralizer ({ρ} : Set MR)))
    (Subgroup.toGroup (Subgroup.centralizer ({fi23EquivJMR ρ} : Set CFSG.Sporadic.Fi23.J))) e hF
  exact hL

theorem fourClassesLarge_leaf_tR {r : R} (hr2 : r * r = 1) (hrT : r * tR = tR * r)
    (hr1 : r ≠ 1) (hrt : r ≠ tR) :
    FourClassesLarge ↥(Subgroup.centralizer ({r} : Set R) ⊓ Subgroup.centralizer ({tR} : Set R)) := by
  have hrP : tProj r ∈ MR := tProj_mem hrT
  let ρ : MR := ⟨tProj r, hrP⟩
  have hρ2 : ρ ^ 2 = 1 := by
    apply Subtype.ext
    show tProj r ^ 2 = 1
    rw [tProj_sq hrT, sq, hr2]
  have hρ1 : ρ ≠ 1 := by
    intro h
    have h' : tProj r = 1 := congrArg Subtype.val h
    rcases tProj_eq_or (x := r) with e | e
    · exact hr1 (e.trans h')
    · exact hrt (by rw [e, h', one_mul])
  have hxC : ∀ x : ↥(Subgroup.centralizer ({r} : Set R) ⊓ Subgroup.centralizer ({tR} : Set R)),
      x.1 * tR = tR * x.1 := fun x => by
    have h := comm_of_mem_centralizer_singleton (Subgroup.mem_inf.1 x.2).2
    exact h
  have hxr : ∀ x : ↥(Subgroup.centralizer ({r} : Set R) ⊓ Subgroup.centralizer ({tR} : Set R)),
      x.1 * r = r * x.1 := fun x => by
    have h := comm_of_mem_centralizer_singleton (Subgroup.mem_inf.1 x.2).1
    exact h
  have hψmem : ∀ x : ↥(Subgroup.centralizer ({r} : Set R) ⊓ Subgroup.centralizer ({tR} : Set R)),
      (⟨tProj x.1, tProj_mem (hxC x)⟩ : MR) ∈ Subgroup.centralizer ({ρ} : Set MR) := by
    intro x
    apply mem_centralizer_of_val_comm
    exact tProj_comm (hxC x) hrT (hxr x)
  let ψ : ↥(Subgroup.centralizer ({r} : Set R) ⊓ Subgroup.centralizer ({tR} : Set R)) →*
      ↥(Subgroup.centralizer ({ρ} : Set MR)) :=
    MonoidHom.mk' (fun x => ⟨⟨tProj x.1, tProj_mem (hxC x)⟩, hψmem x⟩) (fun a b => by
      apply Subtype.ext
      apply Subtype.ext
      exact tProj_mul (hxC a) (hxC b))
  have hψsurj : Function.Surjective ψ := by
    rintro ⟨⟨z, hzM⟩, hz⟩
    have key0 := comm_of_mem_centralizer_val hz
    have key : z * tProj r = tProj r * z := key0
    have hzC : z * tR = tR * z := commute_tR_of_mem_MR hzM
    have hzr : z * r = r * z := by
      rcases tProj_eq_or (x := r) with e | e
      · calc z * r = z * tProj r := by rw [← e]
          _ = tProj r * z := key
          _ = r * z := by rw [← e]
      · rw [e]
        calc z * (tProj r * tR) = (z * tProj r) * tR := by rw [mul_assoc]
          _ = (tProj r * z) * tR := by rw [key]
          _ = tProj r * (z * tR) := by rw [mul_assoc]
          _ = tProj r * (tR * z) := by rw [hzC]
          _ = tProj r * tR * z := by rw [mul_assoc]
    refine ⟨⟨z, Subgroup.mem_inf.2 ⟨mem_centralizer_singleton_of_comm hzr,
      mem_centralizer_singleton_of_comm hzC⟩⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact tProj_of_mem hzM
  have hker : ∀ x : ↥(Subgroup.centralizer ({r} : Set R) ⊓ Subgroup.centralizer ({tR} : Set R)),
      x ^ 4 = 1 → x ^ 2 ≠ 1 → ψ x ^ 2 ≠ 1 := by
    intro x _ hx2 h
    apply hx2
    apply Subtype.ext
    have h' := congrArg (fun w : ↥(Subgroup.centralizer ({ρ} : Set MR)) => ((w : MR) : R)) h
    have h'' : tProj x.1 ^ 2 = 1 := h'
    rw [tProj_sq (hxC x)] at h''
    simpa using h''
  have hL := fourClassesLarge_of_surjective_hom ψ hψsurj
    (fourClassesLarge_centralizer_MR hρ2 hρ1) hker
  exact hL

theorem fourClassesLarge_leaf_tR_J {r : R} (hrJ : r ∈ JR) (hr2 : r * r = 1)
    (hrT : r * tR = tR * r) (hr1 : r ≠ 1) :
    FourClassesLarge ↥(Subgroup.centralizer ({r} : Set R) ⊓ JR ⊓
      Subgroup.centralizer ({tR} : Set R)) := by
  have hrM : r ∈ MR := mem_MR_of_JR_of_commute hrJ hrT
  let ρ : MR := ⟨r, hrM⟩
  have hρ2 : ρ ^ 2 = 1 := by
    apply Subtype.ext
    show r ^ 2 = 1
    rw [sq, hr2]
  have hρ1 : ρ ≠ 1 := fun h => hr1 (congrArg Subtype.val h)
  have hmap : Subgroup.centralizer ({r} : Set R) ⊓ JR ⊓ Subgroup.centralizer ({tR} : Set R) =
      (Subgroup.centralizer ({ρ} : Set MR)).map MR.subtype := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxRJ, hxt⟩ := Subgroup.mem_inf.1 hx
      obtain ⟨hxr, hxJ⟩ := Subgroup.mem_inf.1 hxRJ
      have hxt' := comm_of_mem_centralizer_singleton hxt
      have hxM : x ∈ MR := mem_MR_of_JR_of_commute hxJ hxt'
      have hxr' := comm_of_mem_centralizer_singleton hxr
      have hmem : (⟨x, hxM⟩ : MR) ∈ Subgroup.centralizer ({ρ} : Set MR) :=
        mem_centralizer_of_val_comm hxr'
      exact Subgroup.mem_map.2 ⟨⟨x, hxM⟩, hmem, rfl⟩
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
      have hyr0 := comm_of_mem_centralizer_val hy
      have hyr : (y : R) * r = r * (y : R) := hyr0
      have hyC := mem_centralizer_singleton_of_comm (G := R) hyr
      have hyT := mem_centralizer_singleton_of_comm (G := R) (commute_tR_of_mem_MR y.2)
      have hyRJ : (y : R) ∈ Subgroup.centralizer ({r} : Set R) ⊓ JR :=
        Subgroup.mem_inf.2 ⟨hyC, MR_le_JR y.2⟩
      exact Subgroup.mem_inf.2 ⟨hyRJ, hyT⟩
  have hC := fourClassesLarge_centralizer_MR hρ2 hρ1
  have e₁ := MulEquiv.subgroupCongr hmap
  have e₂ := (Subgroup.equivMapOfInjective (Subgroup.centralizer ({ρ} : Set MR)) MR.subtype
    MR.subtype_injective).symm
  have e := e₁.trans e₂
  have hL := @FourClassesLarge.of_mulEquiv _ _
    (Subgroup.toGroup (Subgroup.centralizer ({r} : Set R) ⊓ JR ⊓ Subgroup.centralizer ({tR} : Set R)))
    (Subgroup.toGroup (Subgroup.centralizer ({ρ} : Set MR))) e hC
  exact hL

theorem fourClassesLarge_leaf_D24 {r u : R} (hu : u ∈ D24) (hr2 : r * r = 1)
    (hru : r * u = u * r) (hr1 : r ≠ 1) (hrne : r ≠ u) :
    FourClassesLarge ↥(Subgroup.centralizer ({r} : Set R) ⊓ Subgroup.centralizer ({u} : Set R)) := by
  obtain ⟨g, hg⟩ := exists_conj_eq_tR hu
  set c : R := jR g with hcdef
  have hmap : (Subgroup.centralizer ({r} : Set R) ⊓ Subgroup.centralizer ({u} : Set R)).map
      (MulAut.conj c).toMonoidHom =
        Subgroup.centralizer ({c * r * c⁻¹} : Set R) ⊓ Subgroup.centralizer ({tR} : Set R) := by
    rw [Subgroup.map_inf _ _ (MulAut.conj c).toMonoidHom (MulAut.conj c).injective,
      map_centralizer_singleton_conj, map_centralizer_singleton_conj, hg]
  have hr2' : c * r * c⁻¹ * (c * r * c⁻¹) = 1 := by
    calc c * r * c⁻¹ * (c * r * c⁻¹) = c * (r * r) * c⁻¹ := by group
      _ = 1 := by rw [hr2]; group
  have hrT' : c * r * c⁻¹ * tR = tR * (c * r * c⁻¹) := by
    rw [← hg]
    calc c * r * c⁻¹ * (c * u * c⁻¹) = c * (r * u) * c⁻¹ := by group
      _ = c * (u * r) * c⁻¹ := by rw [hru]
      _ = c * u * c⁻¹ * (c * r * c⁻¹) := by group
  have hr1' : c * r * c⁻¹ ≠ 1 := by
    intro h
    apply hr1
    calc r = c⁻¹ * (c * r * c⁻¹) * c := by group
      _ = 1 := by rw [h]; group
  have hrt' : c * r * c⁻¹ ≠ tR := by
    intro h
    apply hrne
    calc r = c⁻¹ * (c * r * c⁻¹) * c := by group
      _ = c⁻¹ * (c * u * c⁻¹) * c := by rw [h, hg]
      _ = u := by group
  exact fourClassesLarge_of_map_conj c _ _ hmap
    (fourClassesLarge_leaf_tR hr2' hrT' hr1' hrt')

theorem fourClassesLarge_leaf_D24_J {r u : R} (hu : u ∈ D24) (hrJ : r ∈ JR) (hr2 : r * r = 1)
    (hru : r * u = u * r) (hr1 : r ≠ 1) :
    FourClassesLarge ↥(Subgroup.centralizer ({r} : Set R) ⊓ JR ⊓
      Subgroup.centralizer ({u} : Set R)) := by
  obtain ⟨g, hg⟩ := exists_conj_eq_tR hu
  set c : R := jR g with hcdef
  have hmap : (Subgroup.centralizer ({r} : Set R) ⊓ JR ⊓ Subgroup.centralizer ({u} : Set R)).map
      (MulAut.conj c).toMonoidHom =
        Subgroup.centralizer ({c * r * c⁻¹} : Set R) ⊓ JR ⊓ Subgroup.centralizer ({tR} : Set R) := by
    rw [Subgroup.map_inf _ _ (MulAut.conj c).toMonoidHom (MulAut.conj c).injective,
      Subgroup.map_inf _ _ (MulAut.conj c).toMonoidHom (MulAut.conj c).injective,
      map_centralizer_singleton_conj, map_centralizer_singleton_conj,
      map_conj_of_normal JR normal_JR c, hg]
  have hrJ' : c * r * c⁻¹ ∈ JR := normal_JR.conj_mem r hrJ c
  have hr2' : c * r * c⁻¹ * (c * r * c⁻¹) = 1 := by
    calc c * r * c⁻¹ * (c * r * c⁻¹) = c * (r * r) * c⁻¹ := by group
      _ = 1 := by rw [hr2]; group
  have hrT' : c * r * c⁻¹ * tR = tR * (c * r * c⁻¹) := by
    rw [← hg]
    calc c * r * c⁻¹ * (c * u * c⁻¹) = c * (r * u) * c⁻¹ := by group
      _ = c * (u * r) * c⁻¹ := by rw [hru]
      _ = c * u * c⁻¹ * (c * r * c⁻¹) := by group
  have hr1' : c * r * c⁻¹ ≠ 1 := by
    intro h
    apply hr1
    calc r = c⁻¹ * (c * r * c⁻¹) * c := by group
      _ = 1 := by rw [h]; group
  exact fourClassesLarge_of_map_conj c _ _ hmap
    (fourClassesLarge_leaf_tR_J hrJ' hr2' hrT' hr1')

end Leaf

end CFSG.EvenSporadicStandard.YS14
