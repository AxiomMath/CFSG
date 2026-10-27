module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888M3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888B3g
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888GT2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {G : Type} [Group G] {z : G} {K : Fin 4 → Subgroup G}

private lemma w1_mem_conjugate_iff {X : Type*} [Group X] {H : Subgroup X} {g x : X} :
    x ∈ CFSG.conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    have h : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
    simpa [h] using ha
  · intro h
    exact ⟨g * x * g⁻¹, h, by simp [mul_assoc]⟩

private lemma w1_conjugate_subgroupOf {X : Type*} [Group X] (Hc : Subgroup X) (x : Hc)
    (A : Subgroup X) :
    CFSG.conjugate (A.subgroupOf Hc) x = (CFSG.conjugate A (x : X)).subgroupOf Hc := by
  ext u
  rw [Subgroup.mem_subgroupOf, w1_mem_conjugate_iff, w1_mem_conjugate_iff,
    Subgroup.mem_subgroupOf]
  simp

private lemma w1_coe_mem_zpowers {X : Type*} [Group X] (H : Subgroup X) {h c : H}
    (hc : c ∈ Subgroup.zpowers h) : (c : X) ∈ Subgroup.zpowers (h : X) := by
  have hm : (Subgroup.zpowers h).map H.subtype = Subgroup.zpowers (h : X) :=
    MonoidHom.map_zpowers H.subtype h
  rw [← hm, Subgroup.mem_map]
  exact ⟨c, hc, rfl⟩

private lemma w1_mem_zpowers_subgroupOf {X : Type*} [Group X] (H : Subgroup X) {h c : H}
    (hc : (c : X) ∈ Subgroup.zpowers (h : X)) : c ∈ Subgroup.zpowers h := by
  have hm : (Subgroup.zpowers h).map H.subtype = Subgroup.zpowers (h : X) :=
    MonoidHom.map_zpowers H.subtype h
  rw [← hm, Subgroup.mem_map] at hc
  obtain ⟨c', hc', hcc'⟩ := hc
  rw [show c' = c from Subtype.ext hcc'] at hc'
  exact hc'

private lemma w1_alpha_mem_centralizer_planeV_iff
    {H X : Type} [Group H] [Group X] {z : H} {K : Fin 4 → Subgroup H} {α : H →* X}
    (hS : PlaneSetup z K α) {x : H} :
    α x ∈ centralizer (planeV hS.quad α : Set X) ↔
      ∀ q ∈ Sec5B517Q8 hS.quad, x * q * x⁻¹ * q⁻¹ ∈ zpowers z := by
  constructor
  · intro hx q hq
    have hqV : α q ∈ planeV hS.quad α := Subgroup.mem_map.mpr ⟨q, hq, rfl⟩
    have hcomm : α q * α x = α x * α q :=
      (Subgroup.mem_centralizer_iff.mp hx) (α q) hqV
    rw [← hS.ker, MonoidHom.mem_ker]
    rw [show α (x * q * x⁻¹ * q⁻¹) = α x * α q * (α x)⁻¹ * (α q)⁻¹ by
      simp only [map_mul, map_inv]]
    rw [← hcomm]
    group
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hv
    have hker : x * q * x⁻¹ * q⁻¹ ∈ α.ker := by
      rw [hS.ker]
      exact h q hq
    have h1 : α (x * q * x⁻¹ * q⁻¹) = 1 := MonoidHom.mem_ker.mp hker
    have h2 : α (x * q * x⁻¹) = α q := by
      have h1' := h1
      rw [show α (x * q * x⁻¹ * q⁻¹) = α (x * q * x⁻¹) * (α q)⁻¹ by
        simp only [map_mul, map_inv]] at h1'
      exact mul_inv_eq_one.mp h1'
    rw [show α (x * q * x⁻¹) = α x * α q * (α x)⁻¹ by
      simp only [map_mul, map_inv]] at h2
    have h3 := congrArg (· * α x) h2
    simpa [mul_assoc] using h3.symm

theorem exists_delta_of_quad [Finite G] (hq : Sec5B517Quad K z)
    (hNz : normalizer (Sec5B517Q8 hq : Set G) ≤ centralizer ({z} : Set G))
    (hperm : ∀ n ∈ normalizer (Sec5B517Q8 hq : Set G), ∀ i : Fin 4,
      ∃ j, CFSG.conjugate (K i) n = K j)
    (hparG : ∀ w ∈ normalizer (Sec5B517Q8 hq : Set G), (∀ i, CFSG.conjugate (K i) w = K i) →
      (∀ q ∈ Sec5B517Q8 hq, w * w * q * (w * w)⁻¹ * q⁻¹ ∈ zpowers z) →
        Even (Nat.card {i : Fin 4 // ∃ q ∈ twoCoreIn (K i),
          w⁻¹ * q * w ≠ q ∧ w⁻¹ * q * w ≠ q * z}))
    {U : Subgroup G} (hU : U ≤ normalizer (Sec5B517Q8 hq : Set G))
    (hab : IsElemAbelianModSub
      (centralizerMod z (normalizer (Sec5B517Q8 hq : Set G)) (Sec5B517Q8 hq)) U)
    (hcard : 16 ≤ (centralizerMod z (normalizer (Sec5B517Q8 hq : Set G))
      (Sec5B517Q8 hq)).relIndex U) :
    ∃ (e : G) (i j : Fin 4), i ≠ j ∧ e ∈ Sec5B517Q8 hq ∧ e * e = 1 ∧ e ≠ 1 ∧ e ≠ z ∧
      e ∈ K i ⊔ K j ∧ ∀ u ∈ U, ∃ r ∈ Sec5B517Q8 hq, (u * r) * e * (u * r)⁻¹ = e := by
  classical
  let Hc : Subgroup G := centralizer ({z} : Set G)
  have hz : z ∈ Hc := (zCent z).2
  have hK : ∀ i, K i ≤ Hc := fun i => le_centralizer_of_quad hq i
  let N : Subgroup G := normalizer (Sec5B517Q8 hq : Set G)
  let C : Subgroup G := centralizerMod z N (Sec5B517Q8 hq)
  have hQN : Sec5B517Q8 hq ≤ N := Subgroup.le_normalizer
  have hQH : Sec5B517Q8 hq ≤ Hc := hQN.trans hNz
  have hUH : U ≤ Hc := hU.trans hNz
  have hQ8 : Sec5B517Q8 (quad_subgroupOf hq hK hz) = (Sec5B517Q8 hq).subgroupOf Hc :=
    q8_subgroupOf hq hK hz
  have hzcenter : (⟨z, hz⟩ : Hc) ∈ Subgroup.center Hc := by
    change zCent z ∈ Subgroup.center Hc
    exact zCent_mem_center z
  haveI : (Subgroup.zpowers (⟨z, hz⟩ : Hc)).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le_of_mem hzcenter)
  let α : Hc →* Hc ⧸ Subgroup.zpowers (⟨z, hz⟩ : Hc) := QuotientGroup.mk' _
  have hS : PlaneSetup (⟨z, hz⟩ : Hc) (fun i => (K i).subgroupOf Hc) α :=
    ⟨quad_subgroupOf hq hK hz, QuotientGroup.mk'_surjective _, QuotientGroup.ker_mk' _⟩
  have hperm' : ∀ x ∈ normalizer (Sec5B517Q8 (quad_subgroupOf hq hK hz) : Set Hc),
      ∀ i : Fin 4, ∃ j, CFSG.conjugate ((K i).subgroupOf Hc) x = (K j).subgroupOf Hc := by
    intro x hx i
    have hxN : (x : G) ∈ N := by
      rw [hQ8, ← Subgroup.subgroupOf_normalizer_eq hQH] at hx
      exact Subgroup.mem_subgroupOf.1 hx
    obtain ⟨j, hj⟩ := hperm (x : G) hxN i
    exact ⟨j, by rw [w1_conjugate_subgroupOf Hc x (K i), hj]⟩
  have hpar' : ∀ w ∈ normalizer (Sec5B517Q8 (quad_subgroupOf hq hK hz) : Set Hc),
      (∀ i, CFSG.conjugate ((K i).subgroupOf Hc) w = (K i).subgroupOf Hc) →
      (∀ q ∈ Sec5B517Q8 (quad_subgroupOf hq hK hz),
        w * w * q * (w * w)⁻¹ * q⁻¹ ∈ zpowers (⟨z, hz⟩ : Hc)) →
        Even (Nat.card {i : Fin 4 // ∃ q ∈ Sec5B517Q8 (quad_subgroupOf hq hK hz) ⊓
          (K i).subgroupOf Hc, w⁻¹ * q * w ≠ q ∧
          w⁻¹ * q * w ≠ q * (⟨z, hz⟩ : Hc)}) :=
    parity_subgroupOf hq hK hz hparG
  let U' : Subgroup Hc := U.subgroupOf Hc
  have hU' : U' ≤ normalizer (Sec5B517Q8 (quad_subgroupOf hq hK hz) : Set Hc) := by
    rw [hQ8, ← Subgroup.subgroupOf_normalizer_eq hQH]
    exact Subgroup.subgroupOf_mono Hc hU
  have hab' : ∀ a ∈ U', ∀ b ∈ U',
      (∀ q ∈ Sec5B517Q8 (quad_subgroupOf hq hK hz),
        a * b * a⁻¹ * b⁻¹ * q * (a * b * a⁻¹ * b⁻¹)⁻¹ * q⁻¹ ∈
          zpowers (⟨z, hz⟩ : Hc)) ∧
      (∀ q ∈ Sec5B517Q8 (quad_subgroupOf hq hK hz),
        a * a * q * (a * a)⁻¹ * q⁻¹ ∈ zpowers (⟨z, hz⟩ : Hc)) := by
    intro a ha b hb
    have haU : (a : G) ∈ U := Subgroup.mem_subgroupOf.1 ha
    have hbU : (b : G) ∈ U := Subgroup.mem_subgroupOf.1 hb
    have habC := hab (a : G) haU (b : G) hbU
    constructor
    · intro q0 hq0
      have hqG : (q0 : G) ∈ Sec5B517Q8 hq := by
        rw [hQ8, Subgroup.mem_subgroupOf] at hq0
        exact hq0
      have h := habC.1.2.2.2 (q0 : G) hqG
      exact w1_mem_zpowers_subgroupOf Hc (by simpa using h)
    · intro q0 hq0
      have hqG : (q0 : G) ∈ Sec5B517Q8 hq := by
        rw [hQ8, Subgroup.mem_subgroupOf] at hq0
        exact hq0
      have h := habC.2.2.2.2 (q0 : G) hqG
      exact w1_mem_zpowers_subgroupOf Hc (by simpa using h)
  have hPeq : (Subgroup.comap α (centralizer (planeV (quad_subgroupOf hq hK hz) α : Set _))) ⊓
        U' = (C.subgroupOf Hc) ⊓ U' := by
    ext x
    constructor
    · rintro ⟨hxP, hxU'⟩
      have hxU : (x : G) ∈ U := Subgroup.mem_subgroupOf.1 hxU'
      have hxN : (x : G) ∈ N := hU hxU
      refine ⟨Subgroup.mem_subgroupOf.mpr ?_, hxU'⟩
      have hcomm : ∀ q0 ∈ Sec5B517Q8 hq, (x : G) * q0 * (x : G)⁻¹ * q0⁻¹ ∈ zpowers z := by
        intro q0 hq0
        have hq' : (⟨q0, hQH hq0⟩ : Hc) ∈ Sec5B517Q8 (quad_subgroupOf hq hK hz) := by
          rw [hQ8, Subgroup.mem_subgroupOf]
          exact hq0
        have h := (w1_alpha_mem_centralizer_planeV_iff hS).mp hxP (⟨q0, hQH hq0⟩ : Hc) hq'
        simpa using w1_coe_mem_zpowers Hc h
      exact ⟨hxN, x.2, hxN, hcomm⟩
    · rintro ⟨hxC, hxU'⟩
      refine ⟨?_, hxU'⟩
      apply (w1_alpha_mem_centralizer_planeV_iff hS).mpr
      intro q hq'
      have hqG : (q : G) ∈ Sec5B517Q8 hq := by
        rw [hQ8, Subgroup.mem_subgroupOf] at hq'
        exact hq'
      have h := hxC.2.2.2 (q : G) hqG
      exact w1_mem_zpowers_subgroupOf Hc (by simpa using h)
  have hcard' : 16 ≤ (Subgroup.comap α (centralizer (planeV (quad_subgroupOf hq hK hz) α :
      Set _))).relIndex U' := by
    have h1 : (Subgroup.comap α
          (centralizer (planeV (quad_subgroupOf hq hK hz) α : Set _))).relIndex U' =
        ((Subgroup.comap α
          (centralizer (planeV (quad_subgroupOf hq hK hz) α : Set _))) ⊓ U').relIndex U' :=
      (Subgroup.inf_relIndex_right _ _).symm
    rw [h1, hPeq, Subgroup.inf_relIndex_right]
    change 16 ≤ (C.subgroupOf Hc).relIndex (U.subgroupOf Hc)
    rw [Subgroup.relIndex_subgroupOf hUH]
    exact hcard
  obtain ⟨e, i, j, hij, heQ', hee, he1, hez, heK, hfix⟩ :=
    exists_delta_of_relIndex hS hperm' hpar' hU' hab' hcard'
  refine ⟨(e : G), i, j, hij, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hQ8, Subgroup.mem_subgroupOf] at heQ'
    exact heQ'
  · simpa using congrArg Subtype.val hee
  · intro h
    exact he1 (Subtype.ext (by simpa using h))
  · intro h
    exact hez (Subtype.ext (by simpa using h))
  · have hmem : (e : G) ∈ ((K i).subgroupOf Hc ⊔ (K j).subgroupOf Hc).map Hc.subtype :=
      Subgroup.mem_map.mpr ⟨e, heK, rfl⟩
    rwa [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le (hK i),
      Subgroup.map_subgroupOf_eq_of_le (hK j)] at hmem
  · intro u hu
    have huH : u ∈ Hc := hUH hu
    have hu' : (⟨u, huH⟩ : Hc) ∈ U' := Subgroup.mem_subgroupOf.mpr hu
    obtain ⟨r, hr, hrfix⟩ := hfix (⟨u, huH⟩ : Hc) hu'
    refine ⟨(r : G), ?_, ?_⟩
    · rw [hQ8, Subgroup.mem_subgroupOf] at hr
      exact hr
    · simpa using congrArg Subtype.val hrfix

end CFSG.OddStandard.SmallF3.Omega
