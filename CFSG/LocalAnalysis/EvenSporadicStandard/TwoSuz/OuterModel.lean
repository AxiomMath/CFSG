module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.OuterPerfect
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.InnerAbs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Suz

public section

namespace CFSG.EvenSporadicStandard.TwoSuz

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.SuzOddCore (suzM suzT suzInv suzEquivM)
open CFSG.EvenSporadicStandard.HypOne.Suz (autEquiv autEquiv_apply cover_outer)
open scoped commutatorElement

section SetupHelpers

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z : G}

theorem Setup.outer_orderOf_t (h : Setup G L z) : orderOf (⟨z, h.zmem⟩ : ↥L) = 2 :=
  (Subgroup.orderOf_mk z h.zmem).trans h.z_order

theorem Setup.outer_center_eq_zpowers (h : Setup G L z) :
    center ↥L = zpowers (⟨z, h.zmem⟩ : ↥L) := by
  have hle : zpowers (⟨z, h.zmem⟩ : ↥L) ≤ center ↥L := zpowers_le.2 h.mem_center
  have hfin : Finite (center ↥L) := Nat.finite_of_card_ne_zero (by rw [h.card_center]; omega)
  symm
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Nat.card_zpowers, h.outer_orderOf_t, h.card_center]

theorem Setup.outer_le_commutator (h : Setup G L z) : L ≤ ⁅L, L⁆ := by
  rw [← Subgroup.map_subtype_commutator, h.perfect, Subgroup.map_top, Subgroup.range_subtype]

theorem Setup.outer_conj_mem (h : Setup G L z) {y : G} (hy : y ∈ centralizer ({z} : Set G)) {l : G}
    (hl : l ∈ L) : y * l * y⁻¹ ∈ L :=
  (mem_set_normalizer_iff.1 (h.cent_le_norm hy) l).1 hl

@[expose] def Setup.outerConjHom (h : Setup G L z) {y : G} (hy : y ∈ centralizer ({z} : Set G)) :
    ↥L →* ↥L where
  toFun l := ⟨y * l * y⁻¹, h.outer_conj_mem hy l.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem Setup.outerConjHom_apply (h : Setup G L z) {y : G} (hy : y ∈ centralizer ({z} : Set G))
    (l : ↥L) : ((h.outerConjHom hy l : ↥L) : G) = y * l * y⁻¹ := rfl

theorem Setup.outerConjHom_t (h : Setup G L z) {y : G} (hy : y ∈ centralizer ({z} : Set G)) :
    h.outerConjHom hy ⟨z, h.zmem⟩ = ⟨z, h.zmem⟩ := by
  refine Subtype.ext ?_
  have := mem_centralizer_singleton_iff.1 hy
  rw [Setup.outerConjHom_apply]
  show y * z * y⁻¹ = z
  rw [this]
  group

end SetupHelpers

section Induced

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z : G}

theorem Setup.outer_ker_le_conjHom (h : Setup G L z) (q : ↥L →* suzM)
    (hker : q.ker = zpowers (⟨z, h.zmem⟩ : ↥L)) {y : G} (hy : y ∈ centralizer ({z} : Set G)) :
    q.ker ≤ (q.comp (h.outerConjHom hy)).ker := by
  intro l hl
  have hl' := hl
  rw [hker] at hl
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hl
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, map_zpow, Setup.outerConjHom_t]
  exact hl'

@[expose] noncomputable def Setup.outerInduced (h : Setup G L z) (q : ↥L →* suzM)
    (hq : Function.Surjective q) (hker : q.ker = zpowers (⟨z, h.zmem⟩ : ↥L)) {y : G}
    (hy : y ∈ centralizer ({z} : Set G)) : suzM →* suzM :=
  MonoidHom.liftOfSurjective q hq
    ⟨q.comp (h.outerConjHom hy), Setup.outer_ker_le_conjHom h q hker hy⟩

theorem Setup.outerInduced_apply (h : Setup G L z) (q : ↥L →* suzM) (hq : Function.Surjective q)
    (hker : q.ker = zpowers (⟨z, h.zmem⟩ : ↥L)) {y : G} (hy : y ∈ centralizer ({z} : Set G))
    (l : ↥L) : h.outerInduced q hq hker hy (q l) = q (h.outerConjHom hy l) :=
  MonoidHom.liftOfRightInverse_comp_apply q _ (Function.rightInverse_surjInv hq) _ l

theorem Setup.outer_mem_zpowers_of_q_eq (h : Setup G L z) (q : ↥L →* suzM)
    (hker : q.ker = zpowers (⟨z, h.zmem⟩ : ↥L)) {a b : ↥L} (hab : q a = q b) :
    ((a : G) * (b : G)⁻¹) ∈ zpowers z := by
  have h1 : a * b⁻¹ ∈ q.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hab, mul_inv_cancel]
  rw [hker] at h1
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h1
  exact mem_zpowers_iff.2 ⟨k, by
    have := congrArg (fun x : ↥L => (x : G)) hk
    simpa using this⟩

theorem Setup.outer_exists_mulAut (h : Setup G L z) (q : ↥L →* suzM) (hq : Function.Surjective q)
    (hker : q.ker = zpowers (⟨z, h.zmem⟩ : ↥L)) {y : G} (hy : y ∈ centralizer ({z} : Set G)) :
    ∃ α : MulAut suzM, ∀ l : ↥L, α (q l) = q (h.outerConjHom hy l) := by
  have hy' : y⁻¹ ∈ centralizer ({z} : Set G) := (centralizer ({z} : Set G)).inv_mem hy
  have h1 : ∀ l : ↥L, h.outerConjHom hy' (h.outerConjHom hy l) = l := fun l =>
    Subtype.ext (by simp only [Setup.outerConjHom_apply]; group)
  have h2 : ∀ l : ↥L, h.outerConjHom hy (h.outerConjHom hy' l) = l := fun l =>
    Subtype.ext (by simp only [Setup.outerConjHom_apply]; group)
  refine ⟨MonoidHom.toMulEquiv (h.outerInduced q hq hker hy)
    (h.outerInduced q hq hker hy') ?_ ?_, ?_⟩
  · refine MonoidHom.ext fun m => ?_
    obtain ⟨l, rfl⟩ := hq m
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, Setup.outerInduced_apply _ q hq hker, h1]
  · refine MonoidHom.ext fun m => ?_
    obtain ⟨l, rfl⟩ := hq m
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, Setup.outerInduced_apply _ q hq hker, h2]
  · intro l
    exact Setup.outerInduced_apply h q hq hker hy l

end Induced

section Quotient


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z : G}

theorem Setup.outer_exists_q (h : Setup G L z) :
    ∃ q : ↥L →* suzM, Function.Surjective q ∧ q.ker = zpowers (⟨z, h.zmem⟩ : ↥L) := by
  obtain ⟨e⟩ := h.quot
  let f : (↥L ⧸ center ↥L) ≃* suzM := e.trans suzEquivM
  refine ⟨f.toMonoidHom.comp (QuotientGroup.mk' (center ↥L)),
    f.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
  rw [← h.outer_center_eq_zpowers]
  ext x
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    QuotientGroup.mk'_apply]
  rw [map_eq_one_iff _ f.injective, QuotientGroup.eq_one_iff]

end Quotient

section Main


theorem exists_perfect_of_outer_elt {G : Type} [Group G] [Finite G] {L : Subgroup G} {z : G}
    (h : Setup G L z) (hC : centralizer (L : Set G) = zpowers z) {y : G}
    (hy : y ∈ centralizer ({z} : Set G)) (hy2 : orderOf y = 2) (hyL : y ∉ L) :
    ∃ P : Subgroup G, P ≤ centralizer ({z} : Set G) ⊓ centralizer ({y} : Set G) ∧
      P ≤ ⁅P, P⁆ ∧ z ∈ P := by
  have : Group.IsPerfect ↥L := Group.isPerfect_def.2 h.perfect
  obtain ⟨q, hq, hker⟩ := h.outer_exists_q
  have ht2 : orderOf (⟨z, h.zmem⟩ : ↥L) = 2 := h.outer_orderOf_t
  have hcen : zpowers (⟨z, h.zmem⟩ : ↥L) ≤ center ↥L := zpowers_le.2 h.mem_center
  have hyy : y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy2, sq] at this
  obtain ⟨α, hα⟩ := h.outer_exists_mulAut q hq hker hy
  obtain ⟨τ, hτ⟩ := autEquiv.surjective α
  have hτapply : ∀ l : ↥L, ((q (h.outerConjHom hy l) : suzM) : Equiv.Perm (Fin 1782)) =
      (τ : Equiv.Perm (Fin 1782)) * (q l : Equiv.Perm (Fin 1782)) *
        (τ : Equiv.Perm (Fin 1782))⁻¹ := fun l => by
    rw [← hα l, ← hτ]
    exact autEquiv_apply τ (q l)
  have hττ : τ * τ = 1 := by
    refine autEquiv.injective ?_
    rw [map_mul, hτ, map_one]
    refine MulEquiv.ext fun m => ?_
    obtain ⟨l, rfl⟩ := hq m
    rw [MulAut.mul_apply, hα, hα, MulAut.one_apply]
    congr 1
    refine Subtype.ext ?_
    simp only [Setup.outerConjHom_apply]
    calc y * (y * (l : G) * y⁻¹) * y⁻¹ = (y * y) * l * (y * y)⁻¹ := by group
      _ = l := by rw [hyy]; group
  have hτ1 : (τ : Equiv.Perm (Fin 1782)) * (τ : Equiv.Perm (Fin 1782)) = 1 :=
    congrArg (fun x : suzT => (x : Equiv.Perm (Fin 1782))) hττ
  have hτM : (τ : Equiv.Perm (Fin 1782)) ∉ suzM := by
    intro hτM
    obtain ⟨l0, hl0⟩ := hq ⟨τ, hτM⟩
    have hl0' : ((q l0 : suzM) : Equiv.Perm (Fin 1782)) = τ := congrArg Subtype.val hl0
    have hdL : ∀ l : ↥L, q (l0⁻¹ * h.outerConjHom hy l * l0) = q l := by
      intro l
      refine Subtype.ext ?_
      rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
        hτapply, hl0']
      group
    have hdcomm : ∀ p ∈ L, ((l0 : G)⁻¹ * y) * p * ((l0 : G)⁻¹ * y)⁻¹ * p⁻¹ ∈ zpowers z := by
      intro p hp
      have := h.outer_mem_zpowers_of_q_eq q hker (hdL ⟨p, hp⟩)
      convert this using 1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Setup.outerConjHom_apply]
      group
    have hdz : (l0 : G)⁻¹ * y ∈ centralizer ({z} : Set G) :=
      mul_mem (inv_mem (h.le_cent l0.2)) hy
    have hdcen := h.centralizes_of_perfect (P := L) le_rfl h.outer_le_commutator hdz hdcomm
    have hdmem : (l0 : G)⁻¹ * y ∈ centralizer (L : Set G) :=
      mem_centralizer_iff.2 fun l hl => mem_centralizer_singleton_iff.1 (hdcen hl)
    rw [hC] at hdmem
    have hdL' : (l0 : G)⁻¹ * y ∈ L := zpowers_le.2 h.zmem hdmem
    apply hyL
    have := L.mul_mem l0.2 hdL'
    rwa [mul_inv_cancel_left] at this
  have hne : (τ : Equiv.Perm (Fin 1782)) ≠ 1 := fun h1 => hτM (h1 ▸ suzM.one_mem)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hτ2 : orderOf (τ : Equiv.Perm (Fin 1782)) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hτ1) hne
  obtain ⟨i, hi, g, hg, hτg⟩ := cover_outer τ.2 hτ2 hτM
  obtain ⟨P, hPperf, htP, hPcomm⟩ := exists_perfect_outer_model q hq ht2 hker hcen hi
  obtain ⟨gt, hgt⟩ := hq ⟨g, hg⟩
  have hgt' : ((q gt : suzM) : Equiv.Perm (Fin 1782)) = g := congrArg Subtype.val hgt
  set φ : ↥L →* ↥L := (MulAut.conj gt).toMonoidHom with hφ
  set P' : Subgroup G := (P.map φ).map L.subtype with hP'
  have hP'L : P' ≤ L := Subgroup.map_subtype_le _
  have hP'perf : P' ≤ ⁅P', P'⁆ := perfect_map _ (perfect_map _ hPperf)
  have hzP' : z ∈ P' := by
    refine ⟨⟨z, h.zmem⟩, ⟨⟨z, h.zmem⟩, htP, ?_⟩, rfl⟩
    have := Subgroup.mem_center_iff.1 h.mem_center gt
    show gt * ⟨z, h.zmem⟩ * gt⁻¹ = ⟨z, h.zmem⟩
    rw [this]
    group
  have hcomm : ∀ p' ∈ P', y * p' * y⁻¹ * p'⁻¹ ∈ zpowers z := by
    rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    have hql : ((q (φ p) : suzM) : Equiv.Perm (Fin 1782)) =
        g * (q p : Equiv.Perm (Fin 1782)) * g⁻¹ := by
      show ((q (gt * p * gt⁻¹) : suzM) : Equiv.Perm (Fin 1782)) = _
      rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hgt']
    have hqp := hPcomm p hp
    have hqconj : q (h.outerConjHom hy (φ p)) = q (φ p) := by
      refine Subtype.ext ?_
      rw [hτapply, hql, hτg]
      have e : suzInv i * (q p : Equiv.Perm (Fin 1782)) * (suzInv i)⁻¹ = q p := by
        rw [← hqp]
        group
      calc g * suzInv i * g⁻¹ * (g * (q p : Equiv.Perm (Fin 1782)) * g⁻¹) *
            (g * suzInv i * g⁻¹)⁻¹
          = g * (suzInv i * (q p : Equiv.Perm (Fin 1782)) * (suzInv i)⁻¹) * g⁻¹ := by group
        _ = g * (q p : Equiv.Perm (Fin 1782)) * g⁻¹ := by rw [e]
    have h2 := h.outer_mem_zpowers_of_q_eq q hker hqconj
    have h3 : y * ((φ p : ↥L) : G) * y⁻¹ * ((φ p : ↥L) : G)⁻¹ ∈ zpowers z := by
      simpa only [Setup.outerConjHom_apply] using h2
    exact h3
  have hPy : P' ≤ centralizer ({y} : Set G) := h.centralizes_of_perfect hP'L hP'perf hy hcomm
  exact ⟨P', le_inf (hP'L.trans h.le_cent) hPy, hP'perf, hzP'⟩

end Main

end CFSG.EvenSporadicStandard.TwoSuz
