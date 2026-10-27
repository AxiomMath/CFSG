module

public import CFSG.LieType.Steinberg.Bruhat
import CFSG.LieType.TitsSimplicity.Core
public import CFSG.GroupActions.SplitBNPair
public import CFSG.GH74.BNPair.Basic
import TauCeti.GroupTheory.SpecificGroups.Dihedral.Basic
import Mathlib.Tactic.Group
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

public section

namespace CFSG.GH74.GLS.SP

open CFSG.GH74.BNPair CFSG.GroupActions CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
open scoped Pointwise

theorem mem_map_conj_inv_iff {K : Type*} [Group K] {B : Subgroup K} {m z : K} :
    z ∈ B.map (MulAut.conj m⁻¹).toMonoidHom ↔ m * z * m⁻¹ ∈ B := by
  constructor
  · rintro ⟨b, hb, rfl⟩
    have e : m * ((MulAut.conj m⁻¹).toMonoidHom b) * m⁻¹ = b := by
      change m * (m⁻¹ * b * m⁻¹⁻¹) * m⁻¹ = b
      group
    rw [e]
    exact hb
  · intro h
    refine ⟨m * z * m⁻¹, h, ?_⟩
    change m⁻¹ * (m * z * m⁻¹) * m⁻¹⁻¹ = z
    group

theorem card_coxeterGroup_fin_two (M : CoxeterMatrix (Fin 2)) :
    Nat.card M.Group = 2 * M.M 0 1 := by
  set cs := M.toCoxeterSystem
  have hr : Set.range cs.simple = {cs.simple 0, cs.simple 1} := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · left; rfl
      · right; rfl
    · rintro (rfl | rfl)
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩]
  have hclosure : Subgroup.closure ({cs.simple 0, cs.simple 1} : Set M.Group) = ⊤ := by
    rw [← hr]
    exact cs.subgroup_closure_range_simple
  obtain ⟨e⟩ := TauCeti.nonempty_dihedralGroup_mulEquiv (n := M.M 0 1)
    (cs.simple_mul_simple_self 0) (cs.simple_mul_simple_self 1) (cs.simple_ne_one 0)
    (cs.simple_ne_one 1) (cs.orderOf_simple_mul_simple 0 1) hclosure
  have h := Nat.card_congr e.toEquiv
  rw [DihedralGroup.nat_card] at h
  omega

section Generic

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem commute_of_mem_iSup (hext : SteinbergExtras D n H) {x y : K} (hx : x ∈ ⨆ i, H i)
    (hy : y ∈ ⨆ i, H i) : Commute x y := by
  refine (Subgroup.iSup_induction H hx (C := fun x => ∀ y ∈ ⨆ i, H i, Commute x y)
    (fun i x hx y hy => ?_) (fun y _ => Commute.one_left y)
    (fun a b ha hb y hy => (ha y hy).mul_left (hb y hy))) y hy
  exact Subgroup.iSup_induction H hy (C := fun y => Commute x y)
    (fun j y hy => hext.torus_commute i j x hx y hy) (Commute.one_right x)
    (fun a b ha hb => ha.mul_right hb)

variable
  (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
    (weylAction D.isFiniteType) D.roots D.rootGroup n H)
  (hext : SteinbergExtras D n H)

include hct hext

theorem cartan_normal_of_datum : (cartan (borel D H) (weylN n H)).Normal := by
  change ((borel D H ⊓ weylN n H).subgroupOf (weylN n H)).Normal
  rw [borel_inf_weylN hct hext]
  exact iSup_subgroupOf_weylN_normal hct hext

theorem ker_weylNHom_eq_cartan :
    (weylNHom hct hext).ker = cartan (borel D H) (weylN n H) := by
  rw [ker_weylNHom hct hext]
  change _ = (borel D H ⊓ weylN n H).subgroupOf (weylN n H)
  rw [borel_inf_weylN hct hext]

noncomputable def weylEquiv [hN : (cartan (borel D H) (weylN n H)).Normal] :
    WeylGroup (borel D H) (weylN n H) ≃* (coxeterMatrix D.isFiniteType).Group :=
  (QuotientGroup.quotientMulEquivOfEq (ker_weylNHom_eq_cartan hct hext).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (weylNHom_surjective hct hext))

theorem weylEquiv_n [_hN : (cartan (borel D H) (weylN n H)).Normal] (i : Fin D.rank) :
    weylEquiv hct hext ((⟨n i, n_mem_weylN i⟩ : weylN n H) :
      WeylGroup (borel D H) (weylN n H)) =
        (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i :=
  weylNHom_n hct hext i

theorem actsAs_of_mk_eq [_hN : (cartan (borel D H) (weylN n H)).Normal] {m : weylN n H}
    {i : Fin D.rank}
    (h : (m : WeylGroup (borel D H) (weylN n H)) =
      ((⟨n i, n_mem_weylN i⟩ : weylN n H) : WeylGroup (borel D H) (weylN n H))) :
    ActsAs D (m : K) ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i) := by
  refine (weylNHom_eq_iff hct hext).1 ?_
  have h' := congrArg (weylEquiv hct hext) h
  rw [weylEquiv_n hct hext i] at h'
  exact h'

theorem conjBy_rootGroup_of_mk_eq [_hN : (cartan (borel D H) (weylN n H)).Normal]
    {m : weylN n H} {i : Fin D.rank}
    (h : (m : WeylGroup (borel D H) (weylN n H)) =
      ((⟨n i, n_mem_weylN i⟩ : weylN n H) : WeylGroup (borel D H) (weylN n H)))
    {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) :
    conjBy (m : K) (D.rootGroup γ) = D.rootGroup (weylAction D.isFiniteType
      ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i) γ) := by
  have hm := (actsAs_of_mk_eq hct hext h).inv
  rw [CoxeterSystem.inv_simple] at hm
  exact hm γ hγ

theorem card_weyl_of_datum :
    Nat.card (WeylGroup (borel D H) (weylN n H)) =
      Nat.card (coxeterMatrix D.isFiniteType).Group := by
  have hN := cartan_normal_of_datum hct hext
  exact Nat.card_congr (weylEquiv hct hext).toEquiv

theorem borel_eq_mul_of_datum :
    (borel D H : Set K) = ((borel D H ⊓ weylN n H : Subgroup K) : Set K) *
      (posUnipotent D : Set K) := by
  rw [borel_inf_weylN hct hext]
  exact coe_borel hct

theorem isSplit_of_datum (hnil : Group.IsNilpotent (posUnipotent D)) :
    IsSplit (borel D H) (weylN n H) (posUnipotent D) :=
  ⟨hnil, borel_eq_mul_of_datum hct hext⟩

theorem splitBN_of_datum (hnil : Group.IsNilpotent (posUnipotent D)) :
    SplitBN (borel D H) (weylN n H) (posUnipotent D)
      (fun i : Fin D.rank => (⟨n i, n_mem_weylN i⟩ : weylN n H)) := by
  have hN := cartan_normal_of_datum hct hext
  obtain ⟨e, he⟩ : ∃ e : WeylGroup (borel D H) (weylN n H) ≃*
      (coxeterMatrix D.isFiniteType).Group,
      ∀ i : Fin D.rank, e ((⟨n i, n_mem_weylN i⟩ : weylN n H) :
        WeylGroup (borel D H) (weylN n H)) =
          (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i :=
    ⟨weylEquiv hct hext, weylEquiv_n hct hext⟩
  have hgen : borel D H ⊔ weylN n H = ⊤ := by
    rw [eq_top_iff, ← closure_borel_union_range hct]
    refine (Subgroup.closure_le _).2 (Set.union_subset (fun x hx => Subgroup.mem_sup_left hx) ?_)
    rintro _ ⟨i, rfl⟩
    exact Subgroup.mem_sup_right (n_mem_weylN i)
  have hinj : Function.Injective (fun i : Fin D.rank =>
      ((⟨n i, n_mem_weylN i⟩ : weylN n H) : WeylGroup (borel D H) (weylN n H))) := by
    intro i j hij
    exact (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple_injective
      ((he i).symm.trans ((congrArg e hij).trans (he j)))
  have hord : ∀ i : Fin D.rank, orderOf
      ((⟨n i, n_mem_weylN i⟩ : weylN n H) : WeylGroup (borel D H) (weylN n H)) = 2 := by
    intro i
    rw [← MulEquiv.orderOf_eq e, he, CoxeterSystem.orderOf_simple]
  have hclos : Subgroup.closure (Set.range fun i : Fin D.rank =>
      ((⟨n i, n_mem_weylN i⟩ : weylN n H) : WeylGroup (borel D H) (weylN n H))) = ⊤ := by
    rw [eq_top_iff, ← Subgroup.map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective,
      Subgroup.map_top_of_surjective _ e.surjective, MonoidHom.map_closure,
      ← (coxeterMatrix D.isFiniteType).toCoxeterSystem.subgroup_closure_range_simple]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨_, ⟨i, rfl⟩, he i⟩
  have hmul : ∀ i : Fin D.rank, ∀ x ∈ weylN n H,
      ({n i} : Set K) * (borel D H : Set K) * {x} ⊆
        (borel D H : Set K) * {n i * x} * (borel D H : Set K) ∪
          (borel D H : Set K) * {x} * (borel D H : Set K) := by
    intro i x hx y hy
    obtain ⟨_, ⟨a, ha, b, hb, rfl⟩, c, hc, rfl⟩ := hy
    rw [Set.mem_singleton_iff] at ha hc
    rw [ha, hc]
    obtain ⟨w, hw⟩ := exists_actsAs hct hx
    have hxcell : b * x ∈ bruhatCell hct w := by
      rw [bruhatCell_eq_of_actsAs hct hext hx hw]
      exact ⟨b, hb, 1, one_mem _, by rw [mul_one]⟩
    rcases n_mul_mem_bruhatCell hct hext hxcell i with h | h
    · right
      rw [bruhatCell_eq_of_actsAs hct hext hx hw] at h
      obtain ⟨b₁, hb₁, b₂, hb₂, he'⟩ := h
      exact mem_dcoset_iff.2 ⟨b₁, hb₁, b₂, hb₂, (mul_assoc (n i) b x).trans he'⟩
    · left
      have hnx : n i * x ∈ weylN n H := mul_mem (n_mem_weylN i) hx
      rw [bruhatCell_eq_of_actsAs hct hext hnx ((actsAs_n hct i).mul hw)] at h
      obtain ⟨b₁, hb₁, b₂, hb₂, he'⟩ := h
      exact mem_dcoset_iff.2 ⟨b₁, hb₁, b₂, hb₂, (mul_assoc (n i) b x).trans he'⟩
  have hne : ∀ i : Fin D.rank,
      ¬ ({n i} : Set K) * (borel D H : Set K) * {(n i)⁻¹} ⊆ (borel D H : Set K) := by
    intro i hsub
    refine not_map_conj_n_borel_le hct hext i ?_
    rintro _ ⟨b, hb, rfl⟩
    have h2 : n i * b * (n i)⁻¹ ∈ ({n i} : Set K) * (borel D H : Set K) * {(n i)⁻¹} :=
      ⟨_, ⟨n i, rfl, b, hb, rfl⟩, (n i)⁻¹, rfl, rfl⟩
    simpa [MulAut.conj_apply] using hsub h2
  have hUnorm : ((posUnipotent D).subgroupOf (borel D H)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer posUnipotent_le_borel).2
      (borel_le_normalizer_posUnipotent hct)
  have hcomm : ∀ x ∈ borel D H ⊓ weylN n H, ∀ y ∈ borel D H ⊓ weylN n H, x * y = y * x := by
    intro x hx y hy
    rw [borel_inf_weylN hct hext] at hx hy
    exact (commute_of_mem_iSup hext hx hy).eq
  have hBUH : (borel D H : Set K) =
      (posUnipotent D : Set K) * ((borel D H ⊓ weylN n H : Subgroup K) : Set K) := by
    rw [borel_inf_weylN hct hext]
    have h : (⨆ i, H i) ≤ Subgroup.normalizer (posUnipotent D : Set K) :=
      iSup_le_borel.trans (borel_le_normalizer_posUnipotent hct)
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left (posUnipotent D) (⨆ i, H i) h]
    change ((((⨆ i, H i) ⊔ posUnipotent D : Subgroup K)) : Set K) = _
    rw [sup_comm]
  have hinf : posUnipotent D ⊓ (borel D H ⊓ weylN n H) = ⊥ := by
    rw [borel_inf_weylN hct hext, inf_comm]
    exact hext.torus_inf_posPart
  exact ⟨hN, hgen, hinj, hord, hclos, hmul, hne, posUnipotent_le_borel, hUnorm, hnil, hcomm,
    hBUH, hinf⟩

theorem isSaturated_of_datum (hBE : BruhatExtras D H) :
    IsSaturated (borel D H) (weylN n H) := by
  refine le_antisymm (le_iInf fun m => ?_) ?_
  · intro t ht
    rw [borel_inf_weylN hct hext] at ht
    exact mem_map_conj_inv_iff.2 (iSup_le_borel (conj_mem_iSup_of_mem_weylN hct m.2 ht))
  · intro z hz
    have hz' := Subgroup.mem_iInf.1 hz
    have hzB : z ∈ borel D H := by
      have := mem_map_conj_inv_iff.1 (hz' 1)
      simpa using this
    obtain ⟨w₀, hw₀⟩ := CFSG.LieType.TitsSimplicity.exists_forall_isRightDescent (D := D)
    have hconj : nrep hct w₀ * z * (nrep hct w₀)⁻¹ ∈ borel D H :=
      mem_map_conj_inv_iff.1 (hz' ⟨nrep hct w₀, nrep_mem_weylN hct w₀⟩)
    rw [← SetLike.mem_coe, coe_borel hct, Set.mem_mul] at hzB
    obtain ⟨t, ht, u, hu, rfl⟩ := hzB
    have ht' : nrep hct w₀ * t * (nrep hct w₀)⁻¹ ∈ ⨆ i, H i :=
      conj_mem_iSup_of_mem_weylN hct (nrep_mem_weylN hct w₀) ht
    have hu' := CFSG.LieType.TitsSimplicity.nrep_conj_mem_negUnipotent_of_forall_isRightDescent
      hct hw₀ hu
    have hv : nrep hct w₀ * u * (nrep hct w₀)⁻¹ ∈ borel D H ⊓ negUnipotent D := by
      refine Subgroup.mem_inf.2 ⟨?_, hu'⟩
      have e : nrep hct w₀ * u * (nrep hct w₀)⁻¹ =
          (nrep hct w₀ * t * (nrep hct w₀)⁻¹)⁻¹ * (nrep hct w₀ * (t * u) * (nrep hct w₀)⁻¹) := by
        group
      rw [e]
      exact mul_mem (inv_mem (iSup_le_borel ht')) hconj
    rw [hBE.borel_inf_negUnipotent, Subgroup.mem_bot] at hv
    have hu1 : u = 1 := by
      have e : u = (nrep hct w₀)⁻¹ * (nrep hct w₀ * u * (nrep hct w₀)⁻¹) * nrep hct w₀ := by
        group
      rw [e, hv]
      group
    rw [hu1, mul_one, borel_inf_weylN hct hext]
    exact ht

end Generic

end CFSG.GH74.GLS.SP
