module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.CoverLift
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSStd
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.H35Normal
import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiCoverLift
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Mult
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSTransport
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.EvenSporadicStandard.Induction.Cover

open Subgroup CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.Solomon78
  CFSG.ComponentClassification.PerfectAutomorphisms

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem mem_map_conj_iff (S : Subgroup X) (g x : X) :
    x ∈ S.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ S := by
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

theorem stdBare_of_quotient (hodd : Odd (Nat.card (center X))) {K : Subgroup X} (hK : ⁅K, K⁆ = K)
    (h : StdBare (K.map (q X))) : StdBare K :=
  stdBare_of_bar hodd hK h

omit [Finite X] in
theorem isQuasisimple_of_quotient {K : Subgroup X} (hK : Group.IsPerfect ↥K)
    (hq : CFSG.IsQuasisimple ↥(K.map (q X))) : CFSG.IsQuasisimple ↥K := by
  have hK' : ⁅K, K⁆ = K := isPerfect_iff.mp hK
  set Kt : Subgroup (X ⧸ center X) := K.map (q X) with hKt
  let f : ↥K →* ↥Kt := (q X).subgroupMap K
  have hf : Function.Surjective f := (q X).subgroupMap_surjective K
  let g : ↥K →* ↥Kt ⧸ center ↥Kt := (QuotientGroup.mk' (center ↥Kt)).comp f
  have hg : Function.Surjective g := (QuotientGroup.mk'_surjective _).comp hf
  have hker : center ↥K = g.ker := by
    ext x
    rw [MonoidHom.mem_ker]
    show x ∈ center ↥K ↔ (f x : ↥Kt ⧸ center ↥Kt) = 1
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_center_iff, Subgroup.mem_center_iff]
    constructor
    · intro hx y
      obtain ⟨k, rfl⟩ := hf y
      rw [← map_mul, ← map_mul, hx k]
    · intro hx
      have hxc : (x : X) ∈ centralizer (K : Set X) := by
        rw [mem_centralizer_iff_of_perfect hK', mem_centralizer_iff]
        rintro _ ⟨k, hk, rfl⟩
        exact congrArg Subtype.val (hx (f ⟨k, hk⟩))
      intro y
      exact Subtype.ext (mem_centralizer_iff.1 hxc y y.2)
  have e : ↥K ⧸ center ↥K ≃* (↥Kt ⧸ center ↥Kt) :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective g hg)
  have hs' : IsSimpleGroup (↥K ⧸ center ↥K) := @MulEquiv.isSimpleGroup _ _ _ _ hq.2.1 e
  refine ⟨hK, hs', ?_⟩
  obtain ⟨a, b, hab⟩ := hq.2.2
  exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by rw [map_mul, map_mul]; exact h))⟩

theorem solStd_of_quotient (hodd : Odd (Nat.card (center X))) {K : Subgroup X} {u : X}
    (hKperf : Group.IsPerfect ↥K) (hq : CFSG.IsQuasisimple ↥(K.map (q X)))
    (hstd : StdBare (K.map (q X)))
    (hu2 : orderOf u = 2) (hKu : K ≤ centralizer ({u} : Set X))
    (hnorm : ∀ c ∈ centralizer ({u} : Set X),
      (K.map (q X)).map (conjHom (q X c)) = K.map (q X)) : SolStd K := by
  have hK' : ⁅K, K⁆ = K := isPerfect_iff.mp hKperf
  refine ⟨stdBare_of_quotient hodd hK' hstd, u, hu2, isCompIn_of_normal hKu
    (isQuasisimple_of_quotient hKperf hq) ?_⟩
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKu]
  intro c hc
  rw [Solomon78.mem_normalizer_iff_map_conj_eq]
  refine map_conj_eq_of_perfect hK' fun k hk => ?_
  have h := hnorm c hc
  have : q X (c * k * c⁻¹) ∈ (K.map (q X)).map (conjHom (q X c)) :=
    ⟨q X k, ⟨k, hk, rfl⟩, by simp [map_mul, map_inv]⟩
  rwa [h] at this

@[expose] def autFixing {Y : Type} [Group Y] (K : Subgroup Y) : Subgroup (MulAut Y) where
  carrier := {β | ∀ y ∈ K, β y = y}
  mul_mem' := fun {a b} ha hb y hy => by
    show a (b y) = y
    rw [hb y hy, ha y hy]
  one_mem' := fun _ _ => rfl
  inv_mem' := fun {a} ha y hy => by
    show a.symm y = y
    calc a.symm y = a.symm (a y) := by rw [ha y hy]
      _ = y := a.symm_apply_apply y

theorem twoAdic_autCentralizer_le_of_quotient {H : Type} [Group H] [Finite H] {L K : Subgroup H}
    (hLperf : Group.IsPerfect ↥L) :
    twoAdic (autCentralizer L K) ≤
      twoAdic (autFixing ((K.subgroupOf L).map (q ↥L))) := by
  have : Group.IsPerfect ↥L := hLperf
  refine twoAdic_le_of_map_le (centerQuotientHom ↥L) (centerQuotientHom_injective ↥L) ?_
  rintro _ ⟨α, hα, rfl⟩ y ⟨k, hk, rfl⟩
  show (centerQuotientHom ↥L α) (q ↥L k) = q ↥L k
  have h1 := onCenterQuotient_apply_mk α k
  have h2 : α k = k := hα k (Subgroup.mem_subgroupOf.1 hk)
  change onCenterQuotient α (q ↥L k) = q ↥L k
  rw [h1, h2]

theorem twoAdic_autFixing_le {Y : Type} [Group Y] [Finite Y] (K : Subgroup Y) :
    twoAdic (autFixing K) ≤ twoAdic (autCentralizer (⊤ : Subgroup Y) K) := by
  refine twoAdic_le_of_map_le (MulAut.congr (Subgroup.topEquiv (G := Y)).symm).toMonoidHom
    (MulAut.congr (Subgroup.topEquiv (G := Y)).symm).injective ?_
  rintro _ ⟨β, hβ, rfl⟩ y hy
  show ((MulAut.congr (Subgroup.topEquiv (G := Y)).symm) β y : ↥(⊤ : Subgroup Y)) = y
  apply Subtype.ext
  simp only [MulAut.congr_apply, MulEquiv.trans_apply]
  exact hβ y hy

structure PinnedLocal {Y : Type} [Group Y] (K : Subgroup Y) (u : Y) : Prop where
  quasisimple : CFSG.IsQuasisimple ↥K
  std : StdBare K
  normalized : ∀ c ∈ centralizer ({u} : Set Y), K.map (conjHom c) = K
  autTwo : twoAdic (autFixing K) ≤ 2

end CFSG.EvenSporadicStandard.Induction.Cover

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78 Cover

theorem solomonLocalQ_of_pinned {s : TauCeti.SporadicName} {H : Type} [Group H] [Finite H]
    {L K : Subgroup H} {u : H} (hcov : OddCover s L) (hu : u ∈ L) (hu2 : orderOf u = 2)
    (hKL : K ≤ L) (hKu : ∀ k ∈ K, k * u = u * k) (hKperf : Group.IsPerfect ↥K)
    (P : PinnedLocal ((K.subgroupOf L).map (q ↥L)) (q ↥L ⟨u, hu⟩)) : SolomonLocalQ L K u where
  u_order := hu2
  u_mem := Subgroup.le_normalizer hu
  u_not_central := hcov.not_mem_centralizer_of_orderOf_two hu hu2
  K_le := hKL
  u_mem_centralizer_K := mem_centralizer_iff.2 hKu
  standard_in_L := by
    have hLperf : Group.IsPerfect ↥L := hcov.1.1
    refine solStd_of_quotient hcov.2.1 (isPerfect_subgroupOf_of_le hKL hKperf) P.quasisimple
      P.std (u := (⟨u, hu⟩ : ↥L)) ?_ ?_ ?_
    · rw [Subgroup.orderOf_mk]; exact hu2
    · intro k hk
      rw [mem_centralizer_singleton_iff]
      exact Subtype.ext (hKu k (Subgroup.mem_subgroupOf.1 hk))
    · intro c hc
      refine P.normalized (q ↥L c) ?_
      rw [mem_centralizer_singleton_iff] at hc ⊢
      rw [← map_mul, ← map_mul, hc]
  autCentralizer_two := by
    have hLperf : Group.IsPerfect ↥L := hcov.1.1
    exact (twoAdic_autCentralizer_le_of_quotient hLperf).trans P.autTwo

end CFSG.EvenSporadicStandard.Induction
