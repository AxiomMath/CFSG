module

public import Mathlib.GroupTheory.PGroup

import Mathlib.GroupTheory.Sylow
import TauCeti.Algebra.Group.Subgroup.Normalizer

public section

namespace CFSG.GroupTheory

private theorem isPGroup_quotient_ker_cnp {p : ℕ} {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hH : IsPGroup p H) : IsPGroup p (G ⧸ f.ker) :=
  (hH.to_subgroup f.range).of_equiv (QuotientGroup.quotientKerEquivRange f).symm

private theorem sylow_sup_normal_eq_top_cnp {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    [Finite G] {K : Subgroup G} [K.Normal] (P : Sylow p G) (h : IsPGroup p (G ⧸ K)) :
    (P : Subgroup G) ⊔ K = ⊤ := by
  have htop : (P.mapSurjective (QuotientGroup.mk'_surjective K) : Subgroup (G ⧸ K)) = ⊤ :=
    (P.mapSurjective (QuotientGroup.mk'_surjective K)).is_maximal' (h.to_subgroup ⊤) le_top
      |>.symm
  rw [Sylow.coe_mapSurjective] at htop
  have hcomap := congrArg (Subgroup.comap (QuotientGroup.mk' K)) htop
  rw [Subgroup.comap_top, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at hcomap
  exact hcomap

theorem not_dvd_card_centralizer_of_isPGroup_quotient {X : Type*} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] (hO : ∀ P : Subgroup X, P.Normal → IsPGroup p P → P = ⊥) {N : Subgroup X}
    [N.Normal] (hN : IsPGroup p (X ⧸ N)) :
    ¬ p ∣ Nat.card (Subgroup.centralizer (N : Set X)) := by
  intro hdiv
  let C : Subgroup X := Subgroup.centralizer (N : Set X)
  let f : C →* X ⧸ N := (QuotientGroup.mk' N).comp C.subtype
  let K : Subgroup C := f.ker
  have hKcenter : K ≤ Subgroup.center C := by
    intro k hk
    rw [Subgroup.mem_center_iff]
    intro c
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    have hkN : (k : X) ∈ N := by
      have h1 : f k = 1 := MonoidHom.mem_ker.mp hk
      simpa [f] using h1
    exact (Subgroup.mem_centralizer_iff.mp c.2 (k : X) hkN).symm
  have hKnormal : K.Normal := MonoidHom.normal_ker f
  have hKp : IsPGroup p (C ⧸ K) := isPGroup_quotient_ker_cnp f hN
  let P : Sylow p C := default
  have hsup : (P : Subgroup C) ⊔ K = ⊤ := sylow_sup_normal_eq_top_cnp P hKp
  have hPnormal : (P : Subgroup C).Normal :=
    TauCeti.normal_of_commute_of_sup_eq_top (C := (P : Subgroup C)) (P := K)
      (fun c _ x hx => Subgroup.mem_center_iff.mp (hKcenter hx) c) hsup
  have hPchar : (P : Subgroup C).Characteristic := by
    have hsub : Subsingleton (Sylow p C) := by
      refine ⟨fun Q R => ?_⟩
      have hPnorm : (P : Subgroup C).Normal := hPnormal
      have hQ : Q = P :=
        Sylow.ext (P.is_maximal' Q.isPGroup' (IsPGroup.le_sylow_of_normal P.isPGroup' Q))
      have hR : R = P :=
        Sylow.ext (P.is_maximal' R.isPGroup' (IsPGroup.le_sylow_of_normal P.isPGroup' R))
      rw [hQ, hR]
    have hsubI : Subsingleton (Sylow p C) := hsub
    exact Sylow.characteristic_of_subsingleton P
  have hPnormalX : (P.map C.subtype).Normal := by
    have hCnorm : C.Normal := Subgroup.normal_centralizer
    have hPchar' : (P : Subgroup C).Characteristic := hPchar
    exact ConjAct.normal_of_characteristic_of_normal (H := C) (K := (P : Subgroup C))
  have hPisP : IsPGroup p (P.map C.subtype) := P.isPGroup'.map C.subtype
  have hbot : P.map C.subtype = ⊥ := hO _ hPnormalX hPisP
  have hPbot : (P : Subgroup C) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective (P : Subgroup C) C.subtype_injective).mp hbot
  exact (Sylow.ne_bot_of_dvd_card P hdiv) hPbot

end CFSG.GroupTheory
