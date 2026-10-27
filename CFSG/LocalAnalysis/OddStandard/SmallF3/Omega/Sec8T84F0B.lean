module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup
open scoped Pointwise

theorem exists_odd_conj_normalized {G : Type*} [Group G] [Finite G] {M O Q E : Subgroup G}
    (hO : O ≤ M) (hOn : ∀ m ∈ M, ∀ o ∈ O, m * o * m⁻¹ ∈ O) (hodd : Odd (Nat.card O))
    (hE : E ≤ M) (hE2 : IsPGroup 2 E) (hM : M = E ⊔ O) (hQ : IsPGroup 2 Q)
    (hQM : ∀ q ∈ Q, ∀ m ∈ M, q * m * q⁻¹ ∈ M) :
    ∃ u ∈ O, ∀ q ∈ Q,
      q ∈ normalizer ((E.map (MulAut.conj u).toMonoidHom : Subgroup G) : Set G) := by
  classical
  have hOleN : M ≤ normalizer (O : Set G) := Subgroup.le_normalizer_iff.mpr hOn
  have hQleN : Q ≤ normalizer (M : Set G) := Subgroup.le_normalizer_iff.mpr hQM
  have hcop : Nat.Coprime 2 (Nat.card O) := hodd.coprime_two_left
  have hdisj : Disjoint E O :=
    IsPGroup.disjoint_of_coprime hE2 (IsPGroup.card (G := O)) hcop
  have hEO : E ⊓ O = ⊥ := hdisj.eq_bot
  let A : Subgroup ↥M := E.subgroupOf M
  let B : Subgroup ↥M := O.subgroupOf M
  have hA2 : IsPGroup 2 A := hE2.of_equiv (Subgroup.subgroupOfEquivOfLe hE).symm
  have hBnorm : B.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (H := O) (K := M) hO).mpr hOleN
  haveI : B.Normal := hBnorm
  have hAB_top : A ⊔ B = ⊤ := by
    have h := Subgroup.subgroupOf_sup (A := E) (A' := O) (B := M) hE hO
    rw [← hM, Subgroup.subgroupOf_self] at h
    exact h.symm
  have hAB_bot : A ⊓ B = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro x ⟨hxA, hxB⟩
    have hxE : (x : G) ∈ E := Subgroup.mem_subgroupOf.mp hxA
    have hxO : (x : G) ∈ O := Subgroup.mem_subgroupOf.mp hxB
    have hx : (x : G) ∈ E ⊓ O := ⟨hxE, hxO⟩
    rw [hEO, Subgroup.mem_bot] at hx
    exact Subtype.ext hx
  have hArel : B.relIndex A = Nat.card A := by
    have h := Subgroup.relIndex_mul_card B A
    rw [inf_comm, hAB_bot, Subgroup.card_bot, mul_one] at h
    exact h
  have hcardM : Nat.card ↥M = Nat.card A * Nat.card B := by
    have h := Subgroup.relIndex_mul_card B (A ⊔ B)
    rw [Subgroup.relIndex_sup_right (H := A) (K := B), hArel, hAB_top, inf_top_eq,
      Subgroup.card_top] at h
    exact h.symm
  have hcardB : Nat.card B = Nat.card O :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hO).toEquiv
  have hAidx : A.index = Nat.card O := by
    have h := Subgroup.card_mul_index A
    rw [hcardM] at h
    have hpos : 0 < Nat.card A := Nat.card_pos_iff.mpr ⟨⟨1, A.one_mem⟩, inferInstance⟩
    exact (Nat.mul_left_cancel hpos h).trans hcardB
  have hAodd : Odd A.index := by rw [hAidx]; exact hodd
  have hAnotdvd : ¬ 2 ∣ A.index := by
    rw [← even_iff_two_dvd]
    exact Nat.not_even_iff_odd.mpr hAodd
  let PE : Sylow 2 ↥M := hA2.toSylow hAnotdvd
  have hPE : (PE : Subgroup ↥M) = A := IsPGroup.toSylow_coe hA2 hAnotdvd
  haveI : Finite (Sylow 2 ↥M) := Sylow.finite_of_finiteIndex PE
  let φ : Q →* MulAut ↥M := M.normalizerMonoidHom.comp (Subgroup.inclusion hQleN)
  have hφ : ∀ (q : Q) (x : ↥M), ((φ q x : ↥M) : G) = (q : G) * x * (q : G)⁻¹ :=
    fun q x => Subgroup.normalizerMonoidHom_apply_apply_coe M (Subgroup.inclusion hQleN q) x
  letI : MulAction Q (Sylow 2 ↥M) := MulAction.compHom (Sylow 2 ↥M) φ
  obtain ⟨P, hPfix⟩ := hQ.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 2 ↥M)
    (not_dvd_card_sylow 2 ↥M)
  have hQnormP : ∀ q ∈ Q, q ∈ normalizer ((P : Subgroup ↥M).map M.subtype : Set G) := by
    intro q hq
    let q' : Q := ⟨q, hq⟩
    have hfix : (φ q') • P = P := (MulAction.mem_fixedPoints.mp hPfix) q'
    have hmap : (P : Subgroup ↥M).map ((φ q').toMonoidHom) = P := by
      have h1 : (((φ q') • P : Sylow 2 ↥M) : Subgroup ↥M) = (P : Subgroup ↥M) :=
        congrArg (fun S : Sylow 2 ↥M => (S : Subgroup ↥M)) hfix
      rw [Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def] at h1
      exact h1
    have hcomp : M.subtype.comp ((φ q').toMonoidHom)
        = (MulAut.conj (q' : G)).toMonoidHom.comp M.subtype := by
      ext x
      change ((φ q' x : ↥M) : G) = MulAut.conj (q' : G) (↑x)
      rw [hφ q' x, MulAut.conj_apply]
    have hmapG : ((P : Subgroup ↥M).map M.subtype).map (MulAut.conj (q : G)).toMonoidHom
        = (P : Subgroup ↥M).map M.subtype := by
      have h := congrArg (Subgroup.map M.subtype) hmap
      rw [Subgroup.map_map, hcomp, ← Subgroup.map_map] at h
      exact h
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmapG
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥M) PE P
  have hP' : (P : Subgroup ↥M) = (PE : Subgroup ↥M).map (MulAut.conj g).toMonoidHom := by
    have hcoe : ((g • PE : Sylow 2 ↥M) : Subgroup ↥M)
        = (PE : Subgroup ↥M).map (MulAut.conj g).toMonoidHom := by
      rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      rfl
    exact (congrArg (fun S : Sylow 2 ↥M => (S : Subgroup ↥M)) hg).symm.trans hcoe
  have hcompg : M.subtype.comp ((MulAut.conj g).toMonoidHom)
      = (MulAut.conj (g : G)).toMonoidHom.comp M.subtype := by
    ext x
    rfl
  have hPmap : (P : Subgroup ↥M).map M.subtype
      = E.map (MulAut.conj (g : G)).toMonoidHom := by
    have h := congrArg (Subgroup.map M.subtype) hP'
    rw [Subgroup.map_map, hcompg, ← Subgroup.map_map, hPE, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left hE] at h
    exact h
  have hgM : (g : G) ∈ M := g.2
  have hgprod : (g : G) ∈ (E : Set G) * (O : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right E O (hE.trans hOleN)]
    simpa [← hM] using hgM
  obtain ⟨e, he, o, ho, heo⟩ := Set.mem_mul.mp hgprod
  set o' : G := e * o * e⁻¹ with ho'def
  have ho' : o' ∈ O := hOn e (hE he) o ho
  have hm : (g : G) = o' * e := by
    rw [ho'def]
    calc (g : G) = e * o := heo.symm
      _ = (e * o * e⁻¹) * e := by group
  have hEm : E.map (MulAut.conj (g : G)).toMonoidHom
      = E.map (MulAut.conj o').toMonoidHom := by
    have hmul : MulAut.conj (o' * e) = MulAut.conj o' * MulAut.conj e :=
      map_mul MulAut.conj o' e
    have hcomp2 : (MulAut.conj o' * MulAut.conj e).toMonoidHom
        = (MulAut.conj o').toMonoidHom.comp (MulAut.conj e).toMonoidHom := by
      ext x; rfl
    have hEe : E.map (MulAut.conj e).toMonoidHom = E :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (E.le_normalizer he)
    rw [hm, hmul, hcomp2, ← Subgroup.map_map, hEe]
  refine ⟨o', ho', fun q hq => ?_⟩
  rw [← hEm, ← hPmap]
  exact hQnormP q hq

end CFSG.OddStandard.SmallF3.Omega
