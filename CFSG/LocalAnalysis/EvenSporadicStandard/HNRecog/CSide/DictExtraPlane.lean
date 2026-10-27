module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.DictExtraAux
public import CFSG.GroupTheory.ElemAbelianClosure

@[expose] public section

namespace CFSG.EvenSporadicStandard.HNRecog.CSide

open Subgroup QuadraticMap CFSG.RankThree.Literature.FSmith CFSG.EvenSporadicStandard.HNRecog
open scoped commutatorElement

variable {C : Type} [Group C] {Q : Subgroup C} [hQn : Q.Normal]
  [Module (ZMod 2) (Additive (Abelianization Q))]

theorem cSide_cent_elemAbelian_of_plane [Finite Q] (hE : IsExtraspecialPGroup 2 Q) {ρ : C}
    (hρ : Odd (orderOf ρ))
    (hplane : cSideFixedPlane (extraspecialQuadForm hE) (conjLinEquiv hQn ρ)) :
    ∃ E : Subgroup C, E ≤ Q ⊓ Subgroup.centralizer ({ρ} : Set C) ∧
      CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 2 ^ 3 := by
  classical
  obtain ⟨v, w, hvfix, hwfix, hv0, hw0, hvw, hvq, hwq, hvwpolar⟩ := hplane
  obtain ⟨x, hx⟩ := exists_ofMul_of v
  obtain ⟨y, hy⟩ := exists_ofMul_of w
  have hxsq : x * x = 1 := by
    by_contra h
    have hvq' : extraspecialQuadForm hE (Additive.ofMul (Abelianization.of x)) = 0 := by
      rw [hx]; exact hvq
    rw [extraspecialQuadForm_apply, if_neg (fun h2 => h (by rwa [pow_two] at h2))] at hvq'
    exact one_ne_zero hvq'
  have hysq : y * y = 1 := by
    by_contra h
    have hwq' : extraspecialQuadForm hE (Additive.ofMul (Abelianization.of y)) = 0 := by
      rw [hy]; exact hwq
    rw [extraspecialQuadForm_apply, if_neg (fun h2 => h (by rwa [pow_two] at h2))] at hwq'
    exact one_ne_zero hwq'
  have hxycomm : x * y = y * x := by
    by_contra h
    have hpol : polar (extraspecialQuadForm hE) (Additive.ofMul (Abelianization.of x))
        (Additive.ofMul (Abelianization.of y)) = 0 := by rw [hx, hy]; exact hvwpolar
    exact h ((polar_extraspecialQuadForm_eq_zero_iff hE x y).mp hpol)
  have hxR : (x : C) ∈ Q ⊓ Subgroup.centralizer ({ρ} : Set C) :=
    (cSide_mem_R_iff hE hρ x).mpr (by rw [hx]; exact hvfix)
  have hyR : (y : C) ∈ Q ⊓ Subgroup.centralizer ({ρ} : Set C) :=
    (cSide_mem_R_iff hE hρ y).mpr (by rw [hy]; exact hwfix)
  obtain ⟨z0, hz0ne, hz0uniq⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center ↥Q)).1 hE.2.2.2
  let z : ↥Q := z0.1
  have hzcenter : z ∈ Subgroup.center ↥Q := z0.2
  have hzne : z ≠ 1 := fun h => hz0ne (Subtype.ext h)
  have hzuniq : ∀ y : Subgroup.center ↥Q, y ≠ 1 → y = ⟨z, hzcenter⟩ := fun y hy =>
    hz0uniq y hy
  have hzsq : z * z = 1 := by
    apply Subtype.ext
    have h := sq_eq_one_of_mem_center hE hzcenter
    simpa [pow_two] using congrArg Subtype.val h
  have hzx : z * x = x * z := Subtype.ext (by
    have hmem := (Subgroup.mem_center_iff.mp hzcenter) x
    exact congrArg Subtype.val hmem.symm)
  have hzy : z * y = y * z := Subtype.ext (by
    have hmem := (Subgroup.mem_center_iff.mp hzcenter) y
    exact congrArg Subtype.val hmem.symm)
  let E : Subgroup C := Subgroup.closure ({(x : C), (y : C), (z : C)} : Set C)
  have hxE : (x : C) ∈ E := Subgroup.subset_closure (by simp)
  have hyE : (y : C) ∈ E := Subgroup.subset_closure (by simp)
  have hzE : (z : C) ∈ E := Subgroup.subset_closure (by simp)
  have hEleQ : E ≤ Q := (Subgroup.closure_le Q).mpr (by
    rintro t (rfl | rfl | rfl)
    · exact x.2
    · exact y.2
    · exact z.2)
  have hzR : (z : C) ∈ Q ⊓ Subgroup.centralizer ({ρ} : Set C) :=
    cSide_centerOf_le_cent hE ρ ((mem_centerOf_iff z).mpr hzcenter)
  have hER : E ≤ Q ⊓ Subgroup.centralizer ({ρ} : Set C) :=
    (Subgroup.closure_le (Q ⊓ Subgroup.centralizer ({ρ} : Set C))).mpr (by
      rintro t (rfl | rfl | rfl)
      · exact hxR
      · exact hyR
      · exact hzR)
  have hxycommC : (x : C) * (y : C) = (y : C) * (x : C) := by
    simpa using congrArg Subtype.val hxycomm
  have hzxC : (z : C) * (x : C) = (x : C) * (z : C) := by
    simpa using congrArg Subtype.val hzx
  have hzyC : (z : C) * (y : C) = (y : C) * (z : C) := by
    simpa using congrArg Subtype.val hzy
  have hxsqC : (x : C) ^ 2 = 1 := by
    simpa [pow_two] using congrArg Subtype.val hxsq
  have hysqC : (y : C) ^ 2 = 1 := by
    simpa [pow_two] using congrArg Subtype.val hysq
  have hzsqC : (z : C) ^ 2 = 1 := by
    simpa [pow_two] using congrArg Subtype.val hzsq
  have hEa : CFSG.Open.IsElemAbelian 2 E := by
    refine CFSG.Open.IsElemAbelian.closure_of_commute ?_ ?_
    · intro a ha b hb
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
      · rfl
      · exact hxycommC
      · exact hzxC.symm
      · exact hxycommC.symm
      · rfl
      · exact hzyC.symm
      · exact hzxC
      · exact hzyC
      · rfl
    · intro a ha
      rcases ha with rfl | rfl | rfl
      · exact hxsqC
      · exact hysqC
      · exact hzsqC
  let φE : ↥E →* Multiplicative (Additive (Abelianization Q)) :=
    (cSide_ofMulHom Q).comp (Subgroup.inclusion hEleQ)
  let xE : ↥E := ⟨(x : C), hxE⟩
  let yE : ↥E := ⟨(y : C), hyE⟩
  let zE : ↥E := ⟨(z : C), hzE⟩
  have htop : (⊤ : Subgroup ↥E) = Subgroup.closure ({xE, yE, zE} : Set ↥E) :=
    cSide_top_eq_closure hxE hyE hzE rfl
  have hxphi : φE xE = Additive.ofMul (Abelianization.of x) := rfl
  have hyphi : φE yE = Additive.ofMul (Abelianization.of y) := rfl
  have hzphi : φE zE = 1 := by
    have h : Additive.ofMul (Abelianization.of (Subgroup.inclusion hEleQ zE)) = 0 :=
      (ofMul_of_eq_zero_iff hE (Subgroup.inclusion hEleQ zE)).mpr (by
        rw [show Subgroup.inclusion hEleQ zE = z from Subtype.ext rfl]
        exact hzcenter)
    exact h
  have hrange : φE.range = Subgroup.closure
      ({φE xE, φE yE} : Set (Multiplicative (Additive (Abelianization Q)))) := by
    rw [MonoidHom.range_eq_map, htop, MonoidHom.map_closure]
    apply le_antisymm
    · refine (Subgroup.closure_le _).mpr ?_
      rintro a ⟨e, he, rfl⟩
      rcases he with rfl | rfl | rfl
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · rw [hzphi]; exact Subgroup.one_mem _
    · apply Subgroup.closure_mono
      intro a ha
      rcases ha with rfl | rfl
      · exact ⟨xE, by simp, rfl⟩
      · exact ⟨yE, by simp, rfl⟩
  have hcard_range : Nat.card φE.range = 4 := by
    rw [hrange]
    exact cSide_card_closure_pair (cSide_mul_self_eq_one _) (cSide_mul_self_eq_one _)
      (by rw [hxphi, hx]; exact hv0) (by rw [hyphi, hy]; exact hw0)
      (by rw [hxphi, hyphi, hx, hy]; exact hvw)
  have hcard_ker : Nat.card φE.ker = 2 := by
    have hset : (φE.ker : Set ↥E) = {1, zE} := by
      ext a
      show a ∈ φE.ker ↔ a = 1 ∨ a = zE
      rw [MonoidHom.mem_ker]
      constructor
      · intro ha
        have hmem : (Subgroup.inclusion hEleQ a : ↥Q) ∈ Subgroup.center ↥Q := by
          have : Additive.ofMul (Abelianization.of (Subgroup.inclusion hEleQ a)) = 0 := ha
          exact (ofMul_of_eq_zero_iff hE _).mp this
        rcases cSide_center_eq_one_or hzcenter hzne hzuniq hmem with h | h
        · left
          exact Subtype.ext (by simpa using congrArg (fun t : ↥Q => (t : C)) h)
        · right
          exact Subtype.ext (by simpa [zE] using congrArg (fun t : ↥Q => (t : C)) h)
      · rintro (rfl | rfl)
        · exact φE.map_one
        · exact hzphi
    change Nat.card (φE.ker : Set ↥E) = 2
    rw [Nat.card_coe_set_eq, hset]
    exact Set.ncard_pair (fun h : (1 : ↥E) = zE =>
      hzne (by
        have := congrArg (fun t : ↥E => (Subgroup.inclusion hEleQ t : ↥Q)) h.symm
        exact (Subtype.ext rfl).symm.trans this))
  have hcardE : Nat.card E = 2 ^ 3 := by
    have hprod := Subgroup.card_eq_card_quotient_mul_card_subgroup φE.ker
    have hq : Nat.card (↥E ⧸ φE.ker) = Nat.card φE.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φE).toEquiv
    rw [hq, hcard_ker, hcard_range] at hprod
    rw [hprod]
    norm_num
  exact ⟨E, hER, hEa, hcardE⟩

theorem cSide_plane_of_cent_elemAbelian [Finite Q] (hE : IsExtraspecialPGroup 2 Q) {ρ : C}
    {E : Subgroup C} (hEle : E ≤ Q ⊓ Subgroup.centralizer ({ρ} : Set C))
    (hEa : CFSG.Open.IsElemAbelian 2 E) (hEc : Nat.card E = 2 ^ 3) :
    cSideFixedPlane (extraspecialQuadForm hE) (conjLinEquiv hQn ρ) := by
  classical
  have hEleQ : E ≤ Q := hEle.trans inf_le_left
  let φE : ↥E →* Multiplicative (Additive (Abelianization Q)) :=
    (cSide_ofMulHom Q).comp (Subgroup.inclusion hEleQ)
  haveI hEfin : Finite ↥E := Finite.of_injective
    (fun x : ↥E => (⟨(x : C), hEleQ x.2⟩ : ↥Q))
    (fun a b h => Subtype.ext (by
      have h1 := congrArg (fun t : ↥Q => (t : C)) h
      simpa using h1))
  have hker_le : Nat.card φE.ker ≤ 2 := by
    let f : φE.ker → ↥(centerOf Q) := fun a =>
      ⟨((a.1 : ↥E) : C), by
        have ha : φE a.1 = 1 := a.2
        have ha' : Additive.ofMul (Abelianization.of (Subgroup.inclusion hEleQ a.1)) = 0 := ha
        exact (mem_centerOf_iff _).mpr ((ofMul_of_eq_zero_iff hE _).mp ha')⟩
    have hf : Function.Injective f := by
      intro a b hab
      have h1 : ((a.1 : ↥E) : C) = ((b.1 : ↥E) : C) :=
        congrArg (fun t : ↥(centerOf Q) => (t : C)) hab
      exact Subtype.ext (Subtype.ext h1)
    haveI : Finite ↥(centerOf Q) := Finite.of_injective
      (fun x : ↥(centerOf Q) => (⟨(x : C), (Subgroup.mem_inf.mp x.2).1⟩ : ↥Q))
      (fun a b h => Subtype.ext (by
        have h1 := congrArg (fun t : ↥Q => (t : C)) h
        simpa using h1))
    calc Nat.card φE.ker ≤ Nat.card ↥(centerOf Q) := Nat.card_le_card_of_injective f hf
      _ = 2 := cSide_card_centerOf hE
  have hcardE : Nat.card ↥E = 8 := by rw [hEc]; norm_num
  have hprod : Nat.card φE.ker * Nat.card φE.range = 8 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup φE.ker
    have hq : Nat.card (↥E ⧸ φE.ker) = Nat.card φE.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φE).toEquiv
    rw [hq, hcardE] at h
    rw [mul_comm]
    exact h.symm
  have hrange_ge : 4 ≤ Nat.card φE.range := by
    have hk : Nat.card φE.ker = 1 ∨ Nat.card φE.ker = 2 := by
      haveI : Nonempty φE.ker := ⟨⟨1, φE.ker.one_mem⟩⟩
      have := Nat.card_pos (α := φE.ker)
      omega
    rcases hk with hk | hk <;> rw [hk] at hprod <;> omega
  obtain ⟨v, w, hv0, hw0, hvw⟩ :=
    cSide_exists_two_ne_one (le_trans (by norm_num : 3 ≤ 4) hrange_ge)
  obtain ⟨x, hx⟩ := v.2
  obtain ⟨y, hy⟩ := w.2
  have hxQ : (x : C) ∈ Q := hEleQ x.2
  have hyQ : (y : C) ∈ Q := hEleQ y.2
  have hxphi : Multiplicative.toAdd (φE x) =
      Additive.ofMul (Abelianization.of (⟨(x : C), hxQ⟩ : ↥Q)) := rfl
  have hyphi : Multiplicative.toAdd (φE y) =
      Additive.ofMul (Abelianization.of (⟨(y : C), hyQ⟩ : ↥Q)) := rfl
  have hcomm : (x : C) * (y : C) = (y : C) * (x : C) :=
    CFSG.Open.IsElemAbelian.comm hEa x.2 y.2
  have hxne : φE x ≠ 1 := fun h => hv0 (by
    apply Subtype.ext
    rw [← hx, h]
    rfl)
  have hyne : φE y ≠ 1 := fun h => hw0 (by
    apply Subtype.ext
    rw [← hy, h]
    rfl)
  have hxyne : φE x ≠ φE y := fun h => hvw (by
    apply Subtype.ext
    rw [← hx, ← hy, h])
  refine ⟨Multiplicative.toAdd (φE x), Multiplicative.toAdd (φE y), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hconj : conjAut hQn ρ (⟨(x : C), hxQ⟩ : ↥Q) = ⟨(x : C), hxQ⟩ := by
      apply Subtype.ext
      rw [conjAut_apply]
      have hc : (x : C) * ρ = ρ * (x : C) :=
        Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (hEle x.2)).2
      calc ρ * (x : C) * ρ⁻¹ = ((x : C) * ρ) * ρ⁻¹ := by rw [hc]
        _ = x := by group
    rw [hxphi, conjLinEquiv_apply, hconj]
  · have hconj : conjAut hQn ρ (⟨(y : C), hyQ⟩ : ↥Q) = ⟨(y : C), hyQ⟩ := by
      apply Subtype.ext
      rw [conjAut_apply]
      have hc : (y : C) * ρ = ρ * (y : C) :=
        Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (hEle y.2)).2
      calc ρ * (y : C) * ρ⁻¹ = ((y : C) * ρ) * ρ⁻¹ := by rw [hc]
        _ = y := by group
    rw [hyphi, conjLinEquiv_apply, hconj]
  · intro h
    apply hxne
    apply Multiplicative.toAdd.injective
    simpa using h
  · intro h
    apply hyne
    apply Multiplicative.toAdd.injective
    simpa using h
  · exact hxyne
  · rw [hxphi]
    exact (extraspecialQuadForm_apply hE (⟨(x : C), hxQ⟩ : ↥Q)).trans
      (if_pos (Subtype.ext (hEa.2 (x : C) x.2)))
  · rw [hyphi]
    exact (extraspecialQuadForm_apply hE (⟨(y : C), hyQ⟩ : ↥Q)).trans
      (if_pos (Subtype.ext (hEa.2 (y : C) y.2)))
  · rw [hxphi, hyphi]
    exact (polar_extraspecialQuadForm_eq_zero_iff hE (⟨(x : C), hxQ⟩ : ↥Q)
      (⟨(y : C), hyQ⟩ : ↥Q)).mpr (Subtype.ext hcomm)

end CFSG.EvenSporadicStandard.HNRecog.CSide
