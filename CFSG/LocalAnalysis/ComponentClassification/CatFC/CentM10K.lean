module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentM10Arms
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentM10KAux

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)


section Plumbing

variable {K : Type} [Group K] [Finite K] {S D : Subgroup K} {z : K}

theorem nonabelian_of_centralizer_bot (S : Subgroup K) [IsSimpleGroup ↥S]
    (hC : centralizer (S : Set K) = ⊥) : ∃ a b : ↥S, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hS : S = ⊥ := by
    rw [eq_bot_iff, ← hC]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (h ⟨y, hy⟩ ⟨x, hx⟩)
  obtain ⟨a, ha⟩ := exists_ne (1 : ↥S)
  have : (a : K) ∈ (⊥ : Subgroup K) := hS ▸ a.2
  exact ha (Subtype.ext (by simpa using this))

theorem M10Cfg.card_D (cfg : M10Cfg S D z) : Nat.card ↥D = 360 := by
  obtain ⟨e⟩ := cfg.hDA
  rw [Nat.card_congr e.toEquiv]
  exact alt6_card

theorem M10Cfg.normal_subgroupOf (cfg : M10Cfg S D z) {F : Subgroup K}
    (hF : F ≤ centralizer ({z} : Set K)) :
    (D.subgroupOf F).Normal := by
  refine ⟨fun d hd f => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hd ⊢
  simpa using cfg.hDn (f : K) (hF f.2) (d : K) hd

end Plumbing

variable {K : Type} [Group K] [Finite K] {S D : Subgroup K} {z : K}

theorem M10Cfg.inner_false (hI : A6InnerLieSmall)
    (hZ : CFSG.EvenSporadicStandard.CatNoAlmostSimpleZ2 (alternatingGroup (Fin 6)))
    [S.Normal] [IsSimpleGroup ↥S] (hcat : Catalog ↥S) (hC : centralizer (S : Set K) = ⊥)
    (cfg : M10Cfg S D z) (hzS : z ∈ S) : False := by
  have hna := nonabelian_of_centralizer_bot S hC
  obtain ⟨eD⟩ := cfg.hDA
  set C := centralizer ({z} : Set K) with hCdef
  set F : Subgroup K := S ⊓ C with hFdef
  let z' : ↥S := ⟨z, hzS⟩
  have hz' : orderOf z' = 2 := by
    rw [← cfg.hz]
    exact Subgroup.orderOf_mk z hzS
  have hDF : D ≤ F := le_inf cfg.hDS cfg.hDC
  have hFC : F ≤ C := inf_le_right
  haveI hN : (D.subgroupOf F).Normal := cfg.normal_subgroupOf hFC
  have hmap : (centralizer ({z'} : Set ↥S)).map S.subtype = F :=
    map_centralizer_subtype_eq_inf S z'
  let e₁ : ↥(centralizer ({z'} : Set ↥S)) ≃* ↥F :=
    (Subgroup.equivMapOfInjective _ S.subtype S.subtype_injective).trans
      (MulEquiv.subgroupCongr hmap)
  have hDA : Nonempty (↥(D.subgroupOf F) ≃* alternatingGroup (Fin 6)) :=
    ⟨(Subgroup.subgroupOfEquivOfLe hDF).trans eD⟩
  obtain ⟨D', hD'n, hD'A, -⟩ := exists_normal_of_mulEquiv e₁ (D.subgroupOf F) hDA
  have hcardF : Nat.card ↥(centralizer ({z'} : Set ↥S)) = Nat.card ↥F :=
    Nat.card_congr e₁.toEquiv
  have hdvd : Nat.card ↥F ∣ 1440 := cfg.hcard ▸ Subgroup.card_dvd_of_le hFC
  have hzF : z ∈ F := Subgroup.mem_inf.2 ⟨hzS, mem_centralizer_singleton_iff.2 rfl⟩
  let ζ : ↥F := ⟨z, hzF⟩
  have hζ2 : orderOf ζ = 2 := by
    rw [← cfg.hz]
    exact Subgroup.orderOf_mk z hzF
  have hζD : ζ ∉ D.subgroupOf F := fun h => cfg.hzD h
  have hNcard : Nat.card ↥(D.subgroupOf F) = 360 := by
    rw [← cfg.card_D]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDF).toEquiv
  have hsup : Nat.card ↥(D.subgroupOf F ⊔ zpowers ζ) = 720 := by
    rw [CFSG.Sporadic.SmallOddCore.card_sup_zpowers (u := ζ) (P := D.subgroupOf F)
      (by rw [← hζ2]; exact pow_orderOf_eq_one ζ) ?_ hζD, hNcard]
    intro p hp
    have hpC : (p : K) ∈ C := hFC p.2
    have hzC : z * p = p * z := (mem_centralizer_singleton_iff.1 hpC).symm
    have : ζ * p * ζ⁻¹ = p := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      show z * (p : K) * z⁻¹ = p
      rw [hzC, mul_inv_cancel_right]
    rw [this]
    exact hp
  have h720 : 720 ∣ Nat.card ↥F := hsup ▸ Subgroup.card_subgroup_dvd_card _
  have hF : Nat.card ↥F = 720 ∨ Nat.card ↥F = 1440 := by
    obtain ⟨k, hk⟩ := h720
    have : Nat.card ↥F ≤ 1440 := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < Nat.card ↥F := Nat.card_pos
    rcases k with _ | _ | _ | k
    · omega
    · omega
    · omega
    · omega
  rcases hF with h | h
  ·
    have hcentre : ζ ∈ Subgroup.center ↥F := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact (mem_centralizer_singleton_iff.1 (hFC g.2))
    obtain ⟨eP⟩ := mulEquiv_prod_of_central (D.subgroupOf F) hζ2 hcentre hζD
      (by rw [h, hNcard])
    exact noInnerZ2_of_cat hZ ↥S hna hcat z' hz'
      ⟨e₁.trans (eP.trans (MulEquiv.prodCongr (MulEquiv.refl _)
        ((Subgroup.subgroupOfEquivOfLe hDF).trans eD)))⟩
  · exact arm_inner hI hna hcat hz' (hcardF.trans h) D' hD'A

theorem M10Cfg.outer_x0 (hO : A6OuterLieSmall) [S.Normal] [IsSimpleGroup ↥S] (hcat : Catalog ↥S)
    (hC : centralizer (S : Set K) = ⊥) (cfg : M10Cfg S D z) (hzS : z ∉ S) :
    Nonempty (↥S ≃* CFSG.LieType.Multipliers.U43.X₀) := by
  have hna := nonabelian_of_centralizer_bot S hC
  obtain ⟨eD⟩ := cfg.hDA
  set C := centralizer ({z} : Set K) with hCdef
  have hz2 : z ^ 2 = 1 := by
    rw [← cfg.hz]
    exact pow_orderOf_eq_one z
  set σ : MulAut ↥S := MulAut.conjNormal (H := S) z with hσdef
  have hσ2 : σ ^ 2 = 1 := by
    rw [hσdef, ← map_pow, hz2, map_one]
  have hσ1 : σ ≠ 1 := by
    intro h
    have hzc : z ∈ centralizer (S : Set K) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have := congrArg (fun f : MulAut ↥S => ((f ⟨s, hs⟩ : ↥S) : K)) h
      simp only [hσdef, MulAut.conjNormal_apply, MulAut.one_apply] at this
      exact (mul_inv_eq_iff_eq_mul.1 this).symm
    rw [hC, Subgroup.mem_bot] at hzc
    have h1 := cfg.hz
    rw [hzc, orderOf_one] at h1
    exact absurd h1 (by norm_num)
  have hσ : orderOf σ = 2 := orderOf_eq_prime hσ2 hσ1
  have hout : σ ∉ (MulAut.conj : ↥S →* MulAut ↥S).range := by
    rintro ⟨s, hs⟩
    have hzc : (s : K)⁻¹ * z ∈ centralizer (S : Set K) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have := congrArg (fun f : MulAut ↥S => ((f ⟨x, hx⟩ : ↥S) : K)) hs
      simp only [hσdef, MulAut.conjNormal_apply, MulAut.conj_apply] at this
      calc x * ((s : K)⁻¹ * z) = (s : K)⁻¹ * ((s : K) * x * (s : K)⁻¹) * z := by group
        _ = (s : K)⁻¹ * (z * x * z⁻¹) * z := by
          rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at this
          rw [this]
        _ = (s : K)⁻¹ * z * x := by group
    rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hzc
    exact hzS (hzc ▸ s.2)
  let T : Subgroup ↥C := S.subgroupOf C
  let e₂ := CFSG.ComponentClassification.FixedNormalCentralizer.equivalence S z
  let DC : Subgroup ↥C := D.subgroupOf C
  haveI hDCn : DC.Normal := ⟨fun d hd c => by
    rw [Subgroup.mem_subgroupOf] at hd ⊢
    simpa using cfg.hDn (c : K) c.2 (d : K) hd⟩
  have hDCT : DC ≤ T := fun x hx => cfg.hDS hx
  let DT : Subgroup ↥T := DC.subgroupOf T
  haveI hDTn : DT.Normal := Subgroup.Normal.subgroupOf hDCn T
  have hDTA : Nonempty (↥DT ≃* alternatingGroup (Fin 6)) :=
    ⟨(Subgroup.subgroupOfEquivOfLe hDCT).trans
      ((Subgroup.subgroupOfEquivOfLe (fun x hx => cfg.hDC hx : D ≤ C)).trans eD)⟩
  obtain ⟨Dσ, hDσn, hDσA, hDσmem⟩ := exists_normal_of_mulEquiv e₂.symm DT hDTA
  have hDTcard : Nat.card ↥DT = 360 := by
    rw [← cfg.card_D]
    exact Nat.card_congr ((Subgroup.subgroupOfEquivOfLe hDCT).trans
      (Subgroup.subgroupOfEquivOfLe (fun x hx => cfg.hDC hx : D ≤ C))).toEquiv
  have hCcard : Nat.card ↥C = 1440 := cfg.hcard
  have hTdvd : Nat.card ↥T ∣ 1440 := hCcard ▸ Subgroup.card_subgroup_dvd_card T
  have h360 : 360 ∣ Nat.card ↥T := hDTcard ▸ Subgroup.card_subgroup_dvd_card DT
  have hTne : Nat.card ↥T ≠ 1440 := by
    intro h
    have htop : T = ⊤ := by
      rw [← Subgroup.card_eq_iff_eq_top]
      rw [h, hCcard]
    have hz'T : (⟨z, mem_centralizer_singleton_iff.2 rfl⟩ : ↥C) ∈ T := by
      rw [htop]
      exact Subgroup.mem_top _
    exact hzS hz'T
  have hfix : Nat.card ↥(fixedSubgroup σ) = Nat.card ↥T := (Nat.card_congr e₂.toEquiv).symm
  have hcard : Nat.card ↥(fixedSubgroup σ) = 360 ∨ Nat.card ↥(fixedSubgroup σ) = 720 := by
    rw [hfix]
    obtain ⟨k, hk⟩ := h360
    have hle : Nat.card ↥T ≤ 1440 := Nat.le_of_dvd (by norm_num) hTdvd
    have hpos : 0 < Nat.card ↥T := Nat.card_pos
    have hk4 : k ≤ 4 := by omega
    interval_cases k
    · omega
    · left
      omega
    · right
      omega
    · rw [hk] at hTdvd
      norm_num at hTdvd
    · exact absurd (by omega : Nat.card ↥T = 1440) hTne
  have hinv : ∀ x : ↥(fixedSubgroup σ), orderOf x = 2 → x ∈ Dσ := by
    intro x hx2
    rw [hDσmem]
    have hy2 : orderOf (e₂.symm x) = 2 := by
      rw [← hx2]
      exact MulEquiv.orderOf_eq e₂.symm x
    have hk2 : orderOf (((e₂.symm x : ↥T) : ↥C) : K) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
      exact hy2
    have hkk : (((e₂.symm x : ↥T) : ↥C) : K) * (((e₂.symm x : ↥T) : ↥C) : K) = 1 := by
      have : (((e₂.symm x : ↥T) : ↥C) : K) ^ 2 = 1 := by
        rw [← hk2]
        exact pow_orderOf_eq_one _
      simpa [sq] using this
    have hkS : (((e₂.symm x : ↥T) : ↥C) : K) ∈ S := (e₂.symm x : ↥T).2
    have hkC : (((e₂.symm x : ↥T) : ↥C) : K) ∈ C := ((e₂.symm x : ↥T) : ↥C).2
    have hkD := cfg.inv_mem_D hzS hkS hkC hkk
    show e₂.symm x ∈ DC.subgroupOf T
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact hkD
  haveI := hDσn
  exact (arm_outer hO hna hcat hσ hout hcard Dσ hDσA hinv).1

end CFSG.ComponentClassification.CatFC
