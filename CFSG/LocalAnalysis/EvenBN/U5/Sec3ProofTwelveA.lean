module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3TwelveCommon
public import CFSG.LocalAnalysis.EvenBN.U5.CaseBSharedPartsB

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open scoped MatrixGroups commutatorElement

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem sec312_bar_FK (hp : d.CaseHyp) (k : d.Know10) {X Y : Subgroup G}
    (hXM : X ≤ d.M₁) (hYM : Y ≤ d.M₁) (hXY : X ⊔ Y = d.M₁) {V₁ : Subgroup (Bar d.F)}
    (hV₁V : V₁ ≤ bar d.F d.D)
    (hXN : bar d.F X ≤ normalizer (V₁ : Set (Bar d.F)))
    (hYc : bar d.F Y ≤ centralizer (V₁ : Set (Bar d.F)))
    (hXYc : ∀ x ∈ bar d.F X, ∀ y ∈ bar d.F Y, x * y = y * x)
    (hcomm : ⁅V₁, bar d.F X⁆ = V₁)
    (hVX : ∀ v ∈ bar d.F d.D, ∀ x ∈ bar d.F X, v * x * v⁻¹ * x⁻¹ ∈ V₁) :
    bar d.F (d.F ⊔ d.Kc X) = V₁ ⊔ bar d.F X := by
  have hDN := sec312_D_le_N_F hp k
  have hMN := sec312_M₁_le_N_F hp k
  have hVsq := sec312_bar_sq hp k
  have hVc : ∀ a ∈ bar d.F d.D, ∀ b ∈ bar d.F d.D, a * b = b * a := fun a ha b hb =>
    Common.mul_comm_of_mul_self hVsq ha hb
  have hXL : X ≤ d.L₁ := hXM.trans (sec312_M₁_le_L₁ k)
  have hXN' : X ≤ normalizer (d.F : Set G) := hXM.trans hMN
  have hYN' : Y ≤ normalizer (d.F : Set G) := hYM.trans hMN
  have hL₁N := sec312_L₁_le_N_F hp k
  apply le_antisymm
  · set T : Subgroup G := lift (V₁ ⊔ bar d.F X) with hT
    have hXT : X ≤ T := fun x hx => mem_lift_of_proj_mem (x := ⟨x, hXN' hx⟩)
      (Subgroup.mem_sup_right (proj_mem_bar (A := d.F) (x := ⟨x, hXN' hx⟩) hx))
    have hVnorm : bar d.F d.D ≤ normalizer ((V₁ ⊔ bar d.F X : Subgroup (Bar d.F)) :
        Set (Bar d.F)) := Sec312.normalizer_sup_of_comm hV₁V hVc hXN hVX
    have hDT : d.D ≤ normalizer (T : Set G) := fun g hg =>
      Sec312.mem_normalizer_lift (hDN hg) (hVnorm (proj_mem_bar (A := d.F) (x := ⟨g, hDN hg⟩) hg))
    have hMT : d.M₁ ≤ normalizer (T : Set G) := by
      rw [← hXY]
      refine sup_le (fun g hg => ?_) (fun g hg => ?_)
      · refine Sec312.mem_normalizer_lift (hXN' hg) ?_
        have hgx := proj_mem_bar (A := d.F) (x := ⟨g, hXN' hg⟩) hg
        exact Common.mem_normalizer_sup (hXN hgx) (le_normalizer hgx)
      · refine Sec312.mem_normalizer_lift (hYN' hg) ?_
        have hgy := proj_mem_bar (A := d.F) (x := ⟨g, hYN' hg⟩) hg
        exact Common.mem_normalizer_sup ((centralizer_le_normalizer _) (hYc hgy))
          ((centralizer_le_normalizer _) (mem_centralizer_iff.2 fun x hx =>
            hXYc x hx _ hgy))
    have hLT : d.L₁ ≤ normalizer (T : Set G) := by
      rw [sec312_L₁_eq k]
      exact sup_le hDT hMT
    have hKT : d.Kc X ≤ T := normalClosureIn_le hXT hLT
    have hFKT : d.F ⊔ d.Kc X ≤ T := sup_le (le_lift _) hKT
    calc bar d.F (d.F ⊔ d.Kc X) ≤ bar d.F T := bar_mono hFKT
      _ = V₁ ⊔ bar d.F X := bar_lift _
  · set B := bar d.F (d.F ⊔ d.Kc X) with hB
    have hXK : X ≤ d.Kc X := le_normalClosureIn hXL
    have hXB : bar d.F X ≤ B := bar_mono (hXK.trans le_sup_right)
    have hDnorm : d.D ≤ normalizer ((d.F ⊔ d.Kc X : Subgroup G) : Set G) := fun g hg =>
      Common.mem_normalizer_sup (hL₁N (d.D_le_L₁ hg))
        (le_normalizer_normalClosureIn d.L₁ X (d.D_le_L₁ hg))
    have hVB : bar d.F d.D ≤ normalizer (B : Set (Bar d.F)) :=
      bar_le_normalizer_bar le_sup_left hDnorm
    have hV₁B : V₁ ≤ B := by
      calc V₁ = ⁅V₁, bar d.F X⁆ := hcomm.symm
        _ ≤ B := by
          refine Subgroup.commutator_le.2 fun v hv x hx => ?_
          have h1 : v * x * v⁻¹ ∈ B := (mem_normalizer_iff.1 (hVB (hV₁V hv)) x).1 (hXB hx)
          have e : ⁅v, x⁆ = (v * x * v⁻¹) * x⁻¹ := by
            simp only [commutatorElement_def]
          rw [e]
          exact mul_mem h1 (inv_mem (hXB hx))
    exact sup_le hV₁B hXB

theorem sec312A_of_hyp (hp : d.CaseHyp) (k : d.Know11) : d.Sec312A := by
  intro κ _ _ hκ ψ
  have k10 : d.Know10 := k.toKnow10
  obtain ⟨S, hS, hP⟩ := sec312_exists_S hp
  haveI hc : CharP κ 2 := sec312_charP hκ
  have hkκ := sec312_card_eq hκ
  have hm : 2 ≤ 2 * f := by have := sec312_two_le hp; omega
  have hm3 : 2 * f ≠ 3 := by omega
  have ht : d.t ∈ normalizer (d.F : Set G) := hp.hyp.t_mem_normalizer_F
  have hset := sec312_setting hp k hS hP hκ ψ
  have hXM : Common.prodFactorOne ψ ≤ d.M₁ := Common.prodFactorOne_le ψ
  have hYM : Common.prodFactorTwo ψ ≤ d.M₁ := Common.prodFactorTwo_le ψ
  have hXYsup : Common.prodFactorOne ψ ⊔ Common.prodFactorTwo ψ = d.M₁ :=
    Common.prodFactorOne_sup_prodFactorTwo ψ
  have hDN := sec312_D_le_N_F hp k10
  have hMN := sec312_M₁_le_N_F hp k10
  have hL₁N := sec312_L₁_le_N_F hp k10
  have hXN : Common.prodFactorOne ψ ≤ normalizer (d.F : Set G) := hXM.trans hMN
  have hYN : Common.prodFactorTwo ψ ≤ normalizer (d.F : Set G) := hYM.trans hMN
  have φX' : bar d.F (Common.prodFactorOne ψ) ≃* SL(2, κ) :=
    (Sec312.barEquiv hXN (sec312_inf_F_of_le_M₁ hp k10 hXM)).symm.trans
      (Common.prodFactorOneEquiv ψ)
  have φY' : bar d.F (Common.prodFactorTwo ψ) ≃* SL(2, κ) :=
    (Sec312.barEquiv hYN (sec312_inf_F_of_le_M₁ hp k10 hYM)).symm.trans
      (Common.prodFactorTwoEquiv ψ)
  obtain ⟨hsup, hinf, hcX, hcY⟩ := hset.pairDecomp φX' φY' hkκ hm
  obtain ⟨hcomm, hVX⟩ := Sec312.comm_of_decomp φX' hkκ hm hm3 hset.sq hset.normX hset.comm hsup
    hinf hcY
  set V : Subgroup (Bar d.F) := bar d.F d.D with hV
  set V₁ : Subgroup (Bar d.F) :=
    V ⊓ centralizer ((bar d.F (Common.prodFactorTwo ψ) : Subgroup (Bar d.F)) : Set (Bar d.F))
    with hV₁
  set V₂ : Subgroup (Bar d.F) :=
    V ⊓ centralizer ((bar d.F (Common.prodFactorOne ψ) : Subgroup (Bar d.F)) : Set (Bar d.F))
    with hV₂
  have hV₁V : V₁ ≤ V := inf_le_left
  have hV₂V : V₂ ≤ V := inf_le_left
  have hXN₁ : bar d.F (Common.prodFactorOne ψ) ≤ normalizer (V₁ : Set (Bar d.F)) :=
    Sec312.normalizer_inf_centralizer hset.normX hset.comm
  have hYN₂ : bar d.F (Common.prodFactorTwo ψ) ≤ normalizer (V₂ : Set (Bar d.F)) :=
    Sec312.normalizer_inf_centralizer hset.normY fun y hy x hx => (hset.comm x hx y hy).symm
  have hYc : bar d.F (Common.prodFactorTwo ψ) ≤ centralizer (V₁ : Set (Bar d.F)) := fun y hy =>
    mem_centralizer_iff.2 fun v hv => (mem_centralizer_iff.1 hv.2 y hy).symm
  have hK : bar d.F (d.F ⊔ d.Kc (Common.prodFactorOne ψ)) =
      V₁ ⊔ bar d.F (Common.prodFactorOne ψ) :=
    sec312_bar_FK hp k10 hXM hYM hXYsup hV₁V hXN₁ hYc hset.comm hcomm hVX
  have hτV : V₁.map (MulAut.conj (proj d.F ⟨d.t, ht⟩)).toMonoidHom = V₂ := by
    rw [hV₁, ← Prelim.inf_centralizer_map_conj hset.tNorm, hset.tMapY]
  have e1 : d.F ⊔ (d.Kc (Common.prodFactorOne ψ)).map (MulAut.conj d.t).toMonoidHom =
      (d.F ⊔ d.Kc (Common.prodFactorOne ψ)).map (MulAut.conj d.t).toMonoidHom := by
    rw [Subgroup.map_sup, map_conj_eq_of_mem_normalizer ht]
  have hKt : bar d.F (d.F ⊔ (d.Kc (Common.prodFactorOne ψ)).map
      (MulAut.conj d.t).toMonoidHom) = V₂ ⊔ bar d.F (Common.prodFactorTwo ψ) := by
    rw [e1, Sec312.bar_map_conj ht, hK, Subgroup.map_sup, hτV, hset.tMapX]
  have hbot : bar d.F (⊥ : Subgroup G) = ⊥ :=
    le_bot_iff.1 (Sec312.bar_self (A := d.F) ▸ bar_mono bot_le)
  have hbarXY : bar d.F (Common.prodFactorOne ψ) ⊓ bar d.F (Common.prodFactorTwo ψ) = ⊥ := by
    rw [Sec312.bar_inf_of_inf_eq_bot hMN (sec312_inf_F_of_le_M₁ hp k10 le_rfl) hXM hYM,
      Common.prodFactorOne_inf_prodFactorTwo ψ, hbot]
  have hbarM : bar d.F (Common.prodFactorOne ψ) ⊔ bar d.F (Common.prodFactorTwo ψ) =
      bar d.F d.M₁ := by
    rw [← Sec312.bar_sup hXN hYN, hXYsup]
  have hVM : V ⊓ (bar d.F (Common.prodFactorOne ψ) ⊔ bar d.F (Common.prodFactorTwo ψ)) = ⊥ := by
    rw [hbarM]
    exact sec312_bar_D_inf_M₁ hp k10
  have hlat := Sec312.sup_inf_decomp hV₁V hV₂V (by rw [sup_comm]; exact hsup)
    (by rw [inf_comm]; exact hinf) hbarXY hVM hXN₁ hYN₂
  have hKL : d.Kc (Common.prodFactorOne ψ) ≤ d.L₁ := normalClosureIn_le_self _ _
  have hKtL : (d.Kc (Common.prodFactorOne ψ)).map (MulAut.conj d.t).toMonoidHom ≤ d.L₁ :=
    calc (d.Kc (Common.prodFactorOne ψ)).map (MulAut.conj d.t).toMonoidHom
        ≤ d.L₁.map (MulAut.conj d.t).toMonoidHom := Subgroup.map_mono hKL
      _ = d.L₁ := map_conj_eq_of_mem_normalizer hp.hyp.t_mem_normalizer_L₁
  have hFK : d.F ⊔ d.Kc (Common.prodFactorOne ψ) ≤ normalizer (d.F : Set G) :=
    sup_le le_normalizer (hKL.trans hL₁N)
  have hFKt : d.F ⊔ (d.Kc (Common.prodFactorOne ψ)).map (MulAut.conj d.t).toMonoidHom ≤
      normalizer (d.F : Set G) := sup_le le_normalizer (hKtL.trans hL₁N)
  have hFL : d.F ≤ d.L₁ := (sec312_F_le_D hp k10).trans d.D_le_L₁
  refine ⟨?_, ?_⟩
  · refine Sec312.eq_of_bar_eq (A := d.F) (le_sup_left.trans le_sup_left) hFL
      (sup_le hFK hFKt) hL₁N ?_
    rw [Sec312.bar_sup hFK hFKt, hK, hKt, hlat.1, sec312_L₁_eq k10,
      Sec312.bar_sup hDN hMN, ← hbarM]
  · refine Sec312.eq_of_bar_eq (A := d.F) (le_inf le_sup_left le_sup_left) le_rfl
      (inf_le_left.trans hFK) le_normalizer ?_
    rw [Sec312.bar_inf le_sup_left le_sup_left, hK, hKt, hlat.2, Sec312.bar_self]

end Data

namespace CaseBParts

theorem sec312A : Sec312AStatement :=
  fun _ _ _ _ _ _ _ _ hp k => Data.sec312A_of_hyp hp k

end CaseBParts

end CFSG.LocalAnalysis.EvenBN.U5
