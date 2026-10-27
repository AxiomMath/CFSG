module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3TwelveCommon
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3TwelveGomi
public import CFSG.LocalAnalysis.EvenBN.U5.CaseBSharedPartsB

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open CFSG.Timmesfeld.ARS
open scoped MatrixGroups Matrix commutatorElement

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem sec312_Kc_le_D_sup_X (hp : d.CaseHyp) (k : d.Know10) {X Y : Subgroup G}
    (hXM : X ≤ d.M₁) (hYM : Y ≤ d.M₁) (hXY : X ⊔ Y = d.M₁)
    (hYX : Y ≤ centralizer (X : Set G)) : d.Kc X ≤ d.D ⊔ X := by
  have hXL : X ≤ d.L₁ := hXM.trans (sec312_M₁_le_L₁ k)
  have hYN : ∀ g ∈ Y, g ∈ normalizer ((d.D ⊔ X : Subgroup G) : Set G) := fun g hg =>
    Common.mem_normalizer_sup (sec312_L₁_le_N_D hp ((sec312_M₁_le_L₁ k) (hYM hg)))
      ((centralizer_le_normalizer _) (mem_centralizer_iff.2 fun x hx =>
        mem_centralizer_iff.1 (hYX hg) x hx))
  have hLN : d.L₁ ≤ normalizer ((d.D ⊔ X : Subgroup G) : Set G) := by
    rw [sec312_L₁_eq k]
    refine sup_le (fun g hg => le_normalizer (Subgroup.mem_sup_left hg)) ?_
    refine hXY.symm.le.trans (sup_le (fun g hg => le_normalizer (Subgroup.mem_sup_right hg)) hYN)
  exact normalClosureIn_le le_sup_right hLN

theorem sec312_M₁_inf_Kc (hp : d.CaseHyp) (k : d.Know10) {X Y : Subgroup G}
    (hXM : X ≤ d.M₁) (hYM : Y ≤ d.M₁) (hXY : X ⊔ Y = d.M₁)
    (hYX : Y ≤ centralizer (X : Set G)) : d.M₁ ⊓ d.Kc X = X := by
  have hXN : X ≤ normalizer (d.D : Set G) := hXM.trans ((sec312_M₁_le_L₁ k).trans (sec312_L₁_le_N_D hp))
  have hXK : X ≤ d.Kc X := le_normalClosureIn (hXM.trans (sec312_M₁_le_L₁ k))
  refine le_antisymm (fun g hg => ?_) (le_inf hXM hXK)
  have h1 : g ∈ ((d.D ⊔ X : Subgroup G) : Set G) := sec312_Kc_le_D_sup_X hp k hXM hYM hXY hYX hg.2
  rw [Subgroup.coe_mul_of_right_le_normalizer_left d.D X hXN] at h1
  obtain ⟨e, he, x, hx, hex⟩ := h1
  have he' : e ∈ d.D := he
  have hx' : x ∈ X := hx
  have hex' : e * x = g := hex
  have hmem : e ∈ d.D ⊓ d.M₁ := Subgroup.mem_inf.2 ⟨he', by
    have : e = g * x⁻¹ := by rw [← hex']; group
    rw [this]
    exact mul_mem hg.1 (inv_mem (hXM hx'))⟩
  rw [sec312_D_inf_M₁ k, Subgroup.mem_bot] at hmem
  rw [← hex', hmem, one_mul]
  exact hx'

theorem sec312B_of_hyp (hp : d.CaseHyp) (k : d.Know11) (ha : d.Sec312A) : d.Sec312B := by
  intro κ iF iT hκ ψ
  have k10 : d.Know10 := k.toKnow10
  obtain ⟨S, hS, hP⟩ := sec312_exists_S hp
  haveI hc : CharP κ 2 := sec312_charP hκ
  have hkκ := sec312_card_eq hκ
  have hm : 2 ≤ 2 * f := by have := sec312_two_le hp; omega
  have ht : d.t ∈ normalizer (d.F : Set G) := hp.hyp.t_mem_normalizer_F
  have hset := sec312_setting hp k hS hP hκ ψ
  have hXM : Common.prodFactorOne ψ ≤ d.M₁ := Common.prodFactorOne_le ψ
  have hYM : Common.prodFactorTwo ψ ≤ d.M₁ := Common.prodFactorTwo_le ψ
  have hXYsup : Common.prodFactorOne ψ ⊔ Common.prodFactorTwo ψ = d.M₁ :=
    Common.prodFactorOne_sup_prodFactorTwo ψ
  have hYX : Common.prodFactorTwo ψ ≤ centralizer (Common.prodFactorOne ψ : Set G) :=
    Common.prodFactorTwo_le_centralizer ψ
  have hFD := sec312_F_le_D hp k10
  have hDN := sec312_D_le_N_F hp k10
  have hMN := sec312_M₁_le_N_F hp k10
  have hL₁N := sec312_L₁_le_N_F hp k10
  have hXN : Common.prodFactorOne ψ ≤ normalizer (d.F : Set G) := hXM.trans hMN
  have hYN : Common.prodFactorTwo ψ ≤ normalizer (d.F : Set G) := hYM.trans hMN
  have hXF := sec312_inf_F_of_le_M₁ hp k10 hXM
  set φX' : bar d.F (Common.prodFactorOne ψ) ≃* SL(2, κ) :=
    (Sec312.barEquiv hXN hXF).symm.trans (Common.prodFactorOneEquiv ψ) with hφX'
  have hA := ha κ iF iT hκ ψ
  have hKL : d.Kc (Common.prodFactorOne ψ) ≤ d.L₁ := normalClosureIn_le_self _ _
  have hKtL : (d.Kc (Common.prodFactorOne ψ)).map (MulAut.conj d.t).toMonoidHom ≤ d.L₁ :=
    calc (d.Kc (Common.prodFactorOne ψ)).map (MulAut.conj d.t).toMonoidHom
        ≤ d.L₁.map (MulAut.conj d.t).toMonoidHom := Subgroup.map_mono hKL
      _ = d.L₁ := map_conj_eq_of_mem_normalizer hp.hyp.t_mem_normalizer_L₁
  have hFK : d.F ⊔ d.Kc (Common.prodFactorOne ψ) ≤ normalizer (d.F : Set G) :=
    sup_le le_normalizer (hKL.trans hL₁N)
  have hFKt : d.F ⊔ (d.Kc (Common.prodFactorOne ψ)).map (MulAut.conj d.t).toMonoidHom ≤
      normalizer (d.F : Set G) := sup_le le_normalizer (hKtL.trans hL₁N)
  have hLFK : d.L₁ ≤ normalizer ((d.F ⊔ d.Kc (Common.prodFactorOne ψ) : Subgroup G) : Set G) :=
    fun g hg => Common.mem_normalizer_sup (hL₁N hg)
      (le_normalizer_normalClosureIn d.L₁ (Common.prodFactorOne ψ) hg)
  have hLFKt : d.L₁ ≤ normalizer
      ((d.F ⊔ (d.Kc (Common.prodFactorOne ψ)).map (MulAut.conj d.t).toMonoidHom : Subgroup G) :
        Set G) := fun g hg => Common.mem_normalizer_sup (hL₁N hg)
    (Sec312.le_normalizer_map_conj hp.hyp.t_mem_normalizer_L₁
      (le_normalizer_normalClosureIn d.L₁ (Common.prodFactorOne ψ)) hg)
  set K₁ : Subgroup (Bar d.F) := bar d.F (d.F ⊔ d.Kc (Common.prodFactorOne ψ)) with hK₁
  set K₂ : Subgroup (Bar d.F) := bar d.F (d.F ⊔
    (d.Kc (Common.prodFactorOne ψ)).map (MulAut.conj d.t).toMonoidHom) with hK₂
  have e1 : d.F ⊔ (d.Kc (Common.prodFactorOne ψ)).map (MulAut.conj d.t).toMonoidHom =
      (d.F ⊔ d.Kc (Common.prodFactorOne ψ)).map (MulAut.conj d.t).toMonoidHom := by
    rw [Subgroup.map_sup, map_conj_eq_of_mem_normalizer ht]
  have hτ : K₁.map (MulAut.conj (proj d.F ⟨d.t, ht⟩)).toMonoidHom = K₂ := by
    rw [hK₁, hK₂, e1, Sec312.bar_map_conj ht]
  have hKsup : K₁ ⊔ K₂ = bar d.F d.L₁ := by
    rw [hK₁, hK₂, ← Sec312.bar_sup hFK hFKt, hA.1]
  have hKinf : K₁ ⊓ K₂ = ⊥ := by
    rw [hK₁, hK₂, ← Sec312.bar_inf le_sup_left le_sup_left, hA.2, Sec312.bar_self]
  have hK₁L : K₁ ≤ bar d.F d.L₁ := bar_mono (sup_le (hFD.trans d.D_le_L₁) hKL)
  have hK₂L : K₂ ≤ bar d.F d.L₁ := bar_mono (sup_le (hFD.trans d.D_le_L₁) hKtL)
  have hcomm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a :=
    Sec312.commute_of_normal_of_inf_eq_bot hK₁L hK₂L
      (bar_le_normalizer_bar le_sup_left hLFK) (bar_le_normalizer_bar le_sup_left hLFKt) hKinf
  have hVK : bar d.F d.D ≤ K₁ ⊔ K₂ := hKsup ▸ bar_mono d.D_le_L₁
  have hK₁V : K₁ ≤ bar d.F d.D ⊔ bar d.F (Common.prodFactorOne ψ) := by
    rw [← Sec312.bar_sup hDN hXN]
    exact bar_mono (sup_le (hFD.trans le_sup_left)
      (sec312_Kc_le_D_sup_X hp k10 hXM hYM hXYsup hYX))
  have hVt : (bar d.F d.D).map (MulAut.conj (proj d.F ⟨d.t, ht⟩)).toMonoidHom = bar d.F d.D := by
    rw [← Sec312.bar_map_conj ht, map_conj_eq_of_mem_normalizer hp.hyp.t_mem_normalizer_D]
  have hK₂V : K₂ ≤ bar d.F d.D ⊔ bar d.F (Common.prodFactorTwo ψ) := by
    rw [← hτ]
    calc K₁.map (MulAut.conj (proj d.F ⟨d.t, ht⟩)).toMonoidHom
        ≤ (bar d.F d.D ⊔ bar d.F (Common.prodFactorOne ψ)).map
            (MulAut.conj (proj d.F ⟨d.t, ht⟩)).toMonoidHom := Subgroup.map_mono hK₁V
      _ = bar d.F d.D ⊔ bar d.F (Common.prodFactorTwo ψ) := by
          rw [Subgroup.map_sup, hVt, hset.tMapX]
  have hXL : Common.prodFactorOne ψ ≤ d.L₁ := hXM.trans (sec312_M₁_le_L₁ k10)
  have hXK : bar d.F (Common.prodFactorOne ψ) ≤ K₁ :=
    bar_mono ((le_normalClosureIn hXL).trans le_sup_right)
  have hYK : bar d.F (Common.prodFactorTwo ψ) ≤ K₂ := by
    calc bar d.F (Common.prodFactorTwo ψ)
        = (bar d.F (Common.prodFactorOne ψ)).map
            (MulAut.conj (proj d.F ⟨d.t, ht⟩)).toMonoidHom := hset.tMapX.symm
      _ ≤ K₁.map (MulAut.conj (proj d.F ⟨d.t, ht⟩)).toMonoidHom := Subgroup.map_mono hXK
      _ = K₂ := hτ
  have hbot : bar d.F (⊥ : Subgroup G) = ⊥ :=
    le_bot_iff.1 (Sec312.bar_self (A := d.F) ▸ bar_mono bot_le)
  have hbarXY : bar d.F (Common.prodFactorOne ψ) ⊓ bar d.F (Common.prodFactorTwo ψ) = ⊥ := by
    rw [Sec312.bar_inf_of_inf_eq_bot hMN (sec312_inf_F_of_le_M₁ hp k10 le_rfl) hXM hYM,
      Common.prodFactorOne_inf_prodFactorTwo ψ, hbot]
  have hbarM : bar d.F (Common.prodFactorOne ψ) ⊔ bar d.F (Common.prodFactorTwo ψ) =
      bar d.F d.M₁ := by
    rw [← Sec312.bar_sup hXN hYN, hXYsup]
  have hVM : bar d.F d.D ⊓ (bar d.F (Common.prodFactorOne ψ) ⊔
      bar d.F (Common.prodFactorTwo ψ)) = ⊥ := by
    rw [hbarM]
    exact sec312_bar_D_inf_M₁ hp k10
  obtain ⟨θb, hθ, hrange⟩ := Sec312.natural_module_of_decomposition hset φX' hkκ hm hcomm hVK
    hK₁V hK₂V hXK hYK hKinf hVM hbarXY hτ
  have hMK := sec312_M₁_inf_Kc hp k10 hXM hYM hXYsup hYX
  rw [hMK]
  refine Sec312.isNaturalSection_of_bar (A := d.F) (X' := Common.prodFactorOne ψ)
    (A' := (d.F ⊔ d.Kc (Common.prodFactorOne ψ)) ⊓ d.D) (le_inf le_sup_left hFD)
    (inf_le_right.trans hDN) hXN (Common.prodFactorOneEquiv ψ) θb hθ.map_add hθ.injective ?_ ?_
  · rw [Sec312.bar_inf le_sup_left hFD]
    exact hrange
  · intro x v
    have h1 := hθ.map_mulVec (Sec312.barEquiv hXN hXF x) v
    have h2 : φX' (Sec312.barEquiv hXN hXF x) = Common.prodFactorOneEquiv ψ x := by
      rw [hφX']
      simp
    rw [h2] at h1
    exact h1

end Data

namespace CaseBParts

theorem sec312B : Sec312BStatement :=
  fun _ _ _ _ _ _ _ _ hp k ha => Data.sec312B_of_hyp hp k ha

end CaseBParts

end CFSG.LocalAnalysis.EvenBN.U5
