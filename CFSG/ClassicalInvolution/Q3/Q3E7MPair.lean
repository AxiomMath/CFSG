module

public import CFSG.ClassicalInvolution.Q3.Q3E7MClass
public import CFSG.ClassicalInvolution.ModelFacts.E7ModelPair

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.ModelFacts.Levi CFSG.ClassicalInvolution.ModelFacts
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD CFSG.Timmesfeld
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.ModelFacts.E7Model CFSG.LieType.HighestRoot
open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open scoped commutatorElement MatrixGroups

set_option linter.unusedSectionVars false


local notation "M₇" => E7sc 3 1
local notation "D₇" => e7Datum (GaloisField 3 1)


section AdjFrame

local notation "ρθ" => rootSL2 Tag.E7 (GaloisField 3 1) thetaE7
local notation "dθ" => rootDiagUnit Tag.E7 (thetaDiag thetaE7 (-1 : (GaloisField 3 1)ˣ))
local notation "Lθ" => rootRankOneGroup Tag.E7 (GaloisField 3 1) thetaE7

theorem exists_frame_adj_e7_3 {u₂ : ModGL .E7 (GaloisField 3 1)}
    (hu₂ : u₂ ∈ adjointGroup .E7 (GaloisField 3 1))
    (hcd : (u₂ * dθ * u₂⁻¹) * dθ = dθ * (u₂ * dθ * u₂⁻¹))
    {U : Subgroup (SL2 (GaloisField 3 1))} (hU : Nat.card U = Nat.card (GaloisField 3 1))
    (hinv : ∀ A ∈ U, (u₂ * dθ * u₂⁻¹) * ρθ A * (u₂ * dθ * u₂⁻¹)⁻¹ = (ρθ A)⁻¹)
    (hne : (Lθ).map (MulAut.conj u₂).toMonoidHom ≠ Lθ)
    (hnc : ¬ ∀ x ∈ Lθ, ∀ y ∈ (Lθ).map (MulAut.conj u₂).toMonoidHom, x * y = y * x) :
    ∃ (γ : Fin (Tag.rank .E7) → ℤ) (w : ModGL .E7 (GaloisField 3 1)), IsRoot .E7 γ ∧
      (iform thetaE7 γ = 1 ∨ iform thetaE7 γ = -1) ∧ w ∈ adjointGroup .E7 (GaloisField 3 1) ∧
      w * dθ = dθ * w ∧ (Lθ).map (MulAut.conj (w * u₂)).toMonoidHom = rootRankOneGroup .E7 _ γ := by
  have hF : ringChar (GaloisField 3 1) ≠ 2 := ringChar_galoisField_ne_two (by norm_num)
  have hodd : Odd (Nat.card (GaloisField 3 1)) := odd_gf3
  have hcard : Nat.card (GaloisField 3 1) = 3 ^ 1 := GaloisField.card 3 1 (by norm_num)
  have hdθ : dθ = ρθ (HSL (-1)) := (rootTorusSL2_thetaE7 (-1)).symm
  have hdG : dθ ∈ adjointGroup .E7 (GaloisField 3 1) := by
    rw [hdθ]
    exact LieType.Chevalley.rootSL2_mem_adjointGroup _ _
  have hd2 : dθ * dθ = 1 := by
    rw [hdθ, ← map_mul, HSL_neg_one_mul_self, map_one]
  set c := u₂ * dθ * u₂⁻¹ with hc
  have hcG : c ∈ adjointGroup .E7 (GaloisField 3 1) := mul_mem (mul_mem hu₂ hdG) (inv_mem hu₂)
  have hc2 : c * c = 1 := by
    rw [hc]
    calc u₂ * dθ * u₂⁻¹ * (u₂ * dθ * u₂⁻¹) = u₂ * (dθ * dθ) * u₂⁻¹ := by group
      _ = 1 := by rw [hd2]; group
  obtain ⟨e, hcL, hcU⟩ := exists_conj_mem_levi_of_inverts Fact.out hcard hF hcG hcd hU hinv
  set r := ρθ e with hr
  have hrG : r ∈ adjointGroup .E7 (GaloisField 3 1) :=
    LieType.Chevalley.rootSL2_mem_adjointGroup _ _
  have hrd : r * dθ = dθ * r := by
    rw [hdθ, hr, ← map_mul, ← map_mul, HSL_neg_one_mul]
  set c' := r * c * r⁻¹ with hc'
  have hc'G : c' ∈ adjointGroup .E7 (GaloisField 3 1) :=
    mul_mem (mul_mem hrG hcG) (inv_mem hrG)
  have hc'2 : c' * c' = 1 := by
    rw [hc']
    calc r * c * r⁻¹ * (r * c * r⁻¹) = r * (c * c) * r⁻¹ := by group
      _ = 1 := by rw [hc2]; group
  have hgG : r * u₂ ∈ adjointGroup .E7 (GaloisField 3 1) := mul_mem hrG hu₂
  have hgc : (r * u₂) * dθ * (r * u₂)⁻¹ = c' := by rw [hc', hc]; group
  obtain ⟨δ, hδ, hδθ, w₀, hw₀G, hw₀c, hw₀d⟩ :=
    exists_rational_conj_e7_adj hodd hc'G hgG hc'2 hcL hcU hgc
  set w := w₀ * r with hw
  have hwG : w ∈ adjointGroup .E7 (GaloisField 3 1) := mul_mem hw₀G hrG
  have hwd : w * dθ = dθ * w := by
    rw [hw]
    calc w₀ * r * dθ = w₀ * (r * dθ) := by group
      _ = w₀ * (dθ * r) := by rw [hrd]
      _ = (w₀ * dθ) * r := by group
      _ = (dθ * w₀) * r := by rw [hw₀d]
      _ = dθ * (w₀ * r) := by group
  have hwc : w * c * w⁻¹ = rootDiagUnit .E7 (thetaDiag δ (-1 : (GaloisField 3 1)ˣ)) := by
    rw [hw]
    calc w₀ * r * c * (w₀ * r)⁻¹ = w₀ * (r * c * r⁻¹) * w₀⁻¹ := by group
      _ = _ := hw₀c
  have hconj : (w * u₂) * rootTorusSL2 .E7 (GaloisField 3 1) thetaE7 (-1) * (w * u₂)⁻¹ =
      rootDiagUnit .E7 (thetaDiag δ (-1 : (GaloisField 3 1)ˣ)) := by
    rw [rootTorusSL2_thetaE7, ← hwc, hc]
    group
  obtain ⟨γ, hγ, hLγ, -, -⟩ := exists_rootRankOneGroup_of_conj_toral3
    (isLongRoot_of_isRoot_of_simplyLaced (Or.inr (Or.inl rfl)) isRoot_thetaE7)
    (mul_mem hwG hu₂) (fun i => thetaDiag_neg_one_sign_E7 δ i) hconj
  have hγroot : IsRoot .E7 γ := hγ.1
  have hnormw : (Lθ).map (MulAut.conj w).toMonoidHom = Lθ :=
    map_conj_rootRankOneGroup_of_commute hF hwG hwd
  have hcomp : (Lθ).map (MulAut.conj (w * u₂)).toMonoidHom =
      ((Lθ).map (MulAut.conj u₂).toMonoidHom).map (MulAut.conj w).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
  have hLγ' : ((Lθ).map (MulAut.conj u₂).toMonoidHom).map (MulAut.conj w).toMonoidHom =
      rootRankOneGroup .E7 (GaloisField 3 1) γ := by rw [← hcomp]; exact hLγ
  have hne' : rootRankOneGroup .E7 (GaloisField 3 1) γ ≠ Lθ := by
    intro h
    apply hne
    refine Subgroup.map_injective (f := (MulAut.conj w).toMonoidHom) (MulAut.conj w).injective ?_
    rw [hLγ', h, hnormw]
  have hnc' : ¬ ∀ x ∈ Lθ, ∀ y ∈ rootRankOneGroup .E7 (GaloisField 3 1) γ, x * y = y * x := by
    intro h
    apply hnc
    intro x hx y hy
    have hx' : w * x * w⁻¹ ∈ Lθ := by
      rw [← hnormw]
      exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
    have hy' : w * y * w⁻¹ ∈ rootRankOneGroup .E7 (GaloisField 3 1) γ := by
      rw [← hLγ']
      exact ⟨y, hy, by simp [MulAut.conj_apply]⟩
    have h1 := h _ hx' _ hy'
    have h2 : w * (x * y) * w⁻¹ = w * (y * x) * w⁻¹ := by
      calc w * (x * y) * w⁻¹ = (w * x * w⁻¹) * (w * y * w⁻¹) := by group
        _ = (w * y * w⁻¹) * (w * x * w⁻¹) := h1
        _ = w * (y * x) * w⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  have hodd' : ¬ Even (iform thetaE7 γ) := by
    intro hev
    rcases eq_or_iform_eq_zero_of_even_E7 hγroot hev with rfl | rfl | h0
    · exact hne' rfl
    · apply hne'
      rw [rootRankOneGroup_eq_sup hγroot, rootRankOneGroup_eq_sup isRoot_thetaE7, neg_neg,
        sup_comm]
    · exact hnc' ((isLongRoot_of_isRoot_of_simplyLaced (Or.inr (Or.inl rfl))
        isRoot_thetaE7).commute_rootRankOneGroup hγroot h0)
  have hpair : iform thetaE7 γ = 1 ∨ iform thetaE7 γ = -1 := by
    have hb := abs_iform_le_two_E7 isRoot_thetaE7 hγroot
    rw [abs_le] at hb
    have : Odd (iform thetaE7 γ) := Int.not_even_iff_odd.1 hodd'
    obtain ⟨m, hm⟩ := this
    omega
  exact ⟨γ, w, hγroot, hpair, hwG, hwd, hLγ⟩


end AdjFrame

section Pair

theorem e7_frame_core_3 (θW : SL(3, GaloisField 3 1) →* M₇)
    (hker : θW.ker ≤ Subgroup.center SL(3, GaloisField 3 1))
    {R₂ : Subgroup M₇} (hR₂ : R₂ ∈ Generic.fundamentalSubgroups .E7 D₇)
    (h1 : (B12 (GaloisField 3 1)).map θW = stdRankOne D₇ thetaE7)
    (h2 : (B23 (GaloisField 3 1)).map θW = R₂)
    (hne : stdRankOne D₇ thetaE7 ≠ R₂)
    (hnc : ¬ Commutes (stdRankOne D₇ thetaE7) R₂) :
    ∃ x : M₇, conjSub x (stdRankOne D₇ thetaE7) = stdRankOne D₇ thetaE7 ∧
      ∃ γ : Fin (Tag.rank .E7) → ℤ, IsRoot .E7 γ ∧
        (iform thetaE7 γ = 1 ∨ iform thetaE7 γ = -1) ∧
        conjSub x R₂ = stdRankOne D₇ γ := by
  have hF : ringChar (GaloisField 3 1) ≠ 2 := ringChar_galoisField_ne_two (by norm_num)
  have hodd : Odd (Nat.card (GaloisField 3 1)) := odd_gf3
  have hadm : StatedLieAdmissible .E7 0 3 1 :=
    ⟨Nat.prime_three, le_rfl, rfl⟩
  have hcard : Nat.card (GaloisField 3 1) = 3 ^ 1 := GaloisField.card 3 1 (by norm_num)
  have hsingle : Generic.FundamentalSingleClass .E7 D₇ :=
    fundamentalSingleClass .E7 0 3 1 Nat.prime_three trivial hadm (by decide) (by decide)
  have hlong := isLongestRoot_single .E7 0 3 1 Nat.prime_three trivial hadm
  have hθ : Generic.IsLongestRoot D₇ thetaE7 :=
    isLongestRoot_of_mem_roots_of_forall_single _ rfl (fun k => hlong k trivial)
      ((e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 (GaloisField 3 1)).2
        isRoot_thetaE7)
  have hRθF : stdRankOne D₇ thetaE7 ∈ Generic.fundamentalSubgroups .E7 D₇ :=
    ⟨1, thetaE7, Or.inl hθ, (conjSub_one _).symm⟩
  obtain ⟨g, hg⟩ := hsingle _ hRθF R₂ hR₂
  have h2ne : (2 : GaloisField 3 1) ≠ 0 := Ring.two_ne_zero hF
  obtain ⟨hι₁, hι₁r, hι₂, hι₂r⟩ := pair_block_inj hker h1 h2
  set ι₁ := θW.comp (blockSL (GaloisField 3 1) 3 2 0 (by omega)) with hι₁def
  set ι₂ := θW.comp (blockSL (GaloisField 3 1) 3 2 1 (by omega)) with hι₂def
  set r : M₇ := θW (blockSL (GaloisField 3 1) 3 2 1 (by omega) (-1)) with hr
  have hrR : r ∈ R₂ := by
    rw [← hι₂r]
    exact ⟨-1, rfl⟩
  have hr2 : r * r = 1 := by
    rw [hr, ← map_mul, ← map_mul, show ((-1 : SL(2, GaloisField 3 1)) * (-1)) = 1 by simp,
      map_one, map_one]
  have hrconj : ∀ A : SL2 (GaloisField 3 1), r * ι₁ A * r⁻¹ = ι₁ (diagConj2 (-1) 1 A) := fun A => by
    simp only [hι₁def, hr, MonoidHom.comp_apply]
    rw [← map_inv, ← map_mul, ← map_mul, E7Model.blockSL_neg_one_conj]
  have hrconj_u : ∀ t : GaloisField 3 1, r * ι₁ (uSL t) * r⁻¹ = ι₁ (uSL (-t)) := fun t => by
    rw [hrconj, diagConj2_uSL]
  have hnotcentral : ∀ t : GaloisField 3 1,
      ι₁ (uSL t) ∈ (εm (GaloisField 3 1)).ker → t = 0 := by
    intro t ht
    have hc := Subgroup.mem_center_iff.1 (εm_ker_le_center ht) r
    have h3 : ι₁ (uSL (-t)) = ι₁ (uSL t) := by
      rw [← hrconj_u t, mul_inv_eq_iff_eq_mul]
      exact hc
    have h4 := uSL_injective_of_field (hι₁ h3)
    have : (2 : GaloisField 3 1) * t = 0 := by linear_combination -h4
    exact (mul_eq_zero.1 this).resolve_left h2ne
  set Ψ : Multiplicative (GaloisField 3 1) →* ModGL .E7 (GaloisField 3 1) :=
    (εm (GaloisField 3 1)).comp (ι₁.comp CFSG.SL2MinimalFaithful.unipotentHom) with hΨ
  have hΨapply : ∀ t : GaloisField 3 1,
      Ψ (Multiplicative.ofAdd t) = εm (GaloisField 3 1) (ι₁ (uSL t)) := fun t => rfl
  have hΨinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have := hnotcentral x.toAdd (MonoidHom.mem_ker.2 hx)
    exact toAdd_eq_zero.1 this
  have hεR : (stdRankOne D₇ thetaE7).map (εm (GaloisField 3 1)) =
      rootRankOneGroup .E7 (GaloisField 3 1) thetaE7 := map_stdRankOne_εm isRoot_thetaE7
  have hιL : ∀ A : SL2 (GaloisField 3 1),
      εm (GaloisField 3 1) (ι₁ A) ∈ rootRankOneGroup .E7 (GaloisField 3 1) thetaE7 := fun A => by
    rw [← hεR]
    refine Subgroup.mem_map_of_mem _ ?_
    rw [← hι₁r]
    exact ⟨A, rfl⟩
  set U : Subgroup (SL2 (GaloisField 3 1)) :=
    Ψ.range.comap (rootSL2 .E7 (GaloisField 3 1) thetaE7) with hU
  have hρinj : Function.Injective (rootSL2 .E7 (GaloisField 3 1) thetaE7) :=
    ((exceptional_Lang_root_rank_one_data .E7 (GaloisField 3 1) thetaE7).2.2.2.2.2.2.2.1 hF).1
  have hΨle : Ψ.range ≤ (rootSL2 .E7 (GaloisField 3 1) thetaE7).range := by
    rintro _ ⟨x, rfl⟩
    exact hιL (uSL x.toAdd)
  have hUcard : Nat.card U = Nat.card (GaloisField 3 1) := by
    rw [← Subgroup.card_map_of_injective hρinj, hU, Subgroup.map_comap_eq_self hΨle]
    exact (Nat.card_congr (MonoidHom.ofInjective hΨinj).toEquiv).symm.trans
      (Nat.card_congr Multiplicative.toAdd)
  have hinv : ∀ A ∈ U, εm (GaloisField 3 1) r * rootSL2 .E7 (GaloisField 3 1) thetaE7 A *
      (εm (GaloisField 3 1) r)⁻¹ = (rootSL2 .E7 (GaloisField 3 1) thetaE7 A)⁻¹ := by
    intro A hA
    obtain ⟨x, hx⟩ := Subgroup.mem_comap.1 hA
    rw [← hx]
    have hx' : Ψ x = εm (GaloisField 3 1) (ι₁ (uSL x.toAdd)) := rfl
    have e1 : εm (GaloisField 3 1) r * εm (GaloisField 3 1) (ι₁ (uSL x.toAdd)) *
        (εm (GaloisField 3 1) r)⁻¹ = εm (GaloisField 3 1) (r * ι₁ (uSL x.toAdd) * r⁻¹) := by
      simp only [map_mul, map_inv]
    have e2 : (εm (GaloisField 3 1) (ι₁ (uSL x.toAdd)))⁻¹ =
        εm (GaloisField 3 1) (ι₁ (uSL (-x.toAdd))) := by
      rw [show uSL (-x.toAdd) = (uSL x.toAdd)⁻¹ from (uSL_inv_eq _).symm, map_inv, map_inv]
    rw [hx', e1, e2, hrconj_u]
  set c := εm (GaloisField 3 1) r with hc
  set u₂ := εm (GaloisField 3 1) g with hu₂
  have hu₂G : u₂ ∈ adjointGroup .E7 (GaloisField 3 1) := εm_mem g
  have hεR₂ : R₂.map (εm (GaloisField 3 1)) =
      (rootRankOneGroup .E7 (GaloisField 3 1) thetaE7).map (MulAut.conj u₂).toMonoidHom := by
    rw [hg, map_conjSub, hεR]
  have hc2 : c * c = 1 := by rw [hc, ← map_mul, hr2, map_one]
  have hcR₂ : c ∈ (rootRankOneGroup .E7 (GaloisField 3 1) thetaE7).map
      (MulAut.conj u₂).toMonoidHom := by
    rw [← hεR₂]
    exact Subgroup.mem_map_of_mem _ hrR
  have hc1 : c ≠ 1 := by
    intro h
    have hcen := Subgroup.mem_center_iff.1 (εm_ker_le_center (MonoidHom.mem_ker.2 h))
      (ι₁ (uSL 1))
    have h3 : ι₁ (uSL (-1)) = ι₁ (uSL 1) := by
      rw [← hrconj_u 1, mul_inv_eq_iff_eq_mul]
      exact hcen.symm
    have h4 := uSL_injective_of_field (hι₁ h3)
    exact h2ne (by linear_combination -h4)
  set dθ := rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField 3 1)ˣ)) with hdθdef
  have hdθ : dθ = rootSL2 .E7 (GaloisField 3 1) thetaE7 (HSL (-1)) :=
    (rootTorusSL2_thetaE7 (-1)).symm
  have hdθL : dθ ∈ rootRankOneGroup .E7 (GaloisField 3 1) thetaE7 := ⟨HSL (-1), hdθ.symm⟩
  have hd2 : dθ * dθ = 1 := by rw [hdθ, ← map_mul, HSL_neg_one_mul_self, map_one]
  have hdne : dθ ≠ 1 := by
    rw [hdθdef, ← rootTorusSL2_thetaE7]
    exact rootTorusSL2_neg_one_ne_one hF thetaE7
  have hcn : ∀ x ∈ rootRankOneGroup .E7 (GaloisField 3 1) thetaE7,
      c * x * c⁻¹ ∈ rootRankOneGroup .E7 (GaloisField 3 1) thetaE7 := by
    intro x hx
    rw [← hεR] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [← hι₁r] at hy
    obtain ⟨A, rfl⟩ := hy
    have : c * εm (GaloisField 3 1) (ι₁ A) * c⁻¹ =
        εm (GaloisField 3 1) (ι₁ (diagConj2 (-1) 1 A)) := by
      rw [← hrconj A]
      simp only [hc, map_mul, map_inv]
    rw [this]
    exact hιL _
  have hcdθ : c * dθ = dθ * c := by
    have hz : c * dθ * c⁻¹ ∈ rootRankOneGroup .E7 (GaloisField 3 1) thetaE7 := hcn dθ hdθL
    have hz2 : c * dθ * c⁻¹ * (c * dθ * c⁻¹) = 1 := by
      calc c * dθ * c⁻¹ * (c * dθ * c⁻¹) = c * (dθ * dθ) * c⁻¹ := by group
        _ = 1 := by rw [hd2]; group
    have hz1 : c * dθ * c⁻¹ ≠ 1 := fun h => hdne (by
      have := mul_inv_eq_one.1 h
      simpa using this)
    have := eq_rootTorusSL2_neg_one_of_mul_self_eq_one hF hodd hz hz2 hz1
    rw [rootTorusSL2_thetaE7] at this
    exact mul_inv_eq_iff_eq_mul.1 this
  have hcclass : c = u₂ * dθ * u₂⁻¹ := by
    obtain ⟨x, hx, hxe⟩ := hcR₂
    have hxe' : u₂ * x * u₂⁻¹ = c := hxe
    have hx2 : x * x = 1 := by
      have : u₂ * (x * x) * u₂⁻¹ = c * c := by rw [← hxe']; group
      rw [hc2] at this
      have h3 : x * x = u₂⁻¹ * 1 * u₂ := by
        calc x * x = u₂⁻¹ * (u₂ * (x * x) * u₂⁻¹) * u₂ := by group
          _ = u₂⁻¹ * 1 * u₂ := by rw [this]
      rw [h3]
      group
    have hx1 : x ≠ 1 := by
      rintro rfl
      apply hc1
      rw [← hxe']
      group
    have := eq_rootTorusSL2_neg_one_of_mul_self_eq_one hF hodd hx hx2 hx1
    rw [rootTorusSL2_thetaE7] at this
    rw [← hxe', this]
  have hne' : (rootRankOneGroup .E7 (GaloisField 3 1) thetaE7).map (MulAut.conj u₂).toMonoidHom ≠
      rootRankOneGroup .E7 (GaloisField 3 1) thetaE7 := by
    intro h
    apply hne
    apply eq_of_map_εm_eq3 hRθF hR₂
    rw [hεR, hεR₂, h]
  have hnc' : ¬ ∀ x ∈ rootRankOneGroup .E7 (GaloisField 3 1) thetaE7,
      ∀ y ∈ (rootRankOneGroup .E7 (GaloisField 3 1) thetaE7).map (MulAut.conj u₂).toMonoidHom,
        x * y = y * x := by
    intro h
    apply hnc
    refine commutes_of_map_commute_exponent3 (εm (GaloisField 3 1)) εm_ker_le_center cop_ker3
      (A := stdRankOne D₇ thetaE7) (L := R₂) (pow3_fund3 hR₂) (fun a ha l hl => ?_)
    have hεa : εm (GaloisField 3 1) a ∈ rootRankOneGroup .E7 (GaloisField 3 1) thetaE7 := by
      rw [← hεR]
      exact Subgroup.mem_map_of_mem _ ha
    have hεl : εm (GaloisField 3 1) l ∈ (rootRankOneGroup .E7 (GaloisField 3 1) thetaE7).map
        (MulAut.conj u₂).toMonoidHom := by
      rw [← hεR₂]
      exact Subgroup.mem_map_of_mem _ hl
    exact h _ hεa _ hεl
  have hcd' : (u₂ * dθ * u₂⁻¹) * dθ = dθ * (u₂ * dθ * u₂⁻¹) := by
    rw [← hcclass]
    exact hcdθ
  have hinv' : ∀ A ∈ U, (u₂ * dθ * u₂⁻¹) * rootSL2 .E7 (GaloisField 3 1) thetaE7 A *
      (u₂ * dθ * u₂⁻¹)⁻¹ = (rootSL2 .E7 (GaloisField 3 1) thetaE7 A)⁻¹ := by
    intro A hA
    rw [← hcclass]
    exact hinv A hA
  obtain ⟨γ, w, hγ, hpair, hwG, hwd, hL⟩ :=
    exists_frame_adj_e7_3 hu₂G hcd' hUcard hinv' hne' hnc'
  obtain ⟨x, hx⟩ := εm_surjective hwG
  have hγF : stdRankOne D₇ γ ∈ Generic.fundamentalSubgroups .E7 D₇ := by
    have hγlong : Generic.IsLongestRoot D₇ γ :=
      isLongestRoot_of_mem_roots_of_forall_single _ rfl (fun k => hlong k trivial)
        ((e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 (GaloisField 3 1)).2 hγ)
    exact ⟨1, γ, Or.inl hγlong, (conjSub_one _).symm⟩
  refine ⟨x, ?_, γ, hγ, hpair, ?_⟩
  · apply eq_of_map_εm_eq3 (conjSub_mem_fundamentalSubgroups hRθF x) hRθF
    rw [map_conjSub, hx, hεR, map_conj_rootRankOneGroup_of_commute hF hwG hwd]
  · apply eq_of_map_εm_eq3 (conjSub_mem_fundamentalSubgroups hR₂ x) hγF
    rw [map_conjSub, hx, hεR₂, Subgroup.map_map, map_stdRankOne_εm hγ]
    exact hL


theorem e7PairFrame_sc_3 :
    ∀ R₁ ∈ Generic.fundamentalSubgroups .E7 (e7Datum (GaloisField 3 1)),
      ∀ R₂ ∈ Generic.fundamentalSubgroups .E7 (e7Datum (GaloisField 3 1)),
      CFSG.ClassicalInvolution.RouteD.Gaps.ModelAdj (Subgroup.center (E7sc 3 1)) R₁ R₂ →
      (∃ W, LinearBlockStandardPair (GaloisField 3 1) W R₁ R₂) →
      ∀ a b : Fin 7, CFSG.Timmesfeld.edgeE 7 a b →
        ∃ g : E7sc 3 1, R₁ = conjSub g (rankOne (e7Datum (GaloisField 3 1)).rootGroup a) ∧
          R₂ = conjSub g (rankOne (e7Datum (GaloisField 3 1)).rootGroup b) := by
  intro R₁ hR₁ R₂ hR₂ hadj hlin a b hab
  obtain ⟨W, hW⟩ := hlin
  have hadm : StatedLieAdmissible .E7 0 3 1 :=
    ⟨Nat.prime_three, le_rfl, rfl⟩
  have hsingle : Generic.FundamentalSingleClass .E7 (e7Datum (GaloisField 3 1)) :=
    fundamentalSingleClass .E7 0 3 1 Nat.prime_three trivial hadm (by decide) (by decide)
  have hlong := isLongestRoot_single .E7 0 3 1 Nat.prime_three trivial hadm
  have hθ : Generic.IsLongestRoot (e7Datum (GaloisField 3 1)) thetaE7 :=
    isLongestRoot_of_mem_roots_of_forall_single _ rfl (fun k => hlong k trivial)
      ((e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 (GaloisField 3 1)).2
        isRoot_thetaE7)
  have hRθF : stdRankOne (e7Datum (GaloisField 3 1)) thetaE7 ∈
      Generic.fundamentalSubgroups .E7 (e7Datum (GaloisField 3 1)) :=
    ⟨1, thetaE7, Or.inl hθ, (conjSub_one _).symm⟩
  obtain ⟨g₁, hg₁⟩ := hsingle _ hRθF R₁ hR₁
  obtain ⟨g₂, hg₂⟩ := hsingle _ hRθF R₂ hR₂
  obtain ⟨θW, -, hker, hU, hV⟩ := pair_normalize hW
  set θ' := (MulAut.conj g₁⁻¹).toMonoidHom.comp θW with hθ'
  have hker' : θ'.ker ≤ Subgroup.center SL(3, GaloisField 3 1) := fun x hx =>
    hker (MonoidHom.mem_ker.2 ((MulEquiv.map_eq_one_iff (MulAut.conj g₁⁻¹)).1
      (MonoidHom.mem_ker.1 hx)))
  have hmapθ' : ∀ S : Subgroup SL(3, GaloisField 3 1),
      S.map θ' = conjSub g₁⁻¹ (S.map θW) := fun S => by
    unfold conjSub
    rw [hθ', Subgroup.map_map]
  have h1' : (B12 (GaloisField 3 1)).map θ' = stdRankOne (e7Datum (GaloisField 3 1)) thetaE7 := by
    rw [hmapθ', hU, hg₁, Generic.conjSub_inv_conjSub]
  have h2' : (B23 (GaloisField 3 1)).map θ' = conjSub g₁⁻¹ R₂ := by
    rw [hmapθ', hV]
  have hR₂'F : conjSub g₁⁻¹ R₂ ∈ Generic.fundamentalSubgroups .E7 (e7Datum (GaloisField 3 1)) :=
    ⟨g₁⁻¹ * g₂, thetaE7, Or.inl hθ, by
      show conjSub g₁⁻¹ R₂ = conjSub (g₁⁻¹ * g₂) (stdRankOne (e7Datum (GaloisField 3 1)) thetaE7)
      rw [hg₂, conjSub_mul]⟩
  have hne' : stdRankOne (e7Datum (GaloisField 3 1)) thetaE7 ≠ conjSub g₁⁻¹ R₂ := by
    intro h
    apply hadj.1
    rw [hg₁, h, Generic.conjSub_conjSub_inv]
  have hnc' : ¬ Commutes (stdRankOne (e7Datum (GaloisField 3 1)) thetaE7) (conjSub g₁⁻¹ R₂) := by
    intro h
    apply hadj.2.1
    intro x hx y hy
    have hx' : g₁⁻¹ * x * g₁ ∈ stdRankOne (e7Datum (GaloisField 3 1)) thetaE7 := by
      rw [hg₁, mem_conjSub_iff] at hx
      exact hx
    have hy' : g₁⁻¹ * y * g₁ ∈ conjSub g₁⁻¹ R₂ := by
      rw [mem_conjSub_iff, inv_inv]
      have : g₁ * (g₁⁻¹ * y * g₁) * g₁⁻¹ = y := by group
      rw [this]
      exact hy
    have := h _ hx' _ hy'
    calc x * y = g₁ * (g₁⁻¹ * x * g₁ * (g₁⁻¹ * y * g₁)) * g₁⁻¹ := by group
      _ = g₁ * (g₁⁻¹ * y * g₁ * (g₁⁻¹ * x * g₁)) * g₁⁻¹ := by rw [this]
      _ = y * x := by group
  obtain ⟨x, hx1, γ, hγ, hpair, hx2⟩ :=
    e7_frame_core_3 θ' hker' hR₂'F h1' h2' hne' hnc'
  obtain ⟨k, hk1, hk2⟩ := exists_conj_phase_one (GaloisField 3 1) hγ hpair
  obtain ⟨m, hm1, hm2⟩ := exists_conj_edge (GaloisField 3 1) hab
  rw [e7Idx_fin] at hm1 hm2
  have hR₁' : conjSub (k * x * g₁⁻¹) R₁ = stdRankOne (e7Datum (GaloisField 3 1)) thetaE7 := by
    rw [conjSub_mul, conjSub_mul, hg₁, Generic.conjSub_inv_conjSub, hx1, hk1]
  have hR₂' : conjSub (k * x * g₁⁻¹) R₂ =
      rankOne (e7Datum (GaloisField 3 1)).rootGroup (e7Idx 0) := by
    rw [conjSub_mul, conjSub_mul, hx2, hk2]
  refine ⟨(k * x * g₁⁻¹)⁻¹ * m, ?_, ?_⟩
  · rw [conjSub_mul, hm1, ← hR₁', Generic.conjSub_inv_conjSub]
  · rw [conjSub_mul, hm2, ← hR₂', Generic.conjSub_inv_conjSub]


theorem e7PairFrame3 : TypeE8.E7PairFrame 3 1 := e7PairFrame_sc_3

end Pair

end CFSG.ClassicalInvolution.Q3.Q3W
