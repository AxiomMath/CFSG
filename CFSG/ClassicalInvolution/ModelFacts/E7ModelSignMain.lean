module

public import CFSG.ClassicalInvolution.ModelFacts.E7ModelSignK
public import CFSG.ClassicalInvolution.RouteD.LocalTwinPartner
public import CFSG.ClassicalInvolution.RouteD.TypeE8Model
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate123
public import Certificates.Certificate3951
public import Certificates.Certificate3952

public section

namespace CFSG.ClassicalInvolution.ModelFacts.E7Model

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.ModelFacts.Levi CFSG.ClassicalInvolution.ModelFacts
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.RouteD CFSG.Timmesfeld

theorem eq_or_neg_of_iform_eq_two {α β : Fin (Tag.rank .E7) → ℤ} (hα : IsRoot .E7 α)
    (hβ : IsRoot .E7 β) (h : iform α β = 2 ∨ iform α β = -2) : β = α ∨ β = -α := by
  have hαα := iform_self_isRoot_E7 hα
  have hββ := iform_self_isRoot_E7 hβ
  rcases h with h | h
  · left
    by_contra hne
    have hpos := iform_self_pos (sub_ne_zero.2 hne)
    rw [iform_sub_left, iform_sub_right, iform_sub_right, hαα, hββ, iform_comm β α, h] at hpos
    omega
  · right
    by_contra hne
    have hne' : β + α ≠ 0 := fun h0 => hne (eq_neg_of_add_eq_zero_left h0)
    have hpos := iform_self_pos hne'
    rw [iform_add_left, iform_add_right, iform_add_right, hαα, hββ, iform_comm β α, h] at hpos
    omega

theorem linearBlockStandardPair_symm' {F : Type} [Field F] {X : Type} [Group X]
    {W U V : Subgroup X} (h : LinearBlockStandardPair F W U V) :
    LinearBlockStandardPair F W V U := by
  obtain ⟨θ, c, h1, h2, h3⟩ := h
  exact ⟨θ, c, h1, h2, h3.symm⟩


section Main

variable {p f : ℕ} [Fact p.Prime]

local notation "M₇" => E7sc p f
local notation "D₇" => e7Datum (GaloisField p f)

theorem commutes_std_of_iform_eq_zero (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {α β : Fin (Tag.rank .E7) → ℤ} (hα : IsRoot .E7 α) (hβ : IsRoot .E7 β)
    (h : iform α β = 0) : Commutes (stdRankOne D₇ α) (stdRankOne D₇ β) := by
  obtain ⟨-, -, hperf⟩ := e7_fund_class hp2 hq
  have hαF := std_mem_fund hq hα
  intro x hx y hy
  have hc : ∀ a ∈ rootRankOneGroup .E7 (GaloisField p f) α,
      ∀ b ∈ rootRankOneGroup .E7 (GaloisField p f) β, a * b = b * a :=
    (isLongRoot_of_isRoot_of_simplyLaced (Or.inr (Or.inl rfl)) hα).commute_rootRankOneGroup hβ h
  have hεy : εm (GaloisField p f) y ∈ rootRankOneGroup .E7 (GaloisField p f) β := by
    rw [← map_stdRankOne_εm hβ]
    exact Subgroup.mem_map_of_mem _ hy
  have hu : ∀ z ∈ stdRankOne D₇ α, y * z * y⁻¹ * z⁻¹ ∈ Subgroup.center M₇ := by
    intro z hz
    apply εm_ker_le_center
    rw [MonoidHom.mem_ker]
    have hεz : εm (GaloisField p f) z ∈ rootRankOneGroup .E7 (GaloisField p f) α := by
      rw [← map_stdRankOne_εm hα]
      exact Subgroup.mem_map_of_mem _ hz
    have h3 := hc _ hεz _ hεy
    simp only [map_mul, map_inv]
    calc εm (GaloisField p f) y * εm (GaloisField p f) z * (εm (GaloisField p f) y)⁻¹ *
        (εm (GaloisField p f) z)⁻¹ =
        εm (GaloisField p f) y * εm (GaloisField p f) z * ((εm (GaloisField p f) z) *
          εm (GaloisField p f) y)⁻¹ := by group
      _ = 1 := by rw [h3]; group
  exact (commute_of_commutator_central (stdRankOne D₇ α) (hperf _ hαF).ge y hu x hx).symm


theorem e7Sign_sc (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) :
    ∀ R₁ ∈ fundamentalSubgroups .E7 D₇, ∀ R₂ ∈ fundamentalSubgroups .E7 D₇,
      ∀ R₃ ∈ fundamentalSubgroups .E7 D₇,
      Gaps.ModelAdj (Subgroup.center M₇) R₁ R₂ → Gaps.ModelAdj (Subgroup.center M₇) R₃ R₂ →
      Commutes R₁ R₃ → (∃ W, LinearBlockStandardPair (GaloisField p f) W R₁ R₂) →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W R₂ R₃ := by
  intro R₁ hR₁ R₂ hR₂ R₃ hR₃ hadj12 hadj32 hc13 hlin12
  have he0 : IsRoot .E7 (Pi.single (e7Idx 0) 1 : V7) := isRoot_single .E7 (e7Idx 0)
  have he2 : IsRoot .E7 (Pi.single (e7Idx 2) 1 : V7) := isRoot_single .E7 (e7Idx 2)
  obtain ⟨g, hg1, hg2⟩ := e7PairFrame_sc hp2 hq R₁ hR₁ R₂ hR₂ hadj12 hlin12 0 2 (by decide)
  have hpair : iform (Pi.single (e7Idx 2) 1 : V7) (Pi.single (e7Idx 0) 1) = 1 ∨
      iform (Pi.single (e7Idx 2) 1 : V7) (Pi.single (e7Idx 0) 1) = -1 := by decide +kernel
  obtain ⟨k, hk2, hk0⟩ := exists_conj_theta_e0 (GaloisField p f) he2 he0 hpair
  rw [e7Idx_zero] at hk0
  set x₀ : M₇ := k * g⁻¹ with hx₀
  have hx₀2 : conjSub x₀ R₂ = stdRankOne D₇ thetaE7 := by
    rw [hx₀, conjSub_mul, hg2, conjSub_inv_conjSub]
    exact hk2
  have hx₀1 : conjSub x₀ R₁ = stdRankOne D₇ (Pi.single (e7Idx 0) 1) := by
    rw [hx₀, conjSub_mul, hg1, conjSub_inv_conjSub]
    exact hk0
  obtain ⟨hne32, hnc32, r₃, r₂', hr₃, hr₂', -, hnorm⟩ := hadj32
  set X := conjSub x₀ R₃ with hXdef
  have hXF : X ∈ fundamentalSubgroups .E7 D₇ := conjSub_mem_fundamentalSubgroups hR₃ x₀
  have hr₃' : x₀ * r₃ * x₀⁻¹ ∈ X := conj_mem_conjSub hr₃.1
  have hr₃2 : orderOf (x₀ * r₃ * x₀⁻¹) = 2 := by
    rw [← hr₃.2]
    exact orderOf_injective (MulAut.conj x₀).toMonoidHom (MulAut.conj x₀).injective r₃
  have hr₂'' : x₀ * r₂' * x₀⁻¹ ∈ stdRankOne D₇ thetaE7 := by
    rw [← hx₀2]
    exact conj_mem_conjSub hr₂'.1
  have hr₂2 : orderOf (x₀ * r₂' * x₀⁻¹) = 2 := by
    rw [← hr₂'.2]
    exact orderOf_injective (MulAut.conj x₀).toMonoidHom (MulAut.conj x₀).injective r₂'
  have hnorm' : ∀ x ∈ X, (x₀ * r₂' * x₀⁻¹) * x * (x₀ * r₂' * x₀⁻¹)⁻¹ ∈ X := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
    have : x₀ * (r₂' * a * r₂'⁻¹) * x₀⁻¹ ∈ conjSub x₀ R₃ := conj_mem_conjSub (hnorm a ha)
    convert this using 1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hcomm' : Commutes (stdRankOne D₇ (Pi.single (e7Idx 0) 1)) X := by
    have := hc13.conjSub x₀
    rwa [hx₀1] at this
  obtain ⟨x, hxL, hxE, γ, hγ, hxX⟩ := sign_step hp2 hq hXF hr₃' hr₃2 hr₂'' hr₂2 hnorm' hcomm'
  have hθ : IsRoot .E7 thetaE7 := isRoot_thetaE7
  have hback : ∀ A B : Subgroup M₇, conjSub x A = conjSub x B → A = B := fun A B h => by
    have := congrArg (conjSub x⁻¹) h
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this
  have hback' : ∀ A B : Subgroup M₇, conjSub x₀ A = conjSub x₀ B → A = B := fun A B h => by
    have := congrArg (conjSub x₀⁻¹) h
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this
  have hcomm_back : ∀ (A B : Subgroup M₇) (g : M₇), Commutes (conjSub g A) (conjSub g B) →
      Commutes A B := fun A B g h => by
    have := h.conjSub g⁻¹
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this
  by_cases hγe : γ = Pi.single (e7Idx 0) 1 ∨ γ = -Pi.single (e7Idx 0) 1
  · have hY : conjSub x X = conjSub x (stdRankOne D₇ (Pi.single (e7Idx 0) 1)) := by
      rw [hxX, hxE]
      rcases hγe with h | h
      · rw [h]
      · rw [h, stdRankOne_neg]
    have hX1 : X = stdRankOne D₇ (Pi.single (e7Idx 0) 1) := hback _ _ hY
    have hR31 : R₃ = R₁ := hback' _ _ (hX1.trans hx₀1.symm)
    rw [hR31]
    obtain ⟨W, hW⟩ := hlin12
    exact ⟨W, linearBlockStandardPair_symm' hW⟩
  have hY_ne : stdRankOne D₇ γ ≠ stdRankOne D₇ thetaE7 := by
    intro h
    apply hne32
    have h1 : conjSub x X = conjSub x (stdRankOne D₇ thetaE7) := by rw [hxX, h, hxL]
    have h2 : X = conjSub x₀ R₂ := (hback _ _ h1).trans hx₀2.symm
    exact hback' _ _ h2
  have hLinv : conjSub x⁻¹ (stdRankOne D₇ thetaE7) = stdRankOne D₇ thetaE7 := by
    have := congrArg (conjSub x⁻¹) hxL
    rw [conjSub_inv_conjSub] at this
    exact this.symm
  have hY_nc : ¬ Commutes (stdRankOne D₇ γ) (stdRankOne D₇ thetaE7) := by
    intro h
    apply hnc32
    have h2 := h.conjSub x⁻¹
    rw [← hxX, conjSub_inv_conjSub, hLinv, ← hx₀2] at h2
    exact hcomm_back R₃ R₂ x₀ h2
  have hY_c0 : Commutes (stdRankOne D₇ (Pi.single (e7Idx 0) 1)) (stdRankOne D₇ γ) := by
    have := hcomm'.conjSub x
    rwa [hxE, hxX] at this
  have h0γ : iform (Pi.single (e7Idx 0) 1 : V7) γ = 0 := by
    by_contra hne
    have hb := abs_iform_le_two_E7 he0 hγ
    rw [abs_le] at hb
    have hcases : iform (Pi.single (e7Idx 0) 1 : V7) γ = -2 ∨
        iform (Pi.single (e7Idx 0) 1 : V7) γ = -1 ∨
        iform (Pi.single (e7Idx 0) 1 : V7) γ = 1 ∨ iform (Pi.single (e7Idx 0) 1 : V7) γ = 2 := by
      omega
    rcases hcases with h | h | h | h
    · exact hγe (eq_or_neg_of_iform_eq_two he0 hγ (Or.inr h))
    · obtain ⟨W, hW⟩ := linearPair_of_roots (GaloisField p f) he0 hγ (Or.inr h)
      exact not_commutes_of_linearBlockStandardPair hW hY_c0
    · obtain ⟨W, hW⟩ := linearPair_of_roots (GaloisField p f) he0 hγ (Or.inl h)
      exact not_commutes_of_linearBlockStandardPair hW hY_c0
    · exact hγe (eq_or_neg_of_iform_eq_two he0 hγ (Or.inl h))
  have hθγ : iform thetaE7 γ = 1 ∨ iform thetaE7 γ = -1 := by
    have hb := abs_iform_le_two_E7 hθ hγ
    rw [abs_le] at hb
    by_contra hne
    have hcases : iform thetaE7 γ = -2 ∨ iform thetaE7 γ = 0 ∨ iform thetaE7 γ = 2 := by omega
    have hneg : γ = thetaE7 ∨ γ = -thetaE7 → False := fun h' => hY_ne (by
      rcases h' with h' | h'
      · rw [h']
      · rw [h', stdRankOne_neg])
    rcases hcases with h | h | h
    · exact hneg (eq_or_neg_of_iform_eq_two hθ hγ (Or.inr h))
    · exact hY_nc (commutes_std_of_iform_eq_zero hp2 hq hγ hθ (by rw [iform_comm]; exact h))
    · exact hneg (eq_or_neg_of_iform_eq_two hθ hγ (Or.inl h))
  obtain ⟨W, hW⟩ := linearPair_of_roots (GaloisField p f) hθ hγ hθγ
  have e2 : conjSub (x * x₀) R₂ = stdRankOne D₇ thetaE7 := by rw [conjSub_mul, hx₀2, hxL]
  have e3 : conjSub (x * x₀) R₃ = stdRankOne D₇ γ := by rw [conjSub_mul, ← hXdef, hxX]
  have h4 := linearBlockStandardPair_map_conj hW (x * x₀)⁻¹
  change LinearBlockStandardPair (GaloisField p f) _ (conjSub _ _) (conjSub _ _) at h4
  rw [← e2, ← e3, conjSub_inv_conjSub, conjSub_inv_conjSub] at h4
  exact ⟨_, h4⟩

end Main

theorem e7Sign {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) :
    RouteD.TypeE8.E7Sign p f := e7Sign_sc hp2 hq

end CFSG.ClassicalInvolution.ModelFacts.E7Model
