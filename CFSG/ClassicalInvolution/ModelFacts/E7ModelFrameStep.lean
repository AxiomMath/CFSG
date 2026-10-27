module

public import CFSG.ClassicalInvolution.ModelFacts.E7ModelFrameData
public import CFSG.ClassicalInvolution.ModelFacts.E7ModelSignMain
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

@[expose] def InvComm {G : Type*} [Group G] (A B : Subgroup G) : Prop :=
  ∀ s ∈ A, orderOf s = 2 → ∀ t ∈ B, orderOf t = 2 → s * t = t * s

section InvComm

variable {G : Type*} [Group G] {A B : Subgroup G}

theorem InvComm.conjSub (h : InvComm A B) (g : G) : InvComm (conjSub g A) (conjSub g B) := by
  intro s hs hs2 t ht ht2
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hs
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 ht
  have ha2 : orderOf a = 2 := by
    rw [← hs2]
    exact (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective a).symm
  have hb2 : orderOf b = 2 := by
    rw [← ht2]
    exact (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective b).symm
  have := h a ha ha2 b hb hb2
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
    _ = g * (b * a) * g⁻¹ := by rw [this]
    _ = g * b * g⁻¹ * (g * a * g⁻¹) := by group

theorem invComm_of_commutes (h : Commutes A B) : InvComm A B :=
  fun s hs _ t ht _ => h s hs t ht

end InvComm

section Involutions

variable {p f : ℕ} [Fact p.Prime]

local notation "M₇" => E7sc p f
local notation "D₇" => e7Datum (GaloisField p f)

theorem exists_involution_std (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {γ : V7} (hγ : IsRoot .E7 γ) :
    ∃ r ∈ stdRankOne D₇ γ, orderOf r = 2 := by
  have hF : ringChar (GaloisField p f) ≠ 2 := ringChar_galoisField_ne_two hp2
  have hγF := std_mem_fund hq hγ
  have hmem : rootTorusSL2 .E7 (GaloisField p f) γ (-1) ∈
      (stdRankOne D₇ γ).map (εm (GaloisField p f)) := by
    rw [map_stdRankOne_εm hγ]
    exact ⟨HSL (-1), rfl⟩
  obtain ⟨r, hr, hεr⟩ := Subgroup.mem_map.1 hmem
  have hr2 : r * r = 1 := by
    have hker : r * r ∈ (εm (GaloisField p f)).ker := by
      rw [MonoidHom.mem_ker, map_mul, hεr, rootTorusSL2_neg_one_mul_self]
    exact no_central_fund hp2 hq hγF (mul_mem hr hr) (εm_ker_le_center hker)
  have hr1 : r ≠ 1 := by
    rintro rfl
    exact rootTorusSL2_neg_one_ne_one hF γ (by rw [← hεr, map_one])
  exact ⟨r, hr, orderOf_eq_prime (by rwa [pow_two]) hr1⟩

theorem εm_involution_std (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {γ : V7} (hγ : IsRoot .E7 γ)
    {r : M₇} (hr : r ∈ stdRankOne D₇ γ) (h2 : orderOf r = 2) :
    εm (GaloisField p f) r = rootDiagUnit .E7 (thetaDiag γ (-1 : (GaloisField p f)ˣ)) := by
  have hF : ringChar (GaloisField p f) ≠ 2 := ringChar_galoisField_ne_two hp2
  obtain ⟨hodd, h5⟩ := odd_and_five_le_card_galoisField hp2 hq
  have hγF := std_mem_fund hq hγ
  have hεr : εm (GaloisField p f) r ∈ rootRankOneGroup .E7 (GaloisField p f) γ := by
    rw [← map_stdRankOne_εm hγ]
    exact Subgroup.mem_map_of_mem _ hr
  have hss : r * r = 1 := by rw [← sq]; exact h2 ▸ pow_orderOf_eq_one r
  have hz2 : εm (GaloisField p f) r * εm (GaloisField p f) r = 1 := by
    rw [← map_mul, hss, map_one]
  have hz1 : εm (GaloisField p f) r ≠ 1 := by
    intro h1
    have := no_central_fund hp2 hq hγF hr (εm_ker_le_center (MonoidHom.mem_ker.2 h1))
    rw [this, orderOf_one] at h2
    omega
  rw [eq_rootTorusSL2_neg_one_of_mul_self_eq_one hF hodd hεr hz2 hz1,
    rootTorusSL2_eq_thetaDiag hγ]

theorem exists_involution_fund (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {X : Subgroup M₇}
    (hX : X ∈ fundamentalSubgroups .E7 D₇) : ∃ r ∈ X, orderOf r = 2 := by
  obtain ⟨hsingle, hRθF, -⟩ := e7_fund_class hp2 hq
  obtain ⟨g, hg⟩ := hsingle _ hRθF X hX
  obtain ⟨r, hr, hr2⟩ := exists_involution_std hp2 hq isRoot_thetaE7
  refine ⟨g * r * g⁻¹, ?_, ?_⟩
  · rw [hg]
    exact conj_mem_conjSub hr
  · rw [← hr2]
    exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective r

theorem invComm_of_modelAdj (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {A B : Subgroup M₇}
    (hA : A ∈ fundamentalSubgroups .E7 D₇) (hB : B ∈ fundamentalSubgroups .E7 D₇)
    (h : Gaps.ModelAdj (Subgroup.center M₇) A B) : InvComm A B := by
  obtain ⟨-, -, r₁, r₂, -, hr₂, -, hnorm⟩ := h
  intro s hs hs2 t ht ht2
  have htr : t = r₂ := eq_of_orderOf_two_fund hp2 hq hB ht hr₂.1 ht2 hr₂.2
  have hmem : r₂ * s * r₂⁻¹ ∈ A := hnorm s hs
  have hord : orderOf (r₂ * s * r₂⁻¹) = 2 := by
    rw [← hs2]
    exact orderOf_injective (MulAut.conj r₂).toMonoidHom (MulAut.conj r₂).injective s
  have := eq_of_orderOf_two_fund hp2 hq hA hmem hs hord hs2
  rw [htr]
  calc s * r₂ = (r₂ * s * r₂⁻¹) * r₂ := by rw [this]
    _ = r₂ * s := by group

end Involutions

section Levi

variable {p f : ℕ} [Fact p.Prime]

theorem levi_prefix (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {y : ModGL .E7 (GaloisField p f)}
    (hyG : y ∈ adjointGroup .E7 (GaloisField p f))
    (hyd : y * rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField p f)ˣ)) =
      rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField p f)ˣ)) * y)
    (hye : ∀ A : SL2 (GaloisField p f),
      y * rootSL2 .E7 (GaloisField p f) (Pi.single (e7Idx 0) 1) A =
        rootSL2 .E7 (GaloisField p f) (Pi.single (e7Idx 0) 1) A * y) :
    baseChangeGL (algebraMap (GaloisField p f) (AlgebraicClosure (GaloisField p f))) y ∈
      parabolicLevi .E7 (AlgebraicClosure (GaloisField p f)) Jsign := by
  have : NeZero f := ⟨by rintro rfl; simp at hq⟩
  have hF : ringChar (GaloisField p f) ≠ 2 := ringChar_galoisField_ne_two hp2
  have he0 : IsRoot .E7 (Pi.single (e7Idx 0) 1 : V7) := isRoot_single .E7 (e7Idx 0)
  obtain ⟨a, ha⟩ := exists_unit_sq_ne_one (p := p) (f := f) hq
  have hchar : rootChar (thetaDiag (Pi.single (e7Idx 0) 1 : V7) a) thetaE7 = a := by
    rw [rootChar_thetaDiag, iform_comm, iform_thetaE7_single]
    simp [e7Idx]
  have hyb : y * rootDiagUnit .E7 (thetaDiag (Pi.single (e7Idx 0) 1 : V7) a) =
      rootDiagUnit .E7 (thetaDiag (Pi.single (e7Idx 0) 1 : V7) a) * y := by
    rw [← rootTorusSL2_eq_thetaDiag_gen he0]
    exact hye (HSL a)
  have hyJ : y ∈ parabolicLevi .E7 (GaloisField p f) JE7 :=
    mem_parabolicLevi_of_commute_diag hF hyG hyd (by rw [hchar]; exact ha) hyb
  set k := AlgebraicClosure (GaloisField p f) with hkdef
  set ι := algebraMap (GaloisField p f) k with hι
  have hpk : CharP k p := charP_of_injective_algebraMap ι.injective p
  have hkF : ringChar k ≠ 2 := by rw [ringChar.eq k p]; exact hp2
  have hk2 : (-1 : kˣ) ≠ 1 := fun h =>
    Ring.neg_one_ne_one_of_char_ne_two hkF (by simpa using congrArg Units.val h)
  have hyL : baseChangeGL ι y ∈ parabolicLevi .E7 k JE7 := baseChangeGL_mem_parabolicLevi ι hyJ
  have hyG' : baseChangeGL ι y ∈ adjointGroup .E7 k := baseChangeGL_mem_adjointGroup ι hyG
  have hyde : y * rootDiagUnit .E7
      (thetaDiag (Pi.single (e7Idx 0) 1 : V7) (-1 : (GaloisField p f)ˣ)) =
      rootDiagUnit .E7 (thetaDiag (Pi.single (e7Idx 0) 1 : V7) (-1 : (GaloisField p f)ˣ)) * y := by
    rw [← rootTorusSL2_eq_thetaDiag_gen he0]
    exact hye (HSL (-1))
  have hyde' : baseChangeGL ι y * rootDiagUnit .E7
      (thetaDiag (Pi.single (e7Idx 0) 1 : V7) (-1 : kˣ)) = rootDiagUnit .E7
      (thetaDiag (Pi.single (e7Idx 0) 1 : V7) (-1 : kˣ)) * baseChangeGL ι y := by
    rw [← baseChangeGL_rootDiagUnit_thetaDiag_E7 ι, ← map_mul, ← map_mul, hyde]
  exact mem_levi_of_commute_signdiag hk2 (fun j hj => iform_thetaE7_single_of_mem hj)
    (fun σ hσ => abs_iform_thetaE7_le σ hσ) he0 sign_cut hyG' hyL hyde'

theorem levi_cut (hp2 : p ≠ 2) {J J' : Set (Fin (Tag.rank .E7))} {l : V7} {B : ℕ}
    (hlJ : ∀ j ∈ J, iform l (Pi.single j 1) = 0) (hB : ∀ σ ∈ rootFinset .E7, |iform l σ| ≤ B)
    {z : V7} (hz : IsRoot .E7 z)
    (hker : ∀ σ ∈ rootFinset .E7, iform l σ = 0 → Even (iform z σ) →
      σ ∈ parabolicRoots .E7 J')
    {y : ModGL .E7 (GaloisField p f)} (hyG : y ∈ adjointGroup .E7 (GaloisField p f))
    (hyJ : baseChangeGL (algebraMap (GaloisField p f) (AlgebraicClosure (GaloisField p f))) y ∈
      parabolicLevi .E7 (AlgebraicClosure (GaloisField p f)) J)
    (hyd : y * rootDiagUnit .E7 (thetaDiag z (-1 : (GaloisField p f)ˣ)) =
      rootDiagUnit .E7 (thetaDiag z (-1 : (GaloisField p f)ˣ)) * y) :
    baseChangeGL (algebraMap (GaloisField p f) (AlgebraicClosure (GaloisField p f))) y ∈
      parabolicLevi .E7 (AlgebraicClosure (GaloisField p f)) J' := by
  set k := AlgebraicClosure (GaloisField p f) with hkdef
  set ι := algebraMap (GaloisField p f) k with hι
  have hpk : CharP k p := charP_of_injective_algebraMap ι.injective p
  have hkF : ringChar k ≠ 2 := by rw [ringChar.eq k p]; exact hp2
  have hk2 : (-1 : kˣ) ≠ 1 := fun h =>
    Ring.neg_one_ne_one_of_char_ne_two hkF (by simpa using congrArg Units.val h)
  have hyG' : baseChangeGL ι y ∈ adjointGroup .E7 k := baseChangeGL_mem_adjointGroup ι hyG
  have hyd' : baseChangeGL ι y * rootDiagUnit .E7 (thetaDiag z (-1 : kˣ)) =
      rootDiagUnit .E7 (thetaDiag z (-1 : kˣ)) * baseChangeGL ι y := by
    rw [← baseChangeGL_rootDiagUnit_thetaDiag_E7 ι, ← map_mul, ← map_mul, hyd]
  exact mem_levi_of_commute_signdiag hk2 hlJ hB hz hker hyG' hyJ hyd'

end Levi

section Rel

variable {p f : ℕ} [Fact p.Prime]

local notation "M₇" => E7sc p f
local notation "D₇" => e7Datum (GaloisField p f)

theorem not_commutes_self_std (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {γ : V7} (hγ : IsRoot .E7 γ) :
    ¬ Commutes (stdRankOne D₇ γ) (stdRankOne D₇ γ) := by
  intro h
  obtain ⟨-, -, hperf⟩ := e7_fund_class hp2 hq
  have hγF := std_mem_fund hq hγ
  obtain ⟨r, hr, hr2⟩ := exists_involution_std hp2 hq hγ
  have hbot : ⁅stdRankOne D₇ γ, stdRankOne D₇ γ⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact h y hy x hx
  have hr' : r ∈ ⁅stdRankOne D₇ γ, stdRankOne D₇ γ⁆ := by
    rw [hperf _ hγF]
    exact hr
  rw [hbot, Subgroup.mem_bot] at hr'
  rw [hr', orderOf_one] at hr2
  omega

theorem iform_eq_zero_of_commutes (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {a b : V7} (ha : IsRoot .E7 a)
    (hb : IsRoot .E7 b) (h : Commutes (stdRankOne D₇ a) (stdRankOne D₇ b)) : iform a b = 0 := by
  have hbd := abs_iform_le_two_E7 ha hb
  rw [abs_le] at hbd
  by_contra hne
  have hcases : iform a b = -2 ∨ iform a b = -1 ∨ iform a b = 1 ∨ iform a b = 2 := by omega
  have hsq : iform a b = 2 ∨ iform a b = -2 → False := fun h2 => by
    rcases eq_or_neg_of_iform_eq_two ha hb h2 with rfl | rfl
    · exact not_commutes_self_std hp2 hq ha h
    · rw [stdRankOne_neg] at h
      exact not_commutes_self_std hp2 hq ha h
  rcases hcases with h' | h' | h' | h'
  · exact hsq (Or.inr h')
  · obtain ⟨W, hW⟩ := linearPair_of_roots (GaloisField p f) ha hb (Or.inr h')
    exact not_commutes_of_linearBlockStandardPair hW h
  · obtain ⟨W, hW⟩ := linearPair_of_roots (GaloisField p f) ha hb (Or.inl h')
    exact not_commutes_of_linearBlockStandardPair hW h
  · exact hsq (Or.inl h')

theorem iform_odd_of_rel (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {a b : V7} (ha : IsRoot .E7 a)
    (hb : IsRoot .E7 b) (hne : stdRankOne D₇ a ≠ stdRankOne D₇ b)
    (hnc : ¬ Commutes (stdRankOne D₇ a) (stdRankOne D₇ b)) :
    iform a b = 1 ∨ iform a b = -1 := by
  have hbd := abs_iform_le_two_E7 ha hb
  rw [abs_le] at hbd
  by_contra hne'
  have hcases : iform a b = -2 ∨ iform a b = 0 ∨ iform a b = 2 := by omega
  have hsq : iform a b = 2 ∨ iform a b = -2 → False := fun h2 => by
    rcases eq_or_neg_of_iform_eq_two ha hb h2 with rfl | rfl
    · exact hne rfl
    · exact hne (by rw [stdRankOne_neg])
  rcases hcases with h' | h' | h'
  · exact hsq (Or.inr h')
  · exact hnc (commutes_std_of_iform_eq_zero hp2 hq ha hb h')
  · exact hsq (Or.inl h')

end Rel

section Step

variable {p f : ℕ} [Fact p.Prime]

local notation "M₇" => E7sc p f
local notation "D₇" => e7Datum (GaloisField p f)

theorem stage_step (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {X : Subgroup M₇}
    (hX : X ∈ fundamentalSubgroups .E7 D₇)
    (hθX : InvComm (stdRankOne D₇ thetaE7) X)
    (hcomm : Commutes (stdRankOne D₇ (Pi.single (e7Idx 0) 1)) X)
    {J : Set (Fin (Tag.rank .E7))} (hJ : J ⊆ Jsign) {l : V7} {B : ℕ}
    (hlJ : ∀ j ∈ J, iform l (Pi.single j 1) = 0) (hB : ∀ σ ∈ rootFinset .E7, |iform l σ| ≤ B)
    (hker : ∀ σ ∈ rootFinset .E7, iform l σ = 0 → σ ∈ parabolicRoots .E7 J)
    (Zs : List V7) (hZr : ∀ z ∈ Zs, IsRoot .E7 z)
    (hZJ : ∀ z ∈ Zs, ∀ j ∈ J, Even (iform z (Pi.single j 1)))
    (hZX : ∀ z ∈ Zs, InvComm (stdRankOne D₇ z) X)
    (hLevi : ∀ y : ModGL .E7 (GaloisField p f), y ∈ adjointGroup .E7 (GaloisField p f) →
      y * rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField p f)ˣ)) =
        rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField p f)ˣ)) * y →
      (∀ A : SL2 (GaloisField p f),
        y * rootSL2 .E7 (GaloisField p f) (Pi.single (e7Idx 0) 1) A =
          rootSL2 .E7 (GaloisField p f) (Pi.single (e7Idx 0) 1) A * y) →
      (∀ z ∈ Zs, y * rootDiagUnit .E7 (thetaDiag z (-1 : (GaloisField p f)ˣ)) =
        rootDiagUnit .E7 (thetaDiag z (-1 : (GaloisField p f)ˣ)) * y) →
      baseChangeGL (algebraMap (GaloisField p f) (AlgebraicClosure (GaloisField p f))) y ∈
        parabolicLevi .E7 (AlgebraicClosure (GaloisField p f)) J) :
    ∃ x : M₇, conjSub x (stdRankOne D₇ thetaE7) = stdRankOne D₇ thetaE7 ∧
      conjSub x (stdRankOne D₇ (Pi.single (e7Idx 0) 1)) = stdRankOne D₇ (Pi.single (e7Idx 0) 1) ∧
      (∀ z ∈ Zs, conjSub x (stdRankOne D₇ z) = stdRankOne D₇ z) ∧
      ∃ γ : V7, IsRoot .E7 γ ∧ conjSub x X = stdRankOne D₇ γ := by
  have hF : ringChar (GaloisField p f) ≠ 2 := ringChar_galoisField_ne_two hp2
  obtain ⟨hodd, h5⟩ := odd_and_five_le_card_galoisField hp2 hq
  obtain ⟨hsingle, hRθF, hperf⟩ := e7_fund_class hp2 hq
  have he0 : IsRoot .E7 (Pi.single (e7Idx 0) 1 : V7) := isRoot_single .E7 (e7Idx 0)
  have he0F := std_mem_fund hq he0
  obtain ⟨r₁, hr₁, hr₁2⟩ := exists_involution_fund hp2 hq hX
  obtain ⟨r₂, hr₂, hr₂2⟩ := exists_involution_std hp2 hq isRoot_thetaE7
  have hr₁₂ : r₂ * r₁ = r₁ * r₂ := hθX r₂ hr₂ hr₂2 r₁ hr₁ hr₁2
  have hεr₂ := εm_involution_std hp2 hq isRoot_thetaE7 hr₂ hr₂2
  obtain ⟨h, hh⟩ := hsingle _ hRθF X hX
  have hεr₁ := εm_involution_of_mem_fund hp2 hq (h := h) (by rw [← hh]; exact hr₁) hr₁2
  set y := εm (GaloisField p f) r₁ with hy
  have hr1sq : r₁ * r₁ = 1 := by rw [← sq]; exact hr₁2 ▸ pow_orderOf_eq_one r₁
  have hy2 : y * y = 1 := by
    rw [hy, ← map_mul, hr1sq, map_one]
  have hyd : y * rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField p f)ˣ)) =
      rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField p f)ˣ)) * y := by
    rw [← hεr₂, hy, ← map_mul, ← map_mul, hr₁₂.symm]
  have hye : ∀ A : SL2 (GaloisField p f),
      y * rootSL2 .E7 (GaloisField p f) (Pi.single (e7Idx 0) 1) A =
        rootSL2 .E7 (GaloisField p f) (Pi.single (e7Idx 0) 1) A * y := by
    intro A
    have hmem : rootSL2 .E7 (GaloisField p f) (Pi.single (e7Idx 0) 1) A ∈
        (stdRankOne D₇ (Pi.single (e7Idx 0) 1)).map (εm (GaloisField p f)) := by
      rw [map_stdRankOne_εm he0]
      exact ⟨A, rfl⟩
    obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.1 hmem
    rw [← hxe, hy, ← map_mul, ← map_mul, (hcomm x hx r₁ hr₁).symm]
  have hyz : ∀ z ∈ Zs, y * rootDiagUnit .E7 (thetaDiag z (-1 : (GaloisField p f)ˣ)) =
      rootDiagUnit .E7 (thetaDiag z (-1 : (GaloisField p f)ˣ)) * y := by
    intro z hz
    obtain ⟨rz, hrz, hrz2⟩ := exists_involution_std hp2 hq (hZr z hz)
    have hcz : rz * r₁ = r₁ * rz := hZX z hz rz hrz hrz2 r₁ hr₁ hr₁2
    rw [← εm_involution_std hp2 hq (hZr z hz) hrz hrz2, hy, ← map_mul, ← map_mul, hcz.symm]
  have hyJ := hLevi y (εm_mem r₁) hyd hye hyz
  obtain ⟨δ, hδ, u, huG, hu, hucomm⟩ := exists_rational_levi_conj hodd hlJ hB hker
    (εm_mem r₁) (εm_mem h) hy2 hyJ hεr₁.symm
  obtain ⟨x, hx⟩ := εm_surjective huG
  have hfix : ∀ z : V7, IsRoot .E7 z → (∀ j ∈ J, Even (iform z (Pi.single j 1))) →
      conjSub x (stdRankOne D₇ z) = stdRankOne D₇ z := by
    intro z hz hzJ
    have hzF := std_mem_fund hq hz
    apply eq_of_map_εm_eq (by rw [conjSub_commutator, hperf _ hzF]) (hperf _ hzF)
    have hwd : u * rootTorusSL2 .E7 (GaloisField p f) z (-1) =
        rootTorusSL2 .E7 (GaloisField p f) z (-1) * u := by
      rw [rootTorusSL2_eq_thetaDiag hz]
      exact hucomm _ (fun j hj => by simp [thetaDiag, (hzJ j hj).neg_one_zpow])
    rw [map_conjSub, hx, map_stdRankOne_εm hz,
      map_conj_rootRankOneGroup_of_commute_gen hF hodd hz huG hwd]
  have hθJ : ∀ j ∈ J, Even (iform thetaE7 (Pi.single j 1)) := fun j hj => by
    rw [(Jsign_thetaDiag_one j (hJ hj)).1]
    exact ⟨0, by simp⟩
  have he0J : ∀ j ∈ J, Even (iform (Pi.single (e7Idx 0) 1 : V7) (Pi.single j 1)) := fun j hj => by
    rw [(Jsign_thetaDiag_one j (hJ hj)).2]
    exact ⟨0, by simp⟩
  refine ⟨x, hfix _ isRoot_thetaE7 hθJ, hfix _ he0 he0J,
    fun z hz => hfix z (hZr z hz) (hZJ z hz), ?_⟩
  have hconj : (u * εm (GaloisField p f) h) * rootTorusSL2 .E7 (GaloisField p f) thetaE7 (-1) *
      (u * εm (GaloisField p f) h)⁻¹ =
      rootDiagUnit .E7 (thetaDiag δ (-1 : (GaloisField p f)ˣ)) := by
    rw [rootTorusSL2_thetaE7]
    calc (u * εm (GaloisField p f) h) *
          rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField p f)ˣ)) *
          (u * εm (GaloisField p f) h)⁻¹ =
        u * (εm (GaloisField p f) h *
          rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField p f)ˣ)) *
          (εm (GaloisField p f) h)⁻¹) * u⁻¹ := by group
      _ = u * y * u⁻¹ := by rw [← hεr₁]
      _ = _ := hu
  obtain ⟨γ, hγ, hLγ, -, -⟩ := exists_rootRankOneGroup_of_conj_toral hp2 hq
    (isLongRoot_of_isRoot_of_simplyLaced (Or.inr (Or.inl rfl)) isRoot_thetaE7)
    (mul_mem huG (εm_mem h)) (fun i => thetaDiag_neg_one_sign_E7 δ i) hconj
  have hγr : IsRoot .E7 γ := hγ.1
  refine ⟨γ, hγr, ?_⟩
  have hγF := std_mem_fund hq hγr
  rw [hh, ← conjSub_mul]
  apply eq_of_map_εm_eq (by rw [conjSub_commutator, hperf _ hRθF]) (hperf _ hγF)
  rw [map_conjSub, map_mul, hx, map_stdRankOne_εm isRoot_thetaE7, map_stdRankOne_εm hγr]
  exact hLγ

end Step

end CFSG.ClassicalInvolution.ModelFacts.E7Model
