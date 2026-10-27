module

public import CFSG.ClassicalInvolution.ModelFacts.E7ModelFrame
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

section Round

variable {p f : ℕ} [Fact p.Prime]

local notation "M₇" => E7sc p f
local notation "D₇" => e7Datum (GaloisField p f)
local notation "e0V" => (Pi.single (e7Idx 0) 1 : V7)

@[expose] def GRel (z : V7) : Bool → Subgroup M₇ → Prop
  | true, X => stdRankOne D₇ z ≠ X ∧ ¬ Commutes (stdRankOne D₇ z) X
  | false, X => Commutes (stdRankOne D₇ z) X

@[expose] def RRel (z : V7) : Bool → V7 → Prop
  | true, γ => iform z γ = 1 ∨ iform z γ = -1
  | false, γ => iform z γ = 0

theorem rRel_of_conj (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {z γ : V7} (hz : IsRoot .E7 z)
    (hγ : IsRoot .E7 γ) {X : Subgroup M₇} {k : M₇} (hkX : conjSub k X = stdRankOne D₇ γ)
    (hkz : conjSub k (stdRankOne D₇ z) = stdRankOne D₇ z) (b : Bool) (h : GRel z b X) :
    RRel z b γ := by
  cases b
  · exact iform_eq_zero_of_commutes hp2 hq hz hγ ((transport_rel hkz hkX).2.2 h)
  · obtain ⟨hne, hnc⟩ := h
    exact iform_odd_of_rel hp2 hq hz hγ ((transport_rel hkz hkX).1 hne)
      ((transport_rel hkz hkX).2.1 hnc)

theorem exists_conj_pin' {ω : List ℕ} {γ g : V7} (hγ : IsRoot .E7 γ)
    (h : wordAct ω γ = g ∨ wordAct ω γ = -g) (Zs : List V7)
    (hZ : ∀ z ∈ Zs, IsRoot .E7 z ∧ (wordAct ω z = z ∨ wordAct ω z = -z)) :
    ∃ k : M₇, conjSub k (stdRankOne D₇ γ) = stdRankOne D₇ g ∧
      ∀ z ∈ Zs, conjSub k (stdRankOne D₇ z) = stdRankOne D₇ z := by
  obtain ⟨k, hk⟩ := exists_conj_stdRankOne_wordAct (GaloisField p f) ω
  refine ⟨k, ?_, fun z hz => ?_⟩
  · rw [hk γ hγ]
    rcases h with h | h
    · rw [h]
    · rw [h, stdRankOne_neg]
  · rw [hk z (hZ z hz).1]
    rcases (hZ z hz).2 with h | h
    · rw [h]
    · rw [h, stdRankOne_neg]

theorem round_root (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {X : Subgroup M₇}
    (hX : X ∈ fundamentalSubgroups .E7 D₇) (bθ : Bool) (hθG : GRel thetaE7 bθ X)
    (hθX : InvComm (stdRankOne D₇ thetaE7) X) (hcomm : Commutes (stdRankOne D₇ e0V) X)
    {J : Set (Fin (Tag.rank .E7))} (hJ : J ⊆ Jsign) {l : V7} {B : ℕ}
    (hlJ : ∀ j ∈ J, iform l (Pi.single j 1) = 0) (hB : ∀ σ ∈ rootFinset .E7, |iform l σ| ≤ B)
    (hker : ∀ σ ∈ rootFinset .E7, iform l σ = 0 → σ ∈ parabolicRoots .E7 J)
    (Zs : List (V7 × Bool)) (hZr : ∀ zb ∈ Zs, IsRoot .E7 zb.1)
    (hZJ : ∀ zb ∈ Zs, ∀ j ∈ J, Even (iform zb.1 (Pi.single j 1)))
    (hZX : ∀ zb ∈ Zs, InvComm (stdRankOne D₇ zb.1) X) (hZG : ∀ zb ∈ Zs, GRel zb.1 zb.2 X)
    (hLevi : ∀ y : ModGL .E7 (GaloisField p f), y ∈ adjointGroup .E7 (GaloisField p f) →
      y * rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField p f)ˣ)) =
        rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField p f)ˣ)) * y →
      (∀ A : SL2 (GaloisField p f),
        y * rootSL2 .E7 (GaloisField p f) (Pi.single (e7Idx 0) 1) A =
          rootSL2 .E7 (GaloisField p f) (Pi.single (e7Idx 0) 1) A * y) →
      (∀ zb ∈ Zs, y * rootDiagUnit .E7 (thetaDiag zb.1 (-1 : (GaloisField p f)ˣ)) =
        rootDiagUnit .E7 (thetaDiag zb.1 (-1 : (GaloisField p f)ˣ)) * y) →
      baseChangeGL (algebraMap (GaloisField p f) (AlgebraicClosure (GaloisField p f))) y ∈
        parabolicLevi .E7 (AlgebraicClosure (GaloisField p f)) J) :
    ∃ x : M₇, conjSub x (stdRankOne D₇ thetaE7) = stdRankOne D₇ thetaE7 ∧
      conjSub x (stdRankOne D₇ e0V) = stdRankOne D₇ e0V ∧
      (∀ zb ∈ Zs, conjSub x (stdRankOne D₇ zb.1) = stdRankOne D₇ zb.1) ∧
      ∃ γ : V7, IsRoot .E7 γ ∧ conjSub x X = stdRankOne D₇ γ ∧ RRel thetaE7 bθ γ ∧
        iform e0V γ = 0 ∧ ∀ zb ∈ Zs, RRel zb.1 zb.2 γ := by
  have he0 : IsRoot .E7 e0V := isRoot_single .E7 (e7Idx 0)
  obtain ⟨x, hxθ, hxe, hxZ, γ, hγ, hxγ⟩ := stage_step hp2 hq hX hθX hcomm hJ hlJ hB hker
    (Zs.map Prod.fst) (fun z hz => by
      obtain ⟨zb, hzb, rfl⟩ := List.mem_map.1 hz
      exact hZr zb hzb)
    (fun z hz j hj => by
      obtain ⟨zb, hzb, rfl⟩ := List.mem_map.1 hz
      exact hZJ zb hzb j hj)
    (fun z hz => by
      obtain ⟨zb, hzb, rfl⟩ := List.mem_map.1 hz
      exact hZX zb hzb)
    (fun y hyG hyd hye hyz => hLevi y hyG hyd hye fun zb hzb =>
      hyz zb.1 (List.mem_map.2 ⟨zb, hzb, rfl⟩))
  refine ⟨x, hxθ, hxe, fun zb hzb => hxZ zb.1 (List.mem_map.2 ⟨zb, hzb, rfl⟩), γ, hγ, hxγ,
    rRel_of_conj hp2 hq isRoot_thetaE7 hγ hxγ hxθ bθ hθG, ?_, fun zb hzb => ?_⟩
  · exact rRel_of_conj hp2 hq he0 hγ hxγ hxe false hcomm
  · exact rRel_of_conj hp2 hq (hZr zb hzb) hγ hxγ
      (hxZ zb.1 (List.mem_map.2 ⟨zb, hzb, rfl⟩)) zb.2 (hZG zb hzb)

theorem round_pin (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {X : Subgroup M₇}
    (hX : X ∈ fundamentalSubgroups .E7 D₇) (bθ : Bool) (hθG : GRel thetaE7 bθ X)
    (hθX : InvComm (stdRankOne D₇ thetaE7) X) (hcomm : Commutes (stdRankOne D₇ e0V) X)
    {J : Set (Fin (Tag.rank .E7))} (hJ : J ⊆ Jsign) {l : V7} {B : ℕ}
    (hlJ : ∀ j ∈ J, iform l (Pi.single j 1) = 0) (hB : ∀ σ ∈ rootFinset .E7, |iform l σ| ≤ B)
    (hker : ∀ σ ∈ rootFinset .E7, iform l σ = 0 → σ ∈ parabolicRoots .E7 J)
    (Zs : List (V7 × Bool)) (hZr : ∀ zb ∈ Zs, IsRoot .E7 zb.1)
    (hZJ : ∀ zb ∈ Zs, ∀ j ∈ J, Even (iform zb.1 (Pi.single j 1)))
    (hZX : ∀ zb ∈ Zs, InvComm (stdRankOne D₇ zb.1) X) (hZG : ∀ zb ∈ Zs, GRel zb.1 zb.2 X)
    (hLevi : ∀ y : ModGL .E7 (GaloisField p f), y ∈ adjointGroup .E7 (GaloisField p f) →
      y * rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField p f)ˣ)) =
        rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField p f)ˣ)) * y →
      (∀ A : SL2 (GaloisField p f),
        y * rootSL2 .E7 (GaloisField p f) (Pi.single (e7Idx 0) 1) A =
          rootSL2 .E7 (GaloisField p f) (Pi.single (e7Idx 0) 1) A * y) →
      (∀ zb ∈ Zs, y * rootDiagUnit .E7 (thetaDiag zb.1 (-1 : (GaloisField p f)ˣ)) =
        rootDiagUnit .E7 (thetaDiag zb.1 (-1 : (GaloisField p f)ˣ)) * y) →
      baseChangeGL (algebraMap (GaloisField p f) (AlgebraicClosure (GaloisField p f))) y ∈
        parabolicLevi .E7 (AlgebraicClosure (GaloisField p f)) J)
    (g : V7) (words : List (List ℕ))
    (hpin : ∀ γ : V7, IsRoot .E7 γ → RRel thetaE7 bθ γ → iform e0V γ = 0 →
      (∀ zb ∈ Zs, RRel zb.1 zb.2 γ) → ∃ ω ∈ words, (wordAct ω γ = g ∨ wordAct ω γ = -g) ∧
        (wordAct ω thetaE7 = thetaE7 ∨ wordAct ω thetaE7 = -thetaE7) ∧
        (wordAct ω e0V = e0V ∨ wordAct ω e0V = -e0V) ∧
        ∀ zb ∈ Zs, wordAct ω zb.1 = zb.1 ∨ wordAct ω zb.1 = -zb.1) :
    ∃ k : M₇, conjSub k X = stdRankOne D₇ g ∧
      conjSub k (stdRankOne D₇ thetaE7) = stdRankOne D₇ thetaE7 ∧
      conjSub k (stdRankOne D₇ e0V) = stdRankOne D₇ e0V ∧
      ∀ zb ∈ Zs, conjSub k (stdRankOne D₇ zb.1) = stdRankOne D₇ zb.1 := by
  have he0 : IsRoot .E7 e0V := isRoot_single .E7 (e7Idx 0)
  obtain ⟨x, hxθ, hxe, hxZ, γ, hγ, hxγ, hrθ, hre, hrZ⟩ := round_root hp2 hq hX bθ hθG hθX hcomm
    hJ hlJ hB hker Zs hZr hZJ hZX hZG hLevi
  obtain ⟨ω, -, hωγ, hωθ, hωe, hωZ⟩ := hpin γ hγ hrθ hre hrZ
  obtain ⟨k, hkγ, hkZ⟩ := exists_conj_pin' (p := p) (f := f) hγ hωγ
    (thetaE7 :: e0V :: Zs.map Prod.fst) (by
      intro z hz
      simp only [List.mem_cons, List.mem_map] at hz
      rcases hz with rfl | rfl | ⟨zb, hzb, rfl⟩
      · exact ⟨isRoot_thetaE7, hωθ⟩
      · exact ⟨he0, hωe⟩
      · exact ⟨hZr zb hzb, hωZ zb hzb⟩)
  refine ⟨k * x, ?_, ?_, ?_, fun zb hzb => ?_⟩
  · rw [conjSub_mul, hxγ]
    exact hkγ
  · rw [conjSub_mul, hxθ]
    exact hkZ thetaE7 (by simp)
  · rw [conjSub_mul, hxe]
    exact hkZ e0V (by simp)
  · rw [conjSub_mul, hxZ zb hzb]
    exact hkZ zb.1 (by
      simp only [List.mem_cons, List.mem_map]
      exact Or.inr (Or.inr ⟨zb, hzb, rfl⟩))

theorem pair_normal (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {A B : Subgroup M₇}
    (hA : A ∈ fundamentalSubgroups .E7 D₇) (hB : B ∈ fundamentalSubgroups .E7 D₇)
    (hadj : Gaps.ModelAdj (Subgroup.center M₇) A B)
    (hlin : ∃ W, LinearBlockStandardPair (GaloisField p f) W A B) :
    ∃ x : M₇, conjSub x A = stdRankOne D₇ e0V ∧ conjSub x B = stdRankOne D₇ thetaE7 := by
  have he0 : IsRoot .E7 e0V := isRoot_single .E7 (e7Idx 0)
  have he2 : IsRoot .E7 (Pi.single (e7Idx 2) 1 : V7) := isRoot_single .E7 (e7Idx 2)
  obtain ⟨g, hg1, hg2⟩ := e7PairFrame_sc hp2 hq A hA B hB hadj hlin 0 2 (by decide)
  have hpair : iform (Pi.single (e7Idx 2) 1 : V7) e0V = 1 ∨
      iform (Pi.single (e7Idx 2) 1 : V7) e0V = -1 := by decide +kernel
  obtain ⟨k, hk2, hk0⟩ := exists_conj_theta_e0 (GaloisField p f) he2 he0 hpair
  rw [e7Idx_zero] at hk0
  refine ⟨k * g⁻¹, ?_, ?_⟩
  · rw [conjSub_mul, hg1, conjSub_inv_conjSub]
    exact hk0
  · rw [conjSub_mul, hg2, conjSub_inv_conjSub]
    exact hk2

end Round

end CFSG.ClassicalInvolution.ModelFacts.E7Model
