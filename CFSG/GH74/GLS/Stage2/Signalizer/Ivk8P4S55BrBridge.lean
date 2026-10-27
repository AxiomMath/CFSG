module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BrFrame
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BrGH
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BrNP
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BrData
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BridgeParts
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55FTA
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4QuadOdd

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped commutatorElement

theorem bridge55_of (hS : P34.GHSchreier) (hL : Lift55) (hC : Count55) (hInv : InvSec) :
    Bridge55 := by
  intro G _ _ z k S T Tstar p H P g X Y h
  have hp : p.Prime := h.prime
  have hp2 : p ≠ 2 := h.odd
  have hpf : Fact p.Prime := ⟨hp⟩
  have hgH : g ∈ H := h.g_mem_H
  have hgP : g ∈ P := h.g_mem
  obtain ⟨Γ₀, _, _, V, _, _, _, ρ₀, π, hπ, hρ, hOp, hker, hquadall⟩ :=
    chief_module p h.chief h.X_pgroup
  have hquad := hquadall ⟨g, hgH⟩ h.quad_comm
  have hO : pCore p Γ₀ = ⊥ := hOp _ pCore_normal pCore_isPGroup
  have ha1 : π ⟨g, hgH⟩ ≠ 1 := by
    intro h1
    apply h.s53.2.2.2.2.2.1
    have key : ∀ n : ℤ, ∀ x ∈ X, ⁅x, g ^ n⁆ ∈ Y := by
      intro n x hx
      have h2 : π ((⟨g, hgH⟩ : ↥H) ^ n) = 1 := by rw [map_zpow, h1, one_zpow]
      have := (hker _).mp h2 x hx
      simpa using this
    rw [Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact key n x hx
  obtain ⟨T₀, hT₀⟩ := exists_sylow_map π hπ h.T_sylow h.T_le
  have hP₁p : IsPGroup p ↥((P.subgroupOf H).map π) := map_isPGroup π h.P_pgroup
  have hTS : (T₀ : Subgroup Γ₀) ≤ normalizer (((P.subgroupOf H).map π : Subgroup Γ₀) : Set Γ₀) := by
    rw [hT₀]
    exact map_le_normalizer π h.T_norm
  have hgP₁ : π ⟨g, hgH⟩ ∈ (P.subgroupOf H).map π := ⟨⟨g, hgH⟩, hgP, rfl⟩
  have hodd : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ p → ∀ Q : Subgroup Γ₀, Q.Normal → IsPGroup r ↥Q →
      Q ≤ centralizer ({π ⟨g, hgH⟩} : Set Γ₀) := by
    intro r hr hr2 hrp Q hQn hQ
    have := Fact.mk hr
    exact quadratic_le_centralizer_odd (F := ZMod p) (V := V) hp2 hr2 hrp ρ₀ hρ hquad hQ
      (by rw [Subgroup.normalizer_eq_top_iff.mpr hQn]; exact Subgroup.mem_top _)
  obtain ⟨K, hK, hKnc⟩ :=
    exists_component_not_le_centralizer T₀ hP₁p hp2 hO hTS hgP₁ ha1 hodd
  have hKN : ∀ x ∈ (P.subgroupOf H).map π, x ∈ normalizer (K : Set Γ₀) := fun x hx =>
    mem_normalizer_component T₀ hp2 hP₁p hTS hx hK
  have hna : π ⟨g, hgH⟩ ∉ centralizer (K : Set Γ₀) := by
    intro hc
    apply hKnc
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr ((Subgroup.mem_centralizer_iff.mp hc) x hx)
  let ν : ↥H →* HBar H := QuotientGroup.mk' (pPrimeCore 2 ↥H)
  have hν : Function.Surjective ν := QuotientGroup.mk'_surjective _
  have hνker : ν.ker = pPrimeCore 2 ↥H := QuotientGroup.ker_mk' _
  have hνodd : Odd (Nat.card ν.ker) := by
    rw [hνker]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  obtain ⟨Lb, W, hLbsub, hLbperf, hLbn, hWle, hWn, hWnormal, hsimple, hnonab, hmove, hrec⟩ :=
    lift_setup ν π hν hπ hνodd hK (hKN _ hgP₁) hna
  have hpM : pPrimeCore 2 (HBar H) = ⊥ :=
    _root_.CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := ↥H) 2
  have hghM : ∀ J : Subgroup (HBar H), IsComponent J → GHList (↥J ⧸ center ↥J) :=
    fun J hJ => ghList_of_quotient_component h.ctx.std.kgh h.H_ne_top ν hν hJ.1
  have hcnt := hC G z k S T Tstar p H P g X Y h
  have hĝp : ∃ n : ℕ, ν ⟨g, hgH⟩ ^ p ^ n = 1 := by
    obtain ⟨n, hn⟩ := h.P_pgroup ⟨g, hgP⟩
    refine ⟨n, ?_⟩
    have h2 : (⟨g, hgH⟩ : ↥H) ^ p ^ n = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hn)
    rw [← map_pow, h2, map_one]
  obtain ⟨T₁, hT₁⟩ := exists_sylow_map ν hν h.T_sylow h.T_le
  have hP₂p : IsPGroup p ↥((P.subgroupOf H).map ν) := map_isPGroup ν h.P_pgroup
  have hT₁P₂ : (T₁ : Subgroup (HBar H)) ≤
      normalizer (((P.subgroupOf H).map ν : Subgroup (HBar H)) : Set (HBar H)) := by
    rw [hT₁]
    exact map_le_normalizer ν h.T_norm
  have hĝO : pCore 2 (HBar H) ≤ centralizer ({ν ⟨g, hgH⟩} : Set (HBar H)) :=
    pCore_two_le_centralizer T₁ hP₂p hp2 hT₁P₂ ⟨⟨g, hgH⟩, hgP, rfl⟩
  obtain ⟨J, hJ, hJL, hJW, hJc⟩ := hL hS (HBar H) p hp2 hpM hghM hcnt (ν ⟨g, hgH⟩) hĝp hĝO Lb W
    hLbsub hLbperf hLbn hWle hWn hWnormal hsimple hnonab hmove
  obtain ⟨hDlK, ⟨e⟩⟩ := hrec J hJ hJL hJW
  set Dl : Subgroup ↥H := perfCore (J.comap ν) with hDl
  have hDlperf : ⁅Dl, Dl⁆ = Dl := commutator_perfCore _
  have hDlJ : Dl.map ν = J :=
    map_perfCore_comap_of_subnormal ν hν J hJ.2 (Subgroup.isPerfect_iff.mp hJ.1.1)
  have hDln : ∀ x : ↥H, ν x ∈ normalizer (J : Set (HBar H)) → x ∈ normalizer (Dl : Set ↥H) :=
    fun x hx => mem_normalizer_perfCore (mem_normalizer_comap ν hx)
  have hidx : (normalizer (K : Set Γ₀)).index ≤ 2 := index_le_two ν π hπ hJ hDln hDlK hcnt
  have hgh : GHList (↥K ⧸ center ↥K) :=
    ghList_of_quotient_component h.ctx.std.kgh h.H_ne_top π hπ hK.1
  have hr3 : InvSecGroup k (↥K ⧸ center ↥K) :=
    InvSecGroup.of_equiv e (invSecGroup_of_component hInv h.ctx H hJ)
  have hJg : ¬ barIn H (zpowers g) ≤ centralizer (J : Set (HBar H)) := by
    intro hle
    apply hJc
    intro x hx
    have hmem : ν ⟨g, hgH⟩ ∈ barIn H (zpowers g) := ⟨⟨g, hgH⟩, Subgroup.mem_zpowers g, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp (hle hmem)) x hx)
  exact frame_of_data hp hp2 hgH hgP h.P_pgroup h.T_norm ρ₀ hρ hOp π hπ T₀ hT₀ hK hKN hna hquad
    hgh hr3 hidx hJ hJg hDlperf hDlJ hDlK hDln

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
