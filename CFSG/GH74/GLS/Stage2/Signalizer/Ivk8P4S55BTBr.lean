module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTBrF
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTO2m
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTCnt
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFit
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTNP
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55Lift55
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55FTA

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S T Tstar : Subgroup G} {p : ℕ}
  {H P : Subgroup G} {g : G} {X Y : Subgroup G} {t : G} {q : ℕ} {I Q₁ : Subgroup G}

theorem bridgeB_of (hS : P34.GHSchreier) (hL31 : Lemma31Narrow) (hInv : InvSec)
    (h : Cfg55E G z k S T Tstar p H P g X Y) (hd : Data5A2 z k S T Tstar p H P t q I Q₁)
    (hOut : ∀ J' : Subgroup (HBar H), IsComponent J' → OutTwoNilp (↥J' ⧸ center ↥J')) :
    ∃ J : Subgroup (HBar H), BridgeB k p H P g J := by
  have hp : p.Prime := prime h
  have hp2 : p ≠ 2 := odd h
  have hpf : Fact p.Prime := ⟨hp⟩
  have hgH : g ∈ H := g_mem_H h
  have hgP : g ∈ P := g_mem h
  obtain ⟨Γ₀, _, _, V, _, _, _, ρ₀, π, hπ, hρ, hOp, hker, hquadall⟩ :=
    chief_module p (chief h) (X_pgroup h)
  have hquad := hquadall ⟨g, hgH⟩ (quad_comm h)
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
  obtain ⟨n₀, hn₀⟩ := P_pgroup h ⟨g, hgP⟩
  have hgn : (⟨g, hgH⟩ : ↥H) ^ p ^ n₀ = 1 :=
    Subtype.ext (by simpa using congrArg Subtype.val hn₀)
  have hpodd : Odd (p ^ n₀) := (hp.odd_of_ne_two hp2).pow
  have hodd : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ p → ∀ Q : Subgroup Γ₀, Q.Normal → IsPGroup r ↥Q →
      Q ≤ centralizer ({π ⟨g, hgH⟩} : Set Γ₀) := by
    intro r hr hr2 hrp Q hQn hQ
    have := Fact.mk hr
    exact quadratic_le_centralizer_odd (F := ZMod p) (V := V) hp2 hr2 hrp ρ₀ hρ hquad hQ
      (by rw [Subgroup.normalizer_eq_top_iff.mpr hQn]; exact Subgroup.mem_top _)
  let ν : ↥H →* HBar H := QuotientGroup.mk' (pPrimeCore 2 ↥H)
  have hν : Function.Surjective ν := QuotientGroup.mk'_surjective _
  have hcnt := no_three_comps hL31 h (z_mem_H h hd.u)
  have hgC : ∀ c ∈ centralizer (layer (HBar H) : Set (HBar H)),
      ν ⟨g, hgH⟩ * c = c * ν ⟨g, hgH⟩ := by
    intro c hc
    have hmem : ν ⟨g, hgH⟩ ∈ barIn H P := ⟨⟨g, hgH⟩, hgP, rfl⟩
    exact ((Subgroup.mem_centralizer_iff.mp (P_centralizes h hmem)) c hc).symm
  have h2 : pCore 2 Γ₀ ≤ centralizer ({π ⟨g, hgH⟩} : Set Γ₀) :=
    pCore_two_le_centralizer_of_transfer π hπ hpodd hgn hgC hcnt fun J' hJ' _ => hOut J' hJ'
  have hap : ∃ n : ℕ, π ⟨g, hgH⟩ ^ p ^ n = 1 := ⟨n₀, by rw [← map_pow, hgn, map_one]⟩
  obtain ⟨K, hK, hKnc⟩ := exists_component_not_le_centralizer' hO hap ha1 h2 hodd
  have haK : π ⟨g, hgH⟩ ∈ normalizer (K : Set Γ₀) :=
    quad_mem_normalizer_component hp2 ρ₀ hρ hquad hK
  have hna : π ⟨g, hgH⟩ ∉ centralizer (K : Set Γ₀) := by
    intro hc
    apply hKnc
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr ((Subgroup.mem_centralizer_iff.mp hc) x hx)
  have hνker : ν.ker = pPrimeCore 2 ↥H := QuotientGroup.ker_mk' _
  have hνodd : Odd (Nat.card ν.ker) := by
    rw [hνker]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  obtain ⟨Lb, W, hLbsub, hLbperf, hLbn, hWle, hWn, hWnormal, hsimple, hnonab, hmove, hrec⟩ :=
    lift_setup ν π hν hπ hνodd hK haK hna
  have hpM : pPrimeCore 2 (HBar H) = ⊥ :=
    _root_.CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := ↥H) 2
  have hghM : ∀ J : Subgroup (HBar H), IsComponent J → GHList (↥J ⧸ center ↥J) :=
    fun J hJ => ghList_of_quotient_component h.ctx.std.kgh (H_ne_top h) ν hν hJ.1
  have hĝp : ∃ n : ℕ, ν ⟨g, hgH⟩ ^ p ^ n = 1 := ⟨n₀, by rw [← map_pow, hgn, map_one]⟩
  obtain ⟨J, hJ, hJL, hJW, hJc⟩ := lift55_thm hS (HBar H) p hp2 hpM hghM hcnt (ν ⟨g, hgH⟩)
    hĝp (pCore_two_le_centralizer h) Lb W hLbsub hLbperf hLbn hWle hWn hWnormal hsimple hnonab
    hmove
  obtain ⟨hDlK, ⟨e⟩⟩ := hrec J hJ hJL hJW
  set Dl : Subgroup ↥H := perfCore (J.comap ν) with hDl
  have hDlperf : ⁅Dl, Dl⁆ = Dl := commutator_perfCore _
  have hDlJ : Dl.map ν = J :=
    map_perfCore_comap_of_subnormal ν hν J hJ.2 (Subgroup.isPerfect_iff.mp hJ.1.1)
  have hDln : ∀ x : ↥H, ν x ∈ normalizer (J : Set (HBar H)) → x ∈ normalizer (Dl : Set ↥H) :=
    fun x hx => mem_normalizer_perfCore (mem_normalizer_comap ν hx)
  have hidx : (normalizer (K : Set Γ₀)).index ≤ 2 := index_le_two ν π hπ hJ hDln hDlK hcnt
  have hgh : GHList (↥K ⧸ center ↥K) :=
    ghList_of_quotient_component h.ctx.std.kgh (H_ne_top h) π hπ hK.1
  have hr3 : InvSecGroup k (↥K ⧸ center ↥K) :=
    InvSecGroup.of_equiv e (invSecGroup_of_component hInv h.ctx H hJ)
  have hJg : ¬ barIn H (zpowers g) ≤ centralizer (J : Set (HBar H)) := by
    intro hle
    apply hJc
    intro x hx
    have hmem : ν ⟨g, hgH⟩ ∈ barIn H (zpowers g) := ⟨⟨g, hgH⟩, Subgroup.mem_zpowers g, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp (hle hmem)) x hx)
  exact ⟨J, frameB_of_data hp hp2 hgH hgP (P_pgroup h) ρ₀ hρ hOp π hπ hK hna hquad hgh hr3 hidx
    hJ hJg hDlperf hDlJ hDlK hDln⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
