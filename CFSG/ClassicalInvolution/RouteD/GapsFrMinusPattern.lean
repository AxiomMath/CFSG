module

public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusZ
public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusNodesImg
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedDChain
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedDDischarge
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
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.Assembly.LowTwoRank CFSG.LieType CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.CurtisTits

local macro "fr_idx" : tactic =>
  `(tactic| first
    | (simp [DNodes.adj_def]; done)
    | (simp [DNodes.adj_def]; omega)
    | (simp; done)
    | (simp; omega)
    | omega)

section Main

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem PartnerPatternMinus.of_fixed_member (hMFZ : FundNoncentral p) {u : ℕ} (hu : 1 ≤ u)
    (c : TCtx p f .POmegaMinus (u + 3 + 5) Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 .POmegaMinus (u + 3 + 5) Ω z) {β : Subgroup G} {t : G}
    (hβ : β ∈ Ω) (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β)
    (hfix : HasFixedMember Ω K β z) : PartnerPatternMinus p f (u + 3 + 5) Ω K β t := by
  classical
  have hΩ := c.hΩ
  have htz := partner_involution_commutes c.hp2 c.hz ht hKβ
  obtain ⟨M, hMΩ, hKM, hβM, hMnot⟩ := hfix
  have hMN : ∃ N ∈ centralizingMembers Ω {z}, N ≠ M ∧ ¬ Commutes M N := by
    by_contra hcon
    push Not at hcon
    exact hMnot hcon
  obtain ⟨nd, h0, h1⟩ := exists_dnodes_of_pair_minus (by omega) c hsingle hshape hβ ht hKβ hMΩ hKM
    hβM
  obtain ⟨x, hx2, hxfix⟩ := minus_fixed_of_nodes hMFZ hu c hsingle hshape ht hKβ hMΩ hMN nd h0 h1
  obtain ⟨j, hjK, hjperf, hjY, hjΩ, hjc, hjp, hjtw, hjimg⟩ :=
    exists_nodes_typeTwistedD_img (m := u + 3 + 5) (by omega) (spinMinus6Generated_galois c.hp2)
      (spinMinus6_noCover_galois c.hp2 c.hq) c
  obtain ⟨y₀, hy₀⟩ := QuotientGroup.mk_surjective (c.d.ψ x)
  have hy : (y₀ : G) ∈ locLayer Ω z := y₀.2
  have hyz : (y₀ : G) * z * (y₀ : G)⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp
      (centralizingLayer_le_centralizer Ω {z} hy)
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  have himg : ∀ a : Fin (u + 3 + 5 - 1), locImg Ω z (conjSub (y₀ : G) (j a)) =
      ((rankOne (minusDatum (u + 3 + 5) (minusCoeffs_irr p f)).rootGroup a).map
        (MulAut.conj x).toMonoidHom).map c.d.ψ := by
    intro a
    rw [locImg_conjSub_layer, hjimg a, show locMk Ω z y₀ = c.d.ψ x from hy₀]
    exact map_conj_map_hom c.d.ψ x _
  refine PartnerPatternMinus.of_locAut c hjK hjperf hjY hjΩ hjc hjp hjtw hy htz
    (fun a ha w hw => ?_) (fun a ha => ?_)
  · rw [himg a] at hw
    obtain ⟨r, hr, rfl⟩ := hw
    exact hxfix a ha r hr
  ·
    obtain ⟨a', ha'⟩ := a
    have ha0 : a' = 0 := ha
    subst ha0
    have hmemy : conjSub (y₀ : G) (j ⟨0, by omega⟩) ∈ centralizingMembers Ω {z} := by
      have := centralizingMembers_conj hΩ.conjInvariant (y₀ : G) z
      rw [hyz] at this
      rw [this]
      exact ⟨j ⟨0, by omega⟩, mem_centralizingMembers_of_commutes (hjΩ _ (by simp))
        c.hz.mem (commutes_symm (hjK _)), rfl⟩
    have hK2 : Commutes K (nd.J ⟨2, by omega⟩) := by
      rw [← h0]
      exact nd.commutes_of_not_adj (fin_ne_of_val_ne (by simp)) (by fr_idx)
    have hJ2 : nd.J ⟨2, by omega⟩ ∈ centralizingMembers Ω {z} :=
      mem_centralizingMembers_of_commutes (nd.mem _) c.hz.mem (commutes_symm hK2)
    have heq : conjSub (y₀ : G) (j ⟨0, by omega⟩) = nd.J ⟨2, by omega⟩ :=
      c.eq_of_locImg_eq hmemy hJ2 (by rw [himg, hx2])
    rw [heq]
    obtain ⟨W, hW⟩ := nd.pair_of_adj (a := ⟨1, by omega⟩) (b := ⟨2, by omega⟩) (by fr_idx)
    rw [h1] at hW
    exact ⟨W, hW⟩

end Main

end CFSG.ClassicalInvolution.RouteD.Gaps
