module

public import CFSG.ClassicalInvolution.RouteD.GapsPatternB
public import CFSG.ClassicalInvolution.RouteD.GapsChainConfig
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
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G} {tY : StatedLieTag} {nY : ℕ}

theorem path_all_fixed_false {n : ℕ} (hn : 6 ≤ n) {d : ℕ} (hd : d < 2 * n + 4)
    (hF : ChainBound (Subgroup.center (modelUniv tY nY p f Fact.out).K)
      (fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D) d)
    (c : TCtx p f tY nY Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 tY nY Ω z) (nd : LNodes p f (adjPath n) Ω K)
    {β : Subgroup G} {t : G} (hβ : β ∈ Ω) (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β)
    (hfix : ∀ a, Commutes β (nd.J a)) : False := by
  classical
  have hΩ := c.hΩ
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f c.hp2
  obtain ⟨W, hW⟩ := hKβ
  have hnKβ : ¬ Commutes K β := not_commutes_of_linearBlockStandardPair hW
  have hKne : K ≠ β := ne_of_linearBlockStandardPair hW
  have hzt : Commute z t :=
    standardPair_involutions_commute h2 hW c.hz.mem ht.mem c.hz.orderOf_eq_two ht.orderOf_eq_two
  have hnormK : conjSub t K = K :=
    conjSub_eq_of_standardPair h2 hW ht.mem ht.orderOf_eq_two
  let b : Fin n := ⟨0, by omega⟩
  obtain ⟨cx⟩ := exists_ctx_member c hsingle hshape (nd.mem b) (nd.cl b)
  let idx : ℕ → Fin n := fun a => ⟨min (a + 2) (n - 1), by omega⟩
  have hidx : ∀ a, a < n - 2 → (idx a).val = a + 2 := fun a ha => by
    show min (a + 2) (n - 1) = a + 2
    omega
  have hbne : ∀ a, a < n - 2 → idx a ≠ b := fun a ha =>
    fin_ne_of_val_ne (by rw [hidx a ha]; show a + 2 ≠ 0; omega)
  have hbadj : ∀ a, a < n - 2 → ¬ LNodes.Adj (adjPath n) (idx a) b := fun a ha h => by
    rcases h with h | h
    · have : (idx a).val + 1 = b.val := h
      rw [hidx a ha] at this
      exact absurd this (by show a + 2 + 1 ≠ 0; omega)
    · have : b.val + 1 = (idx a).val := h
      rw [hidx a ha] at this
      exact absurd this (by show 0 + 1 ≠ a + 2; omega)
  have hadjidx : ∀ a, a + 1 < n - 2 → LNodes.Adj (adjPath n) (idx a) (idx (a + 1)) := fun a ha => by
    left
    show (idx a).val + 1 = (idx (a + 1)).val
    rw [hidx a (by omega), hidx (a + 1) ha]
  have hnadjidx : ∀ a b', a + 1 < b' → b' < n - 2 →
      idx a ≠ idx b' ∧ ¬ LNodes.Adj (adjPath n) (idx a) (idx b') := fun a b' hab hb => by
    have h1 := hidx a (by omega)
    have h2 := hidx b' hb
    refine ⟨fin_ne_of_val_ne (by rw [h1, h2]; omega), fun h => ?_⟩
    rcases h with h | h
    · have : (idx a).val + 1 = (idx b').val := h
      rw [h1, h2] at this
      omega
    · have : (idx b').val + 1 = (idx a).val := h
      rw [h1, h2] at this
      omega
  have hloc : ∀ L : Subgroup G, L ∈ Ω → Commutes L (nd.J b) →
      L ∈ centralizingMembers Ω {nd.w b} := fun L hL hc => nd.mem_loc b hL hc
  have hchainmem : ∀ a, a < n - 2 → nd.J (idx a) ∈ centralizingMembers Ω {nd.w b} := fun a ha =>
    hloc _ (nd.mem _) (nd.commutes_of_not_adj (hbne a ha) (hbadj a ha))
  refine absurd (chain_config cx (r := n - 2) (c := fun a => nd.J (idx a))
    (w := fun a => nd.w (idx a)) hF (by omega) hchainmem (fun a _ => nd.cl (idx a))
    (fun a ha => ⟨nd.ne_J hΩ (nd.adj_ne (hadjidx a ha)), nd.not_commutes_of_adj (hadjidx a ha),
      nd.commute_w h2 _ _, nd.conjSub_w h2 (hadjidx a ha)⟩)
    (fun a b' hab hb => nd.commutes_of_not_adj (hnadjidx a b' hab hb).1
      (hnadjidx a b' hab hb).2)
    (hloc K c.hK (nd.commK b)) (hloc β hβ (hfix b)) c.hz ht hKne hnKβ hzt hnormK
    (fun a _ => nd.commK (idx a)) (fun a _ => hfix (idx a))) (by omega)

end CFSG.ClassicalInvolution.RouteD.Gaps
