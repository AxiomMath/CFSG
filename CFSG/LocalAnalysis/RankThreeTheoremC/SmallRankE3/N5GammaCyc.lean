module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGSixMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N5GammaGroup
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N5GammaOmega

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty Subgroup
open CFSG.LocalAnalysis.GLTheoremB (IsOmegaTwo)

variable {A : Type} [Group A] [Finite A] {p : ℕ} {Kb Sb Bb Mb : Subgroup A} {z : A}

theorem n5_false_of_omega (c : KQCfg A p Kb Sb Bb Mb z)
    (hnb : ∀ b ∈ Bb, b ≠ 1 → ¬ ∀ k ∈ Kb, b * k = k * b) {ε : Bool} {n : ℕ} (hn : 3 ≤ n)
    (hΩ : IsOmegaTwo ε n ↥Kb) : False := by
  have hp := c.prime
  have hone : 2 ≤ CFSG.Open.pRank p Kb := by
    refine n5_two_le_pRank_of_inner hp c.B_elem c.B_card
      (fun k hk h => KGQ.center_trivial c hk h) hnb ?_
    intro b hb
    set σ : MulAut ↥Kb := Kb.normalizerMonoidHom ⟨b, c.B_le_K hb⟩ with hσ
    have hσp : σ ^ p = 1 := by
      rw [hσ, ← map_pow]
      have : (⟨b, c.B_le_K hb⟩ : normalizer (Kb : Set A)) ^ p = 1 :=
        Subtype.ext (by simpa using c.B_elem.2 b hb)
      rw [this, map_one]
    obtain ⟨y, hy⟩ := n5_aut_omegaTwo_inner hp c.five_le hn hΩ σ hσp
    refine ⟨y.1, y.2, fun l hl => ?_⟩
    have := congrArg (fun f : MulAut ↥Kb => ((f ⟨l, hl⟩ : ↥Kb) : A)) hy
    simpa [hσ, Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply] using this
  have := c.rank
  omega

theorem n5_false_of_cyclic (hT : KGTransvCent)
    {G : Type} [Group G] [Finite G] {p : ℕ} {H D S B L M : Subgroup G} {z : G}
    [hDn : (D.subgroupOf H).Normal] (d3 : KGC.KGData3 p H D S B L M z)
    (hc : KGStep4Concl (KGC.QA H D) (KGC.img H D L) (KGC.img H D S))
    (hbot : KGC.img H D S ⊓ KGC.img H D L = ⊥) [IsCyclic ↥(KGC.img H D S)]
    (hnb : ∀ b ∈ KGC.img H D B, b ≠ 1 → ¬ ∀ k ∈ KGC.img H D L, b * k = k * b) : False := by
  have c := d3.toData.cfg
  obtain ⟨V, _, _, hV, ρ, hρK, a, ha, ha1, ha2, htv⟩ := KGSix.transvection_of_data d3
  have hp := c.prime
  have hp5 := c.five_le
  haveI : Fact p.Prime := ⟨hp⟩
  have haK : a ∉ KGC.img H D L := fun h => ha1 (by
    have : a ∈ KGC.img H D S ⊓ KGC.img H D L := ⟨ha, h⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact this)
  have hXn : KGC.img H D L ⊔ zpowers a ≤ KGC.img H D L ⊔ KGC.img H D S :=
    sup_le_sup_left (zpowers_le.mpr ha) _
  have hcomm : a * (KGC.qmk H D ⟨z, d3.toData.z_mem_H⟩) = (KGC.qmk H D ⟨z, d3.toData.z_mem_H⟩) * a := by
    have := KGSix.conj_eq_of_cyclic c ha ha1 ha2 c.z_mem_B
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  obtain ⟨ε, n, hn3, hΩ, -⟩ := hT (KGC.QA H D) V hV ρ (KGC.img H D L) a
    (KGC.qmk H D ⟨z, d3.toData.z_mem_H⟩) p c.simple c.nonab hc.2.2 (c.S_le_K ha) ha1 ha2 haK
    (fun x hx hxc => KGQ.eq_one_of_centralizes c (hXn hx) hxc)
    (fun x hx hρx => KGSix.eq_one_of_map_eq_one c ρ hρK (hXn hx) hρx) htv c.z_mem_K c.z_order hp
    hp5 hcomm
  exact n5_false_of_omega c hnb hn3 hΩ

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
