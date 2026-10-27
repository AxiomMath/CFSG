module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxPConstr
public import CFSG.LocalAnalysis.RankThreeTheoremC.ReducedLayer
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622KxCfg

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty (S622IsSimpleSection)

variable {G : Type} [Group G] [Finite G]

theorem p622_not_hasNormalPComplement {p : ℕ} (hp : p.Prime) {X L : Subgroup G}
    (hL : S622IsSimpleSection L ⊥) (hLX : L ≤ X) {z : G} (hzL : z ∈ L) (hzp : orderOf z = p) :
    ¬ CFSG.HasNormalPComplement p ↥X := by
  intro h
  obtain ⟨N, hN, hcop, hquot⟩ := h
  haveI : Fact p.Prime := ⟨hp⟩
  have hsimple : IsSimpleGroup ↥L :=
    Subgroup.isSimpleGroup_iff.mpr ⟨hL.2.2.1.symm, fun H' hH' hn => hL.2.2.2.1 H' bot_le hH' hn⟩
  let φ : ↥L →* ↥X ⧸ N := (QuotientGroup.mk' N).comp (Subgroup.inclusion hLX)
  rcases Subgroup.Normal.eq_bot_or_eq_top (MonoidHom.ker φ) with hk | hk
  ·
    have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hk
    have hPL : IsPGroup p ↥L := hquot.of_injective φ hinj
    have hbot : ⊥ < Subgroup.center ↥L := IsPGroup.bot_lt_center hPL
    have htop : Subgroup.center ↥L = ⊤ :=
      (Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center ↥L)).resolve_left hbot.ne'
    obtain ⟨a, b, hab⟩ :=
      CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.exists_not_comm_of_section_bot hL
    have ha : a ∈ Subgroup.center ↥L := by
      rw [htop]
      exact Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp ha b).symm
  ·
    have hzmem : (⟨z, hzL⟩ : ↥L) ∈ MonoidHom.ker φ := by
      rw [hk]
      exact Subgroup.mem_top _
    have h1 : ((⟨z, hLX hzL⟩ : ↥X) : ↥X ⧸ N) = 1 := MonoidHom.mem_ker.mp hzmem
    have hzN : (⟨z, hLX hzL⟩ : ↥X) ∈ N := (QuotientGroup.eq_one_iff _).mp h1
    have hord : orderOf (⟨⟨z, hLX hzL⟩, hzN⟩ : N) = p := by
      rw [← hzp]
      exact (Subgroup.orderOf_coe (⟨⟨z, hLX hzL⟩, hzN⟩ : N)).symm.trans
        (Subgroup.orderOf_coe (⟨z, hLX hzL⟩ : ↥X)).symm
    have hdvd : p ∣ Nat.card N := by
      rw [← hord]
      exact orderOf_dvd_natCard _
    exact hp.one_lt.ne' (hcop.eq_one_of_dvd hdvd)

namespace P622KxCfg

variable {P : Sylow 3 G} {M : Subgroup G} {x z : G} {T S L : Subgroup G}

theorem isPConstrained_three (hL62 : P622Lemma62Three) (c : P622KxCfg 3 P M x z T S L) :
    CFSG.ABGLocalTools.IsPConstrained 3 ↥M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases hL62 G c.setting c.d1 c.d2 c.u0 P M c.conf.failure.situation x z c.conf.failure.point
      c.conf.failure.central with h | h
  · exact isPConstrained_of_hasPrimeConstraint h
  · exact absurd h (p622_not_hasNormalPComplement Nat.prime_three c.simple c.le_C c.z_mem
      c.orderOf_z)

theorem false_of_section_three (hL62 : P622Lemma62Three) (c : P622KxCfg 3 P M x z T S L)
    {H N : Subgroup G} (hHM : H ≤ M) (hs : S622IsSimpleSection H N) (hzH : z ∈ H)
    (hzN : z ∉ N) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hz := c.conf.failure.central
  have hzc : ∀ g ∈ (P : Subgroup G), g * z = z * g := fun g hg =>
    mem_centralizer_iff.mp hz.centralizes g hg
  exact CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.not_isPConstrained_of_section P c.P_le_M hz.mem
    hzc hz.pow_eq_one hHM hs hzH hzN (c.isPConstrained_three hL62)

end P622KxCfg

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
