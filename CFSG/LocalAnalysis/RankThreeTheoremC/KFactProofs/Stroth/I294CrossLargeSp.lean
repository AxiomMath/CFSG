module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossLargeTransfer
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossLargeModelDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.CrossPSL
import CFSG.GroupTheory.WeirSylow.Symplectic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG.Open CFSG.GroupTheory.WeirSylow CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

theorem I294Large.sq_eq_one_of_mem_scalars_statedSp {n : ℕ} (hn : 1 ≤ n) {F : Type} [Field F]
    (g : StatedSp n F)
    (hg : g ∈ (StatedScalars (Fin n ⊕ Fin n) F).subgroupOf (StatedSp n F)) : g ^ 2 = 1 := by
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hg
  have hc2 : c ^ 2 = 1 :=
    (CFSG.Open.StatedAPI.scalar_mem_statedSp_iff hn c).1 (by rw [hc]; exact g.2)
  apply Subtype.ext
  rw [Subgroup.coe_pow, ← hc, ← map_pow, hc2, map_one, Subgroup.coe_one]

theorem I294Large.not_dvd_card_ker_statedSp {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) {n : ℕ}
    (hn : 1 ≤ n) {F : Type} [Field F] [Finite F] :
    ¬ r ∣ Nat.card (QuotientGroup.mk'
      ((StatedScalars (Fin n ⊕ Fin n) F).subgroupOf (StatedSp n F))).ker := by
  intro hdvd
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' r hdvd
  have hx2 : x ^ 2 = 1 := by
    apply Subtype.ext
    have hmem := (QuotientGroup.ker_mk' _).le x.2
    exact I294Large.sq_eq_one_of_mem_scalars_statedSp hn _ hmem
  have h2 := orderOf_dvd_of_pow_eq_one hx2
  rw [hx] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  omega

theorem i294LargeModelPSp_holds : I294LargeModelPSp := by
  intro r hr h5 F _ _ hrF n hn hS
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fintype F := Fintype.ofFinite F
  have hrF' : ¬ r ∣ Fintype.card F := by rwa [← Nat.card_eq_fintype_card]
  have hodd : Odd r := hr.odd_of_ne_two (by omega)
  have hSp : I294Large.CommOrRank r (StatedSp n F) :=
    I294Large.CommOrRank.of_sylow_sigmaModel hr (PSLCross.one_le_padicValNat_card hr hrF')
      (fun P => sylow_Sp hodd F hrF' n P)
  have hPSp : I294Large.CommOrRank r (StatedProj (StatedSp n F)) :=
    I294Large.CommOrRank.of_surjective_coprime_ker hr (QuotientGroup.mk' _)
      (QuotientGroup.mk'_surjective _) (I294Large.not_dvd_card_ker_statedSp hr h5 hn) hSp
  obtain ⟨S, hS'⟩ := hS
  rcases hPSp with hc | hrk
  · exact (hS' (hc S)).elim
  · omega

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
