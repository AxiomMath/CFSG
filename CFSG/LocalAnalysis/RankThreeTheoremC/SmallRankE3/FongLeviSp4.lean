module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherBorel
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSylow
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSubspaceIndex
public import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194SpBlocks
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviConj
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviSetting
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2Carrier
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi

open Subgroup

theorem b2c_flag_eq {F : Type} [Field F] {i : ℕ} (hi : i ≤ 2) :
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.flag 2 F i =
      CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.isoFlag 2 F i := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.flag, if_pos hi]

theorem b2c_flag_mem_iso {F : Type} [Field F] {i : ℕ} (hi : i ≤ 2) :
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.flag 2 F i ∈
      CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.isoSubspaces 2 F i := by
  rw [b2c_flag_eq hi]
  exact And.intro
    (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.isTotallyIsotropic_isoFlag i)
    (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.finrank_isoFlag hi)

theorem b2c_isoCard {F : Type} [Field F] [Finite F] {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ 2) :
    Nat.card (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.isoSubspaces 2 F k) =
      (Nat.card F + 1) * (Nat.card F ^ 2 + 1) := by
  have hq1 : 1 < Nat.card F := Finite.one_lt_card
  have hq : 2 ≤ Nat.card F := hq1
  have hQ : (2 : ℚ) ≤ (Nat.card F : ℚ) := by exact_mod_cast hq
  have hne : (Nat.card F : ℚ) - 1 ≠ 0 := by
    have h0 : (0 : ℚ) < (Nat.card F : ℚ) - 1 := by linarith
    exact h0.ne'
  have h := CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.card_isoSubspaces
    (r := 2) (K := F) (q := Nat.card F) rfl hk2
  have hval : CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.isoGaussian 2 k (Nat.card F) =
      ((Nat.card F : ℚ) + 1) * ((Nat.card F : ℚ) ^ 2 + 1) := by
    interval_cases k
    · rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.isoGaussian_one, div_eq_iff hne]
      ring
    · rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.isoGaussian_self hq,
        Finset.prod_range_succ, Finset.prod_range_one]
      ring
  exact_mod_cast h.trans hval

theorem b2c_index {F : Type} [Field F] [Finite F] {i : ℕ} (hi1 : 1 ≤ i) (hi2 : i ≤ 2) :
    (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.stabilizer 2 F
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.flag 2 F i)).index =
      (Nat.card F + 1) * (Nat.card F ^ 2 + 1) := by
  have hW := b2c_flag_mem_iso (F := F) hi2
  have h1 := CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.index_projStabilizer hW
  have h2 : (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.stabilizer 2 F
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.flag 2 F i)).index =
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.projStabilizer 2 F
        (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.flag 2 F i)).index := by
    rw [← CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.comap_projStabilizer]
    exact Subgroup.index_comap_of_surjective _
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.proj_surjective (r := 2) (K := F))
  rw [h2, h1]
  exact b2c_isoCard hi1 hi2

theorem b2_core {F : Type} [Field F] [Finite F] [CharP F 2] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hKr : CFSG.Open.pRank p (⊤ : Subgroup (CFSG.Open.StatedSp 2 F)) ≤ 1)
    {P : Subgroup (CFSG.Open.StatedSp 2 F)}
    (hB : CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.borelSubgroup 2 F ≤ P) (hP : P ≠ ⊤)
    {z : CFSG.Open.StatedSp 2 F} (hz : z ∈ P) (hzp : orderOf z = p) : False := by
  obtain ⟨hPeq, -⟩ := CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.borel_overgroups P hB
  have hne : (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.borelCuts F P).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    apply hP
    rw [hPeq, hcon, CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.flagStabilizer_empty]
  obtain ⟨i, hi⟩ := hne
  obtain ⟨hi1, hi2⟩ := CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.borelCuts_le P i hi
  have hPQ : P ≤ CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.stabilizer 2 F
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.flag 2 F i) := by
    intro g hg
    rw [hPeq] at hg
    exact (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.mem_flagStabilizer.mp hg) i hi
  have hcardQ := Subgroup.card_mul_index
    (H := CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.stabilizer 2 F
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.flag 2 F i))
  rw [b2c_index (F := F) hi1 hi2,
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp_two F] at hcardQ
  have hq1 : 1 < Nat.card F := Finite.one_lt_card
  obtain ⟨a, ha⟩ : ∃ a : ℕ, Nat.card F = a + 1 := ⟨Nat.card F - 1, by omega⟩
  obtain ⟨f, hf⟩ : ∃ f : ℕ, Nat.card F = 2 ^ f := by
    have := Fintype.ofFinite F
    obtain ⟨n, -, hn⟩ := FiniteField.card F 2
    exact ⟨n, by rw [Nat.card_eq_fintype_card]; exact hn⟩
  have e1 : (a + 1) ^ 2 - 1 = a * (a + 2) := Nat.sub_eq_of_eq_add (by ring)
  have e2 : (a + 1) ^ 4 - 1 = a * (a + 2) * ((a + 1) ^ 2 + 1) := Nat.sub_eq_of_eq_add (by ring)
  rw [ha, e1, e2] at hcardQ
  set Q := CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.stabilizer 2 F
    (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.flag 2 F i) with hQ
  have hN : Nat.card Q = (a + 1) ^ 4 * (a ^ 2 * (a + 2)) := by
    apply Nat.eq_of_mul_eq_mul_right (show 0 < (a + 1 + 1) * ((a + 1) ^ 2 + 1) by positivity)
    rw [hcardQ]
    ring
  have hpN : p ∣ Nat.card Q := by
    have h := orderOf_dvd_natCard (⟨z, hPQ hz⟩ : Q)
    rwa [Subgroup.orderOf_mk, hzp] at h
  rw [hN] at hpN
  have hdiv : p ∣ a * (a + 2) := by
    rcases (Nat.Prime.dvd_mul hp).mp hpN with h4 | h5
    · exfalso
      have h6 : p ∣ a + 1 := hp.dvd_of_dvd_pow h4
      rw [← ha, hf] at h6
      have h7 : p ∣ 2 := hp.dvd_of_dvd_pow h6
      have h8 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h7
      omega
    · rcases (Nat.Prime.dvd_mul hp).mp h5 with h9 | h10
      · exact Dvd.dvd.mul_right (hp.dvd_of_dvd_pow h9) _
      · exact Dvd.dvd.mul_left h10 _
  have hdvd : p ∣ Nat.card F ^ 2 - 1 := by
    rw [ha, e1]
    exact hdiv
  have hle := CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.le_pRank_statedSp
    (K := F) (n := 2) (r := p) hp hdvd
  have h2 := le_trans hle hKr
  omega

noncomputable def statedProjSpEquiv {F : Type} [Field F] [CharP F 2] (n : ℕ) :
    CFSG.Open.StatedProj (CFSG.Open.StatedSp n F) ≃* CFSG.Open.StatedSp n F :=
  (QuotientGroup.quotientMulEquivOfEq
    (CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot (n := n) (K := F))).trans
    QuotientGroup.quotientBot

theorem b2_false {A : Type} [Group A] [Finite A] {K K₀ B : Subgroup A} {z : A} {p : ℕ}
    (S : E3Setting K K₀ B z p) {q : TauCeti.PrimePower} (hq2 : q.p = 2)
    (hv : (TauCeti.LieTypeIndex.B 2 q).Valid)
    (e : Nonempty (↥K ≃* TauCeti.ValidLieTypeIndex.Group ⟨.B 2 q, hv⟩)) : False := by
  obtain ⟨e⟩ := e
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B 2 q, hv⟩) with hF
  haveI : Finite F := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  have hcard : Nat.card F = 2 ^ q.exponent := by
    rw [CFSG.Models.card_fixedField_of (TauCeti.LieTypeIndex.characteristic_B 2 q)
      (TauCeti.LieTypeIndex.fieldExponent_B 2 q), hq2]
  haveI : CharP F 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card hcard
  let eG : ↥K ≃* CFSG.Open.StatedSp 2 F :=
    (e.trans (CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv)).trans
      (statedProjSpEquiv 2)
  obtain ⟨U₀, hU₀⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.exists_sylow_unipotent (K := F) 2 2
  obtain ⟨φ, P, hφ, hrange, hPK₀, hN⟩ := parabolic_transport eG S.hpar U₀
  have hU₀' : (U₀ : Set (CFSG.Open.StatedSp 2 F)) =
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.unipotent 2 F :
        Set (CFSG.Open.StatedSp 2 F)) :=
    congrArg (fun H : Subgroup (CFSG.Open.StatedSp 2 F) => (H : Set (CFSG.Open.StatedSp 2 F))) hU₀
  have hB : CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.borelSubgroup 2 F ≤ P := by
    rw [hU₀', CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.normalizer_unipotent] at hN
    exact hN
  have hP : P ≠ ⊤ := by
    intro h
    apply S.hne
    rw [← hPK₀, h, Subgroup.map_top, hrange]
  have hzmem : z ∈ P.map φ := by
    rw [hPK₀]
    exact S.hzK₀
  obtain ⟨z', hz'P, hz'z⟩ := Subgroup.mem_map.mp hzmem
  have hzp : orderOf z' = p := by
    rw [← S.hz, ← hz'z]
    exact (orderOf_injective φ hφ z').symm
  have hKr : CFSG.Open.pRank p (⊤ : Subgroup (CFSG.Open.StatedSp 2 F)) ≤ 1 := by
    have h1 := S.hKr
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup K,
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv S.hp.one_lt eG] at h1
    exact h1
  exact b2_core S.hp S.hp5 hKr hB hP hz'P hzp

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi
