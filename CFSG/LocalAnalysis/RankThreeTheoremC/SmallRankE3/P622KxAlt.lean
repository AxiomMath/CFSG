module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622KxEmb
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxDefs
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpCoreA
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG CFSG.Open Subgroup
open CFSG.Yardstones.Md0ec50421ce4 (catalogIs onLie)
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty (S622IsSimpleSection KFact2024 KFact2401Three
  KFact2314 KFact1019 KFact2025 IsDihedralTypeIndex IsReeIndex IsRankTwoOddIndex
  normalizer_le_of_stronglyEmbedded_sub)

variable {G : Type} [Group G] [Finite G]

namespace P622KxCfg

variable {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G} {T S L : Subgroup G}

theorem le_of_section_three (hL613 : P622L613) (hp3 : p ≠ 3) (h2401 : KFact2401Three)
    (c : P622KxCfg p P M x z T S L)
    (hmodel : (∃ n : ℕ, 7 ≤ n ∧ Nonempty (↥L ≃* alternatingGroup (Fin n))) ∨
      catalogIs ↥L (onLie IsRankTwoOddIndex))
    {H N : Subgroup G} (hHL : H ≤ L) (hHM : H ≤ M) (hs : S622IsSimpleSection H N)
    (hzH : z ∈ H) (hzN : z ∉ N) (h3 : 3 ∣ N.relIndex H) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsE : GLBStronglyEmbedded 3 M :=
    c.stronglyEmbedded hL613 hp3 hHL hHM hs hzH hzN Nat.prime_three (by norm_num) (by omega) h3
  have h3H : 3 ∣ Nat.card H := h3.trans (Subgroup.index_dvd_card (N.subgroupOf H))
  obtain ⟨e, he⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) 3 h3H
  have he3 : IsPGroup 3 (zpowers (e : G)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, he, pow_one]
  obtain ⟨E₃, hE₃syl, hXE₃⟩ :=
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.exists_isSylowOf_ge (f := 3)
      (zpowers_le.mpr (hHL e.2)) he3
  have he1 : (e : G) ≠ 1 := by
    intro h1
    have : e = 1 := Subtype.ext h1
    rw [this, orderOf_one] at he
    omega
  have hE₃M : E₃ ⊓ M ≠ ⊥ := by
    intro hbot
    have hmem : (e : G) ∈ E₃ ⊓ M := ⟨hXE₃ (mem_zpowers _), hHM e.2⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact he1 hmem
  have hE₃p : IsPGroup 3 E₃ := hE₃syl.isPGroup
  have hLJ : L ≤ M ⊓ L := h2401 G L E₃ hmodel hE₃syl (M ⊓ L) fun S₀ hS₀E hS₀1 =>
    inf_le_inf_right L (normalizer_le_of_stronglyEmbedded_sub hsE hE₃p hE₃M hS₀E hS₀1)
  exact c.not_le (hLJ.trans inf_le_left)

theorem commutator_commutator_eq (c : P622KxCfg p P M x z T S L) :
    ⁅(⁅zpowers z, S⁆ : Subgroup G), zpowers z⁆ = ⁅zpowers z, S⁆ := by
  haveI : Fact p.Prime := ⟨c.prime⟩
  have hXP : zpowers z ≤ normalizer (S : Set G) := c.conf.z_le_normalizer
  have hcop : Nat.Coprime (Nat.card (zpowers z)) (Nat.card S) := by
    obtain ⟨k, hk⟩ := c.conf.S_isPGroup.exists_card_eq
    rw [hk, Nat.card_zpowers, c.orderOf_z]
    exact Nat.Coprime.pow_right k
      ((Nat.coprime_primes c.prime Nat.prime_two).mpr c.ne_two)
  have h := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.CoreA.commutator_commutator_eq_of_coprime
    hXP hcop
  rw [Subgroup.commutator_comm (zpowers z) S]
  exact h

theorem false_of_alt (hL613 : P622L613) (hp3 : p ≠ 3) (h2024 : KFact2024)
    (h2401 : KFact2401Three) (c : P622KxCfg p P M x z T S L) {n : ℕ} (hn : 7 ≤ n)
    (e : Nonempty (↥L ≃* alternatingGroup (Fin n))) : False := by
  have hp := c.prime
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    have hne2 := c.ne_two
    have hne4 : p ≠ 4 := fun h => by
      rw [h] at hp
      norm_num at hp
    omega
  obtain ⟨T', hT'R, hT'1, hzT', H, N, hH, hs, hzH, hzN, h3⟩ :=
    h2024 G L ⁅zpowers z, S⁆ z n p e (by omega) hp hp5 c.orderOf_z c.z_mem c.rank
      c.commutator_le c.conf.R_isPGroup (c.conf.R_ne_bot c.setting)
      (c.conf.z_le_normalizer_R (mem_zpowers z))
  have hRM : ⁅zpowers z, S⁆ ≤ M := c.conf.R_le_S.trans c.S_le_M
  have hT'M : T' ≤ M := hT'R.trans hRM
  have hT'L : T' ≤ L := hT'R.trans c.commutator_le
  have hT'2 : IsPGroup 2 T' := c.conf.R_isPGroup.to_le hT'R
  have hNM : normalizer (T' : Set G) ⊓ L ≤ M :=
    inf_le_left.trans (c.normalizer_le hT'L hT'2 hzT' (by rwa [inf_eq_left.mpr hT'M]))
  exact c.le_of_section_three hL613 hp3 h2401 (Or.inl ⟨n, hn, e⟩) (hH.trans inf_le_right)
    (hH.trans hNM) hs hzH hzN h3

theorem false_of_lieOdd (hL613 : P622L613) (hp3 : p ≠ 3) (h2314 : KFact2314)
    (h1019 : KFact1019) (h2025 : KFact2025) (h2401 : KFact2401Three)
    (c : P622KxCfg p P M x z T S L)
    (d : TauCeti.ValidLieTypeIndex) (hd2 : d.1.characteristic ≠ 2)
    (e : Nonempty (↥L ≃* (TauCeti.CFSGIndex.lie d).Group)) (hdih : ¬ IsDihedralTypeIndex d.1)
    (hree : ¬ IsReeIndex d.1) : False := by
  have hp := c.prime
  set f : ℕ := d.1.characteristic with hf
  have hfp : f.Prime := TauCeti.LieTypeIndex.characteristic_prime d.1
  have hmodel : catalogIs ↥L (onLie (fun d' =>
      d'.characteristic = f ∧ ¬ IsDihedralTypeIndex d' ∧ ¬ IsReeIndex d')) := by
    refine ⟨TauCeti.CFSGIndex.lie d, ?_, e⟩
    show d.1.characteristic = f ∧ ¬ IsDihedralTypeIndex d.1 ∧ ¬ IsReeIndex d.1
    exact ⟨rfl, hdih, hree⟩
  have hrank : ∀ U : Subgroup G, U ≤ L → U ≠ ⊥ → IsPGroup 2 U →
      CFSG.Open.pRank f (normalizer (U : Set G) ⊓ L) ≤ 3 := by
    intro U hUL hU1 hU2
    by_contra hlt
    push Not at hlt
    exact c.false_of_gen hfp hd2 ⟨U, hUL, hU1, hU2, hlt⟩
  have hlist := h1019 G L d hd2 e hrank
  have hrk2 : catalogIs ↥L (onLie IsRankTwoOddIndex) := by
    rcases hlist with h | h | h
    · exact absurd h hdih
    · exact absurd h hree
    · refine ⟨TauCeti.CFSGIndex.lie d, ?_, e⟩
      exact h
  have hR2 := c.commutator_commutator_eq
  obtain ⟨H, N, hH, hs, hzH, hzN, h3⟩ :=
    h2025 G L ⁅zpowers z, S⁆ z p hrk2 hp c.ne_two c.orderOf_z c.z_mem c.rank
      c.commutator_le c.conf.R_isPGroup (c.conf.R_ne_bot c.setting)
      (c.conf.z_le_normalizer_R (mem_zpowers z)) hR2
  have hRM : ⁅zpowers z, S⁆ ≤ M := c.conf.R_le_S.trans c.S_le_M
  have hRL : ⁅zpowers z, S⁆ ≤ L := c.commutator_le
  have hNM : normalizer ((⁅zpowers z, S⁆ : Subgroup G) : Set G) ⊓ L ≤ M :=
    inf_le_left.trans (c.normalizer_le hRL c.conf.R_isPGroup
      (c.conf.z_le_normalizer_R (mem_zpowers z))
      (by rw [inf_eq_left.mpr hRM]; exact c.conf.R_ne_bot c.setting))
  exact c.le_of_section_three hL613 hp3 h2401 (Or.inr hrk2) (hH.trans inf_le_right)
    (hH.trans hNM) hs hzH hzN h3

end P622KxCfg

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
