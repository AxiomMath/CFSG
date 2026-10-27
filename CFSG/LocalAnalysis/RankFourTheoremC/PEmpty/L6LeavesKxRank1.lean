module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxEmb
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxCount
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG CFSG.Open Subgroup
open CFSG.Yardstones.Md0ec50421ce4 (catalogIs onLie)

variable {G : Type} [Group G] [Finite G]

theorem not_isSolvable_of_simpleSection {H N : Subgroup G} (hs : S622IsSimpleSection H N) :
    ¬ Group.IsSolvable ↥H := by
  intro hsol
  haveI : (N.subgroupOf H).Normal := hs.2.1
  haveI : IsSimpleGroup (↥H ⧸ N.subgroupOf H) := L613.isSimpleGroup_quotient_of_section hs
  haveI : Group.IsSolvable (↥H ⧸ N.subgroupOf H) := inferInstance
  exact L613.not_comm_quotient_of_section hs (IsSimpleGroup.comm_iff_isSolvable.mpr this)

namespace KxCfg

variable {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G} {T S L : Subgroup G}

theorem false_of_dihedralType (hD : KFactDihedralTypeAut) (c : KxCfg p P M x z T S L)
    (h : catalogIs ↥L (onLie IsDihedralTypeIndex)) : False := by
  have hp := c.conf.config.prime
  have hp5 : 5 ≤ p := c.conf.config.situation.p_ge
  obtain ⟨y, hy, hzy⟩ := c.exists_not_commute
  exact hzy (hD G L ⁅zpowers z, S⁆ z p h c.commutator_le c.conf.R_isPGroup c.z_mem
    (c.conf.z_le_normalizer_R (mem_zpowers z)) hp hp5 c.orderOf_z y hy)

theorem false_of_ree (hL613 : L613) (hE : KFactReeSylowTwo) (h27 : KFactReeL28)
    (hB : KFactReeBorel) (c : KxCfg p P M x z T S L) (h : catalogIs ↥L (onLie IsReeIndex)) :
    False := by
  have hp := c.conf.config.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := c.conf.config.situation.p_ge
  set R : Subgroup G := ⁅zpowers z, S⁆ with hR
  have hzR : z ∈ normalizer (R : Set G) := c.conf.z_le_normalizer_R (mem_zpowers z)
  have hRM : R ≤ M := c.conf.R_le_S.trans c.conf.S_le_M
  obtain ⟨E, hEsyl, hRE⟩ := exists_isSylowOf_ge (f := 2) c.commutator_le c.conf.R_isPGroup
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hEcard⟩ := hE G L E c.isSimple h hEsyl
  have hRcard : Nat.card R ∣ 8 := hEcard ▸ Subgroup.card_dvd_of_le hRE
  obtain ⟨hp7, hR8⟩ := eq_seven_of_not_centralizes hp5 c.orderOf_z hzR hRcard c.exists_not_commute
  have hRE' : R = E := Subgroup.eq_of_le_of_card_ge hRE (by omega)
  have hz7 : orderOf z = 7 := hp7 ▸ c.orderOf_z
  have hzE : z ∈ normalizer (E : Set G) := hRE' ▸ hzR
  obtain ⟨H, N, hHle, hs, hzH, hzN, h3⟩ := h27 G L E z h hEsyl c.z_mem hz7 hzE
  have hHL : H ≤ L := hHle.trans (sup_le inf_le_right hEsyl.le)
  have hHM : H ≤ M := hHle.trans (sup_le c.normalizer_zpowers_le (hRE' ▸ hRM))
  have hsE : GLBStronglyEmbedded 3 M :=
    c.stronglyEmbedded hL613 hHL hHM hs hzH hzN Nat.prime_three (by norm_num)
      (by omega) h3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3H : 3 ∣ Nat.card H :=
    h3.trans ((Subgroup.index_dvd_card (N.subgroupOf H)))
  obtain ⟨e, he⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) 3 h3H
  have he3 : IsPGroup 3 (zpowers (e : G)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, he, pow_one]
  obtain ⟨E₃, hE₃syl, hXE₃⟩ := exists_isSylowOf_ge (f := 3)
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
  have hE₃1 : E₃ ≠ ⊥ := fun h1 => hE₃M (by rw [h1]; exact bot_inf_eq _)
  have hNM : normalizer (E₃ : Set G) ≤ M :=
    normalizer_le_of_stronglyEmbedded_sub hsE hE₃p hE₃M le_rfl hE₃1
  obtain ⟨hsol, hmax⟩ := hB G L E₃ h hE₃syl
  have hJ1 : normalizer (E₃ : Set G) ⊓ L ≤ M ⊓ L := inf_le_inf_right L hNM
  rcases hmax (M ⊓ L) hJ1 inf_le_right with hJ | hJ
  · have hHJ : H ≤ normalizer (E₃ : Set G) ⊓ L := hJ ▸ le_inf hHM hHL
    haveI := hsol
    haveI : Group.IsSolvable ↥H := Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective hHJ)
    exact not_isSolvable_of_simpleSection hs this
  · exact c.not_le (hJ ▸ inf_le_left)

end KxCfg

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
