module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K292Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.LThreeEpsCase
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292LinUniCent
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.K3Core

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K292S

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (IsLThreeEps)
open CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K292

theorem le_of_isSylowOf_of_normal {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P K N : Subgroup G} (hP : IsSylowOf p P K) (hNK : N ≤ K)
    (hKN : K ≤ normalizer (N : Set G)) (hN : IsPGroup p N) : N ≤ P :=
  inf_eq_right.1 ((hP.inf_of_le_normalizer hNK hKN).eq_of_le inf_le_right le_rfl hN).symm

variable {X : Type} [Group X] [Finite X] {L : Subgroup X} {x : X} {Px B : Subgroup X}

theorem card_le_nine (h : T29.T29Setup X L x) {E : Subgroup X} (hE : IsElemAbelian 3 E)
    (hEC : E ≤ centralizer ({x} : Set X)) : Nat.card E ≤ 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨j, hj⟩ := hE.isPGroup.exists_card_eq
  have hjle : j ≤ CFSG.Open.pRank 3 (centralizer ({x} : Set X)) :=
    T29.le_pRank_of_isElemAbelian_card Nat.prime_three hEC hE hj.ge
  rw [h.cent] at hjle
  rw [hj]
  calc 3 ^ j ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hjle
    _ = 9 := by norm_num

theorem false_of_index_three (cfg : LinUniCfgThree L x Px B) {N : Subgroup X} (hN : N.Normal)
    (hNi : N.index = 3) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := hN
  have hp : IsPGroup 3 (X ⧸ N) := IsPGroup.of_card (n := 1) (by
    show Nat.card (X ⧸ N) = 3 ^ 1
    rw [pow_one]
    exact hNi)
  have htop : N = ⊤ := cfg.perf N hp
  rw [htop, Subgroup.index_top] at hNi
  omega

theorem core_facts (hT : T29.GL83I291Three) (cfg : LinUniCfgThree L x Px B) :
    IsCyclic ↥(CFSG.pCore 3 X) ∧ (∀ y ∈ CFSG.pCore 3 X, y ^ 3 = 1 → y ∈ L) ∧
      IsLThreeEps (↥L ⧸ center ↥L) ∧ Nat.card (center ↥L) = 3 := by
  have h := cfg.setup
  haveI : L.Normal := h.normal
  obtain ⟨hcyc, hΩ, -, hconc⟩ := hT X h.catalog h.core L h.comp h.uniq h.rank x h.ord h.cent
  rcases hconc with ⟨hLε, hZ3, -, -, hfield | h9⟩ | hb
  · obtain ⟨y, hy, hyf⟩ := hfield
    obtain ⟨N, hN, hNi⟩ := T29.exists_normal_index_three_of_field h hLε hy hyf
    exact (false_of_index_three cfg hN hNi).elim
  · refine ⟨hcyc, hΩ, hLε, ?_⟩
    rcases (Nat.dvd_prime Nat.prime_three).1 hZ3 with h1 | h3
    · exfalso
      have hO := h.pCore_eq_bot (Subgroup.card_eq_one.1 h1)
      rw [hO, Subgroup.card_bot] at h9
      omega
    · exact h3
  · exfalso
    obtain ⟨e', -, -⟩ := id hb
    have hZ : center ↥L = ⊥ := T29.k3_center_eq_bot_of_psl227 h.comp.2.2.1 e'
    have hC : centralizer (L : Set X) = ⊥ := h.centralizer_eq_bot hZ
    obtain ⟨N, hN, hNi⟩ := K2.exists_index_three_normal h.normal ⟨e'⟩ hC
      (T29.index_eq_of_fieldAut_L227 hC hb)
    exact false_of_index_three cfg hN hNi

theorem centralizer_eq_pCore (cfg : LinUniCfgThree L x Px B) (hcyc : IsCyclic ↥(CFSG.pCore 3 X))
    (hΩ : ∀ y ∈ CFSG.pCore 3 X, y ^ 3 = 1 → y ∈ L) :
    centralizer (L : Set X) = CFSG.pCore 3 X := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292.centralizer_eq_pCore cfg.setup.core
    cfg.setup.comp cfg.setup.uniq hcyc hΩ

theorem plane_eq (cfg : LinUniCfgThree L x Px B) (hZ3 : Nat.card (center ↥L) = 3) :
    B = zpowers x ⊔ (center ↥L).map L.subtype ∧ Nat.card B = 9 := by
  have h := cfg.setup
  haveI : L.Normal := h.normal
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Z : Subgroup X := (center ↥L).map L.subtype with hZdef
  haveI hZn : Z.Normal := T29.normal_map_center_subtype L
  have hZcard : Nat.card Z = 3 := by
    rw [hZdef, Subgroup.card_map_of_injective L.subtype_injective, hZ3]
  have hx3 : x ^ 3 = 1 := T29.Parrott.T29Setup.pow_three h
  set C : Subgroup X := centralizer ({x} : Set X) with hC
  have hZC : Z ≤ C := fun z hz => by
    have h1 := CFSG.Quasithin.A318P.commute_of_card_three hZcard (m := x) (k := 1)
      (by rw [pow_one]; exact hx3) hz
    rw [hC, mem_centralizer_singleton_iff]
    calc z * x = x * z * x⁻¹ * x := by rw [h1]
      _ = x * z := by group
  have hxC : zpowers x ≤ C := zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl)
  have hCx : C ≤ normalizer (zpowers x : Set X) := by
    have e : C = centralizer ((zpowers x : Subgroup X) : Set X) := by
      rw [hC, zpowers_eq_closure, centralizer_closure]
    rw [e]
    exact centralizer_le_normalizer _
  have hxp : IsPGroup 3 (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.ord, pow_one])
  have hxP : zpowers x ≤ Px := le_of_isSylowOf_of_normal cfg.sylow hxC hCx hxp
  have hZp : IsPGroup 3 Z := h.center_isPGroup.map L.subtype
  have hCZ : C ≤ normalizer (Z : Set X) := by
    rw [Subgroup.normalizer_eq_top Z]
    exact le_top
  have hZP : Z ≤ Px := le_of_isSylowOf_of_normal cfg.sylow hZC hCZ hZp
  have hle : zpowers x ⊔ Z ≤ B := by
    refine sup_le (zpowers_le.2 (cfg.omega x (hxP (mem_zpowers x)) hx3))
      (fun z hz => cfg.omega z (hZP hz) ?_)
    have h1 := pow_card_eq_one' (G := ↥Z) (x := ⟨z, hz⟩)
    rw [hZcard] at h1
    exact congrArg Subtype.val h1
  have hxZ : x ∉ Z := fun hxZ => by
    have h1 := T29.Parrott.three_le_of_mem_center h (dvd_of_eq hZ3) hxZ
    rw [h.cent] at h1
    omega
  have hcard : Nat.card ↥(zpowers x ⊔ Z) = 9 := by
    rw [sup_comm, CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three Z hx3 hxZ
      (fun e he => mem_centralizer_singleton_iff.1 (hZC he)), hZcard]
  have hB9 : Nat.card B ≤ 9 := card_le_nine h cfg.elem (cfg.le.trans cfg.sylow.le)
  have heq : zpowers x ⊔ Z = B := Subgroup.eq_of_le_of_card_ge hle (by rw [hcard]; exact hB9)
  exact ⟨heq.symm, heq ▸ hcard⟩

theorem isSCp_of_card (cfg : LinUniCfgThree L x Px B) (hxB : x ∈ B) (hB9 : Nat.card B = 9) :
    CFSG.LocalAnalysis.GLTheoremB.IsSCp 3 ⊤ B := by
  refine ⟨le_top, cfg.elem, fun E _ hE hBE => ?_⟩
  have hEC : E ≤ centralizer ({x} : Set X) := fun e he =>
    mem_centralizer_singleton_iff.2 (hE.comm he (hBE hxB))
  exact (Subgroup.eq_of_le_of_card_ge hBE (by rw [hB9]; exact card_le_nine cfg.setup hE hEC)).symm

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K292S
