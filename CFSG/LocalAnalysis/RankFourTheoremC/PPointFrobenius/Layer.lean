module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.Ctx
import CFSG.LocalAnalysis.RankThreeTheoremC.LayerNormal
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoUnipotentCentralizer
import CFSG.LocalAnalysis.RankFourTheoremC.Equivalence
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Center

public section

open Subgroup
open scoped MatrixGroups

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem layerOf_le_centralizer (x : G) : layerOf x ≤ centralizer ({x} : Set G) := by
  rw [layerOf_eq]
  exact CFSG.LocalAnalysis.RankThreeTheoremC.rankThreeLayer_le _

theorem centralizer_le_normalizer_layerOf (x : G) :
    centralizer ({x} : Set G) ≤ normalizer ((layerOf x : Subgroup G) : Set G) := by
  rw [layerOf_eq]
  exact CFSG.LocalAnalysis.RankThreeTheoremC.le_normalizer_rankThreeLayer _

theorem fr_prime (hl : FrobLocal p P M x) : p.Prime := hl.loc.beta.1

theorem fr_layer_sylow [Fact p.Prime] (hG : FrobGlobal G) (hl : FrobLocal p P M x) :
    ∃ n : ℕ, 2 ≤ n ∧ Nonempty (layerOf x ≃* PSL(2, GaloisField p n)) ∧
      CFSG.ABGLocalTools.IsSylowOf p (frU P x) (layerOf x) ∧
      CFSG.Open.IsElemAbelian p (frU P x) ∧ Nat.card (frU P x) = p ^ n := by
  obtain ⟨hF, n, hn, ⟨e⟩⟩ := hl.layer
  have hp : p.Prime := Fact.out
  have hp5 := hl.p5
  have hSyl : CFSG.ABGLocalTools.IsSylowOf p (frU P x) (layerOf x) := by
    have h := hl.point.sylow.inf_of_le_normalizer (layerOf_le_centralizer x)
      (centralizer_le_normalizer_layerOf x)
    rwa [inf_of_le_left (fr_P_le_centralizer hl)] at h
  have hfac : (Nat.card (layerOf x)).factorization p = n := by
    obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow p (CFSG.AGLEmbedding.PSL2GF p n)))
    have h1 := (CFSG.AGLEmbedding.psl2GF_sylow p n (by omega) T).2
    have h2 := Sylow.card_eq_multiplicity T
    have h3 : (Nat.card (CFSG.AGLEmbedding.PSL2GF p n)).factorization p = n :=
      Nat.pow_right_injective hp.two_le (h2.symm.trans h1)
    rw [Nat.card_congr e.toEquiv]
    exact h3
  refine ⟨n, hn, ⟨e⟩, hSyl, ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩, ?_⟩
  · have h := hl.abel.is_comm.comm ⟨a, a.2.1⟩ ⟨b, b.2.1⟩
    have h2 := congrArg Subtype.val h
    exact h2
  · intro u hu
    obtain ⟨Q, hQ⟩ := hSyl
    rw [← hQ] at hu
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hu
    have hes : Function.Surjective (e : (layerOf x) →* CFSG.AGLEmbedding.PSL2GF p n) :=
      e.surjective
    set T : Sylow p (CFSG.AGLEmbedding.PSL2GF p n) := Q.mapSurjective hes with hTdef
    have hT := (CFSG.AGLEmbedding.psl2GF_sylow p n (by omega) T).1
    have hmem : e q ∈ (T : Subgroup (CFSG.AGLEmbedding.PSL2GF p n)) := by
      rw [hTdef, Sylow.coe_mapSurjective]
      exact Subgroup.mem_map.2 ⟨q, hq, rfl⟩
    have h1 : (e q) ^ p = 1 := hT.2 _ hmem
    have h2 : q ^ p = 1 := by
      apply e.injective
      rw [map_pow, h1, map_one]
    show (q : G) ^ p = 1
    rw [← Subgroup.coe_pow, h2]
    rfl
  · rw [hSyl.card_eq, hfac]

theorem fr_x_mem_Z0 (hl : FrobLocal p P M x) :
    x ∈ (P : Subgroup G) ⊓ centralizer ((layerOf x : Subgroup G) : Set G) := by
  refine ⟨hl.point.mem, mem_centralizer_iff.mpr fun l hl' => ?_⟩
  exact mem_centralizer_singleton_iff.mp (layerOf_le_centralizer x hl')

theorem fr_Z0_cyclic (hl : FrobLocal p P M x) :
    IsCyclic ((P : Subgroup G) ⊓ centralizer ((layerOf x : Subgroup G) : Set G) : Subgroup G) := by
  haveI : Fact p.Prime := ⟨fr_prime hl⟩
  refine hl.cyclic _ (le_inf ?_ inf_le_right) ?_
  · refine inf_le_left.trans ?_
    rw [centralizer_zpowers_eq]
    exact fr_P_le_centralizer hl
  · exact P.isPGroup'.to_inf_left

theorem fr_Z0_unique [Fact p.Prime] (hl : FrobLocal p P M x) {A : Subgroup G}
    (hA : A ≤ (P : Subgroup G) ⊓ centralizer ((layerOf x : Subgroup G) : Set G))
    (hAp : Nat.card A = p) : A = zpowers x := by
  have hxZ := fr_x_mem_Z0 hl
  haveI : IsCyclic ((P : Subgroup G) ⊓ centralizer ((layerOf x : Subgroup G) : Set G) :
      Subgroup G) := fr_Z0_cyclic hl
  have hxp : Nat.card (zpowers x) = p := by
    rw [Nat.card_zpowers]
    exact hl.point.elem.2.1
  have hxle : zpowers x ≤ (P : Subgroup G) ⊓ centralizer ((layerOf x : Subgroup G) : Set G) :=
    zpowers_le.mpr hxZ
  have hcard : Nat.card (A.subgroupOf ((P : Subgroup G) ⊓
        centralizer ((layerOf x : Subgroup G) : Set G))) =
      Nat.card ((zpowers x).subgroupOf ((P : Subgroup G) ⊓
        centralizer ((layerOf x : Subgroup G) : Set G))) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hxle).toEquiv, hAp, hxp]
  have heq := (IsCyclic.subgroup_eq_iff_card_eq).2 hcard
  rw [Subgroup.subgroupOf_inj, inf_of_le_left hA, inf_of_le_left hxle] at heq
  exact heq

theorem fr_P_decomp [Fact p.Prime] (hG : FrobGlobal G) (hl : FrobLocal p P M x) {g : G}
    (hg : g ∈ (P : Subgroup G)) :
    ∃ t ∈ frU P x, ∃ z ∈ (P : Subgroup G) ⊓ centralizer ((layerOf x : Subgroup G) : Set G),
      g = t * z := by
  obtain ⟨n, hn, ⟨e⟩, hSyl, hUel, hUcard⟩ := fr_layer_sylow hG hl
  have hp2 : p ≠ 2 := by have := hl.p5; omega
  obtain ⟨T, hT⟩ := hSyl
  have hes : Function.Surjective (e : (layerOf x) →* CFSG.AGLEmbedding.PSL2GF p n) :=
    e.surjective
  set U' : Sylow p (CFSG.AGLEmbedding.PSL2GF p n) := T.mapSurjective hes with hU'
  have hU'mem : ∀ u ∈ (U' : Subgroup (CFSG.AGLEmbedding.PSL2GF p n)),
      ∃ t ∈ (T : Subgroup (layerOf x)), e t = u := by
    intro u hu
    rw [hU', Sylow.coe_mapSurjective] at hu
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hu
    exact ⟨t, ht, rfl⟩
  have htU : ∀ t ∈ (T : Subgroup (layerOf x)), ((t : layerOf x) : G) ∈ frU P x := fun t ht =>
    hT ▸ Subgroup.mem_map_of_mem (layerOf x).subtype ht
  have hgC : g ∈ centralizer ({x} : Set G) := fr_P_le_centralizer hl hg
  have hgN : g ∈ normalizer ((layerOf x : Subgroup G) : Set G) :=
    centralizer_le_normalizer_layerOf x hgC
  set φ : MulAut (layerOf x) := (layerOf x).normalizerMonoidHom ⟨g, hgN⟩ with hφ
  have hφapp : ∀ l : layerOf x, ((φ l : layerOf x) : G) = g * l * g⁻¹ := fun l => rfl
  set α : MulAut (CFSG.AGLEmbedding.PSL2GF p n) := MulAut.congr e φ with hα
  have hαe : ∀ k : layerOf x, α (e k) = e (φ k) := fun k => by
    simp [hα, MulAut.congr]
  have hfix : ∀ u ∈ (U' : Subgroup (CFSG.AGLEmbedding.PSL2GF p n)), α u = u := by
    intro u hu
    obtain ⟨t, ht, rfl⟩ := hU'mem u hu
    rw [hαe]
    congr 1
    refine Subtype.ext ?_
    rw [hφapp]
    have hcomm := congrArg Subtype.val
      (hl.abel.is_comm.comm (⟨g, hg⟩ : (P : Subgroup G)) ⟨(t : G), (htU t ht).1⟩)
    exact mul_inv_eq_of_eq_mul hcomm
  obtain ⟨u, hu, hαu⟩ := CFSG.AGLEmbedding.kFactL2UnipotentCentralizer p n hp2 (by omega) U' α
    hfix
  obtain ⟨t, ht, rfl⟩ := hU'mem u hu
  have hconj : ∀ l ∈ layerOf x, g * l * g⁻¹ = (t : G) * l * (t : G)⁻¹ := by
    intro l hlL
    have h := hαe ⟨l, hlL⟩
    rw [hαu, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul] at h
    have h' := congrArg Subtype.val (e.injective h)
    rw [hφapp] at h'
    simpa using h'.symm
  have hz : (t : G)⁻¹ * g ∈ centralizer ((layerOf x : Subgroup G) : Set G) := by
    rw [mem_centralizer_iff]
    intro l hlL
    have h := hconj l hlL
    calc l * ((t : G)⁻¹ * g) = (t : G)⁻¹ * ((t : G) * l * (t : G)⁻¹) * g := by group
      _ = (t : G)⁻¹ * (g * l * g⁻¹) * g := by rw [← h]
      _ = (t : G)⁻¹ * g * l := by group
  refine ⟨(t : G), htU t ht, (t : G)⁻¹ * g, ⟨?_, hz⟩, by group⟩
  exact P.mul_mem ((P : Subgroup G).inv_mem (htU t ht).1) hg

theorem fr_P_eq_sup [Fact p.Prime] (hG : FrobGlobal G) (hl : FrobLocal p P M x) :
    (P : Subgroup G) = frU P x ⊔ ((P : Subgroup G) ⊓ centralizer ((layerOf x : Subgroup G) : Set G))
      ∧ frU P x ⊓ ((P : Subgroup G) ⊓ centralizer ((layerOf x : Subgroup G) : Set G)) = ⊥ := by
  refine ⟨le_antisymm (fun g hg => ?_) (sup_le inf_le_left inf_le_left), ?_⟩
  · obtain ⟨t, ht, z, hz, rfl⟩ := fr_P_decomp hG hl hg
    exact Subgroup.mul_mem_sup ht hz
  · rw [eq_bot_iff]
    rintro y ⟨hyU, hyZ⟩
    obtain ⟨n, hn, ⟨e⟩, -⟩ := fr_layer_sylow hG hl
    have hyL : y ∈ layerOf x := hyU.2
    have hc : (⟨y, hyL⟩ : layerOf x) ∈ Subgroup.center (layerOf x) := by
      rw [Subgroup.mem_center_iff]
      intro l
      exact Subtype.ext ((mem_centralizer_iff.mp hyZ.2 l l.2))
    have hc' : e ⟨y, hyL⟩ ∈ Subgroup.center (CFSG.AGLEmbedding.PSL2GF p n) := by
      rw [Subgroup.mem_center_iff]
      intro z'
      obtain ⟨l, rfl⟩ := e.surjective z'
      rw [← map_mul, ← map_mul]
      exact congrArg e (Subtype.ext ((mem_centralizer_iff.mp hyZ.2 l l.2)))
    rw [CFSG.GorensteinWalter.psl2_center_eq_bot, Subgroup.mem_bot] at hc'
    have : (⟨y, hyL⟩ : layerOf x) = 1 := e.injective (hc'.trans (map_one e).symm)
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)

theorem fr_layer_rank [Fact p.Prime] (hG : FrobGlobal G) (hl : FrobLocal p P M x) :
    ∃ n : ℕ, 3 ≤ n ∧ Nonempty (layerOf x ≃* PSL(2, GaloisField p n)) ∧
      CFSG.ABGLocalTools.IsSylowOf p (frU P x) (layerOf x) ∧
      CFSG.Open.IsElemAbelian p (frU P x) ∧ Nat.card (frU P x) = p ^ n := by
  obtain ⟨n, hn, he, hSyl, hUel, hUcard⟩ := fr_layer_sylow hG hl
  refine ⟨n, ?_, he, hSyl, hUel, hUcard⟩
  have hp : p.Prime := Fact.out
  have h4 : 4 ≤ CFSG.Open.pRank p (P : Subgroup G) :=
    CFSG.LocalAnalysis.RankFourTheoremC.four_le_pRank_sylow hl.loc.beta P
  have hxp : Nat.card (zpowers x) = p := by
    rw [Nat.card_zpowers]
    exact hl.point.elem.2.1
  have hle : CFSG.Open.pRank p (P : Subgroup G) ≤ n + 1 := by
    refine CFSG.SectionRank.pRank_le hp.one_lt fun E hEP hE => ?_
    have hdec : ∀ e : E, ∃ a : (frU P x) × (zpowers x), (e : G) = (a.1 : G) * (a.2 : G) := by
      intro e
      obtain ⟨t, ht, z, hz, hez⟩ := fr_P_decomp hG hl (hEP e.2)
      have hcomm : t * z = z * t := by
        have := congrArg Subtype.val (hl.abel.is_comm.comm (⟨t, ht.1⟩ : (P : Subgroup G))
          ⟨z, hz.1⟩)
        exact this
      have hep : (e : G) ^ p = 1 := hE.2 _ e.2
      have htp : t ^ p = 1 := hUel.2 t ht
      have hzp : z ^ p = 1 := by
        have h1 : (t * z) ^ p = t ^ p * z ^ p := (Commute.mul_pow (show Commute t z from hcomm) p)
        rw [← hez, hep, htp, one_mul] at h1
        exact h1.symm
      have hzx : z ∈ zpowers x := by
        have hord : orderOf z ∣ p := orderOf_dvd_of_pow_eq_one hzp
        rcases (Nat.dvd_prime hp).1 hord with h1 | h1
        · rw [orderOf_eq_one_iff.mp h1]
          exact one_mem _
        · have hA : zpowers z = zpowers x := by
            refine fr_Z0_unique hl (zpowers_le.mpr hz) ?_
            rw [Nat.card_zpowers, h1]
          rw [← hA]
          exact mem_zpowers z
      exact ⟨(⟨t, ht⟩, ⟨z, hzx⟩), hez⟩
    choose ι hι using hdec
    have hinj : Function.Injective ι := fun a b hab => Subtype.ext (by rw [hι a, hι b, hab])
    have h := Nat.card_le_card_of_injective ι hinj
    rw [Nat.card_prod, hUcard, hxp] at h
    rwa [← pow_succ] at h
  omega

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
