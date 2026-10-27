module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.Layer
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoUnipotentCentralizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Center
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.Point.Ctx

public section

open Subgroup
open scoped MatrixGroups

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

structure LayerLocal (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x : G) : Prop extends
    PtPoint p P M x, PtStruct p P M x

theorem lp_P_le_centralizer (hl : LayerLocal p P M x) :
    (P : Subgroup G) ≤ centralizer ({x} : Set G) := by
  intro g hg
  rw [mem_centralizer_singleton_iff]
  have h := hl.abel.is_comm.comm (⟨x, hl.point.mem⟩ : (P : Subgroup G)) ⟨g, hg⟩
  exact (congrArg Subtype.val h).symm

theorem lp_prime (hl : LayerLocal p P M x) : p.Prime := hl.loc.beta.1

theorem lp_layer_sylow [Fact p.Prime] (hG : FrobGlobal G) (hl : LayerLocal p P M x) :
    ∃ n : ℕ, 2 ≤ n ∧ Nonempty (layerOf x ≃* PSL(2, GaloisField p n)) ∧
      CFSG.ABGLocalTools.IsSylowOf p (frU P x) (layerOf x) ∧
      CFSG.Open.IsElemAbelian p (frU P x) ∧ Nat.card (frU P x) = p ^ n := by
  obtain ⟨hF, n, hn, ⟨e⟩⟩ := hl.layer
  have hp : p.Prime := Fact.out
  have hp5 := hl.p5
  have hSyl : CFSG.ABGLocalTools.IsSylowOf p (frU P x) (layerOf x) := by
    have h := hl.point.sylow.inf_of_le_normalizer (layerOf_le_centralizer x)
      (centralizer_le_normalizer_layerOf x)
    rwa [inf_of_le_left (lp_P_le_centralizer hl)] at h
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

theorem lp_x_mem_Z0 (hl : LayerLocal p P M x) :
    x ∈ (P : Subgroup G) ⊓ centralizer ((layerOf x : Subgroup G) : Set G) := by
  refine ⟨hl.point.mem, mem_centralizer_iff.mpr fun l hl' => ?_⟩
  exact mem_centralizer_singleton_iff.mp (layerOf_le_centralizer x hl')

theorem lp_Z0_cyclic (hl : LayerLocal p P M x) :
    IsCyclic ((P : Subgroup G) ⊓ centralizer ((layerOf x : Subgroup G) : Set G) : Subgroup G) := by
  haveI : Fact p.Prime := ⟨lp_prime hl⟩
  refine hl.cyclic _ (le_inf ?_ inf_le_right) ?_
  · refine inf_le_left.trans ?_
    rw [centralizer_zpowers_eq]
    exact lp_P_le_centralizer hl
  · exact P.isPGroup'.to_inf_left

theorem lp_Z0_unique [Fact p.Prime] (hl : LayerLocal p P M x) {A : Subgroup G}
    (hA : A ≤ (P : Subgroup G) ⊓ centralizer ((layerOf x : Subgroup G) : Set G))
    (hAp : Nat.card A = p) : A = zpowers x := by
  have hxZ := lp_x_mem_Z0 hl
  haveI : IsCyclic ((P : Subgroup G) ⊓ centralizer ((layerOf x : Subgroup G) : Set G) :
      Subgroup G) := lp_Z0_cyclic hl
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

theorem lp_P_decomp [Fact p.Prime] (hG : FrobGlobal G) (hl : LayerLocal p P M x) {g : G}
    (hg : g ∈ (P : Subgroup G)) :
    ∃ t ∈ frU P x, ∃ z ∈ (P : Subgroup G) ⊓ centralizer ((layerOf x : Subgroup G) : Set G),
      g = t * z := by
  obtain ⟨n, hn, ⟨e⟩, hSyl, hUel, hUcard⟩ := lp_layer_sylow hG hl
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
  have hgC : g ∈ centralizer ({x} : Set G) := lp_P_le_centralizer hl hg
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

theorem lp_P_eq_sup [Fact p.Prime] (hG : FrobGlobal G) (hl : LayerLocal p P M x) :
    (P : Subgroup G) = frU P x ⊔ ((P : Subgroup G) ⊓ centralizer ((layerOf x : Subgroup G) : Set G))
      ∧ frU P x ⊓ ((P : Subgroup G) ⊓ centralizer ((layerOf x : Subgroup G) : Set G)) = ⊥ := by
  refine ⟨le_antisymm (fun g hg => ?_) (sup_le inf_le_left inf_le_left), ?_⟩
  · obtain ⟨t, ht, z, hz, rfl⟩ := lp_P_decomp hG hl hg
    exact Subgroup.mul_mem_sup ht hz
  · rw [eq_bot_iff]
    rintro y ⟨hyU, hyZ⟩
    obtain ⟨n, hn, ⟨e⟩, -⟩ := lp_layer_sylow hG hl
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

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
