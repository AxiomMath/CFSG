module

public import CFSG.GH74.GLS.Bg.Pu5.ZStruct
public import CFSG.GH74.GLS.Bg.G4Statements

public section

namespace CFSG.GH74.GLS.Bg.Pu5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.ABGLocalTools CFSG.GH74.GLS.Bg.Iii2 CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec6

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem rigid_nonempty {z : G} (hz : orderOf z = 2) (hzK : z ∈ rigidProduct z) :
    {K : Subgroup G | IsRigidRankOneComp z K}.Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hb : rigidProduct z = ⊥ := by simp [rigidProduct, h]
  rw [hb, Subgroup.mem_bot] at hzK
  rw [hzK, orderOf_one] at hz
  exact absurd hz (by norm_num)

theorem mem_sylow_of_forall_comm {X T : Subgroup G} (hT : IsSylowOf 2 T X) {x : G} (hxX : x ∈ X)
    (hx2 : orderOf x = 2) (hcomm : ∀ y ∈ X, y * x = x * y) : x ∈ T := by
  obtain ⟨h, hh, hmem⟩ := exists_conj_mem_of_isSylowOf' hT hxX ⟨1, by simpa using hx2⟩
  have : h * x * h⁻¹ = x := by
    rw [hcomm h hh]
    group
  rwa [this] at hmem

theorem exists_cfg (hG : IsKProperSimple G) (hgen : Gen4 G) (h3 : 3 ≤ pRank 2 G) {z t : G}
    (hz : orderOf z = 2) (hzK : z ∈ rigidProduct z) (ht : t ∈ centralizer ({z} : Set G))
    (hconj : IsConj z t) (hnot : t ∉ zStar (rigidProduct z)) : ∃ S : Subgroup G, Cfg G z t S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 : orderOf t = 2 := by rw [← hconj.orderOf_eq, hz]
  obtain ⟨T, hT⟩ := exists_isSylowOf (G := G) 2 (centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G))
  have htT : t ∈ T := by
    refine mem_sylow_of_forall_comm hT (Subgroup.mem_inf.2 ⟨ht, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩)
      ht2 fun y hy => ?_
    exact Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hy).2
  obtain ⟨S, hS, hTS⟩ := exists_isSylowOf_ge' (K := centralizer ({z} : Set G))
    (hT.le.trans inf_le_left) hT.isPGroup
  refine ⟨S, hG, hgen, h3, hz, hzK, hconj, ht, hnot, hS, hTS htT, ?_⟩
  have hle : S ⊓ centralizer ({t} : Set G) ≤ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) :=
    inf_le_inf_right _ hS.le
  have heq : S ⊓ centralizer ({t} : Set G) = T := by
    have hTle : T ≤ S ⊓ centralizer ({t} : Set G) :=
      le_inf hTS (hT.le.trans inf_le_right)
    exact hT.eq_of_le hTle hle (hS.isPGroup.to_inf_left)
  rw [heq]
  exact hT

theorem cfg_swap (h44 : II4_44) (hquat : II4_4_quat) (h293 : L293) {z t : G} {S : Subgroup G}
    (h : Cfg G z t S) : ∃ S' : Subgroup G, Cfg G t z S' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 : orderOf t = 2 := by rw [← h.conj.orderOf_eq, h.hz]
  obtain ⟨c, hc⟩ := isConj_iff.1 h.conj
  have htK : t ∈ rigidProduct t := by
    have := mem_rigidProduct_conj h.hzK c
    rwa [hc] at this
  have htz : z * t = t * z := (Subgroup.mem_centralizer_singleton_iff.1 h.tC).symm
  have hzC : z ∈ centralizer ({t} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 htz
  have hzZ : z ∉ zStar (rigidProduct t) := by
    intro hzt
    obtain ⟨K, hK⟩ := rigid_nonempty h.hz h.hzK
    obtain ⟨L, hL⟩ := rigid_nonempty ht2 htK
    have h2 : ∃ n : ℕ, z ^ (2 ^ n) = 1 := ⟨1, by
      have := pow_orderOf_eq_one z
      rwa [h.hz, ← pow_one 2] at this⟩
    exact h293 G z t S h z h.hz (Subgroup.mem_centralizer_singleton_iff.2 rfl) hzC K hK
      (mem_cSec_of_mem_zStar h44 hquat h.simple h.gen4 (self_mem_zStar_rigidProduct h.hzK) h2 hK) L hL
      (mem_cSec_of_mem_zStar h44 hquat h.simple h.gen4 hzt h2 hL)
  have hzS : z ∈ S := mem_sylow_of_forall_comm h.sylow
    (Subgroup.mem_centralizer_singleton_iff.2 rfl) h.hz fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.1 hy
  have hzT : z ∈ S ⊓ centralizer ({t} : Set G) := ⟨hzS, hzC⟩
  obtain ⟨S', hS', hTS'⟩ := exists_isSylowOf_ge' (K := centralizer ({t} : Set G))
    (h.ext.le.trans inf_le_right) h.ext.isPGroup
  refine ⟨S', h.simple, h.gen4, h.rank, ht2, htK, h.conj.symm, hzC, hzZ, hS', hTS' hzT, ?_⟩
  have hle : S' ⊓ centralizer ({z} : Set G) ≤ centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G) :=
    inf_le_inf_right _ hS'.le
  have hext : IsSylowOf 2 (S ⊓ centralizer ({t} : Set G)) (centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G)) := by
    rw [inf_comm (centralizer ({t} : Set G))]
    exact h.ext
  have hTle : S ⊓ centralizer ({t} : Set G) ≤ S' ⊓ centralizer ({z} : Set G) := by
    refine le_inf hTS' ?_
    exact (h.ext.le.trans inf_le_left)
  have heq : S' ⊓ centralizer ({z} : Set G) = S ⊓ centralizer ({t} : Set G) :=
    hext.eq_of_le hTle hle (hS'.isPGroup.to_inf_left)
  rw [heq]
  exact hext

theorem normalizes_zStar_rigidProduct {z c : G} (hc : c ∈ centralizer ({z} : Set G)) :
    c ∈ normalizer ((zStar (rigidProduct z) : Subgroup G) : Set G) := by
  have hconj : ∀ d ∈ centralizer ({z} : Set G), ∀ x ∈ rigidProduct z, d * x * d⁻¹ ∈ rigidProduct z := by
    intro d hd x hx
    have hdz : d * z * d⁻¹ = z := by
      rw [Subgroup.mem_centralizer_singleton_iff.1 hd]
      group
    have := mem_rigidProduct_conj hx d
    rwa [hdz] at this
  have hcmap : ∀ d ∈ centralizer ({z} : Set G), cmap d (rigidProduct z) = rigidProduct z := by
    intro d hd
    ext x
    rw [mem_cmap]
    constructor
    · intro hx
      have := hconj d hd _ hx
      simpa [mul_assoc] using this
    · intro hx
      have := hconj d⁻¹ (inv_mem hd) x hx
      simpa using this
  have hmap : ∀ d ∈ centralizer ({z} : Set G), ∀ x ∈ zStar (rigidProduct z),
      d * x * d⁻¹ ∈ zStar (rigidProduct z) := by
    intro d hd x hx
    refine ⟨hconj d hd x (Subgroup.mem_inf.1 hx).1, ?_⟩
    have h1 := conj_mem_cSec_cmap (Subgroup.mem_inf.1 hx).2 d
    rwa [hcmap d hd] at h1
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact fun hx => hmap c hc x hx
  · intro hx
    have := hmap c⁻¹ (inv_mem hc) _ hx
    simpa [mul_assoc] using this

theorem b_pu5_G4_of (hquat : II4_4_quat) (h294a : L294a) (h296 : L296) (h297 : L297) (h299 : L299) :
    B_pu5_G4 := by
  intro G _ _ hG hgen h3 z hz hzK
  refine ⟨hz, fun t ht hconj hnot => ?_⟩
  obtain ⟨S, hcfg⟩ := exists_cfg hG hgen h3 hz hzK ht hconj hnot
  have hne := rigid_nonempty hz hzK
  have hle := rr_ncard_le_two hquat hG hgen hz
  have hpos : 0 < Set.ncard {K : Subgroup G | IsRigidRankOneComp z K} :=
    (Set.ncard_pos (Set.toFinite _)).2 hne
  obtain ⟨hZ, hrank⟩ := h296 G z t S hcfg
  refine ⟨by omega, ?_, hrank, h297 G z t S hcfg, (h294a G z t S hcfg).1, h299 G z t S hcfg⟩
  have hsub : zStar (rigidProduct z) ≤ centralizer ({z} : Set G) := fun x hx =>
    rigidProduct_le_cent z (Subgroup.mem_inf.1 hx).1
  have hnorm : centralizer ({z} : Set G) ≤ normalizer ((zStar (rigidProduct z) : Subgroup G) : Set G) :=
    fun c hc => normalizes_zStar_rigidProduct hc
  have := hcfg.sylow.inf_of_le_normalizer hsub hnorm
  rwa [hZ] at this

end CFSG.GH74.GLS.Bg.Pu5
