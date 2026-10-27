module

public import CFSG.GH74.GLS.Bg.Pu5.L299T
public import CFSG.GH74.E2.TermLeaves
public import CFSG.GH74.GLS.Bg.Pu5.L294

public section

namespace CFSG.GH74.GLS.Bg.Pu5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.ABGLocalTools CFSG.GH74.GLS.Bg.Iii2 CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec6

variable {G : Type} [Group G] [Finite G] {z t : G} {S : Subgroup G}

theorem Cfg.z_mul_self (hC : Cfg G z t S) : z * z = 1 := mul_self_eq_one_of_orderOf_eq_two hC.hz

theorem Cfg.t_mul_self (hC : Cfg G z t S) : t * t = 1 := mul_self_eq_one_of_orderOf_eq_two hC.t_orderOf

theorem Cfg.t_ne_z (hC : Cfg G z t S) : t ≠ z := fun h => hC.tZ (h ▸ hC.z_mem_zStar)

theorem Cfg.z_mem_cSec (h44 : II4_44) (hquat : II4_4_quat) (hC : Cfg G z t S) {K : Subgroup G}
    (hK : IsRigidRankOneComp z K) : z ∈ cSec K :=
  mem_cSec_of_mem_zStar h44 hquat hC.simple hC.gen4 hC.z_mem_zStar
    (exists_two_pow_eq_one_of_orderOf hC.hz) hK

theorem Cfg.z_mem_Q (h44 : II4_44) (hquat : II4_4_quat) (hC : Cfg G z t S) {K : Subgroup G}
    (hK : IsRigidRankOneComp z K) : z ∈ S ⊓ cSec K :=
  ⟨hC.z_mem_S, hC.z_mem_cSec h44 hquat hK⟩

theorem Q_conj (hC : Cfg G z t S) (hcard : Set.ncard {K : Subgroup G | IsRigidRankOneComp z K} = 1)
    {K : Subgroup G} (hK : IsRigidRankOneComp z K) {s : G} (hs : s ∈ S) {q : G}
    (hq : q ∈ S ⊓ cSec K) : s * q * s⁻¹ ∈ S ⊓ cSec K :=
  ⟨S.mul_mem (S.mul_mem hs hq.1) (S.inv_mem hs),
    cSec_conj K (mem_normalizer_of_ncard_one hcard hK (hC.sylow.le hs)) hq.2⟩

theorem eq_of_commuting_involutions (h296 : L296) (hC : Cfg G z t S) {K : Subgroup G}
    (hK : IsRigidRankOneComp z K) {a b : G}
    (ha : a ∈ centralizer ({z, t} : Set G) ⊓ cSec K) (hb : b ∈ centralizer ({z, t} : Set G) ⊓ cSec K)
    (ha2 : orderOf a = 2) (hb2 : orderOf b = 2) (hab : a * b = b * a) : a = b := by
  by_contra hne
  have h2 := CFSG.GH74.E2.two_le_pRank_of_commuting_involutions
    (a := (⟨a, ha⟩ : ↥(centralizer ({z, t} : Set G) ⊓ cSec K))) (b := ⟨b, hb⟩)
    (by rw [← Subgroup.orderOf_coe]; exact ha2) (by rw [← Subgroup.orderOf_coe]; exact hb2)
    (fun h => hne (congrArg Subtype.val h)) (Subtype.ext hab)
  have := (h296 G z t S hC).2 K hK
  omega

theorem Cfg.t_not_mem_cSec (h44 : II4_44) (hquat : II4_4_quat) (h296 : L296) (hC : Cfg G z t S)
    {K : Subgroup G} (hK : IsRigidRankOneComp z K) : t ∉ cSec K := by
  intro htK
  have hD : ∀ g : G, g ∈ centralizer ({z, t} : Set G) ⊓ cSec K ↔
      (g * z = z * g ∧ g * t = t * g) ∧ g ∈ cSec K := by
    intro g
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1.symm, h2.symm⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1.symm, h2.symm⟩, h3⟩
  have hzt : z * t = t * z := (Subgroup.mem_centralizer_singleton_iff.1 hC.tC).symm
  have hzD : z ∈ centralizer ({z, t} : Set G) ⊓ cSec K :=
    (hD z).2 ⟨⟨rfl, hzt⟩, hC.z_mem_cSec h44 hquat hK⟩
  have htD : t ∈ centralizer ({z, t} : Set G) ⊓ cSec K :=
    (hD t).2 ⟨⟨hzt.symm, rfl⟩, htK⟩
  exact hC.t_ne_z (eq_of_commuting_involutions h296 hC hK htD hzD hC.t_orderOf hC.hz hzt.symm)

end CFSG.GH74.GLS.Bg.Pu5
