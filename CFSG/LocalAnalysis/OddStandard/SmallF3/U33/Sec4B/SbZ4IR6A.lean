module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IZ3E
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingNormalizerBasic
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC17
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL414c
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4FA

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem z4i_isSylow_map {Qg L : Subgroup G} (hL : L = normalizer (Qg : Set G)) (P : Subgroup L)
    (hP : IsPGroup 2 P) (hmax : ∀ P'' : Subgroup L, IsPGroup 2 P'' → P ≤ P'' → P'' ≤ P)
    (hQf : S4B.z4iQf P = Qg.subgroupOf L) :
    ∃ S : Sylow 2 G, (S : Subgroup G) = P.map L.subtype := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQleL : Qg ≤ L := by rw [hL]; exact Subgroup.le_normalizer
  have hQfmap : S4B.z4iQf (P.map L.subtype) = Qg := by
    rw [S4B.z4iQf_map L.subtype L.subtype_injective P, hQf,
      Subgroup.map_subgroupOf_eq_of_le hQleL]
  refine CFSG.SeitzReduction.RankOne.exists_sylow_eq_of_normalizer_le
    (Q := P.map L.subtype) (N := L) (hP.map L.subtype) ?_ ?_
  · intro K hK hPK hKL
    have hK' : IsPGroup 2 (K.subgroupOf L) := hK.comap_subtype
    have hPK' : P ≤ K.subgroupOf L := by
      intro x hx
      rw [Subgroup.mem_subgroupOf]
      exact hPK (Subgroup.mem_map_of_mem L.subtype hx)
    have hle := hmax (K.subgroupOf L) hK' hPK'
    intro k hk
    have hk' : (⟨k, hKL hk⟩ : L) ∈ K.subgroupOf L := Subgroup.mem_subgroupOf.mpr hk
    exact Subgroup.mem_map_of_mem L.subtype (hle hk')
  · intro z hz _
    rw [hL, Subgroup.mem_normalizer_iff]
    intro x
    rw [← hQfmap]
    constructor
    · intro hx
      exact S4B.z4iQf_conj_mem (W := P.map L.subtype) hz hx
    · intro hx
      have h1 : z⁻¹ * (z * x * z⁻¹) * (z⁻¹)⁻¹ ∈ S4B.z4iQf (P.map L.subtype) :=
        S4B.z4iQf_conj_mem (W := P.map L.subtype) (inv_mem hz) hx
      convert h1 using 1
      group

variable {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

namespace Ctx4Z


private lemma isElemAbelian_zpowers_of_mul_self {a : G} (ha : a * a = 1) :
    CFSG.Open.IsElemAbelian 2 (zpowers a) := by
  have ha2 : a ^ 2 = 1 := by rwa [pow_two]
  have haz : a ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast]
    exact ha2
  refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
  · intro x y
    apply Subtype.ext
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp x.2
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp y.2
    show (x : G) * (y : G) = (y : G) * (x : G)
    rw [← hm, ← hn, ← zpow_add, ← zpow_add, add_comm]
  · intro x hx
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hx
    show (x : G) ^ 2 = 1
    rw [← hm, pow_two, ← zpow_add, show m + m = 2 * m by ring, zpow_mul a 2 m, haz, one_zpow]

theorem z4i_tG_not_cent_Y (hz : Ctx4Z t L S x₁ x₂ lam rho tau) (g : G)
    (h : ∀ y ∈ ctxYq t tau x₁ x₂ rho, y * (g * t * g⁻¹) = (g * t * g⁻¹) * y) : False := by
  set u : G := g * t * g⁻¹ with hu
  have hu2 : u * u = 1 := by
    rw [hu]
    calc (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [hz.t_mul_self]; group
  have huNotY : u ∉ ctxYq t tau x₁ x₂ rho := by
    intro huY
    refine hz.tG_Qtau g u (Subgroup.mem_sup_left (hz.Y_le_Q huY)) hu.symm
  have hcomm : ∀ y ∈ ctxYq t tau x₁ x₂ rho, y * u = u * y := fun y hy => h y hy
  have hcomm' : ∀ y ∈ ctxYq t tau x₁ x₂ rho, ∀ z ∈ zpowers u, y * z = z * y := by
    intro y hy z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (show Commute y u from hcomm y hy).zpow_right k
  let B : Subgroup G := ctxYq t tau x₁ x₂ rho ⊔ zpowers u
  have hBe : CFSG.Open.IsElemAbelian 2 B :=
    S4B.isElemAbelian_sup hz.Y_isElemAbelian (isElemAbelian_zpowers_of_mul_self hu2) hcomm'
  have hBcard : Nat.card B = 32 := by
    have hcard := S4B.card_sup_zpowers_of_commute (T := ctxYq t tau x₁ x₂ rho) (lam := u)
      (by rw [pow_two]; exact hu2) huNotY hcomm
    change Nat.card ↥(ctxYq t tau x₁ x₂ rho ⊔ zpowers u) = 32
    rw [hcard, hz.card_Y]
  have hBcent : B ≤ centralizer ({u} : Set G) := by
    change ctxYq t tau x₁ x₂ rho ⊔ zpowers u ≤ centralizer ({u} : Set G)
    refine sup_le (fun y hy => ?_) ?_
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (h y hy)
    · exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hbound : Nat.card B ≤ 16 :=
    S4B.c17_card_elemAbelian_conj_le hz.toCtx10 g (by rw [← hu]; exact hBcent) hBe
  rw [hBcard] at hbound
  omega

end Ctx4Z

end CFSG.OddStandard.SmallF3.HarrisU33
