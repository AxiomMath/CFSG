module

public import CFSG.GH74.GLS.Stage2.Final.L26.Core
public import CFSG.GH74.GLS.Stage2.Final.L26.G2Three
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S2Abs
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S2Comp
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SubSec31TwoAux
public import CFSG.GroupTheory.CommutingProductFixedSubgroup

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Final.Thm4 CFSG.GH74.GLS.Bg
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87 (comp_le_or_le_of_commute comp_eq_of_le_quasisimple)
open CFSG.GH74.GLS.Stage2.Final.L26 (isSolvable_of_hasSL2Model_three')

section Layer

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem isComponent_of_isPComponent_of_central {L : Subgroup X} (hL : IsPComponent 2 L)
    (hcomm : ∀ j ∈ L, ∀ r ∈ L ⊓ pPrimeCore 2 X, j * r = r * j) : IsComponent L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf : Group.IsPerfect ↥L :=
    CFSG.ComponentClassification.CatalogueBAlternating.pComponent_perfect hL
  obtain ⟨K, hK, hsub, hmap, -⟩ := hL
  refine ⟨?_, hsub⟩
  let π := QuotientGroup.mk' (pPrimeCore 2 X)
  have hmem : ∀ x : ↥L, π (x : X) ∈ K := fun x => hmap ▸ Subgroup.mem_map_of_mem π x.2
  let φ : ↥L →* ↥K := (π.comp L.subtype).codRestrict K hmem
  have hφ : Function.Surjective φ := by
    intro k
    have hk : (k : X ⧸ pPrimeCore 2 X) ∈ L.map π := hmap ▸ k.2
    obtain ⟨x, hx, hxk⟩ := hk
    exact ⟨⟨x, hx⟩, Subtype.ext hxk⟩
  have hker : φ.ker ≤ Subgroup.center ↥L := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hxN : (x : X) ∈ pPrimeCore 2 X := by
      have h1 : φ x = 1 := hx
      have h2 : π (x : X) = 1 := congrArg Subtype.val h1
      exact (QuotientGroup.eq_one_iff _).mp h2
    exact Subtype.ext (hcomm y y.2 (x : X) ⟨x.2, hxN⟩)
  exact isQuasisimple_of_perfect_central_cover φ hφ hperf hker hK.1

end Layer

section Kinds

variable {G : Type} [Group G] [Finite G]

theorem pLayerOf_eq_Em_of_central {M : Subgroup G}
    (hq : ∀ J : Subgroup G, IsPCompIn 2 M J → pPrimeCoreOf 2 J ≤ centralizer (J : Set G)) :
    pLayerOf 2 M = Em M := by
  rw [pLayerOf_eq_map, Em_eq]
  congr 1
  refine le_antisymm (sSup_le fun L hL => le_sSup ?_) layer_le_pLayer
  have hJ : IsPCompIn 2 M (L.map M.subtype) :=
    ⟨Subgroup.map_subtype_le L, by
      rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
      exact hL⟩
  have hc := hq _ hJ
  refine isComponent_of_isPComponent_of_central hL fun j hj r hr => ?_
  have hLn : L.IsSubnormal := by
    obtain ⟨K, -, hLn, -⟩ := hL
    exact hLn
  have h1 := pPrimeCoreOf_eq_inf (X := ↥M) hLn
  have h2 := pPrimeCoreOf_map_subtype (M := M) L
  have hrG : (r : G) ∈ pPrimeCoreOf 2 (L.map M.subtype) := by
    rw [h2, h1]
    exact ⟨r, hr, rfl⟩
  exact Subtype.ext (mem_centralizer_iff.1 (hc hrG) (j : G) ⟨j, hj, rfl⟩)

end Kinds

section ThreeShape

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}

theorem comp_eq_L1_of_three {r₁ : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)}
    (hsh : G2Shape z S r₁ 3 L₁ L₂) {K : Subgroup (CentralizerBar z)} (hK : IsComponent K) :
    K = L₁ := by
  obtain ⟨hr₁, hr₂, hgt₁, hprod, m₁, m₂, -, h3, -, -, -, -⟩ := hsh
  obtain ⟨-, hF⟩ := h3 rfl
  have hq₁ : IsQuasisimple ↥L₁ := (sl2_model_facts hr₁ (by omega) m₁).1
  have hFL : generalizedFitting (CentralizerBar z) ≤ LBar z := by
    rw [hF]
    exact Subgroup.map_subtype_le _
  have hKle : K ≤ L₁ ⊔ L₂ := by
    rw [hprod.1]
    exact ((le_sSup hK : K ≤ layer (CentralizerBar z)).trans le_sup_right).trans hFL
  have hsolv₂ : Group.IsSolvable ↥L₂ := isSolvable_of_hasSL2Model_three' m₂
  rcases comp_le_or_le_of_commute hprod.2.1 hK hKle with h | h
  · exact comp_eq_of_le_quasisimple hq₁ hK h
  · exfalso
    have : Group.IsSolvable ↥K :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective h)
    have : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
    have : Group.IsPerfect ↥K := hK.1.1
    exact Group.IsPerfect.not_isSolvable ↥K inferInstance

end ThreeShape

section Misc

theorem exists_conj_mem_sylow {X : Type} [Group X] [Finite X] (Q : Sylow 2 X) {x : X}
    (hx : ∃ k : ℕ, x ^ (2 ^ k) = 1) : ∃ g : X, g * x * g⁻¹ ∈ (Q : Subgroup X) := by
  have hp : IsPGroup 2 (Subgroup.zpowers x) := by
    obtain ⟨a, ha⟩ := hx
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one ha)
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  obtain ⟨S₁, hS₁⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X S₁ Q
  refine ⟨g, ?_⟩
  have hmem : g * x * g⁻¹ ∈ ((g • S₁ : Sylow 2 X) : Subgroup X) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) _ (hS₁ (Subgroup.mem_zpowers x))
  rw [hg] at hmem
  exact hmem

variable {Y : Type} [Group Y]

theorem mem_left_of_centralizes {A B : Subgroup Y} {b : ℕ} (hb : Odd b)
    (hB : HasSL2Model ↥B (fun r => r = b)) (hcomm : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x)
    (hI : Nat.card ↥(A ⊓ B) = 2) {x : Y} (hx : x ∈ A ⊔ B) (hxc : x ∈ centralizer (B : Set Y)) :
    x ∈ A := by
  obtain ⟨a₀, ha₀, b₀, hb₀, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm hx
  have hZB := (sl2_model_center_inv hb hB).1
  have hcomm' : ∀ x ∈ B, ∀ y ∈ A, x * y = y * x := fun x hx y hy => (hcomm y hy x hx).symm
  have hcb : ∀ c ∈ B, c * b₀ = b₀ * c := by
    intro c hc
    have h1 : c * (a₀ * b₀) = (a₀ * b₀) * c := mem_centralizer_iff.1 hxc c hc
    have h2 : a₀ * (c * b₀) = a₀ * (b₀ * c) := by
      calc a₀ * (c * b₀) = (a₀ * c) * b₀ := by rw [mul_assoc]
        _ = (c * a₀) * b₀ := by rw [hcomm' c hc a₀ ha₀]
        _ = c * (a₀ * b₀) := by rw [mul_assoc]
        _ = a₀ * b₀ * c := h1
        _ = a₀ * (b₀ * c) := by rw [mul_assoc]
    exact mul_left_cancel h2
  have hb_mem : b₀ ∈ A := central_mem_of_card_inf hcomm' hZB (by rwa [inf_comm]) hb₀ hcb
  exact mul_mem ha₀ hb_mem

end Misc

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S2
