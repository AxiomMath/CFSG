module

public import CFSG.GH74.GLS.Stage1.Thm4.Conj
public import CFSG.GH74.GLS.Stage2.Local.Defs

public section

namespace CFSG.GH74.GLS.Stage1.Thm4

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5
open scoped commutatorElement

structure Ctx98 (G : Type) [Group G] [Finite G] (Lh : Type) [Group Lh] (z t : G) (S K : Subgroup G) :
    Prop where
  std : Std9 G Lh z t S K
  r1 : RigidSet Lh z = {K}
  q1 : Qof S K = zpowers z

namespace Ctx98

variable {G : Type} [Group G] [Finite G] {Lh : Type} [Group Lh] {z t : G} {S K : Subgroup G}
  (h : Ctx98 G Lh z t S K)

include h

theorem K_le : K ≤ Cz z := h.std.K_rigid.1.1.2.2.1

theorem S_le : S ≤ Cz z := h.std.sylow.le

theorem z_mem : z ∈ K := h.std.z_mem

theorem z_comm {k : G} (hk : k ∈ K) : k * z = z * k :=
  Subgroup.mem_centralizer_singleton_iff.1 (h.K_le hk)

theorem cmap_eq {c : G} (hc : c ∈ Cz z) : cmap c K = K := by
  have hK : K ∈ RigidSet Lh z := h.std.K_rigid
  have := (cmap_mem_rigidSet_iff (Lh := Lh) hc).2 hK
  rw [h.r1] at this
  exact this

theorem mem_normalizer {c : G} (hc : c ∈ Cz z) : c ∈ normalizer (K : Set G) := by
  refine Subgroup.mem_normalizer_iff.2 fun x => ?_
  have h1 := h.cmap_eq (inv_mem hc)
  have : x ∈ cmap c⁻¹ K ↔ x ∈ K := by rw [h1]
  rw [mem_cmap] at this
  simpa using this.symm

theorem pPrimeCoreOf_conj {c : G} (hc : c ∈ Cz z) {x : G} (hx : x ∈ pPrimeCoreOf 2 K) :
    c * x * c⁻¹ ∈ pPrimeCoreOf 2 K := by
  have h1 := pPrimeCoreOf_cmap c K
  rw [h.cmap_eq hc] at h1
  rw [h1]
  exact Subgroup.mem_map_of_mem _ hx

theorem pPrimeCoreOf_le_Oz : pPrimeCoreOf 2 K ≤ Oz z := by
  have hKle : pPrimeCoreOf 2 K ≤ Cz z := (Subgroup.map_subtype_le _).trans h.K_le
  have hnorm : ((pPrimeCoreOf 2 K).subgroupOf (Cz z)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    exact h.pPrimeCoreOf_conj g.2 hn
  have hcop : Nat.Coprime 2 (Nat.card ((pPrimeCoreOf 2 K).subgroupOf (Cz z))) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKle).toEquiv]
    unfold pPrimeCoreOf
    rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact pPrimeCore_coprime_card
  have hle : (pPrimeCoreOf 2 K).subgroupOf (Cz z) ≤ pPrimeCore 2 ↥(Cz z) := le_sSup ⟨hnorm, hcop⟩
  intro x hx
  exact ⟨⟨x, hKle hx⟩, hle hx, rfl⟩

end Ctx98

end CFSG.GH74.GLS.Stage1.Thm4
