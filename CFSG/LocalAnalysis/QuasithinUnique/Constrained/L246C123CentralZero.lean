module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C123CentralZeroAbs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C123Setup

public section

namespace CFSG.QuasithinUnique.L246.C123

open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem blockZ_eq_bot_of_isExcA7Block
    {L : Subgroup G} (hL : IsExcA7Block L) :
    blockZ L = ⊥ := by
  obtain ⟨hsh, ⟨α, hα, hαker⟩, hidx⟩ := hL
  have hcomm : ∀ a b : ↥(blockU L), a * b = b * a := fun a b =>
    Subtype.ext (C1.blockU_comm hsh a a.2 b (C1.blockU_le_blockQ hsh b.2))
  let _ : CommGroup ↥(blockU L) := { (inferInstance : Group ↥(blockU L)) with mul_comm := hcomm }
  have hLN : L ≤ Subgroup.normalizer (blockU L : Set G) := C1.le_normalizer_blockU L
  let act : ↥L →* MulAut ↥(blockU L) := (conjAct (blockU L)).comp (Subgroup.inclusion hLN)
  have hact : ∀ (g : ↥L) (u : ↥(blockU L)),
      ((act g u : ↥(blockU L)) : G) = (g : G) * (u : G) * (g : G)⁻¹ := fun g u =>
    coe_conjAct (Subgroup.inclusion hLN g) u
  have hV2 : ∀ v : ↥(blockU L), v ^ 2 = 1 := fun v =>
    Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact C1.blockU_sq hsh v v.2)
  have hker : ∀ q : ↥L, α q = 1 → act q = 1 := by
    intro q hq
    have hqQ : (q : G) ∈ blockQ L := by
      have h1 : q ∈ α.ker := hq
      rw [hαker] at h1
      exact ⟨q, h1, rfl⟩
    refine MulEquiv.ext fun u => Subtype.ext ?_
    rw [hact, MulAut.one_apply]
    have h2 : (q : G) * (u : G) = (u : G) * (q : G) :=
      (Subgroup.mem_centralizer_iff.1 (hsh.2.2.1.1 u.2).2 q hqQ)
    rw [h2, mul_inv_cancel_right]
  have hZfix : ∀ g : ↥L, ∀ z ∈ (blockZ L).subgroupOf (blockU L), act g z = z := by
    intro g z hz
    have hz' : (z : G) ∈ Subgroup.centralizer (L : Set G) := (Subgroup.mem_subgroupOf.1 hz).2
    refine Subtype.ext ?_
    rw [hact]
    have h2 : (g : G) * (z : G) = (z : G) * (g : G) := Subgroup.mem_centralizer_iff.1 hz' g g.2
    rw [h2, mul_inv_cancel_right]
  have hcard : Nat.card ↥(blockU L) = 16 * Nat.card ↥((blockZ L).subgroupOf (blockU L)) := by
    have h := ((blockZ L).subgroupOf (blockU L)).index_mul_card
    rw [hidx] at h
    rw [← h]
    norm_num
  have hgen : Subgroup.closure {x : ↥(blockU L) |
      ∃ (g : ↥L) (v : ↥(blockU L)), x = act g v * v⁻¹} = ⊤ := by
    set S : Subgroup ↥(blockU L) := Subgroup.closure {x : ↥(blockU L) |
      ∃ (g : ↥L) (v : ↥(blockU L)), x = act g v * v⁻¹} with hS
    rw [eq_top_iff]
    intro u _
    have hu : (u : G) ∈ ⁅blockU L, L⁆ := by
      rw [C1.commutator_blockU hsh]
      exact u.2
    rw [Subgroup.commutator_def] at hu
    have key : Subgroup.closure {g : G | ∃ g₁ ∈ blockU L, ∃ g₂ ∈ L, ⁅g₁, g₂⁆ = g} ≤
        S.map (blockU L).subtype := by
      rw [Subgroup.closure_le]
      rintro _ ⟨g₁, hg₁, g₂, hg₂, rfl⟩
      refine ⟨(act ⟨g₂, hg₂⟩ ⟨g₁, hg₁⟩ * (⟨g₁, hg₁⟩ : ↥(blockU L))⁻¹)⁻¹,
        S.inv_mem (Subgroup.subset_closure ⟨⟨g₂, hg₂⟩, ⟨g₁, hg₁⟩, rfl⟩), ?_⟩
      show (((act ⟨g₂, hg₂⟩ ⟨g₁, hg₁⟩ * (⟨g₁, hg₁⟩ : ↥(blockU L))⁻¹)⁻¹ : ↥(blockU L)) : G) = _
      rw [Subgroup.coe_inv, Subgroup.coe_mul, hact, Subgroup.coe_inv, commutatorElement_def]
      group
    obtain ⟨s, hs, hsu⟩ := key hu
    have hsu' : s = u := Subtype.ext hsu
    rwa [hsu'] at hs
  have hbot := central_zero_abstract (V := ↥(blockU L)) hV2 (Λ := ↥L) act α hα hker
    ((blockZ L).subgroupOf (blockU L)) hZfix hcard hgen
  rw [eq_bot_iff]
  intro z hz
  have h1 : (⟨z, hz.1⟩ : ↥(blockU L)) ∈ (blockZ L).subgroupOf (blockU L) :=
    Subgroup.mem_subgroupOf.2 hz
  rw [hbot, Subgroup.mem_bot] at h1
  have h2 : z = 1 := congrArg Subtype.val h1
  rw [h2]
  exact Subgroup.one_mem _

end CFSG.QuasithinUnique.L246.C123
