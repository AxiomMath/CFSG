
module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCZ
public import CFSG.Quasithin.Background.C1GNBlockLemmas

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def D5Data {G : Type} [Group G] (L : Subgroup G) : Prop :=
  ∃ (V Q : Subgroup G), V ≤ Q ∧ Q ≤ L ∧ IsPGroup 2 Q ∧
    L ≤ Subgroup.normalizer (Q : Set G) ∧ L ≤ Subgroup.normalizer (V : Set G) ∧
    ∃ α : ↥L →* ↥(alternatingGroup (Fin 5)), Function.Surjective α ∧
      (∀ l : ↥L, α l = 1 ↔ (l : G) ∈ Q) ∧
      ∃ β : ↥V ≃* Multiplicative ↥(evenWeight 5),
        ∀ (l : ↥L) (v w : ↥V), (w : G) = l * v * l⁻¹ →
          Multiplicative.toAdd (β w) =
            Delta5.vact ((α l : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5))
              (Multiplicative.toAdd (β v))

theorem d5Data_of_block {G : Type} [Group G] [Finite G] {L : Subgroup G} (hL : IsShort2 L)
    (h5 : IsAltType L 5) : D5Data L := by
  have hZ : blockZ L = ⊥ := AppC.blockZ_eq_bot_of_alt5 hL h5
  obtain ⟨α, hα, hαk, β, hβ, hβk, hβe⟩ := h5
  have hinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, hZ, Subgroup.bot_subgroupOf]
  refine ⟨blockU L, blockQ L, C1.blockU_le_blockQ hL, C1.blockQ_le L, C1.blockQ_isPGroup L,
    C1.le_normalizer_blockQ L, C1.le_normalizer_blockU L, α, hα, ?_,
    MulEquiv.ofBijective β ⟨hinj, hβ⟩, ?_⟩
  · intro l
    rw [← MonoidHom.mem_ker, hαk]
    exact AppC.mem_pCore_iff_mem_blockQ l
  · intro l v w hw
    apply Subtype.ext
    funext i
    exact hβe l v w hw i

theorem perfect_of_block {G : Type} [Group G] [Finite G] {L : Subgroup G} (hL : IsShort2 L)
    (h5 : IsAltType L 5) : ⁅L, L⁆ = L := by
  obtain ⟨α, hα, hαk, -⟩ := h5
  have hQ : commutator ↥(alternatingGroup (Fin 5)) = ⊤ :=
    commutator_alternatingGroup_eq_top (by simp)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← Subgroup.isPerfect_iff, Group.isPerfect_def]
  apply C1GN.isShort2_eq_top_of_sup_pCore hL (commutator ↥L)
  have hmap : (commutator ↥L).map α = ⊤ := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hα]
    exact hQ
  have h := Subgroup.comap_map_eq α (commutator ↥L)
  rw [hmap, Subgroup.comap_top, hαk] at h
  exact h.symm

theorem d5_V_ne_bot {G : Type} [Group G] {V : Subgroup G}
    (β : ↥V ≃* Multiplicative ↥(evenWeight 5)) : V ≠ ⊥ := by
  intro hV
  let x : Multiplicative ↥(evenWeight 5) := Multiplicative.ofAdd ⟨Delta5.w0, Delta5.w0_mem⟩
  have h1 : β.symm x = 1 := by
    apply Subtype.ext
    have : (β.symm x : G) ∈ (⊥ : Subgroup G) := hV ▸ (β.symm x).2
    exact Subgroup.mem_bot.1 this
  have h2 : x = 1 := by
    have := congrArg β h1
    rwa [MulEquiv.apply_symm_apply, map_one] at this
  have h3 := congrArg (fun y : Multiplicative ↥(evenWeight 5) =>
    ((Multiplicative.toAdd y : ↥(evenWeight 5)) : Fin 5 → ZMod 2) 0) h2
  revert h3
  decide +kernel

end CFSG.QuasithinUnique.A5
