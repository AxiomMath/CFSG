module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupDefs
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.OddStandard.AltStdSec.SwapPattern

open Subgroup
open scoped Pointwise

variable {X : Type} [Group X] [Finite X] {t : X} {A K : Subgroup X}

@[expose] def conjSub (t : X) (K : Subgroup X) : Subgroup X :=
  K.map (MulAut.conj t).toMonoidHom

structure WreathK (t : X) (A K : Subgroup X) : Prop where
  comp : CFSG.IsComponent K
  ne : conjSub t K ≠ K
  layer : CFSG.layer X = K ⊔ conjSub t K
  iso : Nonempty (K ≃* alternatingGroup (Fin 8))
  diag : (A : Set X) = {g | ∃ k ∈ K, g = k * (t * k * t⁻¹)}

theorem WreathK.exists_of_wreathOutcome (h : WreathOutcome t A 8) : ∃ K, WreathK t A K := by
  obtain ⟨K, hcomp, hne, hlayer, hiso, hdiag⟩ := h
  exact ⟨K, ⟨hcomp, hne, hlayer, hiso, hdiag⟩⟩

theorem mem_conjSub_iff {K : Subgroup X} {y : X} : y ∈ conjSub t K ↔ t⁻¹ * y * t ∈ K := by
  rw [conjSub, Subgroup.mem_map]
  constructor
  · rintro ⟨k, hk, hky⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hky
    rw [← hky]
    have hk' : t⁻¹ * (t * k * t⁻¹) * t = k := by group
    rwa [hk']
  · intro hy
    refine ⟨t⁻¹ * y * t, hy, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem WreathK.comp_conjSub (hK : WreathK t A K) : CFSG.IsComponent (conjSub t K) := by
  rw [conjSub]
  exact CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj t) hK.comp

theorem WreathK.commute (hK : WreathK t A K) {a b : X} (ha : a ∈ K) (hb : b ∈ conjSub t K) :
    a * b = b * a := by
  rcases CFSG.LocalCores.distinct_components_commute hK.comp hK.comp_conjSub with h | h
  · exact (hK.ne h.symm).elim
  · have hle : K ≤ Subgroup.centralizer (conjSub t K : Set X) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
    exact (Subgroup.mem_centralizer_iff.1 (hle ha) b hb).symm

theorem WreathK.inf_eq_bot (hK : WreathK t A K) : K ⊓ conjSub t K = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  obtain ⟨hgK, hgK'⟩ := hg
  obtain ⟨e⟩ := hK.iso
  have hmem : e ⟨g, hgK⟩ ∈ Subgroup.center (alternatingGroup (Fin 8)) := by
    rw [Subgroup.mem_center_iff]
    intro a
    rw [← e.apply_symm_apply a, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hK.commute (e.symm a).2 hgK')
  have hbot : e ⟨g, hgK⟩ = 1 := by
    have h := alternatingGroup.center_eq_bot (α := Fin 8) (by simp)
    rw [h] at hmem
    simpa using hmem
  have h1 : (⟨g, hgK⟩ : K) = 1 := e.injective (by rw [hbot, map_one])
  simpa using congrArg Subtype.val h1

theorem WreathK.le_layer (hK : WreathK t A K) : K ≤ CFSG.layer X := by
  rw [hK.layer]
  exact le_sup_left

theorem WreathK.conjSub_le_layer (hK : WreathK t A K) : conjSub t K ≤ CFSG.layer X := by
  rw [hK.layer]
  exact le_sup_right

theorem WreathK.mem_layer_iff (hK : WreathK t A K) {g : X} :
    g ∈ CFSG.layer X ↔ ∃ k ∈ K, ∃ k' ∈ conjSub t K, g = k * k' := by
  have hcent : K ≤ Subgroup.centralizer (conjSub t K : Set X) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (hK.commute hk hb).symm
  have hLE : K ≤ Subgroup.normalizer (conjSub t K : Set X) :=
    hcent.trans (Subgroup.centralizer_le_normalizer _)
  have hcoe : (↑(K ⊔ conjSub t K) : Set X) = (K : Set X) * (conjSub t K : Set X) :=
    Subgroup.coe_mul_of_left_le_normalizer_right K (conjSub t K) hLE
  rw [hK.layer]
  change g ∈ (↑(K ⊔ conjSub t K) : Set X) ↔ ∃ k ∈ K, ∃ k' ∈ conjSub t K, g = k * k'
  rw [hcoe, Set.mem_mul]
  constructor
  · rintro ⟨k, hk, k', hk', hg⟩
    exact ⟨k, hk, k', hk', hg.symm⟩
  · rintro ⟨k, hk, k', hk', hg⟩
    exact ⟨k, hk, k', hk', hg.symm⟩

theorem WreathK.eq_of_mul_eq (hK : WreathK t A K) {k l k' l' : X} (hk : k ∈ K) (hl : l ∈ K)
    (hk' : k' ∈ conjSub t K) (hl' : l' ∈ conjSub t K) (h : k * k' = l * l') : k = l ∧ k' = l' := by
  have h1 : l⁻¹ * k = l' * k'⁻¹ := by
    have := congrArg (fun x => l⁻¹ * x * k'⁻¹) h
    simpa [mul_assoc] using this
  have hmem : l⁻¹ * k ∈ K ⊓ conjSub t K :=
    ⟨K.mul_mem (K.inv_mem hl) hk,
      h1 ▸ (conjSub t K).mul_mem hl' ((conjSub t K).inv_mem hk')⟩
  rw [hK.inf_eq_bot, Subgroup.mem_bot] at hmem
  have hkl : k = l := by
    rw [inv_mul_eq_one] at hmem
    exact hmem.symm
  have hkl' : k' = l' := by
    rw [hkl] at h
    exact mul_left_cancel h
  exact ⟨hkl, hkl'⟩

theorem WreathK.card_conjSub (hK : WreathK t A K) : Nat.card (conjSub t K) = Nat.card K := by
  rw [conjSub]
  exact (Nat.card_congr
    (K.equivMapOfInjective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective).toEquiv).symm

theorem WreathK.card_K (hK : WreathK t A K) : Nat.card K = 20160 := by
  obtain ⟨e⟩ := hK.iso
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  norm_num [Nat.factorial]

theorem WreathK.card_layer (hK : WreathK t A K) : Nat.card (CFSG.layer X) = 20160 * 20160 := by
  let f : K × conjSub t K → CFSG.layer X := fun x =>
    ⟨(x.1 : X) * (x.2 : X), (hK.mem_layer_iff).2 ⟨x.1, x.1.2, x.2, x.2.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      have h : (x.1 : X) * (x.2 : X) = (y.1 : X) * (y.2 : X) := Subtype.ext_iff.1 hxy
      obtain ⟨h1, h2⟩ := hK.eq_of_mul_eq x.1.2 y.1.2 x.2.2 y.2.2 h
      exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
    · intro y
      obtain ⟨k, hk, k', hk', hy⟩ := (hK.mem_layer_iff).1 y.2
      exact ⟨(⟨k, hk⟩, ⟨k', hk'⟩), Subtype.ext hy.symm⟩
  have hcard : Nat.card (K × conjSub t K) = Nat.card (CFSG.layer X) :=
    Nat.card_congr (Equiv.ofBijective f hf)
  rw [Nat.card_prod, hK.card_conjSub, hK.card_K] at hcard
  exact hcard.symm

end CFSG.OddStandard.AltStdSec.SwapPattern
