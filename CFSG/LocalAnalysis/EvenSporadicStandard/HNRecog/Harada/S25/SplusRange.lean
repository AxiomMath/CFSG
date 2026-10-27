module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.S25.SplusKer

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada.S25

open Subgroup

theorem range_comp_inclusion_eq {H : Type*} [Group H] [Finite H] {z : H} {R0 : Subgroup H}
    (hzR : z ∈ R0) (hR0 : IsPGroup 2 R0)
    {ψ : ↥(centralizer ({z} : Set H)) →* Equiv.Perm (Fin 5)}
    (hker : ψ.ker = R0.subgroupOf (centralizer ({z} : Set H)))
    {Y : Subgroup H} (hY : Y ≤ centralizer ({z} : Set H)) (hperf : ⁅Y, Y⁆ = Y)
    {f : ↥Y →* alternatingGroup (Fin 5)} (hf : Function.Surjective f)
    (hfk : f.ker ≤ (zpowers z).subgroupOf Y) :
    (ψ.comp (Subgroup.inclusion hY)).range = alternatingGroup (Fin 5) := by
  let ψY : ↥Y →* Equiv.Perm (Fin 5) := ψ.comp (Subgroup.inclusion hY)
  have hcomm : _root_.commutator ↥Y = ⊤ := by
    refine le_antisymm le_top (fun y _ => ?_)
    have hmem : (y : H) ∈ (_root_.commutator ↥Y).map Y.subtype := by
      rw [Subgroup.map_subtype_commutator, hperf]
      exact y.2
    rcases Subgroup.mem_map.mp hmem with ⟨c, hc, hceq⟩
    have hcy : c = y := Subtype.ext hceq
    simpa [hcy] using hc
  have hsign : ∀ y : ↥Y, Equiv.Perm.sign (ψY y) = 1 := by
    have hle : (⊤ : Subgroup ↥Y) ≤ (Equiv.Perm.sign.comp ψY).ker := by
      rw [← hcomm]
      exact Abelianization.commutator_subset_ker _
    intro y
    exact MonoidHom.mem_ker.mp (hle (Subgroup.mem_top y))
  have hle_range : ψY.range ≤ alternatingGroup (Fin 5) := by
    intro g hg
    rcases MonoidHom.mem_range.mp hg with ⟨y, rfl⟩
    exact hsign y
  have n : ψY.ker = f.ker := ker_comp_inclusion_eq hzR hR0 hker hY hf hfk
  haveI : Nonempty f.ker := ⟨1, f.ker.one_mem⟩
  have h1 : Nat.card f.ker * Nat.card ψY.range = Nat.card ↥Y := by
    rw [← n]
    exact Subgroup.card_ker_mul_card_range ψY
  have h2 : Nat.card f.ker * Nat.card f.range = Nat.card ↥Y :=
    Subgroup.card_ker_mul_card_range f
  have hcard_range : Nat.card ψY.range = Nat.card f.range :=
    Nat.mul_left_cancel (Nat.card_pos (α := f.ker)) (h1.trans h2.symm)
  have hfrange : f.range = ⊤ := MonoidHom.range_eq_top_of_surjective f hf
  have hcard_alt_eq : Nat.card (alternatingGroup (Fin 5)) = Nat.card f.range := by
    rw [← Subgroup.card_top (G := alternatingGroup (Fin 5)), ← hfrange]
  have hcard_le : Nat.card (alternatingGroup (Fin 5)) ≤ Nat.card ψY.range := by
    rw [hcard_alt_eq, hcard_range]
  exact Subgroup.eq_of_le_of_card_ge hle_range hcard_le

end CFSG.EvenSporadicStandard.HNRecog.Harada.S25
