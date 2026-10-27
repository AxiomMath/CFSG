module

public import CFSG.Quasithin.Background.B1MoreTenD
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.QuasithinUnique

open CFSG.Quasithin CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

namespace Bridge

namespace FStarSimple

variable {S : Type} [CommGroup S] {G L : Subgroup (MulAut S)}

theorem le_G (hF : L = quasithinGenFitting G) : L ≤ G := by
  rw [hF]; exact CFSG.Quasithin.quasithinGenFitting_le G

theorem normal (hF : L = quasithinGenFitting G) : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L := by
  intro g hg l hl
  have h := CFSG.Quasithin.le_normalizer_quasithinGenFitting G hg
  rw [← hF] at h
  exact (Subgroup.mem_normalizer_iff.1 h l).1 hl

theorem cent_trivial [Finite S] (hF : L = quasithinGenFitting G) (hcen : Subgroup.center ↥L = ⊥) :
    ∀ g ∈ G, (∀ l ∈ L, g * l = l * g) → g = 1 := by
  intro g hg hc
  have h1 : g ∈ G ⊓ Subgroup.centralizer (quasithinGenFitting G : Set (MulAut S)) := by
    refine ⟨hg, Subgroup.mem_centralizer_iff.2 fun l hl => ?_⟩
    rw [← hF] at hl
    exact (hc l hl).symm
  have h2 := CFSG.Quasithin.centralizer_quasithinGenFitting_le G h1
  rw [← hF] at h2
  have h3 : (⟨g, h2⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro k
    exact Subtype.ext (hc k k.2).symm
  rw [hcen, Subgroup.mem_bot] at h3
  exact congrArg Subtype.val h3

theorem comm_eq [Finite S] (hF : L = quasithinGenFitting G) (hsimple : IsSimpleGroup ↥L)
    (hcen : Subgroup.center ↥L = ⊥) {A : Subgroup (MulAut S)} (hA : IsFFStarOffender G A) :
    ⁅L, A⁆ = L := by
  have := hsimple
  have hAG : A ≤ G := hA.1
  set N := ⁅L, A⁆ with hN
  have hNL : N ≤ L := by
    rw [hN, Subgroup.commutator_le]
    intro l hl a ha
    have h1 := normal hF a (hAG ha) l⁻¹ (L.inv_mem hl)
    have e : l * a * l⁻¹ * a⁻¹ = l * (a * l⁻¹ * a⁻¹) := by group
    show l * a * l⁻¹ * a⁻¹ ∈ L
    rw [e]
    exact L.mul_mem hl h1
  have hnorm : (N.subgroupOf L).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hn' : (n : MulAut S) ∈ ⁅A, L⁆ := by rw [Subgroup.commutator_comm]; exact hn
    have := conj_mem_commutator (H := A) (A := L) g.2 hn'
    rw [Subgroup.commutator_comm] at this
    exact this
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf L) with h | h
  · exfalso
    have hcomm : ∀ a ∈ A, ∀ l ∈ L, a * l = l * a := by
      intro a ha l hl
      have hmemN : ⁅l, a⁆ ∈ N := Subgroup.commutator_mem_commutator hl ha
      have hmemL : (⟨⁅l, a⁆, hNL hmemN⟩ : ↥L) ∈ N.subgroupOf L := hmemN
      rw [h, Subgroup.mem_bot] at hmemL
      have h1 : ⁅l, a⁆ = 1 := congrArg Subtype.val hmemL
      exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm
    exact hA.2.1 (eq_bot_iff.2 fun a ha =>
      Subgroup.mem_bot.2 (cent_trivial hF hcen a (hAG ha) (hcomm a ha)))
  · apply le_antisymm hNL
    intro l hl
    have : (⟨l, hl⟩ : ↥L) ∈ N.subgroupOf L := by rw [h]; trivial
    exact Subgroup.mem_subgroupOf.1 this

theorem le_ffJ [Finite S] (hF : L = quasithinGenFitting G) (hsimple : IsSimpleGroup ↥L)
    (hcen : Subgroup.center ↥L = ⊥) {A : Subgroup (MulAut S)} (hA : IsFFStarOffender G A) :
    L ≤ ffJ G :=
  B1Red.K_le_ffJ (le_G hF) hA (comm_eq hF hsimple hcen hA)

end FStarSimple

end Bridge

end CFSG.QuasithinUnique
