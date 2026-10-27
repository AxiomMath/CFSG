module

public import CFSG.HardMathSupport.U4FF.Model
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyDisplacement
public import CFSG.LocalAnalysis.EvenBN.U4.Model.Rank
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.HardMathSupport.U4FF

open CFSG.LocalAnalysis CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.EvenBN.U4
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag CFSG.Quasithin

variable {S : Type} [CommGroup S] {n : ℕ} {L : Subgroup (MulAut S)}

theorem card_le_q4_of_elemAbelian (hL : IsU4Group n L) {E : Subgroup (MulAut S)}
    (hE : IsElemAbelian2 E) (hEL : E ≤ L) : Nat.card E ≤ (2 ^ n) ^ 4 := by
  classical
  obtain ⟨K, _, h, ⟨η⟩⟩ := exists_equiv_gramSU hL
  haveI : CharP K 2 := h.charP
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := finite_gramSU_miyamotoJ4 h
  obtain ⟨U, hU⟩ := exists_sylow_miyamotoP h
  set E₁ : Subgroup (gramSU h (miyamotoJ4 K)) := (E.subgroupOf L).map η.toMonoidHom with hE₁
  have hmem₁ : ∀ a ∈ E₁, ∃ x : L, (x : MulAut S) ∈ E ∧ η x = a := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, Subgroup.mem_subgroupOf.mp hx, rfl⟩
  have hcomm₁ : ∀ a ∈ E₁, ∀ b ∈ E₁, a * b = b * a := by
    intro a ha b hb
    obtain ⟨x, hx, rfl⟩ := hmem₁ a ha
    obtain ⟨y, hy, rfl⟩ := hmem₁ b hb
    rw [← map_mul, ← map_mul]
    exact congrArg η (Subtype.ext (hE.1 _ hx _ hy))
  have hsq₁ : ∀ a ∈ E₁, a * a = 1 := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := hmem₁ a ha
    rw [← map_mul]
    have : x * x = 1 := Subtype.ext (by simpa [sq] using hE.2 _ hx)
    rw [this, map_one]
  obtain ⟨g, hg⟩ := CFSG.QuasithinUnique.Setup.Family.exists_conj_le_sylow_two U E₁ hsq₁
  let χ : gramSU h (miyamotoJ4 K) →* GL (Fin 4) K :=
    (gramSU h (miyamotoJ4 K)).subtype.comp (MulAut.conj g⁻¹).toMonoidHom
  have hχinj : Function.Injective χ :=
    (gramSU h (miyamotoJ4 K)).subtype_injective.comp (MulAut.conj g⁻¹).injective
  set E₂ : Subgroup (GL (Fin 4) K) := E₁.map χ with hE₂
  have hE₂P : E₂ ≤ miyamotoP h := by
    rintro _ ⟨a, ha, rfl⟩
    have := hg a ha
    rw [hU, Subgroup.mem_subgroupOf] at this
    simpa [χ, MulAut.conj_apply] using this
  haveI : CFSG.IsElementaryAbelian 2 E₂ := by
    refine CFSG.IsElementaryAbelian.two_of_forall_mul_self ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hcomm₁ a ha b hb]
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_mul, hsq₁ a ha, map_one]
  have hc := (card_le_and_eq_A1_of_isElementaryAbelian h hE₂P).1
  have hcard₂ : Nat.card E₂ = Nat.card E₁ := Subgroup.card_map_of_injective hχinj
  have hcard₁ : Nat.card E₁ = Nat.card (E.subgroupOf L) :=
    Subgroup.card_map_of_injective η.injective
  have hcard : Nat.card (E.subgroupOf L) = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv
  calc Nat.card E = Nat.card E₂ := by rw [hcard₂, hcard₁, hcard]
    _ ≤ (2 ^ n) ^ 4 := hc

end CFSG.HardMathSupport.U4FF
