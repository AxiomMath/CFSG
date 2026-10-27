module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutGen

public section

namespace CFSG.AGLEmbedding.LieOut

open CFSG.RankThree.PartOne.Sec66T (fixSub)
open CFSG.SignalizerFunctorTheorem.CatalogBridge (NonLocalized)
open scoped commutatorElement

theorem genFixes_of_equiv {T : Type} [Group T] {p : ℕ} (hp5 : 5 ≤ p) (α : MulAut T)
    {G : Type*} [Group G] (Φ : ↥(fixSub α) ≃* G)
    (hgen : Subgroup.closure {g : G | g ^ 2 = 1} = ⊤)
    (hperf : ∃ V : Subgroup G, ⁅V, V⁆ = V ∧ V ≠ ⊥) (hNL : NonLocalized (fixSub α)) :
    GenFixes p α := by
  refine ⟨⟨fixSub α, hNL, fun y hy => ?_⟩, ?_⟩
  · have hmem : Φ ⟨y, hy⟩ ∈ Subgroup.closure {g : G | g ^ 2 = 1} := hgen ▸ Subgroup.mem_top _
    have key : ∀ g ∈ Subgroup.closure {g : G | g ^ 2 = 1},
        ((Φ.symm g : ↥(fixSub α)) : T) ∈
          Subgroup.closure {y : T | α y = y ∧ ¬ p ∣ orderOf y} := by
      intro g hg
      induction hg using Subgroup.closure_induction with
      | mem g hg =>
        refine Subgroup.subset_closure ⟨(Φ.symm g).2, fun hd => ?_⟩
        have h2 : ((Φ.symm g : ↥(fixSub α)) : T) ^ 2 = 1 := by
          have : (Φ.symm g) ^ 2 = 1 := by rw [← map_pow, hg, map_one]
          exact congrArg Subtype.val this
        have := (hd.trans (orderOf_dvd_of_pow_eq_one h2))
        have := Nat.le_of_dvd (by norm_num) this
        omega
      | one => simp
      | mul a b _ _ iha ihb => simpa using Subgroup.mul_mem _ iha ihb
      | inv a _ iha => simpa using Subgroup.inv_mem _ iha
    simpa using key _ hmem
  · obtain ⟨V, hV, hV0⟩ := hperf
    refine ⟨(V.map Φ.symm.toMonoidHom).map (fixSub α).subtype, ?_, ?_, ?_⟩
    · rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, hV]
    · intro hbot
      apply hV0
      have h1 := (Subgroup.map_eq_bot_iff_of_injective _ (fixSub α).subtype_injective).1 hbot
      exact (Subgroup.map_eq_bot_iff_of_injective _ Φ.symm.injective).1 h1
    · rintro _ ⟨u, -, rfl⟩
      exact u.2

theorem closure_involutions_perm (n : ℕ) :
    Subgroup.closure {g : Equiv.Perm (Fin n) | g ^ 2 = 1} = ⊤ := by
  rw [eq_top_iff, ← Equiv.Perm.closure_isSwap]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨a, b, hab, rfl⟩
  show Equiv.swap a b ^ 2 = 1
  rw [sq]
  exact Equiv.swap_mul_self a b

end CFSG.AGLEmbedding.LieOut
