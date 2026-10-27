module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.Defs
import CFSG.LocalAnalysis.GLTheoremB.I2810.InducedAux

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.OmegaAux

section Descent

theorem exists_lift {G H L : Type*} [Group G] [Group H] [Group L] (f : G →* H)
    (hf : Function.Surjective f) (g : G →* L) (hg : f.ker ≤ g.ker) :
    ∃ h : H →* L, h.comp f = g :=
  ⟨_, f.liftOfRightInverse_comp (Function.surjInv hf) (Function.rightInverse_surjInv hf) ⟨g, hg⟩⟩

variable {X : Type} [Group X] {W K : Subgroup X} [W.Normal]

theorem descend {H : Type*} [Group H] (θ : ↥K →* H) (hθ : ∀ k : ↥K, (k : X) ∈ W → θ k = 1) :
    ∃ θb : ↥(bar W K) →* H, θb.comp (toBar W K) = θ := by
  have hsurj : Function.Surjective (toBar W K) := InducedAux.toBar_surjective
  have hker : (toBar W K).ker ≤ θ.ker := fun k hk =>
    hθ k (InducedAux.toBar_eq_one_iff.mp hk)
  exact exists_lift (toBar W K) hsurj θ hker

end Descent

section Quasisimple
variable {G H : Type*} [Group G] [Group H]

theorem quasisimple_quot_iso (hG : CFSG.IsQuasisimple G) [IsSimpleGroup H] (φ : G →* H)
    (hφ : Function.Surjective φ) : Nonempty ((G ⧸ Subgroup.center G) ≃* H) := by
  have hGs : IsSimpleGroup (G ⧸ Subgroup.center G) := hG.2.1
  by_cases hM : φ.ker ≤ Subgroup.center G
  · have hker : φ.ker ≤ (QuotientGroup.mk' (Subgroup.center G)).ker := by
      rw [QuotientGroup.ker_mk']; exact hM
    obtain ⟨π, hπφ⟩ := exists_lift φ hφ (QuotientGroup.mk' (Subgroup.center G)) hker
    have hπs : Function.Surjective π := by
      intro y
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) y
      exact ⟨φ g, by rw [← MonoidHom.comp_apply, hπφ]⟩
    have hπi : Function.Injective π := by
      rw [← MonoidHom.ker_eq_bot_iff]
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with h | h
      · exact h
      · exfalso
        have hsub : Subsingleton (G ⧸ Subgroup.center G) := by
          refine ⟨fun x y => ?_⟩
          obtain ⟨a, rfl⟩ := hπs x
          obtain ⟨b, rfl⟩ := hπs y
          have ha : a ∈ π.ker := h ▸ Subgroup.mem_top a
          have hb : b ∈ π.ker := h ▸ Subgroup.mem_top b
          rw [MonoidHom.mem_ker] at ha hb
          rw [ha, hb]
        exact not_subsingleton _ hsub
    exact ⟨(MulEquiv.ofBijective π ⟨hπi, hπs⟩).symm⟩
  · exfalso
    have htop : φ.ker = ⊤ :=
      InducedAux.eq_top_of_quasisimple_normal hG.1.commutator_eq_top hGs φ.ker hM
    have hsub : Subsingleton H := by
      refine ⟨fun x y => ?_⟩
      obtain ⟨a, rfl⟩ := hφ x
      obtain ⟨b, rfl⟩ := hφ y
      have ha : a ∈ φ.ker := htop ▸ Subgroup.mem_top a
      have hb : b ∈ φ.ker := htop ▸ Subgroup.mem_top b
      rw [MonoidHom.mem_ker] at ha hb
      rw [ha, hb]
    exact not_subsingleton _ hsub

end Quasisimple

section NotAlt
variable {X : Type} [Group X] {W K S : Subgroup X} [W.Normal]

theorem false_of_alt_quotient (hR : Red28 W K S) (h1 : Hyp28One W K S) {m : ℕ} (hm : 5 ≤ m)
    (φ : ↥K →* ↥(alternatingGroup (Fin m))) (hs : Function.Surjective φ)
    (hW : ∀ k : ↥K, (k : X) ∈ W → φ k = 1) : False := by
  obtain ⟨φb, hφb⟩ := descend φ hW
  have hsurj : Function.Surjective φb := by
    intro y
    obtain ⟨k, rfl⟩ := hs y
    exact ⟨toBar W K k, by rw [← MonoidHom.comp_apply, hφb]⟩
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin m)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hm)
  obtain ⟨e⟩ := quasisimple_quot_iso hR.quasi φb hsurj
  exact h1.2.1 ⟨hR.quasi, m, hm, ⟨e⟩⟩

end NotAlt

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.OmegaAux
