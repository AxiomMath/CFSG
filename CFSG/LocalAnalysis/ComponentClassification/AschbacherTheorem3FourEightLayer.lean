module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3FourEightGoldschmidt
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3FourEightDiagonal

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3.FourEight

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.Open
open CFSG.SignalizerFunctor.Helpers
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]
variable {G T S Q H : Subgroup X} {g y : X}

namespace ElemCtx

theorem eq_bot_of_perfect (c : ElemCtx G T S Q H g y) {N : Subgroup X} (hNG : N ≤ G)
    (hN : G ⊔ T ≤ Subgroup.normalizer (N : Set X)) (hne : N ≠ G) (hperf : ⁅N, N⁆ = N)
    (hsol : ∀ D ≤ N, N ≤ Subgroup.normalizer (D : Set X) → IsPGroup 2 D → ⁅D, N⁆ = ⊥) :
    N = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := c.sylowFrame
  have hW := c.le_normalizer_of_normal hNG hN hne
  set W₁ := relativeWeakClosure N T (S ⊓ (N ⊔ T)) with hW₁def
  have hTW₁ : T ≤ W₁ := subgroup_le_relative_weak_closure _ _ _ (le_inf h.le le_sup_right)
  have hW₁S : W₁ ≤ S ⊓ (N ⊔ T) := relative_weak_closure_le _ _ _
  have hND : N ≤ Subgroup.normalizer ((W₁ ⊓ N : Subgroup X) : Set X) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hW hx, Subgroup.le_normalizer hx⟩
  have hD2 : IsPGroup 2 (W₁ ⊓ N : Subgroup X) :=
    h.sylow.isPGroup.to_le (inf_le_left.trans (hW₁S.trans inf_le_left))
  have hDc := hsol _ inf_le_right hND hD2
  have hTN : ⁅T, N⁆ ≤ W₁ ⊓ N := by
    rw [Subgroup.commutator_le]
    intro t ht n hn
    rw [commutatorElement_def]
    refine ⟨?_, ?_⟩
    · have h1 := (Subgroup.mem_normalizer_iff.mp (hW hn) t⁻¹).mp (W₁.inv_mem (hTW₁ ht))
      have h2 := W₁.mul_mem (hTW₁ ht) h1
      simpa [mul_assoc] using h2
    · have h1 := (Subgroup.mem_normalizer_iff.mp (hN (Subgroup.mem_sup_right ht)) n).mp hn
      exact N.mul_mem h1 (N.inv_mem hn)
  have h1 : ⁅⁅T, N⁆, N⁆ = ⊥ := le_bot_iff.mp ((Subgroup.commutator_mono hTN le_rfl).trans hDc.le)
  have h2 : ⁅⁅N, T⁆, N⁆ = ⊥ := by rw [Subgroup.commutator_comm N T]; exact h1
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h2 h1
  rw [hperf, Subgroup.commutator_comm] at h3
  have hTC : T ≤ Subgroup.centralizer (N : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3
  have hGC := c.le_centralizer_of_normal hN hTC
  rw [← hperf]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hNG.trans hGC)

theorem commutator_eq_bot_of_isQuasisimple {K D : Subgroup X} (hq : CFSG.Open.IsQuasisimple K)
    (hDK : D ≤ K) (hKD : K ≤ Subgroup.normalizer (D : Set X)) (hD : IsPGroup 2 D) :
    ⁅D, K⁆ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases central_or_eq_of_normal hq hDK hKD with h | h
  · rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (h d hd k hk).symm
  · exfalso
    rw [h] at hD
    exact CFSG.GorensteinWalter.not_isNilpotent_of_isQuasisimple K (isQuasisimple_gw hq)
      hD.isNilpotent

theorem isQuasisimple_G (c : ElemCtx G T S Q H g y) (hin : Theorem48Inputs) :
    CFSG.Open.IsQuasisimple G ∧ goldschmidtSimpleType (G ⧸ Subgroup.center G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨L, hLG, hLN, hZL, ho1, ho2, ho3⟩ := c.goldschmidt_L hin
  have hEchar : (goldschmidtLayer L).Characteristic := by
    rw [goldschmidtLayer_eq_layer]
    exact CFSG.LocalCores.layer_characteristic
  set E := (goldschmidtLayer L).map L.subtype with hEdef
  have hEL : E ≤ L := Subgroup.map_subtype_le _
  have hEN : G ⊔ T ≤ Subgroup.normalizer (E : Set X) := fun x hx =>
    mem_normalizer_map_of_characteristic (goldschmidtLayer L) (hLN hx)
  have hE : goldschmidtLayer L ≠ ⊥ := by
    intro hE
    rw [hE, sup_bot_eq] at ho1
    rw [ho1, top_sup_eq] at ho2
    have hLZ : L ≤ (T ⊔ rightConjugate T g) ⊓ G := fun x hx => by
      have : (⟨x, hx⟩ : L) ∈ ((T ⊔ rightConjugate T g) ⊓ G).subgroupOf L :=
        ho2 ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp this
    have heq : L = (T ⊔ rightConjugate T g) ⊓ G := le_antisymm hLZ hZL
    exact c.false_of_normal_Z (heq ▸ (le_sup_left.trans hLN))
  have hEperf : ⁅E, E⁆ = E := by
    have h1 := congrArg (Subgroup.map L.subtype) (CFSG.LocalCores.layer_perfect (G := L))
    rwa [Subgroup.map_commutator, ← goldschmidtLayer_eq_layer] at h1
  have hEsol : ∀ D ≤ E, E ≤ Subgroup.normalizer (D : Set X) → IsPGroup 2 D → ⁅D, E⁆ = ⊥ := by
    intro D hDE hED hD2
    have hDL : D ≤ L := hDE.trans hEL
    have hD2' : IsPGroup 2 (D.subgroupOf L) :=
      hD2.of_equiv (Subgroup.subgroupOfEquivOfLe hDL).symm
    have hsol : Group.IsSolvable (D.subgroupOf L) := by
      have := hD2'.isNilpotent
      infer_instance
    have hle : D.subgroupOf L ≤ goldschmidtLayer L := by
      intro x hx
      obtain ⟨y, hy, hyx⟩ := hDE (Subgroup.mem_subgroupOf.mp hx)
      rwa [← Subtype.ext hyx]
    have hsub : (D.subgroupOf L).IsSubnormal := by
      refine Subgroup.IsSubnormal.step _ (goldschmidtLayer L) hle
        (Subgroup.normal_of_characteristic _).isSubnormal ?_
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
      intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro d
      have hxE : (x : X) ∈ E := ⟨x, hx, rfl⟩
      have h1 := Subgroup.mem_normalizer_iff.mp (hED hxE) (d : X)
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      simpa using h1
    have h := (CFSG.LocalCores.component_solvable_centralizer hsol hsub).2
    rw [← goldschmidtLayer_eq_layer] at h
    have h1 := congrArg (Subgroup.map L.subtype) h
    rw [Subgroup.map_commutator, Subgroup.map_bot, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hDL] at h1
    rw [Subgroup.commutator_comm]
    exact h1
  by_cases hEG : E = G
  ·
    have hLeq : L = G := le_antisymm hLG (hEG ▸ hEL)
    have hlayer : goldschmidtLayer L = ⊤ := by
      apply Subgroup.map_injective L.subtype_injective
      rw [← hEdef, hEG, map_subtype_top, hLeq]
    obtain ⟨K₀, hK₀⟩ : ∃ K₀ : Subgroup L, IsComponentOf K₀ ⊤ := by
      by_contra h
      simp only [not_exists] at h
      exact hE (sSup_eq_bot.mpr fun K hK => absurd hK (h K))
    have hK₀n : K₀.Normal := CFSG.LocalCores.component_normal_of_layer_eq_top
      (by rw [← goldschmidtLayer_eq_layer]; exact hlayer) ((CFSG.isComponent_iff_open K₀).mpr hK₀)
    set K := K₀.map L.subtype with hKdef
    have hKG : K ≤ G := (Subgroup.map_subtype_le _).trans hLG
    have hGK : G ≤ Subgroup.normalizer (K : Set X) := by
      intro x hx
      have hxL : x ∈ L := hLeq ▸ hx
      have key : ∀ l ∈ L, ∀ k ∈ K, l * k * l⁻¹ ∈ K := by
        rintro l hl _ ⟨k, hk, rfl⟩
        exact ⟨⟨l, hl⟩ * k * ⟨l, hl⟩⁻¹, hK₀n.conj_mem k hk _, by simp⟩
      exact mem_normalizer_of_conj_le (key x hxL)
        (by simpa using key x⁻¹ (L.inv_mem hxL))
    have hq : CFSG.Open.IsQuasisimple K :=
      isQuasisimple_of_equiv (K₀.equivMapOfInjective _ L.subtype_injective) hK₀.2.2
    by_cases hT : T ≤ Subgroup.normalizer (K : Set X)
    · have hKeq : K = G := by
        by_contra hne
        exact ne_bot_of_isQuasisimple hq (c.eq_bot_of_perfect hKG (sup_le hGK hT) hne
          (commutator_eq_self_of_isQuasisimple hq)
          (fun D hDK hKD hD => commutator_eq_bot_of_isQuasisimple hq hDK hKD hD))
      set e : K₀ ≃* G := (K₀.equivMapOfInjective _ L.subtype_injective).trans
        (MulEquiv.subgroupCongr hKeq) with hedef
      refine ⟨isQuasisimple_of_equiv e hK₀.2.2, ?_⟩
      exact goldschmidtSimpleType_of_mulEquiv
        (QuotientGroup.congr (Subgroup.center G) (Subgroup.center K₀) e.symm
          (Subgroup.map_center_eq e.symm)) (ho3 K₀ hK₀)
    · exfalso
      obtain ⟨t, ht, htK⟩ := Set.not_subset.mp hT
      exact c.false_of_moved_component hin hKG hGK hq ht htK
  · exfalso
    have hbot := c.eq_bot_of_perfect (hEL.trans hLG) hEN hEG hEperf hEsol
    exact hE ((Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).mp hbot)

end ElemCtx

end CFSG.ComponentClassification.AschbacherTheorem3.FourEight
