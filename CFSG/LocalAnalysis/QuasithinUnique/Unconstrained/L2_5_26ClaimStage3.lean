module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_26ClaimS8
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_26ClaimGamma

public section

namespace CFSG.QuasithinUnique.Claim2526

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem claim_final_contradiction (h : UniqueSetting G T M)
    (hnc : ∀ H : Subgroup G, IsGamma0 M H → ¬ CharTwo H) {L : Subgroup G}
    {φ : ↥L ≃* alternatingGroup (Fin 8)} {t i : G} (D : S8Data L φ t i)
    (hcomp : IsComponentIn L (Subgroup.centralizer ({i} : Set G))) (hT : Nat.card T = 512) :
    False := by
  obtain ⟨H1, H2, T0, hH1, hH2, hT01, hT02, hc1, hc2, hO1, hO2, hs1, hs2, hcard, hgen⟩ :=
    exists_two_locals D
  obtain ⟨S', hT0S', hS'⟩ := exists_isSylowTwoOf_of_le (le_top : T0 ≤ ⊤) hs1.isPGroup
  obtain ⟨m, -, hm⟩ := h.sylow.exists_conj hS'
  set f : G ≃* G := (MulAut.conj m).symm with hf
  have hfT : ∀ x ∈ T0, f x ∈ T := by
    intro x hx
    have hx' : x ∈ T.map (MulAut.conj m).toMonoidHom := hm ▸ hT0S' hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx'
    have : f x = y := by
      rw [hf, MulEquiv.symm_apply_eq]
      exact hyx.symm
    rw [this]
    exact hy
  have hUT : T0.map f.toMonoidHom ≤ T := by
    rintro _ ⟨x, hx, rfl⟩
    exact hfT x hx
  have hUcard : Nat.card (T0.map f.toMonoidHom) = 256 := by
    rw [Subgroup.card_map_of_injective f.injective, hcard]
  have hT2 : Nat.card T = 2 * Nat.card (T0.map f.toMonoidHom) := by rw [hT, hUcard]
  have hcomapeq : M.comap f.toMonoidHom = M.map f.symm.toMonoidHom := by
    ext x
    constructor
    · intro hx
      exact ⟨f x, hx, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  have hM'' : CharTwo (M.comap f.toMonoidHom) := by
    rw [hcomapeq]
    exact (charTwo_map_equiv_iff f.symm M).mpr h.charTwo
  have hnot : ¬ (H1.map f.toMonoidHom ≤ M ∧ H2.map f.toMonoidHom ≤ M) := by
    rintro ⟨h1, h2⟩
    have hcomap : ∀ X : Subgroup G, X.map f.toMonoidHom ≤ M → X ≤ M.comap f.toMonoidHom :=
      fun X hX => Subgroup.map_le_iff_le_comap.mp hX
    have hH0 := hgen _ (hcomap _ h1) (hcomap _ h2)
    have hL3 : 3 ∣ Nat.card L := by
      rw [Nat.card_congr φ.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
    have hsimple : IsSimpleGroup ↥L := by
      have : IsSimpleGroup (alternatingGroup (Fin 8)) :=
        alternatingGroup.isSimpleGroup (by norm_num : 5 ≤ Nat.card (Fin 8))
      exact MulEquiv.isSimpleGroup φ
    exact no_component_in_charTwo hM'' (hH0 (i_mem_H0 D)) (by rw [sq]; exact D.i_sq) hcomp
      (fun x hx => hH0 (L_le_H0 D hx)) hsimple hL3
  by_cases h1 : H1.map f.toMonoidHom ≤ M
  · have h2 : ¬ H2.map f.toMonoidHom ≤ M := fun h2 => hnot ⟨h1, h2⟩
    exact gamma_contradiction h hnc ((charTwo_map_equiv_iff f H2).mpr hc2)
      ((pCoreOf_map_equiv_ne_bot_iff 2 f H2).mpr hO2) (hs2.map_equiv f) hUT hT2 h2
  · exact gamma_contradiction h hnc ((charTwo_map_equiv_iff f H1).mpr hc1)
      ((pCoreOf_map_equiv_ne_bot_iff 2 f H1).mpr hO1) (hs1.map_equiv f) hUT hT2 h1

end CFSG.QuasithinUnique.Claim2526
