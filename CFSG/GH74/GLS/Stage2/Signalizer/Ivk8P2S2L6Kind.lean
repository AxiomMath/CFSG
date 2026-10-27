module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S2L6Gen
public import CFSG.GH74.GLS.Stage2.Local.Prop28Basic
public import CFSG.LocalAnalysis.ComponentInitial.AlternatingLocalComponents
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Defs18

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Final.Thm4 CFSG.GH74.GLS.Bg
open CFSG.LocalAnalysis.ComponentInitial (isComponent_le_centralizer_of_isPGroup)
open CFSG.GH74.GLS.Stage2.Final.L26 (WBar_normal WBar_two_pow WBar_le_generalizedFitting)

section Kinds

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}

omit [Finite G] in
theorem exists_component_of_Em_ne_bot {M : Subgroup G} (h : Em M ≠ ⊥) :
    ∃ J : Subgroup ↥M, IsComponent J := by
  refine exists_isComponent_of_layer_ne_bot (fun hb => h ?_)
  rw [Em_eq, hb, Subgroup.map_bot]

theorem WBar_le_zpowers_of_pair {q : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)}
    (hz : orderOf z = 2) (hP : Stage1Pair G z S q L₁ L₂) : WBar z ≤ barOf z (zpowers z) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK₁ : IsComponent L₁ := (show L₁ ∈ {K | IsComponent K} by
    rw [hP.comps]; exact Set.mem_insert _ _)
  have hK₂ : IsComponent L₂ := (show L₂ ∈ {K | IsComponent K} by
    rw [hP.comps]; exact Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hWp : IsPGroup 2 ↥(WBar z) := by
    rintro ⟨w, hw⟩
    obtain ⟨a, ha⟩ := WBar_two_pow z w hw
    exact ⟨a, Subtype.ext ha⟩
  have hc₁ := isComponent_le_centralizer_of_isPGroup hK₁ (WBar_normal z) hWp
  have hc₂ := isComponent_le_centralizer_of_isPGroup hK₂ (WBar_normal z) hWp
  have hZ : zBar z ∈ L₁ ⊓ L₂ := by
    refine central_le_inf hP.odd hP.odd hP.sl₁ hP.sl₂ hP.prod.2.1 hP.prod.2.2 ?_ ?_
    · rw [hP.prod.1, ← hP.fitting]
      exact zBar_mem_generalizedFitting z
    · intro y _
      exact zBar_central z y
  intro w hw
  have hwL : w ∈ L₁ ⊔ L₂ := by
    rw [hP.prod.1, ← hP.fitting]
    exact WBar_le_generalizedFitting z hw
  have hwc : ∀ y ∈ L₁ ⊔ L₂, y * w = w * y := by
    intro y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hP.prod.2.1 hy
    have h1 : w * a = a * w := mem_centralizer_iff.1 (hc₁ ha) w hw
    have h2 : w * b = b * w := mem_centralizer_iff.1 (hc₂ hb) w hw
    calc a * b * w = a * (b * w) := by rw [mul_assoc]
      _ = a * (w * b) := by rw [h2]
      _ = (a * w) * b := by rw [mul_assoc]
      _ = (w * a) * b := by rw [h1]
      _ = w * (a * b) := by rw [mul_assoc]
  have hwI : w ∈ L₁ ⊓ L₂ :=
    central_le_inf hP.odd hP.odd hP.sl₁ hP.sl₂ hP.prod.2.1 hP.prod.2.2 hwL hwc
  have hwz : w ∈ zpowers (zBar z) :=
    mem_zpowers_of_card_two hP.prod.2.2 hZ (zBar_ne_one hz) hwI
  exact (zpowers_le.2 (zBar_mem_barOf z)) hwz

theorem WBar_le_zpowers_of_cover {n : ℕ} (hz : orderOf z = 2)
    (h : IsDoubleCoverOfAlt (CentralizerBar z) n) : WBar z ≤ barOf z (zpowers z) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htop : IsComponent (⊤ : Subgroup (CentralizerBar z)) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm h.1,
      Subgroup.IsSubnormal.top⟩
  have hWp : IsPGroup 2 ↥(WBar z) := by
    rintro ⟨w, hw⟩
    obtain ⟨a, ha⟩ := WBar_two_pow z w hw
    exact ⟨a, Subtype.ext ha⟩
  have hWc := isComponent_le_centralizer_of_isPGroup htop (WBar_normal z) hWp
  intro w hw
  have hwc : w ∈ center (CentralizerBar z) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact (mem_centralizer_iff.1 (hWc (Subgroup.mem_top g)) w hw).symm
  have hzc : zBar z ∈ center (CentralizerBar z) := by
    rw [Subgroup.mem_center_iff]
    exact zBar_central z
  exact (zpowers_le.2 (zBar_mem_barOf z)) (mem_zpowers_of_card_two h.2.1 hzc (zBar_ne_one hz) hwc)

theorem images_of_pair {q : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)}
    (hP : Stage1Pair G z S q L₁ L₂) (hE : ∃ J : Subgroup ↥(Cen z), IsComponent J) :
    ∀ K : Subgroup (CentralizerBar z), IsComponent K →
      ∃ J : Subgroup ↥(Cen z), IsComponent J ∧ J.map (toBar z) = K := by
  obtain ⟨J, hJ⟩ := hE
  have hK₀ : IsComponent (J.map (toBar z)) := isComponent_map_pPrimeCore hJ
  obtain ⟨s, -, ht, h12, h21⟩ := hP.swap
  have hJ' : IsComponent (conjugate J ⟨s, ht⟩) :=
    CFSG.LocalCores.isComponent_map_mulEquiv _ hJ
  have himg : (conjugate J ⟨s, ht⟩).map (toBar z) =
      conjugate (J.map (toBar z)) (toBar z ⟨s, ht⟩) :=
    CFSG.ComponentClassification.UnbalancedLayer.map_conjugate _ _ _
  intro K hK
  have hKm : K = L₁ ∨ K = L₂ := by
    have : K ∈ ({L₁, L₂} : Set (Subgroup (CentralizerBar z))) := hP.comps ▸ hK
    exact this
  have hK₀m : J.map (toBar z) = L₁ ∨ J.map (toBar z) = L₂ := by
    have : J.map (toBar z) ∈ ({L₁, L₂} : Set (Subgroup (CentralizerBar z))) := hP.comps ▸ hK₀
    exact this
  rcases hK₀m with h1 | h2
  · rcases hKm with hk | hk
    · exact ⟨J, hJ, h1.trans hk.symm⟩
    · exact ⟨_, hJ', himg.trans (by rw [h1, h12, hk])⟩
  · rcases hKm with hk | hk
    · exact ⟨_, hJ', himg.trans (by rw [h2, h21, hk])⟩
    · exact ⟨J, hJ, h2.trans hk.symm⟩

theorem images_of_cover {n : ℕ} (h : IsDoubleCoverOfAlt (CentralizerBar z) n)
    (hE : ∃ J : Subgroup ↥(Cen z), IsComponent J) :
    ∀ K : Subgroup (CentralizerBar z), IsComponent K →
      ∃ J : Subgroup ↥(Cen z), IsComponent J ∧ J.map (toBar z) = K := by
  obtain ⟨J, hJ⟩ := hE
  have hK₀ : IsComponent (J.map (toBar z)) := isComponent_map_pPrimeCore hJ
  intro K hK
  refine ⟨J, hJ, ?_⟩
  rw [Prop28.isComponent_eq_top_of_isQuasisimple h.1 hK₀,
    Prop28.isComponent_eq_top_of_isQuasisimple h.1 hK]

theorem no_component_of_m12 (h : Stage1M12 G z S) (K : Subgroup (CentralizerBar z)) :
    ¬ IsComponent K := by
  intro hK
  obtain ⟨A, -, -, -, hF, -, -⟩ := h.L_shape
  have hKF : K ≤ generalizedFitting (CentralizerBar z) :=
    ((le_sSup hK : K ≤ layer (CentralizerBar z))).trans le_sup_right
  rw [hF] at hKF
  have hKp : IsPGroup 2 ↥K := by
    rintro ⟨x, hx⟩
    obtain ⟨a, ha⟩ := WBar_two_pow z x (hKF hx)
    exact ⟨a, Subtype.ext ha⟩
  have hsolvK : Group.IsSolvable ↥K := by
    have : Group.IsNilpotent ↥K := hKp.isNilpotent
    infer_instance
  have : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
  have : Group.IsPerfect ↥K := hK.1.1
  exact Group.IsPerfect.not_isSolvable ↥K hsolvK

theorem false_of_pair {q : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)} (ctx : Stage2Ctx G z k S)
    (hF : Fail17 G z k S (Cen z)) (hE : Em (Cen z) ≠ ⊥) (hP : Stage1Pair G z S q L₁ L₂) :
    False :=
  hF.fail (thm4Concl_of_images ctx.central.1 ctx.sylow
    (images_of_pair hP (exists_component_of_Em_ne_bot hE))
    (WBar_le_zpowers_of_pair ctx.central.1 hP))

theorem false_of_cover {n : ℕ} (ctx : Stage2Ctx G z k S) (hF : Fail17 G z k S (Cen z))
    (hE : Em (Cen z) ≠ ⊥) (h : IsDoubleCoverOfAlt (CentralizerBar z) n) : False :=
  hF.fail (thm4Concl_of_images ctx.central.1 ctx.sylow
    (images_of_cover h (exists_component_of_Em_ne_bot hE))
    (WBar_le_zpowers_of_cover ctx.central.1 h))

theorem false_of_m12 (h : Stage1M12 G z S) (hE : Em (Cen z) ≠ ⊥) : False := by
  obtain ⟨J, hJ⟩ := exists_component_of_Em_ne_bot hE
  exact no_component_of_m12 h _ (isComponent_map_pPrimeCore hJ)

end Kinds

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S2
