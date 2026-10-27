module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3HAPerm2
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.Child5HAutTransfer
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDV2
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3DHyp5

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.Fischer Subgroup CFSG.EvenSmallLie.UnitarySix.YamadaHAut

variable {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* T46} {t : G}
  {Θ : centralizer ({t} : Set G) →* Equiv.Perm (Fin 693)}

theorem NHA₄_le' (hΘ : ThetaSpec t e Θ) :
    normalizer ((sec3DData e t).A₄ : Set G) ⊓ (sec3DData e t).H ≤
      normalizer ((sec3DData e t).A₃ : Set G) := by
  rintro g ⟨hgN, hgH⟩
  have h1 := (hΘ.mem_normalizer_toG_iff (grp_le_T46 gensOK_chA4) ⟨g, hgH⟩).1 hgN
  exact (hΘ.mem_normalizer_toG_iff (grp_le_T46 gensOK_chA3) ⟨g, hgH⟩).2
    (NHA4_perm (hΘ.mem_autT _) h1)

theorem oTwo_NA₄' (hΘ : ThetaSpec t e Θ) :
    ∀ P : Subgroup G, P ≤ normalizer ((sec3DData e t).withT (sec3DData e t).A₄ : Set G) ⊓
        (sec3DData e t).H →
      normalizer ((sec3DData e t).withT (sec3DData e t).A₄ : Set G) ⊓ (sec3DData e t).H ≤
        normalizer (P : Set G) → IsPGroup 2 P →
      P ≤ (sec3DData e t).withT (sec3DData e t).A₃ := by
  intro P hP hnorm h2
  have hPH : P ≤ centralizer ({t} : Set G) := fun x hx => (hP hx).2
  refine (hΘ.le_toG_sup_iff (grp_le_T46 gensOK_chA3) hPH).2 ?_
  apply oTwo_NA4_perm
  · rintro _ ⟨x, -, rfl⟩
    exact hΘ.mem_autT x
  · rintro _ ⟨x, hx, rfl⟩
    exact (hΘ.mem_normalizer_toG_sup_iff (grp_le_T46 gensOK_chA4) x).1 (hP hx).1
  · exact ThetaSpec.isPGroup_map h2
  · intro g hg
    have hgT : g ∈ T46 := grp_le_T46 gensOK_chP2 hg
    have hl : iotaG e ⟨g, hgT⟩ ∈
        normalizer ((sec3DData e t).withT (sec3DData e t).A₄ : Set G) ⊓ (sec3DData e t).H := by
      refine ⟨?_, hΘ.L_le_centralizer (iotaG_mem _)⟩
      refine (hΘ.mem_normalizer_toG_sup_iff (grp_le_T46 gensOK_chA4)
        ⟨_, hΘ.L_le_centralizer (iotaG_mem _)⟩).2 ?_
      rw [hΘ.apply_iotaG]
      exact chP2_le_normalizer_A4 hg
    have := ThetaSpec.map_le_normalizer (Θ := Θ) hnorm ⟨⟨_, hl.2⟩, hl, hΘ.apply_iotaG _⟩
    exact this

theorem oTwo_CA₄' (hΘ : ThetaSpec t e Θ) :
    ∀ P : Subgroup G, P ≤ centralizer ((sec3DData e t).A₄ : Set G) ⊓ (sec3DData e t).H →
      centralizer ((sec3DData e t).A₄ : Set G) ⊓ (sec3DData e t).H ≤ normalizer (P : Set G) →
      IsPGroup 2 P → P ≤ (sec3DData e t).withT (sec3DData e t).A₃ := by
  intro P hP hnorm h2
  have hPH : P ≤ centralizer ({t} : Set G) := fun x hx => (hP hx).2
  refine (hΘ.le_toG_sup_iff (grp_le_T46 gensOK_chA3) hPH).2 ?_
  apply oTwo_CA4_perm
  · rintro _ ⟨x, -, rfl⟩
    exact hΘ.mem_autT x
  · rintro _ ⟨x, hx, rfl⟩
    exact (hΘ.mem_centralizer_toG_iff (grp_le_T46 gensOK_chA4) x).1 (hP hx).1
  · exact ThetaSpec.isPGroup_map h2
  · intro g hg
    have hgT : g ∈ T46 := grp_le_T46 gensOK_chSigA3 hg
    have hgC : g ∈ centralizer (chA4.grp : Set (Equiv.Perm (Fin 693))) := by
      rw [chSigA3_eq] at hg
      exact (sup_le xComm_spec.2.2.2.1 xComm_spec.2.1) hg
    have hl : iotaG e ⟨g, hgT⟩ ∈
        centralizer ((sec3DData e t).A₄ : Set G) ⊓ (sec3DData e t).H := by
      refine ⟨?_, hΘ.L_le_centralizer (iotaG_mem _)⟩
      refine (hΘ.mem_centralizer_toG_iff (grp_le_T46 gensOK_chA4)
        ⟨_, hΘ.L_le_centralizer (iotaG_mem _)⟩).2 ?_
      rw [hΘ.apply_iotaG]
      exact hgC
    exact ThetaSpec.map_le_normalizer (Θ := Θ) hnorm ⟨⟨_, hl.2⟩, hl, hΘ.apply_iotaG _⟩

theorem NZ₂S' (hΘ : ThetaSpec t e Θ) :
    ∀ c ∈ (sec3DData e t).H, c * (sec3DData e t).e = (sec3DData e t).e * c →
      c ∈ normalizer ((sec3DData e t).Z₂S : Set G) →
      c ∈ normalizer ((sec3DData e t).A₄ : Set G) := by
  intro c hcH _ hcN
  have hcN' : c ∈ normalizer (toG e chZ2S.grp : Set G) := by
    rw [← d_Z₂S_eq (t := t)]
    exact hcN
  have h1 := (hΘ.mem_normalizer_toG_iff (grp_le_T46 gensOK_chZ2S) ⟨c, hcH⟩).1 hcN'
  exact (hΘ.mem_normalizer_toG_iff (grp_le_T46 gensOK_chA4) ⟨c, hcH⟩).2
    (NZ2S_perm (hΘ.mem_autT _) h1)

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
