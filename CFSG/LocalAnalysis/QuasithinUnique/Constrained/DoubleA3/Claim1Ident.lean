module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Claim1Setup
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Claim1A8
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Claim1Order
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdList

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G] [Finite G] {T M H S L K : Subgroup G} {s x z₁ z₂ : G}

theorem A3A3K.false_of_larger_component
    (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3)
    (h34 : Lemma2_4_34_used) (hI : Inputs2436) (hK : A3A3K T M H S L s x z₁ z₂ K) {r : G}
    (hrR : r ∈ baum S) (hrC : r ∈ Subgroup.centralizer (K : Set G)) (hr2 : r * r = 1)
    (hr1 : r ≠ 1) {J : Subgroup G} (hJ : IsComponentIn J (centralizerElem r)) (hKJ : K ≤ J)
    (hKJne : K ≠ J) (hJN : centralizerElem r ≤ normalizer (J : Set G))
    (hz₂N : z₂ ∈ normalizer (J : Set G)) : False := by
  have hcs := hK.cs
  have hsimple := hcs.setting.simple
  have hnonab := hcs.setting.nonabelian
  have hq := hcs.setting.qtke
  obtain ⟨e₀⟩ := hK.nonempty_alt6 h34
  have hz₂2 : z₂ * z₂ = 1 := by simpa [pow_two] using hK.toA3A3x.sq₂
  have hJq : CFSG.IsQuasisimple ↥J := BenderBranch.isQuasisimple_of_isComponentIn hJ
  have hKz : K ≤ centralizerElem z₂ := hK.K_comp.1
  have hKcomp : IsComponentIn K (J ⊓ Subgroup.centralizer ({z₂} : Set G)) :=
    BenderBranch.isComponentIn_of_le hK.K_comp (le_inf hKJ hKz) inf_le_right
  have hcomm : ⁅J, Subgroup.zpowers z₂⁆ = J := by
    rcases Id2519.commutator_dichotomy hJq hz₂N with h | h
    · exact h
    · exfalso
      have hJle : J ⊓ Subgroup.centralizer ({z₂} : Set G) = J := inf_eq_left.mpr h
      rw [hJle] at hKcomp
      exact hKJne (Id2519.eq_of_isComponentIn_of_isQuasisimple hKcomp hJq)
  have hex : ∃ z : G, Lemma115Cases J z :=
    Id2519.exists_lemma115Cases hI.list115 hsimple hnonab hq hr1 hr2 hJ
  have hA6 := hI.ident G J K z₂ hJq hex hz₂N hz₂2 hcomm hKcomp ⟨e₀⟩
  obtain ⟨Tr, hTrS, hz₂Tr, hbound⟩ :=
    hK.exists_sylow_cent hD h27_1 h34 hrR hrC hr2 hr1 hJ
  have hJle : J ≤ centralizerElem r := hJ.1
  have hPsyl : IsSylowTwoOf (Tr ⊓ J) J := A4.isSylowTwoOf_inf_normal hTrS hJle hJN
  have hz₂P : z₂ ∈ normalizer ((Tr ⊓ J : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 : y ∈ Tr ↔ z₂ * y * z₂⁻¹ ∈ Tr := by
      constructor
      · intro hy
        exact Tr.mul_mem (Tr.mul_mem hz₂Tr hy) (Tr.inv_mem hz₂Tr)
      · intro hy
        have h3 := Tr.mul_mem (Tr.mul_mem (Tr.inv_mem hz₂Tr) hy) hz₂Tr
        have e : z₂⁻¹ * (z₂ * y * z₂⁻¹) * z₂ = y := by group
        rwa [e] at h3
    have h2 : y ∈ J ↔ z₂ * y * z₂⁻¹ ∈ J := Subgroup.mem_normalizer_iff.mp hz₂N y
    exact ⟨fun hy => ⟨h1.mp hy.1, h2.mp hy.2⟩, fun hy => ⟨h1.mpr hy.1, h2.mpr hy.2⟩⟩
  have hb4 : (Subgroup.centralizer ({z₂} : Set G)).relIndex (Tr ⊓ J) ≤ 4 :=
    hbound _ inf_le_left
  rcases hA6 with hpat | hpat | hpat | hpat
  · have h8 := hI.class8 G J K z₂ hJq hz₂N hz₂2 hcomm hKcomp (Or.inl hpat) (Tr ⊓ J) hPsyl hz₂P
    omega
  · have h8 := hI.class8 G J K z₂ hJq hz₂N hz₂2 hcomm hKcomp (Or.inr (Or.inl hpat)) (Tr ⊓ J) hPsyl
      hz₂P
    omega
  · have h8 := hI.class8 G J K z₂ hJq hz₂N hz₂2 hcomm hKcomp (Or.inr (Or.inr hpat)) (Tr ⊓ J) hPsyl
      hz₂P
    omega
  · exact hK.false_of_A8 hD h27_1 h34 hKcomp hpat

theorem lemma2_4_36_claim2_of_inputs
    (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3)
    (h34 : Lemma2_4_34_used) (hI : Inputs2436) : Lemma2_4_36_claim2 := by
  intro G _ _ T M H S L s x z₁ z₂ K hK r hr hr2 hr1
  obtain ⟨hrR, hrC⟩ := hr
  have hrz : r * z₂ = z₂ * r := Subgroup.mem_centralizer_iff.mp hK.toA3A3x.z₂_mem.2 r hrR
  rcases hK.balance hI h34 hrC hr2 hr1 hrz with h | ⟨J, hJ, hKJ, hKJne, hJN, hz₂N⟩
  · exact h
  · exact (hK.false_of_larger_component hD h27_1 h34 hI hrR hrC hr2 hr1 hJ hKJ hKJne hJN
      hz₂N).elim

end CFSG.QuasithinUnique.DoubleA3
