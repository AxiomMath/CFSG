module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Statements
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.CfgBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin

theorem lemma2_4_17 (hSing : SingerNormalizerCyclic) (h8 : Lemma2_4_8) (h12 : Lemma2_4_12)
    (h14 : Lemma2_4_14) (h16 : Lemma2_4_16) : Lemma2_4_17 := by
  intro G _ _ T M H S L D n hcfg Z hZ
  obtain ⟨⟨hTS, hTnS, hTnR⟩, -, -, -, ⟨B, hB⟩, h6, -, hDcyc, -⟩ := h8 G T M H S L D n hcfg
  have hST : S ≤ T := hcfg.S_le_T
  have hRS : thompsonJ S ≤ S := thompsonJ_le_self S
  have hRT : thompsonJ S ≤ T := hRS.trans hST
  have hn2 : 2 ≤ n := hcfg.one_lt
  obtain ⟨x₀, hx₀T, hx₀S⟩ : ∃ x ∈ T, x ∉ S := by
    by_contra hcon
    exact hcfg.S_ne_T (le_antisymm hST fun x hx => by_contra fun hxS => hcon ⟨x, hx, hxS⟩)
  obtain ⟨hZ1, hZ2, -⟩ := h16 G T M H S L D n hcfg Z hZ
  have hZel := hZ1.1
  have hZcard := hZ1.2.1
  have hZcases : (centerOf L = ⊥ ∧ Z = centerOf (thompsonJ S)) ∨
      (centerOf L ≠ ⊥ ∧ Z = centerOf L) := by
    by_cases hc : centerOf L = ⊥
    · left; exact ⟨hc, by simp [hZ, lin2Z, hc]⟩
    · right; exact ⟨hc, by simp [hZ, lin2Z, hc]⟩
  have hZne : Z ≠ ⊥ := by
    intro h
    have : Nat.card Z = 1 := by rw [h]; exact Subgroup.card_bot
    rw [hZcard] at this
    have h4' : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  have hZR : Z ≤ centerOf (thompsonJ S) := by
    rcases hZ2 x₀ hx₀T hx₀S with ⟨-, -, hZe⟩ | ⟨-, hZR2, -⟩
    · exact hZe.le
    · rw [hZR2]; exact le_sup_left
  have hRC : thompsonJ S ≤ Subgroup.centralizer (Z : Set G) := by
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.1 (hZR hz).2 r hr).symm
  have hlt : 2 ^ (n / 2) < 2 ^ n :=
    Nat.pow_lt_pow_right (by norm_num) (Nat.div_lt_self (by omega) (by norm_num))
  have hCSR : S ⊓ Subgroup.centralizer (Z : Set G) = thompsonJ S := by
    apply le_antisymm
    · rintro s ⟨hsS, hsC⟩
      obtain ⟨⟨hcyc, hRF, hRFS, -, -⟩, hinv⟩ := h12 G T M H S L D n hcfg B hB
      have hFN : (S ⊓ Subgroup.normalizer (B : Set G) : Subgroup G) ≤
          Subgroup.normalizer (thompsonJ S : Set G) := fun g hg => hTnR (hST hg.1)
      have hs : s ∈ (((S ⊓ Subgroup.normalizer (B : Set G) : Subgroup G) ⊔ thompsonJ S :
          Subgroup G) : Set G) := by
        rw [sup_comm, hRFS]; exact hsS
      rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hFN] at hs
      obtain ⟨f, hf, r, hr, rfl⟩ := hs
      have hfC : f ∈ Subgroup.centralizer (Z : Set G) := by
        have h1 := (Subgroup.centralizer (Z : Set G)).mul_mem hsC
          ((Subgroup.centralizer (Z : Set G)).inv_mem (hRC hr))
        simpa using h1
      show f * r ∈ thompsonJ S
      by_cases hf1 : f = 1
      · rw [hf1, one_mul]; exact hr
      · exfalso
        have hF2 : IsPGroup 2 ((S ⊓ Subgroup.normalizer (B : Set G)) ⊓
            Subgroup.centralizer (Z : Set G) : Subgroup G) :=
          hcfg.S_isPGroup.to_le (inf_le_left.trans inf_le_left)
        have hbot : (S ⊓ Subgroup.normalizer (B : Set G)) ⊓ Subgroup.centralizer (Z : Set G) ≠ ⊥ :=
          fun h => hf1 (by
            have : f ∈ (S ⊓ Subgroup.normalizer (B : Set G)) ⊓ Subgroup.centralizer (Z : Set G) :=
              ⟨hf, hfC⟩
            rw [h] at this
            simpa using this)
        obtain ⟨f₁, hf₁, hf₁2, hf₁1⟩ := exists_involution_of_isPGroup hF2 hbot
        have := (hinv f₁ hf₁.1 hf₁1 hf₁2).2.2.2.1
        rw [← hZ] at this
        have hZf : Z ⊓ Subgroup.centralizer ({f₁} : Set G) = Z := by
          apply inf_eq_left.2
          intro z hz
          rw [Subgroup.mem_centralizer_iff]
          intro g hg
          rw [Set.mem_singleton_iff] at hg
          subst hg
          exact (Subgroup.mem_centralizer_iff.1 hf₁.2 z hz).symm
        rw [hZf, hZcard] at this
        exact absurd this hlt.ne'
    · exact le_inf hRS hRC
  refine ⟨?_, ?_⟩
  · by_cases hCT : T ⊓ Subgroup.centralizer (Z : Set G) = thompsonJ S
    · exact Or.inl hCT
    · right
      obtain ⟨u, huK, huS⟩ : ∃ u ∈ T ⊓ Subgroup.centralizer (Z : Set G), u ∉ S := by
        by_contra hcon
        apply hCT
        apply le_antisymm
        · intro k hk
          have hkS : k ∈ S := by
            by_contra hkS
            exact hcon ⟨k, hk, hkS⟩
          rw [← hCSR]; exact ⟨hkS, hk.2⟩
        · exact le_inf hRT hRC
      have hu2 : u ^ 2 ∈ thompsonJ S := by
        rw [← hCSR]
        exact ⟨sq_mem_of_relIndex_two hTS huK.1, pow_mem huK.2 2⟩
      obtain ⟨⟨i, hi, hi2⟩, -, -⟩ := h14 G T M H S L D n hcfg u huK.1 huS hu2
      have e : u * (u⁻¹ * i) = i := by group
      have hiT : i ∈ T := by rw [← e]; exact T.mul_mem huK.1 (hRT hi)
      have hiC : i ∈ Subgroup.centralizer (Z : Set G) := by
        rw [← e]; exact (Subgroup.centralizer (Z : Set G)).mul_mem huK.2 (hRC hi)
      have hiS : i ∉ S := by
        intro hiS
        apply huS
        have h1 : i * (u⁻¹ * i)⁻¹ ∈ S := S.mul_mem hiS (S.inv_mem (hRS hi))
        have e' : i * (u⁻¹ * i)⁻¹ = u := by group
        rwa [e'] at h1
      have hKeq : T ⊓ Subgroup.centralizer (Z : Set G) = thompsonJ S ⊔ Subgroup.zpowers i := by
        apply le_antisymm
        · intro k hk
          by_cases hkS : k ∈ S
          · exact Subgroup.mem_sup_left (by rw [← hCSR]; exact ⟨hkS, hk.2⟩)
          · have h1 := inv_mul_mem_of_relIndex_two hTS hiT hk.1 hiS hkS
            have h2 : i⁻¹ * k ∈ Subgroup.centralizer (Z : Set G) :=
              (Subgroup.centralizer (Z : Set G)).mul_mem
                ((Subgroup.centralizer (Z : Set G)).inv_mem hiC) hk.2
            have h3 : i⁻¹ * k ∈ thompsonJ S := by rw [← hCSR]; exact ⟨h1, h2⟩
            have e2 : k = i * (i⁻¹ * k) := by group
            rw [e2]
            exact (thompsonJ S ⊔ Subgroup.zpowers i).mul_mem
              (Subgroup.mem_sup_right (Subgroup.mem_zpowers i)) (Subgroup.mem_sup_left h3)
        · exact sup_le (le_inf hRT hRC) (Subgroup.zpowers_le.2 ⟨hiT, hiC⟩)
      have hZi : Z ≤ Subgroup.centralizer ({i} : Set G) := by
        intro z hz
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        rw [Set.mem_singleton_iff] at hg
        subst hg
        exact (Subgroup.mem_centralizer_iff.1 hiC z hz).symm
      obtain ⟨-, -, htypes⟩ := h14 G T M H S L D n hcfg i hiT hiS (by rw [hi2]; exact one_mem _)
      rcases htypes hi2 with ⟨hc, hZZ, -⟩ | ⟨hc, -, -, hcard2⟩ | ⟨hc, -, hcard2⟩
      · have hZe : Z = centerOf (thompsonJ S) :=
          (hZcases.resolve_right (fun h => h.1 hc)).2
        exact ⟨hc, i, hiT, hiS, hi2, hKeq, hZe, hZe.trans hZZ⟩
      · exfalso
        have hle : Z ≤ omegaOneOf (thompsonJ S ⊓ Subgroup.centralizer ({i} : Set G)) := by
          intro z hz
          exact Subgroup.subset_closure ⟨⟨(hZR hz).1, hZi hz⟩, hZel.2 z hz⟩
        have := Subgroup.card_le_of_le hle
        rw [hZcard, hcard2] at this
        exact absurd this (not_le.2 hlt)
      · exfalso
        rcases hZ2 i hiT hiS with ⟨hc', -, -⟩ | ⟨-, -, hTI⟩
        · exact hc hc'
        · have hiN : i ∈ Subgroup.normalizer (Z : Set G) :=
            Subgroup.centralizer_le_normalizer _ hiC
          rw [conjR_eq_of_mem_normalizer hiN, inf_idem] at hTI
          exact hZne hTI
  · intro hc
    have hZe : Z = centerOf (thompsonJ S) := (hZcases.resolve_right (fun h => h.1 hc)).2
    obtain ⟨hDB, hHall, hBab, hTprod, hSRD, hBR, hTRB, hRB, hRNT, hRNT', hDD⟩ := hB
    obtain ⟨hBle, hreg⟩ := (h6 B ⟨hDB, hHall, hBab, hTprod, hSRD, hBR, hTRB, hRB, hRNT, hRNT',
      hDD⟩).2 hc
    have hBle' : B ≤ D ⊔ Subgroup.centralizer (Z : Set G) := by rw [hZe]; exact hBle
    have hreg' : ActsRegularlyOn D (nonIdentity Z) := by rw [hZe]; exact hreg
    have hTN : T ≤ Subgroup.normalizer (Z : Set G) := by
      intro g hg
      rw [← conjR_eq_self_iff, hZe]
      exact centerOf_normalized (hTnR hg)
    have hDN : D ≤ Subgroup.normalizer (Z : Set G) := by
      intro g hg
      rw [← conjR_eq_self_iff, hZe]
      exact centerOf_normalized (hBR (hDB hg))
    have hTC : T ≤ Subgroup.normalizer ((Subgroup.centralizer (Z : Set G) : Subgroup G) : Set G) := by
      intro g hg
      rw [← conjR_eq_self_iff, ← conjR_centralizer, conjR_eq_of_mem_normalizer (hTN hg)]
    have hTE : T ≤ Subgroup.normalizer
        ((D ⊔ Subgroup.centralizer (Z : Set G) : Subgroup G) : Set G) := by
      have h1 : T ≤ Subgroup.normalizer
          (((thompsonJ S ⊔ B) ⊔ Subgroup.centralizer (Z : Set G) : Subgroup G) : Set G) :=
        fun g hg => Subgroup.inf_normalizer_le_normalizer_sup _ _
          ⟨hTRB (Subgroup.mem_sup_left hg), hTC hg⟩
      have h2 : (thompsonJ S ⊔ B) ⊔ Subgroup.centralizer (Z : Set G) =
          D ⊔ Subgroup.centralizer (Z : Set G) := by
        apply le_antisymm
        · exact sup_le (sup_le (hRC.trans le_sup_right) hBle') le_sup_right
        · exact sup_le_sup_right (hDB.trans le_sup_right) _
      rwa [h2] at h1
    exact hSing G Z D T hZel hZne hDN hDcyc.1 hreg' hcfg.sylowT.isPGroup hTN hTE

end CFSG.QuasithinUnique.Lin2
