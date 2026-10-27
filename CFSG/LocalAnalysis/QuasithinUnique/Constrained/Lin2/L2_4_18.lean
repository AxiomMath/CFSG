module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Statements
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.General
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesConfining

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

theorem thompsonJ_eq_sup_of_forall {G : Type*} [Group G] {S U V : Subgroup G}
    (h : ∀ A : Subgroup G, IsMaxElemAbelian S A ↔ A = U ∨ A = V) : thompsonJ S = U ⊔ V := by
  apply le_antisymm
  · refine iSup₂_le fun A hA => ?_
    rcases (h A).1 hA with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  · refine sup_le ?_ ?_
    · exact le_iSup₂_of_le U ((h U).2 (Or.inl rfl)) le_rfl
    · exact le_iSup₂_of_le V ((h V).2 (Or.inr rfl)) le_rfl

theorem lemma2_4_18 (h8 : Lemma2_4_8) (h11 : Lemma2_4_11) (h14 : Lemma2_4_14)
    (h16 : Lemma2_4_16) (h17 : Lemma2_4_17) : Lemma2_4_18 := by
  intro G _ _ T M H S L D n hcfg Z hZ
  obtain ⟨⟨hTS, hTnS, hTnR⟩, ⟨hOL, hUQ⟩, ⟨hJbaum, hRsyl, h3⟩, h4, ⟨B, hB⟩, h6, h7, -, hirr⟩ :=
    h8 G T M H S L D n hcfg
  obtain ⟨-, -, h113⟩ := h11 G T M H S L D n hcfg
  have hST : S ≤ T := hcfg.S_le_T
  have hRS : thompsonJ S ≤ S := thompsonJ_le_self S
  have hRT : thompsonJ S ≤ T := hRS.trans hST
  have hset := hcfg.cs.setting
  have hTM : T ≤ M := hset.le
  by_cases hc : centerOf L = ⊥
  ·
    have hZe : Z = centerOf (thompsonJ S) := by simp [hZ, lin2Z, hc]
    obtain ⟨x₀, hx₀T, hx₀S⟩ : ∃ x ∈ T, x ∉ S := by
      by_contra hcon
      exact hcfg.S_ne_T (le_antisymm hST fun x hx => by_contra fun hxS => hcon ⟨x, hx, hxS⟩)
    obtain ⟨hZ1, hZ2, -⟩ := h16 G T M H S L D n hcfg Z hZ
    have hZel := hZ1.1
    have hZcard := hZ1.2.1
    have hn2 : 2 ≤ n := hcfg.one_lt
    have hZne : Z ≠ ⊥ := by
      intro h
      have : Nat.card Z = 1 := by rw [h]; exact Subgroup.card_bot
      rw [hZcard] at this
      have h4' : 4 ≤ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      omega
    obtain ⟨hDB, hHall, hBab, hTprod, hSRD, hBR, hTRB, hRB, hRNT, hRNT', hDD⟩ := hB
    obtain ⟨hBle, hreg⟩ := (h6 B ⟨hDB, hHall, hBab, hTprod, hSRD, hBR, hTRB, hRB, hRNT,
      hRNT', hDD⟩).2 hc
    have hDM : D ≤ M := hcfg.hall.1.trans inf_le_right
    have hDL : D ≤ L := hcfg.hall.1.trans inf_le_left
    have hZT : Z ≤ T := by
      rw [hZe]; exact (inf_le_left : centerOf (thompsonJ S) ≤ thompsonJ S).trans hRT
    have hZn : T ≤ Subgroup.normalizer (Z : Set G) := by
      intro g hg
      rw [← conjR_eq_self_iff, hZe]
      exact centerOf_normalized (hTnR hg)
    have hDZ : D ≤ Subgroup.normalizer (Z : Set G) := by
      intro g hg
      rw [← conjR_eq_self_iff, hZe]
      exact centerOf_normalized (hBR (hDB hg))
    have hreg' : ActsRegularlyOn D (nonIdentity Z) := by rw [hZe]; exact hreg
    obtain ⟨z₀, hz₀Z, hz₀1, hz₀T⟩ :=
      exists_mem_inf_center_of_normal hcfg.sylowT.isPGroup hZT hZn hZne
    have hz₀2 : z₀ ^ 2 = 1 := hZel.2 z₀ hz₀Z
    have hPT : pCoreOf 2 M ≤ T := hset.isSylowTwoOf_M.pCoreOf_le
    have hPN : M ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
      CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M
    have hz₀P : z₀ ∈ centerOf (pCoreOf 2 M) := by
      have h1 : z₀ ∈ Subgroup.centralizer (pCoreOf 2 M : Set G) :=
        Subgroup.centralizer_le (by exact_mod_cast hPT) hz₀T
      exact ⟨hset.charTwo ⟨hTM (hZT hz₀Z), h1⟩, h1⟩
    have hZP : Z ≤ centerOf (pCoreOf 2 M) := by
      intro w hw
      by_cases hw1 : w = 1
      · rw [hw1]; exact one_mem _
      · obtain ⟨b, hb, hbw⟩ := hreg'.2.1 z₀ ⟨hz₀Z, hz₀1⟩ w ⟨hw, hw1⟩
        have hbN : b⁻¹ ∈ Subgroup.normalizer (centerOf (pCoreOf 2 M) : Set G) := by
          rw [← conjR_eq_self_iff]
          exact centerOf_normalized (hPN (hDM (D.inv_mem hb)))
        have h2 := (Subgroup.mem_normalizer_iff.1 hbN z₀).1 hz₀P
        rw [inv_inv, hbw] at h2
        exact h2
    have hZM : M ≤ Subgroup.normalizer (Z : Set G) := by
      by_cases hRP : thompsonJ S ≤ pCoreOf 2 M
      ·
        have hJT : thompsonJ T = thompsonJ S := by
          rw [thompsonJ_eq_sup_of_forall ((h3 x₀ hx₀T hx₀S).2.2.2), ← (h3 x₀ hx₀T hx₀S).1]
        have hJP : thompsonJ (pCoreOf 2 M) = thompsonJ S := by
          have h1 : thompsonJ T ≤ pCoreOf 2 M := hJT ▸ hRP
          rw [← hJT]
          exact thompsonJ_eq_of_le h1 hPT
        intro m hm
        rw [← conjR_eq_self_iff, hZe, ← hJP, conjR_centerOf, conjR_thompsonJ,
          conjR_eq_of_mem_normalizer (hPN hm)]
      ·
        have hLU : L ≤ Subgroup.normalizer (blockU L : Set G) := by
          rw [← hOL]
          exact CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 L
        obtain ⟨hRsup, hZRU, -, -⟩ := h3 x₀ hx₀T hx₀S
        have hPx : conjR (pCoreOf 2 M) x₀ = pCoreOf 2 M :=
          conjR_eq_of_mem_normalizer (hPN (hTM hx₀T))
        have hZx : conjR Z x₀ = Z := by rw [hZe]; exact centerOf_normalized (hTnR hx₀T)
        have hUnP : ¬ blockU L ≤ pCoreOf 2 M := by
          intro hUP
          apply hRP
          rw [hRsup]
          refine sup_le hUP ?_
          calc conjR (blockU L) x₀ ≤ conjR (pCoreOf 2 M) x₀ := conjR_mono hUP x₀
            _ = pCoreOf 2 M := hPx
        have hUP : blockU L ⊓ pCoreOf 2 M = Z := by
          have hle1 : centerOf (thompsonJ S) ≤ blockU L ⊓ pCoreOf 2 M := by
            refine le_inf ?_ ?_
            · rw [← hZRU]; exact inf_le_left
            · rw [← hZe]; exact hZP.trans inf_le_left
          have hDN : D ≤ Subgroup.normalizer ((blockU L ⊓ pCoreOf 2 M : Subgroup G) : Set G) :=
            fun g hg => Subgroup.inf_normalizer_le_normalizer_inf ⟨hLU (hDL hg), hPN (hDM hg)⟩
          rcases hirr _ hle1 inf_le_left hDN with h | h
          · rw [h, hZe]
          · exact absurd (h ▸ inf_le_right) hUnP
        have hUxP : conjR (blockU L) x₀ ⊓ pCoreOf 2 M = Z := by
          have := congrArg (fun K => conjR K x₀) hUP
          simp only [conjR_inf] at this
          rw [hPx, hZx] at this
          exact this
        have hinvol : ∀ r ∈ thompsonJ S ⊓ pCoreOf 2 M, r ^ 2 = 1 → r ∈ Z := by
          intro r hr hr2
          have hE : IsElemAbelian 2 (Subgroup.zpowers r) := by
            refine ⟨inferInstance, fun y hy => ?_⟩
            obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
            rcases zpow_of_sq_eq_one hr2 k with hk | hk <;> simp [hk, hr2]
          have hEle : Subgroup.zpowers r ≤ thompsonJ S := Subgroup.zpowers_le.2 hr.1
          rcases (h7 x₀ hx₀T hx₀S).2.2 _ hEle hE with h | h
          · have : r ∈ blockU L ⊓ pCoreOf 2 M := ⟨h (Subgroup.mem_zpowers r), hr.2⟩
            rwa [hUP] at this
          · have : r ∈ conjR (blockU L) x₀ ⊓ pCoreOf 2 M := ⟨h (Subgroup.mem_zpowers r), hr.2⟩
            rwa [hUxP] at this
        by_contra hZnn
        have hexT : ∃ t ∈ centerOf (pCoreOf 2 M), t ^ 2 = 1 ∧ t ∉ Z := by
          by_contra hno
          apply hZnn
          have hZeq : Z = omegaOneOf (centerOf (pCoreOf 2 M)) := by
            apply le_antisymm
            · intro z hz
              exact Subgroup.subset_closure ⟨hZP hz, hZel.2 z hz⟩
            · refine (Subgroup.closure_le _).2 fun y hy => ?_
              by_contra hyZ
              exact hno ⟨y, hy.1, hy.2, hyZ⟩
          intro m hm
          rw [← conjR_eq_self_iff, hZeq, conjR_omegaOneOf, conjR_centerOf,
            conjR_eq_of_mem_normalizer (hPN hm)]
        obtain ⟨t, htP, ht2, htZ⟩ := hexT
        have htT : t ∈ T := hPT htP.1
        have htR : t ∉ thompsonJ S := fun htR => htZ (hinvol t ⟨htR, htP.1⟩ ht2)
        have htC : t ∈ Subgroup.centralizer (Z : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro z hz
          exact Subgroup.mem_centralizer_iff.1 htP.2 z (hZP hz).1
        obtain ⟨h17a, -⟩ := h17 G T M H S L D n hcfg Z hZ
        rcases h17a with hCT | ⟨-, t', ht'T, ht'S, ht'2, hCT, -, -⟩
        · exact htR (hCT ▸ ⟨htT, htC⟩)
        · have htS : t ∉ S := by
            have h1 : t ∈ thompsonJ S ⊔ Subgroup.zpowers t' := hCT ▸ ⟨htT, htC⟩
            rcases mem_sup_zpowers_of_sq_eq_one (hTnR ht'T) ht'2 h1 with h | ⟨r, hr, hrt⟩
            · exact absurd h htR
            · intro htS'
              apply ht'S
              have : t' = r⁻¹ * t := by rw [hrt]; group
              rw [this]
              exact S.mul_mem (S.inv_mem (hRS hr)) htS'
          obtain ⟨-, -, htypes⟩ := h14 G T M H S L D n hcfg t htT htS
            (by rw [ht2]; exact one_mem _)
          have hcomm : ⁅thompsonJ S, Subgroup.zpowers t⁆ ≤ Z := by
            rw [Subgroup.commutator_le]
            intro r hr y hy
            obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
            rcases zpow_of_sq_eq_one ht2 k with hk | hk
            · rw [hk]; simp
            · rw [hk]
              have hrN : r ∈ Subgroup.normalizer (centerOf (pCoreOf 2 M) : Set G) := by
                rw [← conjR_eq_self_iff]
                exact centerOf_normalized (hPN (hTM (hRT hr)))
              have ha : r * t * r⁻¹ ∈ centerOf (pCoreOf 2 M) := (Subgroup.mem_normalizer_iff.1 hrN t).1 htP
              have hb : t⁻¹ ∈ centerOf (pCoreOf 2 M) := (centerOf (pCoreOf 2 M)).inv_mem htP
              have e1 : ⁅r, t⁆ = (r * t * r⁻¹) * t⁻¹ := by simp [commutatorElement_def]
              have e2 : ⁅r, t⁆ = r * (t * r⁻¹ * t⁻¹) := by simp [commutatorElement_def, mul_assoc]
              apply hinvol
              · refine ⟨?_, ?_⟩
                · rw [e2]
                  exact (thompsonJ S).mul_mem hr
                    ((Subgroup.mem_normalizer_iff.1 (hTnR htT) r⁻¹).1 ((thompsonJ S).inv_mem hr))
                · rw [e1]
                  exact (pCoreOf 2 M).mul_mem ha.1 hb.1
              · rw [e1]
                have hcomm' : Commute (r * t * r⁻¹) t⁻¹ := by
                  exact (Subgroup.mem_centralizer_iff.1 hb.2 _ ha.1)
                rw [hcomm'.mul_pow]
                have ha2 : (r * t * r⁻¹) ^ 2 = 1 := by
                  have : (r * t * r⁻¹) ^ 2 = r * t ^ 2 * r⁻¹ := by simp only [pow_two]; group
                  rw [this, ht2]; simp
                have hb2 : (t⁻¹) ^ 2 = 1 := by rw [inv_pow, ht2, inv_one]
                rw [ha2, hb2, one_mul]
          rcases htypes ht2 with ⟨-, -, hnc⟩ | ⟨-, -, -, hcard2⟩ | ⟨hc', -⟩
          · exact absurd (hZe ▸ hcomm) hnc
          · exfalso
            have hle : Z ≤ omegaOneOf (thompsonJ S ⊓ Subgroup.centralizer ({t} : Set G)) := by
              intro z hz
              refine Subgroup.subset_closure ⟨⟨(hZe ▸ hz : z ∈ centerOf (thompsonJ S)).1, ?_⟩, hZel.2 z hz⟩
              exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 htC z hz)
            have := Subgroup.card_le_of_le hle
            have hlt : 2 ^ (n / 2) < 2 ^ n :=
              Nat.pow_lt_pow_right (by norm_num) (Nat.div_lt_self (by omega) (by norm_num))
            rw [hZcard, hcard2] at this
            exact absurd this (not_le.2 hlt)
          · exact hc' hc
    have hZ2' : IsPGroup 2 Z := hcfg.sylowT.isPGroup.to_le hZT
    have hNZ : Subgroup.normalizer (Z : Set G) = M :=
      hset.maxLocal.2 _ ⟨Z, hZne, hZ2', rfl⟩ hZM
    have hTI : fusionIsTI Z := by
      refine fusionIsTI_of_centralizer_le hNZ ?_ ?_
      · intro u hu hu1
        obtain ⟨b, hb, hbu⟩ := hreg'.2.1 z₀ ⟨hz₀Z, hz₀1⟩ u ⟨hu, hu1⟩
        have hz₀C : Subgroup.centralizer ({z₀} : Set G) ≤ M :=
          hset.le_of_isTwoLocal_of_isSylowTwoOf_M hset.isSylowTwoOf_M
            (isTwoLocal_centralizer_of_sq_eq_one hz₀2 hz₀1) (fun t ht => by
              rw [Subgroup.mem_centralizer_singleton_iff]
              exact Subgroup.mem_centralizer_iff.1 hz₀T t ht)
        intro g hg
        rw [Subgroup.mem_centralizer_singleton_iff] at hg
        have hz : z₀ = b * u * b⁻¹ := by rw [← hbu]; group
        have hg' : b * g * b⁻¹ ∈ Subgroup.centralizer ({z₀} : Set G) := by
          rw [Subgroup.mem_centralizer_singleton_iff]
          calc b * g * b⁻¹ * z₀ = b * (g * u) * b⁻¹ := by rw [hz]; group
            _ = b * (u * g) * b⁻¹ := by rw [hg]
            _ = z₀ * (b * g * b⁻¹) := by rw [hz]; group
        have h1 := hz₀C hg'
        have e : g = b⁻¹ * (b * g * b⁻¹) * b := by group
        rw [e]
        exact M.mul_mem (M.mul_mem (M.inv_mem (hDM hb)) h1) (hDM hb)
      · intro u hu g hg
        by_cases hu1 : u = 1
        · exact ⟨1, M.one_mem, by simp [hu1]⟩
        · have hv1 : g⁻¹ * u * g ≠ 1 := by
            intro h
            apply hu1
            have : u = g * (g⁻¹ * u * g) * g⁻¹ := by group
            rw [this, h]; group
          obtain ⟨b, hb, hbv⟩ := hreg'.2.1 u ⟨hu, hu1⟩ (g⁻¹ * u * g) ⟨hg, hv1⟩
          exact ⟨b, hDM hb, hbv.symm⟩
    exact ⟨hTI, fun _ => hNZ, fun h => absurd hc h⟩
  · have hZe : Z = centerOf L := by simp [hZ, lin2Z, hc]
    obtain ⟨hTI, hN⟩ := h113 hc
    exact ⟨hZe ▸ hTI, fun h => absurd h hc, fun _ => hZe ▸ hN.symm⟩

end CFSG.QuasithinUnique.Lin2
