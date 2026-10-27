module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5SolWitness

public section

namespace CFSG.ComponentClassification.Foote5.SolMax

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem moved_conj_of_moved {t z : G} {K₁ U : Subgroup G} (hz : orderOf z = 2)
    (hzt : z * t = t * z) (hU : IsTwoComponentIn U (centralizer ({t} : Set G)))
    (hmv : ¬ conjugate K₁ z ≤ coreActionKernel U) :
    IsTwoComponentIn (conjugate U z) (centralizer ({t} : Set G)) ∧
      ¬ K₁ ≤ coreActionKernel (conjugate U z) ∧ conjugate (conjugate U z) z = U := by
  have hzz : z * z = 1 := by rw [← pow_two, ← hz, pow_orderOf_eq_one]
  have hcc : ∀ X : Subgroup G, conjugate (conjugate X z) z = X := fun X => by
    rw [UnbalancedLayer.conjugate_conjugate, hzz, UnbalancedLayer.conjugate_one]
  have hzC : z ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.mpr hzt
  refine ⟨?_, fun h => hmv ?_, hcc U⟩
  · have h1 := Sol76.isTwoComponentIn_map (MulAut.conj z⁻¹) hU
    have h2 : (centralizer ({t} : Set G)).map (MulAut.conj z⁻¹).toMonoidHom =
        centralizer ({t} : Set G) := mem_normalizer_iff_map_conj_eq.mp (le_normalizer (inv_mem hzC))
    rw [h2] at h1
    exact h1
  · have h1 := map_mono (f := (MulAut.conj z⁻¹).toMonoidHom) h
    rw [Sol76.map_coreActionKernel (MulAut.conj z⁻¹) (conjugate U z)] at h1
    have h2 : (conjugate U z).map (MulAut.conj z⁻¹).toMonoidHom = conjugate (conjugate U z) z := rfl
    rw [h2, hcc U] at h1
    exact h1

theorem backward {J K K₁ T : Subgroup G} (hML : GSMirrorMaximal J) (hK : IsSolomonMember K)
    (hT2 : IsPGroup 2 T) (hT : T ≠ ⊥) (hTQ : T ≤ coreActionKernel K)
    (hK₁ : IsTwoComponentIn K₁ (conjClosure (twoLayerIn (K ⊓ centralizer (T : Set G)))
      (twoLayerIn (centralizer (T : Set G)))))
    (hiso : Nonempty (↥K ⧸ Open.fusionZStar ↥K ≃* ↥K₁ ⧸ Open.fusionZStar ↥K₁))
    (hK₁g : MirrorGood J K₁) : MirrorGood J K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKq := isQuasisimple_coreQuot_of_isSolomonMember hK
  have hK₁g' := hK₁g
  obtain ⟨hK₁q, ⟨eK₁⟩, -⟩ := hK₁g'
  obtain ⟨eKK₁⟩ := hiso
  have eK : ↥K ⧸ Open.fusionZStar ↥K ≃* ↥J ⧸ Open.fusionZStar ↥J := eKK₁.trans eK₁
  have hKZ : Nat.card (↥K ⧸ Open.fusionZStar ↥K) = Nat.card (↥J ⧸ Open.fusionZStar ↥J) :=
    Nat.card_congr eK.toEquiv
  have hstarT := star_of_isSolomonMember hK hT2 hTQ
  obtain ⟨hK₁C, hmvK₁⟩ := isTwoComponentIn_of_conjClosure hstarT hK₁
  obtain ⟨P₀, hTP₀⟩ := (hT2.comap_subtype (K := coreActionKernel K)).exists_le_sylow
  obtain ⟨Y, hY, hKY, -⟩ := single_of_sylow hK P₀
  set P := (P₀ : Subgroup ↥(coreActionKernel K)).map (coreActionKernel K).subtype with hP
  have hP2 : IsPGroup 2 P := P₀.isPGroup'.map (coreActionKernel K).subtype
  have hPQ : P ≤ coreActionKernel K := map_subtype_le _
  have hTP : T ≤ P := fun x hx => ⟨⟨x, hTQ hx⟩, hTP₀ (mem_subgroupOf.mpr hx), rfl⟩
  obtain ⟨z, hzP, hz, hzP'⟩ :=
    GSLit.exists_involution_mem_center hP2 le_rfl le_normalizer (ne_bot_of_le_ne_bot hT hTP)
  have hzQ : z ∈ coreActionKernel K := hPQ hzP
  have hPz : P ≤ centralizer ({z} : Set G) := fun x hx =>
    mem_centralizer_singleton_iff.mpr (hzP' x hx)
  have hz2 : IsPGroup 2 (zpowers z) := isPGroup_zpowers_of_orderOf hz
  have hstarz : twoLayerIn (K ⊓ centralizer ({z} : Set G)) ≤
      twoLayerIn (centralizer ({z} : Set G)) := by
    have h1 := star_of_isSolomonMember hK hz2 (zpowers_le.mpr hzQ)
    rwa [centralizer_zpowers'] at h1
  have hCPz : centralizer (P : Set G) ≤ centralizer ({z} : Set G) := by
    rw [← centralizer_zpowers']; exact centralizer_le (zpowers_le.mpr hzP)
  obtain ⟨-, -, hKPsup, -⟩ := cover_facts hKq inf_le_left
    (inf_centralizer_sup_oddCoreIn_eq hP2 hPQ)
  have hKPKz : twoLayerIn (K ⊓ centralizer (P : Set G)) ≤
      twoLayerIn (K ⊓ centralizer ({z} : Set G)) := by
    have h1 := twoLayerIn_inf_centralizer_anti hKq hz2 hP2 (zpowers_le.mpr hzQ) hPQ
      (zpowers_le.mpr hzP)
    rwa [centralizer_zpowers'] at h1
  obtain ⟨hKzc, hKzr, -, -⟩ := cover_facts hKq inf_le_left
    (inf_centralizer_sup_oddCoreIn_eq hz2 (zpowers_le.mpr hzQ))
  rw [centralizer_zpowers'] at hKzc hKzr
  have hKzperf : ⁅twoLayerIn (K ⊓ centralizer ({z} : Set G)),
      twoLayerIn (K ⊓ centralizer ({z} : Set G))⁆ = twoLayerIn (K ⊓ centralizer ({z} : Set G)) := by
    rw [hKzr]
    exact UnbalancedCorr.commutator_eq_of_isPComponent hKzc.1 hKzc.2
  have hKzK : twoLayerIn (K ⊓ centralizer ({z} : Set G)) ≤ K := (map_subtype_le _).trans inf_le_left
  have hKPsup' : twoLayerIn (K ⊓ centralizer (P : Set G)) ⊔ oddCoreIn K = K := by
    obtain ⟨-, hr, -, -⟩ := cover_facts hKq inf_le_left (inf_centralizer_sup_oddCoreIn_eq hP2 hPQ)
    rw [hr]
    exact hKPsup
  have hmovY : ∀ M : Subgroup G, IsTwoComponentIn M (centralizer ({z} : Set G)) →
      ¬ twoLayerIn (K ⊓ centralizer ({z} : Set G)) ≤ coreActionKernel M →
      ¬ Y ≤ coreActionKernel M := by
    intro M hM hmv hYM
    exact hmv (le_coreActionKernel_of_cover hKPKz hKzK hKPsup' hKzperf
      (hstarz.trans (twoLayerIn_le_normalizer hM)) (hKY.trans hYM))
  have hYz : IsTwoComponentIn Y (centralizer ({z} : Set G) ⊓ centralizer (P : Set G)) := by
    rw [inf_eq_right.mpr hCPz]; exact hY
  have hYL : Y ≤ twoLayerIn (centralizer ({z} : Set G)) := by
    have h1 := GrSLit.pLayer_inf_centralizer_le (Y := centralizer ({z} : Set G)) (A := P) hPz hP2
    exact (le_twoLayerIn_of_isTwoComponentIn hYz).trans h1
  obtain ⟨M₀, -, horb⟩ := orbit_of_isPGroup hPz hP2 Y hYz hYL
  obtain ⟨U, hU, hmvU, hUcls⟩ : ∃ U : Subgroup G, IsTwoComponentIn U (centralizer ({z} : Set G)) ∧
      ¬ twoLayerIn (K ⊓ centralizer ({z} : Set G)) ≤ coreActionKernel U ∧ GSMirrorReach J U := by
    have hzT : ∀ x ∈ T, x * z = z * x := fun x hx => hzP' x (hTP hx)
    set Tz := T ⊔ zpowers z with hTz
    have hTzP : Tz ≤ P := sup_le hTP (zpowers_le.mpr hzP)
    have hTz2 : IsPGroup 2 Tz := hP2.to_le hTzP
    have hTzQ : Tz ≤ coreActionKernel K := hTzP.trans hPQ
    have hCTz : centralizer (Tz : Set G) =
        centralizer (T : Set G) ⊓ centralizer ({z} : Set G) := by
      rw [hTz, centralizer_sup_eq, centralizer_zpowers']
    have hstarTz := star_of_isSolomonMember hK hTz2 hTzQ
    set J₂ := twoLayerIn (K ⊓ centralizer (Tz : Set G)) with hJ₂
    obtain ⟨hJ₂c, hJ₂r, hJ₂sup, ⟨eJ₂⟩⟩ := cover_facts hKq inf_le_left
      (inf_centralizer_sup_oddCoreIn_eq hTz2 hTzQ)
    have hJ₂perf : ⁅J₂, J₂⁆ = J₂ := by
      rw [hJ₂, hJ₂r]; exact UnbalancedCorr.commutator_eq_of_isPComponent hJ₂c.1 hJ₂c.2
    have hJ₂q : IsQuasisimple (↥J₂ ⧸ pPrimeCore 2 ↥J₂) := by
      rw [hJ₂, hJ₂r]; exact LocalCores.isQuasisimple_of_mulEquiv eJ₂.symm hKq
    have eJ₂K : ↥J₂ ⧸ Open.fusionZStar ↥J₂ ≃* ↥K ⧸ Open.fusionZStar ↥K := by
      rw [hJ₂, hJ₂r]; exact Sol78.fusionZStarQuotOfCore eJ₂
    have hJ₂card : Nat.card (↥J₂ ⧸ Open.fusionZStar ↥J₂) = Nat.card (↥K ⧸ Open.fusionZStar ↥K) :=
      Nat.card_congr eJ₂K.toEquiv
    have hJ₂sup' : J₂ ⊔ oddCoreIn K = K := by rw [hJ₂, hJ₂r]; exact hJ₂sup
    have hJ₂KT : J₂ ≤ twoLayerIn (K ⊓ centralizer (T : Set G)) :=
      twoLayerIn_inf_centralizer_anti hKq hT2 hTz2 hTQ hTzQ le_sup_left
    have hJ₂Kz : J₂ ≤ twoLayerIn (K ⊓ centralizer ({z} : Set G)) := by
      have h1 := twoLayerIn_inf_centralizer_anti hKq hz2 hTz2 (zpowers_le.mpr hzQ) hTzQ
        le_sup_right
      rwa [centralizer_zpowers'] at h1
    obtain ⟨hKTc, hKTr, -, -⟩ := cover_facts hKq inf_le_left
      (inf_centralizer_sup_oddCoreIn_eq hT2 hTQ)
    have hKTperf : ⁅twoLayerIn (K ⊓ centralizer (T : Set G)),
        twoLayerIn (K ⊓ centralizer (T : Set G))⁆ = twoLayerIn (K ⊓ centralizer (T : Set G)) := by
      rw [hKTr]; exact UnbalancedCorr.commutator_eq_of_isPComponent hKTc.1 hKTc.2
    have hKTK : twoLayerIn (K ⊓ centralizer (T : Set G)) ≤ K :=
      (map_subtype_le _).trans inf_le_left
    have hJ₂K₁ : ¬ J₂ ≤ coreActionKernel K₁ := fun h => hmvK₁ (le_coreActionKernel_of_cover hJ₂KT
      hKTK hJ₂sup' hKTperf (hstarT.trans (twoLayerIn_le_normalizer hK₁C)) h)
    have hzCT : z ∈ centralizer (T : Set G) := mem_centralizer_iff.mpr fun x hx => hzT x hx
    have hzz : z * z = 1 := by rw [← pow_two, ← hz, pow_orderOf_eq_one]
    obtain ⟨D, hD, hmvD, hDK⟩ : ∃ D : Subgroup G, IsTwoComponentIn D (centralizer (Tz : Set G)) ∧
        ¬ J₂ ≤ coreActionKernel D ∧ D ≤ K₁ ⊔ conjugate K₁ z := by
      by_contra hno
      push Not at hno
      apply hJ₂K₁
      refine (le_iSup_moved hstarTz hJ₂perf).trans (iSup₂_le fun D hD' => ?_)
      obtain ⟨hD, hmvD⟩ := hD'
      have hDle := hno D hD hmvD
      have hD₁ : IsTwoComponentIn D (centralizer (T : Set G) ⊓ centralizer ({z} : Set G)) := by
        rw [← hCTz]; exact hD
      have hDL : D ≤
          (pLayer ↥(centralizer (T : Set G)) 2).map (centralizer (T : Set G)).subtype := by
        have h1 := GrSLit.pLayer_inf_centralizer_le (Y := centralizer (T : Set G)) (A := zpowers z)
          (zpowers_le.mpr hzCT) hz2
        rw [centralizer_zpowers'] at h1
        exact (le_twoLayerIn_of_isTwoComponentIn hD₁).trans h1
      obtain ⟨V, hVC, hVp, hDV, -⟩ := UnbalancedCorr.exists_orbit_component hz hzCT
        (by rw [inf_comm]; exact hD₁.1) (by rw [inf_comm]; exact hD₁.2) hDL
      have hV : IsTwoComponentIn V (centralizer (T : Set G)) := ⟨hVC, hVp⟩
      have hVz : IsTwoComponentIn (conjugate V z) (centralizer (T : Set G)) := by
        have h1 := Sol76.isTwoComponentIn_map (MulAut.conj z⁻¹) hV
        have h2 : (centralizer (T : Set G)).map (MulAut.conj z⁻¹).toMonoidHom =
            centralizer (T : Set G) :=
          mem_normalizer_iff_map_conj_eq.mp (le_normalizer (inv_mem hzCT))
        rw [h2] at h1
        exact h1
      have hne1 : K₁ ≠ V := by rintro rfl; exact hDle hDV
      have hne2 : K₁ ≠ conjugate V z := by
        intro h
        apply hDle
        have hVK : V = conjugate K₁ z := by
          rw [h, UnbalancedLayer.conjugate_conjugate, hzz, UnbalancedLayer.conjugate_one]
        rw [hVK, UnbalancedLayer.conjugate_conjugate, hzz, UnbalancedLayer.conjugate_one,
          sup_comm] at hDV
        exact hDV
      exact hDV.trans (sup_le (le_coreActionKernel_of_ne hK₁C hV hne1)
        (le_coreActionKernel_of_ne hK₁C hVz hne2))
    obtain ⟨t, htT, ht, htT'⟩ := GSLit.exists_involution_mem_center hT2 le_rfl le_normalizer hT
    have hzt : z * t = t * z := (hzT t htT).symm
    have hTt : T ≤ centralizer ({t} : Set G) := fun x hx =>
      mem_centralizer_singleton_iff.mpr (htT' x hx)
    have hCTt : centralizer (T : Set G) ≤ centralizer ({t} : Set G) := by
      rw [← centralizer_zpowers']; exact centralizer_le (zpowers_le.mpr htT)
    have hCTzT : centralizer (Tz : Set G) ≤ centralizer (T : Set G) := by
      rw [hCTz]; exact inf_le_left
    have hCTzz : centralizer (Tz : Set G) ≤ centralizer ({z} : Set G) := by
      rw [hCTz]; exact inf_le_right
    have hTzt : Tz ≤ centralizer ({t} : Set G) :=
      sup_le hTt (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hzt))
    have hTzz : Tz ≤ centralizer ({z} : Set G) := sup_le
      (fun x hx => mem_centralizer_singleton_iff.mpr (hzT x hx))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
    have htK₁ : t ∈ coreActionKernel K₁ := Sol78.mem_coreActionKernel_of_commute fun k hk =>
      ((mem_centralizer_iff.mp (hK₁C.1 hk)) t htT).symm
    have hK₁t := anchor_at hML hK₁g ht htK₁
    have hK₁tl : twoLayerIn (K₁ ⊓ centralizer ({t} : Set G)) = K₁ := by
      rw [inf_eq_left.mpr (hK₁C.1.trans hCTt), twoLayerIn_eq_self hK₁C]
    have hDcls : ∀ U : Subgroup G, IsTwoComponentIn U (centralizer ({t} : Set G)) →
        ¬ D ≤ coreActionKernel U → GSMirrorReach J U := by
      intro U hU hmvU
      by_cases h1 : K₁ ≤ coreActionKernel U
      · have h2 : ¬ conjugate K₁ z ≤ coreActionKernel U := fun h2 =>
          hmvU (hDK.trans (sup_le h1 h2))
        obtain ⟨hU', hmv', hUU⟩ := moved_conj_of_moved hz hzt hU h2
        have h3 := hK₁t.2.2.2 (conjugate U z) hU' (by rw [hK₁tl]; exact hmv')
        rw [← hUU]
        exact h3.conj z
      · exact hK₁t.2.2.2 U hU (by rw [hK₁tl]; exact h1)
    have hDq : IsQuasisimple (↥D ⧸ pPrimeCore 2 ↥D) :=
      ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 D _ hD.1).1 hD.2).2.2
    have hDperf : ⁅D, D⁆ = D := UnbalancedCorr.commutator_eq_of_isPComponent hD.1 hD.2
    have hDCt : D ≤ centralizer ({t} : Set G) := hD.1.trans (hCTzT.trans hCTt)
    have hDLt : D ≤ twoLayerIn (centralizer ({t} : Set G)) := by
      have h1 := GrSLit.pLayer_inf_centralizer_le (Y := centralizer ({t} : Set G)) (A := Tz)
        hTzt hTz2
      rw [inf_eq_right.mpr (hCTzT.trans hCTt)] at h1
      exact (le_twoLayerIn_of_isTwoComponentIn hD).trans h1
    obtain ⟨U₁, hU₁, hmvU₁⟩ := exists_moved hDLt hDperf (ne_bot_of_isQuasisimple hDq)
    have hU₁card := card_eq_of_reach hML (hDcls U₁ hU₁ hmvU₁)
    have hlow := (moved_facts hstarTz hJ₂perf hJ₂q hD hmvD).1
    have hup := (moved_facts hDLt hDperf hDq hU₁ hmvU₁).1
    rw [hJ₂card] at hlow
    rw [hU₁card, ← hKZ] at hup
    have hDcard : Nat.card (↥D ⧸ Open.fusionZStar ↥D) = Nat.card (↥K ⧸ Open.fusionZStar ↥K) :=
      le_antisymm hup hlow
    obtain ⟨⟨eJ₂D⟩, -⟩ := (moved_facts hstarTz hJ₂perf hJ₂q hD hmvD).2 (by rw [hJ₂card, hDcard])
    have hDtl : twoLayerIn (D ⊓ centralizer ({t} : Set G)) = D := by
      rw [inf_eq_left.mpr hDCt, twoLayerIn_eq_self hD]
    have htD : t ∈ coreActionKernel D := Sol78.mem_coreActionKernel_of_commute fun k hk =>
      mem_centralizer_singleton_iff.mp (hDCt hk)
    have hDg : MirrorGood J D := ⟨hDq, ⟨(eJ₂D.symm.trans eJ₂K).trans eK⟩, t, ht, htD,
      by rw [hDtl]; exact hDLt, fun U hU hmv => hDcls U hU (by rwa [hDtl] at hmv)⟩
    have hzD : z ∈ coreActionKernel D := Sol78.mem_coreActionKernel_of_commute fun k hk =>
      mem_centralizer_singleton_iff.mp (hCTzz (hD.1 hk))
    have hDz := anchor_at hML hDg hz hzD
    have hDzl : twoLayerIn (D ⊓ centralizer ({z} : Set G)) = D := by
      rw [inf_eq_left.mpr (hD.1.trans hCTzz), twoLayerIn_eq_self hD]
    have hDLz : D ≤ twoLayerIn (centralizer ({z} : Set G)) := by
      rw [← hDzl]; exact hDz.2.2.1
    obtain ⟨U, hU, hmvU⟩ := exists_moved hDLz hDperf (ne_bot_of_isQuasisimple hDq)
    have hUcls := hDz.2.2.2 U hU (by rw [hDzl]; exact hmvU)
    refine ⟨U, hU, fun hc => hmvU ?_, hUcls⟩
    have hLTz : twoLayerIn (centralizer (Tz : Set G)) ≤ normalizer (U : Set G) := by
      have h1 := GrSLit.pLayer_inf_centralizer_le (Y := centralizer ({z} : Set G)) (A := Tz)
        hTzz hTz2
      rw [inf_eq_right.mpr hCTzz] at h1
      exact h1.trans (twoLayerIn_le_normalizer hU)
    exact (le_conjClosure_of_not_le_coreActionKernel hD hstarTz hmvD).trans
      (conjClosure_le_coreActionKernel (hJ₂Kz.trans hc) hLTz)
  refine ⟨hKq, ⟨eK⟩, z, hz, hzQ, hstarz, fun M hM hmv => ?_⟩
  obtain ⟨g, -, rfl⟩ := horb M hM (hmovY M hM hmv)
  obtain ⟨g₁, -, hUg⟩ := horb U hU (hmovY U hU hmvU)
  have h1 : conjugate M₀ g = conjugate U (g₁⁻¹ * g) := by
    rw [hUg, UnbalancedLayer.conjugate_conjugate, ← mul_assoc, mul_inv_cancel, one_mul]
  rw [h1]
  exact hUcls.conj _

end CFSG.ComponentClassification.Foote5.SolMax
