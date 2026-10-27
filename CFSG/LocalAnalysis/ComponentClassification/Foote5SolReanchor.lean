module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5SolPiece
public import CFSG.LocalAnalysis.ComponentClassification.Foote5SolAscent

public section

namespace CFSG.ComponentClassification.Foote5.SolMax

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76

variable {G : Type} [Group G] [Finite G]

theorem reanchor {J K : Subgroup G} {w c : G} (hML : GSMirrorMaximal J)
    (hKq : IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K))
    (hKZ : Nat.card (↥K ⧸ Open.fusionZStar ↥K) = Nat.card (↥J ⧸ Open.fusionZStar ↥J))
    (hw : orderOf w = 2) (hc : orderOf c = 2) (hwc : w * c = c * w)
    (hwK : w ∈ coreActionKernel K) (hcK : c ∈ coreActionKernel K)
    (hstar : twoLayerIn (K ⊓ centralizer ({w} : Set G)) ≤ twoLayerIn (centralizer ({w} : Set G)))
    (hcls : ∀ V : Subgroup G, IsTwoComponentIn V (centralizer ({w} : Set G)) →
      ¬ twoLayerIn (K ⊓ centralizer ({w} : Set G)) ≤ coreActionKernel V → GSMirrorReach J V) :
    twoLayerIn (K ⊓ centralizer ({c} : Set G)) ≤ twoLayerIn (centralizer ({c} : Set G)) ∧
    ∀ M : Subgroup G, IsTwoComponentIn M (centralizer ({c} : Set G)) →
      ¬ twoLayerIn (K ⊓ centralizer ({c} : Set G)) ≤ coreActionKernel M → GSMirrorReach J M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Cw := centralizer ({w} : Set G) with hCw
  set Cc := centralizer ({c} : Set G) with hCc
  have hA2 : IsPGroup 2 (zpowers w) := isPGroup_zpowers_of_orderOf hw
  have hc2 : IsPGroup 2 (zpowers c) := isPGroup_zpowers_of_orderOf hc
  have hcA : c ∈ normalizer ((zpowers w : Subgroup G) : Set G) := by
    refine centralizer_le_normalizer _ ?_
    rw [centralizer_zpowers', mem_centralizer_singleton_iff]
    exact hwc.symm
  have hwC : w ∈ normalizer ((zpowers c : Subgroup G) : Set G) := by
    refine centralizer_le_normalizer _ ?_
    rw [centralizer_zpowers', mem_centralizer_singleton_iff]
    exact hwc
  have hAQ : zpowers w ≤ coreActionKernel K := zpowers_le.mpr hwK
  have hcQ : zpowers c ≤ coreActionKernel K := zpowers_le.mpr hcK
  have hBQ : zpowers w ⊔ zpowers c ≤ coreActionKernel K := sup_le hAQ hcQ
  have hB2 : IsPGroup 2 ↥(zpowers w ⊔ zpowers c) := by
    have := IsPGroup.to_sup_of_normal_right' hc2 hA2 (zpowers_le.mpr hcA)
    rwa [sup_comm] at this
  have hc2A : c ^ 2 ∈ zpowers w := by
    rw [← hc, pow_orderOf_eq_one]
    exact one_mem _
  have hCB := centralizer_zpowers_sup w c
  have hstarA : twoLayerIn (K ⊓ centralizer ((zpowers w : Subgroup G) : Set G)) ≤
      twoLayerIn (centralizer ((zpowers w : Subgroup G) : Set G)) := by
    rw [centralizer_zpowers']; exact hstar
  have htypA : ∀ V : Subgroup G, IsTwoComponentIn V (centralizer ((zpowers w : Subgroup G) :
      Set G)) → ¬ twoLayerIn (K ⊓ centralizer ((zpowers w : Subgroup G) : Set G)) ≤
        coreActionKernel V →
      Nat.card (↥V ⧸ Open.fusionZStar ↥V) = Nat.card (↥K ⧸ Open.fusionZStar ↥K) := by
    intro V hV hmv
    rw [centralizer_zpowers'] at hV hmv
    rw [hKZ]
    exact card_eq_of_reach hML (hcls V hV hmv)
  have hstarB := star_sup_zpowers hKq hA2 hAQ hc2 hcK hcA hc2A hstarA htypA
  have hBc : zpowers w ⊔ zpowers c ≤ normalizer ((zpowers c : Subgroup G) : Set G) :=
    sup_le (zpowers_le.mpr hwC) le_normalizer
  have hstarc' := twoLayer_inf_centralizer_le_of_normalizes hKq hc2 hB2 le_sup_right hBc hBQ
    hstarB
  rw [centralizer_zpowers'] at hstarc'
  refine ⟨hstarc', fun M hM hmove => ?_⟩
  rw [hCB] at hstarB
  set J₂ := twoLayerIn (K ⊓ (Cw ⊓ Cc)) with hJ₂
  obtain ⟨hJ₂c, hJ₂r, hJ₂sup, ⟨eJ₂⟩⟩ := cover_facts hKq inf_le_left
    (inf_centralizer_sup_oddCoreIn_eq hB2 hBQ)
  rw [hCB] at hJ₂c hJ₂r hJ₂sup eJ₂
  have hJ₂perf : ⁅J₂, J₂⁆ = J₂ := by
    rw [hJ₂, hJ₂r]
    exact UnbalancedCorr.commutator_eq_of_isPComponent hJ₂c.1 hJ₂c.2
  have hJ₂q : IsQuasisimple (↥J₂ ⧸ pPrimeCore 2 ↥J₂) := by
    rw [hJ₂, hJ₂r]
    exact LocalCores.isQuasisimple_of_mulEquiv eJ₂.symm hKq
  have hJ₂card : Nat.card (↥J₂ ⧸ Open.fusionZStar ↥J₂) =
      Nat.card (↥K ⧸ Open.fusionZStar ↥K) := by
    rw [hJ₂, hJ₂r]
    exact Nat.card_congr (Sol78.fusionZStarQuotOfCore eJ₂).toEquiv
  have hJ₂sup' : J₂ ⊔ oddCoreIn K = K := by rw [hJ₂, hJ₂r]; exact hJ₂sup
  have hJ₂Kc : J₂ ≤ twoLayerIn (K ⊓ Cc) := by
    have h1 := twoLayerIn_inf_centralizer_anti hKq hc2 hB2 hcQ hBQ le_sup_right
    rw [hCB, centralizer_zpowers'] at h1
    exact h1
  have hJ₂Kw : J₂ ≤ twoLayerIn (K ⊓ Cw) := by
    have h1 := twoLayerIn_inf_centralizer_anti hKq hA2 hB2 hAQ hBQ le_sup_left
    rw [hCB, centralizer_zpowers'] at h1
    exact h1
  obtain ⟨hKcc, hKcr, -, -⟩ := cover_facts hKq inf_le_left
    (inf_centralizer_sup_oddCoreIn_eq hc2 hcQ)
  rw [centralizer_zpowers'] at hKcc hKcr
  have hKcperf : ⁅twoLayerIn (K ⊓ Cc), twoLayerIn (K ⊓ Cc)⁆ = twoLayerIn (K ⊓ Cc) := by
    rw [hKcr]
    exact UnbalancedCorr.commutator_eq_of_isPComponent hKcc.1 hKcc.2
  have hKcK : twoLayerIn (K ⊓ Cc) ≤ K := (map_subtype_le _).trans inf_le_left
  have hJ₂M : ¬ J₂ ≤ coreActionKernel M := fun h => hmove
    (le_coreActionKernel_of_cover hJ₂Kc hKcK hJ₂sup' hKcperf
      (hstarc'.trans (twoLayerIn_le_normalizer hM)) h)
  have hcw : c ∈ Cw := mem_centralizer_singleton_iff.mpr hwc.symm
  have hwc' : w ∈ Cc := mem_centralizer_singleton_iff.mpr hwc
  let Pk : Subgroup G → Prop := fun P => ∃ V : Subgroup G, IsTwoComponentIn V Cw ∧
    GSMirrorReach J V ∧ P ≤ V ⊔ conjugate V c ∧ (conjugate V c = V → c ∈ coreActionKernel V)
  have hPk_inv : ∀ P : Subgroup G, ∀ x ∈ Cw ⊓ Cc, Pk P →
      Pk (P.map (MulAut.conj x).toMonoidHom) := by
    rintro P x hx ⟨V, hV, hVcls, hPV, hfix⟩
    obtain ⟨hxw, hxc⟩ := mem_inf.mp hx
    have hxc' : x * c = c * x := mem_centralizer_singleton_iff.mp hxc
    have hCwφ : Cw.map (MulAut.conj x).toMonoidHom = Cw :=
      mem_normalizer_iff_map_conj_eq.mp (le_normalizer hxw)
    refine ⟨V.map (MulAut.conj x).toMonoidHom, ?_, ?_, ?_, ?_⟩
    · have := Sol76.isTwoComponentIn_map (MulAut.conj x) hV
      rwa [hCwφ] at this
    · have h1 : V.map (MulAut.conj x).toMonoidHom = conjugate V x⁻¹ := by
        unfold conjugate; rw [inv_inv]
      rw [h1]
      exact hVcls.conj x⁻¹
    · calc P.map (MulAut.conj x).toMonoidHom
          ≤ (V ⊔ conjugate V c).map (MulAut.conj x).toMonoidHom := map_mono hPV
        _ = V.map (MulAut.conj x).toMonoidHom ⊔
            conjugate (V.map (MulAut.conj x).toMonoidHom) c := by
          rw [Subgroup.map_sup, map_conj_conjugate_of_commute V hxc']
    · intro hVc'
      have hVc : conjugate V c = V := by
        have h1 : (conjugate V c).map (MulAut.conj x).toMonoidHom =
            V.map (MulAut.conj x).toMonoidHom := by
          rw [map_conj_conjugate_of_commute V hxc', hVc']
        exact Subgroup.map_injective (MulAut.conj x).injective h1
      have h3 : (MulAut.conj x) c ∈ (coreActionKernel V).map (MulAut.conj x).toMonoidHom :=
        mem_map_of_mem _ (hfix hVc)
      rw [Sol76.map_coreActionKernel (MulAut.conj x) V] at h3
      have h4 : (MulAut.conj x) c = c := by
        rw [MulAut.conj_apply, hxc', mul_inv_cancel_right]
      rwa [h4] at h3
  have hmovP : ∀ P : Subgroup G, IsTwoComponentIn P (Cw ⊓ Cc) → ¬ J₂ ≤ coreActionKernel P →
      Pk P := by
    intro P hP hmvP
    have hPL : P ≤ (pLayer ↥Cw 2).map Cw.subtype := by
      have h1 := GrSLit.pLayer_inf_centralizer_le (Y := Cw) (A := zpowers c)
        (zpowers_le.mpr hcw) hc2
      rw [centralizer_zpowers'] at h1
      exact (le_twoLayerIn_of_isTwoComponentIn hP).trans h1
    obtain ⟨V, hVCw, hVp, hPV, -⟩ := UnbalancedCorr.exists_orbit_component hc hcw
      (by rw [inf_comm]; exact hP.1) (by rw [inf_comm]; exact hP.2) hPL
    have hV : IsTwoComponentIn V Cw := ⟨hVCw, hVp⟩
    have hVc : IsTwoComponentIn (conjugate V c) Cw := by
      have h1 := Sol76.isTwoComponentIn_map (MulAut.conj c⁻¹) hV
      have h2 : Cw.map (MulAut.conj c⁻¹).toMonoidHom = Cw :=
        mem_normalizer_iff_map_conj_eq.mp (le_normalizer (inv_mem hcw))
      rw [h2] at h1
      exact h1
    have hJ₂Cw : J₂ ≤ Cw := hJ₂Kw.trans ((map_subtype_le _).trans inf_le_right)
    have hJ₂NP : J₂ ≤ normalizer (P : Set G) := hstarB.trans (twoLayerIn_le_normalizer hP)
    have hcc : conjugate (conjugate V c) c = V := by
      rw [UnbalancedLayer.conjugate_conjugate, ← pow_two, ← hc, pow_orderOf_eq_one,
        UnbalancedLayer.conjugate_one]
    have key : ∃ V' : Subgroup G, IsTwoComponentIn V' Cw ∧ P ≤ V' ⊔ conjugate V' c ∧
        ¬ J₂ ≤ coreActionKernel V' := by
      by_cases h1 : J₂ ≤ coreActionKernel V
      · by_cases h2 : J₂ ≤ coreActionKernel (conjugate V c)
        · exact absurd (le_coreActionKernel_of_le_sup hV hVc hPV hJ₂Cw hJ₂NP h1 h2) hmvP
        · refine ⟨conjugate V c, hVc, ?_, h2⟩
          rw [hcc, sup_comm]
          exact hPV
      · exact ⟨V, hV, hPV, h1⟩
    obtain ⟨V', hV', hPV', hmvV'⟩ := key
    have hKwV' : ¬ twoLayerIn (K ⊓ Cw) ≤ coreActionKernel V' := fun h => hmvV' (hJ₂Kw.trans h)
    have hV'cls := hcls V' hV' hKwV'
    refine ⟨V', hV', hV'cls, hPV', fun hV'c => ?_⟩
    have hJ₂L : J₂ ≤ twoLayerIn Cw := hJ₂Kw.trans hstar
    have hcard : Nat.card (↥J₂ ⧸ Open.fusionZStar ↥J₂) =
        Nat.card (↥V' ⧸ Open.fusionZStar ↥V') := by
      rw [hJ₂card, hKZ, card_eq_of_reach hML hV'cls]
    have hmf := (moved_facts hJ₂L hJ₂perf hJ₂q hV' hmvV').2 hcard
    refine hmf.2 c hcw (fun r hr => ?_) (UnbalancedLayer.mem_normalizer_of_conjugate_eq hV'c)
    have hr' : r ∈ Cc := (mem_inf.mp (mem_inf.mp ((map_subtype_le _) hr)).2).2
    exact (mem_centralizer_singleton_iff.mp hr').symm
  have hJ₂D := le_iSup_of_moved Pk (fun P _ x hx h => hPk_inv P x hx h) hstarB hJ₂perf hmovP
  set 𝒰 : Set (Subgroup G) := {M' | IsTwoComponentIn M' Cc ∧ GSMirrorReach J M'} with h𝒰
  have hD𝒰 : (⨆ (P : Subgroup G) (_ : IsTwoComponentIn P (Cw ⊓ Cc) ∧ Pk P), P) ≤
      ⨆ U ∈ 𝒰, U := by
    refine iSup₂_le fun P hP' => ?_
    obtain ⟨hP, V, hV, hVcls, hPV, hfix⟩ := hP'
    have hPLc : P ≤ (pLayer ↥Cc 2).map Cc.subtype := by
      have h1 := GrSLit.pLayer_inf_centralizer_le (Y := Cc) (A := zpowers w)
        (zpowers_le.mpr hwc') hA2
      rw [centralizer_zpowers', inf_comm] at h1
      exact (le_twoLayerIn_of_isTwoComponentIn hP).trans h1
    obtain ⟨M', hM'Cc, hM'p, hPM', -⟩ := UnbalancedCorr.exists_orbit_component hw hwc' hP.1
      hP.2 hPLc
    have hM' : IsTwoComponentIn M' Cc := ⟨hM'Cc, hM'p⟩
    have hM'cls := reach_of_piece hw hc hwc hV hVcls hPV hfix hP hM' hPM'
    have hM'w : IsTwoComponentIn (conjugate M' w) Cc := by
      have h1 := Sol76.isTwoComponentIn_map (MulAut.conj w⁻¹) hM'
      have h2 : Cc.map (MulAut.conj w⁻¹).toMonoidHom = Cc :=
        mem_normalizer_iff_map_conj_eq.mp (le_normalizer (inv_mem hwc'))
      rw [h2] at h1
      exact h1
    calc P ≤ M' ⊔ conjugate M' w := hPM'
      _ ≤ ⨆ U ∈ 𝒰, U := sup_le (le_iSup₂_of_le M' ⟨hM', hM'cls⟩ le_rfl)
          (le_iSup₂_of_le (conjugate M' w) ⟨hM'w, hM'cls.conj w⟩ le_rfl)
  exact (mem_of_not_le_coreActionKernel (fun U hU => hU.1) (hJ₂D.trans hD𝒰) hM hJ₂M).2

end CFSG.ComponentClassification.Foote5.SolMax
