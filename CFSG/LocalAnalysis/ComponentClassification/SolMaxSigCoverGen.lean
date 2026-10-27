module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSigCoverMember
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSigCover

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  (S : Sig36 X t J n e E D)
include S

theorem false_of_isTwoComponentIn_centralizer (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    {H M : Subgroup X} (hMH : M ≤ H) (hMpc : IsPComponent 2 (M.subgroupOf H))
    (hCt : centralizer ({t} : Set X) ≤ H) (htM : t ∈ normalizer (M : Set X))
    (hsup : J ⊔ FooteLit.oddCoreIn M = M)
    (eM : Nonempty (↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n))) {T : Subgroup X}
    (hT2 : IsPGroup 2 T) (hTM : T ≤ normalizer (M : Set X))
    (hTK : ¬ T ≤ UnbalancedLayer.coreActionKernel M) {K : Subgroup X}
    (hKT : FooteLit.IsTwoComponentIn K (centralizer (T : Set X)))
    (hKK : K ≤ UnbalancedLayer.coreActionKernel M)
    (eK : Nonempty (↥K ⧸ pPrimeCore 2 ↥K ≃* alternatingGroup (Fin n))) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn9 := S.nine_le
  obtain ⟨θK⟩ := eK
  set C := centralizer (T : Set X) with hCdef
  obtain ⟨hKC, hKpc⟩ := hKT
  have hT1 : T ≠ ⊥ := fun h => hTK (h ▸ bot_le)
  have hKM : K ≤ normalizer (M : Set X) := fun k hk => (hKK hk).1
  set P := K ⊔ M with hPdef
  have hMP : M ≤ P := le_sup_right
  have hPM : P ≤ normalizer (M : Set X) := sup_le hKM le_normalizer
  set O := FooteLit.oddCoreIn P with hOdef
  have hOP : O ≤ P := map_subtype_le _
  have hPO : P ≤ normalizer (O : Set X) := Sol76.le_normalizer_oddCoreIn P
  have hKO : K ≤ normalizer (O : Set X) := le_sup_left.trans hPO
  have hOMO : FooteLit.oddCoreIn M ≤ O :=
    Sol78H.le_oddCoreIn_of_normal ((map_subtype_le _).trans hMP)
      (fun p hp => mem_normalizer_iff_map_conj_eq.mpr (Sol76.map_conj_oddCoreIn (hPM hp)))
      (Sol76.coprime_card_oddCoreIn M)
  have hc : ⁅K, M⁆ ≤ O := by
    rw [commutator_le]
    intro a ha m hm
    have h1 := (hKK ha).2 m⁻¹ (inv_mem hm)
    have hO : a ∈ normalizer ((FooteLit.oddCoreIn M : Subgroup X) : Set X) :=
      mem_normalizer_iff_map_conj_eq.mpr (Sol76.map_conj_oddCoreIn (hKM ha))
    have h2 := (mem_normalizer_iff.mp hO _).mp h1
    rw [commutatorElement_def,
      show a * m * a⁻¹ * m⁻¹ = a * (m⁻¹⁻¹ * a⁻¹ * m⁻¹ * a) * a⁻¹ by group]
    exact hOMO h2
  set JJ := K ⊔ O with hJJdef
  have hJJP : JJ ≤ P := sup_le le_sup_left hOP
  have hPJJ : P ≤ normalizer (JJ : Set X) :=
    sup_le (le_sup_left.trans le_normalizer)
      (Sol78H.le_normalizer_sup_of_commutator hc (hMP.trans hPO))
  have hOJJ : O ≤ FooteLit.oddCoreIn JJ :=
    Sol78H.le_oddCoreIn_of_normal le_sup_right (hJJP.trans hPO) (Sol76.coprime_card_oddCoreIn P)
  have hsupJJ : K ⊔ FooteLit.oddCoreIn JJ = JJ :=
    le_antisymm (sup_le le_sup_left (map_subtype_le _))
      (sup_le le_sup_left (hOJJ.trans le_sup_right))
  obtain ⟨φJJ⟩ := Sol78H.nonempty_coreQuot_equiv_of_sup le_sup_left hsupJJ
  obtain ⟨hK₂P, -, ⟨θK₂⟩⟩ :=
    isTwoComponentIn_oddResidualIn hJJP hPJJ (by omega) (φJJ.symm.trans θK)
  set K₂ := FooteLit.oddResidualIn JJ with hK₂def
  have hK₂JJ : K₂ ≤ JJ := FooteLit.oddResidualIn_le JJ
  have hKres : FooteLit.oddResidualIn K = K :=
    FooteLit.oddResidualIn_eq_self_of_isPComponent hKC hKpc
  have hKK₂ : K ≤ K₂ :=
    calc K = FooteLit.oddResidualIn K := hKres.symm
      _ ≤ K₂ := FooteLit.oddResidualIn_mono le_sup_left
  obtain ⟨-, hMres, hMq⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 M H hMH).mp hMpc
  have hMn : (M.subgroupOf P).Normal := (normal_subgroupOf_iff_le_normalizer hMP).mpr hPM
  have hMpcP : IsPComponent 2 (M.subgroupOf P) :=
    (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 M P hMP).mpr ⟨hMn.isSubnormal, hMres, hMq⟩
  have hmM : FooteLit.IsSolomonMember M :=
    S.isSolomonMember_of_trivial_pump hMH hMpc hCt htM hsup
  have hTCK : T ≤ centralizer (K : Set X) := le_centralizer_iff.mp hKC
  have hTKn : T ≤ normalizer (K : Set X) :=
    hTCK.trans (Subgroup.centralizer_le_normalizer (K : Set X))
  have hTP : T ≤ normalizer (P : Set X) := Sol76T13.le_normalizer_sup hTKn hTM
  have hTO : T ≤ normalizer (O : Set X) := fun τ hτ =>
    mem_normalizer_iff_map_conj_eq.mpr (Sol76.map_conj_oddCoreIn (hTP hτ))
  have hTJJ : T ≤ normalizer (JJ : Set X) := Sol76T13.le_normalizer_sup hTKn hTO
  have hTK₂ : T ≤ normalizer (K₂ : Set X) := fun τ hτ =>
    Sol78H.mem_normalizer_oddResidualIn (hTJJ hτ)
  have hK₂O : K₂ ⊓ O ≤ FooteLit.oddCoreIn K₂ :=
    Sol78H.le_oddCoreIn_of_normal inf_le_left
      (fun k hk => mem_normalizer_inf_of_mem (le_normalizer hk) (hPO (hK₂P.1 hk)))
      (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
        (Sol76.coprime_card_oddCoreIn P))
  have hTK₂K : T ≤ UnbalancedLayer.coreActionKernel K₂ := by
    intro τ hτ
    refine ⟨hTK₂ hτ, fun k hk => ?_⟩
    have hkJJ : k ∈ O ⊔ K := by
      rw [sup_comm]
      exact hK₂JJ hk
    obtain ⟨o, ho, a, ha, rfl⟩ := Sol76.exists_mul_of_mem_sup_normalizer hKO hkJJ
    have haτ : a * τ = τ * a := (mem_centralizer_iff.mp (hKC ha) τ hτ).symm
    refine hK₂O (mem_inf.mpr ⟨?_, ?_⟩)
    · have h1 : τ⁻¹ * (o * a) * τ⁻¹⁻¹ ∈ K₂ :=
        (mem_normalizer_iff.mp (inv_mem (hTK₂ hτ)) _).mp hk
      rw [inv_inv] at h1
      have h2 := mul_mem (inv_mem hk) h1
      rwa [show (o * a)⁻¹ * (τ⁻¹ * (o * a) * τ) = (o * a)⁻¹ * τ⁻¹ * (o * a) * τ by group]
        at h2
    · have h1 : τ⁻¹ * o * τ⁻¹⁻¹ ∈ O := (mem_normalizer_iff.mp (inv_mem (hTO hτ)) _).mp ho
      rw [inv_inv] at h1
      have h2 : o⁻¹ * (τ⁻¹ * o * τ) ∈ O := mul_mem (inv_mem ho) h1
      have h3 : a⁻¹ * (o⁻¹ * (τ⁻¹ * o * τ)) * a⁻¹⁻¹ ∈ O :=
        (mem_normalizer_iff.mp (inv_mem (hKO ha)) _).mp h2
      rw [inv_inv] at h3
      have h4 : (o * a)⁻¹ * τ⁻¹ * (o * a) * τ = a⁻¹ * (o⁻¹ * (τ⁻¹ * o * τ)) * a := by
        calc (o * a)⁻¹ * τ⁻¹ * (o * a) * τ = a⁻¹ * o⁻¹ * τ⁻¹ * o * (a * τ) := by group
          _ = a⁻¹ * o⁻¹ * τ⁻¹ * o * (τ * a) := by rw [haτ]
          _ = a⁻¹ * (o⁻¹ * (τ⁻¹ * o * τ)) * a := by group
      rw [h4]
      exact h3
  set U := K₂ ⊓ C with hUdef
  have hKU : K ≤ U := le_inf hKK₂ hKC
  have hUC : U ≤ C := inf_le_right
  have hKpcU : IsPComponent 2 (K.subgroupOf U) :=
    UnbalancedCorr.isPComponent_subgroupOf_of_le hKU hUC hKpc
  have hOUK : FooteLit.oddCoreIn U ≤ normalizer (K : Set X) :=
    UnbalancedCorr.pPrimeCore_le_normalizer_of_isPComponent hKU hKpcU
  have hOCK : FooteLit.oddCoreIn C ≤ normalizer (K : Set X) :=
    UnbalancedCorr.pPrimeCore_le_normalizer_of_isPComponent hKC hKpc
  have hUOU : U ⊓ O ≤ FooteLit.oddCoreIn U :=
    Sol78H.le_oddCoreIn_of_normal inf_le_left
      (fun u hu => mem_normalizer_inf_of_mem (le_normalizer hu) (hPO (hK₂P.1 (mem_inf.mp hu).1)))
      (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
        (Sol76.coprime_card_oddCoreIn P))
  have hfix : FooteLit.oddResidualIn (FooteLit.oddCoreIn C ⊔ U) = K := by
    apply le_antisymm
    · refine (closure_le _).mpr fun g hg => ?_
      obtain ⟨hgA, hg2⟩ := hg
      have hA : FooteLit.oddCoreIn C ⊔ U ≤ (U ⊓ O) ⊔ (K ⊔ FooteLit.oddCoreIn C) := by
        refine sup_le (le_sup_of_le_right le_sup_right) fun k hk => ?_
        have hkJJ : k ∈ O ⊔ K := by
          rw [sup_comm]
          exact hK₂JJ (mem_inf.mp hk).1
        obtain ⟨o, ho, a, ha, rfl⟩ := Sol76.exists_mul_of_mem_sup_normalizer hKO hkJJ
        have hoU : o ∈ U := by
          have h1 := mul_mem hk (inv_mem (hKU ha))
          rwa [mul_inv_cancel_right] at h1
        exact mul_mem (mem_sup_left (mem_inf.mpr ⟨hoU, ho⟩)) (mem_sup_right (mem_sup_left ha))
      have hUON : U ⊓ O ≤ normalizer ((K ⊔ FooteLit.oddCoreIn C : Subgroup X) : Set X) :=
        Sol76T13.le_normalizer_sup (hUOU.trans hOUK)
          ((inf_le_left.trans hUC).trans (Sol76.le_normalizer_oddCoreIn C))
      have hUOodd : FooteLit.oddResidualIn (U ⊓ O) ≤ K ⊔ FooteLit.oddCoreIn C := by
        rw [FooteLit.oddResidualIn_eq_bot_of_odd ((Nat.coprime_two_left.mp
          (Sol76.coprime_card_oddCoreIn P)).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right))]
        exact bot_le
      have h1 := FooteLit.mem_of_two_element_of_mem_sup hUON hUOodd (hA hgA) hg2
      have hCodd : FooteLit.oddResidualIn (FooteLit.oddCoreIn C) ≤ K := by
        rw [FooteLit.oddResidualIn_eq_bot_of_odd
          (Nat.coprime_two_left.mp (Sol76.coprime_card_oddCoreIn C))]
        exact bot_le
      rw [sup_comm] at h1
      exact FooteLit.mem_of_two_element_of_mem_sup hOCK hCodd h1 hg2
    · calc K = FooteLit.oddResidualIn K := hKres.symm
        _ ≤ FooteLit.oddResidualIn (FooteLit.oddCoreIn C ⊔ U) :=
          FooteLit.oddResidualIn_mono (le_sup_of_le_right hKU)
  have hmK₂ : FooteLit.IsSolomonMember K₂ := by
    refine ⟨UnbalancedCorr.commutator_eq_of_isPComponent hK₂P.1 hK₂P.2, T, hT1, hT2, hTK₂K, ?_⟩
    show FooteLit.IsTwoComponentIn (FooteLit.oddResidualIn (FooteLit.oddCoreIn C ⊔ U)) C
    rw [hfix]
    exact ⟨hKC, hKpc⟩
  have hMK₂ : M = K₂ := S.eq_of_isPComponent_alt_of_member hT13 hML hSch hMP hK₂P.1 hMpcP
    hK₂P.2 hmM hmK₂ eM ⟨θK₂⟩
  apply hTK
  rw [hMK₂]
  exact hTK₂K

theorem false_of_cover_of_isTwoComponentIn (h33 : Sol78.BalanceLemmaInput)
    (h35 : SignalizerLemma35) (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    {M : Subgroup X} (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (hsup : J ⊔ FooteLit.oddCoreIn M = M) (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n))
    {N : Subgroup X} (θN : ↥N ⧸ pPrimeCore 2 ↥N ≃* alternatingGroup (Fin n)) {Y : Subgroup X}
    (hYN : Y ≤ N) (hYH : Y ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hYK : Y ≤ UnbalancedLayer.coreActionKernel M)
    (hsupY : Y ⊔ (pPrimeCore 2 ↥N).map N.subtype = N) {T : Subgroup X} (hT2 : IsPGroup 2 T)
    (hTM : T ≤ normalizer (M : Set X)) (hTK : ¬ T ≤ UnbalancedLayer.coreActionKernel M)
    (hKT : FooteLit.IsTwoComponentIn (FooteLit.oddResidualIn N) (centralizer (T : Set X))) :
    False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn9 := S.nine_le
  have hON := S.pPrimeCore_le_of_cover h33 h35 hT13 hML hSch hMH hMpc hHN θ hsup θN hYN hYH hYK
    hsupY
  have hNH : N ≤ normalizer (Sol78.signalizerCompletion E E : Set X) := by
    rw [← hsupY]
    exact sup_le hYH hON
  have hKNK : FooteLit.oddResidualIn N ≤ UnbalancedLayer.coreActionKernel M := by
    have hON' : FooteLit.oddCoreIn N ≤
        normalizer ((N ⊓ UnbalancedLayer.coreActionKernel M : Subgroup X) : Set X) := by
      intro o ho
      have hoN : o ∈ N := map_subtype_le _ ho
      exact mem_normalizer_inf_of_mem (le_normalizer hoN)
        (mem_normalizer_coreActionKernel (hHN (hNH hoN)))
    have hR : FooteLit.oddResidualIn (FooteLit.oddCoreIn N) ≤
        N ⊓ UnbalancedLayer.coreActionKernel M := by
      rw [FooteLit.oddResidualIn_eq_bot_of_odd
        (Nat.coprime_two_left.mp (Sol76.coprime_card_oddCoreIn N))]
      exact bot_le
    have hNle : N ≤ FooteLit.oddCoreIn N ⊔ (N ⊓ UnbalancedLayer.coreActionKernel M) := by
      calc N = Y ⊔ FooteLit.oddCoreIn N := hsupY.symm
        _ ≤ FooteLit.oddCoreIn N ⊔ (N ⊓ UnbalancedLayer.coreActionKernel M) :=
          sup_le (le_sup_of_le_right (le_inf hYN hYK)) le_sup_left
    refine (closure_le _).mpr fun x hx => ?_
    obtain ⟨hxN, hx2⟩ := hx
    exact (mem_inf.mp (FooteLit.mem_of_two_element_of_mem_sup hON' hR (hNle hxN) hx2)).2
  obtain ⟨-, -, ⟨θKN⟩⟩ := isTwoComponentIn_oddResidualIn le_rfl le_normalizer (by omega) θN
  have hCt := S.centralizer_le_normalizer_completion h33 h35 hT13 hML hSch
  exact S.false_of_isTwoComponentIn_centralizer hT13 hML hSch hMH hMpc hCt
    (hHN (hCt (mem_centralizer_singleton_iff.mpr rfl))) hsup ⟨θ⟩ hT2 hTM hTK hKT hKNK ⟨θKN⟩

end Sig36

end CFSG.ComponentClassification.SolMax
