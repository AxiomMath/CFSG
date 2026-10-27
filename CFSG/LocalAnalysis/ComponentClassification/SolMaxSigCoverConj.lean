module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxNineH
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxNineE

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}

theorem false_of_cover_of_conj_fixedLayer (S : Sig36 X t J n e E D)
    (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput) {M : Subgroup X}
    (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (hsup : J ⊔ FooteLit.oddCoreIn M = M)
    (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n))
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin n)} (hρ : IsPermAction θ ρ) {T : Subgroup X}
    (hTH : T ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hTK : T ≤ UnbalancedLayer.coreActionKernel M) (hT2 : IsPGroup 2 T) (hT1 : T ≠ ⊥) {x s : X}
    (hTx : T.map (MulAut.conj x).toMonoidHom ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hsT : s ∈ T.map (MulAut.conj x).toMonoidHom) (hs1 : ρ ⟨s, hHN (hTx hsT)⟩ ≠ 1)
    {Y : Subgroup X} (hYL : Y ≤ (GSLit.fixedLayer M T).map (MulAut.conj x).toMonoidHom)
    (hYH : Y ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hsupY : Y ⊔ (pPrimeCore 2 ↥((GSLit.fixedLayer M T).map (MulAut.conj x).toMonoidHom)).map
      ((GSLit.fixedLayer M T).map (MulAut.conj x).toMonoidHom).subtype =
        (GSLit.fixedLayer M T).map (MulAut.conj x).toMonoidHom) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  have hMq : IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 M H hMH).mp hMpc).2.2
  have hMsub : (M.subgroupOf H).IsSubnormal := hMpc.choose_spec.2.1
  set L := GSLit.fixedLayer M T with hLdef
  have hCT : centralizer (T : Set X) ≤ H :=
    S.centralizer_le_of_le_coreActionKernel h33 h35 hT13 hML hSch hMH hMpc hHN θ hsup hTH hTK hT2
      hT1
  have hle := GSLit.fixedLayer_le_inf M T
  have hLM : L ≤ M := hle.trans inf_le_left
  have hLC : L ≤ centralizer (T : Set X) := hle.trans inf_le_right
  have hLpc : IsPComponent 2 (L.subgroupOf (centralizer (T : Set X))) := by
    have h1 := GSLit.fixedLayer_isPComponent hMH hMsub hTH hTK hT2 hMq
    rwa [inf_eq_right.mpr hCT] at h1
  obtain ⟨hLsup, -⟩ := GSLit.fixedLayer_sup_pPrimeCore hMq hTK hT2
  obtain ⟨θL, -⟩ := exists_coreQuot_of_sup hLM hLsup θ
  set N := L.map (MulAut.conj x).toMonoidHom with hNdef
  have hNC : N ≤ centralizer ((T.map (MulAut.conj x).toMonoidHom : Subgroup X) : Set X) := by
    rw [← map_conj_centralizer]
    exact map_mono hLC
  have hNpc : IsPComponent 2 (N.subgroupOf
      (centralizer ((T.map (MulAut.conj x).toMonoidHom : Subgroup X) : Set X))) := by
    rw [← map_conj_centralizer]
    exact isPComponent_map_conj hLC hLpc x
  let θN : ↥N ⧸ pPrimeCore 2 ↥N ≃* alternatingGroup (Fin n) :=
    (Sol78.coreQuotCongr (L.equivMapOfInjective (MulAut.conj x).toMonoidHom
      (MulAut.conj x).injective)).symm.trans θL
  have hNs : N ≤ centralizer ({s} : Set X) :=
    hNC.trans (centralizer_le (Set.singleton_subset_iff.mpr hsT))
  exact S.false_of_cover_of_centralizer h33 h35 hT13 hML hSch hMH hMpc hHN hsup θ hρ (hTx hsT)
    hs1 θN hYL hYH (hYL.trans hNs) hsupY (hT2.map _) hTx hsT
    (by rw [FooteLit.oddResidualIn_eq_self_of_isPComponent hNC hNpc]; exact ⟨hNC, hNpc⟩)

theorem false_of_conj_of_centralizer_le (S : Sig36 X t J n e E D)
    (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput) {M : Subgroup X}
    (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (hsup : J ⊔ FooteLit.oddCoreIn M = M)
    (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n))
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin n)} (hρ : IsPermAction θ ρ) {Q : Subgroup X}
    (hQH : Q ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hQK : Q ≤ UnbalancedLayer.coreActionKernel M) (hQ2 : IsPGroup 2 Q) (htQ : t ∈ Q)
    {x w y : X} (hwx : w ∈ Q.map (MulAut.conj x).toMonoidHom)
    (hCw : centralizer ({w} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hyx : y ∈ Q.map (MulAut.conj x).toMonoidHom)
    (hyH : y ∈ normalizer (Sol78.signalizerCompletion E E : Set X)) (hy1 : ρ ⟨y, hHN hyH⟩ ≠ 1) :
    False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  have hn9 := S.nine_le
  have hMq : IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 M H hMH).mp hMpc).2.2
  set P := Q.map (MulAut.conj x).toMonoidHom with hPdef
  have hCP : centralizer (P : Set X) ≤ H :=
    (centralizer_le (Set.singleton_subset_iff.mpr hwx)).trans hCw
  have hLC : GSLit.fixedLayer M Q ≤ centralizer (Q : Set X) :=
    (GSLit.fixedLayer_le_inf M Q).trans inf_le_right
  have hK'C : (GSLit.fixedLayer M Q).map (MulAut.conj x).toMonoidHom ≤ centralizer (P : Set X) := by
    rw [hPdef, ← map_conj_centralizer]
    exact map_mono hLC
  have hK'H := hK'C.trans hCP
  have hQ1 : Q ≠ ⊥ := by
    intro h
    have h1 := htQ
    rw [h, mem_bot] at h1
    have h2 := S.pair.1.1
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  obtain ⟨z, hzQ, hzo, hzZ⟩ := Sol78H.exists_central_involution hQ1 hQ2
  set s := (MulAut.conj x).toMonoidHom z with hsdef
  have hsP : s ∈ P := ⟨z, hzQ, rfl⟩
  have hsC : s ∈ centralizer (P : Set X) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨q, hq, rfl⟩
    rw [hsdef, ← map_mul, ← map_mul, hzZ q hq]
  have hsH : s ∈ H := hCP hsC
  by_cases hsK : s ∈ UnbalancedLayer.coreActionKernel M
  ·
    have hs2 : IsPGroup 2 (zpowers s) := (hQ2.map _).to_le (zpowers_le.mpr hsP)
    have hs1 : zpowers s ≠ ⊥ := by
      intro h
      apply (show z ≠ 1 from fun h1 => by rw [h1, orderOf_one] at hzo; omega)
      apply (MulAut.conj x).injective
      rw [map_one]
      exact zpowers_eq_bot.mp h
    have hCs := S.centralizer_le_of_le_coreActionKernel h33 h35 hT13 hML hSch hMH hMpc hHN θ hsup
      (zpowers_le.mpr hsH) (zpowers_le.mpr hsK) hs2 hs1
    have hPH : P ≤ H := fun p hp => hCs (by
      rw [UnbalancedLayer.centralizer_zpowers_eq, mem_centralizer_singleton_iff]
      exact mem_centralizer_iff.mp hsC p hp)
    exact S.false_of_cover_of_conj_fixedLayer h33 h35 hT13 hML hSch hMH hMpc hHN hsup θ hρ hQH hQK
      hQ2 hQ1 hPH hyx hy1 le_rfl hK'H (sup_eq_left.mpr (map_subtype_le _))
  ·
    have hBQ : zpowers z ≤ Q := zpowers_le.mpr hzQ
    have hB1 : zpowers z ≠ ⊥ := fun h => by
      rw [zpowers_eq_bot] at h
      rw [h, orderOf_one] at hzo
      omega
    have hBx : (zpowers z).map (MulAut.conj x).toMonoidHom ≤ H := by
      rw [MonoidHom.map_zpowers]
      exact zpowers_le.mpr hsH
    have hsB : s ∈ (zpowers z).map (MulAut.conj x).toMonoidHom := ⟨z, mem_zpowers z, rfl⟩
    have hs1 : ρ ⟨s, hHN (hBx hsB)⟩ ≠ 1 := fun h => hsK (hρ.mem_coreActionKernel _ h)
    obtain ⟨hnest, hnsup⟩ := GSLit.fixedLayer_nested hMq hQK hQ2 hBQ
    have hsupY := congrArg (Subgroup.map (MulAut.conj x).toMonoidHom) hnsup
    rw [Subgroup.map_sup] at hsupY
    have h1 := Sol76.map_oddCoreIn (MulAut.conj x) (GSLit.fixedLayer M (zpowers z))
    rw [FooteLit.oddCoreIn, FooteLit.oddCoreIn] at h1
    rw [h1] at hsupY
    exact S.false_of_cover_of_conj_fixedLayer h33 h35 hT13 hML hSch hMH hMpc hHN hsup θ hρ
      (hBQ.trans hQH) (hBQ.trans hQK) (hQ2.to_le hBQ) hB1 hBx hsB hs1 (map_mono hnest) hK'H hsupY

end Sig36

end CFSG.ComponentClassification.SolMax
