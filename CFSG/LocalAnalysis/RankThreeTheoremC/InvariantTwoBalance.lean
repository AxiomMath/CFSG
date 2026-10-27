module

public import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoConstrained
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityKFacts
import CFSG.LocalAnalysis.RankThreeTheoremC.HasPrimeConstraintBridge
import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityRank
import CFSG.LocalAnalysis.AGLEmbedding.Signalizer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem glbPrimeCore_map_automorphism_le (p : ℕ) (H : Subgroup G) (φ : MulAut G) :
    (GLBPrimeCore p H).map φ.toMonoidHom ≤ GLBPrimeCore p (H.map φ.toMonoidHom) := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le ?_
  rintro N ⟨hNH, hnormal, hcop⟩
  rw [← Subgroup.map_le_iff_le_comap]
  refine le_sSup ⟨Subgroup.map_mono hNH, ?_, ?_⟩
  · rw [Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_mono hNH)]
    exact (Subgroup.map_mono ((Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mp hnormal)).trans
      (Subgroup.le_normalizer_map φ.toMonoidHom)
  · rwa [Subgroup.card_map_of_injective φ.injective]

omit [Finite G] in
theorem glbPrimeCore_map_automorphism (p : ℕ) (H : Subgroup G) (φ : MulAut G) :
    (GLBPrimeCore p H).map φ.toMonoidHom = GLBPrimeCore p (H.map φ.toMonoidHom) := by
  refine le_antisymm (glbPrimeCore_map_automorphism_le p H φ) ?_
  apply (Subgroup.map_le_map_iff_of_injective (f := φ.symm.toMonoidHom) φ.symm.injective).mp
  rw [map_automorphism_symm_map]
  have hinv := glbPrimeCore_map_automorphism_le p (H.map φ.toMonoidHom) φ.symm
  rwa [map_automorphism_symm_map] at hinv

omit [Finite G] in
theorem signalizer_le_glbPrimeCore_map_conj {p : ℕ} {D H : Subgroup G} {g : G}
    (hg : g ∈ normalizer (D : Set G))
    (h : ∀ Y : Subgroup G, Y ≤ H → p.Coprime (Nat.card Y) → D ≤ normalizer (Y : Set G) →
      Y ≤ GLBPrimeCore p H)
    {Y : Subgroup G} (hYH : Y ≤ H.map (MulAut.conj g).toMonoidHom) (hY : p.Coprime (Nat.card Y))
    (hDY : D ≤ normalizer (Y : Set G)) :
    Y ≤ GLBPrimeCore p (H.map (MulAut.conj g).toMonoidHom) := by
  set φ : MulAut G := MulAut.conj g
  have hDg : D.map φ.symm.toMonoidHom = D := by
    have hg' : D.map φ.toMonoidHom = D := mem_normalizer_iff_map_conj_eq.mp hg
    have h' := map_automorphism_symm_map D φ
    rwa [hg'] at h'
  have hYH' : Y.map φ.symm.toMonoidHom ≤ H := by
    have h' := Subgroup.map_mono (f := φ.symm.toMonoidHom) hYH
    rwa [map_automorphism_symm_map] at h'
  have hDY' : D ≤ normalizer (Y.map φ.symm.toMonoidHom : Set G) := by
    have h' := (Subgroup.map_mono (f := φ.symm.toMonoidHom) hDY).trans
      (Subgroup.le_normalizer_map φ.symm.toMonoidHom)
    rwa [hDg] at h'
  have hYcop : p.Coprime (Nat.card (Y.map φ.symm.toMonoidHom)) := by
    rwa [Subgroup.card_map_of_injective φ.symm.injective]
  have hYO := h _ hYH' hYcop hDY'
  have hback : (Y.map φ.symm.toMonoidHom).map φ.toMonoidHom = Y := by
    have h' := map_automorphism_symm_map Y φ.symm
    rwa [MulEquiv.symm_symm] at h'
  calc Y = (Y.map φ.symm.toMonoidHom).map φ.toMonoidHom := hback.symm
    _ ≤ (GLBPrimeCore p H).map φ.toMonoidHom := Subgroup.map_mono hYO
    _ ≤ GLBPrimeCore p (H.map φ.toMonoidHom) := glbPrimeCore_map_automorphism_le p H φ

theorem ExtremalObstruction.signalizer_le_glbPrimeCore_normalizer_zpowers (hS : Setting G)
    (hD1 : TheoremD1 G) (hKF1 : KF1At G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G)
    (hp5 : 5 ≤ p) {P : Sylow p G} {M D : Subgroup G} (hext : ExtremalObstruction p P M D)
    (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G)) (hDab : IsMulCommutative D) {z : G}
    (hzD : z ∈ D) (hz1 : z ≠ 1) (hzc : z ∈ centralizer (P : Set G)) (hzp : z ^ p = 1)
    (hN₀M : normalizer ((zpowers z : Subgroup G) : Set G) ≤ M) {Y : Subgroup G}
    (hYN : Y ≤ normalizer ((zpowers z : Subgroup G) : Set G)) (hY : p.Coprime (Nat.card Y))
    (hDY : D ≤ normalizer (Y : Set G)) :
    Y ≤ GLBPrimeCore p (normalizer ((zpowers z : Subgroup G) : Set G)) := by
  have hprime := sigmaA_prime p hp
  have hodd := sigmaA_odd p hp
  have : Fact p.Prime := ⟨hprime⟩
  have hDP : D ≤ (P : Subgroup G) := hext.obstruction.2.1
  have hzH : z ∈ normalizer ((zpowers z : Subgroup G) : Set G) := le_normalizer (mem_zpowers z)
  have hPN₀ : (P : Subgroup G) ≤ normalizer ((zpowers z : Subgroup G) : Set G) :=
    le_normalizer_zpowers_of_le_centralizer hzc
  have hCD : centralizer (D : Set G) ≤ M :=
    (centralizer_le (Set.singleton_subset_iff.mpr hzD)).trans
      ((centralizer_singleton_le_normalizer_zpowers z).trans hN₀M)
  have hcon := hext.isPConstrained_of_five_le hS hKF1 hp hp5 hPD hPN₀
    (hS.normalizer_zpowers_ne_top hz1) hzH hzD hz1 hzc hzp (normal_zpowers_subtype_mk z hzH)
  exact CFSG.AGLEmbedding.signalizer_le_glbPrimeCore_of_contains hprime hodd
    (hasPrimeConstraint_of_isPConstrained hcon) (P.isPGroup'.to_le hDP) (hDP.trans hPN₀)
    (fun y _ hyC hyo => hext.mem_of_mem_centralizer_of_isMulCommutative hS hD1 hp hDab hCD hyC
      (by rw [← hyo]; exact pow_orderOf_eq_one y)) hYN hY hDY

theorem ExtremalObstruction.inf_centralizer_le_glbPrimeCore_of_coprime (hS : Setting G)
    (hD1 : TheoremD1 G) (hKF1 : KF1At G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G)
    (hp5 : 5 ≤ p) {P : Sylow p G} {M D : Subgroup G} (hext : ExtremalObstruction p P M D)
    (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G)) (hDab : IsMulCommutative D) {z : G}
    (hzD : z ∈ D) (hz1 : z ≠ 1) (hzc : z ∈ centralizer (P : Set G)) (hzp : z ^ p = 1)
    (hN₀M : normalizer ((zpowers z : Subgroup G) : Set G) ≤ M) {T : Subgroup G}
    (hT : p.Coprime (Nat.card T)) (hDT : D ≤ normalizer (T : Set G)) {d : G} (hdD : d ∈ D)
    (hd1 : d ≠ 1) :
    T ⊓ centralizer ({d} : Set G) ≤
      GLBPrimeCore p (normalizer ((zpowers d : Subgroup G) : Set G)) := by
  have hCD : centralizer (D : Set G) ≤ M :=
    (centralizer_le (Set.singleton_subset_iff.mpr hzD)).trans
      ((centralizer_singleton_le_normalizer_zpowers z).trans hN₀M)
  obtain ⟨g, hgD, hgz⟩ := hext.exists_mem_normalizer_zpowers_eq hS hD1 hp hPD hDab hCD hzD hz1
    hzc hN₀M hdD hd1
  have hNd : normalizer ((zpowers d : Subgroup G) : Set G) =
      (normalizer ((zpowers z : Subgroup G) : Set G)).map (MulAut.conj g).toMonoidHom := by
    rw [hgz, Subgroup.map_equiv_normalizer_eq]
  have hdC : D ≤ centralizer ({d} : Set G) :=
    (le_centralizer_iff_isMulCommutative.mpr hDab).trans
      (centralizer_le (Set.singleton_subset_iff.mpr hdD))
  rw [hNd]
  refine signalizer_le_glbPrimeCore_map_conj hgD (fun Y hYN hY hDY =>
    hext.signalizer_le_glbPrimeCore_normalizer_zpowers hS hD1 hKF1 hp hp5 hPD hDab hzD hz1 hzc hzp
      hN₀M hYN hY hDY) ?_ (hT.of_dvd_right (Subgroup.card_dvd_of_le inf_le_left))
    (le_trans (le_inf hDT (hdC.trans le_normalizer)) inf_normalizer_le_normalizer_inf)
  rw [← hNd]
  exact inf_le_right.trans (centralizer_singleton_le_normalizer_zpowers d)

theorem ExtremalObstruction.inf_centralizer_le_glbPrimeCore (hS : Setting G)
    (hD1 : TheoremD1 G) (hKF1 : KF1At G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G)
    (hp5 : 5 ≤ p) {P : Sylow p G} {M D : Subgroup G} (hext : ExtremalObstruction p P M D)
    (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G)) (hDab : IsMulCommutative D) {z : G}
    (hzD : z ∈ D) (hz1 : z ≠ 1) (hzc : z ∈ centralizer (P : Set G)) (hzp : z ^ p = 1)
    (hN₀M : normalizer ((zpowers z : Subgroup G) : Set G) ≤ M) {T : Subgroup G}
    (hT : invariantTwoMaximalWithin D M T) {d : G} (hdD : d ∈ D) (hd1 : d ≠ 1) :
    T ⊓ centralizer ({d} : Set G) ≤
      GLBPrimeCore p (normalizer ((zpowers d : Subgroup G) : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT.2.1
  have hTcop : p.Coprime (Nat.card T) := by
    rw [hk]
    exact ((Nat.coprime_primes (sigmaA_prime p hp) Nat.prime_two).mpr (sigmaA_odd p hp)).pow_right k
  exact hext.inf_centralizer_le_glbPrimeCore_of_coprime hS hD1 hKF1 hp hp5 hPD hDab hzD hz1 hzc
    hzp hN₀M hTcop hT.2.2.1 hdD hd1

theorem ExtremalObstruction.inf_centralizer_le_pPrimeCoreIn (hS : Setting G)
    (hD1 : TheoremD1 G) (hKF1 : KF1At G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G)
    (hp5 : 5 ≤ p) {P : Sylow p G} {M D : Subgroup G} (hext : ExtremalObstruction p P M D)
    (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G)) (hDab : IsMulCommutative D) {z : G}
    (hzD : z ∈ D) (hz1 : z ≠ 1) (hzc : z ∈ centralizer (P : Set G)) (hzp : z ^ p = 1)
    (hN₀M : normalizer ((zpowers z : Subgroup G) : Set G) ≤ M) {T : Subgroup G}
    (hT : invariantTwoMaximalWithin D M T) {d : G} (hdD : d ∈ D) (hd1 : d ≠ 1) :
    T ⊓ centralizer ({d} : Set G) ≤
      CFSG.ABGTheoremB.pPrimeCoreIn p (normalizer ((zpowers d : Subgroup G) : Set G)) :=
  (hext.inf_centralizer_le_glbPrimeCore hS hD1 hKF1 hp hp5 hPD hDab hzD hz1 hzc hzp hN₀M hT hdD
    hd1).trans (glbPrimeCore_le_pPrimeCoreIn p _)

@[expose] def GL83InvariantTwoWithinNonConstrainedBal (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M D : Subgroup G), ExtremalObstruction p P M D →
    ¬ (P : Subgroup G) ≤ normalizer (D : Set G) → IsMulCommutative D →
      ∀ z ∈ D, z ≠ 1 → z ∈ centralizer (P : Set G) → z ^ p = 1 →
        normalizer ((zpowers z : Subgroup G) : Set G) ≤ M → ¬ HasPrimeConstraint (G := M) p →
        ∀ T : Subgroup G, invariantTwoMaximalWithin D M T →
          (5 ≤ p → ∀ d ∈ D, d ≠ 1 → T ⊓ centralizer ({d} : Set G) ≤
            CFSG.ABGTheoremB.pPrimeCoreIn p (normalizer ((zpowers d : Subgroup G) : Set G))) →
          T ≤ CFSG.ABGTheoremB.pPrimeCoreIn p M ⊔
            CFSG.ABGTheoremB.pPrimeCoreIn p (normalizer ((zpowers z : Subgroup G) : Set G))

theorem gl83InvariantTwoWithinNonConstrained_of_bal (hS : Setting G) (hD1 : TheoremD1 G)
    (hKF1 : KF1At G) (h : GL83InvariantTwoWithinNonConstrainedBal G) :
    GL83InvariantTwoWithinNonConstrained G := by
  intro p hp P M D hext hPD hab z hzD hz1 hzc hzp hN₀M hcon T hT
  exact h p hp P M D hext hPD hab z hzD hz1 hzc hzp hN₀M hcon T hT fun hp5 d hdD hd1 =>
    hext.inf_centralizer_le_pPrimeCoreIn hS hD1 hKF1 hp hp5 hPD hab hzD hz1 hzc hzp hN₀M hT hdD
      hd1

theorem gl83InvariantTwoWithin_of_bal (hS : Setting G) (hD1 : TheoremD1 G)
    (hKF1 : KF1At G) (h : GL83InvariantTwoWithinNonConstrainedBal G) :
    GL83InvariantTwoWithin G :=
  gl83InvariantTwoWithin_of_nonConstrained hS hD1
    (gl83InvariantTwoWithinNonConstrained_of_bal hS hD1 hKF1 h)

end CFSG.LocalAnalysis.RankThreeTheoremC
