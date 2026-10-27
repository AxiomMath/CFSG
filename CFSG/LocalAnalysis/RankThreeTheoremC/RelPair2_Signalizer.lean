module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Bal3Lemma2_2Main
import CFSG.LocalAnalysis.RankThreeTheoremC.HasPrimeConstraintBridge
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem ExtremalObstruction.exists_normal_coprime_signalizer (hS : Setting G) (hD1 : TheoremD1 G)
    (hK : KFactLemma212) {p : ℕ} (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M D : Subgroup G}
    (hext : ExtremalObstruction p P M D) (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G))
    (hR : TransitivityReduction G) (h13 : GL83InvariantTwoSylow G) {d : G} (hdD : d ∈ D)
    (hd1 : d ≠ 1) :
    ∃ K : Subgroup G, K ≤ normalizer ((zpowers d : Subgroup G) : Set G) ∧
      normalizer ((zpowers d : Subgroup G) : Set G) ≤ normalizer (K : Set G) ∧
      p.Coprime (Nat.card K) ∧ ∀ Y : Subgroup G,
        Y ≤ normalizer ((zpowers d : Subgroup G) : Set G) → p.Coprime (Nat.card Y) →
          D ≤ normalizer (Y : Set G) → Y ≤ K := by
  classical
  have hprime := sigmaA_prime p hp
  have hodd := sigmaA_odd p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  obtain ⟨hDab, z, hzD, hz1, hzc, hzp, hN₀M, hCD, -⟩ :=
    hext.transitivity_data hS hD1 hp hPD hR h13
  obtain ⟨hM, hDP, -, -⟩ := hext.obstruction
  set N₀ := normalizer ((zpowers z : Subgroup G) : Set G) with hN₀
  have hcon : HasPrimeConstraint (G := N₀) p :=
    hasPrimeConstraint_of_isPConstrained
      (hext.isPConstrained_normalizer_zpowers_of_kfact hS hD1 hK hp hPD hDab hzD hz1 hzc hzp
        hN₀M)
  have hDN₀ : D ≤ N₀ := by
    intro x hx
    refine centralizer_singleton_le_normalizer_zpowers z ?_
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hDab.is_comm.comm ⟨x, hx⟩ ⟨z, hzD⟩)
  have hcontains : ∀ x : G, x ∈ N₀ → x ∈ centralizer (D : Set G) → orderOf x = p → x ∈ D :=
    fun x _ hxC hxo => hext.mem_of_mem_centralizer_of_isMulCommutative hS hD1 hp hDab hCD hxC
      (by rw [← hxo]; exact pow_orderOf_eq_one x)
  obtain ⟨g, hgN, hgz⟩ := hext.exists_mem_normalizer_zpowers_eq hS hD1 hp hPD hDab hCD hzD hz1
    hzc hN₀M hdD hd1
  have hD : D.map (MulAut.conj g).toMonoidHom = D := mem_normalizer_iff_map_conj_eq.mp hgN
  have hD' : D.map (MulAut.conj g⁻¹).toMonoidHom = D :=
    mem_normalizer_iff_map_conj_eq.mp (inv_mem hgN)
  set K₀ := (primeComplementCore (G := N₀) p).map N₀.subtype with hK₀
  have hK₀N : K₀ ≤ N₀ := Subgroup.map_subtype_le _
  have hK₀norm : N₀ ≤ normalizer (K₀ : Set G) := CFSG.ABGTheoremB.le_normalizer_map_subtype N₀ _
  have hNd : normalizer ((zpowers d : Subgroup G) : Set G) =
      N₀.map (MulAut.conj g).toMonoidHom := by
    rw [hgz, hN₀, Subgroup.map_equiv_normalizer_eq]
  refine ⟨K₀.map (MulAut.conj g).toMonoidHom, ?_, ?_, ?_, ?_⟩
  · rw [hNd]
    exact Subgroup.map_mono hK₀N
  · rw [hNd, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hK₀norm
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hK₀,
      Subgroup.card_map_of_injective N₀.subtype_injective]
    exact primeComplementCore_coprime p
  · intro Y hYN hYc hDY
    set Y' := Y.map (MulAut.conj g⁻¹).toMonoidHom with hY'
    have hYY' : Y'.map (MulAut.conj g).toMonoidHom = Y := by
      rw [hY', Subgroup.map_map]
      have : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom = MonoidHom.id G := by
        ext x
        simp [MulAut.conj_apply]
        group
      rw [this, Subgroup.map_id]
    have hY'N : Y' ≤ N₀ := by
      have h := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hYN
      rw [hNd, Subgroup.map_map] at h
      have : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id G := by
        ext x
        simp [MulAut.conj_apply]
        group
      rwa [this, Subgroup.map_id] at h
    have hDY' : D ≤ normalizer (Y' : Set G) := by
      rw [← hD', ← Subgroup.map_equiv_normalizer_eq]
      exact Subgroup.map_mono hDY
    have hY'c : p.Coprime (Nat.card Y') := by
      rw [hY', Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
      exact hYc
    have hle := ambient_prime_constraint_signalizer_le_core p hprime hodd N₀ D Y' hcon
      (P.isPGroup'.to_le hDP) hDN₀ hY'c hY'N hDY' hcontains
    rw [← hYY']
    exact Subgroup.map_mono hle

end CFSG.LocalAnalysis.RankThreeTheoremC
