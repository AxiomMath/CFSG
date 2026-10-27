module

public import CFSG.LieType.Chevalley.OrthogonalFixedOrbitMaps
public import CFSG.RankThree.PartOne.KA5L.Chain
public import CFSG.RankThree.PartOne.KE.A1SL2

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KA5L

variable {τ : Tag} {L : Type} [Field L]

theorem theta_mem_torusGroup_of_monomial {Fr : L →+* L} (hFr : Function.Bijective Fr)
    {n : ModGL .E7 L} (hn : n ∈ monomialSubgroup .E7 L) {x : ModGL .E7 L}
    (hx : x ∈ torusGroup .E7 L) :
    n * Units.map (entrywiseHom Fr) x * n⁻¹ ∈ torusGroup .E7 L := by
  have h1 : Units.map (entrywiseHom Fr) x ∈ torusGroup .E7 L := by
    have := entrywise_mem_torusGroup (σ := RingEquiv.ofBijective Fr hFr) hx
    exact this
  exact (Subgroup.mem_normalizer_iff.1 (mem_normalizer_torusGroup_of_mem_monomialSubgroup hn)
    (Units.map (entrywiseHom Fr) x)).1 h1

theorem map_entrywise_rootSpan_eq {Fr : L →+* L} (hFr : Function.Bijective Fr)
    (S : Set (Fin Tag.E7.rank → ℤ)) :
    (rootSpan .E7 L S).map (Units.map (entrywiseHom Fr)) = rootSpan .E7 L S := by
  have := hFr
  let σ : L ≃+* L := RingEquiv.ofBijective Fr hFr
  have hσ : σ.toRingHom = Fr := RingHom.ext fun _ => rfl
  rw [← hσ, rootSpan, Subgroup.map_iSup]
  refine iSup_congr fun α => ?_
  rw [Subgroup.map_iSup]
  exact iSup_congr fun _ => map_entrywise_rootSubgroup σ α

theorem map_conj_rootSpan_eq {n : ModGL .E7 L} (hn : n ∈ monomialSubgroup .E7 L)
    {w : WeylGroup Tag.E7} (hnw : MapsRootLines n w) {S : Set (Fin Tag.E7.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot Tag.E7 α) (hwS : ∀ α ∈ S, w • α ∈ S)
    (hwS' : ∀ α ∈ S, ∃ β ∈ S, w • β = α) :
    (rootSpan .E7 L S).map (MulAut.conj n).toMonoidHom = rootSpan .E7 L S := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have := conj_mem_rootSpan_of_mapsRootLines hn hnw hS hx
    refine (iSup₂_le fun r hr => ?_ : rootSpan .E7 L ((fun α => w • α) '' S) ≤ rootSpan .E7 L S) this
    obtain ⟨α, hα, rfl⟩ := hr
    exact le_iSup₂_of_le (w • α) (hwS α hα) le_rfl
  · intro g hg
    have hn' : n⁻¹ ∈ monomialSubgroup .E7 L := inv_mem hn
    have := conj_mem_rootSpan_of_mapsRootLines hn' hnw.inv hS hg
    have hle : rootSpan .E7 L ((fun α => w⁻¹ • α) '' S) ≤ rootSpan .E7 L S := by
      refine iSup₂_le fun r hr => ?_
      obtain ⟨α, hα, rfl⟩ := hr
      obtain ⟨β, hβ, rfl⟩ := hwS' α hα
      show rootSubgroup Tag.E7 L (w⁻¹ • (w • β)) ≤ _
      rw [inv_smul_smul]
      exact le_iSup₂_of_le β hβ le_rfl
    refine ⟨n⁻¹ * g * n⁻¹⁻¹, hle this, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem map_theta_rootSpan_eq {Fr : L →+* L} (hFr : Function.Bijective Fr)
    {n : ModGL .E7 L} (hn : n ∈ monomialSubgroup .E7 L)
    {w : WeylGroup Tag.E7} (hnw : MapsRootLines n w) {S : Set (Fin Tag.E7.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot Tag.E7 α) (hwS : ∀ α ∈ S, w • α ∈ S)
    (hwS' : ∀ α ∈ S, ∃ β ∈ S, w • β = α) :
    (rootSpan .E7 L S).map ((MulAut.conj n).toMonoidHom.comp (Units.map (entrywiseHom Fr))) =
      rootSpan .E7 L S := by
  rw [← Subgroup.map_map, map_entrywise_rootSpan_eq hFr, map_conj_rootSpan_eq hn hnw hS hwS hwS']

theorem smul_neg_mem_parabolicRoots {J : Set (Fin Tag.E7.rank)} {u : WeylGroup Tag.E7}
    (hu : u ∈ parabolicWeylGroup Tag.E7 J) {α : Fin Tag.E7.rank → ℤ}
    (hα : α ∈ parabolicRoots Tag.E7 J) : u • ((-1 : ℤ) • α) ∈ parabolicRoots Tag.E7 J := by
  refine ⟨?_, fun i hi => ?_⟩
  · rw [neg_one_zsmul]
    exact IsRoot.smul (IsRoot.neg hα.1) u
  · rw [neg_one_zsmul, smul_apply_of_mem_parabolicWeylGroup hu _ hi]
    simp [hα.2 i hi]

theorem perm_of_act {J : Set (Fin Tag.E7.rank)} {w u : WeylGroup Tag.E7}
    (hu : u ∈ parabolicWeylGroup Tag.E7 J)
    (hact : ∀ α ∈ parabolicRoots Tag.E7 J, w • α = u • ((-1 : ℤ) • α)) :
    (∀ α ∈ parabolicRoots Tag.E7 J, w • α ∈ parabolicRoots Tag.E7 J) ∧
      ∀ α ∈ parabolicRoots Tag.E7 J, ∃ β ∈ parabolicRoots Tag.E7 J, w • β = α := by
  refine ⟨fun α hα => by rw [hact α hα]; exact smul_neg_mem_parabolicRoots hu hα,
    fun α hα => ?_⟩
  have hu' : u⁻¹ ∈ parabolicWeylGroup Tag.E7 J := inv_mem hu
  have hβ : (-1 : ℤ) • (u⁻¹ • α) ∈ parabolicRoots Tag.E7 J := by
    refine ⟨?_, fun i hi => ?_⟩
    · rw [neg_one_zsmul]
      exact IsRoot.neg (IsRoot.smul hα.1 u⁻¹)
    · rw [neg_one_zsmul]
      simp [smul_apply_of_mem_parabolicWeylGroup hu' _ hi, hα.2 i hi]
  refine ⟨(-1 : ℤ) • (u⁻¹ • α), hβ, ?_⟩
  rw [hact _ hβ]
  simp only [neg_one_zsmul, neg_neg, smul_inv_smul]

end CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7
