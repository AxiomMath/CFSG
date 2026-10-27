module

public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.A5Diag
public import CFSG.HardMathSupport.Foote.Coordinator.LangTorus.Monomial
public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.A5Theta
public import CFSG.RankThree.PartOne.KA5L.Core

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KA5L CFSG.RankThree.Classical2
open scoped MatrixGroups

variable {L : Type} [Field L]

theorem torusGroup_inf_rootSpan_eq :
    torusGroup Tag.E7 L ⊓ rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)) =
      supportedTorus Tag.E7 L (a5Nodes Tag.E7) := by
  have hJ : subsystemGroup Tag.E7 L (a5Nodes Tag.E7) ⊓ torusGroup Tag.E7 L =
      supportedTorus Tag.E7 L (a5Nodes Tag.E7) :=
    subsystemGroup_inf_torusGroup_eq_supportedTorus _
  rw [subsystemGroup_eq_rootSpan] at hJ
  rw [inf_comm]; exact hJ

theorem lang_torus_inf_rootSpan [IsAlgClosed L] {Fr : L →+* L} {q : ℕ} (hq : 2 ≤ q)
    (hFr : ∀ c, Fr c = c ^ q) {n : ModGL Tag.E7 L} (hn : n ∈ monomialSubgroup Tag.E7 L)
    (hJ : ∀ β ∈ parabolicRoots Tag.E7 (a5Nodes Tag.E7),
      weylQuotientHom Tag.E7 L ⟨n, hn⟩ • β ∈ parabolicRoots Tag.E7 (a5Nodes Tag.E7)) :
    ∀ s ∈ torusGroup Tag.E7 L ⊓ rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)),
      ∃ t ∈ torusGroup Tag.E7 L ⊓ rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)),
        t⁻¹ * (n * Units.map (entrywiseHom Fr) t * n⁻¹) = s := by
  rw [torusGroup_inf_rootSpan_eq]
  exact CFSG.HardMathSupport.Foote.Coordinator.exists_lang_supportedTorus_of_monomial hq hFr n hn hJ

theorem pow_six_of_mem_ker {k : SL(6, L)} (hk : k ∈ (a5Frame L).ker) : k ^ 6 = 1 := by
  obtain ⟨r, hr, hkr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 (ker_a5Frame_le_center hk)
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, ← hkr, ← map_pow]
  simp only [Fintype.card_fin] at hr
  rw [hr]
  simp

theorem exists_lang_lift [IsAlgClosed L] {Fr : L →+* L} (hFrb : Function.Bijective Fr) {q : ℕ}
    (hq : 2 ≤ q) (hFr : ∀ c, Fr c = c ^ q) {n : ModGL Tag.E7 L}
    (hn : n ∈ monomialSubgroup Tag.E7 L) {w : WeylGroup Tag.E7}
    (hnw : MapsRootLines n w) (hwS : ∀ α ∈ parabolicRoots Tag.E7 (a5Nodes Tag.E7),
      w • α ∈ parabolicRoots Tag.E7 (a5Nodes Tag.E7))
    (hwS' : ∀ α ∈ parabolicRoots Tag.E7 (a5Nodes Tag.E7),
      ∃ β ∈ parabolicRoots Tag.E7 (a5Nodes Tag.E7), w • β = α)
    (Φ' : SL(6, L) ≃* SL(6, L))
    (hΦ' : ∀ X, n * Units.map (entrywiseHom Fr) (a5Frame L X) * n⁻¹ = a5Frame L (Φ' X))
    {z : SL(6, L)} (hz : z ∈ (a5Frame L).ker) :
    ∃ s ∈ (chainDiag L).range, Φ' s * s⁻¹ = z := by
  classical
  have hwn : weylQuotientHom Tag.E7 L ⟨n, hn⟩ = w := weylQuotientHom_eq hnw
  have hJ : ∀ β ∈ parabolicRoots Tag.E7 (a5Nodes Tag.E7),
      weylQuotientHom Tag.E7 L ⟨n, hn⟩ • β ∈ parabolicRoots Tag.E7 (a5Nodes Tag.E7) := by
    intro β hβ
    rw [hwn]
    exact hwS β hβ
  set T : Subgroup SL(6, L) := (chainDiag L).range with hT
  have hcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := fun x hx y hy =>
    chainDiag_comm ⟨x, hx⟩ ⟨y, hy⟩
  have hρT : ∀ s ∈ T, a5Frame L s ∈ torusGroup Tag.E7 L ⊓
      rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)) := by
    rintro _ ⟨a, rfl⟩
    exact (mem_chainTorus_iff).2 ⟨a, (a5Frame_chainDiag a).symm ▸ rfl⟩
  have hHT : ∀ h ∈ torusGroup Tag.E7 L ⊓
      rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)), ∃ s ∈ T, a5Frame L s = h := by
    intro h hh
    obtain ⟨a, rfl⟩ := (mem_chainTorus_iff).1 hh
    exact ⟨chainDiag L a, ⟨a, rfl⟩, a5Frame_chainDiag a⟩
  have hθ : ∀ s ∈ T, a5Frame L (Φ' s) ∈ torusGroup Tag.E7 L ⊓
      rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)) := by
    intro s hs
    obtain ⟨hH, hQ⟩ := Subgroup.mem_inf.1 (hρT s hs)
    rw [← hΦ' s]
    refine Subgroup.mem_inf.2 ⟨theta_mem_torusGroup_of_monomial hFrb hn hH, ?_⟩
    have := map_theta_rootSpan_eq hFrb hn hnw (fun α hα => hα.1) hwS hwS'
    have hmem : n * Units.map (entrywiseHom Fr) (a5Frame L s) * n⁻¹ ∈
        (rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7))).map
          ((MulAut.conj n).toMonoidHom.comp (Units.map (entrywiseHom Fr))) :=
      ⟨a5Frame L s, hQ, by simp [MulAut.conj_apply]⟩
    rw [this] at hmem
    exact hmem
  have hΦT : ∀ s ∈ T, Φ' s ∈ T := by
    intro s hs
    obtain ⟨s', hs', hs'e⟩ := hHT _ (hθ s hs)
    have hk : Φ' s * s'⁻¹ ∈ (a5Frame L).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, ← hs'e, mul_inv_cancel]
    have hkT := ker_a5Frame_le_range_chainDiag hk
    have : Φ' s = (Φ' s * s'⁻¹) * s' := by group
    rw [this]
    exact T.mul_mem hkT hs'
  have hTB : ∀ r ∈ T, ∃ s ∈ T, (s⁻¹ * Φ' s)⁻¹ * r ∈ (a5Frame L).ker := by
    intro r hr
    obtain ⟨t, htHQ, ht⟩ := lang_torus_inf_rootSpan hq hFr hn hJ _ (hρT r hr)
    obtain ⟨s, hs, rfl⟩ := hHT t htHQ
    refine ⟨s, hs, ?_⟩
    have h1 : a5Frame L (s⁻¹ * Φ' s) = a5Frame L r := by
      rw [map_mul, map_inv, ← hΦ' s]; exact ht
    rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
  have hzT := ker_a5Frame_le_range_chainDiag hz
  obtain ⟨w₀, hw₀T, hw₀⟩ := exists_pow_six_chainDiag hzT
  obtain ⟨s₁, hs₁T, hk⟩ := hTB w₀ hw₀T
  set b : SL(6, L) := s₁⁻¹ * Φ' s₁ with hb
  set k : SL(6, L) := b⁻¹ * w₀ with hkdef
  have hw : w₀ = b * k := by rw [hkdef]; group
  have hkc : Commute b k := by
    have := Subgroup.mem_center_iff.1 (ker_a5Frame_le_center hk)
    exact (this b)
  have hk6 : k ^ 6 = 1 := pow_six_of_mem_ker hk
  have hz6 : z = b ^ 6 := by
    rw [← hw₀, hw, hkc.mul_pow, hk6, mul_one]
  have hcs : Commute s₁⁻¹ (Φ' s₁) :=
    hcomm _ (T.inv_mem hs₁T) _ (hΦT s₁ hs₁T)
  refine ⟨s₁ ^ 6, T.pow_mem hs₁T 6, ?_⟩
  have : b ^ 6 = (s₁ ^ 6)⁻¹ * Φ' (s₁ ^ 6) := by
    rw [hb, hcs.mul_pow, inv_pow, map_pow]
  rw [hz6, this]
  have hc2 : Commute (s₁ ^ 6)⁻¹ (Φ' (s₁ ^ 6)) := by
    rw [← inv_pow, map_pow]
    exact hcs.pow_pow 6 6
  rw [hc2.eq]

theorem exists_split_fixed_Q [IsAlgClosed L] {Fr : L →+* L} (hFrb : Function.Bijective Fr)
    {q : ℕ} (hq : 2 ≤ q) (hFr : ∀ c, Fr c = c ^ q) {n : ModGL Tag.E7 L}
    (hn : n ∈ monomialSubgroup Tag.E7 L) {w : WeylGroup Tag.E7}
    (hnw : MapsRootLines n w) (hwS : ∀ α ∈ parabolicRoots Tag.E7 (a5Nodes Tag.E7),
      w • α ∈ parabolicRoots Tag.E7 (a5Nodes Tag.E7))
    (hwS' : ∀ α ∈ parabolicRoots Tag.E7 (a5Nodes Tag.E7),
      ∃ β ∈ parabolicRoots Tag.E7 (a5Nodes Tag.E7), w • β = α)
    (Φ' : SL(6, L) ≃* SL(6, L))
    (hΦ' : ∀ X, n * Units.map (entrywiseHom Fr) (a5Frame L X) * n⁻¹ = a5Frame L (Φ' X))
    {g : ModGL Tag.E7 L}
    (hgQ : g ∈ rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)))
    (hg : n * Units.map (entrywiseHom Fr) g * n⁻¹ = g) :
    ∃ s ∈ torusGroup Tag.E7 L ⊓ rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)),
      n * Units.map (entrywiseHom Fr) s * n⁻¹ = s ∧
      ∃ x ∈ (fixSubgroup Φ').map (a5Frame L), g = s * x := by
  have hΓ : g ∈ rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom Fr)) := Subgroup.mem_inf.2 ⟨hgQ, hg⟩
  rw [Gamma_eq_map Fr n Φ' hΦ'] at hΓ
  obtain ⟨X, hX, rfl⟩ := hΓ
  have hz : Φ' X * X⁻¹ ∈ (a5Frame L).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, mem_fixRho.1 hX, mul_inv_cancel]
  obtain ⟨s₁, hs₁T, hs₁⟩ := exists_lang_lift hFrb hq hFr hn hnw hwS hwS' Φ' hΦ' hz
  have hΦs : Φ' s₁ = (Φ' X * X⁻¹) * s₁ := by rw [← hs₁]; group
  have hfix : Φ' (s₁⁻¹ * X) = s₁⁻¹ * X := by
    rw [map_mul, map_inv, hΦs]
    group
  refine ⟨a5Frame L s₁, ?_, ?_, a5Frame L (s₁⁻¹ * X),
    ⟨s₁⁻¹ * X, (mem_fixSubgroup Φ').2 hfix, rfl⟩, ?_⟩
  · obtain ⟨a, rfl⟩ := hs₁T
    exact (mem_chainTorus_iff).2 ⟨a, (a5Frame_chainDiag a).symm⟩
  · rw [hΦ' s₁, hΦs, map_mul, MonoidHom.mem_ker.1 hz, one_mul]
  · rw [← map_mul]
    congr 1
    group

end CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7
