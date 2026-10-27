module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.MemQz

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog Subgroup

private theorem orderOf_eq_of_isConj' {G : Type} [Group G] {x y : G} (h : IsConj x y) :
    orderOf x = orderOf y := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  have hsem : SemiconjBy c x y := by
    rw [SemiconjBy, ← hc]
    group
  exact SemiconjBy.orderOf_eq c hsem

private theorem exists_conj_b0_of_mem_orb2A (hI : TwoHSInterface) {G : Type} [Group G] {a z : G}
    (h : IsF5Type a z) (hF1 : Fusion1Facts a z) (hF2 : Fusion2Facts a z)
    {z₀ b₀ u₀ : ↥(Gx a)} (hF : TwoHSFacts ↥(Gx a) (GxSelf a) z₀ b₀ u₀)
    (hz₀ : IsConj z (z₀ : G)) {b : G} (hb : b ∈ orb2A a a) :
    ∃ k : ↥(Gx a), (k : G) * (b₀ : G) * (k : G)⁻¹ = b := by
  have ha2 : a ^ 2 = 1 := by rw [← h.orderOf_a]; exact pow_orderOf_eq_one a
  have hbord : orderOf b = 2 := (orderOf_eq_of_isConj' hb.1).symm.trans h.orderOf_a
  have habord : orderOf (a * b) = 2 := (orderOf_eq_of_isConj' hb.2).symm.trans h.orderOf_a
  have hb2 : b ^ 2 = 1 := by rw [← hbord]; exact pow_orderOf_eq_one b
  have hab2 : (a * b) ^ 2 = 1 := by rw [← habord]; exact pow_orderOf_eq_one (a * b)
  have hbinv : b⁻¹ = b := by rw [inv_eq_iff_mul_eq_one, ← pow_two]; exact hb2
  have hainv : a⁻¹ = a := by rw [inv_eq_iff_mul_eq_one, ← pow_two]; exact ha2
  have hab2' : (a * b) * (a * b) = 1 := by rw [← pow_two]; exact hab2
  have hcomm : a * b = b * a := by
    calc a * b = (a * b)⁻¹ := (inv_eq_iff_mul_eq_one.mpr hab2').symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [hbinv, hainv]
  have hbGx : b ∈ Gx a := mem_Gx.mpr hcomm
  have hba : b ≠ a := by
    intro h1
    have hconj1 : IsConj a (1 : G) := by
      have h2 := hb.2
      rw [h1] at h2
      simpa [← pow_two, ha2] using h2
    have hord := orderOf_eq_of_isConj' hconj1
    rw [h.orderOf_a, orderOf_one] at hord
    exact absurd hord (by norm_num)
  have hb_notderived : b ∉ derivedOf (Gx a) :=
    not_mem_derivedOf_of_isConj hI h hF1 hb.1 hb.2 hba
  have hborder : orderOf (⟨b, hbGx⟩ : ↥(Gx a)) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hbord
  obtain ⟨⟨_hb0A, _hab0A, _hb0not, _hb0shape⟩, hu0z, _hau0z, _haQ, _hQ5, _hpCore, _hQ4,
    _hu0shape⟩ := hF2.reps_bu z₀ b₀ u₀ hF hz₀
  have hbd : ¬ ((⟨b, hbGx⟩ : ↥(Gx a)) ∈ commutator ↥(Gx a)) := fun hm =>
    hb_notderived (mem_derivedOf_iff.mpr ⟨hbGx, hm⟩)
  have hmem_of_conj : ∀ c : ↥(Gx a), c ∈ commutator ↥(Gx a) →
      ∀ x : ↥(Gx a), IsConj c x → x ∈ commutator ↥(Gx a) := by
    intro c hc x hx
    obtain ⟨k, hk⟩ := isConj_iff.mp hx
    have := (inferInstance : (commutator ↥(Gx a)).Normal).conj_mem c hc k
    rwa [hk] at this
  obtain ⟨i, hi⟩ := hF.involution_cover ⟨b, hbGx⟩ hborder
  fin_cases i
  · exact absurd (hmem_of_conj (GxSelf a) hF.mem_commutator.1 ⟨b, hbGx⟩ hi) hbd
  · exact absurd (hmem_of_conj z₀ hF.mem_commutator.2.1 ⟨b, hbGx⟩ hi) hbd
  · exact absurd (hmem_of_conj (GxSelf a * z₀) hF.mem_commutator.2.2 ⟨b, hbGx⟩ hi) hbd
  · obtain ⟨k, hk⟩ := isConj_iff.mp hi
    exact ⟨k, by
      have := congrArg Subtype.val hk
      simpa using this⟩
  · exfalso
    have hiG : IsConj (u₀ : G) b := by
      obtain ⟨k, hk⟩ := isConj_iff.mp hi
      refine isConj_iff.mpr ⟨(k : G), ?_⟩
      have := congrArg Subtype.val hk
      simpa using this
    exact not_isConj_of_isF5Type hI h ((hb.1.trans hiG.symm).trans hu0z.symm)

theorem exists_conj_of_mem_orb2A (hI : TwoHSInterface) {G : Type} [Group G] {a z : G}
    (h : IsF5Type a z) (hF1 : Fusion1Facts a z) (hF2 : Fusion2Facts a z) {b b' : G}
    (hb : b ∈ orb2A a a) (hb' : b' ∈ orb2A a a) : ∃ k ∈ Gx a, k * b * k⁻¹ = b' := by
  obtain ⟨z₀, b₀, u₀, hF, hz₀, _⟩ := hF1.rep_z
  obtain ⟨k, hk⟩ := exists_conj_b0_of_mem_orb2A hI h hF1 hF2 hF hz₀ hb
  obtain ⟨k', hk'⟩ := exists_conj_b0_of_mem_orb2A hI h hF1 hF2 hF hz₀ hb'
  refine ⟨k' * k⁻¹, Subgroup.mul_mem _ k'.2 (Subgroup.inv_mem _ k.2), ?_⟩
  have hb0 : (b₀ : G) = (k : G)⁻¹ * b * (k : G) := by rw [← hk]; group
  have hkey : (k' : G) * (k : G)⁻¹ * b * ((k' : G) * (k : G)⁻¹)⁻¹ = b' := by
    calc (k' : G) * (k : G)⁻¹ * b * ((k' : G) * (k : G)⁻¹)⁻¹
        = (k' : G) * ((k : G)⁻¹ * b * (k : G)) * (k' : G)⁻¹ := by group
      _ = (k' : G) * (b₀ : G) * (k' : G)⁻¹ := by rw [hb0]
      _ = b' := hk'
  simpa using hkey

theorem exists_conj_pair (hI : TwoHSInterface) {G : Type} [Group G] {a z : G} (h : IsF5Type a z)
    (hF1 : Vert Fusion1Facts a z) (hF2 : Vert Fusion2Facts a z) {x y x' y' : G}
    (hx : IsConj a x) (hy : IsConj a y) (hxy : IsConj a (x * y)) (hx' : IsConj a x')
    (hy' : IsConj a y') (hxy' : IsConj a (x' * y')) :
    ∃ g : G, g * x * g⁻¹ = x' ∧ g * y * g⁻¹ = y' := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hx
  obtain ⟨c', hc'⟩ := isConj_iff.mp hx'
  let g₁ := c⁻¹
  let g₂ := c'⁻¹
  have hg₁ : g₁ * x * g₁⁻¹ = a := by
    rw [← hc]
    simp only [g₁]
    group
  have hg₂ : g₂ * x' * g₂⁻¹ = a := by
    rw [← hc']
    simp only [g₂]
    group
  let y₁ := g₁ * y * g₁⁻¹
  let y₁' := g₂ * y' * g₂⁻¹
  have hy₁ : y₁ ∈ orb2A a a := by
    refine ⟨hy.trans (isConj_iff.mpr ⟨g₁, rfl⟩), ?_⟩
    have h1 : g₁ * (x * y) * g₁⁻¹ = a * y₁ := by
      calc g₁ * (x * y) * g₁⁻¹ = (g₁ * x * g₁⁻¹) * (g₁ * y * g₁⁻¹) := by group
        _ = a * (g₁ * y * g₁⁻¹) := by rw [hg₁]
    exact hxy.trans (isConj_iff.mpr ⟨g₁, h1⟩)
  have hy₁' : y₁' ∈ orb2A a a := by
    refine ⟨hy'.trans (isConj_iff.mpr ⟨g₂, rfl⟩), ?_⟩
    have h1 : g₂ * (x' * y') * g₂⁻¹ = a * y₁' := by
      calc g₂ * (x' * y') * g₂⁻¹ = (g₂ * x' * g₂⁻¹) * (g₂ * y' * g₂⁻¹) := by group
        _ = a * (g₂ * y' * g₂⁻¹) := by rw [hg₂]
    exact hxy'.trans (isConj_iff.mpr ⟨g₂, h1⟩)
  obtain ⟨k, hkGx, hk⟩ := exists_conj_of_mem_orb2A hI h hF1.self hF2.self hy₁ hy₁'
  have hka : k * a * k⁻¹ = a := by
    rw [← mem_Gx.mp hkGx]
    group
  refine ⟨g₂⁻¹ * k * g₁, ?_, ?_⟩
  · calc (g₂⁻¹ * k * g₁) * x * (g₂⁻¹ * k * g₁)⁻¹
        = g₂⁻¹ * (k * (g₁ * x * g₁⁻¹) * k⁻¹) * g₂ := by group
      _ = g₂⁻¹ * (k * a * k⁻¹) * g₂ := by rw [hg₁]
      _ = g₂⁻¹ * a * g₂ := by rw [hka]
      _ = x' := by rw [← hg₂]; group
  · calc (g₂⁻¹ * k * g₁) * y * (g₂⁻¹ * k * g₁)⁻¹
        = g₂⁻¹ * (k * (g₁ * y * g₁⁻¹) * k⁻¹) * g₂ := by group
      _ = g₂⁻¹ * (k * y₁ * k⁻¹) * g₂ := by simp only [y₁]
      _ = g₂⁻¹ * y₁' * g₂ := by rw [hk]
      _ = y' := by simp only [y₁']; group

end CFSG.EvenSporadicStandard.HNRecog.Section3
