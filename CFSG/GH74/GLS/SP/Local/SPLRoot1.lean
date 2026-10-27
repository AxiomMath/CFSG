module

public import CFSG.GH74.GLS.SP.Local.SPLStages
public import CFSG.GH74.GLS.SP.Local.SPLRoot1SL2

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK.L2Torus CFSG.GH74.BNPair

namespace SL2Root

theorem conj_sw0_mem_upperSub_iff {F : Type*} [Field F] {s : SL2m F} (hs : s ∈ diagSub F)
    (x : SL2m F) : s * w0 F * x * (s * w0 F)⁻¹ ∈ upperSub F ↔ x ∈ lowerSub F := by
  have h : s * w0 F * x * (s * w0 F)⁻¹ = s * (w0 F * x * (w0 F)⁻¹) * s⁻¹ := by group
  rw [h, diag_conj_mem_upperSub_iff hs, mem_lowerSub_iff_w0]

theorem rootGroups_aux {G : Type} [Group G] {F : Type} [Field F] [Finite F] {p f : ℕ}
    (hp : p.Prime) (hcard : Nat.card F = p ^ f) (hodd : Odd (Nat.card F))
    {ι : SL2m F →* G} (hι : Function.Injective ι) {K : Subgroup G} (hK : ι.range = K)
    {τ s : SL2m F} (hτ : zpowers τ = diagSub F) (hτ2 : τ.1 0 0 * τ.1 0 0 ≠ 1)
    (hs : s ∈ diagSub F) {h w z : G} (hh : ι τ = h) (hw : ι (s * w0 F) = w) (hz : w * w = z) :
    ∃ X : Subgroup G, X ≤ K ∧ Nat.card X = Nat.card F ∧ IsEAb p X ∧
      (∀ g ∈ zpowers h, ∀ x ∈ X, g * x * g⁻¹ ∈ X) ∧
      X ≠ conjBy w X ∧ K = X ⊔ conjBy w X ∧
      (∀ W : Subgroup G, W ≤ K → Nat.card W = Nat.card F →
        (∀ g ∈ zpowers h, ∀ x ∈ W, g * x * g⁻¹ ∈ W) → W = X ∨ W = conjBy w X) ∧
      (∀ Y : Subgroup G, Y ≤ X → (∀ g ∈ zpowers h, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y) →
        Y = ⊥ ∨ Y = X) ∧
      (∀ g ∈ zpowers h, (∀ x ∈ X, g * x = x * g) → g ∈ zpowers z) := by
  have : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite F
  have hchar : CharP F p :=
    charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have hτD : τ ∈ diagSub F := hτ ▸ mem_zpowers τ
  have hzh : ∀ g ∈ zpowers h, ∃ g' ∈ diagSub F, ι g' = g := by
    intro g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    exact ⟨τ ^ k, hτ ▸ zpow_mem_zpowers τ k, by rw [map_zpow, hh]⟩
  have hdh : ∀ g' ∈ diagSub F, ι g' ∈ zpowers h := by
    intro g' hg'
    rw [← hτ] at hg'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg'
    rw [map_zpow, hh]
    exact zpow_mem_zpowers h k
  have hXK : (upperSub F).map ι ≤ K := by
    rintro _ ⟨x, -, rfl⟩
    rw [← hK]
    exact ⟨x, rfl⟩
  have hconjeq : conjBy w ((upperSub F).map ι) = (lowerSub F).map ι := by
    ext x
    rw [mem_conjBy_iff]
    constructor
    · intro hx
      have hwK : w ∈ K := by rw [← hK, ← hw]; exact ⟨_, rfl⟩
      have hxK : x ∈ K := by
        have h1 : w⁻¹ * (w * x * w⁻¹) * w ∈ K :=
          mul_mem (mul_mem (K.inv_mem hwK) (hXK hx)) hwK
        simpa [mul_assoc] using h1
      rw [← hK] at hxK
      obtain ⟨x₁, rfl⟩ := hxK
      refine ⟨x₁, ?_, rfl⟩
      rw [← hw, ← map_inv, ← map_mul, ← map_mul, Subgroup.mem_map_iff_mem hι] at hx
      exact (conj_sw0_mem_upperSub_iff hs x₁).1 hx
    · rintro ⟨x₁, hx₁, rfl⟩
      rw [← hw, ← map_inv, ← map_mul, ← map_mul, Subgroup.mem_map_iff_mem hι]
      exact (conj_sw0_mem_upperSub_iff hs x₁).2 hx₁
  refine ⟨(upperSub F).map ι, hXK, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hι, card_upperSub]
  · refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, upperSub_comm hx hy]
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, upperSub_pow_char hx, map_one]
  · rintro g hg _ ⟨x, hx, rfl⟩
    obtain ⟨g', hg', rfl⟩ := hzh g hg
    refine ⟨g' * x * g'⁻¹, diag_conj_mem_upperSub hg' hx, ?_⟩
    simp
  · rw [hconjeq]
    intro hEq
    exact upperSub_ne_lowerSub (Subgroup.map_injective hι hEq)
  · rw [hconjeq, ← Subgroup.map_sup, upperSub_sup_lowerSub, ← MonoidHom.range_eq_map, hK]
  · intro W hWK hWcard hWn
    have hWmap : (W.comap ι).map ι = W := Subgroup.map_comap_eq_self (hK ▸ hWK)
    have hW'card : Nat.card (W.comap ι) = Nat.card F := by
      rw [← Subgroup.card_map_of_injective hι, hWmap, hWcard]
    have hW'n : ∀ x ∈ W.comap ι, τ * x * τ⁻¹ ∈ W.comap ι := by
      intro x hx
      show ι (τ * x * τ⁻¹) ∈ W
      rw [map_mul, map_mul, map_inv, hh]
      exact hWn h (mem_zpowers h) _ hx
    rcases eq_upperSub_or_eq_lowerSub hp hcard hτD hτ2 hW'card hW'n with h1 | h1
    · left
      rw [← hWmap, h1]
    · right
      rw [← hWmap, h1, hconjeq]
  · intro Y hYX hYn
    have hYK : Y ≤ ι.range := hK ▸ hYX.trans hXK
    have hYmap : (Y.comap ι).map ι = Y := Subgroup.map_comap_eq_self hYK
    have hY'le : Y.comap ι ≤ upperSub F := by
      intro y hy
      obtain ⟨x, hx, hxy⟩ := hYX hy
      rw [← hι hxy]
      exact hx
    have hY'n : ∀ d ∈ diagSub F, ∀ y ∈ Y.comap ι, d * y * d⁻¹ ∈ Y.comap ι := by
      intro d hd y hy
      show ι (d * y * d⁻¹) ∈ Y
      rw [map_mul, map_mul, map_inv]
      exact hYn (ι d) (hdh d hd) (ι y) hy
    rcases eq_bot_or_eq_upperSub hodd hY'le hY'n with h1 | h1
    · left
      rw [← hYmap, h1, Subgroup.map_bot]
    · right
      rw [← hYmap, h1]
  · intro g hg hc
    obtain ⟨g', hg'D, rfl⟩ := hzh g hg
    have hc' : ∀ x ∈ upperSub F, g' * x = x * g' := by
      intro x hx
      apply hι
      rw [map_mul, map_mul]
      exact hc (ι x) ⟨x, hx, rfl⟩
    have hw2 : ι (w0 F ^ 2) = z := by
      have h1 := w0_inv_diag hs
      have h2 : s * w0 F * (s * w0 F) = w0 F ^ 2 := by
        calc s * w0 F * (s * w0 F) = s * (w0 F * s * (w0 F)⁻¹) * (w0 F * w0 F) := by group
          _ = w0 F ^ 2 := by rw [h1]; simp [pow_two]
      rw [← hz, ← hw, ← map_mul, h2]
    rcases eq_one_or_eq_w0_sq hg'D hc' with h1 | h1
    · rw [h1, map_one]
      exact one_mem _
    · rw [h1, hw2]
      exact mem_zpowers z

end SL2Root

open SL2Root

theorem sl2_rootGroups {G : Type} [Group G] [Finite G] (K : Subgroup G) (q p : ℕ) (hp : p.Prime)
    (hmod : CFSG.GH74.GLS.HasSL2Model ↥K (fun r => r = q)) (hodd : Odd q) (h5 : 5 ≤ q)
    (hpq : ∃ k : ℕ, 1 ≤ k ∧ q = p ^ k) (z : G)
    (_hz : (Subgroup.center ↥K).map K.subtype = Subgroup.zpowers z)
    (h w : G) (hhK : h ∈ K) (hwK : w ∈ K) (hord : orderOf h = q - 1) (hwsq : w * w = z)
    (hinv : ∀ k ∈ Subgroup.zpowers h, w * k * w⁻¹ = k⁻¹)
    (_hnorm : Subgroup.normalizer (Subgroup.zpowers h : Set G) ⊓ K =
      Subgroup.zpowers h ⊔ Subgroup.zpowers w) :
    ∃ X : Subgroup G, X ≤ K ∧ Nat.card ↥X = q ∧ IsEAb p X ∧
      (∀ g ∈ Subgroup.zpowers h, ∀ x ∈ X, g * x * g⁻¹ ∈ X) ∧
      X ≠ CFSG.GH74.BNPair.conjBy w X ∧ K = X ⊔ CFSG.GH74.BNPair.conjBy w X ∧
      (∀ W : Subgroup G, W ≤ K → IsPGroup p ↥W → Nat.card ↥W = q →
        (∀ g ∈ Subgroup.zpowers h, ∀ x ∈ W, g * x * g⁻¹ ∈ W) →
        W = X ∨ W = CFSG.GH74.BNPair.conjBy w X) ∧
      (∀ Y : Subgroup G, Y ≤ X → (∀ g ∈ Subgroup.zpowers h, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y) →
        Y = ⊥ ∨ Y = X) ∧
      (∀ g ∈ Subgroup.zpowers h, (∀ x ∈ X, g * x = x * g) → g ∈ Subgroup.zpowers z) := by
  obtain ⟨F, _, _, hFq, ⟨e⟩⟩ := hmod
  have hFq' : Nat.card F = q := hFq
  obtain ⟨k, -, hkq⟩ := hpq
  have hoddF : Odd (Nat.card F) := by rw [hFq']; exact hodd
  have h3F : 3 < Nat.card F := by rw [hFq']; omega
  let ε₀ : ↥K ≃* SL2m F :=
    e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm
  let hk : ↥K := ⟨h, hhK⟩
  let wk : ↥K := ⟨w, hwK⟩
  have hordk : orderOf hk = q - 1 := by
    rw [← Subgroup.orderOf_coe]
    exact hord
  have hCcard : Nat.card (zpowers (ε₀ hk)) = Nat.card F - 1 := by
    rw [Nat.card_zpowers, MulEquiv.orderOf_eq, hordk, hFq']
  obtain ⟨P, hP⟩ := exists_map_conj_eq_diagSub hoddF h3F (zpowers (ε₀ hk))
    (Subgroup.isCyclic_zpowers _) hCcard
  let ε : ↥K ≃* SL2m F := ε₀.trans (MulAut.conj P⁻¹)
  let ι : SL2m F →* G := K.subtype.comp ε.symm.toMonoidHom
  have hι : Function.Injective ι := K.subtype_injective.comp ε.symm.injective
  have hιε : ∀ x : ↥K, ι (ε x) = x := fun x => by simp [ι]
  have hιrange : ι.range = K := by
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      exact (ε.symm s).2
    · intro hx
      exact ⟨ε ⟨x, hx⟩, hιε ⟨x, hx⟩⟩
  have hτ : zpowers (ε hk) = diagSub F := by
    rw [← hP, MonoidHom.map_zpowers]
    rfl
  have hτo : orderOf (ε hk) = q - 1 := by rw [MulEquiv.orderOf_eq, hordk]
  have hτD : ε hk ∈ diagSub F := hτ ▸ mem_zpowers (ε hk)
  have hτ2 : (ε hk).1 0 0 * (ε hk).1 0 0 ≠ 1 := sq_ne_one_of_orderOf hτD (by omega)
  have hωτ : ε wk * ε hk * (ε wk)⁻¹ = (ε hk)⁻¹ := by
    have h1 : wk * hk * wk⁻¹ = hk⁻¹ := Subtype.ext (hinv h (mem_zpowers h))
    calc ε wk * ε hk * (ε wk)⁻¹ = ε (wk * hk * wk⁻¹) := by simp
      _ = (ε hk)⁻¹ := by rw [h1]; simp
  have hne : (ε hk).1 0 0 ≠ (ε hk).1 1 1 := by
    intro h0
    apply hτ2
    have hdet := sl2_det (ε hk)
    rw [hτD.1, hτD.2, ← h0] at hdet
    linear_combination hdet
  obtain ⟨s, hs, hωs⟩ : ∃ s ∈ diagSub F, ε wk = s * w0 F := by
    rcases mem_diagSub_or_antidiag hτD hne (hωτ ▸ (diagSub F).inv_mem hτD) with hd | ha
    · exfalso
      have hcomm : ε wk * ε hk = ε hk * ε wk := diag_comm hd hτD
      have h1 : (ε hk)⁻¹ = ε hk := by rw [← hωτ, hcomm, mul_inv_cancel_right]
      have h2 : ε hk ^ 2 = 1 := by
        rw [pow_two]
        nth_rewrite 1 [← h1]
        exact inv_mul_cancel _
      have := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h2)
      omega
    · exact exists_mul_w0_of_antidiag ha.1 ha.2
  have hh : ι (ε hk) = h := hιε hk
  have hw : ι (s * w0 F) = w := by rw [← hωs]; exact hιε wk
  obtain ⟨X, hXK, hXc, hXe, hXn, hXne, hXK', hXW, hXY, hXZ⟩ :=
    rootGroups_aux hp (hFq'.trans hkq) hoddF hι hιrange hτ hτ2 hs hh hw hwsq
  exact ⟨X, hXK, hXc.trans hFq', hXe, hXn, hXne, hXK',
    fun W hWK _ hWc hWn => hXW W hWK (hWc.trans hFq'.symm) hWn, hXY, hXZ⟩

end CFSG.GH74.GLS.SP.Local
