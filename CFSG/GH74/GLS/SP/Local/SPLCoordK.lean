module

public import CFSG.GH74.GLS.SP.Local.SPLRoot1
public import CFSG.GH74.GLS.Stage4.HexSL2Defs

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK.L2Torus CFSG.GH74.BNPair
open CFSG.GH74.GLS.Stage4.Hex SL2Root

theorem sl2_iso_data {G : Type} [Group G] [Finite G] (K : Subgroup G) (q p : ℕ) (hp : p.Prime)
    (hmod : CFSG.GH74.GLS.HasSL2Model ↥K (fun r => r = q)) (hodd : Odd q) (h5 : 5 ≤ q)
    (hpq : ∃ k : ℕ, 1 ≤ k ∧ q = p ^ k) (h w : G) (hhK : h ∈ K) (hwK : w ∈ K)
    (hord : orderOf h = q - 1)
    (hinv : ∀ k ∈ Subgroup.zpowers h, w * k * w⁻¹ = k⁻¹)
    (X₁ : Subgroup G) (hX₁K : X₁ ≤ K) (hX₁c : Nat.card ↥X₁ = q)
    (hX₁n : ∀ g ∈ Subgroup.zpowers h, ∀ x ∈ X₁, g * x * g⁻¹ ∈ X₁) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (ε : ↥K ≃* SL2m F), Nat.card F = q ∧
      (∀ k : ↥K, (k : G) ∈ X₁ ↔ ε k ∈ upperSub F) ∧
      (∀ u : Fˣ, ((ε.symm (sl2D u) : ↥K) : G) ∈ Subgroup.zpowers h) ∧
      (∃ s ∈ diagSub F, ε ⟨w, hwK⟩ = s * w0 F) := by
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
  have hdiagh : ∀ d ∈ diagSub F, ((ε.symm d : ↥K) : G) ∈ Subgroup.zpowers h := by
    intro d hd
    rw [← hτ] at hd
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hd
    have e : ε.symm ((ε hk) ^ i) = hk ^ i := by
      rw [map_zpow, MulEquiv.symm_apply_apply]
    rw [e]
    exact ⟨i, by simp [hk]⟩
  have hD : ∀ u : Fˣ, sl2D u ∈ diagSub F := fun u => by simp [mem_diagSub]
  have hwK' : ε wk = s * w0 F := hωs
  have hhE : ι (ε hk) = h := hιε hk
  have hwE : ι (s * w0 F) = w := by rw [← hωs]; exact hιε wk
  have htwo : ∀ W : Subgroup G, W ≤ K → Nat.card ↥W = Nat.card F →
      (∀ g ∈ Subgroup.zpowers h, ∀ x ∈ W, g * x * g⁻¹ ∈ W) →
      W = (upperSub F).map ι ∨ W = (lowerSub F).map ι := by
    intro W hWK hWcard hWn
    have hWmap : (W.comap ι).map ι = W := Subgroup.map_comap_eq_self (hιrange ▸ hWK)
    have hW'card : Nat.card (W.comap ι) = Nat.card F := by
      rw [← Subgroup.card_map_of_injective hι, hWmap, hWcard]
    have hW'n : ∀ x ∈ W.comap ι, ε hk * x * (ε hk)⁻¹ ∈ W.comap ι := by
      intro x hx
      show ι (ε hk * x * (ε hk)⁻¹) ∈ W
      rw [map_mul, map_mul, map_inv, hhE]
      exact hWn h (mem_zpowers h) _ hx
    rcases eq_upperSub_or_eq_lowerSub hp (hFq'.trans hkq) hτD hτ2 hW'card hW'n with h1 | h1
    · left
      rw [← hWmap, h1]
    · right
      rw [← hWmap, h1]
  have hX₁c' : Nat.card ↥X₁ = Nat.card F := by rw [hX₁c, hFq']
  have hX₁n' : ∀ g ∈ Subgroup.zpowers h, ∀ x ∈ X₁, g * x * g⁻¹ ∈ X₁ := hX₁n
  rcases htwo X₁ hX₁K hX₁c' hX₁n' with h1 | h1
  · refine ⟨F, inferInstance, inferInstance, ε, hFq', ?_, ?_, ⟨s, hs, hωs⟩⟩
    · intro k
      rw [h1]
      constructor
      · rintro ⟨x, hx, hxk⟩
        have : x = ε k := by
          apply hι
          rw [hxk, hιε]
        rw [← this]; exact hx
      · intro hk
        exact ⟨ε k, hk, hιε k⟩
    · intro u
      exact hdiagh _ (hD u)
  · set g : SL2m F := s * w0 F with hg
    have hgN : g ∈ normalizer (diagSub F : Set (SL2m F)) :=
      mul_mem (le_normalizer hs) w0_mem_normalizer
    refine ⟨F, inferInstance, inferInstance, ε.trans (MulAut.conj g), hFq', ?_, ?_, ?_⟩
    · intro k
      rw [h1]
      show _ ↔ g * ε k * g⁻¹ ∈ upperSub F
      rw [hg, conj_sw0_mem_upperSub_iff hs]
      constructor
      · rintro ⟨x, hx, hxk⟩
        have : x = ε k := by
          apply hι
          rw [hxk, hιε]
        rw [← this]; exact hx
      · intro hk
        exact ⟨ε k, hk, hιε k⟩
    · intro u
      have e : (ε.trans (MulAut.conj g)).symm (sl2D u) = ε.symm (g⁻¹ * sl2D u * g) := by
        simp [MulEquiv.symm_trans_apply, MulAut.conj_symm_apply]
      rw [e]
      apply hdiagh
      have := (mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) (sl2D u)).mp (hD u)
      simpa using this
    · refine ⟨s, hs, ?_⟩
      show g * ε wk * g⁻¹ = s * w0 F
      rw [hwK', ← hg]
      group

end CFSG.GH74.GLS.SP.Local
