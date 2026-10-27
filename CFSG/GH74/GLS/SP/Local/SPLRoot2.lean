module

public import CFSG.GH74.GLS.SP.Local.SPLRoot1
public import CFSG.GH74.GLS.SP.Local.SPLRoot2SL2

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK.L2Torus CFSG.GH74.BNPair
  CFSG.SL2MinimalFaithful
open scoped Pointwise

namespace SL2Root

theorem exists_upper_model {G : Type} [Group G] (K : Subgroup G) (q p : ℕ) (hp : p.Prime)
    (hmod : CFSG.GH74.GLS.HasSL2Model ↥K (fun r => r = q)) (hodd : Odd q) (h5 : 5 ≤ q)
    (hpq : ∃ k : ℕ, 1 ≤ k ∧ q = p ^ k) (h w : G) (hhK : h ∈ K) (hwK : w ∈ K)
    (hord : orderOf h = q - 1) (hinv : ∀ k ∈ Subgroup.zpowers h, w * k * w⁻¹ = k⁻¹)
    (X : Subgroup G) (hXK : X ≤ K) (hXcard : Nat.card ↥X = q)
    (hXn : ∀ g ∈ Subgroup.zpowers h, ∀ x ∈ X, g * x * g⁻¹ ∈ X) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (ε : ↥K ≃* SL2m F),
      (∀ g : ↥K, (g : G) ∈ zpowers h ↔ ε g ∈ diagSub F) ∧
      (∀ x : ↥K, (x : G) ∈ X ↔ ε x ∈ upperSub F) ∧
      ∃ s ∈ diagSub F, ε ⟨w, hwK⟩ = s * w0 F := by
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
  have hD : ∀ g : ↥K, (g : G) ∈ zpowers h ↔ ε g ∈ diagSub F := by
    intro g
    rw [← hτ]
    constructor
    · intro hg
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hg
      have hgn : g = hk ^ n := Subtype.ext (by rw [← hn]; rfl)
      rw [hgn, map_zpow]
      exact zpow_mem_zpowers _ _
    · intro hg
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hg
      have hgn : g = hk ^ n := ε.injective (by rw [map_zpow, hn])
      rw [hgn, Subgroup.coe_zpow]
      exact zpow_mem_zpowers h n
  have hXmap : (X.comap ι).map ι = X := Subgroup.map_comap_eq_self (hιrange ▸ hXK)
  have hXcard' : Nat.card (X.comap ι) = Nat.card F := by
    rw [← Subgroup.card_map_of_injective hι, hXmap, hXcard, hFq']
  have hXn' : ∀ x ∈ X.comap ι, ε hk * x * (ε hk)⁻¹ ∈ X.comap ι := by
    intro x hx
    show ι (ε hk * x * (ε hk)⁻¹) ∈ X
    rw [map_mul, map_mul, map_inv, hιε hk]
    exact hXn h (mem_zpowers h) _ hx
  have hmem : ∀ x : ↥K, (x : G) ∈ X ↔ ε x ∈ X.comap ι := by
    intro x
    rw [Subgroup.mem_comap, hιε x]
  rcases eq_upperSub_or_eq_lowerSub hp (hFq'.trans hkq) hτD hτ2 hXcard' hXn' with h1 | h1
  · refine ⟨F, inferInstance, inferInstance, ε, hD, fun x => ?_, s, hs, hωs⟩
    rw [hmem x, h1]
  · refine ⟨F, inferInstance, inferInstance, ε.trans (MulAut.conj (w0 F)), fun g => ?_,
      fun x => ?_, s⁻¹, (diagSub F).inv_mem hs, ?_⟩
    · rw [hD g]
      exact (w0_conj_mem_diagSub_iff (ε g)).symm
    · rw [hmem x, h1]
      exact mem_lowerSub_iff_w0 (ε x)
    · show w0 F * ε wk * (w0 F)⁻¹ = s⁻¹ * w0 F
      rw [hωs]
      calc w0 F * (s * w0 F) * (w0 F)⁻¹ = (w0 F * s * (w0 F)⁻¹) * w0 F := by group
        _ = s⁻¹ * w0 F := by rw [w0_inv_diag hs]

variable {G : Type} [Group G] {K : Subgroup G} {F : Type} [Field F]

theorem model_aut (ε : ↥K ≃* SL2m F) {h w z : G} (hwK : w ∈ K) {X : Subgroup G}
    (hD : ∀ g : ↥K, (g : G) ∈ zpowers h → ε g ∈ diagSub F)
    (hU : ∀ x : ↥K, (x : G) ∈ X → ε x ∈ upperSub F) {s : SL2m F} (hs : s ∈ diagSub F)
    (hεw : ε ⟨w, hwK⟩ = s * w0 F) (hz : w * w = z) :
    ∃ α : ↥K ≃* ↥K, (∀ x : ↥K, (x : G) ∈ X → (α x : G) = (x : G)⁻¹) ∧
      (∀ g : ↥K, (g : G) ∈ zpowers h → α g = g) ∧ (α ⟨w, hwK⟩ : G) = w * z ∧
      ∀ k, α (α k) = k := by
  refine ⟨(ε.trans (negOff F)).trans ε.symm, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have h1 : ((ε.trans (negOff F)).trans ε.symm) x = x⁻¹ := by
      show ε.symm (negOff F (ε x)) = x⁻¹
      rw [negOff_of_mem_upperSub (hU x hx), map_inv, ε.symm_apply_apply]
    rw [h1]
    rfl
  · intro g hg
    show ε.symm (negOff F (ε g)) = g
    rw [negOff_of_mem_diagSub (hD g hg), ε.symm_apply_apply]
  · show ((ε.symm (negOff F (ε ⟨w, hwK⟩)) : ↥K) : G) = w * z
    have h1 : ε.symm (negOff F (ε ⟨w, hwK⟩)) = ⟨w, hwK⟩ * (⟨w, hwK⟩ * ⟨w, hwK⟩) := by
      apply ε.injective
      rw [ε.apply_symm_apply, hεw, negOff_mul_w0 hs, map_mul, map_mul, hεw]
    rw [h1, ← hz]
    rfl
  · intro k
    show ε.symm (negOff F (ε (ε.symm (negOff F (ε k))))) = k
    rw [ε.apply_symm_apply, negOff_negOff, ε.symm_apply_apply]

theorem model_mem_borel (ε : ↥K ≃* SL2m F) {h : G} {X : Subgroup G}
    (hD : ∀ g : ↥K, (g : G) ∈ zpowers h ↔ ε g ∈ diagSub F)
    (hU : ∀ x : ↥K, (x : G) ∈ X ↔ ε x ∈ upperSub F) (k : ↥K) (hk : (ε k).1 1 0 = 0) :
    (k : G) ∈ X ⊔ zpowers h := by
  obtain ⟨u, hu, d, hd, hud⟩ := exists_upperSub_mul_diagSub hk
  have h1 : k = ε.symm u * ε.symm d := by rw [← map_mul, ← hud, ε.symm_apply_apply]
  rw [h1]
  refine Subgroup.mul_mem_sup ?_ ?_
  · exact (hU _).2 (by rw [ε.apply_symm_apply]; exact hu)
  · exact (hD _).2 (by rw [ε.apply_symm_apply]; exact hd)

theorem model_normalizer (ε : ↥K ≃* SL2m F) {h : G} (hhK : h ∈ K) {X : Subgroup G}
    (hXK : X ≤ K) (hD : ∀ g : ↥K, (g : G) ∈ zpowers h ↔ ε g ∈ diagSub F)
    (hU : ∀ x : ↥K, (x : G) ∈ X ↔ ε x ∈ upperSub F)
    (hXn : ∀ g ∈ zpowers h, ∀ x ∈ X, g * x * g⁻¹ ∈ X) :
    normalizer (X : Set G) ⊓ K = X ⊔ zpowers h := by
  apply le_antisymm
  · rintro k ⟨hkN, hkK⟩
    have hM : ε ⟨k, hkK⟩ * unipotent 1 * (ε ⟨k, hkK⟩)⁻¹ ∈ upperSub F := by
      have hxX : ((ε.symm (unipotent 1) : ↥K) : G) ∈ X :=
        (hU _).2 (by rw [ε.apply_symm_apply]; exact unipotent_mem_upperSub 1)
      have h1 : k * ((ε.symm (unipotent 1) : ↥K) : G) * k⁻¹ ∈ X :=
        (mem_normalizer_iff.1 hkN _).1 hxX
      have h2 := (hU (⟨k, hkK⟩ * ε.symm (unipotent 1) * ⟨k, hkK⟩⁻¹)).1 h1
      simpa using h2
    exact model_mem_borel ε hD hU ⟨k, hkK⟩ (entry_10_eq_zero_of_conj_mem_upperSub hM)
  · refine sup_le (le_inf Subgroup.le_normalizer hXK) (le_inf ?_ (Subgroup.zpowers_le.2 hhK))
    intro g hg
    rw [mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hXn g hg x hx, fun hx => ?_⟩
    have := hXn g⁻¹ ((zpowers h).inv_mem hg) _ hx
    simpa [mul_assoc] using this

theorem model_bruhat_cell (ε : ↥K ≃* SL2m F) {h w : G} (hwK : w ∈ K) {X : Subgroup G}
    (hD : ∀ g : ↥K, (g : G) ∈ zpowers h ↔ ε g ∈ diagSub F)
    (hU : ∀ x : ↥K, (x : G) ∈ X ↔ ε x ∈ upperSub F) {s : SL2m F} (hs : s ∈ diagSub F)
    (hεw : ε ⟨w, hwK⟩ = s * w0 F) (k : ↥K) (hk : (ε k).1 1 0 ≠ 0) :
    ∃ x₁ ∈ X, ∃ δ ∈ zpowers h, ∃ x₂ ∈ X, (k : G) = x₁ * δ * w * x₂ := by
  obtain ⟨d, hd, hdec⟩ := exists_bruhat_decomp hk
  have hkeq : k = ε.symm (unipotent ((ε k).1 0 0 / (ε k).1 1 0)) * ε.symm (d * s⁻¹) *
      ⟨w, hwK⟩ * ε.symm (unipotent ((ε k).1 1 1 / (ε k).1 1 0)) := by
    apply ε.injective
    conv_lhs => rw [hdec]
    simp only [map_mul, ε.apply_symm_apply, hεw]
    group
  refine ⟨((ε.symm (unipotent ((ε k).1 0 0 / (ε k).1 1 0)) : ↥K) : G), ?_,
    ((ε.symm (d * s⁻¹) : ↥K) : G), ?_,
    ((ε.symm (unipotent ((ε k).1 1 1 / (ε k).1 1 0)) : ↥K) : G), ?_, ?_⟩
  · exact (hU _).2 (by rw [ε.apply_symm_apply]; exact unipotent_mem_upperSub _)
  · exact (hD _).2 (by rw [ε.apply_symm_apply]; exact mul_mem hd ((diagSub F).inv_mem hs))
  · exact (hU _).2 (by rw [ε.apply_symm_apply]; exact unipotent_mem_upperSub _)
  · conv_lhs => rw [hkeq]
    rfl

end SL2Root

open SL2Root

theorem sl2_diagAut_bruhat {G : Type} [Group G] [Finite G] (K : Subgroup G) (q p : ℕ)
    (hp : p.Prime) (hmod : CFSG.GH74.GLS.HasSL2Model ↥K (fun r => r = q)) (hodd : Odd q)
    (h5 : 5 ≤ q) (hpq : ∃ k : ℕ, 1 ≤ k ∧ q = p ^ k) (z : G)
    (_hz : (Subgroup.center ↥K).map K.subtype = Subgroup.zpowers z)
    (h w : G) (hhK : h ∈ K) (hwK : w ∈ K) (hord : orderOf h = q - 1) (hwsq : w * w = z)
    (hinv : ∀ k ∈ Subgroup.zpowers h, w * k * w⁻¹ = k⁻¹)
    (_hnorm : Subgroup.normalizer (Subgroup.zpowers h : Set G) ⊓ K =
      Subgroup.zpowers h ⊔ Subgroup.zpowers w)
    (X : Subgroup G) (hXK : X ≤ K) (hXcard : Nat.card ↥X = q)
    (hXn : ∀ g ∈ Subgroup.zpowers h, ∀ x ∈ X, g * x * g⁻¹ ∈ X) :
    (∃ α : ↥K ≃* ↥K, (∀ x : ↥K, (x : G) ∈ X → (α x : G) = (x : G)⁻¹) ∧
        (∀ g : ↥K, (g : G) ∈ Subgroup.zpowers h → α g = g) ∧
        (α ⟨w, hwK⟩ : G) = w * z ∧ ∀ k, α (α k) = k) ∧
    Subgroup.normalizer (X : Set G) ⊓ K = X ⊔ Subgroup.zpowers h ∧
    (∀ k ∈ K, k ∈ ((X ⊔ Subgroup.zpowers h : Subgroup G) : Set G) ∨
        k ∈ ((X ⊔ Subgroup.zpowers h : Subgroup G) : Set G) * {w} * (X : Set G)) ∧
    (∀ y ∈ CFSG.GH74.BNPair.conjBy w X, y ≠ 1 →
        y ∈ (X : Set G) * (Subgroup.zpowers h : Set G) * {w} * (X : Set G)) := by
  obtain ⟨F, _, _, ε, hD, hU, s, hs, hεw⟩ :=
    exists_upper_model K q p hp hmod hodd h5 hpq h w hhK hwK hord hinv X hXK hXcard hXn
  refine ⟨model_aut ε hwK (fun g hg => (hD g).1 hg) (fun x hx => (hU x).1 hx) hs hεw hwsq,
    model_normalizer ε hhK hXK hD hU hXn, ?_, ?_⟩
  · intro k hk
    by_cases h10 : (ε ⟨k, hk⟩).1 1 0 = 0
    · exact Or.inl (model_mem_borel ε hD hU ⟨k, hk⟩ h10)
    · right
      obtain ⟨x₁, hx₁, δ, hδ, x₂, hx₂, hkeq⟩ := model_bruhat_cell ε hwK hD hU hs hεw ⟨k, hk⟩ h10
      refine ⟨x₁ * δ * w, ⟨x₁ * δ, Subgroup.mul_mem_sup hx₁ hδ, w, rfl, rfl⟩, x₂, hx₂, ?_⟩
      exact hkeq.symm
  · intro y hy hy1
    rw [mem_conjBy_iff] at hy
    have hyK : y ∈ K := by
      have h1 : w⁻¹ * (w * y * w⁻¹) * w ∈ K :=
        mul_mem (mul_mem (K.inv_mem hwK) (hXK hy)) hwK
      simpa [mul_assoc] using h1
    have hlow : ε ⟨y, hyK⟩ ∈ lowerSub F := by
      have h1 : ((⟨w, hwK⟩ * ⟨y, hyK⟩ * ⟨w, hwK⟩⁻¹ : ↥K) : G) ∈ X := hy
      have h2 := (hU _).1 h1
      rw [map_mul, map_mul, map_inv, hεw] at h2
      exact (conj_sw0_mem_upperSub_iff hs _).1 h2
    have hc : (ε ⟨y, hyK⟩).1 1 0 ≠ 0 := by
      intro h0
      apply hy1
      obtain ⟨h00, h11, h01⟩ := hlow
      have h1 : ε ⟨y, hyK⟩ = 1 := by
        apply sl2_ext <;> simp [h00, h11, h01, h0]
      have h2 : (⟨y, hyK⟩ : ↥K) = 1 := ε.injective (h1.trans (map_one ε).symm)
      exact congrArg Subtype.val h2
    obtain ⟨x₁, hx₁, δ, hδ, x₂, hx₂, hkeq⟩ := model_bruhat_cell ε hwK hD hU hs hεw ⟨y, hyK⟩ hc
    exact ⟨x₁ * δ * w, ⟨x₁ * δ, ⟨x₁, hx₁, δ, hδ, rfl⟩, w, rfl, rfl⟩, x₂, hx₂, hkeq.symm⟩

end CFSG.GH74.GLS.SP.Local
