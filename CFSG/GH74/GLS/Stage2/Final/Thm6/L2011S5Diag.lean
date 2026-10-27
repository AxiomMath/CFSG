module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011Frat
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2012NFModel
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2012NFOuter

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Final.Thm6.L2012

variable {Y : Type} [Group Y]

theorem inf_sup_zpowers {K₁ K₂ : Subgroup Y} {w : Y} (hw₂ : w ∈ normalizer (K₂ : Set Y))
    (hw2 : w * w = 1) (hwK : w ∉ K₁ ⊔ K₂) : K₁ ⊓ (K₂ ⊔ zpowers w) = K₁ ⊓ K₂ := by
  apply le_antisymm
  · rintro x ⟨hx₁, hx⟩
    refine ⟨hx₁, ?_⟩
    rcases mem_sup_zpowers_cases' hw₂ hw2 hx with h | ⟨n, hn, hxn⟩
    · exact h
    · exfalso
      apply hwK
      have : w = n⁻¹ * x := by rw [hxn]; group
      rw [this]
      exact Subgroup.mul_mem _ (mem_sup_right (K₂.inv_mem hn)) (mem_sup_left hx₁)
  · exact inf_le_inf_left _ le_sup_left

theorem le_normalizer_of_commute {K₁ K₂ : Subgroup Y} (hcomm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) :
    K₂ ≤ normalizer (K₁ : Set Y) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have : b * h * b⁻¹ = h := by
      have := hcomm h hh b hb
      calc b * h * b⁻¹ = (b * h) * b⁻¹ := rfl
        _ = (h * b) * b⁻¹ := by rw [this]
        _ = h := by group
    rw [this]; exact hh
  · intro hh
    have hc := hcomm _ hh b hb
    have : h = b * h * b⁻¹ := by
      calc h = b⁻¹ * ((b * h * b⁻¹) * b) := by group
        _ = b⁻¹ * (b * (b * h * b⁻¹)) := by rw [hc]
        _ = b * h * b⁻¹ := by group
    rwa [← this] at hh

theorem quot_iso_of_pgl {K₁ K₂ : Subgroup Y} {w : Y} {q : ℕ}
    (hZ : (center ↥K₂).map K₂.subtype = K₁ ⊓ K₂)
    (hcomm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (hw₁ : w ∈ normalizer (K₁ : Set Y)) (hw₂ : w ∈ normalizer (K₂ : Set Y)) (hw2 : w * w = 1)
    (hwK : w ∉ K₁ ⊔ K₂) (hpgl : PGLOver K₂ (zpowers w) q)
    (X : Subgroup Y) (hX₁ : K₁ ≤ X) (hX₂ : K₂ ⊔ zpowers w ≤ X) (hX : X ≤ K₁ ⊔ (K₂ ⊔ zpowers w)) :
    ∃ _ : (K₁.subgroupOf X).Normal, IVK.IsPGL2 (↥X ⧸ K₁.subgroupOf X) (fun r => r = q) := by
  have hY2N : K₂ ⊔ zpowers w ≤ normalizer (K₁ : Set Y) :=
    sup_le (le_normalizer_of_commute hcomm) (zpowers_le.2 hw₁)
  have hXN : X ≤ normalizer (K₁ : Set Y) := hX.trans (sup_le Subgroup.le_normalizer hY2N)
  have hN : (K₁.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hX₁).2 hXN
  obtain ⟨hn, F₀, hF₀, hFin₀, hF₀q, ⟨e₀⟩⟩ := hpgl
  refine ⟨hN, F₀, hF₀, hFin₀, hF₀q, ⟨?_⟩⟩
  let φ : ↥(K₂ ⊔ zpowers w) →* ↥X ⧸ K₁.subgroupOf X :=
    (QuotientGroup.mk' (K₁.subgroupOf X)).comp (Subgroup.inclusion hX₂)
  have hsurj : Function.Surjective φ := by
    intro a
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    have hx : (x : Y) ∈ ((K₁ ⊔ (K₂ ⊔ zpowers w) : Subgroup Y) : Set Y) := hX x.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left K₁ (K₂ ⊔ zpowers w) hY2N] at hx
    obtain ⟨a₁, ha₁, y, hy, hxy⟩ := hx
    refine ⟨⟨y, hy⟩, ?_⟩
    show QuotientGroup.mk' (K₁.subgroupOf X) (Subgroup.inclusion hX₂ ⟨y, hy⟩) = QuotientGroup.mk x
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hyinv : y⁻¹ ∈ normalizer (K₁ : Set Y) := (normalizer (K₁ : Set Y)).inv_mem (hY2N hy)
    have h1 := (Subgroup.mem_normalizer_iff.1 hyinv a₁).1 ha₁
    simp only [inv_inv] at h1
    show (y : Y)⁻¹ * (x : Y) ∈ K₁
    rw [← hxy]
    simpa [mul_assoc] using h1
  have hker : φ.ker = (K₁ ⊓ K₂).subgroupOf (K₂ ⊔ zpowers w) := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show QuotientGroup.mk' (K₁.subgroupOf X) (Subgroup.inclusion hX₂ y) = 1 ↔ (y : Y) ∈ K₁ ⊓ K₂
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    show (y : Y) ∈ K₁ ↔ (y : Y) ∈ K₁ ⊓ K₂
    constructor
    · intro hy1
      have : (y : Y) ∈ K₁ ⊓ (K₂ ⊔ zpowers w) := ⟨hy1, y.2⟩
      rwa [inf_sup_zpowers hw₂ hw2 hwK] at this
    · exact fun h => h.1
  have hker' : φ.ker = ((center ↥K₂).map K₂.subtype).subgroupOf (K₂ ⊔ zpowers w) := by
    rw [hker, hZ]
  exact ((QuotientGroup.quotientKerEquivOfSurjective φ hsurj).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker')).trans e₀

theorem isDiagInv_of_pgl {K₁ K₂ : Subgroup Y} {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁] [Finite F₂]
    {q : ℕ} (hPr : IVK.ProdSL2 Y K₁ K₂ F₁ F₂) (hF₁ : Nat.card F₁ = q) (hF₂ : Nat.card F₂ = q)
    {w : Y} (hw2 : w * w = 1) (hw₁ : w ∈ normalizer (K₁ : Set Y)) (hw₂ : w ∈ normalizer (K₂ : Set Y))
    (hwK : w ∉ K₁ ⊔ K₂) (hp₁ : PGLOver K₁ (zpowers w) q) (hp₂ : PGLOver K₂ (zpowers w) q) :
    IVK.IsDiagInv K₁ K₂ F₁ F₂ w := by
  obtain ⟨ζ, hζ, hζ1⟩ := IVK.Proofs2.Lemma31g.exists_nontrivial_inter hPr
  have hZ₂ : (center ↥K₂).map K₂.subtype = K₁ ⊓ K₂ := center_map_eq_inf hPr hζ hζ1
  have hζ' : ζ ∈ K₂ ⊓ K₁ := by rwa [inf_comm] at hζ
  have hZ₁ : (center ↥K₁).map K₁.subtype = K₂ ⊓ K₁ := center_map_eq_inf hPr.symm hζ' hζ1
  have hcomm₂ : ∀ a ∈ K₂, ∀ b ∈ K₁, a * b = b * a := fun a ha b hb => (hPr.comm b hb a ha).symm
  have hwK' : w ∉ K₂ ⊔ K₁ := by rwa [sup_comm] at hwK
  refine ⟨fun x hx => (Subgroup.mem_normalizer_iff.1 hw₁ x).1 hx,
    fun x hx => (Subgroup.mem_normalizer_iff.1 hw₂ x).1 hx, ?_, ?_⟩
  · obtain ⟨hN, F₀, hF₀, hFin₀, hF₀q, ⟨e₀⟩⟩ := quot_iso_of_pgl hZ₂ hPr.comm hw₁ hw₂ hw2 hwK hp₂
      (K₁ ⊔ K₂ ⊔ zpowers w) (le_sup_of_le_left le_sup_left)
      (sup_le (le_sup_of_le_left le_sup_right) le_sup_right) (by rw [sup_assoc])
    refine ⟨hN, ⟨?_⟩⟩
    have := Fintype.ofFinite F₀
    have := Fintype.ofFinite F₂
    have hc : Fintype.card F₀ = Fintype.card F₂ := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF₀q, hF₂]
    exact e₀.trans (CFSG.GorensteinWalter.pgl2RingEquiv (FiniteField.ringEquivOfCardEq hc))
  · obtain ⟨hN, F₀, hF₀, hFin₀, hF₀q, ⟨e₀⟩⟩ := quot_iso_of_pgl hZ₁ hcomm₂ hw₂ hw₁ hw2 hwK' hp₁
      (K₁ ⊔ K₂ ⊔ zpowers w) (le_sup_of_le_left le_sup_right)
      (sup_le (le_sup_of_le_left le_sup_left) le_sup_right) (by rw [sup_assoc, sup_left_comm])
    refine ⟨hN, ⟨?_⟩⟩
    have := Fintype.ofFinite F₀
    have := Fintype.ofFinite F₁
    have hc : Fintype.card F₀ = Fintype.card F₁ := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF₀q, hF₁]
    exact e₀.trans (CFSG.GorensteinWalter.pgl2RingEquiv (FiniteField.ringEquivOfCardEq hc))

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011
