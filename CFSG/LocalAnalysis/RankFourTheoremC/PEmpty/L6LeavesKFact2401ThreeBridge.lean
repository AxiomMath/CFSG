module

public import CFSG.Open.GeneratedCore
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Bridge2401

theorem ne_bot_of_one_le_pRank {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {R : Subgroup G} (h : 1 ≤ CFSG.Open.pRank p R) : R ≠ ⊥ := by
  rintro rfl
  obtain ⟨E, hE, -, hc⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊥ : Subgroup G)
  rw [le_bot_iff.mp hE, Subgroup.card_bot] at hc
  have h0 : CFSG.Open.pRank p (⊥ : Subgroup G) = 0 := by
    by_contra hne
    have h1 := Nat.one_lt_pow hne hp.one_lt
    rw [← hc] at h1
    exact lt_irrefl 1 h1
  omega

theorem coe_mem_normalizer_map {A : Type} [Group A] {L : Subgroup A} {R : Subgroup L} {g : L}
    (hg : g ∈ Subgroup.normalizer (R : Set L)) :
    (g : A) ∈ Subgroup.normalizer ((R.map L.subtype : Subgroup A) : Set A) := by
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  change ∀ y : L, y ∈ R ↔ g * y * g⁻¹ ∈ R at hg
  change ∀ h : A, h ∈ R.map L.subtype ↔ (g : A) * h * (g : A)⁻¹ ∈ R.map L.subtype
  have hinj : Function.Injective L.subtype := Subtype.val_injective
  have hle : R.map L.subtype ≤ L := Subgroup.map_subtype_le R
  intro h
  by_cases hh : h ∈ L
  · obtain ⟨y, rfl⟩ : ∃ y : L, (y : A) = h := ⟨⟨h, hh⟩, rfl⟩
    have e1 : (y : A) ∈ R.map L.subtype ↔ y ∈ R := by
      have := Subgroup.mem_map_iff_mem (f := L.subtype) hinj (K := R) (x := y)
      simpa using this
    have e2 : (g : A) * (y : A) * (g : A)⁻¹ ∈ R.map L.subtype ↔ g * y * g⁻¹ ∈ R := by
      have hc : (g : A) * (y : A) * (g : A)⁻¹ = ((g * y * g⁻¹ : L) : A) := by simp
      rw [hc]
      have := Subgroup.mem_map_iff_mem (f := L.subtype) hinj (K := R) (x := g * y * g⁻¹)
      simpa using this
    rw [e1, e2]
    exact hg y
  · have hh' : (g : A) * h * (g : A)⁻¹ ∉ L := by
      intro hc
      apply hh
      have hid : h = (g : A)⁻¹ * ((g : A) * h * (g : A)⁻¹) * (g : A) := by group
      rw [hid]
      exact L.mul_mem (L.mul_mem (L.inv_mem g.2) hc) g.2
    exact ⟨fun hx => absurd (hle hx) hh, fun hx => absurd (hle hx) hh'⟩

theorem normalizer_le_subgroupOf {A : Type} [Group A] [Finite A] {L E J : Subgroup A}
    {Q : Subgroup L} (hQ : Q.map L.subtype = E)
    (hJ : ∀ S₀ : Subgroup A, S₀ ≤ E → S₀ ≠ ⊥ → Subgroup.normalizer (S₀ : Set A) ⊓ L ≤ J)
    {R : Subgroup L} (hRQ : R ≤ Q) (hR : 1 ≤ CFSG.Open.pRank 3 R) :
    Subgroup.normalizer (R : Set L) ≤ J.subgroupOf L := by
  intro g hg
  rw [Subgroup.mem_subgroupOf]
  have hS : R.map L.subtype ≤ E := (Subgroup.map_mono hRQ).trans hQ.le
  have hne : R.map L.subtype ≠ ⊥ := by
    intro h0
    apply ne_bot_of_one_le_pRank (G := L) Nat.prime_three hR
    ext x
    constructor
    · intro hx
      have hx' : L.subtype x ∈ R.map L.subtype := ⟨x, hx, rfl⟩
      rw [h0, Subgroup.mem_bot] at hx'
      rw [Subgroup.mem_bot]
      exact Subtype.ext (by simpa using hx')
    · intro hx
      rw [Subgroup.mem_bot] at hx
      rw [hx]
      exact R.one_mem
  exact hJ _ hS hne ⟨coe_mem_normalizer_map hg, g.2⟩

theorem le_of_glbCore_eq_top {A : Type} [Group A] [Finite A] {L E J : Subgroup A}
    {Q : Sylow 3 L} (hQ : (Q : Subgroup L).map L.subtype = E)
    (hJ : ∀ S₀ : Subgroup A, S₀ ≤ E → S₀ ≠ ⊥ → Subgroup.normalizer (S₀ : Set A) ⊓ L ≤ J)
    (htop : CFSG.Open.GLBCore 3 1 (Q : Subgroup L) = ⊤) : L ≤ J := by
  have hle : CFSG.Open.GLBCore 3 1 (Q : Subgroup L) ≤ J.subgroupOf L := by
    unfold CFSG.Open.GLBCore
    apply sSup_le
    rintro N ⟨R, hRQ, hR, rfl⟩
    exact normalizer_le_subgroupOf hQ hJ hRQ hR
  rw [htop] at hle
  intro x hx
  exact Subgroup.mem_subgroupOf.mp (hle (Subgroup.mem_top ⟨x, hx⟩))

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Bridge2401

end
