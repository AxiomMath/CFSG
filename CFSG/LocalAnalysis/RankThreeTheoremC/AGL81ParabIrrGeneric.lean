module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommGeneric

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm

variable {A : Type} [Group A]

@[expose] def IrredOn (N B : Subgroup A) : Prop :=
  ∀ V : Subgroup A, V ≤ B → ¬ V ≤ (frattini ↥B).map B.subtype →
    N ≤ Subgroup.normalizer (V : Set A) → V = B

theorem isCyclic_of_le_frattini [Finite A] {B V : Subgroup A} {x : A} (hx : x ∈ B)
    (hB : B ≤ V ⊔ Subgroup.zpowers x) (hV : V ≤ (frattini ↥B).map B.subtype) :
    IsCyclic ↥B := by
  set H : Subgroup ↥B := Subgroup.zpowers (⟨x, hx⟩ : ↥B) ⊔ frattini ↥B with hH
  have hmap : H.map B.subtype = Subgroup.zpowers x ⊔ (frattini ↥B).map B.subtype := by
    rw [hH, Subgroup.map_sup, MonoidHom.map_zpowers]
    rfl
  have htop : H = ⊤ := by
    refine eq_top_iff.2 fun b _ => ?_
    have hb : (b : A) ∈ H.map B.subtype := by
      rw [hmap]
      exact sup_le (hV.trans le_sup_right) le_sup_left (hB b.2)
    obtain ⟨c, hc, hce⟩ := hb
    rwa [show c = b from Subtype.ext hce] at hc
  have hz := frattini_nongenerating htop
  exact isCyclic_iff_exists_zpowers_eq_top.2 ⟨_, hz⟩

theorem eq_of_le_sup_zpowers [Finite A] {N B V : Subgroup A} (hcyc : ¬ IsCyclic ↥B)
    (hN : IrredOn N B) (hVB : V ≤ B) (hNV : N ≤ Subgroup.normalizer (V : Set A)) {x : A}
    (hx : x ∈ B) (hB : B ≤ V ⊔ Subgroup.zpowers x) : V = B :=
  hN V hVB (fun hV => hcyc (isCyclic_of_le_frattini hx hB hV)) hNV

theorem forall_eq_one_of_irred [Finite A] {N B : Subgroup A} (hcyc : ¬ IsCyclic ↥B)
    (hN : IrredOn N B) (hNB : N ≤ Subgroup.normalizer (B : Set A)) {K : Type*} [Field K]
    (θ : ↥B →* Kˣ)
    (hθ : ∀ n ∈ N, ∀ b : ↥B, θ b = 1 → ∀ hb : n * (b : A) * n⁻¹ ∈ B, θ ⟨_, hb⟩ = 1) :
    ∀ b, θ b = 1 := by
  set V : Subgroup A := θ.ker.map B.subtype with hV
  have hVB : V ≤ B := by
    rintro _ ⟨b, -, rfl⟩
    exact b.2
  have hNV : N ≤ Subgroup.normalizer (V : Set A) := by
    intro n hn
    haveI : Finite ↥V := inferInstance
    refine Subgroup.mem_normalizer_fintype fun v hv => ?_
    obtain ⟨b, hb, rfl⟩ := hv
    have hnb : n * (b : A) * n⁻¹ ∈ B :=
      (Subgroup.mem_normalizer_iff.1 (hNB hn) b).1 b.2
    exact ⟨⟨_, hnb⟩, hθ n hn b hb hnb, rfl⟩
  haveI : Finite ↥θ.range := Finite.of_surjective _ θ.rangeRestrict_surjective
  haveI : IsCyclic θ.range :=
    isCyclic_of_injective_ringHom ((Units.coeHom K).comp θ.range.subtype)
      (fun a b h => Subtype.ext (Units.ext h))
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := θ.range)
  obtain ⟨c, hc⟩ := g.2
  have hBle : B ≤ V ⊔ Subgroup.zpowers (c : A) := by
    intro a ha
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨θ ⟨a, ha⟩, ⟨a, ha⟩, rfl⟩)
    have hk' : θ (c ^ k) = θ ⟨a, ha⟩ := by
      rw [map_zpow, hc]
      exact congrArg Subtype.val hk
    have hker : (⟨a, ha⟩ * (c ^ k)⁻¹ : ↥B) ∈ θ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hk', mul_inv_cancel]
    have h1 : ((⟨a, ha⟩ * (c ^ k)⁻¹ : ↥B) : A) ∈ V := ⟨_, hker, rfl⟩
    have hmem : ((⟨a, ha⟩ * (c ^ k)⁻¹ : ↥B) : A) * (c : A) ^ k ∈ V ⊔ Subgroup.zpowers (c : A) :=
      Subgroup.mul_mem _ (le_sup_left (b := Subgroup.zpowers (c : A)) h1)
        (le_sup_right (a := V) (Subgroup.zpow_mem_zpowers (c : A) k))
    simpa using hmem
  have hVeq := eq_of_le_sup_zpowers hcyc hN hVB hNV c.2 hBle
  intro b
  have hb : (b : A) ∈ V := by
    rw [hVeq]
    exact b.2
  obtain ⟨b', hb', hbe⟩ := hb
  rwa [show b' = b from Subtype.ext hbe] at hb'

theorem ker_invariant_of_eq_centralizer {B Y : Subgroup A} {K : Type*} [Monoid K] (θ : ↥B →* K)
    (hθ : ∀ b : ↥B, θ b = 1 ↔ ∀ y ∈ Y, (b : A) * y = y * b) {n : A}
    (hnY : n ∈ Subgroup.normalizer (Y : Set A)) (b : ↥B) (hb1 : θ b = 1)
    (hb : n * (b : A) * n⁻¹ ∈ B) : θ ⟨_, hb⟩ = 1 := by
  rw [hθ] at hb1 ⊢
  intro y hy
  have hy' : n⁻¹ * y * n⁻¹⁻¹ ∈ Y :=
    (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hnY) y).1 hy
  have h := hb1 _ hy'
  calc n * (b : A) * n⁻¹ * y = n * ((b : A) * (n⁻¹ * y * n⁻¹⁻¹)) * n⁻¹ := by group
    _ = n * ((n⁻¹ * y * n⁻¹⁻¹) * b) * n⁻¹ := by rw [h]
    _ = y * (n * (b : A) * n⁻¹) := by group

@[expose] def ParabIrrOn (𝔉 : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (Y P B N : Subgroup A) (p : ℕ), p.Prime → p ≠ 2 →
    Open.IsQuasisimple ↥Y → pCoreOf 2 Y = ⊥ → 𝔉 (↥Y ⧸ Subgroup.center ↥Y) →
    IsParabolicTwo Y P → P ≠ Y → (∃ x ∈ P, ∃ y ∈ P, x * y * x⁻¹ * y⁻¹ ∉ pCoreOf 2 P) →
    IsPGroup p ↥B → ¬ IsCyclic ↥B → B ≤ Subgroup.normalizer (Y : Set A) →
    B ≤ Subgroup.normalizer (P : Set A) → (∀ b ∈ B, WCent P b) →
    N ≤ Subgroup.normalizer (Y : Set A) → N ≤ Subgroup.normalizer (P : Set A) →
    N ≤ Subgroup.normalizer (B : Set A) → IrredOn N B →
    (∀ b ∈ B, ∀ y ∈ Y, b * y = y * b) ∨ 4 ≤ Open.pRank p Y

theorem parabIrrOn_or {𝔉₁ 𝔉₂ : ∀ (X : Type) [Group X], Prop} (h₁ : ParabIrrOn 𝔉₁)
    (h₂ : ParabIrrOn 𝔉₂) : ParabIrrOn fun X _ => 𝔉₁ X ∨ 𝔉₂ X :=
  fun A _ _ Y P B N p hp hp2 hY h2 hF =>
    hF.elim (h₁ A Y P B N p hp hp2 hY h2) (h₂ A Y P B N p hp hp2 hY h2)

theorem ParabIrrOn.mono {𝔉₁ 𝔉₂ : ∀ (X : Type) [Group X], Prop} (h : ParabIrrOn 𝔉₂)
    (himp : ∀ (X : Type) [Group X], 𝔉₁ X → 𝔉₂ X) : ParabIrrOn 𝔉₁ :=
  fun A _ _ Y P B N p hp hp2 hY h2 hF => h A Y P B N p hp hp2 hY h2 (himp _ hF)

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr
