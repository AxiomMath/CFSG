module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.FreeTranslatesBridge

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.FreeTranslates

open CFSG.LocalAnalysis.RankThreeUC

section Quotient

variable {G : Type} [Group G] {P Q : Subgroup G}

@[reducible] private def quotCommGroup [(P.subgroupOf Q).Normal]
    (hcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ P) : CommGroup (↥Q ⧸ P.subgroupOf Q) :=
  { (inferInstance : Group (↥Q ⧸ P.subgroupOf Q)) with
    mul_comm := by
      intro a b
      induction a using QuotientGroup.induction_on with | H x => ?_
      induction b using QuotientGroup.induction_on with | H y => ?_
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have h := hcomm _ (Q.inv_mem y.2) _ (Q.inv_mem x.2)
      have e : (((x * y)⁻¹ * (y * x) : ↥Q) : G) =
          (y : G)⁻¹ * (x : G)⁻¹ * (y : G)⁻¹⁻¹ * (x : G)⁻¹⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e]
      exact h }

private def conjQuotEnd [Q.Normal] [P.Normal] : G →* Monoid.End (↥Q ⧸ P.subgroupOf Q) where
  toFun g := QuotientGroup.map (P.subgroupOf Q) (P.subgroupOf Q) (MulAut.conjNormal (H := Q) g).toMonoidHom
    (fun y hy => by
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
      rw [Subgroup.mem_subgroupOf] at hy
      simpa using (inferInstance : P.Normal).conj_mem _ hy g)
  map_one' := by
    refine MonoidHom.ext fun a => ?_
    induction a using QuotientGroup.induction_on with | H y => ?_
    show (QuotientGroup.mk (MulAut.conjNormal (1 : G) y) : ↥Q ⧸ P.subgroupOf Q) = QuotientGroup.mk y
    rw [map_one]
    rfl
  map_mul' g h := by
    refine MonoidHom.ext fun a => ?_
    induction a using QuotientGroup.induction_on with | H y => ?_
    show (QuotientGroup.mk (MulAut.conjNormal (g * h) y) : ↥Q ⧸ P.subgroupOf Q) =
      QuotientGroup.mk (MulAut.conjNormal g (MulAut.conjNormal h y))
    rw [map_mul]
    rfl

end Quotient

variable {G : Type} [Group G] [Finite G]

theorem mem_of_support_card_lt {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : BinaryActionRankCounterexample G p P T B e ρ)
    (hker : ∀ s ∈ twoCoreCommutator T B, s ∈ Subgroup.normalizer ((⁅B, P⁆ : Subgroup G) : Set G) →
      ∀ E ∈ Delta p P ρ, E.map (MulAut.conj s).toMonoidHom = E)
    {B₀ : Subgroup G} (hB₀B : B₀ ≤ B) (hB₀ : B₀ ≠ ⊥)
    {Q : Subgroup G} (hQn : Q.Normal) (_hPQ : P ≤ Q)
    (hQcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ P)
    (hfix : ∀ b ∈ B₀, b ≠ 1 → ∀ y ∈ Q, b * y * b⁻¹ * y⁻¹ ∈ P → y ∈ P)
    (R : Subgroup G → Subgroup G) (hRP : ∀ D ∈ Delta p P ρ, P ≤ R D)
    (_hRQ : ∀ D ∈ Delta p P ρ, R D ≤ Q)
    (hRG : ∀ g : G, ∀ D ∈ Delta p P ρ,
      (R D).map (MulAut.conj g).toMonoidHom = R (D.map (MulAut.conj g).toMonoidHom))
    (hint : ∀ x ∈ Q, (∀ D ∈ Delta p P ρ, x ∈ R D) → x ∈ P)
    {Γ : Set (Subgroup G)} (hΓ : Γ ⊆ Delta p P ρ)
    (hcount : (Nat.card B₀ - 1) * Nat.card ↥Γ ^ 2 < Nat.card ↥(Delta p P ρ))
    {x : G} (hx : x ∈ Q) (hxR : ∀ D ∈ Delta p P ρ, D ∉ Γ → x ∈ R D) :
    x ∈ P := by
  classical
  have hP : P.Normal := hc.faithfulBinaryIrreducibleAction.normal
  haveI : P.Normal := hP
  haveI : Q.Normal := hQn
  letI : CommGroup (↥Q ⧸ P.subgroupOf Q) := quotCommGroup hQcomm
  haveI : Finite (Subgroup G) := Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  let rad : ↥(Delta p P ρ) → Subgroup (↥Q ⧸ P.subgroupOf Q) := fun D =>
    ((R D.1).subgroupOf Q).map (QuotientGroup.mk' (P.subgroupOf Q))
  have hmap : ∀ (g : G) (D : ↥(Delta p P ρ)) (z : ↥Q ⧸ P.subgroupOf Q), z ∈ rad D →
      conjQuotEnd (P := P) (Q := Q) g z ∈
        rad (DeltaConjugationAction.act hP ρ g D) := by
    intro g D z hz
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
    refine Subgroup.mem_map.mpr ⟨MulAut.conjNormal g y, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    have h1 := hRG g D.1 D.2
    have h2 : (g * (y : G) * g⁻¹) ∈ (R D.1).map (MulAut.conj g).toMonoidHom :=
      ⟨y, hy, by simp [MulAut.conj_apply]⟩
    rw [h1] at h2
    exact h2
  have hbot : ∀ z : ↥Q ⧸ P.subgroupOf Q, (∀ D, z ∈ rad D) → z = 1 := by
    intro z hz
    induction z using QuotientGroup.induction_on with | H y => ?_
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    refine hint y y.2 fun D hD => ?_
    obtain ⟨w, hw, hwy⟩ := Subgroup.mem_map.mp (hz ⟨D, hD⟩)
    rw [Subgroup.mem_subgroupOf] at hw
    have hwy' : (w⁻¹ * y : ↥Q) ∈ P.subgroupOf Q := QuotientGroup.eq.mp hwy
    rw [Subgroup.mem_subgroupOf] at hwy'
    have h3 : (y : G) = (w : G) * ((w : G)⁻¹ * (y : G)) := by group
    rw [h3]
    exact (R D).mul_mem hw (hRP D hD (by simpa using hwy'))
  have hM : ∀ b ∈ B₀, b ≠ 1 → ∀ z : ↥Q ⧸ P.subgroupOf Q,
      conjQuotEnd (P := P) (Q := Q) b z = z → z = 1 := by
    intro b hb hb1 z hz
    induction z using QuotientGroup.induction_on with | H y => ?_
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    refine hfix b hb hb1 y y.2 ?_
    have h4 := QuotientGroup.eq_iff_div_mem.mp hz
    rw [Subgroup.mem_subgroupOf] at h4
    simpa [div_eq_mul_inv] using h4
  obtain ⟨b₁, hb₁⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB₀
  have hBnt : ∃ b ∈ B₀, b ≠ 1 := ⟨b₁, b₁.2, fun h => hb₁ (Subtype.ext h)⟩
  have hc' := (regularConfig_of_counterexample hc hker).mono hB₀B
  have hΓ' : (Subtype.val ⁻¹' Γ : Set ↥(Delta p P ρ)).ncard = Nat.card ↥Γ := by
    rw [Set.ncard_preimage_of_injective_subset_range Subtype.val_injective
      (by rw [Subtype.range_coe]; exact hΓ), Nat.card_coe_set_eq]
  have hcount' : (Nat.card B₀ - 1) * (Subtype.val ⁻¹' Γ : Set ↥(Delta p P ρ)).ncard ^ 2 <
      Nat.card ↥(Delta p P ρ) := by
    rw [hΓ']
    exact hcount
  have hsupp : (QuotientGroup.mk ⟨x, hx⟩ : ↥Q ⧸ P.subgroupOf Q) ∈
      supported rad (Subtype.val ⁻¹' Γ : Set ↥(Delta p P ρ)) := by
    rw [mem_supported]
    intro D hD
    exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩, Subgroup.mem_subgroupOf.mpr (hxR D.1 D.2 hD), rfl⟩
  have h1 := eq_one_of_card_lt (conjQuotEnd (P := P) (Q := Q)) rad hmap hbot hc' hBnt hM hcount' hsupp
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  exact h1

end CFSG.LocalAnalysis.RankThreeUC.Section5.FreeTranslates
