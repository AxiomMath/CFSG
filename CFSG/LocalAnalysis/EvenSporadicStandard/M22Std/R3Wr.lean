module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutSetup
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.XbarSetup

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.EvenSporadicStandard.M23Std

@[expose] def OuterWr (Xb : Type) [Group Xb] [Finite Xb] (zb : Xb) : Prop :=
  ∃ B : Subgroup Xb, B.index = 2 ∧ zb ∉ B ∧
    (∀ q ∈ B, q * q = 1 → q ≠ 1 → 128 ∣ Nat.card (centralizer ({q} : Set Xb))) ∧
    ∀ P : Subgroup Xb, IsPGroup 2 P → ¬ 2 ∣ P.index → zb ∈ P →
      ∀ y0 ∈ P, y0 * y0 = 1 → y0 ∉ B → y0 ∈ centralizer ({zb} : Set Xb) →
        y0 ∉ zpowers zb ⊔ (commutator ↥(centralizer ({zb} : Set Xb))).map
          (centralizer ({zb} : Set Xb)).subtype →
        (∀ y ∈ P, y * y = 1 → y ∉ B →
          (∃ c ∈ P, y = c⁻¹ * zb * c) ∨ (∃ c ∈ P, y = c⁻¹ * y0 * c)) ∧
        (IsConj zb y0 → ∃ c ∈ P, y0 = c⁻¹ * zb * c)

variable {G : Type} [Group G]

@[expose] def preimageX (L1 : Subgroup G) (B : Subgroup (Xbar L1)) : Subgroup G :=
  (B.comap (QuotientGroup.mk' ((centralizer (L1 : Set G)).subgroupOf
    (normalizer (L1 : Set G))))).map (normalizer (L1 : Set G)).subtype

theorem mem_preimageX_iff {L1 : Subgroup G} {B : Subgroup (Xbar L1)} {g : G} :
    g ∈ preimageX L1 B ↔
      ∃ hg : g ∈ normalizer (L1 : Set G), (QuotientGroup.mk ⟨g, hg⟩ : Xbar L1) ∈ B := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, h, rfl⟩

theorem rho_L1 {L : Subgroup G} {z : G} {F L1 N : Subgroup G} (S : OutSetup L z F L1 N) {l : G}
    (hl : l ∈ L1) : (QuotientGroup.mk ⟨l, Subgroup.le_normalizer hl⟩ : Xbar L1) = 1 := by
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  exact mem_centralizer_iff.2 fun x hx => S.L1_comm x hx l hl

end CFSG.EvenSporadicStandard.M22Std
