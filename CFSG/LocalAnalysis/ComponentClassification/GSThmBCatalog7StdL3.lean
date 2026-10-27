module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdRows

public section

namespace CFSG.ComponentClassification.GSThmB

namespace Catalog7Std

open CFSG Subgroup

@[expose] def L3EpsL2Input : Prop :=
  ∀ (H : Type) [Group H] [Finite H], IsSimpleGroup ↥(generalizedFitting H) →
    centralizer (generalizedFitting H : Set H) = ⊥ →
    ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    (Blueprint.LieModel ↥(generalizedFitting H) .PSL 3 p f ∨
      Blueprint.LieModel ↥(generalizedFitting H) .PSU 3 p f) →
    ∀ x : H, orderOf x = 2 → ∀ L : Subgroup H, L ≤ generalizedFitting H →
      L ≤ centralizer ({x} : Set H) → IsPComponent 2 (L.subgroupOf (centralizer ({x} : Set H))) →
      ∀ p' f' : ℕ, p'.Prime → p' ≠ 2 → 1 ≤ f' → 5 ≤ p' ^ f' →
        Blueprint.LieModel (L ⧸ pPrimeCore 2 L) .PSL 2 p' f' → p' = p ∧ f' = f

variable {H : Type} [Group H] [Finite H]

theorem StdConf.false_of_l3eps (h : L3EpsL2Input) (c : StdConf H) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hm : Blueprint.LieModel ↥(generalizedFitting H) .PSL 3 p f ∨
      Blueprint.LieModel ↥(generalizedFitting H) .PSU 3 p f) : False := by
  have hf1 := c.one_le
  have h5 := c.five_le
  have hq2 : 5 ≤ c.p ^ (2 * c.f) :=
    h5.trans (Nat.pow_le_pow_right c.prime.pos (by omega))
  obtain ⟨-, hK⟩ := h H c.simple c.centralizer_eq_bot p f hp hp2 hf hm c.b c.orderOf_b c.K
    c.K_le_G c.K_le c.isPComponent_K c.p (2 * c.f) c.prime c.ne_two (by omega) hq2 c.type_K
  obtain ⟨-, hJ⟩ := h H c.simple c.centralizer_eq_bot p f hp hp2 hf hm c.a c.orderOf_a c.J
    c.J_le_G c.J_le c.isPComponent_J c.p c.f c.prime c.ne_two c.one_le h5 c.type_J
  omega

theorem rowL3 (h : L3EpsL2Input) : RowL3 := fun _ _ _ c _ _ hp hp2 hf hm =>
  c.false_of_l3eps h hp hp2 hf (Or.inl hm)

theorem rowU3 (h : L3EpsL2Input) : RowU3 := fun _ _ _ c _ _ hp hp2 hf hm =>
  c.false_of_l3eps h hp hp2 hf (Or.inr hm)

end Catalog7Std

end CFSG.ComponentClassification.GSThmB
