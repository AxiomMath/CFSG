module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4Order
public import CFSG.HardMathSupport.Lang.AnisoE6.TwPlane

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.HardMathSupport.Lang.AnisoE6 CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open

set_option linter.unusedSectionVars false

theorem exists_conj_le_range_of_factorization {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (φ : H →* G) (hφ : Function.Injective φ) {p : ℕ} [hp : Fact p.Prime]
    (hord : (Nat.card G).factorization p = (Nat.card H).factorization p)
    (E : Subgroup G) (hE : IsPGroup p E) :
    ∃ g : G, E.map (MulAut.conj g).toMonoidHom ≤ φ.range := by
  obtain ⟨K₀, hK₀⟩ := Sylow.exists_subgroup_card_pow_prime p (Nat.ordProj_dvd (Nat.card H) p)
  set P : Subgroup G := K₀.map φ with hPdef
  have hPle : P ≤ φ.range := by
    rw [hPdef]
    exact Subgroup.map_le_range φ K₀
  have hPcard : Nat.card P = p ^ (Nat.card G).factorization p := by
    rw [hPdef, Subgroup.card_map_of_injective hφ, hK₀, hord]
  have hP : IsPGroup p P := IsPGroup.iff_card.2 ⟨_, hPcard⟩
  obtain ⟨Q₀, hQ₀⟩ := hP.exists_le_sylow
  have hQcard : Nat.card (Q₀ : Subgroup G) = p ^ (Nat.card G).factorization p :=
    Sylow.card_eq_multiplicity Q₀
  have hPeq : P = (Q₀ : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge hQ₀ (by rw [hQcard, hPcard])
  obtain ⟨R, hER⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G R Q₀
  refine ⟨g, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have hmem : (MulAut.conj g) y ∈ (Q₀ : Set G) := by
    rw [← hg, Sylow.coe_smul]
    exact Set.mem_smul_set.2 ⟨y, hER hy, rfl⟩
  have hmemP : (MulAut.conj g) y ∈ P := by
    rw [hPeq]
    exact hmem
  exact hPle hmemP


theorem threeSubgroup_conj_into_F4 {k K : Type} [Field k] [Finite k] [Field K] [Finite K] [Algebra k K]
    (σ : K ≃+* K) (hσ : ∀ c : K, σ c = c ^ Nat.card k) (hK : Nat.card K = (Nat.card k) ^ 2)
    (hfix : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c)
    (hq : Nat.card k % 3 = 1) (hq2 : 2 ≤ Nat.card k)
    (E₀ : Subgroup (twistedE6RootGroup K σ)) (hE₀ : ∀ x ∈ E₀, x ^ 3 = 1) :
    ∃ g : twistedE6RootGroup K σ,
      E₀.map (MulAut.conj g).toMonoidHom ≤
        ((phiG σ hfix).comp (e6FixedF4EquivAll k).symm.toMonoidHom).range := by
  haveI : Fintype k := Fintype.ofFinite k
  obtain ⟨n, hn, hkcard⟩ := FiniteField.card k (ringChar k)
  have hℓ : (ringChar k).Prime := hn
  have hf : 1 ≤ (n : ℕ) := n.pos
  have hkq : Nat.card k = ringChar k ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hkcard
  have hGcard : Nat.card (twistedE6RootGroup K σ) = ordTwistedE6 (Nat.card k) := by
    rw [card_twistedE6RootGroup_eq hℓ hf σ (by rw [hkq] at hK; exact hK)
      (by intro c; rw [hσ c, hkq]), ← hkq]
  have hFcard : Nat.card (adjointGroup .F4 k) = ordF4 (Nat.card k) := card_adjointGroup_F4_eq k
  have hord : (Nat.card (twistedE6RootGroup K σ)).factorization 3 =
      (Nat.card (adjointGroup .F4 k)).factorization 3 := by
    rw [hGcard, hFcard]
    exact factorization_three_ordTwistedE6 hq hq2
  have hφ : Function.Injective ((phiG σ hfix).comp (e6FixedF4EquivAll k).symm.toMonoidHom) :=
    (phiG_injective σ hfix).comp (MulEquiv.injective _)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE3 : IsPGroup 3 E₀ := fun x => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (by simpa using hE₀ x.1 x.2)⟩
  exact exists_conj_le_range_of_factorization _ hφ hord E₀ hE3

end CFSG.LieType.SeitzGeneration.ExcHighThree
