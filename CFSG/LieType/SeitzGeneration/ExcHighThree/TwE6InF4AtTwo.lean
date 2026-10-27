module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4Two
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6TwoBase

public section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.HardMathSupport.Lang.AnisoE6 CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


@[expose] def TwHighPlaneContainedAtTwo : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (k : Type) [Field k] [Finite k] [Algebra k K]
    (hfix : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c),
    Nat.card K = 2 ^ 2 → (∀ c : K, σ c = c ^ 2) → Nat.card k = 2 →
    ∀ E₀ : Subgroup (twistedE6RootGroup K σ), (∀ x ∈ E₀, x ^ 3 = 1) → Nat.card E₀ = 3 ^ 2 →
      ¬ NormalizesRIn (ringChar K) E₀ →
      ∃ g : twistedE6RootGroup K σ,
        E₀.map (MulAut.conj g).toMonoidHom ≤
          ((phiG σ hfix).comp (e6FixedF4EquivAll k).symm.toMonoidHom).range

theorem twE6HighInF4_at_two_of (hCont : TwHighPlaneContainedAtTwo) (hC : TwE6Two.TwCloseAtTwo) :
    TwE6HighInF4_at_two := by
  intro K _ _ σ hK hσ E₀ hexp hcard hn
  obtain ⟨k, hkF, hkfin, hkalg, hkq, hkchar, hfix⟩ := exists_fixed_subfield 2 K σ hK hσ le_rfl
  obtain ⟨g₀, hg₀⟩ := hCont K σ k hfix hK hσ hkq E₀ hexp hcard hn
  set ι : adjointGroup .F4 k →* twistedE6RootGroup K σ :=
    (phiG σ hfix).comp (e6FixedF4EquivAll k).symm.toMonoidHom with hιdef
  have hι : Function.Injective ι :=
    (phiG_injective σ hfix).comp (e6FixedF4EquivAll k).symm.injective
  set E₃ : Subgroup (adjointGroup .F4 k) := (E₀.map (MulAut.conj g₀).toMonoidHom).comap ι with hE₃def
  have hE₃ : E₃.map ι = E₀.map (MulAut.conj g₀).toMonoidHom := Subgroup.map_comap_eq_self hg₀
  have hexp₃ : ∀ x ∈ E₃, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hx)
    apply hι
    rw [map_pow, map_one, ← hyx, ← map_pow, hexp y hy, map_one]
  have hcardE₃ : Nat.card E₃ = 3 ^ 2 := by
    have h1 : Nat.card (E₃.map ι) = Nat.card E₃ := Subgroup.card_map_of_injective hι
    have h2 : Nat.card (E₀.map (MulAut.conj g₀).toMonoidHom) = Nat.card E₀ :=
      Subgroup.card_map_of_injective (MulAut.conj g₀).injective
    rw [← h1, hE₃, h2, hcard]
  obtain ⟨e, he, he1, hcl⟩ := hC K σ k hfix hK hσ hkq E₃ hexp₃ hcardE₃
  exact ⟨k, inferInstance, inferInstance, g₀, ι, E₃, hkq, hkchar, hι, hE₃, e, he, he1, hcl⟩

end CFSG.LieType.SeitzGeneration.ExcHighThree
