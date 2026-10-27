module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.TNormalizes
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.NotComm
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.YSup

public section

namespace CFSG.EvenSporadicStandard.M12Std.PropA

open Subgroup CFSG.EvenSporadicStandard.Solomon78

theorem eq_of_isCompIn_alt5 {G : Type} [Group G] [Finite G] {x t : G} {J : Subgroup G}
    (hx2 : x * x = 1) (hx1 : x ≠ 1) (ht2 : t * t = 1) (hxt : x * t = t * x)
    (hJc : IsCompIn J (centralizer ({x} : Set G)))
    (hJA : Nonempty (J ≃* alternatingGroup (Fin 5))) (hJt : ∀ j ∈ J, t * j = j * t)
    (hG0 : ∀ R : Subgroup G, R ≤ centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G) →
      ⁅R, R⁆ = R → R ≤ J)
    (hY : Nat.card ↥(centralizer (J : Set G) ⊓
      (centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G))) = 8)
    (hG3 : ∃ c ∈ centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G),
      ∃ y ∈ centralizer (J : Set G) ⊓ (centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G)),
        c * y * c⁻¹ * y⁻¹ = x)
    {J₁ : Subgroup G} (hJ₁c : IsCompIn J₁ (centralizer ({x} : Set G)))
    (hJ₁A : Nonempty (J₁ ≃* alternatingGroup (Fin 5))) : J₁ = J := by
  by_contra hne
  have htJ₁ := map_conj_eq_of_alt5_comp hxt ht2 hJc hJ₁c hne hJA hJ₁A hJt hG0
  obtain ⟨c, hcC, y, hyY, hcy⟩ := hG3
  have hcX : c ∈ centralizer ({x} : Set G) := hcC.1
  have hc : c * x = x * c := Subgroup.mem_centralizer_singleton_iff.1 hcX
  have hxJ : ∀ j ∈ J₁, x * j = j * x := by
    intro j hj
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hJ₁c.le hj)).symm
  have hZ : ∀ j ∈ J₁, (∀ j' ∈ J₁, j * j' = j' * j) → j = 1 := by
    intro j hj hcen
    exact alt5_subgroup_center hJ₁A.some hj hcen
  have hcomm : J₁.map (MulAut.conj c).toMonoidHom ≠ J₁ →
      ∀ a ∈ J₁.map (MulAut.conj c).toMonoidHom, ∀ b ∈ J₁, a * b = b * a := by
    intro hne'
    exact IsCompIn.commute_of_ne (hJ₁c.map_conj hcX) hJ₁c hne'
  have hy : y ∈ zpowers x ⊔ J₁ :=
    Y_le_sup_of_alt5_comp hx2 hx1 ht2 hxt hJc hJ₁c hne hJ₁A htJ₁ hY hyY
  exact false_of_commutator_eq hx1 hc hxJ hZ hcomm hy hcy

theorem map_conj_eq_of_isCompIn_alt5 {G : Type} [Group G] [Finite G] {x t : G} {J : Subgroup G}
    (hx2 : x * x = 1) (hx1 : x ≠ 1) (ht2 : t * t = 1) (hxt : x * t = t * x)
    (hJc : IsCompIn J (centralizer ({x} : Set G)))
    (hJA : Nonempty (J ≃* alternatingGroup (Fin 5))) (hJt : ∀ j ∈ J, t * j = j * t)
    (hG0 : ∀ R : Subgroup G, R ≤ centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G) →
      ⁅R, R⁆ = R → R ≤ J)
    (hY : Nat.card ↥(centralizer (J : Set G) ⊓
      (centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G))) = 8)
    (hG3 : ∃ c ∈ centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G),
      ∃ y ∈ centralizer (J : Set G) ⊓ (centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G)),
        c * y * c⁻¹ * y⁻¹ = x)
    {c : G} (hc : c ∈ centralizer ({x} : Set G)) :
    J.map (MulAut.conj c).toMonoidHom = J := by
  let J' : Subgroup G := J.map (MulAut.conj c).toMonoidHom
  have hJ'c : IsCompIn J' (centralizer ({x} : Set G)) := hJc.map_conj hc
  have hJ'A : Nonempty (J' ≃* alternatingGroup (Fin 5)) := by
    obtain ⟨e⟩ := hJA
    exact ⟨(J.equivMapOfInjective (MulAut.conj c).toMonoidHom
      (MulAut.conj c).injective).symm.trans e⟩
  have h := eq_of_isCompIn_alt5 hx2 hx1 ht2 hxt hJc hJA hJt hG0 hY hG3 hJ'c hJ'A
  simpa [J'] using h

end CFSG.EvenSporadicStandard.M12Std.PropA
