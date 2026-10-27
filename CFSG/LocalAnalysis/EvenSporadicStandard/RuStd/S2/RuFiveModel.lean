module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuFiveGroup
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.Transport

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2

open Subgroup CFSG.EvenSporadicStandard.RuStd

section Conj

variable {G : Type} [Group G]

theorem orderOf_conj' (c a : G) : orderOf (c * a * c⁻¹) = orderOf a := by
  simpa using (MulAut.conj c).orderOf_eq a

theorem centralizer_conj (c a : G) :
    centralizer ({c * a * c⁻¹} : Set G) =
      (centralizer ({a} : Set G)).map (MulAut.conj c).toMonoidHom := by
  simpa using centralizer_singleton_map (MulAut.conj c) a

theorem centralizer_eq_map {f x : G} {c : G} (hz : zpowers (c * x * c⁻¹) = zpowers f) :
    centralizer ({f} : Set G) = (centralizer ({x} : Set G)).map (MulAut.conj c).toMonoidHom := by
  rw [← centralizer_eq_of_zpowers_eq hz, centralizer_conj]

theorem card_centralizer_eq {f x : G} {c : G} (hz : zpowers (c * x * c⁻¹) = zpowers f) :
    Nat.card (centralizer ({f} : Set G)) = Nat.card (centralizer ({x} : Set G)) := by
  rw [centralizer_eq_map hz, Subgroup.card_map_of_injective (MulAut.conj c).injective]

theorem hasKlein_centralizer_iff {f x : G} {c : G} (hz : zpowers (c * x * c⁻¹) = zpowers f) :
    HasKlein ((centralizer ({f} : Set G) : Subgroup G) : Set G) ↔
      HasKlein ((centralizer ({x} : Set G) : Subgroup G) : Set G) := by
  rw [centralizer_eq_map hz, Subgroup.coe_map]
  exact hasKlein_image_iff (MulAut.conj c) _

end Conj

structure FiveData (G : Type) [Group G] where
  Q : Sylow 5 G
  Q_exp : ∀ q ∈ (Q : Subgroup G), q ^ 5 = 1
  x₀ : G
  x₁ : G
  x₀_mem : x₀ ∈ (Q : Subgroup G)
  x₁_mem : x₁ ∈ (Q : Subgroup G)
  x₀_order : orderOf x₀ = 5
  x₁_order : orderOf x₁ = 5
  cover : ∀ q ∈ (Q : Subgroup G), q ≠ 1 →
    (∃ (d : G) (k : ℤ), d * x₀ * d⁻¹ = q ^ k) ∨ (∃ (d : G) (k : ℤ), d * x₁ * d⁻¹ = q ^ k)
  card_C₀ : Nat.card (centralizer ({x₀} : Set G)) = 1000
  A : Subgroup G
  A_le : A ≤ centralizer ({x₀} : Set G)
  A_normal : ∀ c ∈ centralizer ({x₀} : Set G), ∀ a ∈ A, c * a * c⁻¹ ∈ A
  card_A : Nat.card A = 125
  qi : G
  qj : G
  qi_mem : qi ∈ centralizer ({x₀} : Set G)
  qj_mem : qj ∈ centralizer ({x₀} : Set G)
  qi_pow : qi ^ 4 = 1
  qi_sq : qi ^ 2 ≠ 1
  qj_sq : qj ^ 2 = qi ^ 2
  qj_conj : qj * qi * qj⁻¹ = qi⁻¹
  card_C₁ : Nat.card (centralizer ({x₁} : Set G)) = 300
  D : Subgroup G
  D_le : D ≤ centralizer ({x₁} : Set G)
  D_simple : IsSimpleGroup D
  card_D : Nat.card D = 60
  y : G
  y_mem : y ∈ (Q : Subgroup G)
  y_comm : y * x₁ = x₁ * y
  y_not_mem : y ∉ zpowers x₁
  y_unique : ∀ q ∈ (Q : Subgroup G), q ≠ 1 → q * x₁ = x₁ * q →
    Nat.card (centralizer ({q} : Set G)) = 1000 → q ∈ zpowers y

namespace FiveData

variable {G : Type} [Group G] [Finite G] (d : FiveData G)

include d

theorem exists_conj {f : G} (hf : orderOf f = 5) :
    (∃ c : G, zpowers (c * d.x₀ * c⁻¹) = zpowers f) ∨
      (∃ c : G, zpowers (c * d.x₁ * c⁻¹) = zpowers f) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hP : IsPGroup 5 (zpowers f) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hf]; norm_num)
  obtain ⟨c, hc⟩ := exists_conj_mem_sylow d.Q hP
  have hq : c * f * c⁻¹ ∈ (d.Q : Subgroup G) := hc f (mem_zpowers f)
  have hne : c * f * c⁻¹ ≠ 1 := by
    intro h
    have : orderOf (c * f * c⁻¹) = 1 := by rw [h, orderOf_one]
    rw [orderOf_conj', hf] at this
    omega
  have key : ∀ (x : G) (e : G) (k : ℤ), orderOf x = 5 → e * x * e⁻¹ = (c * f * c⁻¹) ^ k →
      zpowers (c⁻¹ * e * x * (c⁻¹ * e)⁻¹) = zpowers f := by
    intro x e k hx hk
    have hfk : c⁻¹ * e * x * (c⁻¹ * e)⁻¹ = f ^ k := by
      calc c⁻¹ * e * x * (c⁻¹ * e)⁻¹ = c⁻¹ * (e * x * e⁻¹) * c := by group
        _ = c⁻¹ * (c * f * c⁻¹) ^ k * c := by rw [hk]
        _ = f ^ k := by rw [conj_zpow]; group
    rw [hfk]
    have hord : orderOf (f ^ k) = 5 := by rw [← hfk, orderOf_conj', hx]
    apply Subgroup.eq_of_le_of_card_ge
    · exact zpowers_le.2 (zpow_mem (mem_zpowers f) k)
    · rw [Nat.card_zpowers, Nat.card_zpowers, hord, hf]
  rcases d.cover _ hq hne with ⟨e, k, hk⟩ | ⟨e, k, hk⟩
  · exact Or.inl ⟨c⁻¹ * e, key _ e k d.x₀_order hk⟩
  · exact Or.inr ⟨c⁻¹ * e, key _ e k d.x₁_order hk⟩

theorem exists_hom₀ : ∃ ρ : ↥(centralizer ({d.x₀} : Set G)) →* QuaternionGroup 2,
    IsPGroup 5 ρ.ker := by
  set C := centralizer ({d.x₀} : Set G) with hC
  let i : C := ⟨d.qi, d.qi_mem⟩
  let j : C := ⟨d.qj, d.qj_mem⟩
  have hi4 : i ^ 4 = 1 := Subtype.ext (by simpa using d.qi_pow)
  have hi2 : i ^ 2 ≠ 1 := fun h => d.qi_sq (by simpa using congrArg Subtype.val h)
  have hj : j ^ 2 = i ^ 2 := Subtype.ext (by simpa using d.qj_sq)
  have hji : j * i * j⁻¹ = i⁻¹ := Subtype.ext (by simpa using d.qj_conj)
  let ψ := quatHom (n := 2) i j (by simpa using hi4) hj hji
  have hψ : Function.Injective ψ := quatHom_injective hi4 hi2 hj hji
  let N : Subgroup C := d.A.subgroupOf C
  have hN : N.Normal := ⟨fun n hn g => by
    have := d.A_normal g.1 g.2 n.1 hn
    exact this⟩
  have hcardN : Nat.card N = 125 := by
    rw [← d.card_A]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe d.A_le).toEquiv
  obtain ⟨ρ, hρ⟩ := exists_hom_quat N d.card_C₀ hcardN ψ hψ
  refine ⟨ρ, ?_⟩
  rw [hρ]
  exact IsPGroup.of_card (n := 3) (by rw [hcardN]; norm_num)

end FiveData

end CFSG.EvenSporadicStandard.RuStd.S2
