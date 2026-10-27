module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotOmegaRowUniqueReduce

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.UnitaryPilot (modelToG mem_modelToG)
open CFSG.Quasithin (perfectCore)

section Defs

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

@[expose] def CosetInnConjInput {X : Type*} [Group X] (θ : MulAut X) : Prop :=
  ∀ y : X, (MulAut.conj y * θ) * (MulAut.conj y * θ) = 1 →
    (∃ β : MulAut X, β * θ = (MulAut.conj y * θ) * β) →
      ∃ z : X, MulAut.conj y * θ = MulAut.conj z * θ * (MulAut.conj z)⁻¹

end Defs

section Generic

variable {G : Type} [Group G]

theorem normalizerMonoidHom_eq_conj_of_mem {H : Subgroup G} {y : G} (hy : y ∈ H)
    (hyN : y ∈ normalizer (H : Set G)) :
    H.normalizerMonoidHom ⟨y, hyN⟩ = MulAut.conj ⟨y, hy⟩ := by
  ext z
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply]
  rfl

theorem normalizerMonoidHom_mul' {H : Subgroup G} {a b : G} (ha : a ∈ normalizer (H : Set G))
    (hb : b ∈ normalizer (H : Set G)) (hab : a * b ∈ normalizer (H : Set G)) :
    H.normalizerMonoidHom ⟨a * b, hab⟩ =
      H.normalizerMonoidHom ⟨a, ha⟩ * H.normalizerMonoidHom ⟨b, hb⟩ := by
  rw [← map_mul]
  rfl

theorem mulAut_mul_conj_eq_of_apply_eq {X : Type*} [Group X] {η : MulAut X} {x : X}
    (hηx : η x = x) : η * MulAut.conj x = MulAut.conj x * η := by
  ext y
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hηx]

theorem exists_conj_eq_of_normalizerMonoidHom_eq [Finite G] {H : Subgroup G}
    (hodd : Odd (Nat.card (centralizer (H : Set G)))) {u v : G} (hu : u * u = 1) (hv : v * v = 1)
    (huN : u ∈ normalizer (H : Set G)) (hvN : v ∈ normalizer (H : Set G))
    (h : H.normalizerMonoidHom ⟨u, huN⟩ = H.normalizerMonoidHom ⟨v, hvN⟩) :
    ∃ c ∈ centralizer (H : Set G), v = c * u * c⁻¹ := by
  set w := u⁻¹ * v with hw
  have hwC : w ∈ centralizer (H : Set G) := by
    rw [mem_centralizer_iff]
    intro y hy
    have h1 := congrArg (fun φ : MulAut H => ((φ ⟨y, hy⟩ : H) : G)) h
    simp only [Subgroup.normalizerMonoidHom_apply_apply_coe] at h1
    have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
    calc y * w = u⁻¹ * (u * y * u⁻¹) * v := by rw [hw]; group
      _ = u⁻¹ * (v * y * v⁻¹) * v := by rw [h1]
      _ = w * y := by rw [hw]; group
  have hwo : Odd (orderOf w) := by
    have h1 : orderOf (⟨w, hwC⟩ : centralizer (H : Set G)) ∣ Nat.card (centralizer (H : Set G)) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hodd h1
  have huw : u * w = v := by rw [hw, mul_inv_cancel_left]
  obtain ⟨k, hk⟩ := exists_conj_eq_of_mul_self_of_odd hu hwo (by rw [huw]; exact hv)
  refine ⟨w ^ k, pow_mem hwC k, ?_⟩
  rw [← huw, hk]

theorem card_le_card_fixedSubgroup_of_mem_normalizer [Finite G] {G₀ L : Subgroup G} {t g : G}
    (hLG : L ≤ G₀) (hLt : L ≤ centralizer ({t} : Set G)) (hgN : g ∈ normalizer (G₀ : Set G))
    (hg : g⁻¹ * t * g ∈ normalizer (G₀ : Set G)) :
    Nat.card L ≤ Nat.card (fixedSubgroup (G₀.normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩)) := by
  have hmem : ∀ l ∈ L, g⁻¹ * l * g ∈ G₀ := by
    intro l hl
    have := (mem_normalizer_iff.1 (inv_mem hgN) l).1 (hLG hl)
    simpa [mul_assoc] using this
  let φ : L → fixedSubgroup (G₀.normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩) := fun l =>
    ⟨⟨g⁻¹ * l * g, hmem l l.2⟩, by
      show G₀.normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩ ⟨g⁻¹ * l * g, hmem l l.2⟩ =
        ⟨g⁻¹ * l * g, hmem l l.2⟩
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      have hlt : t * (l : G) = l * t := (mem_centralizer_singleton_iff.1 (hLt l.2)).symm
      change g⁻¹ * t * g * (g⁻¹ * l * g) * (g⁻¹ * t * g)⁻¹ = g⁻¹ * l * g
      calc g⁻¹ * t * g * (g⁻¹ * l * g) * (g⁻¹ * t * g)⁻¹ = g⁻¹ * (t * l) * t⁻¹ * g := by group
        _ = g⁻¹ * l * g := by rw [hlt]; group⟩
  refine Nat.card_le_card_of_injective φ fun a b hab => ?_
  have h1 := congrArg
    (fun y : fixedSubgroup (G₀.normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩) => ((y : G₀) : G)) hab
  change g⁻¹ * (a : G) * g = g⁻¹ * b * g at h1
  exact Subtype.ext (by simpa using h1)

end Generic

theorem odd_card_leviTorusSp {K : Type} [Field K] [Finite K] {f : ℕ} (hKc : Nat.card K = 2 ^ f)
    (hf : 1 ≤ f) {n : ℕ} (J : Finset (Fin n)) : Odd (Nat.card (leviTorusSp K J)) := by
  have hU : Odd (Nat.card Kˣ) := by
    rw [Nat.card_units, hKc]
    exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one
  have hpi : Odd (Nat.card (Fin n → Kˣ)) := by
    rw [Nat.card_fun]
    exact hU.pow
  have h1 : Nat.card (leviTorusSp K J) ∣ Nat.card (leviTorusParam K J) :=
    Subgroup.card_map_dvd (leviTorusParam K J) (diagSp K n)
  have h2 : Nat.card (leviTorusParam K J) ∣ Nat.card (Fin n → Kˣ) :=
    Subgroup.card_subgroup_dvd_card _
  exact Odd.of_dvd_nat hpi (h1.trans h2)

end CFSG.SeitzReduction.SymplecticPilot
