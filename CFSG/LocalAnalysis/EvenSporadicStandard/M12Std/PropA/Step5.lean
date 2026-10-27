module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.Defs
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.EvenSporadicStandard.M12Std.PropA

open Subgroup

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G}

theorem mem_centralizer_jOf_of_conj {t x : G} (hJ : Nat.card ↥(jOf L x) = 60)
    (hCx : Nat.card ↥(centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G)) = 960)
    (hG0 : ∀ R : Subgroup G, R ≤ centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G) →
      ⁅R, R⁆ = R → R ≤ jOf L x)
    (hG2 : ∀ x' ∈ centralizer ({t} : Set G), orderOf x' = 2 →
      Nat.card ↥(centralizer ({x'} : Set G) ⊓ centralizer ({t} : Set G)) ∣ 960 →
      ∃ R : Subgroup G, R ≤ centralizer ({x'} : Set G) ⊓ centralizer ({t} : Set G) ∧
        ⁅R, R⁆ = R ∧ 60 ≤ Nat.card ↥R)
    (hx2 : orderOf x = 2) (hC : centralizer ({x} : Set G) ≤ centralizer ({t} : Set G)) (g : G)
    (hgx : g * t * g⁻¹ ∈ centralizer ({x} : Set G)) :
    g * t * g⁻¹ ∈ centralizer ((jOf L x) : Set G) := by
  set φ : G →* G := (MulAut.conj g).toMonoidHom with hφ
  have hφi : Function.Injective φ := (MulAut.conj g).injective
  have hφa : ∀ a, φ a = g * a * g⁻¹ := fun a => rfl
  obtain ⟨x', hx'⟩ : ∃ x' : G, x' = g⁻¹ * x * g := ⟨_, rfl⟩
  have hxx : φ x' = x := by rw [hφa, hx']; group
  have hx'2 : orderOf x' = 2 := by
    rw [← orderOf_injective φ hφi x', hxx, hx2]
  have hwx : (g * t * g⁻¹) * x = x * (g * t * g⁻¹) :=
    (mem_centralizer_singleton_iff.1 hgx)
  have hx't : x' ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    apply hφi
    rw [map_mul, map_mul, hxx, hφa t]
    exact hwx.symm
  set K := centralizer ({x'} : Set G) ⊓ centralizer ({t} : Set G) with hK
  have hmapK : K.map φ ≤ centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G) := by
    rintro _ ⟨k, ⟨hk1, -⟩, rfl⟩
    have : φ k ∈ centralizer ({x} : Set G) := by
      rw [mem_centralizer_singleton_iff, ← hxx, ← map_mul, ← map_mul,
        (mem_centralizer_singleton_iff.1 hk1)]
    exact ⟨this, hC this⟩
  have hdvd : Nat.card K ∣ 960 := by
    rw [← hCx, ← card_map_of_injective hφi]
    exact card_dvd_of_le hmapK
  obtain ⟨R, hRK, hRp, hR60⟩ := hG2 x' hx't hx'2 hdvd
  have hR'p : ⁅R.map φ, R.map φ⁆ = R.map φ := by rw [← map_commutator, hRp]
  have hR'J : R.map φ ≤ jOf L x := hG0 (R.map φ) ((map_mono hRK).trans hmapK) hR'p
  have hR'card : Nat.card ↥(R.map φ) = Nat.card ↥R := card_map_of_injective hφi
  have hJR : R.map φ = jOf L x :=
    eq_of_le_of_card_ge hR'J (by rw [hR'card, hJ]; exact hR60)
  rw [mem_centralizer_iff]
  intro j hj
  rw [SetLike.mem_coe, ← hJR] at hj
  obtain ⟨r, hr, rfl⟩ := hj
  have hrt : r * t = t * r := (mem_centralizer_singleton_iff.1 (hRK hr).2)
  rw [← hφa t, ← map_mul, ← map_mul, hrt]

end CFSG.EvenSporadicStandard.M12Std.PropA
