module

public import CFSG.CGT.PushingUpLit.T2K.Inputs
public import CFSG.CGT.PushingUpLit.T2K.Transvection
public import CFSG.RankThree.PartOne.S12.Sec15Final

public section

namespace CFSG.CGT.PushingUpLit.T2K

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.Assembly
open scoped commutatorElement

theorem mem_map_conj_iff {G : Type} [Group G] (g : G) (X : Subgroup G) (x : G) :
    x ∈ X.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ X := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro hx
    exact ⟨g⁻¹ * x * g, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem normalizer_zpowers_eq_centralizer_of_sq {G : Type} [Group G] {z : G} (hz : z ^ 2 = 1)
    (hz1 : z ≠ 1) :
    Subgroup.normalizer (Subgroup.zpowers z : Set G) = Subgroup.centralizer ({z} : Set G) := by
  ext c
  constructor
  · intro hc
    have h1 : c * z * c⁻¹ ∈ Subgroup.zpowers z :=
      (Subgroup.mem_normalizer_iff.1 hc z).1 (Subgroup.mem_zpowers z)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h1
    rcases zpow_eq_one_or_self hz k with h2 | h2
    · exfalso
      apply hz1
      have : c * z * c⁻¹ = 1 := hk.symm.trans h2
      have e : z = c⁻¹ * (c * z * c⁻¹) * c := by group
      rw [e, this]
      group
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have : c * z * c⁻¹ = z := hk.symm.trans h2
      calc c * z = (c * z * c⁻¹) * c := by group
        _ = z * c := by rw [this]
  · intro hc
    have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.1 hc
    have hcomm : ∀ k : ℤ, c * z ^ k = z ^ k * c := fun k =>
      ((Commute.zpow_right (show Commute c z from hcz) k)).eq
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
      rw [hcomm k]
      group
    · intro hy
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hy
      refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
      have : c * y = c * z ^ k := by
        rw [hcomm k, hk]
        group
      exact (mul_left_cancel this).symm

theorem isPLocal_centralizer_of_sq {G : Type} [Group G] {z : G} (hz : z ^ 2 = 1) (hz1 : z ≠ 1) :
    IsPLocal 2 (Subgroup.centralizer ({z} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨Subgroup.zpowers z, ?_, ?_, (normalizer_zpowers_eq_centralizer_of_sq hz hz1).symm⟩
  · intro h0
    apply hz1
    have : z ∈ Subgroup.zpowers z := Subgroup.mem_zpowers z
    rw [h0] at this
    simpa using this
  · refine IsPGroup.of_card (n := 1) ?_
    have : orderOf z = 2 := orderOf_eq_prime hz hz1
    rw [Nat.card_zpowers, this]
    simp

namespace T2Hyp

variable {G : Type} [Group G] [Finite G] {L M : Subgroup G} {n : ℕ}
variable (h : T2Hyp G L M n)
include h

theorem le_normalizer_centralizer (hE1 : FooteNonsolvableSimple) :
    M ≤ Subgroup.normalizer (Subgroup.centralizer (L : Set G) : Set G) := fun _ hm =>
  mem_normalizer_centralizer (h.normal hE1 hm)

theorem odd_inf_conj {g : G} (hg : g ∉ M) :
    Odd (Nat.card ↥(Subgroup.centralizer (L : Set G) ⊓
      (Subgroup.centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom)) := by
  by_contra hodd
  have hev := Nat.not_odd_iff_even.1 hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu2⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.1 hev)
  have hord : orderOf (u : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hu2
  have hu1 : (u : G) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hord
    omega
  have hsq : (u : G) ^ 2 = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
  have hcomL : ∀ l ∈ L, l * (u : G) = (u : G) * l := fun l hl =>
    Subgroup.mem_centralizer_iff.1 u.2.1 l hl
  have hconj : g⁻¹ * (u : G) * g ∈ Subgroup.centralizer (L : Set G) :=
    (mem_map_conj_iff g _ _).1 u.2.2
  have hcomL' : ∀ l ∈ L, (g * l * g⁻¹) * (u : G) = (u : G) * (g * l * g⁻¹) := by
    intro l hl
    have h1 := Subgroup.mem_centralizer_iff.1 hconj l hl
    calc (g * l * g⁻¹) * (u : G) = g * (l * (g⁻¹ * (u : G) * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * (u : G) * g) * l) * g⁻¹ := by rw [h1]
      _ = (u : G) * (g * l * g⁻¹) := by group
  have hloc := isPLocal_centralizer_of_sq hsq hu1
  obtain ⟨N, hCN, hNmax⟩ := Sec15Final.exists_isMaximalTwoLocal_ge hloc
  have hLC : L ≤ Subgroup.centralizer ({(u : G)} : Set G) := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.2 (hcomL l hl)
  have hNM : N = M := by
    have : N ∈ maximalTwoLocalsContaining (L : Set G) := ⟨hNmax, fun x hx => hCN (hLC hx)⟩
    rw [h.unique] at this
    exact this
  have hN' : IsMaximalTwoLocal (M.map (MulAut.conj g⁻¹).toMonoidHom) :=
    RankThree.PartTwo.Late.isMaximalTwoLocal_map h.maxLocal (MulAut.conj g⁻¹)
  have hLN' : L ≤ M.map (MulAut.conj g⁻¹).toMonoidHom := by
    intro l hl
    have hmem : g * l * g⁻¹ ∈ M := by
      rw [← hNM]
      refine hCN ?_
      exact Subgroup.mem_centralizer_singleton_iff.2 (hcomL' l hl)
    exact ⟨g * l * g⁻¹, hmem, by simp [mul_assoc]⟩
  have hN'M : M.map (MulAut.conj g⁻¹).toMonoidHom = M := by
    have : M.map (MulAut.conj g⁻¹).toMonoidHom ∈ maximalTwoLocalsContaining (L : Set G) :=
      ⟨hN', hLN'⟩
    rw [h.unique] at this
    exact this
  have hginv := RankThree.PartTwo.Late.mem_of_map_conj_eq_of_isMaximalTwoLocal h.maxLocal hN'M
  have := M.inv_mem hginv
  rw [inv_inv] at this
  exact hg this

theorem normalizer_centralizer_eq (hE1 : FooteNonsolvableSimple)
    (heven : Even (Nat.card ↥(Subgroup.centralizer (L : Set G)))) :
    Subgroup.normalizer (Subgroup.centralizer (L : Set G) : Set G) = M := by
  refine le_antisymm (fun g hg => ?_) (h.le_normalizer_centralizer hE1)
  by_contra hgM
  have hodd := h.odd_inf_conj hgM
  have heq : (Subgroup.centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer (L : Set G) := by
    ext x
    rw [mem_map_conj_iff]
    have := Subgroup.mem_normalizer_iff.1 hg (g⁻¹ * x * g)
    simpa [mul_assoc] using this
  rw [heq, inf_idem] at hodd
  exact (Nat.not_even_iff_odd.2 hodd) heven

theorem isTightlyEmbedded (hE1 : FooteNonsolvableSimple)
    (heven : Even (Nat.card ↥(Subgroup.centralizer (L : Set G)))) :
    IsTightlyEmbedded (Subgroup.centralizer (L : Set G)) :=
  ⟨heven, fun _ hg => h.odd_inf_conj fun hgM => hg (h.le_normalizer_centralizer hE1 hgM)⟩

end T2Hyp

end CFSG.CGT.PushingUpLit.T2K
