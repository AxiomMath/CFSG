module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.CoverFixInduced

public section

namespace CFSG.EvenSporadicStandard.Induction.CoverFix

open Subgroup

variable {K G : Type*} [Group K] [Group G]

theorem card_comap_of_surjective (π : K →* G) (hπ : Function.Surjective π) (V : Subgroup G) :
    Nat.card (V.comap π) = Nat.card V * Nat.card π.ker := by
  let ψ : ↥(V.comap π) →* ↥V :=
    { toFun := fun d => ⟨π d, d.2⟩
      map_one' := Subtype.ext (map_one π)
      map_mul' := fun a b => Subtype.ext (map_mul π (a : K) (b : K)) }
  have hker : ψ.ker = π.ker.subgroupOf (V.comap π) := by
    ext d
    simp [ψ, MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subtype.ext_iff]
  have hrange : ψ.range = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨v, hv⟩ -
    obtain ⟨x, rfl⟩ := hπ v
    exact ⟨⟨x, hv⟩, rfl⟩
  have hle : π.ker ≤ V.comap π := fun z hz => by
    show π z ∈ V
    rw [MonoidHom.mem_ker.1 hz]
    exact V.one_mem
  have h1 := Subgroup.card_mul_index ψ.ker
  rw [Subgroup.index_ker, hrange, hker] at h1
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
    Nat.card_congr (Subgroup.topEquiv).toEquiv] at h1
  rw [mul_comm]
  exact h1.symm

theorem card_dvd_card_fixed_inf [Finite K] (π : K →* G) (hπ : Function.Surjective π)
    (hZ : π.ker ≤ center K) {α : MulAut K} {β : MulAut G} (h : ∀ x, π (α x) = β (π x))
    (B : Subgroup G) (hB : ∀ b ∈ B, β b = b) :
    Nat.card B ∣ Nat.card ↥(fixed α ⊓ B.comap π) := by
  let C : Subgroup K := B.comap π
  have hC : ∀ x ∈ C, π (α x) = π x := fun x hx => by
    rw [h x]
    exact hB _ hx
  let δ := discrHom π hZ α C hC
  have hmap : δ.ker.map C.subtype = fixed α ⊓ C := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.coe_subtype, Subgroup.mem_inf, mem_fixed]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(mem_ker_discrHom π hZ α C hC y).1 hy, y.2⟩
    · rintro ⟨hx, hxC⟩
      exact ⟨⟨x, hxC⟩, (mem_ker_discrHom π hZ α C hC ⟨x, hxC⟩).2 hx, rfl⟩
  have hker : Nat.card ↥(fixed α ⊓ C) = Nat.card δ.ker := by
    rw [← hmap, Subgroup.card_map_of_injective C.subtype_injective]
  have h1 := Subgroup.card_ker_mul_card_range δ
  have h2 := card_comap_of_surjective π hπ B
  have h3 : Nat.card δ.range ∣ Nat.card π.ker := Subgroup.card_subgroup_dvd_card _
  obtain ⟨s, hs⟩ := h3
  have hr : 0 < Nat.card δ.range := Nat.card_pos
  rw [hker]
  refine ⟨s, ?_⟩
  have h4 : Nat.card B * (Nat.card δ.range * s) = Nat.card δ.ker * Nat.card δ.range := by
    rw [← hs, ← h2]
    exact h1.symm
  have h5 : (Nat.card B * s) * Nat.card δ.range = Nat.card δ.ker * Nat.card δ.range := by
    rw [← h4]
    ring
  exact (Nat.eq_of_mul_eq_mul_right hr h5).symm

theorem exists_subgroup_card_two_pow [Finite K] (π : K →* G) (hπ : Function.Surjective π)
    (hZ : π.ker ≤ center K) {α : MulAut K} {β : MulAut G} (h : ∀ x, π (α x) = β (π x))
    (B : Subgroup G) (hB : ∀ b ∈ B, β b = b) {n : ℕ} (hBn : Nat.card B = 2 ^ n) :
    ∃ P : Subgroup K, P ≤ fixed α ⊓ B.comap π ∧ Nat.card P = 2 ^ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd := card_dvd_card_fixed_inf π hπ hZ h B hB
  rw [hBn] at hd
  obtain ⟨P', hP'⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥(fixed α ⊓ B.comap π)) 2 hd
  refine ⟨P'.map (fixed α ⊓ B.comap π).subtype, Subgroup.map_subtype_le P', ?_⟩
  rw [Subgroup.card_map_of_injective (fixed α ⊓ B.comap π).subtype_injective, hP']

end CFSG.EvenSporadicStandard.Induction.CoverFix
