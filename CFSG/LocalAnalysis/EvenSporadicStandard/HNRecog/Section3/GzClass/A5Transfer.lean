module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.A5Five
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.A5Outer

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private theorem a5Transfer_natCard_A5WrTwo : Nat.card A5WrTwo = 7200 := by
  haveI : Finite (Multiplicative (ZMod 2)) := inferInstance
  rw [RegularWreathProduct.card]
  have h5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  rw [h5, h2]
  norm_num

private theorem a5Transfer_card_centralizer {Γ : Type*} [Group Γ] (e : Γ ≃* A5WrTwo)
    (u : Γ) : Nat.card (Subgroup.centralizer ({e u} : Set A5WrTwo)) =
      Nat.card (Subgroup.centralizer ({u} : Set Γ)) := by
  have hmap : (Subgroup.centralizer ({u} : Set Γ)).map e.toMonoidHom =
      Subgroup.centralizer ({e u} : Set A5WrTwo) := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff,
      MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [← map_mul, ← map_mul, hz]
    · intro hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply, hy]
  rw [← hmap, Subgroup.card_map_of_injective e.injective]

private theorem a5Transfer_natCard_eq {Γ : Type*} [Group Γ] (e : Γ ≃* A5WrTwo) :
    Nat.card Γ = 7200 := by
  rw [Nat.card_congr e.toEquiv, a5Transfer_natCard_A5WrTwo]

private theorem a5Transfer_mem_commutator {Γ : Type*} [Group Γ] (e : Γ ≃* A5WrTwo)
    (u : Γ) : u ∈ commutator Γ ↔ e u ∈ commutator A5WrTwo := by
  have hmap : (commutator Γ).map e.toMonoidHom = commutator A5WrTwo := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]
  rw [← hmap, Subgroup.mem_map_equiv]
  simp

theorem ne_one_of_card_centralizer_ne {Γ : Type*} [Group Γ] (e : Γ ≃* A5WrTwo) {u : Γ}
    (h : Nat.card ↥(Subgroup.centralizer ({u} : Set Γ)) ≠ 7200) : u ≠ 1 := by
  rintro rfl
  apply h
  rw [show Subgroup.centralizer ({1} : Set Γ) = ⊤ by simp, Subgroup.card_top,
    a5Transfer_natCard_eq e]

theorem involution_cases_of_mulEquiv {Γ : Type*} [Group Γ] (e : Γ ≃* A5WrTwo) {u : Γ}
    (hu2 : u ^ 2 = 1) (hu1 : u ≠ 1) :
    (u ∉ commutator Γ ∧ Nat.card ↥(Subgroup.centralizer ({u} : Set Γ)) = 120) ∨
    (u ∈ commutator Γ ∧ Nat.card ↥(Subgroup.centralizer ({u} : Set Γ)) = 240) ∨
    (u ∈ commutator Γ ∧ Nat.card ↥(Subgroup.centralizer ({u} : Set Γ)) = 32) := by
  have heu2 : (e u) ^ 2 = 1 := by rw [← map_pow, hu2, map_one]
  have heu1 : e u ≠ 1 := fun h1 => hu1 ((MulEquiv.map_eq_one_iff e).mp h1)
  have hcard := a5Transfer_card_centralizer e u
  by_cases hmem : e u ∈ commutator A5WrTwo
  · rcases baseInvolution_cases hmem heu2 heu1 with
      ⟨x, _, _, _, h240⟩ | ⟨x, y, _, _, _, _, _, h32⟩
    · right; left
      exact ⟨(a5Transfer_mem_commutator e u).mpr hmem, by rw [← hcard]; exact h240⟩
    · right; right
      exact ⟨(a5Transfer_mem_commutator e u).mpr hmem, by rw [← hcard]; exact h32⟩
  · left
    exact ⟨fun hc => hmem ((a5Transfer_mem_commutator e u).mp hc),
      by rw [← hcard]; exact card_centralizer_outer_involution hmem heu2⟩

theorem card_centralizer_five_of_mulEquiv {Γ : Type*} [Group Γ] (e : Γ ≃* A5WrTwo) {u ρ : Γ}
    (hu : u ∈ commutator Γ) (hu2 : u ^ 2 = 1)
    (hu240 : Nat.card ↥(Subgroup.centralizer ({u} : Set Γ)) = 240) (hρ : orderOf ρ = 5)
    (hρu : ρ * u = u * ρ) :
    Nat.card ↥(Subgroup.centralizer ({ρ} : Set Γ)) = 300 := by
  have heu2 : (e u) ^ 2 = 1 := by rw [← map_pow, hu2, map_one]
  have heu : e u ∈ commutator A5WrTwo := (a5Transfer_mem_commutator e u).mp hu
  have heρ : orderOf (e ρ) = 5 := by rw [MulEquiv.orderOf_eq, hρ]
  have heρu : e ρ * e u = e u * e ρ := by rw [← map_mul, ← map_mul, hρu]
  have heu240 : Nat.card ↥(Subgroup.centralizer ({e u} : Set A5WrTwo)) = 240 := by
    rw [a5Transfer_card_centralizer e u, hu240]
  rw [← a5Transfer_card_centralizer e ρ]
  exact card_centralizer_five heu heu2 heu240 heρ heρu

theorem exists_outer_involution_mul_of_mulEquiv {Γ : Type*} [Group Γ] (e : Γ ≃* A5WrTwo) {u : Γ}
    (hu2 : u ^ 2 = 1) (hu1 : u ≠ 1)
    (h : u ∉ commutator Γ ∨ Nat.card ↥(Subgroup.centralizer ({u} : Set Γ)) = 32) :
    ∃ v : Γ, v ^ 2 = 1 ∧ v ∉ commutator Γ ∧ ∀ k : ℕ, orderOf (u * v) ≠ 2 ^ k := by
  have heu2 : (e u) ^ 2 = 1 := by rw [← map_pow, hu2, map_one]
  have heu1 : e u ≠ 1 := fun h1 => hu1 ((MulEquiv.map_eq_one_iff e).mp h1)
  have heh : e u ∉ commutator A5WrTwo ∨
      Nat.card ↥(Subgroup.centralizer ({e u} : Set A5WrTwo)) = 32 := by
    rcases h with h | h
    · left
      exact fun hc => h ((a5Transfer_mem_commutator e u).mpr hc)
    · right
      rw [a5Transfer_card_centralizer e u, h]
  obtain ⟨v', hv'2, hv'out, hv'ord⟩ := exists_outer_involution_mul heu2 heu1 heh
  refine ⟨e.symm v', ?_, ?_, ?_⟩
  · apply e.injective
    rw [map_pow, map_one, e.apply_symm_apply]
    exact hv'2
  · intro hc
    apply hv'out
    have h' := (a5Transfer_mem_commutator e (e.symm v')).mp hc
    simpa using h'
  · intro k hk
    apply hv'ord k
    have hmul : e (u * e.symm v') = e u * v' := by
      rw [map_mul, e.apply_symm_apply]
    rw [← hmul, MulEquiv.orderOf_eq]
    exact hk

theorem exists_conj_of_outer_of_mulEquiv {Γ : Type*} [Group Γ] (e : Γ ≃* A5WrTwo) {u v : Γ}
    (hu : u ∉ commutator Γ) (hv : v ∉ commutator Γ) (hu2 : u ^ 2 = 1) (hv2 : v ^ 2 = 1) :
    ∃ b ∈ commutator Γ, b * u * b⁻¹ = v := by
  have heu : e u ∉ commutator A5WrTwo :=
    fun hc => hu ((a5Transfer_mem_commutator e u).mpr hc)
  have hev : e v ∉ commutator A5WrTwo :=
    fun hc => hv ((a5Transfer_mem_commutator e v).mpr hc)
  have heu2 : (e u) ^ 2 = 1 := by rw [← map_pow, hu2, map_one]
  have hev2 : (e v) ^ 2 = 1 := by rw [← map_pow, hv2, map_one]
  obtain ⟨b', hb'mem, hb'⟩ :=
    A5WrTwo.exists_conj_of_outer_involutions heu hev heu2 hev2
  refine ⟨e.symm b', ?_, ?_⟩
  · exact (a5Transfer_mem_commutator e (e.symm b')).mpr (by simpa using hb'mem)
  · apply e.injective
    calc e (e.symm b' * u * (e.symm b')⁻¹)
        = b' * e u * b'⁻¹ := by simp
      _ = e v := hb'

end CFSG.EvenSporadicStandard.HNRecog.Section3
