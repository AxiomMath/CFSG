module

public import TauCeti.GroupTheory.Coset.Basic
public import TauCeti.GroupTheory.Transfer
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Fusion

public section

namespace CFSG.EvenSporadicStandard

open MulAction Subgroup

variable {G : Type*} [Group G]

@[expose] noncomputable def valAt (H : Subgroup G) (φ : H →* ℤˣ) (a b : G) : ℤˣ := by
  classical
  exact if h : a⁻¹ * b ∈ H then φ ⟨a⁻¹ * b, h⟩ else 1

theorem valAt_of_mem {H : Subgroup G} (φ : H →* ℤˣ) {a b : G} (h : a⁻¹ * b ∈ H) :
    valAt H φ a b = φ ⟨a⁻¹ * b, h⟩ := by
  simp [valAt, h]

theorem transfer_involution_eq_prod {H : Subgroup G} (φ : H →* ℤˣ) {z : G} (hz : z * z = 1)
    [H.FiniteIndex] [Fintype (G ⧸ H)] [DecidableEq (G ⧸ H)] :
    φ.transfer z = ∏ q ∈ (Finset.univ.filter fun q : G ⧸ H => z • q = q),
      valAt H φ q.out (z * q.out) := by
  classical
  have h1 : φ.transfer z = ∏ q : G ⧸ H, valAt H φ (z • q).out (z * q.out) := by
    rw [MonoidHom.transfer_eq_prod_of_bijective φ (fun q : G ⧸ H => q.out) (by simp) z (z • ·)
      (fun q => QuotientGroup.mk_out_smul z q)]
    refine Finset.prod_congr rfl fun q _ => ?_
    rw [valAt_of_mem φ (QuotientGroup.eq.mp (QuotientGroup.mk_out_smul z q))]
  rw [h1, ← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun q : G ⧸ H => z • q = q)]
  have hzz : ∀ q : G ⧸ H, z • (z • q) = q := fun q => by rw [smul_smul, hz, one_smul]
  have hnf : ∏ q ∈ Finset.univ.filter (fun q : G ⧸ H => ¬ z • q = q),
      valAt H φ (z • q).out (z * q.out) = 1 := by
    refine Finset.prod_involution (fun q _ => z • q) ?_ ?_ ?_ ?_
    · intro q hq
      have h2 : (z • q).out⁻¹ * (z * q.out) ∈ H :=
        QuotientGroup.eq.mp (QuotientGroup.mk_out_smul z q)
      have h3 : q.out⁻¹ * (z * (z • q).out) ∈ H := by
        have := QuotientGroup.eq.mp (QuotientGroup.mk_out_smul z (z • q))
        rw [hzz q] at this
        exact this
      rw [hzz q]
      rw [valAt_of_mem φ h2, valAt_of_mem φ h3, ← map_mul]
      have : (⟨(z • q).out⁻¹ * (z * q.out), h2⟩ * ⟨q.out⁻¹ * (z * (z • q).out), h3⟩ : H) = 1 := by
        ext
        simp only [Subgroup.coe_mul, OneMemClass.coe_one]
        calc (z • q).out⁻¹ * (z * q.out) * (q.out⁻¹ * (z * (z • q).out))
            = (z • q).out⁻¹ * (z * z) * (z • q).out := by group
          _ = 1 := by rw [hz]; group
      rw [this, map_one]
    · intro q hq _
      simpa using hq
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      rw [hzz q]
      exact fun h => hq h.symm
    · intro q hq
      exact hzz q
  rw [hnf, mul_one]
  refine Finset.prod_congr rfl fun q hq => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
  rw [hq]

theorem even_card_fixed_neg {H : Subgroup G} (φ : H →* ℤˣ) {z : G} (hz : z * z = 1)
    (hG : ∀ ψ : G →* ℤˣ, ψ = 1) [H.FiniteIndex] [Fintype (G ⧸ H)] [DecidableEq (G ⧸ H)] :
    Even (Finset.univ.filter fun q : G ⧸ H => z • q = q ∧
      valAt H φ q.out (z * q.out) = -1).card := by
  classical
  have h1 : φ.transfer z = 1 := by
    have := congrArg (fun ψ : G →* ℤˣ => ψ z) (hG (φ.transfer))
    simpa using this
  rw [transfer_involution_eq_prod φ hz] at h1
  have h2 : ∀ q : G ⧸ H, valAt H φ q.out (z * q.out) =
      if valAt H φ q.out (z * q.out) = -1 then -1 else 1 := by
    intro q
    rcases Int.units_eq_one_or (valAt H φ q.out (z * q.out)) with h | h <;> simp [h]
  rw [Finset.prod_congr rfl fun q _ => h2 q, Finset.prod_ite, Finset.prod_const,
    Finset.prod_const_one, mul_one, Finset.filter_filter] at h1
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  have := (neg_one_pow_eq_one_iff_even hne).1 h1
  simpa [and_comm] using this

section Helpers

variable {H : Subgroup G}

theorem out_inv_mul_mem_of_smul_eq {g : G} {q : G ⧸ H} (hq : g • q = q) :
    q.out⁻¹ * (g * q.out) ∈ H := by
  have h1 : (↑(g * q.out) : G ⧸ H) = ↑q.out := by
    rw [← QuotientGroup.mk_out_smul, QuotientGroup.out_eq', hq, QuotientGroup.out_eq']
  exact QuotientGroup.eq.mp h1.symm

end Helpers

theorem even_nat_card_fixed_neg {H : Subgroup G} (φ : H →* ℤˣ) {z : G} (hz : z * z = 1)
    (hG : ∀ ψ : G →* ℤˣ, ψ = 1) [H.FiniteIndex] [Finite G] :
    Even (Nat.card {q : G ⧸ H // z • q = q ∧ valAt H φ q.out (z * q.out) = -1}) := by
  classical
  let _ : Fintype (G ⧸ H) := Fintype.ofFinite _
  have := even_card_fixed_neg φ hz hG
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact this

theorem card_units_int : Nat.card ℤˣ = 2 := by
  rw [Nat.card_eq_two_iff]
  refine ⟨1, -1, by decide, ?_⟩
  ext u
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  exact Int.units_eq_one_or u

theorem hom_units_eq_one_of_simple {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (ψ : G →* ℤˣ) : ψ = 1 := by
  by_contra hne
  obtain ⟨g, hg⟩ : ∃ g, ψ g ≠ 1 := by
    by_contra h
    push Not at h
    exact hne (MonoidHom.ext h)
  have hsurj : Function.Surjective ψ := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, map_one ψ⟩
    · exact ⟨g, (Int.units_eq_one_or (ψ g)).resolve_left hg⟩
  have hidx : ψ.ker.index = 2 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top, card_units_int]
  exact not_exists_normal_index_two_of_nonabelian hnonab ⟨ψ.ker, inferInstance, hidx⟩

end CFSG.EvenSporadicStandard
