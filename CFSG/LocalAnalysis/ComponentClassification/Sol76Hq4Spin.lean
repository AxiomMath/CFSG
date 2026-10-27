module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76Hq4Main
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Hq4OrthCent

public section

namespace CFSG.ComponentClassification.Sol76T13.Hq4

open CFSG Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank
open CFSG.Blueprint CFSG.LieType.Steinberg.CentralExt CFSG.LieType.Universal.Spin

theorem exists_noncentral_involution_of_POmegaPlus {Q : Type} [Group Q] [Finite Q]
    {n p f : ℕ} (hp2 : p ≠ 2) (hL : LieModel (Q ⧸ center Q) .POmegaPlus n p f) :
    ∃ x : Q, orderOf x = 2 ∧ x ∉ center Q := by
  classical
  obtain ⟨⟨hp, hf, hn4⟩, K, _, _, hK, ⟨e⟩⟩ :=
    GriessNative.classical_of_lieModel (t := .POmegaPlus) hL (by decide)
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := SectionRank.ClassicalOdd.charP_of_card hK
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP p hp2
  have hn4' : 4 ≤ n := hn4
  have hn3 : 3 ≤ n := by omega
  set S := StatedProj (StatedOmega (StatedQuadPlus n K))
  set qS := spinToStatedProj (quadPlus n K) (range_spinMatrix_quadPlus (K := K) hn3) with hqS
  obtain ⟨hqsurj, hqker, -⟩ := spinToStatedProj_quadPlus (K := K) hn3
  set πQ : Q →* S := e.toMonoidHom.comp (QuotientGroup.mk' (center Q)) with hπQ
  have hπQsurj : Function.Surjective πQ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπQ1 : ∀ y : Q, πQ y = 1 ↔ y ∈ center Q := by
    intro y
    rw [hπQ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  set E : Subgroup (spinGroup (quadPlus n K) × Q) :=
    (qS.comp (MonoidHom.fst _ Q)).eqLocus (πQ.comp (MonoidHom.snd _ Q)) with hE
  have hmemE : ∀ a, a ∈ E ↔ qS a.1 = πQ a.2 := fun _ => Iff.rfl
  set π₁ : ↥E →* spinGroup (quadPlus n K) := (MonoidHom.fst _ Q).comp E.subtype with hπ₁
  have hπ₁surj : Function.Surjective π₁ := by
    intro a
    obtain ⟨y, hy⟩ := hπQsurj (qS a)
    exact ⟨⟨(a, y), (hmemE _).mpr hy.symm⟩, rfl⟩
  have hπ₁ker : π₁.ker ≤ center ↥E := by
    intro g hg
    have h1 : (g : spinGroup (quadPlus n K) × Q).1 = 1 := hg
    have h2' := (hmemE _).mp g.2
    rw [h1, map_one] at h2'
    have hz : (g : spinGroup (quadPlus n K) × Q).2 ∈ center Q := (hπQ1 _).mp h2'.symm
    rw [mem_center_iff]
    intro k
    apply Subtype.ext
    apply Prod.ext
    · change (k : spinGroup (quadPlus n K) × Q).1 * (g : spinGroup (quadPlus n K) × Q).1 =
        (g : spinGroup (quadPlus n K) × Q).1 * (k : spinGroup (quadPlus n K) × Q).1
      rw [h1, one_mul, mul_one]
    · exact mem_center_iff.mp hz _
  obtain ⟨σ, hσ⟩ : ∃ σ : spinGroup (quadPlus n K) →* ↥E, ∀ g, π₁ (σ g) = g := by
    have hq3 : 3 ≤ Nat.card K := by
      rw [hK]
      exact le_trans (by have := hp.two_le; omega) (Nat.le_self_pow (by omega) p)
    by_cases h3 : Nat.card K = 3
    · exact SpinPlusClosed.spinPlus_three_exists_section_of_central hn3 h3 hn4' hπ₁surj hπ₁ker
    · exact SpinPlusClosed.spinPlus_exists_section_of_central hn3 (by omega) hπ₁surj hπ₁ker
  set τ : spinGroup (quadPlus n K) →* Q := (MonoidHom.snd _ Q).comp (E.subtype.comp σ)
    with hτ
  have hτq : ∀ a, πQ (τ a) = qS a := by
    intro a
    have h1 := (hmemE _).mp (σ a).2
    have h2' : ((σ a : ↥E) : spinGroup (quadPlus n K) × Q).1 = a := hσ a
    rw [h2'] at h1
    exact h1.symm
  set t := SpinPlusClosed.pairTorus K hn3 0 0 with ht
  have ht2 : t * t = 1 := SpinPlusClosed.pairTorus_mul_self (K := K) hn3 0 0
  have hact := SpinPlusClosed.actsBy_pairTorus (K := K) hn3 (o := 0) (l := 0) (by omega)
  have hqt : qS t ≠ 1 := by
    intro h
    have hk : t ∈ qS.ker := h
    rw [hqker, Subgroup.mem_comap, mem_statedScalars_iff, toLinEquiv_spinMatrix] at hk
    obtain ⟨c, hc⟩ := mem_scalars.mp hk
    set F := plusFrame n K hn3
    have hv : ∀ m r, F.vec m r ≠ 0 := fun m r h0 => by
      have := F.polar_vec_not m r
      rw [h0, polar_zero_left] at this
      exact zero_ne_one this
    have h0 := hact ⟨0, by omega⟩ true
    have h2v := hact ⟨2, by omega⟩ true
    rw [hc] at h0 h2v
    have hm1 : c = -1 := by simpa using eq_of_smul_eq_smul (hv _ _) h0
    have hp1 : c = 1 := by simpa using eq_of_smul_eq_smul (hv _ _) h2v
    rw [hm1] at hp1
    exact h2 (by linear_combination -hp1)
  refine ⟨τ t, orderOf_eq_prime (by rw [pow_two, ← map_mul, ht2, map_one]) ?_, ?_⟩
  · intro h
    apply hqt
    rw [← hτq, h, map_one]
  · intro h
    apply hqt
    rw [← hτq]
    exact (hπQ1 _).mpr h

theorem pOmegaPlusInvolutionInput : POmegaPlusInvolutionInput :=
  fun _ _ _ _ _ _ _ hp2 _ hL _ _ _ _ _ _ _ _ _ => exists_noncentral_involution_of_POmegaPlus hp2 hL

end CFSG.ComponentClassification.Sol76T13.Hq4
