module

public import CFSG.LargeExtraspecial.S45QPhi
public import CFSG.LargeExtraspecial.S45QLin
public import CFSG.LargeExtraspecial.S45QSp
public import CFSG.LargeExtraspecial.S45QOmegaMinus

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S45Q

open Module Subgroup

theorem fifteen_dvd_card_of_transitive {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (h4 : finrank (ZMod 2) V = 4)
    {X : Subgroup (V ≃ₗ[ZMod 2] V)} {a : V} (ha : a ≠ 0)
    (htr : ∀ v : V, v ≠ 0 → ∃ x ∈ X, x a = v) : 15 ∣ Nat.card X := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have hV : Nat.card V = 16 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), h4, Nat.card_zmod]
    norm_num
  have horb : MulAction.orbit X a = (Set.univ : Set V) \ {0} := by
    ext v
    simp only [MulAction.mem_orbit_iff, Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff,
      true_and]
    constructor
    · rintro ⟨x, rfl⟩
      change (x : V ≃ₗ[ZMod 2] V) a ≠ 0
      exact (LinearEquiv.map_ne_zero_iff _).mpr ha
    · intro hv
      obtain ⟨x, hx, hxa⟩ := htr v hv
      exact ⟨⟨x, hx⟩, hxa⟩
  have hcard : (MulAction.orbit X a).ncard = 15 := by
    rw [horb, Set.ncard_sdiff_singleton_of_mem (Set.mem_univ 0), Set.ncard_univ, hV]
  have h := (MulAction.stabilizer X a).card_mul_index
  rw [MulAction.index_stabilizer, hcard] at h
  exact ⟨_, by rw [← h, mul_comm]⟩

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

theorem hyp45Q (H : S4.Hyp4 S g) (C : S4.Cons311 S g) : S5.Hyp45Q H C where
  lin_two _ hL h2 := by
    rw [hL.eq_top]
    exact isSolvable_top_of_finrank_two h2
  lin _ hL h3 := by
    rw [hL.eq_top]
    exact ⟨isSimpleGroup_top_of_three_le h3, nonabelianSylowTwo_top h3⟩
  sp ht ht1 hVQ hSp h6 := by
    rw [hSp.eq_sp]
    exact ⟨isSimpleGroup_isometryGroup (S4.beta_isAlt H C ht ht1 hVQ)
      (S4.beta_nondegenerate H C ht ht1 hVQ) h6,
      nonabelianSylowTwo_isometryGroup (S4.beta_isAlt H C ht ht1 hVQ)
        (S4.beta_nondegenerate H C ht ht1 hVQ) (by omega)⟩
  sp_four ht ht1 hVQ hSp h4 := by
    rw [hSp.eq_sp]
    obtain ⟨hN, hS, hI, hNS⟩ := commutator_isometryGroup_four (S4.beta_isAlt H C ht ht1 hVQ)
      (S4.beta_nondegenerate H C ht ht1 hVQ) h4
    exact ⟨_, commutator_le_self _, hN, hS, hI, hNS⟩
  a6 ht ht1 hVQ hA := by
    rw [hA.eq_commutator]
    exact (commutator_isometryGroup_four (S4.beta_isAlt H C ht ht1 hVQ)
      (S4.beta_nondegenerate H C ht ht1 hVQ) hA.finrank_eq).2.1
  omega _ _ _ hO h6 := by
    obtain ⟨Q, hQ, -, hR, -, -⟩ := hO.exists_form
    rw [hR]
    exact isSimpleGroup_omegaGroup_and_nonabelianSylowTwo hQ h6
  omega_four _ _ _ hO h4 := by
    obtain ⟨Q, hQ, -, hR, -, -⟩ := hO.exists_form
    rw [hR]
    exact omegaGroup_simple_or_solvable_four hQ h4
  pgl25 ht ht1 hVQ hP :=
    exists_simple_normal_of_fifteen_dvd (S4.beta_isAlt H C ht ht1 hVQ)
      (S4.beta_nondegenerate H C ht ht1 hVQ) hP.finrank_eq
      (S4.RmodN_le_isometryGroup H C ht ht1 hVQ)
      (fifteen_dvd_card_of_transitive hP.finrank_eq (S4.aV_ne_zero H ht) hP.transitive)

end CFSG.LargeExtraspecial.S45Q
