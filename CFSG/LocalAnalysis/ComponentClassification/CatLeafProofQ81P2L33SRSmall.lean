module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRBase
public import CFSG.Sporadic.Co3
public import CFSG.Sporadic.SmallOddCore.J3Aut
public import CFSG.Sporadic.SmallOddCore.HSAut
public import CFSG.Sporadic.SmallOddCore.McLAut
public import CFSG.Sporadic.SmallOddCore.Co3GenFitting

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.SR

open CFSG Subgroup CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Co3
open CFSG.Sporadic.SmallOddCore

section AutModel

variable {M : Type} [Group M] {P R : Subgroup M}

theorem forall_of_autModel (h : CFSG.Sporadic.SmallOddCore.AutModel P R)
    (hC : ∀ x ∈ R, orderOf x = 2 → ¬ IsPGroup 2 ↥(P ⊓ centralizer ({x} : Set M))) :
    ∀ a : MulAut P, orderOf a = 2 → ¬ IsPGroup 2 ↥(fixedPoints a) := by
  intro a ha
  refine not_isPGroup_fixedPoints_of_conj (h.elt_spec a) (hC _ (h.elt_mem a) ?_)
  rw [← h.hom_apply, orderOf_injective h.hom h.hom_injective, ha]

theorem forall_of_autModel_rows (h : CFSG.Sporadic.SmallOddCore.AutModel P R) {ι : Type*}
    (rows : List ι) (rep : ι → M)
    (hcov : ∀ t ∈ R, orderOf t = 2 → ∃ r ∈ rows, ∃ g ∈ P, t = g * rep r * g⁻¹)
    (hrow : ∀ r ∈ rows, ¬ IsPGroup 2 ↥(P ⊓ centralizer ({rep r} : Set M))) :
    ∀ a : MulAut P, orderOf a = 2 → ¬ IsPGroup 2 ↥(fixedPoints a) := by
  refine forall_of_autModel h fun x hx ho => ?_
  obtain ⟨r, hr, g, hg, rfl⟩ := hcov x hx ho
  exact not_isPGroup_inf_centralizer_conj hg (hrow r hr)

end AutModel

theorem not_isPGroup_classRow {n : ℕ} {P : Subgroup (Equiv.Perm (Fin n))} {rows : List ClassRow}
    {r : ClassRow} (hr : r ∈ rows) {L : List (Bool × ℕ × ℕ)}
    (hmap : rows.map (fun r => (r.outer, r.classSize, r.centOrder)) = L)
    (hL : ∀ x ∈ L, 3 ∣ x.2.2)
    (hc : Nat.card ↥(P ⊓ centralizer ({tp n r.rep} : Set (Equiv.Perm (Fin n)))) = r.centOrder) :
    ¬ IsPGroup 2 ↥(P ⊓ centralizer ({tp n r.rep} : Set (Equiv.Perm (Fin n)))) := by
  apply not_isPGroup_of_three_dvd
  rw [hc]
  have hm := List.mem_map_of_mem (f := fun r : ClassRow => (r.outer, r.classSize, r.centOrder)) hr
  rw [hmap] at hm
  exact hL _ hm

theorem j1_not_comm :
    ∃ x y : NativeSporadic.J1, x * y ≠ y * x := by
  obtain ⟨-, -, -, hc, -⟩ := at_j1_image_pair_count
  refine ⟨j1PermEquiv.symm j1a, j1PermEquiv.symm j1b, fun h => ?_⟩
  have h' : j1a * j1b = j1b * j1a := by
    simpa using congrArg j1PermEquiv h
  have h1 : j1A1 * j1A2 * j1A1⁻¹ * j1A2⁻¹ = 1 := by
    have h2 : j1A1 * j1A2 = j1A2 * j1A1 := congrArg Subtype.val h'
    rw [h2]
    group
  rw [h1, orderOf_one] at hc
  norm_num at hc

theorem sporNoTwoFix_J1 :
    SporNoTwoFix .J1 := by
  have : Finite NativeSporadic.J1 := CFSG.Sporadic.J1.fam_j1_simplicity.1
  have : IsSimpleGroup NativeSporadic.J1 := CFSG.Sporadic.J1.isSimpleGroup_J1
  have hZ : center NativeSporadic.J1 = ⊥ := CatLeaf.center_eq_bot_of_simple j1_not_comm
  refine sporNoTwoFix_of_mulEquiv (P := NativeSporadic.J1) (MulEquiv.refl _)
    (forall_of_inner hZ at_j1_schreier.2.1 fun t ht => ?_)
  apply not_isPGroup_of_three_dvd
  rw [(ctugs_j1_involution_centralizer_odd_core_free ⟨MulEquiv.refl _⟩ t ht).1]
  norm_num

theorem sporNoTwoFix_J2 :
    SporNoTwoFix .J2 := by
  obtain ⟨-, -, -, hrows, hcov, -, hmap, -⟩ :=
    ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial
  refine sporNoTwoFix_of_mulEquiv (P := ↥j2P) j2PermEquiv
    (forall_of_autModel_rows j2_autModel j2Rows (fun r => tp 315 r.rep) hcov fun r hr => ?_)
  exact not_isPGroup_classRow hr hmap (by decide) (hrows r hr).2.2.2.2.1

theorem sporNoTwoFix_J3 :
    SporNoTwoFix .J3 := by
  obtain ⟨-, -, -, hrows, hcov, -, hmap, -⟩ :=
    ctuc_j3_all_involution_fixed_subgroups_odd_core_trivial
  refine sporNoTwoFix_of_mulEquiv (P := ↥j3P) j3PermEquiv
    (forall_of_autModel_rows j3_autModel j3Rows (fun r => tp 6156 r.rep) hcov fun r hr => ?_)
  exact not_isPGroup_classRow hr hmap (by decide) (hrows r hr).2.2.2.2.1

theorem sporNoTwoFix_HS :
    SporNoTwoFix .HS := by
  obtain ⟨-, -, -, hrows, hcov, -, hmap, -⟩ := hs_involution_centralizers
  refine sporNoTwoFix_of_mulEquiv (P := ↥hsP) hsPermEquiv
    (forall_of_autModel_rows hs_autModel hsRows (fun r => tp 3850 r.rep) hcov fun r hr => ?_)
  exact not_isPGroup_classRow hr hmap (by decide) (hrows r hr).2.2.2.2.1

theorem sporNoTwoFix_McL :
    SporNoTwoFix .McL := by
  obtain ⟨-, -, -, hrows, hcov, -, hmap, -⟩ := mcl_involution_centralizers
  refine sporNoTwoFix_of_mulEquiv (P := ↥mclP) mclPermEquiv
    (forall_of_autModel_rows mcl_autModel mclRows (fun r => tp 275 r.rep) hcov fun r hr => ?_)
  exact not_isPGroup_classRow hr hmap (by decide) (hrows r hr).2.2.2.2.1

theorem sporNoTwoFix_Co3 :
    SporNoTwoFix .Co3 := by
  have hS : IsSimpleGroup NativeSporadic.Co3 := CFSG.Sporadic.Co3.isSimpleGroup_Co3
  have : IsSimpleGroup co3P := @MulEquiv.isSimpleGroup _ _ _ _ hS co3PermEquiv.symm
  obtain ⟨hM, hMc, hM1, hM1c, -⟩ := AT_Co3_exact_involution_centralizers
  obtain ⟨-, -, -, hiff, -⟩ := ctuc_co3_complete_inner_involution_classes
  refine sporNoTwoFix_of_mulEquiv (P := ↥co3P) co3PermEquiv
    (forall_of_autModel_rows co3_autModel [co3Z, co3Tt] (fun x => x) ?_ ?_)
  · intro t ht ho
    by_cases h : ∃ g ∈ co3P, t = g * co3Tt * g⁻¹
    · obtain ⟨g, hg, rfl⟩ := h
      exact ⟨co3Tt, by simp, g, hg, rfl⟩
    · obtain ⟨g, hg, rfl⟩ := (hiff t ht ho).2 h
      exact ⟨co3Z, by simp, g, hg, rfl⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [← hM]
      exact not_isPGroup_of_three_dvd (by rw [hMc]; norm_num)
    · rw [← hM1]
      exact not_isPGroup_of_three_dvd (by rw [hM1c]; norm_num)

end CFSG.ComponentClassification.HarrisLit.L33.SR
