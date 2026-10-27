module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZSigCtx
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinE4tModel
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Sp6B
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4O8D
public import Certificates.Certificate550105
public import Certificates.Certificate550106

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.TL4.E4Sp6

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Co3 CFSG.EvenSmallLie.Sp6
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Q3.TL4.E4C CFSG.ClassicalInvolution.Q3.TL4.E4Sp6Data

theorem valid_of_centCheck_sp6 {Q : RawSchreierDatum 36} {c : ℕ}
    {gs reps : List (Equiv.Perm (Fin 36))} {r : Equiv.Perm (Fin 36)}
    (h : CFSG.EvenSmallLie.Sp6.centCheck Q c gs reps r = true) : ValidSchreier Q := by
  simp only [CFSG.EvenSmallLie.Sp6.centCheck, Bool.and_eq_true] at h
  exact h.1.1.1.1.1

theorem sp6_move :
    ∀ a ∈ co3X36, a * a = 1 → a ≠ 1 → a ≠ sp6Rep2 → (∀ x ∈ K0, a * x = x * a) →
      ∃ c ∈ co3X36, c ^ 3 = 1 ∧ c * sp6Rep2 = sp6Rep2 * c ∧ c * a ≠ a * c := by
  intro a ha ha2 ha1 hax hK
  have hρK : rho () ∈ K0 := Subgroup.subset_closure (Set.mem_insert _ _)
  have hjK : jay () ∈ K0 := Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have haρ := hK _ hρK
  have haj := hK _ hjK
  have hr2 : rho () * rho () = sp6Rep2 := by
    have := check_parts.1
    rwa [tab_eq] at this
  have har : a * sp6Rep2 = sp6Rep2 * a := by
    rw [← hr2]
    calc a * (rho () * rho ()) = (a * rho ()) * rho () := by rw [mul_assoc]
      _ = (rho () * a) * rho () := by rw [haρ]
      _ = rho () * (a * rho ()) := by rw [mul_assoc]
      _ = rho () * (rho () * a) := by rw [haρ]
      _ = (rho () * rho ()) * a := by rw [mul_assoc]
  have hvalid : ValidSchreier sp6CentQ2 := valid_of_centCheck_sp6 sp6_cent_check₂
  have hmemA : a ∈ moveElems () := by
    rw [moveElems, mem_enumerationTab_iff _ hvalid, ← sp6_cent_spec₂.1]
    exact mem_centralizerIn.2 ⟨by rwa [sp6Q_originalSubgroup], har⟩
  have hin : a ∈ moveInvs (moveElems ()) := by
    simp only [moveInvs, tab_eq, List.mem_filter, decide_eq_true_eq]
    exact ⟨hmemA, ha2, ha1, hax, haρ, haj⟩
  have hcheck : moveCheck () = true := Certificates.certificate550105
  simp only [moveCheck, List.all_eq_true, List.any_eq_true, decide_eq_true_eq] at hcheck
  obtain ⟨c, hc, hca⟩ := hcheck a hin
  simp only [moveThrees, List.mem_filter, decide_eq_true_eq] at hc
  obtain ⟨hcmem, hc3⟩ := hc
  rw [moveElems, mem_enumerationTab_iff _ hvalid, ← sp6_cent_spec₂.1] at hcmem
  obtain ⟨hcX, hcr⟩ := mem_centralizerIn.1 hcmem
  exact ⟨c, by rwa [sp6Q_originalSubgroup] at hcX, by rw [pow_three']; exact hc3, hcr, hca⟩

end CFSG.ClassicalInvolution.Q3.TL4.E4Sp6

namespace CFSG.ClassicalInvolution.Q3.TL4.E4O8

open CFSG.EvenSmallLie.OmegaEight CFSG.Certificates CFSG.Certificates.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.ComponentClassification.J2Cover
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.O8Data CFSG.ClassicalInvolution.Q3.TL4.E4O8Data
open CFSG.ClassicalInvolution.Q3.TL4.E4A CFSG.ClassicalInvolution.Q3.TL4.E4C

theorem o8_move :
    ∀ a ∈ omegaT, a * a = 1 → a ≠ 1 → a ≠ mainPerm 0 → (∀ x ∈ K0, a * x = x * a) →
      ∃ c ∈ omegaT, c ^ 3 = 1 ∧ c * mainPerm 0 = mainPerm 0 * c ∧ c * a ≠ a * c := by
  intro a ha ha2 ha1 hax hK
  have hu0K : u0 ∈ K0 := Subgroup.subset_closure (Set.mem_insert _ _)
  have hv0K : v0 ∈ K0 := Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hau := hK u0 hu0K
  have hav := hK v0 hv0K
  exact Certificates.certificate550106 a ha ha2 ha1 hax hau hav

end CFSG.ClassicalInvolution.Q3.TL4.E4O8

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ZSig

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Q3.TL4

theorem e4MoveW_of_model {M G : Type} [Group M] [Group G] (H Kc : Subgroup G) (rc : G)
    (hid : ∀ (K : Subgroup M) (s : M), Nonempty (↥K ≃* QuaternionGroup 2) →
      IsUniqueInvolution K s →
      (∀ c ∈ Subgroup.centralizer ({s} : Set M), conjSub c K = K ∨
        ∀ x ∈ K, ∀ y ∈ conjSub c K, x * y = y * x) →
      ∃ φ : M →* G, Function.Injective φ ∧ φ.range = H ∧ K.map φ = Kc)
    (hrc : ∀ sc, IsUniqueInvolution Kc sc → sc = rc)
    (hmove : ∀ a ∈ H, a * a = 1 → a ≠ 1 → a ≠ rc → (∀ x ∈ Kc, a * x = x * a) →
      ∃ c ∈ H, c ^ 3 = 1 ∧ c * rc = rc * c ∧ c * a ≠ a * c) : E4MoveW M := by
  intro K s hq hinv htw a ha2 ha1 has haK
  obtain ⟨φ, hφ, hrange, hKc⟩ := hid K s hq hinv htw
  have hs : φ s = rc := by
    refine hrc _ ?_
    rw [← hKc]
    exact Vtx.isUniqueInvolution_map φ hφ hinv
  obtain ⟨c', hcH, hc3, hcr, hca⟩ := hmove (φ a) (hrange ▸ ⟨a, rfl⟩)
    (by rw [← map_mul, ha2, map_one])
    (fun h => ha1 (hφ (by rw [h, map_one])))
    (fun h => has (hφ (by rw [h, hs])))
    (by
      rintro _ hx
      rw [← hKc] at hx
      obtain ⟨x, hx, rfl⟩ := hx
      rw [← map_mul, ← map_mul, haK x hx])
  rw [← hrange] at hcH
  obtain ⟨c, rfl⟩ := hcH
  refine ⟨c, hφ (by rw [map_pow, hc3, map_one]), hφ (by rw [map_mul, map_mul, hs]; exact hcr),
    fun h => hca ?_⟩
  rw [← map_mul, ← map_mul, h]

theorem e4MoveW_PSp
    {M : Type} [Group M] [Finite M] (hM : CFSG.Blueprint.LieModel M .PSp 3 2 1) : E4MoveW M := by
  obtain ⟨e⟩ := CFSG.EvenSmallLie.Sp6.nonempty_mulEquiv_co3X36 hM
  exact e4MoveW_of_model CFSG.Sporadic.Schreier.Co3.co3X36 E4Sp6.K0
    CFSG.EvenSmallLie.Sp6.sp6Rep2
    (fun K s hq hinv htw => TwinThmE.exists_emb_of_ident e
      (fun K s hd => E4Sp6.ident_ambient hd) hq hinv htw)
    (fun sc hsc => E4Sp6.eq_rep_of_isUniqueInvolution hsc) E4Sp6.sp6_move

theorem e4MoveW_POmegaPlus
    {M : Type} [Group M] [Finite M] (hM : CFSG.Blueprint.LieModel M .POmegaPlus 4 2 1) :
    E4MoveW M := by
  obtain ⟨e⟩ := CFSG.EvenSmallLie.OmegaEight.nonempty_mulEquiv_omegaT hM
  exact e4MoveW_of_model CFSG.EvenSmallLie.OmegaEight.omegaT E4O8.K0
    (CFSG.EvenSmallLie.OmegaEight.mainPerm 0)
    (fun K s hq hinv htw => TwinThmE.exists_emb_of_ident e
      (fun K s hd => E4O8.ident_omega hd) hq hinv htw)
    (fun sc hsc => E4O8.eq_x0_of_isUniqueInvolution hsc) E4O8.o8_move

theorem e4ModelMove_of_certs :
    E4ModelMove := by
  intro M _ _ hM
  exact hM.elim e4MoveW_PSp e4MoveW_POmegaPlus

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ZSig
