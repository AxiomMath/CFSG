module

public import CFSG.ClassicalInvolution.Q3.TL4S289GenD2
public import CFSG.ClassicalInvolution.Q3.TL4S289GenCS4
public import CFSG.ClassicalInvolution.Q3.TL4StarSecSU4
public import CFSG.ClassicalInvolution.Q3.Q3AM289S4LSU03

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.ClassicalInvolution.Q3.Q3PP (F9 card_F9 two_ne_zero_F9)
open CFSG.ClassicalInvolution.Q3.Q3AM (pair01 pair02 pair12 uElt uElt_mul_self uElt_comm
  uElt_mem_LcU zEltU_pair02_mul_pair01 centralizer_pair01_sup_pair02)

namespace S289G


theorem starFrameGenAll_of_su4 {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}
    (hR : TypeRFam 3 Φ) (h : SecIdQ8Shape (CompData.model .PSU 4) Φ)
    (h284 : ∀ M ∈ Φ, ∀ N ∈ omegaNbr Φ M, ∀ m n : X, IsUniqueInvolution M m →
      IsUniqueInvolution N n → m * n ∈ Subgroup.center X) :
    ∀ L ∈ Φ, StarFrameGenAll Φ L := by
  obtain ⟨φ, hφs, hk, hfund⟩ := h
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSU 4 3 1 :=
    ⟨Nat.prime_three, le_rfl, by norm_num, by decide⟩
  obtain ⟨e, he⟩ := RouteD.psu_model_equiv (p := 3) (f := 1) (by norm_num) hadm
  set ψ : Su F9 3 1 4 →* X := φ.comp e.symm.toMonoidHom with hψ
  have hs : Function.Surjective ψ := hφs.comp e.symm.surjective
  have hker : ψ.ker ≤ Subgroup.center (Su F9 3 1 4) := by
    intro x hx
    have h1 : e.symm x ∈ φ.ker := hx
    have h2 := Subgroup.mem_map_of_mem (e : (CompData.model .PSU 4).G →* Su F9 3 1 4) (hk h1)
    rw [Subgroup.map_center_eq e] at h2
    simpa using h2
  have hfund' : ∀ L ∈ Φ, ∃ R ∈ longRootSetU (K := F9) (p := 3) (f := 1) (show 2 ≤ 4 by norm_num),
      IsSylow2In L (R.map ψ) := by
    intro L hL
    obtain ⟨R, hR', hLR⟩ := hfund L hL
    refine ⟨R.map e.toMonoidHom, (he R).mp hR', ?_⟩
    have hmap : (R.map e.toMonoidHom).map ψ = R.map φ := by
      rw [Subgroup.map_map]
      congr 1
      ext x
      simp [hψ]
    rw [hmap]
    exact hLR
  obtain ⟨i, hi, hσi⟩ := Q3MFOU4.exists_iota
  have : Group.IsPerfect (Su F9 3 1 4) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_SUid
      (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution card_F9) (by norm_num)
      (fun h => absurd h (by norm_num))
  have hainv : (zEltU F9 3 1 pair01)⁻¹ = zEltU F9 3 1 pair01 :=
    inv_eq_of_mul_eq_one_right (zEltU_mul_self pair01)
  refine starFrameGenAll_of_kframe hs hker
    (by rw [← commutator_def]; exact Group.IsPerfect.commutator_eq_top) hfund'
    (fun R hR' R' hR'' => Q3AM.exists_conj_map_longRoot ψ hR' hR'')
    (LcU_mem_longRootSetU two_ne_zero_F9 _ pair01) (LcU_mem_longRootSetU two_ne_zero_F9 _ pair02)
    (isUniqueInvolution_LcU card_F9 (by norm_num) (by norm_num) pair01)
    (isUniqueInvolution_LcU card_F9 (by norm_num) (by norm_num) pair02)
    (zEltU_not_mem_center pair01) (zEltU_not_mem_center pair02) (uElt_mem_LcU hi hσi)
    (orderOf_eq_four_of_mul_self (uElt_mul_self hi hσi)) (uElt_mul_self hi hσi)
    (uElt_comm hi hσi).symm ?_ ?_ hR h284
  · rw [hainv, zEltU_pair02_mul_pair01]
    exact zEltU_not_mem_center pair12
  · rw [centralizer_pair01_sup_pair02, top_sup_eq]

theorem secIdStarGenS4_proved : SecIdStarGenS4 := by
  intro X _ _ Φ hR _ _ _ _ h h284
  rcases h with h | h | h
  · exact starFrameGenAll_of_su4 hR h h284
  · exact starFrameGenAll_of_pkg modelPkg_odd3 hR h h284
  · exact starFrameGenAll_of_pkg modelPkg_minus4 hR h h284

end S289G

end CFSG.ClassicalInvolution.Q3.TL4
