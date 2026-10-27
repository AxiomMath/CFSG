module

public import CFSG.GH74.GLS.Stage4.T2NegDefs
public import CFSG.GH74.GLS.Stage4.T2NegRU3Std
public import CFSG.GH74.GLS.Stage4.T2NegRU3Conj
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk41RQuot

public section

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.GH74.GLS.IVK.Proofs2.Ivk41R CFSG.GH74.GLS.IVK.Proofs2.Ivk41RU3 CFSG.Assembly.LowTwoRank

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup

theorem unitaryFieldData_of_natCard_sq {p n : ℕ} (hp : p.Prime) {F : Type} [Field F] [Finite F]
    (hcard : Nat.card F = (p ^ n) ^ 2) : UnitaryFieldData p n F := by
  have hn : 1 ≤ n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    have h1 : Nat.card F = 1 := by rw [hcard, hn0]; simp
    have := Finite.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial F)
    omega
  exact ⟨hp, hn, by rw [hcard, ← pow_mul, mul_comm]⟩

theorem rgood_hypSU {p n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p n K) (hp2 : p ≠ 2)
    (z : hypSU h 1 1) (X : Subgroup (hypSU h 1 1)) (hz : orderOf z = 2)
    (hXz : X ≤ centralizer ({z} : Set (hypSU h 1 1))) (hXc : Nat.card X = p ^ n) :
    RGood p n z X := by
  obtain ⟨g, hg1, hg2⟩ := rconjU3 h hp2 z X hz hXz hXc
  let ε : hypSU h 1 1 ≃* hypSU h 1 1 := MulAut.conj g
  have hεz : ε z = tzU h := by
    show g * z * g⁻¹ = tzU h
    exact hg1
  have hεX : X.map ε.toMonoidHom = X0U h := hg2
  exact RGood.congr ε.symm ((MulEquiv.symm_apply_eq _).2 hεz.symm)
    (by rw [← hεX]; exact map_map_symm_mulEquiv ε X) (rstdU3 h hp2)

theorem hypScalars_pow_three {p n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p n K)
    {w : hypSU h 1 1} (hw : w ∈ hypScalars h 1 1) : w ^ 3 = 1 := by
  obtain ⟨c, -, hcn, hw⟩ := hw
  apply Subtype.ext
  rw [SubgroupClass.coe_pow, hw, ← map_pow]
  have : c ^ 3 = 1 := hcn
  rw [this, map_one]
  rfl

theorem ivk_4_1_R_U3 : IVK_4_1_R_U3 := by
  intro J _ _ p n hp hp2 hJ z hz X hXz hXp hXc
  have : Fact p.Prime := ⟨hp⟩
  rcases hJ with (⟨h1, -⟩ | ⟨-, F, hF, hFin, hcard, ⟨e⟩⟩) | (⟨h1, -⟩ | ⟨-, F, hF, hFin, hcard, ⟨e⟩⟩)
  · exact absurd h1 (by norm_num)
  · have h := unitaryFieldData_of_natCard_sq hp hcard
    obtain ⟨R, hR⟩ := exists_isHypTransport (r := 1) (ε := 1) h
    exact rgood_transport (e.trans (hypTransport h hR).symm)
      (fun z' X' hz' hXz' _ hXc' => rgood_hypSU h hp2 z' X' hz' hXz' hXc') hz hXz hXp hXc
  · exact absurd h1 (by norm_num)
  · have h := unitaryFieldData_of_natCard_sq hp hcard
    obtain ⟨R, hR⟩ := exists_isHypTransport (r := 1) (ε := 1) h
    have : Finite (hypSU h 1 1) := finite_hypSU h
    have hZ : Nat.Coprime (Nat.card (hypScalars h 1 1)) p := by
      rw [card_hypScalars h (r := 1) (ε := 1) (by norm_num), Nat.coprime_comm,
        hp.coprime_iff_not_dvd]
      exact not_dvd_gcd_pow_add_one h _
    exact rgood_transport (e.trans (hypPSUEquivStatedProj h hR (by norm_num)).symm)
      (fun z' X' hz' hXz' hXp' hXc' =>
        rgood_quotient (S := hypSU h 1 1) (hypScalars h 1 1)
          (normOneScalars_le_center h (hypSU h 1 1) _) hZ (fun w hw => hypScalars_pow_three h hw)
          (fun a X'' ha hXa hXc'' => rgood_hypSU h hp2 a X'' ha hXa hXc'') hz' hXz' hXp' hXc')
      hz hXz hXp hXc

end CFSG.GH74.GLS.IVK.Proofs2
