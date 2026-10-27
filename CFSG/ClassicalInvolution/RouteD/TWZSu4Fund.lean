module

public import CFSG.ClassicalInvolution.RouteD.TWZSu4Planes
public import CFSG.ClassicalInvolution.RouteD.TypeULocal

public section

namespace CFSG.ClassicalInvolution.RouteD.TWZ

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.RouteD

section Fund

variable {p : ℕ} [Fact p.Prime]

theorem lower_fund_psu4 (hp2 : p ≠ 2) {e : ℕ} (hq : 5 ≤ p ^ e) :
    (p ^ e) ^ 2 * ((p ^ e) ^ 2 + 1) <
      (CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .PSU
        (CFSG.ClassicalInvolution.Generic.modelUniv .PSU 4 p e Fact.out).D).ncard := by
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h
      simp at hq
    · exact h
  have hadm : StatedLieAdmissible .PSU 4 p e :=
    ⟨Fact.out, he, by norm_num, fun h => by
      have : (4 : ℕ) = 3 := congrArg Prod.fst h
      omega⟩
  have : NeZero (2 * e) := ⟨by omega⟩
  have hK : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul p e he
  obtain ⟨φ, hφ⟩ := psu_model_equiv hp2 hadm
  have hfin : Finite (CFSG.ClassicalInvolution.Generic.modelUniv .PSU 4 p e Fact.out).K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv hp2 Fact.out trivial hadm
  have hsub : longRootSetU (K := GaloisField p (2 * e)) (p := p) (f := e)
      (show 2 ≤ 4 by norm_num) ⊆
      (fun R => R.map φ.toMonoidHom) ''
        (CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .PSU
          (CFSG.ClassicalInvolution.Generic.modelUniv .PSU 4 p e Fact.out).D) := by
    intro L hL
    have hid : (L.map φ.symm.toMonoidHom).map φ.toMonoidHom = L := by
      rw [Subgroup.map_map]
      have : φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id _ := by
        ext x
        simp
      rw [this, Subgroup.map_id]
    exact ⟨L.map φ.symm.toMonoidHom, (hφ _).mpr (by rw [hid]; exact hL), hid⟩
  have h1 := card_longRootSetU_ge (K := GaloisField p (2 * e)) (p := p) (f := e) hK hp2
  have h2 : Set.ncard (longRootSetU (K := GaloisField p (2 * e)) (p := p) (f := e)
      (show 2 ≤ 4 by norm_num)) ≤ (CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .PSU
        (CFSG.ClassicalInvolution.Generic.modelUniv .PSU 4 p e Fact.out).D).ncard :=
    (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_image_le (Set.toFinite _))
  have hq1 : 1 ≤ (p ^ e) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h3 : (p ^ e) ^ 2 * ((p ^ e) ^ 2 + 1) < 2 * ((p ^ e) ^ 2 - 1) * (p ^ e) ^ 2 := by
    have h4 : 5 * 5 ≤ (p ^ e) * (p ^ e) := Nat.mul_le_mul hq hq
    zify [hq1]
    nlinarith [sq_nonneg (((p ^ e : ℕ) : ℤ) ^ 2)]
  omega

end Fund

end CFSG.ClassicalInvolution.RouteD.TWZ
