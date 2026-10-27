module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.A15LocalPerm

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.AGLEmbedding.A15Local

open Equiv CFSG.Open

theorem card_perm_pt : Nat.card (Perm Pt) = 1307674368000 := by
  rw [Nat.card_perm]
  simp [Nat.card_eq_fintype_card, Nat.factorial]

theorem not_pow_five_four_dvd : ¬ 5 ^ 4 ∣ Nat.card (Perm Pt) := by
  rw [card_perm_pt]
  norm_num

theorem eq_sylowT_of_le {Q : Subgroup (Perm Pt)} (hQ : IsPGroup 5 Q) (h : sylowT ≤ Q) :
    Q = sylowT := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  have hdvd : Nat.card Q ∣ Nat.card (Perm Pt) := Subgroup.card_subgroup_dvd_card Q
  rw [hn] at hdvd
  have hn3 : n ≤ 3 := by
    by_contra hlt
    exact not_pow_five_four_dvd ((pow_dvd_pow 5 (not_le.1 hlt)).trans hdvd)
  have hle : Nat.card Q ≤ Nat.card sylowT := by
    rw [hn, card_sylowT]
    exact Nat.pow_le_pow_right (by norm_num) hn3
  exact (Subgroup.eq_of_le_of_card_ge h hle).symm

theorem exists_conj_le_sylowT {P : Subgroup (Perm Pt)} (hP : IsPGroup 5 P) :
    ∃ g : Perm Pt, ∀ x ∈ P, g * x * g⁻¹ ∈ sylowT := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨R, hR⟩ := isPGroup_sylowT.exists_le_sylow
  have hRT : (R : Subgroup (Perm Pt)) = sylowT := eq_sylowT_of_le R.isPGroup' hR
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Perm Pt) Q R
  refine ⟨g, fun x hx => ?_⟩
  have h1 : MulAut.conj g x ∈ ((g • Q : Sylow 5 (Perm Pt)) : Subgroup (Perm Pt)) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul_iff.2 (hQ hx)
  rw [hg, hRT] at h1
  simpa using h1

theorem exists_conj_eq_sylowT {P : Subgroup (Perm Pt)} (hP : IsPGroup 5 P)
    (hcard : Nat.card P = 5 ^ 3) :
    ∃ g : Perm Pt, P.map (MulAut.conj g).toMonoidHom = sylowT := by
  obtain ⟨g, hg⟩ := exists_conj_le_sylowT hP
  refine ⟨g, Subgroup.eq_of_le_of_card_ge ?_ ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hg x hx
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard, card_sylowT]

end CFSG.AGLEmbedding.A15Local
