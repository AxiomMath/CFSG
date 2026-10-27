module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.A9LocalPerm
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.AGLEmbedding.A9Local

open Equiv CFSG.Open

theorem card_perm_pt : Nat.card (Perm Pt) = 362880 := by
  rw [Nat.card_perm]
  simp [Nat.card_eq_fintype_card]
  decide

theorem eq_sylowT_of_le {Q : Subgroup (Perm Pt)} (hQ : IsPGroup 3 Q) (h : sylowT ≤ Q) :
    Q = sylowT := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  have hdvd : Nat.card Q ∣ Nat.card (Perm Pt) := Subgroup.card_subgroup_dvd_card Q
  rw [hn, card_perm_pt] at hdvd
  have hn4 : n ≤ 4 := by
    by_contra hlt
    have h5 : 3 ^ 5 ∣ 362880 := (pow_dvd_pow 3 (not_le.1 hlt)).trans hdvd
    norm_num at h5
  have hle : Nat.card Q ≤ Nat.card sylowT := by
    rw [hn, card_sylowT]
    calc 3 ^ n ≤ 3 ^ 4 := Nat.pow_le_pow_right (by norm_num) hn4
      _ = 81 := by norm_num
  exact (Subgroup.eq_of_le_of_card_ge h hle).symm

theorem exists_conj_le_sylowT {P : Subgroup (Perm Pt)} (hP : IsPGroup 3 P) :
    ∃ g : Perm Pt, ∀ x ∈ P, g * x * g⁻¹ ∈ sylowT := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨R, hR⟩ := isPGroup_sylowT.exists_le_sylow
  have hRT : (R : Subgroup (Perm Pt)) = sylowT := eq_sylowT_of_le R.isPGroup' hR
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Perm Pt) Q R
  refine ⟨g, fun x hx => ?_⟩
  have h1 : MulAut.conj g x ∈ ((g • Q : Sylow 3 (Perm Pt)) : Subgroup (Perm Pt)) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul_iff.2 (hQ hx)
  rw [hg, hRT] at h1
  simpa using h1

theorem zmod_three_eq_zero_or_eq_or :
    ∀ l : ZMod 3, l ≠ 0 → ∀ i : ZMod 3, i = 0 ∨ i = l ∨ i = l + l := by
  decide

theorem exists_affPerm_of_mem_sylowT_of_not_mem_baseGroup {x : Perm Pt} (hx : x ∈ sylowT)
    (hxB : x ∉ baseGroup) : ∃ (l : ZMod 3) (f : ZMod 3 → ZMod 3), l ≠ 0 ∧ x = affPerm l f := by
  obtain ⟨l, f, rfl⟩ := hx
  refine ⟨l, f, ?_, rfl⟩
  rintro rfl
  exact hxB (by rw [affPerm_zero_left]; exact shiftPerm_mem_baseGroup f)

theorem eq_one_of_fix_origin_of_commute_affPerm {l : ZMod 3} (hl : l ≠ 0) (g : ZMod 3 → ZMod 3)
    {u : Perm Pt} (hu : u ∈ sylowT) (hcomm : u * affPerm l g = affPerm l g * u)
    (hfix : u (0, 0) = (0, 0)) : u = 1 := by
  obtain ⟨lu, fu, rfl⟩ := hu
  simp only [affPerm_apply, zero_add, Prod.mk.injEq] at hfix
  obtain ⟨rfl, hfu0⟩ := hfix
  have key : ∀ i, fu (i + l) = fu i := fun i => by
    have := congrArg (fun σ : Perm Pt => (σ (i, 0)).2) hcomm
    simp at this
    linear_combination this
  have hconst : ∀ i, fu i = 0 := fun i => by
    have hl0 : fu l = 0 := by rw [← zero_add l, key 0]; exact hfu0
    rcases zmod_three_eq_zero_or_eq_or l hl i with h | h | h
    · rw [h]; exact hfu0
    · rw [h]; exact hl0
    · rw [h, key l]; exact hl0
  rw [← affPerm_one]
  congr 1
  exact funext hconst

theorem card_le_nine_of_not_le_baseGroup {E : Subgroup (Perm Pt)} (hE : E ≤ sylowT)
    (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (h : ¬ E ≤ baseGroup) : Nat.card E ≤ 9 := by
  obtain ⟨x, hxE, hxB⟩ := IsConcreteLE.not_le_iff_exists.1 h
  obtain ⟨l, f, hl, rfl⟩ := exists_affPerm_of_mem_sylowT_of_not_mem_baseGroup (hE hxE) hxB
  have hinj : Function.Injective (fun y : E => (y : Perm Pt) (0, 0)) := by
    intro y y' hyy'
    have hu : (y : Perm Pt)⁻¹ * y' ∈ E := E.mul_mem (E.inv_mem y.2) y'.2
    have hfix : ((y : Perm Pt)⁻¹ * y') (0, 0) = (0, 0) := by
      have hyy'' : (y : Perm Pt) (0, 0) = (y' : Perm Pt) (0, 0) := hyy'
      simp [Perm.mul_apply, ← hyy'']
    have := eq_one_of_fix_origin_of_commute_affPerm hl f (hE hu) (hc _ hu _ hxE) hfix
    exact Subtype.ext (inv_mul_eq_one.1 this)
  calc Nat.card E ≤ Nat.card Pt := Nat.card_le_card_of_injective _ hinj
    _ = 9 := by simp [Nat.card_eq_fintype_card]

theorem mul_comm_of_isElemAbelian {G : Type*} [Group G] {p : ℕ} {E : Subgroup G}
    (hel : IsElemAbelian p E) : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
  congrArg Subtype.val (hel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem card_le_of_le_sylowT {E : Subgroup (Perm Pt)} (hE : E ≤ sylowT)
    (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) : Nat.card E ≤ 3 ^ 3 := by
  by_cases h : E ≤ baseGroup
  · calc Nat.card E ≤ Nat.card baseGroup := Subgroup.card_le_of_le h
      _ = 3 ^ 3 := by rw [card_baseGroup]; norm_num
  · have := card_le_nine_of_not_le_baseGroup hE hc h
    omega

theorem eq_baseGroup_of_le_sylowT {E : Subgroup (Perm Pt)} (hE : E ≤ sylowT)
    (hel : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 3) : E = baseGroup := by
  by_cases h : E ≤ baseGroup
  · refine Subgroup.eq_of_le_of_card_ge h ?_
    rw [card_baseGroup, hcard]
    norm_num
  · have := card_le_nine_of_not_le_baseGroup hE (mul_comm_of_isElemAbelian hel) h
    rw [hcard] at this
    norm_num at this

theorem isPGroup_three_of_isElemAbelian {E : Subgroup (Perm Pt)} (hel : IsElemAbelian 3 E) :
    IsPGroup 3 E := CFSG.Open.IsElemAbelian.isPGroup hel

theorem exists_conj_isElemAbelian_le_sylowT {E : Subgroup (Perm Pt)} (hel : IsElemAbelian 3 E) :
    ∃ g : Perm Pt, E.map (MulAut.conj g).toMonoidHom ≤ sylowT ∧
      IsElemAbelian 3 (E.map (MulAut.conj g).toMonoidHom) ∧
      Nat.card (E.map (MulAut.conj g).toMonoidHom) = Nat.card E := by
  obtain ⟨g, hg⟩ := exists_conj_le_sylowT (isPGroup_three_of_isElemAbelian hel)
  refine ⟨g, ?_, CFSG.SectionRank.isElemAbelian_map hel _,
    Subgroup.card_map_of_injective (MulAut.conj g).injective⟩
  rintro _ ⟨x, hx, rfl⟩
  exact hg x hx

theorem exists_conj_eq_baseGroup {E : Subgroup (Perm Pt)} (hel : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 3) :
    ∃ g : Perm Pt, E.map (MulAut.conj g).toMonoidHom = baseGroup := by
  obtain ⟨g, hle, hel', hcard'⟩ := exists_conj_isElemAbelian_le_sylowT hel
  exact ⟨g, eq_baseGroup_of_le_sylowT hle hel' (hcard'.trans hcard)⟩

theorem card_le_of_isElemAbelian {E : Subgroup (Perm Pt)} (hel : IsElemAbelian 3 E) :
    Nat.card E ≤ 3 ^ 3 := by
  obtain ⟨g, hle, hel', hcard'⟩ := exists_conj_isElemAbelian_le_sylowT hel
  rw [← hcard']
  exact card_le_of_le_sylowT hle (mul_comm_of_isElemAbelian hel')

theorem pRank_top_le_three : CFSG.Open.pRank 3 (⊤ : Subgroup (Perm Pt)) ≤ 3 :=
  CFSG.SectionRank.pRank_le (by norm_num) fun _ _ hel => card_le_of_isElemAbelian hel

end CFSG.AGLEmbedding.A9Local
