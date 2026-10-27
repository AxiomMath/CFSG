module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.Classes
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.AlternatingFactsEight
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.ElementaryPerm

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Equiv Subgroup

namespace IsTwoANine

variable {J : Type*} [Group J] (hJ : IsTwoANine J) (e : J ⧸ center J ≃* alternatingGroup (Fin 9))
include hJ

theorem card_comap_proj (F : Subgroup (alternatingGroup (Fin 9))) :
    Nat.card (F.comap (proj e)) = 2 * Nat.card F := by
  have h1 := Subgroup.card_mul_index (F.comap (proj e))
  rw [Subgroup.index_comap_of_surjective F (proj_surjective e), hJ.card_eq] at h1
  have h2 := Subgroup.card_mul_index F
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card (α := Fin 9), Fintype.card_fin] at h2
  have h2' : Nat.card F * F.index = 181440 := by rw [h2]; decide
  have hi : 0 < F.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  refine Nat.eq_of_mul_eq_mul_right hi ?_
  rw [h1, mul_assoc, h2']
  norm_num

variable {E : Subgroup J} (hE2 : ∀ x ∈ E, x ^ 2 = 1)
include hE2

omit hJ in
theorem sq_eq_one_of_mem_map_proj {g : alternatingGroup (Fin 9)} (hg : g ∈ E.map (proj e)) :
    g ^ 2 = 1 := by
  obtain ⟨x, hx, rfl⟩ := hg
  rw [← map_pow, hE2 x hx, map_one]

theorem cycleType_of_mem_map_proj {g : alternatingGroup (Fin 9)} (hg : g ∈ E.map (proj e))
    (hg1 : g ≠ 1) : (g : Perm (Fin 9)).cycleType = {2, 2, 2, 2} := by
  obtain ⟨x, hx, rfl⟩ := hg
  have hx1 : x ≠ 1 := fun h => hg1 (by rw [h, map_one])
  have hxz : x ≠ zbar J := fun h => hg1 (by rw [h]; exact hJ.proj_zbar e)
  exact hJ.cycleType_eq_of_orderOf_eq_two e (orderOf_eq_prime (hE2 x hx) hx1) hxz

omit hJ in
theorem isPGroup_map_proj : IsPGroup 2 (E.map (proj e)) :=
  IsPGroup.map (fun x => ⟨1, Subtype.ext (by rw [pow_one]; exact hE2 x x.2)⟩) (proj e)

theorem card_map_proj_le : Nat.card (E.map (proj e)) ≤ 8 :=
  card_le_eight_of_cycleType (isPGroup_map_proj e hE2) fun _ hg hg1 =>
    hJ.cycleType_of_mem_map_proj e hE2 hg hg1

variable (hE : Nat.card E = 16)
include hE

theorem comap_map_proj_eq : (E.map (proj e)).comap (proj e) = E := by
  have := hJ.finite
  refine (Subgroup.eq_of_le_of_card_ge (Subgroup.le_comap_map _ _) ?_).symm
  rw [hJ.card_comap_proj e, hE]
  have := hJ.card_map_proj_le e hE2
  omega

theorem zbar_mem_of_card_eq : zbar J ∈ E := by
  obtain ⟨e⟩ := hJ.nonempty_mulEquiv
  rw [← hJ.comap_map_proj_eq e hE2 hE, Subgroup.mem_comap, hJ.proj_zbar e]
  exact Subgroup.one_mem _

theorem card_map_proj_eq : Nat.card (E.map (proj e)) = 8 := by
  have h := hJ.card_comap_proj e (E.map (proj e))
  rw [hJ.comap_map_proj_eq e hE2 hE, hE] at h
  omega

theorem existsUnique_forall_apply_eq_of_card_eq :
    ∃! p : Fin 9, ∀ g ∈ E.map (proj e), (g : Perm (Fin 9)) p = p :=
  existsUnique_forall_apply_eq_of_cycleType (hJ.card_map_proj_eq e hE2 hE)
    fun _ hg hg1 => hJ.cycleType_of_mem_map_proj e hE2 hg hg1

theorem existsUnique_mem_map_proj_apply_eq {p : Fin 9}
    (hp : ∀ g ∈ E.map (proj e), (g : Perm (Fin 9)) p = p) {i j : Fin 9} (hi : i ≠ p)
    (hj : j ≠ p) : ∃! g, g ∈ E.map (proj e) ∧ (g : Perm (Fin 9)) i = j :=
  existsUnique_mem_apply_eq_of_cycleType
    (fun _ hg hg1 => hJ.cycleType_of_mem_map_proj e hE2 hg hg1) hp
    (hJ.card_map_proj_eq e hE2 hE) hi hj

theorem centralizer_map_proj_eq :
    Subgroup.centralizer ((E.map (proj e) : Subgroup (alternatingGroup (Fin 9))) :
      Set (alternatingGroup (Fin 9))) = E.map (proj e) :=
  centralizer_eq_self_of_cycleType (fun _ hg => sq_eq_one_of_mem_map_proj e hE2 hg)
    (hJ.card_map_proj_eq e hE2 hE) fun _ hg hg1 => hJ.cycleType_of_mem_map_proj e hE2 hg hg1

theorem mem_map_proj_of_forall_commute {T : Subgroup J} (hET : E ≤ T)
    {c : alternatingGroup (Fin 9)} (hc : ∀ g ∈ T.map (proj e), g * c = c * g) :
    c ∈ E.map (proj e) := by
  rw [← hJ.centralizer_map_proj_eq e hE2 hE]
  exact Subgroup.mem_centralizer_iff.mpr fun g hg => hc g (Subgroup.map_mono hET hg)

theorem map_subtype_center_le {T : Subgroup J} (hET : E ≤ T) :
    (center (T.map (proj e))).map (T.map (proj e)).subtype ≤ E.map (proj e) := by
  rintro _ ⟨c, hc, rfl⟩
  exact hJ.mem_map_proj_of_forall_commute e hE2 hE hET fun g hg =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨g, hg⟩)

theorem exists_le_of_le_of_isPGroup {E' : Subgroup J} (hE2' : ∀ x ∈ E', x ^ 2 = 1)
    (hE' : Nat.card E' = 16) {T : Subgroup J} (hT : IsPGroup 2 T) (hET : E ≤ T) (hE'T : E' ≤ T) :
    ∃ V : Subgroup J, V ≤ E ∧ V ≤ E' ∧ zbar J ∈ V ∧ Nat.card V = 4 := by
  have := hJ.finite
  obtain ⟨e⟩ := hJ.nonempty_mulEquiv
  have hnt : Nontrivial (T.map (proj e)) := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    have := Subgroup.card_le_of_le (Subgroup.map_mono (f := proj e) hET)
    rw [hJ.card_map_proj_eq e hE2 hE] at this
    omega
  have := (hT.map (proj e)).center_nontrivial
  obtain ⟨c, hc1⟩ := exists_ne (1 : center (T.map (proj e)))
  have hmem : ∀ {E₀ : Subgroup J}, (∀ x ∈ E₀, x ^ 2 = 1) → Nat.card E₀ = 16 → E₀ ≤ T →
      ((c : T.map (proj e)) : alternatingGroup (Fin 9)) ∈ E₀.map (proj e) :=
    fun hE₀2 hE₀ hE₀T => hJ.map_subtype_center_le e hE₀2 hE₀ hE₀T ⟨c, c.2, rfl⟩
  have hle : ∀ {E₀ : Subgroup J}, (∀ x ∈ E₀, x ^ 2 = 1) → Nat.card E₀ = 16 → E₀ ≤ T →
      (zpowers ((c : T.map (proj e)) : alternatingGroup (Fin 9))).comap (proj e) ≤ E₀ :=
    fun hE₀2 hE₀ hE₀T => by
      rw [← hJ.comap_map_proj_eq e hE₀2 hE₀]
      exact Subgroup.comap_mono (Subgroup.zpowers_le.mpr (hmem hE₀2 hE₀ hE₀T))
  refine ⟨_, hle hE2 hE hET, hle hE2' hE' hE'T, ?_, ?_⟩
  · rw [Subgroup.mem_comap, hJ.proj_zbar e]
    exact Subgroup.one_mem _
  · have hne : ((c : T.map (proj e)) : alternatingGroup (Fin 9)) ≠ 1 := fun h =>
      hc1 (Subtype.ext (Subtype.ext h))
    rw [hJ.card_comap_proj e, Nat.card_zpowers,
      orderOf_eq_prime (sq_eq_one_of_mem_map_proj e hE2 (hmem hE2 hE hET)) hne]

end IsTwoANine

namespace IsTwoANine

variable {J : Type*} [Group J] (hJ : IsTwoANine J) (e : J ⧸ center J ≃* alternatingGroup (Fin 9))
include hJ

theorem sq_eq_one_of_mem_comap_aNineEZero {x : J} (hx : x ∈ ANineEZero.comap (proj e)) :
    x ^ 2 = 1 := by
  by_cases h1 : proj e x = 1
  · exact hJ.sq_eq_one_of_mem_center ((proj_eq_one_iff e).mp h1)
  · exact hJ.sq_eq_one_of_cycleType_two_two_two_two e (cycleType_of_mem_aNineEZero hx h1)

theorem card_comap_aNineEZero : Nat.card (ANineEZero.comap (proj e)) = 16 := by
  rw [hJ.card_comap_proj e, card_aNineEZero]

end IsTwoANine

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
