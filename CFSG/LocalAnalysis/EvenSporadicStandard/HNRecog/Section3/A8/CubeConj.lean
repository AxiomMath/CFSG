module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.A8.Perm
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.A8.Decomp
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.A8.CubeEnum
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem exists_t_of_cube {G : Type} [Group G] {a z : G} (hF3 : Fusion3Facts a z) {E : Subgroup G}
    (hE : IsElemTwo 3 E) {b : G} (haE : a ∈ E) (hbE : b ∈ E) (hab : a ≠ b) (hb : b ∈ orb2A a a) :
    ∃ t ∈ derivedOf (Gxy a b), t ^ 2 = 1 ∧ t ≠ 1 ∧ E = Subgroup.closure ({a, b, t} : Set G) := by
  have ha2 : a ^ 2 = 1 := hE.1.2 a haE
  have hb2 : b ^ 2 = 1 := hE.1.2 b hbE
  have hcommE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have habcomm : a * b = b * a := hcommE a haE b hbE
  have ha1 : a ≠ 1 := by
    intro haeq
    have hb1 : b = 1 := isConj_one_right.mp (haeq ▸ hb.1)
    exact hab (haeq.trans hb1.symm)
  have hb1 : b ≠ 1 := by
    intro hbeq
    have haeq : a = 1 := isConj_one_left.mp (hbeq ▸ hb.1)
    exact hab (haeq.trans hbeq.symm)
  obtain ⟨t₀, ht₀E, ht₀not⟩ := exists_mem_not_mem_closure_pair hE haE hbE ha1 hb1 hab
  have ht₀G : t₀ ∈ Gxy a b := by
    rw [mem_Gxy]
    exact ⟨mem_Gx.mpr (hcommE a haE t₀ ht₀E), mem_Gx.mpr (hcommE b hbE t₀ ht₀E)⟩
  have hX : IsShapeTwoTwoTimesA8 ↥(Gxy a b) := hF3.shape_2A b hb
  obtain ⟨u, hu, s, hs, ht₀eq⟩ :=
    exists_mul_eq_of_isShapeTwoTwoTimesA8 hX ha2 hb2 habcomm ha1 hb1 hab t₀ ht₀G
  have hclE : Subgroup.closure ({a, b} : Set G) ≤ E := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact haE
    · exact hbE
  have hsE : s ∈ E := by
    have hs_eq : s = u⁻¹ * t₀ := by rw [ht₀eq, inv_mul_cancel_left]
    rw [hs_eq]
    exact E.mul_mem (E.inv_mem (hclE hu)) ht₀E
  have hsnot : s ∉ Subgroup.closure ({a, b} : Set G) := by
    intro hscl
    exact ht₀not (by rw [ht₀eq]; exact (Subgroup.closure ({a, b} : Set G)).mul_mem hu hscl)
  have hs1 : s ≠ 1 := by
    intro hseq
    apply ht₀not
    rw [ht₀eq, hseq, mul_one]
    exact hu
  exact ⟨s, hs, hE.1.2 s hsE, hs1,
    (closure_three_eq_of_isElemTwo hE haE hbE hsE ha1 hb1 hab hsnot).symm⟩

theorem cube_conj_of_fusion3 {G : Type} [Group G] {a z : G} (hF3 : Fusion3Facts a z) :
    ∀ E : Subgroup G, IsElemTwo 3 E →
      (∃ a' ∈ E, ∃ b' ∈ E, a' ≠ b' ∧ IsConj a a' ∧ IsConj a b' ∧ IsConj a (a' * b')) →
        ∃ g b t : G, b ∈ orb2A a a ∧ t ∈ derivedOf (Gxy a b) ∧ t ^ 2 = 1 ∧ t ≠ 1 ∧
          E.map (MulAut.conj g).toMonoidHom = Subgroup.closure {a, b, t} := by
  intro E hE hdata
  obtain ⟨a', ha'E, b', hb'E, hne', haa', hab', habprod⟩ := hdata
  obtain ⟨c, hc⟩ := isConj_iff.mp haa'
  let g : G := c⁻¹
  let b : G := g * b' * g⁻¹
  have hga : g * a' * g⁻¹ = a := by
    dsimp only [g]
    rw [← hc]
    group
  have hgb : g * b' * g⁻¹ = b := rfl
  have hf : Function.Injective (MulAut.conj g).toMonoidHom :=
    fun x y h => (MulAut.conj g).injective h
  have hE' : IsElemTwo 3 (E.map (MulAut.conj g).toMonoidHom) :=
    isElemTwo_map (MulAut.conj g).toMonoidHom hf hE
  have haE' : a ∈ E.map (MulAut.conj g).toMonoidHom := by
    refine Subgroup.mem_map.mpr ⟨a', ha'E, ?_⟩
    simpa using hga
  have hbE' : b ∈ E.map (MulAut.conj g).toMonoidHom := by
    refine Subgroup.mem_map.mpr ⟨b', hb'E, ?_⟩
    simpa using hgb
  have hne : a ≠ b := by
    intro hab_eq
    apply hne'
    have h : g * a' * g⁻¹ = g * b' * g⁻¹ := hga.trans (hab_eq.trans hgb.symm)
    exact mul_left_cancel (mul_right_cancel h)
  have hb_conj : IsConj b' b := isConj_iff.mpr ⟨g, hgb⟩
  have hab_mul : a * b = g * (a' * b') * g⁻¹ := by
    rw [← hga, ← hgb]
    group
  have hprod_conj : IsConj (a' * b') (a * b) := isConj_iff.mpr ⟨g, hab_mul.symm⟩
  have hb2A : b ∈ orb2A a a := ⟨hab'.trans hb_conj, habprod.trans hprod_conj⟩
  obtain ⟨t, htmem, ht2, ht1, hEclosure⟩ := exists_t_of_cube hF3 hE' haE' hbE' hne hb2A
  exact ⟨g, b, t, hb2A, htmem, ht2, ht1, hEclosure⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
