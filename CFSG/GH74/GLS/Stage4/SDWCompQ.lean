module

public import CFSG.GroupTheory.QuasiDihedralFusion.Defs
import CFSG.GroupTheory.QuasiDihedralFusion.Basic
import CFSG.GroupTheory.QuasiDihedralFusion.Structure

public section

namespace CFSG.GH74.GLS.Stage4.Rest

private theorem sdwQ_aux_eq_a_of_orderOf_eq_two {n : ℕ} [NeZero n] {c : QuaternionGroup n}
    (hc : orderOf c = 2) : c = QuaternionGroup.a n := by
  cases c with
  | a i =>
    have h2 : QuaternionGroup.a (i + i) = QuaternionGroup.a (0 : ZMod (2 * n)) := by
      rw [← QuaternionGroup.a_mul_a, ← QuaternionGroup.one_def, ← sq, ← hc, pow_orderOf_eq_one]
    have hii : i + i = 0 := QuaternionGroup.a.inj h2
    have hi0 : i ≠ 0 := by
      rintro rfl
      rw [← QuaternionGroup.one_def, orderOf_one] at hc
      exact absurd hc (by norm_num)
    have hval := ZMod.val_add i i
    rw [hii, ZMod.val_zero] at hval
    have hpos : i.val ≠ 0 := fun h => hi0 ((ZMod.val_eq_zero i).mp h)
    have hn : i.val = n := by
      have h1 : 2 * n ∣ 2 * i.val := by
        rw [two_mul i.val]
        exact Nat.dvd_of_mod_eq_zero hval.symm
      exact Nat.eq_of_dvd_of_lt_two_mul hpos (Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1)
        (ZMod.val_lt i)
    rw [← ZMod.natCast_zmod_val i, hn]
  | xa i =>
    rw [QuaternionGroup.orderOf_xa] at hc
    exact absurd hc (by norm_num)

private theorem sdwQ_aux_isPGroup_closure_pair {G : Type*} [Group G] {a b : G}
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : Commute a b) :
    IsPGroup 2 (Subgroup.closure ({a, b} : Set G)) := by
  have hcomm : ({a, b} : Set G).Pairwise Commute := by
    intro x hx y hy hxy
    rcases hx with rfl | rfl
    · rcases hy with rfl | rfl
      · exact absurd rfl hxy
      · exact hab
    · rcases hy with rfl | rfl
      · exact hab.symm
      · exact absurd rfl hxy
  have hcommU : IsMulCommutative (Subgroup.closure ({a, b} : Set G)) :=
    Subgroup.isMulCommutative_closure hcomm
  have hsq : ∀ x ∈ Subgroup.closure ({a, b} : Set G), x ^ 2 = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · rw [← ha]; exact pow_orderOf_eq_one _
      · rw [← hb]; exact pow_orderOf_eq_one _
    | one => exact one_pow 2
    | mul x y hx hy ihx ihy =>
      have hxy : Commute x y :=
        congrArg Subtype.val (isMulCommutative_iff.mp hcommU ⟨x, hx⟩ ⟨y, hy⟩)
      rw [hxy.mul_pow, ihx, ihy, one_mul]
    | inv x hx ih => rw [inv_pow, ih, inv_one]
  intro g
  exact ⟨1, Subtype.ext (by simpa using hsq g g.2)⟩

theorem sdw_not_klein_four_in_Q {X : Type} [Group X] [Finite X] {R : Sylow 2 X} {K₀ : Subgroup X}
    (h : CFSG.QuasiDihedralFusion.IsQGroupData R K₀) {u v : X} (hu : u ∈ K₀) (hv : v ∈ K₀)
    (hu2 : orderOf u = 2) (hv2 : orderOf v = 2) (huv : u * v = v * u) (hne : u ≠ v) : False := by
  have : K₀.Normal := h.normal
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, -, ⟨eY⟩⟩ := h.quaternion.exists_quaternion_equiv
  set u' : K₀ := ⟨u, hu⟩ with hu'
  set v' : K₀ := ⟨v, hv⟩ with hv'
  have hu'2 : orderOf u' = 2 := by rw [hu', Subgroup.orderOf_mk]; exact hu2
  have hv'2 : orderOf v' = 2 := by rw [hv', Subgroup.orderOf_mk]; exact hv2
  obtain ⟨P, hP⟩ := (sdwQ_aux_isPGroup_closure_pair hu'2 hv'2 (Subtype.ext huv)).exists_le_sylow
  have hu'P : u' ∈ (P : Subgroup K₀) := hP (Subgroup.subset_closure (Set.mem_insert _ _))
  have hv'P : v' ∈ (P : Subgroup K₀) :=
    hP (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  obtain ⟨eP⟩ := CFSG.QuasiDihedralFusion.nonempty_sylow_equiv_inf R K₀ P
  let e : P ≃* QuaternionGroup (2 ^ k) := eP.trans eY
  have : NeZero (2 ^ k) := ⟨by positivity⟩
  have hinv : ∀ (c : K₀) (hc : c ∈ (P : Subgroup K₀)), orderOf c = 2 →
      e ⟨c, hc⟩ = QuaternionGroup.a (2 ^ k : ℕ) := by
    intro c hc hc2
    apply sdwQ_aux_eq_a_of_orderOf_eq_two
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact hc2
  have h1 := (hinv u' hu'P hu'2).trans (hinv v' hv'P hv'2).symm
  exact hne (congrArg (fun c : (P : Subgroup K₀) => ((c : K₀) : X)) (e.injective h1))

end CFSG.GH74.GLS.Stage4.Rest
