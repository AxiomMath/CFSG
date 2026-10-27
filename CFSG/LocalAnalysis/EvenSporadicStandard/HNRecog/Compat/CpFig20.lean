module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpFig20Uniq
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpFig20Prod

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G G' : Type} [Group G] [Group G'] {a z : G} {a' z' : G'} {α : G → G'}
  {F : Fam a α} {θ : G → G'}

theorem theta_clique_two (hC : Cover4A) (hW : Wit20) (hG : Gen2A) (h : F5Std a z)
    (h' : F5Std a' z') (hα : IsIsoOn (Gx a) (Gx a') α) (hθ : IsTheta a F θ) {x y b : G}
    (hx : x ∈ orb3A a a ∪ orb6A a a) (hb : b ∈ orb2A a a ∩ orb2A a x) (hy : y ∈ orb2A a x)
    (hyb : y ∈ orb4A a z b) : IsClique3 a' (θ x) (θ y) (θ (x * y)) := by
  have hxA : IsConj a x := by
    rcases hx with h3 | h6
    exacts [h3.1, h6.1]
  have hbA : IsConj a b := hb.1.1
  have hyA : IsConj a y := hy.1
  have hbxG : b ∈ Gx x := h.mem_Gx_of_orb2A hxA hb.2
  have hxb : x * b = b * x := mem_Gx.1 hbxG
  have hxy : x * y = y * x := h.mul_comm (Or.inl hxA) (Or.inl hyA) (Or.inl hy.2)
  have hbb : b * b = 1 := cp_mul_self_eq_one h (Or.inl hbA)
  have hxx : x * x = 1 := cp_mul_self_eq_one h (Or.inl hxA)
  have hyy : y * y = 1 := cp_mul_self_eq_one h (Or.inl hyA)
  have hcxb : Commute x b := hxb
  have hcxy : Commute x y := hxy
  have hxInv : x ∈ InvIn (Gx b) := ⟨mem_Gx.2 hxb.symm, h.orderOf_eq_two (Or.inl hxA)⟩
  obtain ⟨hyyb, hybxy, hybsq⟩ := cp_dihedral_yb hbb hyy (cp_mul_self_eq_one h (Or.inr hyb.2))
  obtain ⟨yb, hyb_def⟩ : ∃ yb, b * y * b⁻¹ = yb := ⟨_, rfl⟩
  rw [hyb_def] at hyyb hybxy hybsq
  have hybA : IsConj a yb := hyb_def ▸ cp_isConj_conj hyA b
  have hcxyb : Commute x yb := by
    rw [← hyb_def]
    exact (hcxb.mul_right hcxy).mul_right hcxb.inv_right
  have hconj : b * (x * y) * b⁻¹ = x * yb := by
    rw [← hyb_def]
    calc b * (x * y) * b⁻¹ = (b * x) * (y * b⁻¹) := by group
      _ = (x * b) * (y * b⁻¹) := by rw [hxb]
      _ = x * (b * y * b⁻¹) := by group
  have hxyb2A : IsConj a (x * yb) := by rw [← hconj]; exact cp_isConj_conj hy.2 b
  have hxGx : x ∈ Gx x := self_mem_Gx x
  have hyGx : y ∈ Gx x := mem_Gx.2 hxy
  have hxyGx : x * y ∈ Gx x := (Gx x).mul_mem hxGx hyGx
  have hybGx : yb ∈ Gx x := mem_Gx.2 hcxyb
  have hxybGx : x * yb ∈ Gx x := (Gx x).mul_mem hxGx hybGx
  have hxxy : x * (x * y) = y := by rw [← mul_assoc, hxx, one_mul]
  have hxy2A : x * y ∈ orb2A a x := ⟨hy.2, by rw [hxxy]; exact hyA⟩
  have hbxy : (b * (x * y)) ^ 2 = (b * y) ^ 2 := by
    have e : b * (x * y) = x * (b * y) := by
      calc b * (x * y) = (b * x) * y := by rw [mul_assoc]
        _ = (x * b) * y := by rw [hxb]
        _ = x * (b * y) := by rw [mul_assoc]
    rw [e, (hcxb.mul_right hcxy).mul_pow, pow_two x, hxx, one_mul]
  have hxy4A : x * y ∈ orb4A a z b := ⟨hy.2, by rw [hbxy]; exact hyb.2⟩
  obtain ⟨ℬ, hA⟩ := cp_fig20_family hC hW h h' hα hθ hb.1 hxA hb.2 hy hyb
  obtain ⟨ℬ', hB'⟩ := cp_fig20_family hC hW h h' hα hθ hb.1 hxA hb.2 hxy2A hxy4A
  have hB := cp_fig20_swap hbb hbxG ℬ ℬ' (cp_member_unique hG h hbA hxA hb.2 ℬ ℬ') hxyGx hB'
  rw [hyb_def] at hA
  rw [hconj] at hB
  have hTx : ℬ.app x x = θ x := cp_fam_apply_x h hθ hxA hb.1 hb.2 ℬ
  have hT : ∀ {u v : G}, u ∈ Gx x → v ∈ Gx x → IsConj a (u * v) →
      IsConj a' (ℬ.app x u * ℬ.app x v) := fun hu hv huv =>
    cp_fam_prod_typed h h' hα hθ hb.1 ℬ hxInv hu hv huv
  have hbF : F5Std b z := h.of_isConj hbA (IsConj.refl z)
  have hyb' : y ∈ orb4A b z b := ⟨hbA.symm.trans hyA, hyb.2⟩
  have hxbA : IsConj a (b * x) := by rw [← hxb]; exact hb.2.2
  have hx2A : x ∈ orb2A b b ∩ orb2A b y :=
    ⟨⟨hbA.symm.trans hxA, hbA.symm.trans hxbA⟩,
      hbA.symm.trans hxA, hbA.symm.trans ((cp_isConj_mul_comm a x y).1 hy.2)⟩
  have hzx : IsConj a ((b * y) ^ 2 * x) := hbA.trans (hbF.loc.lines.self.fig14_a y hyb' x hx2A).1
  have hxz : x * (b * y) ^ 2 = (b * y) ^ 2 * x := ((hcxb.mul_right hcxy).pow_right 2).eq
  have hxzA : IsConj a (x * (b * y) ^ 2) := by rw [hxz]; exact hzx
  have P1 : IsConj a' (θ x * θ y) := by
    rw [← hTx]
    rcases hA with e | e <;> rw [e]
    · exact hT hxGx hyGx hy.2
    · exact hT hxGx hybGx hxyb2A
  have P2 : IsConj a' (θ x * θ (x * y)) := by
    rw [← hTx]
    rcases hB with e | e <;> rw [e]
    · exact hT hxGx hxyGx hxy2A.2
    · refine hT hxGx hxybGx ?_
      rw [← mul_assoc, hxx, one_mul]
      exact hybA
  have P3 : IsConj a' (θ y * θ (x * y)) := by
    rcases hA with e | e <;> rcases hB with f | f <;> rw [e, f]
    · refine hT hyGx hxyGx ?_
      rw [hcxy.symm.left_comm y, hyy, mul_one]
      exact hxA
    · refine hT hyGx hxybGx ?_
      rw [hcxy.symm.left_comm yb, hyyb]
      exact hxzA
    · refine hT hybGx hxyGx ?_
      rw [hcxyb.symm.left_comm y, hybxy]
      exact hxzA
    · refine hT hybGx hxybGx ?_
      rw [hcxyb.symm.left_comm yb, hybsq, mul_one]
      exact hxA
  have hθxA : IsConj a' (θ x) := hθ.typed h h' hα hxA
  have hθyA : IsConj a' (θ y) := hθ.typed h h' hα hyA
  exact ⟨⟨cp_ne_of_isConj_mul h' hθxA P1, P1⟩, ⟨cp_ne_of_isConj_mul h' hθxA P2, P2⟩,
    ⟨cp_ne_of_isConj_mul h' hθyA P3, P3⟩⟩

end CFSG.EvenSporadicStandard.HNRecog.Section4
