module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888XSf
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888XSp
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888XS0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888XS1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888E4b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888E5b

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {X : Type} [Group X] {V : Subgroup X} {W : Fin 4 → Subgroup X}

private lemma s888_mem_centralizer_of_conj_eq {F : Subgroup X} {x : X}
    (h : ∀ u ∈ F, u * x * u⁻¹ = x) : x ∈ centralizer (F : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have h' := h u hu
  calc u * x = (u * x * u⁻¹) * u := by group
    _ = x * u := by rw [h']

private lemma s888_exists_two_ne_one {A : Subgroup X} (hA : Nat.card A = 4) :
    ∃ x y : X, x ∈ A ∧ y ∈ A ∧ x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y := by
  classical
  haveI : Finite A := Nat.finite_of_card_ne_zero (by rw [hA]; decide)
  haveI : Fintype A := Fintype.ofFinite A
  have hcard : Fintype.card A = 4 := by rw [← Nat.card_eq_fintype_card, hA]
  let s : Finset A := (Finset.univ : Finset A).erase 1
  have hs : s.card = 3 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ 1), Finset.card_univ, hcard]
  have h1 : 1 < s.card := by omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h1
  have ha1 : (a : X) ≠ 1 := by simpa using (Finset.mem_erase.mp ha).1
  have hb1 : (b : X) ≠ 1 := by simpa using (Finset.mem_erase.mp hb).1
  exact ⟨(a : X), (b : X), a.2, b.2, ha1, hb1, fun h => hab (Subtype.ext h)⟩

private lemma s888_triple_mul_eq_one {x y z : X} (hxy : Commute x y) (hxz : Commute x z)
    (hyz : Commute y z) (hx : x * x = 1) (hy : y * y = 1) (hz : z * z = 1) :
    (x * y) * (x * z) * (y * z) = 1 := by
  have h1 : (x * y) * (x * z) = (x * x) * (y * z) := hxy.symm.mul_mul_mul_comm x z
  have h2 : (y * z) * (y * z) = (y * y) * (z * z) := hyz.symm.mul_mul_mul_comm y z
  calc (x * y) * (x * z) * (y * z) = ((x * x) * (y * z)) * (y * z) := by rw [h1]
    _ = (y * z) * (y * z) := by rw [hx, one_mul]
    _ = (y * y) * (z * z) := h2
    _ = 1 := by rw [hy, hz, mul_one]

private noncomputable def s888_cvEquiv (V F : Subgroup X) :
    ↥(V ⊓ centralizer (F : Set X)) ≃ {v : V // ∀ y ∈ F, y * (v : X) * y⁻¹ = v} where
  toFun z := ⟨⟨z.1, z.2.1⟩, fun y hy => by
    have hcomm : y * (z : X) = (z : X) * y :=
      (Subgroup.mem_centralizer_iff.mp z.2.2) y hy
    calc y * (z : X) * y⁻¹ = ((z : X) * y) * y⁻¹ := by rw [hcomm]
      _ = z := by rw [mul_assoc, mul_inv_cancel, mul_one]⟩
  invFun v := ⟨v.1.1, v.1.2, Subgroup.mem_centralizer_iff.mpr (fun y hy => by
    have h := v.2 y hy
    calc y * (v.1 : X) = (y * (v.1 : X) * y⁻¹) * y := by group
      _ = (v.1 : X) * y := by rw [h])⟩
  left_inv z := Subtype.ext rfl
  right_inv v := Subtype.ext rfl

private lemma s888_mem_inf_centralizer {F : Subgroup X} {x : X} (hxV : x ∈ V)
    (hfix : ∀ u ∈ F, u * x * u⁻¹ = x) : x ∈ V ⊓ centralizer (F : Set X) :=
  ⟨hxV, s888_mem_centralizer_of_conj_eq hfix⟩

theorem exists_suppTwo [Finite X] (hS : PlaneSys V W) (hpar : PlaneParity V W) {F : Subgroup X}
    (hF : ActsElemAb V F) {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ 2)
    (hrk : (centralizer (V : Set X)).relIndex F = 2 ^ k)
    (hm : ∀ u ∈ F, u ∉ centralizer (V : Set X) →
      2 ^ 6 ≤ Nat.card {v : V // u * (v : X) * u⁻¹ = v})
    {I : Subgroup X} (hIV : I ≤ V) (hIF : ∀ v ∈ I, ∀ u ∈ F, u * v * u⁻¹ = v)
    (hI : 2 ^ (8 - 2 * k) ≤ Nat.card I) : ∃ v : V, (v : X) ∈ I ∧ SuppTwo hS v := by
  classical
  let H := planeImage hS F
  let D := suppSet hS F
  let Cv := V ⊓ centralizer (F : Set X)
  have hcardCv : Nat.card Cv ≤ fixedBound H D := by
    change Nat.card ↥(V ⊓ centralizer (F : Set X)) ≤
      fixedBound (planeImage hS F) (suppSet hS F)
    rw [Nat.card_congr (s888_cvEquiv V F)]
    exact card_fixed_le hS hF
  have hHD : H.card * D.card = 2 ^ k := by
    have h := relIndex_centralizer_eq hS hF
    rw [hrk] at h
    exact h.symm
  have hH1 : 1 ∈ H := (planeImage_group hS hF).1
  have hmulH : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H := (planeImage_group hS hF).2.1
  have hsqH : ∀ a ∈ H, a * a = 1 := (planeImage_group hS hF).2.2
  have hD0 : 0 ∈ D := (suppSet_subspace hS hF).1
  have haddD : ∀ x ∈ D, ∀ y ∈ D, x + y ∈ D := (suppSet_subspace hS hF).2
  have htab := table71 hH1 hmulH hsqH hD0 haddD
    (suppSet_even hS hpar hF) (suppSet_fixed hS hF)
  have hfirst : H.card * D.card * fixedBound H D ≤ 2 ^ 7 := by
    rcases htab with h | ⟨hH, hD⟩
    · exact h
    · exfalso
      have hone : H.card * D.card = 1 := by rw [hH, hD]
      rw [hone] at hHD
      have h2 : 2 ≤ 2 ^ k := by
        have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hk1
        simpa using this
      omega
  have hbound : Nat.card Cv * 2 ^ k ≤ 2 ^ 7 := by
    calc Nat.card Cv * 2 ^ k = Nat.card Cv * (H.card * D.card) := by rw [hHD]
      _ = H.card * D.card * Nat.card Cv := by ring
      _ ≤ H.card * D.card * fixedBound H D := Nat.mul_le_mul_left _ hcardCv
      _ ≤ 2 ^ 7 := hfirst
  have hI_Cv : I ≤ Cv := by
    intro v hv
    exact s888_mem_inf_centralizer (V := V) (F := F) (hIV hv) (hIF v hv)
  have hcardI_le : Nat.card Cv ≤ 2 * Nat.card I := by
    have hk : k = 1 ∨ k = 2 := by omega
    rcases hk with rfl | rfl <;> norm_num at hbound hI ⊢ <;> omega
  have htriple : ∃ a b c : Cv, SuppTwo hS ⟨a.1, a.2.1⟩ ∧
      SuppTwo hS ⟨b.1, b.2.1⟩ ∧ SuppTwo hS ⟨c.1, c.2.1⟩ ∧ a * b * c = 1 := by
    by_cases hpl : ∀ f : normalizer (V : Set X), (f : X) ∈ F → planeHom hS f = 1
    ·
      obtain ⟨e0, he0W, he01, he0fix⟩ := exists_fixed_in_plane hS hF hpl 0
      obtain ⟨e1, he1W, he11, he1fix⟩ := exists_fixed_in_plane hS hF hpl 1
      obtain ⟨e2, he2W, he21, he2fix⟩ := exists_fixed_in_plane hS hF hpl 2
      have h01 : ∀ u ∈ F, u * (e0 * e1) * u⁻¹ = e0 * e1 := by
        intro u hu
        rw [show u * (e0 * e1) * u⁻¹ = (u * e0 * u⁻¹) * (u * e1 * u⁻¹) by group,
          he0fix u hu, he1fix u hu]
      have h02 : ∀ u ∈ F, u * (e0 * e2) * u⁻¹ = e0 * e2 := by
        intro u hu
        rw [show u * (e0 * e2) * u⁻¹ = (u * e0 * u⁻¹) * (u * e2 * u⁻¹) by group,
          he0fix u hu, he2fix u hu]
      have h12 : ∀ u ∈ F, u * (e1 * e2) * u⁻¹ = e1 * e2 := by
        intro u hu
        rw [show u * (e1 * e2) * u⁻¹ = (u * e1 * u⁻¹) * (u * e2 * u⁻¹) by group,
          he1fix u hu, he2fix u hu]
      let a : Cv := ⟨e0 * e1, V.mul_mem (hS.le 0 he0W) (hS.le 1 he1W),
        s888_mem_centralizer_of_conj_eq h01⟩
      let b : Cv := ⟨e0 * e2, V.mul_mem (hS.le 0 he0W) (hS.le 2 he2W),
        s888_mem_centralizer_of_conj_eq h02⟩
      let c : Cv := ⟨e1 * e2, V.mul_mem (hS.le 1 he1W) (hS.le 2 he2W),
        s888_mem_centralizer_of_conj_eq h12⟩
      refine ⟨a, b, c, ?_, ?_, ?_, ?_⟩
      · exact suppTwo_mul hS (by decide : (0 : Fin 4) ≠ 1) he0W he1W he01 he11
      · exact suppTwo_mul hS (by decide : (0 : Fin 4) ≠ 2) he0W he2W he01 he21
      · exact suppTwo_mul hS (by decide : (1 : Fin 4) ≠ 2) he1W he2W he11 he21
      · apply Subtype.ext
        show (e0 * e1) * (e0 * e2) * (e1 * e2) = 1
        exact s888_triple_mul_eq_one
          (hS.comm e0 (hS.le 0 he0W) e1 (hS.le 1 he1W))
          (hS.comm e0 (hS.le 0 he0W) e2 (hS.le 2 he2W))
          (hS.comm e1 (hS.le 1 he1W) e2 (hS.le 2 he2W))
          (hS.sq e0 (hS.le 0 he0W)) (hS.sq e1 (hS.le 1 he1W))
          (hS.sq e2 (hS.le 2 he2W))
    ·
      push Not at hpl
      obtain ⟨τ, hτF, hτ⟩ := hpl
      obtain ⟨c, d, hcd, hfix⟩ := exists_fixed_pair hS hF hm hτF hτ
      obtain ⟨x1, x2, hx1W, hx2W, hx11, hx21, hx12⟩ :=
        s888_exists_two_ne_one (A := W c) (hS.card c)
      obtain ⟨y1, y2, hy1W, hy2W, hy11, hy21, hy12⟩ :=
        s888_exists_two_ne_one (A := W d) (hS.card d)
      let x3 : X := x1 * x2
      let y3 : X := y1 * y2
      have hx3W : x3 ∈ W c := by
        show x1 * x2 ∈ W c
        exact (W c).mul_mem hx1W hx2W
      have hy3W : y3 ∈ W d := by
        show y1 * y2 ∈ W d
        exact (W d).mul_mem hy1W hy2W
      have hx31 : x3 ≠ 1 := by
        intro hx3one
        have hx1sq : x1 * x1 = 1 := hS.sq x1 (hS.le c hx1W)
        have h : x1 * x2 = x1 * x1 := by
          rw [show x1 * x2 = x3 from rfl, hx3one, hx1sq]
        exact hx12 (mul_left_cancel h).symm
      have hy31 : y3 ≠ 1 := by
        intro hy3one
        have hy1sq : y1 * y1 = 1 := hS.sq y1 (hS.le d hy1W)
        have h : y1 * y2 = y1 * y1 := by
          rw [show y1 * y2 = y3 from rfl, hy3one, hy1sq]
        exact hy12 (mul_left_cancel h).symm
      have hfix1 : ∀ u ∈ F, u * (x1 * y1) * u⁻¹ = x1 * y1 :=
        fun u hu => hfix u hu _ ((W c ⊔ W d).mul_mem (Subgroup.mem_sup_left hx1W)
          (Subgroup.mem_sup_right hy1W))
      have hfix2 : ∀ u ∈ F, u * (x2 * y2) * u⁻¹ = x2 * y2 :=
        fun u hu => hfix u hu _ ((W c ⊔ W d).mul_mem (Subgroup.mem_sup_left hx2W)
          (Subgroup.mem_sup_right hy2W))
      have hfix3 : ∀ u ∈ F, u * (x3 * y3) * u⁻¹ = x3 * y3 :=
        fun u hu => hfix u hu _ ((W c ⊔ W d).mul_mem (Subgroup.mem_sup_left hx3W)
          (Subgroup.mem_sup_right hy3W))
      let a : Cv := ⟨x1 * y1, V.mul_mem (hS.le c hx1W) (hS.le d hy1W),
        s888_mem_centralizer_of_conj_eq hfix1⟩
      let b : Cv := ⟨x2 * y2, V.mul_mem (hS.le c hx2W) (hS.le d hy2W),
        s888_mem_centralizer_of_conj_eq hfix2⟩
      let e : Cv := ⟨x3 * y3, V.mul_mem (hS.le c hx3W) (hS.le d hy3W),
        s888_mem_centralizer_of_conj_eq hfix3⟩
      have hcomm_y1x2 : Commute y1 x2 :=
        (hS.comm x2 (hS.le c hx2W) y1 (hS.le d hy1W)).symm
      have hv12 : (x1 * y1) * (x2 * y2) = (x1 * x2) * (y1 * y2) :=
        hcomm_y1x2.mul_mul_mul_comm x1 y2
      refine ⟨a, b, e, ?_, ?_, ?_, ?_⟩
      · exact suppTwo_mul hS hcd hx1W hy1W hx11 hy11
      · exact suppTwo_mul hS hcd hx2W hy2W hx21 hy21
      · exact suppTwo_mul hS hcd hx3W hy3W hx31 hy31
      · apply Subtype.ext
        show (x1 * y1) * (x2 * y2) * (x3 * y3) = 1
        change (x1 * y1) * (x2 * y2) * ((x1 * x2) * (y1 * y2)) = 1
        rw [← hv12]
        exact hS.sq ((x1 * y1) * (x2 * y2))
          (V.mul_mem (V.mul_mem (hS.le c hx1W) (hS.le d hy1W))
            (V.mul_mem (hS.le c hx2W) (hS.le d hy2W)))
  obtain ⟨a, b, c, haSupp, hbSupp, hcSupp, habc⟩ := htriple
  have habcX : (a : X) * (b : X) * (c : X) = 1 := by
    have h := congrArg (fun z : Cv => (z : X)) habc
    simpa using h
  rcases mem_of_triple_of_card_le hI_Cv hcardI_le a.2 b.2 c.2 habcX with ha | hb | hc
  · exact ⟨⟨a.1, a.2.1⟩, by simpa using ha, haSupp⟩
  · exact ⟨⟨b.1, b.2.1⟩, by simpa using hb, hbSupp⟩
  · exact ⟨⟨c.1, c.2.1⟩, by simpa using hc, hcSupp⟩

end CFSG.OddStandard.SmallF3.Omega
