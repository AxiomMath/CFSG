module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.Clique

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

@[expose] def Segev29 : Prop :=
  ∀ (H : Type) [Group H] (a x y : H), orderOf a = 2 → orderOf x = 2 → orderOf y = 2 →
    x * y = y * x → orderOf (a * x) = 5 → orderOf (a * y) = 5 → orderOf (a * (x * y)) = 5 →
      ∃ ω : H, orderOf ω = 11 ∧ ω ∈ Subgroup.closure {a, x, y} ∧
        (a * x) * ω * (a * x)⁻¹ ∈ Subgroup.zpowers ω ∧
        Subgroup.closure {a, x, ω} = Subgroup.closure {a, x, y}

variable {G G' : Type} [Group G] [Group G'] {a z : G} {a' z' : G'} {α : G → G'}
  {F : Fam a α} {θ : G → G'}

private theorem eleven_prod_order_two (p : Multiplicative (ZMod 11) × Multiplicative (ZMod 2))
    (hp : orderOf p = 2) : p = (1, Multiplicative.ofAdd 1) := by
  have hp2 : p ^ 2 = 1 := by
    have h := pow_orderOf_eq_one p
    rwa [hp] at h
  have hpne : p ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hp
    omega
  obtain ⟨a, b⟩ := p
  have ha2 : a ^ 2 = 1 := by simpa using congrArg Prod.fst hp2
  have hb2 : b ^ 2 = 1 := by simpa using congrArg Prod.snd hp2
  have ha1 : a = 1 := by
    have h2 : orderOf a ∣ 2 := orderOf_dvd_iff_pow_eq_one.2 ha2
    have h11 : orderOf a ∣ 11 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      have h := pow_card_eq_one' (G := Multiplicative (ZMod 11)) (x := a)
      rwa [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod] at h
    have hgcd : orderOf a ∣ Nat.gcd 2 11 := Nat.dvd_gcd h2 h11
    rw [show Nat.gcd 2 11 = 1 by decide] at hgcd
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hgcd)
  have hbne : b ≠ 1 := by
    intro hb
    exact hpne (by rw [ha1, hb]; rfl)
  have hb1 : b = Multiplicative.ofAdd 1 := by
    have h2eq : ∀ x : Multiplicative (ZMod 2), x ≠ 1 → x = Multiplicative.ofAdd 1 := by
      decide
    exact h2eq b hbne
  exact Prod.ext ha1 hb1

private theorem eleven_prod_inv_order :
    orderOf ((1, Multiplicative.ofAdd 1) :
      Multiplicative (ZMod 11) × Multiplicative (ZMod 2)) = 2 := by
  apply orderOf_eq_prime
  · decide
  · decide

private theorem shape_eleven_exists_unique_inv {X : Type} [Group X]
    (hX : IsShapeCentralizerEleven X) :
    ∃ t : X, orderOf t = 2 ∧ ∀ s : X, orderOf s = 2 → s = t := by
  obtain ⟨e⟩ := hX
  refine ⟨e.symm (1, Multiplicative.ofAdd 1), ?_, ?_⟩
  · exact (MulEquiv.orderOf_eq e.symm (1, Multiplicative.ofAdd 1)).trans
      eleven_prod_inv_order
  · intro s hs
    apply e.injective
    rw [MulEquiv.apply_symm_apply]
    exact eleven_prod_order_two (e s) ((MulEquiv.orderOf_eq e s).trans hs)

private theorem clique_not_five_E (hC : Cover4A) (hW : Wit20) (hG : Gen2A) (h : F5Std a z)
    (h' : F5Std a' z') (hα : IsIsoOn (Gx a) (Gx a') α) (hθ : IsTheta a F θ) {t w : G}
    (ht : IsConj a t) (htne : t ∉ orb5E a a) (hw : w ∈ orb2A a t) :
    IsClique3 a' (θ t) (θ w) (θ (t * w)) := by
  by_cases hta : t = a
  · subst t
    have hwA : IsConj a (w * a) := (cp_isConj_mul_comm a a w).1 hw.2
    have hcomm : w * a = a * w :=
      h.mul_comm (Or.inl hw.1) (Or.inl (IsConj.refl a)) (Or.inl hwA)
    have hcl := theta_clique_of_not_five_E hC hW hG h h' hα hθ (x := w) (y := a)
      (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hw)))))) ⟨IsConj.refl a, hwA⟩
    rw [hcomm] at hcl
    exact hcl.swap12
  · have htmem : t ∈ gammaSet a z a :=
      h.loc.gamma.self.eq_gamma a t (IsConj.refl a) ht
    simp only [gammaSet, Set.mem_union, Set.mem_singleton_iff] at htmem
    rcases htmem with (((((((hta' | h2A) | h2B) | h3A) | h4A) | h4B) | h5A) | h5E) | h6A
    · exact absurd hta' hta
    · exact theta_clique_of_not_five_E hC hW hG h h' hα hθ
        (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h2A)))))) hw
    · exact theta_clique_of_not_five_E hC hW hG h h' hα hθ
        (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h2B)))))) hw
    · exact theta_clique_of_not_five_E hC hW hG h h' hα hθ
        (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h3A))))) hw
    · exact theta_clique_of_not_five_E hC hW hG h h' hα hθ
        (Or.inl (Or.inl (Or.inl (Or.inr h4A)))) hw
    · exact theta_clique_of_not_five_E hC hW hG h h' hα hθ
        (Or.inl (Or.inl (Or.inr h4B))) hw
    · exact theta_clique_of_not_five_E hC hW hG h h' hα hθ
        (Or.inl (Or.inr h5A)) hw
    · exact absurd h5E htne
    · exact theta_clique_of_not_five_E hC hW hG h h' hα hθ (Or.inr h6A) hw

theorem theta_five_E (hC : Cover4A) (hW : Wit20) (hG : Gen2A) (h29 : Segev29) (h : F5Std a z)
    (h' : F5Std a' z') (hα : IsIsoOn (Gx a) (Gx a') α) (hθ : IsTheta a F θ) {x y : G}
    (hx : x ∈ orb5E a a)
    (hy : y ∈ orb2A a x) : θ y ∈ orb2A a' (θ x) := by
  have hc : a' ≠ 1 := cp_ne_one_of_orderOf_eq_two h'.typ.orderOf_a
  have hx2 : orderOf x = 2 := h.orderOf_eq_two (Or.inl hx.1.1)
  have hy2 : orderOf y = 2 := h.orderOf_eq_two (Or.inl hy.1)
  have hcomm : x * y = y * x := h.mul_comm (Or.inl hx.1.1) (Or.inl hy.1) (Or.inl hy.2)
  have hP : IsClique3 a' (θ x) (θ y) (θ (x * y)) := by
    by_cases hy5 : y ∈ orb5E a a
    · by_cases hxy5 : x * y ∈ orb5E a a
      ·
        let ρ : G := a * x
        obtain ⟨ω, hω11, hωcl, hρωρ, hclω⟩ :=
          h29 G a x y h.typ.orderOf_a hx2 hy2 hcomm hx.2.1 hy5.2.1 hxy5.2.1
        have hshapeω : IsShapeCentralizerEleven ↥(Gx ω) := h.loc.order.cent_eleven ω hω11
        obtain ⟨t, ht2, _⟩ := shape_eleven_exists_unique_inv hshapeω
        have htG2 : orderOf (t : G) = 2 := (Subgroup.orderOf_coe t).trans ht2
        have hρωρ11 : orderOf (ρ * ω * ρ⁻¹) = 11 := by
          have h := (MulEquiv.orderOf_eq (MulAut.conj ρ) ω).trans hω11
          simpa [MulAut.conj_apply] using h
        have hshapeρωρ : IsShapeCentralizerEleven ↥(Gx (ρ * ω * ρ⁻¹)) :=
          h.loc.order.cent_eleven _ hρωρ11
        obtain ⟨u, _hu2, huuniq⟩ := shape_eleven_exists_unique_inv hshapeρωρ
        have ht_comm_ρωρ : (t : G) ∈ Gx (ρ * ω * ρ⁻¹) := by
          have htω : ω * (t : G) = (t : G) * ω := mem_Gx.1 t.2
          have hωGt : ω ∈ Gx (t : G) := mem_Gx.2 htω.symm
          have hρGt : ρ * ω * ρ⁻¹ ∈ Gx (t : G) := (Subgroup.zpowers_le.2 hωGt) hρωρ
          exact mem_Gx.2 (mem_Gx.1 hρGt).symm
        have hconjt : ρ * (t : G) * ρ⁻¹ ∈ Gx (ρ * ω * ρ⁻¹) := by
          have htω : ω * (t : G) = (t : G) * ω := mem_Gx.1 t.2
          refine mem_Gx.2 ?_
          calc (ρ * ω * ρ⁻¹) * (ρ * (t : G) * ρ⁻¹)
              = ρ * (ω * (t : G)) * ρ⁻¹ := by group
            _ = ρ * ((t : G) * ω) * ρ⁻¹ := by rw [htω]
            _ = (ρ * (t : G) * ρ⁻¹) * (ρ * ω * ρ⁻¹) := by group
        have hu2' : orderOf (⟨ρ * (t : G) * ρ⁻¹, hconjt⟩ :
            ↥(Gx (ρ * ω * ρ⁻¹))) = 2 := by
          simpa [MulAut.conj_apply]
            using (MulEquiv.orderOf_eq (MulAut.conj ρ) (t : G)).trans htG2
        have hv2 : orderOf (⟨(t : G), ht_comm_ρωρ⟩ :
            ↥(Gx (ρ * ω * ρ⁻¹))) = 2 := by simpa using htG2
        have hval1 : (⟨(t : G), ht_comm_ρωρ⟩ : ↥(Gx (ρ * ω * ρ⁻¹))) = u :=
          huuniq _ hv2
        have hval2 : (⟨ρ * (t : G) * ρ⁻¹, hconjt⟩ : ↥(Gx (ρ * ω * ρ⁻¹))) = u :=
          huuniq _ hu2'
        have ht_eq_conj : ρ * (t : G) * ρ⁻¹ = (t : G) :=
          (congrArg Subtype.val hval2).trans (congrArg Subtype.val hval1).symm
        have hcommρt : ρ * (t : G) = (t : G) * ρ := by
          calc ρ * (t : G) = (ρ * (t : G) * ρ⁻¹) * ρ := by group
            _ = (t : G) * ρ := by rw [ht_eq_conj]
        have htGxax : (t : G) ∈ Gx (a * x) := mem_Gx.2 hcommρt
        have htGxyax : (t : G) ∈ Gxy a x := h.loc.five.self.inv_cent x hx (t : G) htG2 htGxax
        have htGxa : (t : G) ∈ Gx a := (mem_Gxy.mp htGxyax).1
        have htGxx : (t : G) ∈ Gx x := (mem_Gxy.mp htGxyax).2
        have hsub : ({a, x, ω} : Set G) ⊆ Gx (t : G) := by
          intro g hg
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
          rcases hg with rfl | rfl | rfl
          · exact mem_Gx.2 (mem_Gx.1 htGxa).symm
          · exact mem_Gx.2 (mem_Gx.1 htGxx).symm
          · exact mem_Gx.2 (mem_Gx.1 t.2).symm
        have hy_in : y ∈ Subgroup.closure ({a, x, ω} : Set G) := by
          rw [hclω]
          exact Subgroup.subset_closure (by simp)
        have hcl_le : Subgroup.closure ({a, x, ω} : Set G) ≤ Gx (t : G) :=
          (Subgroup.closure_le (Gx (t : G))).2 hsub
        have htGy : (t : G) ∈ Gx y :=
          mem_Gx.2 (mem_Gx.1 (hcl_le hy_in)).symm
        have htx : (t : G) ∈ Gxyz a x y := mem_Gxyz.mpr ⟨htGxa, htGxx, htGy⟩
        exact IsLine.isClique3 hc (theta_line h h' hα hθ hx.1.1 hy ⟨htx, htG2⟩)
      ·
        have hxx : x * x = 1 := cp_mul_self_eq_one_of_orderOf_eq_two hx2
        have hmul : (x * y) * x = y := by
          calc (x * y) * x = (y * x) * x := by rw [hcomm]
            _ = y * (x * x) := by group
            _ = y := by rw [hxx, mul_one]
        have hw : x ∈ orb2A a (x * y) := ⟨hx.1.1, by rw [hmul]; exact hy.1⟩
        have hcl := clique_not_five_E hC hW hG h h' hα hθ hy.2 hxy5 hw
        rw [hmul] at hcl
        exact hcl.rotate
    ·
      have hw : x ∈ orb2A a y := ⟨hx.1.1, (cp_isConj_mul_comm a x y).1 hy.2⟩
      have hcl := clique_not_five_E hC hW hG h h' hα hθ hy.1 hy5 hw
      rw [← hcomm] at hcl
      exact hcl.swap12
  exact ⟨hθ.typed h h' hα hy.1, hP.1.2⟩

end CFSG.EvenSporadicStandard.HNRecog.Section4
