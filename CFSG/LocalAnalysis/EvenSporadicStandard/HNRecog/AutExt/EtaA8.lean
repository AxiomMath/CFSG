module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.Tau
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.A8Outer
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.A8.Decomp

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G : Type} [Group G] {a z : G}

private theorem mem_closure_pair_iff {p q x : G} (hp : p * p = 1) (hq : q * q = 1)
    (hpq : p * q = q * p) :
    x ∈ Subgroup.closure ({p, q} : Set G) ↔ x = 1 ∨ x = p ∨ x = q ∨ x = p * q := by
  have hp' : ∀ y, p * (p * y) = y := fun y => by rw [← mul_assoc, hp, one_mul]
  have hqp : ∀ y, q * (p * y) = p * (q * y) := fun y => by rw [← mul_assoc, ← hpq, mul_assoc]
  have hpi : p⁻¹ = p := inv_eq_of_mul_eq_one_right hp
  have hqi : q⁻¹ = q := inv_eq_of_mul_eq_one_right hq
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    | one => exact Or.inl rfl
    | mul x y _ _ hx hy =>
      rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
        simp only [mul_assoc, hp, hq, hp', hqp, hpq.symm, mul_one, one_mul, true_or, or_true]
    | inv x _ hx =>
      rcases hx with rfl | rfl | rfl | rfl <;>
        simp only [inv_one, hpi, hqi, mul_inv_rev, hpq.symm, true_or, or_true]
  · rintro (rfl | rfl | rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · have hp_mem : p ∈ Subgroup.closure ({p, q} : Set G) := Subgroup.subset_closure (by simp)
      have hq_mem : q ∈ Subgroup.closure ({p, q} : Set G) := Subgroup.subset_closure (by simp)
      exact Subgroup.mul_mem (Subgroup.closure ({p, q} : Set G)) hp_mem hq_mem

theorem decomp_2A_of_base (h : F5Base a z) {b : G} (hb : b ∈ orb2A a a) :
    ∀ x ∈ Gxy a b, ∃ y ∈ derivedOf (Gxy a b), x = y ∨ x = a * y ∨ x = b * y ∨ x = a * b * y := by
  have ha2 : a ^ 2 = 1 := by
    simpa [h.orderOf_eq_two (Or.inl (IsConj.refl a))] using pow_orderOf_eq_one a
  have haa : a * a = 1 := by rwa [pow_two] at ha2
  have hb2 : b ^ 2 = 1 := by
    simpa [h.orderOf_eq_two (Or.inl hb.1)] using pow_orderOf_eq_one b
  have hbb : b * b = 1 := by rwa [pow_two] at hb2
  have hab : a * b = b * a :=
    h.mul_comm (Or.inl (IsConj.refl a)) (Or.inl hb.1) (Or.inl hb.2)
  have ha1 : a ≠ 1 := by
    intro h1
    have h2 := h.orderOf_eq_two (Or.inl (IsConj.refl a))
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hb1 : b ≠ 1 := by
    intro h1
    have h2 := h.orderOf_eq_two (Or.inl hb.1)
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hne : a ≠ b := by
    intro hab_eq
    have hmul : a * b = 1 := by rw [← hab_eq]; exact haa
    have hconj : IsConj a 1 := by rw [← hmul]; exact hb.2
    exact ha1 (isConj_one_left.mp hconj)
  intro x hx
  obtain ⟨u, hu, s, hs, hxu⟩ := exists_mul_eq_of_isShapeTwoTwoTimesA8
    (h.loc.fusion3.self.shape_2A b hb) ha2 hb2 hab ha1 hb1 hne x hx
  rcases (mem_closure_pair_iff haa hbb hab).mp hu with rfl | rfl | rfl | rfl
  · exact ⟨s, hs, Or.inl (by rw [hxu, one_mul])⟩
  · exact ⟨s, hs, Or.inr (Or.inl hxu)⟩
  · exact ⟨s, hs, Or.inr (Or.inr (Or.inl hxu))⟩
  · exact ⟨s, hs, Or.inr (Or.inr (Or.inr hxu))⟩

theorem decomp_2A (h : F5Std a z) {b : G} (hb : b ∈ orb2A a a) :
    ∀ x ∈ Gxy a b, ∃ y ∈ derivedOf (Gxy a b), x = y ∨ x = a * y ∨ x = b * y ∨ x = a * b * y :=
  decomp_2A_of_base h.toF5Base hb

theorem exists_eta_A8 (h : F5Std a z) {b : G} (hb : b ∈ orb2A a a) :
    ∃ η : G → G, IsIsoOn (Gx b) (Gx b) η ∧ η a = a ∧ η b = b ∧
      ¬ ∃ g ∈ derivedOf (Gxy a b), ∀ x ∈ derivedOf (Gxy a b), η x = g * x * g⁻¹ := by
  classical
  have ha2 : a ^ 2 = 1 := by
    simpa [h.orderOf_eq_two (Or.inl (IsConj.refl a))] using pow_orderOf_eq_one a
  have haa : a * a = 1 := by rwa [pow_two] at ha2
  have hbb : b * b = 1 := by
    have h2 : b ^ 2 = 1 := by
      simpa [h.orderOf_eq_two (Or.inl hb.1)] using pow_orderOf_eq_one b
    rwa [pow_two] at h2
  have hab : a * b = b * a :=
    h.mul_comm (Or.inl (IsConj.refl a)) (Or.inl hb.1) (Or.inl hb.2)
  obtain ⟨c, hc⟩ := ((h.loc.tableIV.self.partition b hb).orbit 2).nonempty
  have hcmem : c ∈ sBase a b ∧ (a * c) ^ 2 = b := by simpa [sSet] using hc
  obtain ⟨hcbase, hac2⟩ := hcmem
  obtain ⟨hcA, hbcA, _hca, _hcab⟩ := hcbase
  have hc2 : c ^ 2 = 1 := by
    simpa [h.orderOf_eq_two (Or.inl hcA)] using pow_orderOf_eq_one c
  have hcc : c * c = 1 := by rwa [pow_two] at hc2
  have hbc : b * c = c * b := h.mul_comm (Or.inl hb.1) (Or.inl hcA) (Or.inl hbcA)
  have hcGb : c ∈ Gx b := mem_Gx.mpr hbc
  have h1 : a * c * a * c = b := by
    have h1' := hac2
    rw [pow_two] at h1'
    simpa only [mul_assoc] using h1'
  have hcac : c * a * c = a * b := by
    apply mul_left_cancel (a := a)
    calc a * (c * a * c) = a * c * a * c := by simp only [mul_assoc]
      _ = b := h1
      _ = a * (a * b) := by rw [← mul_assoc, haa, one_mul]
  have hFb : F5Std b z := h.of_isConj hb.1 (IsConj.refl z)
  obtain ⟨τ, hτ, hτder, hτout⟩ := exists_tau hFb (Or.inl (IsConj.refl b))
  have hle : Gxy a b ≤ Gx b := by rw [Gxy_eq_inf]; exact inf_le_right
  let η : G → G := fun x => c * τ x * c⁻¹
  have haGb : a ∈ Gx b := mem_Gx.mpr hab.symm
  have hba_conj : IsConj b (b * a) := hb.1.symm.trans (by rw [hab.symm]; exact hb.2)
  have ha_not_der : a ∉ derivedOf (Gx b) := by
    rw [hFb.loc.fusion2.self.mem_derived_iff a haGb ha2]
    intro hiff
    exact (hiff.mp hb.1.symm) hba_conj
  have hτa : τ a = a * b := hτout a haGb ha_not_der
  have heta_a : η a = a := by
    have h2 : c * (c * a * c) * c⁻¹ = a := by
      have h3 : c * (c * a * c) * c⁻¹ = (c * c) * a * (c * c⁻¹) := by
        simp only [mul_assoc]
      rw [h3, hcc, one_mul, mul_inv_cancel, mul_one]
    show c * τ a * c⁻¹ = a
    rw [hτa, ← hcac]
    exact h2
  have hτb : τ b = b := hτder b (derived_Gx_a hFb).1
  have hcb : c * b * c⁻¹ = b := by
    rw [hbc.symm, mul_assoc, mul_inv_cancel, mul_one]
  have heta_b : η b = b := by
    show c * τ b * c⁻¹ = b
    rw [hτb, hcb]
  refine ⟨η, ?_, heta_a, heta_b, ?_⟩
  · exact (hτ.comp (isIsoOn_conj hcGb)).congr (fun x _ => rfl)
  · rintro ⟨g, hgK, hg⟩
    have hK : Nonempty (alternatingGroup (Fin 8) ≃* ↥(derivedOf (Gxy a b))) :=
      nonempty_mulEquiv_derivedOf_of_isShapeTwoTwoTimesA8
        (h.loc.fusion3.self.shape_2A b hb)
    have hM : Nonempty (↥(derivedOf (Gxy a b) ⊔ Subgroup.zpowers c) ≃* Sym 8) :=
      h.loc.tableIV.self.s8_4B b hb c hc
    refine not_inner_of_equiv_sym_eight hK hM ⟨g, hgK, fun x hxK => ?_⟩
    have hxKb : x ∈ derivedOf (Gx b) := (derivedOf_mono hle) hxK
    have hτx : τ x = x := hτder x hxKb
    have hηx : η x = c * x * c⁻¹ := by
      show c * τ x * c⁻¹ = c * x * c⁻¹
      rw [hτx]
    rw [← hηx, hg x hxK]

theorem out_A8 (h : F5Std a z) {b : G} (hb : b ∈ orb2A a a) {ψ₁ ψ₂ : G → G}
    (h₁ : IsIsoOn (derivedOf (Gxy a b)) (derivedOf (Gxy a b)) ψ₁)
    (h₂ : IsIsoOn (derivedOf (Gxy a b)) (derivedOf (Gxy a b)) ψ₂)
    (n₁ : ¬ ∃ g ∈ derivedOf (Gxy a b), ∀ x ∈ derivedOf (Gxy a b), ψ₁ x = g * x * g⁻¹)
    (n₂ : ¬ ∃ g ∈ derivedOf (Gxy a b), ∀ x ∈ derivedOf (Gxy a b), ψ₂ x = g * x * g⁻¹) :
    ∃ g ∈ derivedOf (Gxy a b), ∀ x ∈ derivedOf (Gxy a b), ψ₁ (ψ₂ x) = g * x * g⁻¹ := by
  obtain ⟨e⟩ := nonempty_mulEquiv_derivedOf_of_isShapeTwoTwoTimesA8
    (h.loc.fusion3.self.shape_2A b hb)
  exact out_of_equiv_alt_eight e h₁ h₂ n₁ n₂

end CFSG.EvenSporadicStandard.HNRecog.Section4
