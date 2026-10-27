module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.F4SylowE6

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.CentralExt.FieldFour
  Matrix

variable (K : Type) [Field K] [Finite K] [CharP K 2]

@[expose] def posU7 : Subgroup (e7Data_valid.minGroup K) :=
  ⨆ γ ∈ {γ : Fin Tag.E7.rank → ℤ | IsRoot Tag.E7 γ ∧ 0 < (1 : ℤ) * ht γ},
    e7Data_valid.rootGroup K γ

theorem isPGroup_posU7 : IsPGroup 2 (posU7 K) := by
  intro g
  have hg : (g : e7Data_valid.minGroup K) ∈ ⨆ γ ∈ {γ : Fin Tag.E7.rank → ℤ |
      IsRoot Tag.E7 γ ∧ 0 < (1 : ℤ) * ht γ}, e7Data_valid.rootGroup K γ := g.2
  obtain ⟨s, hs⟩ := exists_pow_two_eq_one_of_isUni K _ (e7Data_valid.isUni_of_mem K (η := 1) hg)
  refine ⟨s, Subtype.ext (e7Data_valid.endo_injective K ?_)⟩
  change e7Data_valid.endo K ((g : e7Data_valid.minGroup K) ^ 2 ^ s) = e7Data_valid.endo K 1
  rw [endo_pow, hs, e7Data_valid.endo_one K]

theorem rootGroup_le_posU7 {γ : Fin Tag.E7.rank → ℤ} (hγ : IsRoot Tag.E7 γ)
    (hpos : 0 < height γ) : e7Data_valid.rootGroup K γ ≤ posU7 K :=
  le_iSup₂_of_le (f := fun γ (_ : γ ∈ {γ : Fin Tag.E7.rank → ℤ |
    IsRoot Tag.E7 γ ∧ 0 < (1 : ℤ) * ht γ}) => e7Data_valid.rootGroup K γ) γ
    ⟨hγ, by rw [one_mul]; exact hpos⟩ le_rfl

theorem e7Eps_mul_self (γ : Fin Tag.E7.rank → ℤ) : (e7Eps γ : K) * (e7Eps γ : K) = 1 := by
  rcases e7Eps_eq_one_or γ with h | h <;> rw [h] <;> simp

theorem Uad_le_map_posU7 : Uad K Tag.E7 ≤ (posU7 K).map (e7Isogeny K) := by
  intro g hg
  have hg' : g.1 ∈ CFSG.Blueprint.Chevalley.posUnipotent Tag.E7 K := hg
  suffices h : ∀ x ∈ CFSG.Blueprint.Chevalley.posUnipotent Tag.E7 K, ∃ y : adjointGroup Tag.E7 K,
      y.1 = x ∧ y ∈ (posU7 K).map (e7Isogeny K) by
    obtain ⟨y, hy1, hy⟩ := h _ hg'
    have : y = g := Subtype.ext hy1
    rwa [this] at hy
  intro x hx
  unfold CFSG.Blueprint.Chevalley.posUnipotent CFSG.Blueprint.Chevalley.rootSpan at hx
  refine Subgroup.iSup_induction _ (C := fun x => ∃ y : adjointGroup Tag.E7 K, y.1 = x ∧
    y ∈ (posU7 K).map (e7Isogeny K)) hx (fun α x hx => ?_) ⟨1, rfl, one_mem _⟩
    (fun x y ⟨a, ha1, ha⟩ ⟨b, hb1, hb⟩ => ⟨a * b, by rw [Subgroup.coe_mul, ha1, hb1], mul_mem ha hb⟩)
  refine Subgroup.iSup_induction _ (C := fun x => ∃ y : adjointGroup Tag.E7 K, y.1 = x ∧
    y ∈ (posU7 K).map (e7Isogeny K)) hx (fun hα z hz => ?_) ⟨1, rfl, one_mem _⟩
    (fun x y ⟨a, ha1, ha⟩ ⟨b, hb1, hb⟩ => ⟨a * b, by rw [Subgroup.coe_mul, ha1, hb1], mul_mem ha hb⟩)
  obtain ⟨hroot, hpos⟩ := hα
  have hz' : (⟨z, rootSubgroup_le_adjointGroup α hz⟩ : adjointGroup Tag.E7 K) ∈
      (CFSG.Blueprint.Chevalley.rootSubgroup Tag.E7 K α).subgroupOf (adjointGroup Tag.E7 K) := hz
  rw [(rootOperatorFamily Tag.E7).subgroupOf_rootSubgroup_eq K ⟨α, hroot⟩] at hz'
  obtain ⟨c, hc⟩ := (rootOperatorFamily Tag.E7).mem_rootSubgroup.1 hz'
  refine ⟨⟨z, rootSubgroup_le_adjointGroup α hz⟩, rfl, ?_⟩
  refine ⟨e7Data_valid.xm K α ((e7Eps α : K) * c),
    rootGroup_le_posU7 K hroot hpos (e7Data_valid.xm_mem_rootGroup K α _), ?_⟩
  rw [e7Isogeny_xm K α, ← mul_assoc, e7Eps_mul_self, one_mul,
    CFSG.LieType.Steinberg.Adjoint.xPar_of_isRoot hroot]
  exact hc

theorem finite_minGroup7 : Finite (e7Data_valid.minGroup K) := finite_minGroup' (K := K) e7Data_valid

theorem two_group_inf_ker7 {z : e7Data_valid.minGroup K}
    (hz : e7Isogeny K z = 1) : z = 1 := by
  have hker : z ∈ Subgroup.center (e7Data_valid.minGroup K) := by
    rw [← e7Isogeny_ker_eq_center]; exact hz
  have hcard := (CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e7 (k := K)).1
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hn, hq⟩ := FiniteField.card K 2
  have hq' : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hq]
  have h2q : 2 ∣ Nat.card K := by rw [hq']; exact dvd_pow_self 2 n.pos.ne'
  have hpos : 0 < Nat.card K := Nat.card_pos
  have hc1 : Nat.card (Subgroup.center (e7Data_valid.minGroup K)) = 1 := by
    rw [hcard]
    have h1 : Nat.gcd 2 (Nat.card K - 1) ∣ 2 := Nat.gcd_dvd_left _ _
    have h3 : Nat.gcd 2 (Nat.card K - 1) ∣ Nat.card K - 1 := Nat.gcd_dvd_right _ _
    rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
    · exact h
    · rw [h] at h3; omega
  have hb : Subgroup.center (e7Data_valid.minGroup K) = ⊥ := Subgroup.eq_bot_of_card_eq _ hc1
  rw [hb, Subgroup.mem_bot] at hker
  exact hker

theorem e7_posU7_sylow : ∃ P : Sylow 2 (e7Data_valid.minGroup K), (P : Subgroup _) = posU7 K := by
  have := finite_minGroup7 K
  obtain ⟨P, hP⟩ := (isPGroup_posU7 K).exists_le_sylow
  refine ⟨P, ?_⟩
  symm
  have hPp : IsPGroup 2 (P : Subgroup (e7Data_valid.minGroup K)) := P.isPGroup'
  set π := e7Isogeny K with hπ
  have hfin : Finite (adjointGroup Tag.E7 K) := by
    have := finite_modGL (τ := Tag.E7) (K := K)
    infer_instance
  have hinj : Function.Injective (fun x : (P : Subgroup (e7Data_valid.minGroup K)) =>
      (⟨π x, ⟨x, x.2, rfl⟩⟩ : (P : Subgroup (e7Data_valid.minGroup K)).map π)) := by
    intro x y hxy
    have h1 : π (x : e7Data_valid.minGroup K) = π y := congrArg Subtype.val hxy
    have h2 : (x : e7Data_valid.minGroup K)⁻¹ * y = 1 :=
      two_group_inf_ker7 K (by rw [map_mul, map_inv, h1, inv_mul_cancel])
    exact Subtype.ext (inv_mul_eq_one.1 h2)
  have hcardP : Nat.card (P : Subgroup (e7Data_valid.minGroup K)) =
      Nat.card ((P : Subgroup (e7Data_valid.minGroup K)).map π) := by
    refine Nat.card_congr (Equiv.ofBijective _ ⟨hinj, ?_⟩)
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨g, hg⟩ := adjoint_conj_into_U K Tag.E7 _ (hPp.map π)
  have hc1 : Nat.card (((P : Subgroup (e7Data_valid.minGroup K)).map π).map
      (MulAut.conj g).toMonoidHom) = Nat.card ((P : Subgroup (e7Data_valid.minGroup K)).map π) :=
    (Nat.card_congr (Subgroup.equivMapOfInjective _ _ (MulAut.conj g).injective).toEquiv).symm
  have h2 := Subgroup.card_le_of_le (Uad_le_map_posU7 K)
  have h3 := card_map_le_of_surj (posU7 K) π
  have h4 := Subgroup.card_le_of_le hg
  have h5 : Nat.card (posU7 K) ≤ Nat.card (P : Subgroup (e7Data_valid.minGroup K)) :=
    Subgroup.card_le_of_le hP
  have hcard : Nat.card (P : Subgroup (e7Data_valid.minGroup K)) ≤ Nat.card (posU7 K) := by
    rw [hcardP, ← hc1]
    exact h4.trans (h2.trans h3)
  exact Subgroup.eq_of_le_of_card_ge hP hcard

theorem e7_conj_into_posU7 (A : Subgroup (e7Data_valid.minGroup K)) (hA : IsPGroup 2 A) :
    ∃ g : e7Data_valid.minGroup K, A.map (MulAut.conj g).toMonoidHom ≤ posU7 K := by
  have := finite_minGroup7 K
  obtain ⟨P, hP⟩ := e7_posU7_sylow K
  obtain ⟨g, hg⟩ := exists_conj_le_sylow P A hA
  exact ⟨g, hP ▸ hg⟩

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc
