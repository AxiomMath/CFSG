module

public import CFSG.RankThree.PartOne.KE.E7ThreeStab
public import CFSG.LieType.SeitzGeneration.ExcHigh.E7SevenWeylPair

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
open CFSG.RankThree.E6 (charVal charVal_single)

theorem charVal_pi_single {R : Type*} [CommRing R] {τ : Tag} (j : Fin τ.rank) (c : R)
    (x : Fin τ.rank → ℤ) : charVal (Pi.single j c : Fin τ.rank → R) x = (x j : R) * c := by
  unfold charVal
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hi
    simp [Pi.single_apply, hi]
  · simp

theorem e7_coeff_check : ∀ l ∈ Tag.E7.artifactRoots, |l.getD 1 0| ≤ 2 := by
  decide +kernel

theorem e7_coeff_bound {α : Fin Tag.E7.rank → ℤ}
    (hα : IsRoot Tag.E7 α) : |α 1| ≤ 2 := by
  have h := e7_coeff_check _ (isRoot_iff_mem_artifactRoots.1 hα)
  have e : (List.ofFn α).getD 1 0 = α 1 := by
    rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; decide), List.getElem_ofFn]
    rfl
  rwa [e] at h

theorem e7_fixed_col_eq {y : Fin Tag.E7.rank → ZMod 7} (h : y = ![0, y 1, 0, 0, 0, 0, 0]) :
    y = Pi.single 1 (y 1) := by
  funext i
  conv_lhs => rw [h]
  fin_cases i <;> rfl

theorem e7_stab_e1_le
    {c : ZMod 7} (hc : c ≠ 0) {w : WeylGroup Tag.E7}
    (hw : w ∈ dualWeylStabilizer (Pi.single (1 : Fin Tag.E7.rank) c)) :
    w ∈ Subgroup.closure {s | ∃ α, IsRoot Tag.E7 α ∧ α 1 = 0 ∧ s = rootReflection α} := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set r : Fin Tag.E7.rank → ℤ := Pi.single 1 1 with hr
  have hcharr : ∀ x : Fin Tag.E7.rank → ℤ, charVal r x = x 1 := fun x => by
    rw [hr, charVal_pi_single]
    simp
  have hcoef : ∀ j : Fin Tag.E7.rank,
      charVal r (w • (Pi.single j 1 : Fin Tag.E7.rank → ℤ)) = charVal r (Pi.single j 1) := by
    intro j
    have h := mem_dualWeylStabilizer.1 hw (Pi.single j 1)
    rw [charVal_pi_single, charVal_pi_single] at h
    have h' := mul_right_cancel₀ hc h
    rw [hcharr, hcharr]
    have hroot := e7_coeff_bound (IsRoot.smul (isRoot_single Tag.E7 j) w)
    have hj : |(Pi.single j 1 : Fin Tag.E7.rank → ℤ) 1| ≤ 1 := by
      by_cases hj : j = 1
      · subst hj
        simp
      · rw [Pi.single_apply, if_neg (Ne.symm hj)]
        simp
    have hdvd : (7 : ℤ) ∣ (w • (Pi.single j 1 : Fin Tag.E7.rank → ℤ)) 1 -
        (Pi.single j 1 : Fin Tag.E7.rank → ℤ) 1 := by
      have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd
        ((w • (Pi.single j 1 : Fin Tag.E7.rank → ℤ)) 1 - (Pi.single j 1 : Fin Tag.E7.rank → ℤ) 1)
        7).1 (by rw [Int.cast_sub, h', sub_self])
      simpa using h0
    rw [abs_le] at hroot hj
    omega
  have hint : ∀ x, charVal r (w • x) = charVal r x := by
    intro x
    have h1 := charVal_smul_eq_sum r w x
    have h2 := charVal_smul_eq_sum r (1 : WeylGroup Tag.E7) x
    simp only [one_smul, Int.cast_id] at h1 h2
    exact h1.trans ((Finset.sum_congr rfl fun j _ => by rw [hcoef j]).trans h2.symm)
  refine Subgroup.closure_mono ?_ (mem_closure_of_charVal_int r hint)
  rintro _ ⟨α, hα, h0, rfl⟩
  exact ⟨α, hα, by rwa [hcharr] at h0, rfl⟩

theorem e7_inf_le_closure_of_fix
    {z₀ z₁ : Fin Tag.E7.rank → ZMod 7}
    (h₀ : e7G0 ∈ dualWeylStabilizer z₀) (h₁ : e7G0 ∈ dualWeylStabilizer z₁) :
    dualWeylStabilizer z₀ ⊓ dualWeylStabilizer z₁ ≤
      Subgroup.closure {s | ∃ α ∈ rootKernel z₀ ∩ rootKernel z₁, s = rootReflection α} := by
  have e₀ := e7_fixed_col_eq (e7G0_fix h₀)
  have e₁ := e7_fixed_col_eq (e7G0_fix h₁)
  generalize z₀ 1 = c₀ at e₀
  generalize z₁ 1 = c₁ at e₁
  subst e₀ e₁
  by_cases hz : c₀ = 0 ∧ c₁ = 0
  ·
    obtain ⟨rfl, rfl⟩ := hz
    refine le_trans le_top ?_
    rw [← closure_rootReflection_eq_top (τ := Tag.E7)]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨α, hα, rfl⟩
    exact ⟨α, ⟨⟨hα, by rw [charVal_pi_single]; simp⟩, ⟨hα, by rw [charVal_pi_single]; simp⟩⟩, rfl⟩
  ·
    have hsub : {s | ∃ α, IsRoot Tag.E7 α ∧ α 1 = 0 ∧ s = rootReflection α} ⊆
        {s | ∃ α ∈ rootKernel (Pi.single (1 : Fin Tag.E7.rank) c₀) ∩
          rootKernel (Pi.single (1 : Fin Tag.E7.rank) c₁), s = rootReflection α} := by
      rintro _ ⟨α, hα, h1, rfl⟩
      exact ⟨α, ⟨⟨hα, by rw [charVal_pi_single, h1]; simp⟩,
        ⟨hα, by rw [charVal_pi_single, h1]; simp⟩⟩, rfl⟩
    intro w hw
    refine Subgroup.closure_mono hsub ?_
    rcases not_and_or.1 hz with h | h
    · exact e7_stab_e1_le h hw.1
    · exact e7_stab_e1_le h hw.2

theorem exists_conj_e7G0_mem
    {H : Subgroup (WeylGroup Tag.E7)} (h7 : 7 ∣ Nat.card H) :
    ∃ x : WeylGroup Tag.E7, x * e7G0 * x⁻¹ ∈ H := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fintype (WeylGroup Tag.E7) := Fintype.ofFinite _
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 7 h7
  have hW : Nat.card (WeylGroup Tag.E7) = 2903040 :=
    (CFSG.RankThree.Chevalley.E7_weyl_length_polynomial).2
  have hfac : (Nat.card (WeylGroup Tag.E7)).factorization 7 = 1 := by
    rw [hW]
    exact factorization_seven_e7
  let P : Sylow 7 (WeylGroup Tag.E7) := Sylow.ofCard (Subgroup.zpowers (g : WeylGroup Tag.E7))
    (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hg, hfac, pow_one])
  let P₀ : Sylow 7 (WeylGroup Tag.E7) := Sylow.ofCard (Subgroup.zpowers e7G0)
    (by rw [Nat.card_zpowers, orderOf_e7G0, hfac, pow_one])
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (WeylGroup Tag.E7) P₀ P
  refine ⟨x, ?_⟩
  have h1 : e7G0 ∈ (P₀ : Subgroup (WeylGroup Tag.E7)) := Subgroup.mem_zpowers e7G0
  have h2 : (MulAut.conj x) e7G0 ∈ ((x • P₀ : Sylow 7 (WeylGroup Tag.E7)) :
      Subgroup (WeylGroup Tag.E7)) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ h1
  rw [hx] at h2
  have h3 : (MulAut.conj x) e7G0 ∈ Subgroup.zpowers (g : WeylGroup Tag.E7) := h2
  rw [MulAut.conj_apply] at h3
  exact (Subgroup.zpowers_le.2 g.2) h3

theorem exists_conj_col_e7 {z : Fin Tag.E7.rank → ZMod 7} {x : WeylGroup Tag.E7}
    (hx : x * e7G0 * x⁻¹ ∈ dualWeylStabilizer z) :
    ∃ z' : Fin Tag.E7.rank → ZMod 7,
      (∀ y, charVal z' (x⁻¹ • y) = charVal z y) ∧ e7G0 ∈ dualWeylStabilizer z' := by
  set z' : Fin Tag.E7.rank → ZMod 7 := fun i =>
    charVal z (x • (Pi.single i 1 : Fin Tag.E7.rank → ℤ)) with hz'
  have hz'x : ∀ y, charVal z' y = charVal z (x • y) := fun y => by
    rw [charVal_smul_eq_sum]
    rfl
  have hconj : ∀ y, charVal z' (x⁻¹ • y) = charVal z y := fun y => by
    rw [hz'x, smul_inv_smul]
  refine ⟨z', hconj, ?_⟩
  have := (e7_mem_dualStab_conj hconj (x * e7G0 * x⁻¹)).1 hx
  simpa [mul_assoc] using this

theorem exists_conj_fix_e7_pair
    {z₀ z₁ : Fin Tag.E7.rank → ZMod 7}
    (h7 : 7 ∣ Nat.card ↥(dualWeylStabilizer z₀ ⊓ dualWeylStabilizer z₁)) :
    ∃ (a : WeylGroup Tag.E7) (z₀' z₁' : Fin Tag.E7.rank → ZMod 7),
      (∀ y, charVal z₀' (a • y) = charVal z₀ y) ∧ (∀ y, charVal z₁' (a • y) = charVal z₁ y) ∧
      e7G0 ∈ dualWeylStabilizer z₀' ∧ e7G0 ∈ dualWeylStabilizer z₁' := by
  obtain ⟨x, hx⟩ := exists_conj_e7G0_mem h7
  obtain ⟨z₀', h₀, g₀⟩ := exists_conj_col_e7 (Subgroup.mem_inf.1 hx).1
  obtain ⟨z₁', h₁, g₁⟩ := exists_conj_col_e7 (Subgroup.mem_inf.1 hx).2
  exact ⟨x⁻¹, z₀', z₁', h₀, h₁, g₀, g₁⟩

theorem e7_inf_le_closure_of_conj
    {a : WeylGroup Tag.E7} {z₀ z₁ z₀' z₁' : Fin Tag.E7.rank → ZMod 7}
    (h₀ : ∀ y, charVal z₀' (a • y) = charVal z₀ y) (h₁ : ∀ y, charVal z₁' (a • y) = charVal z₁ y)
    (h : dualWeylStabilizer z₀' ⊓ dualWeylStabilizer z₁' ≤
      Subgroup.closure {s | ∃ α ∈ rootKernel z₀' ∩ rootKernel z₁', s = rootReflection α}) :
    dualWeylStabilizer z₀ ⊓ dualWeylStabilizer z₁ ≤
      Subgroup.closure {s | ∃ α ∈ rootKernel z₀ ∩ rootKernel z₁, s = rootReflection α} := by
  intro y hy
  have hy' : a * y * a⁻¹ ∈ dualWeylStabilizer z₀' ⊓ dualWeylStabilizer z₁' :=
    ⟨(e7_mem_dualStab_conj h₀ y).1 (Subgroup.mem_inf.1 hy).1,
      (e7_mem_dualStab_conj h₁ y).1 (Subgroup.mem_inf.1 hy).2⟩
  have hle : Subgroup.closure
      {s | ∃ β ∈ rootKernel z₀' ∩ rootKernel z₁', s = rootReflection β} ≤
      (Subgroup.closure {s | ∃ α ∈ rootKernel z₀ ∩ rootKernel z₁, s = rootReflection α}).comap
        (MulAut.conj a⁻¹).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro _ ⟨β, ⟨hβ₀, hβ₁⟩, rfl⟩
    have hα : IsRoot Tag.E7 (a⁻¹ • β) := IsRoot.smul hβ₀.1 a⁻¹
    have hk₀ : charVal z₀ (a⁻¹ • β) = 0 := by rw [← h₀, smul_inv_smul]; exact hβ₀.2
    have hk₁ : charVal z₁ (a⁻¹ • β) = 0 := by rw [← h₁, smul_inv_smul]; exact hβ₁.2
    rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have hconj : a⁻¹ * rootReflection β * a = rootReflection (a⁻¹ • β) := by
      rw [rootReflection_smul_root a⁻¹ hβ₀.1, inv_inv]
    rw [hconj]
    exact Subgroup.subset_closure ⟨a⁻¹ • β, ⟨⟨hα, hk₀⟩, ⟨hα, hk₁⟩⟩, rfl⟩
  have h3 := hle (h hy')
  rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h3
  simpa [mul_assoc] using h3

theorem e7_inf_le_closure_of_seven_dvd
    {z₀ z₁ : Fin Tag.E7.rank → ZMod 7}
    (h7 : 7 ∣ Nat.card ↥(dualWeylStabilizer z₀ ⊓ dualWeylStabilizer z₁)) :
    dualWeylStabilizer z₀ ⊓ dualWeylStabilizer z₁ ≤
      Subgroup.closure {s | ∃ α ∈ rootKernel z₀ ∩ rootKernel z₁, s = rootReflection α} := by
  obtain ⟨a, z₀', z₁', h₀, h₁, g₀, g₁⟩ := exists_conj_fix_e7_pair h7
  exact e7_inf_le_closure_of_conj h₀ h₁ (e7_inf_le_closure_of_fix g₀ g₁)

theorem e7_inf_dualWeylStabilizer_le_closure
    (z₀ z₁ : Fin Tag.E7.rank → ZMod 7) :
    dualWeylStabilizer z₀ ⊓ dualWeylStabilizer z₁ ≤
      Subgroup.closure {s | ∃ α ∈ rootKernel z₀ ∩ rootKernel z₁, s = rootReflection α} := by
  by_cases h7 : 7 ∣ Nat.card ↥(dualWeylStabilizer z₀ ⊓ dualWeylStabilizer z₁)
  · exact e7_inf_le_closure_of_seven_dvd h7
  · haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact inf_dualWeylStabilizer_le_closure_of_card z₀ z₁ h7

end CFSG.LieType.SeitzGeneration.ExcHigh

end
