module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltDataOfAlt
import CFSG.Permutation.AlternatingAutomorphism.ThreeCycle

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open Equiv

theorem hom_apply_eq_one_of_isPerfect {J : Type*} [Group J] (hJ : Group.IsPerfect J) {B : Type*}
    [CommGroup B] (f : J →* B) (j : J) : f j = 1 := by
  have h1 : commutator J ≤ f.ker := Abelianization.commutator_subset_ker f
  have h2 : commutator J = ⊤ := hJ.commutator_eq_top
  exact h1 (h2 ▸ Subgroup.mem_top j)

namespace AltFiveThreeRank

variable {α : Type*} [DecidableEq α]

theorem mem_range_subtypeCongrHom_of_forall_mem_iff (O : Finset α) {σ : Perm α}
    (h : ∀ x, x ∈ O ↔ σ x ∈ O) : σ ∈ (Perm.subtypeCongrHom fun x => x ∈ O).range := by
  refine ⟨(σ.subtypePerm fun x => (h x).symm, σ.subtypePerm fun x => not_congr (h x).symm), ?_⟩
  ext x
  by_cases hx : x ∈ O <;> simp [Perm.subtypeCongrHom, Perm.subtypeCongr, hx]

theorem card_range_subtypeCongrHom [Finite α] (O : Finset α) :
    Nat.card (Perm.subtypeCongrHom fun x => x ∈ O).range =
      (Nat.card {a // a ∈ O}).factorial * (Nat.card {a // a ∉ O}).factorial := by
  rw [← Nat.card_congr (MonoidHom.ofInjective
    (Perm.subtypeCongrHom_injective fun x => x ∈ O)).toEquiv, Nat.card_prod, Nat.card_perm,
    Nat.card_perm]

end AltFiveThreeRank

namespace D2AltModel

variable {X : Type} [Group X] {A X₀ K : Subgroup X}

section General

variable {p : ℕ} {e : K ≃* alternatingGroup (Fin (2 * p))}

theorem mem_iff_apply_mem_of_odd (M : D2AltModel p A X₀ K e) {x : X} (hx : x ∈ X₀) {k : ℕ}
    (hk : Odd k) (hxk : x ^ k = 1) (y : Fin (2 * p)) : y ∈ M.O₁ ↔ M.ι x y ∈ M.O₁ := by
  rcases M.preserves _ (Subgroup.mem_map_of_mem M.ι hx) with h | h
  · exact h y
  · exfalso
    have hex : ∀ z, z ∈ M.O₁ ↔ M.ι x z ∉ M.O₁ := fun z => (h z).trans (M.mem₂_iff _)
    have hpow : ∀ (n : ℕ) (z : Fin (2 * p)), (M.ι x ^ n) z ∈ M.O₁ ↔ (z ∈ M.O₁ ↔ Even n) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        intro z
        have h₁ := hex ((M.ι x ^ n) z)
        have h₂ := ih z
        rw [pow_succ', Perm.mul_apply, Nat.even_add_one]
        tauto
    have h₃ := hpow k y
    rw [show M.ι x ^ k = 1 by rw [← map_pow, hxk, map_one], Perm.one_apply] at h₃
    have hne : ¬ Even k := Nat.not_even_iff_odd.mpr hk
    tauto

theorem card_dvd_factorial_sq_of_odd (M : D2AltModel p A X₀ K e) {E : Subgroup X}
    (hE : E ≤ X₀) (hodd : ∀ x ∈ E, ∃ k, Odd k ∧ x ^ k = 1) :
    Nat.card E ∣ (Nat.factorial p) ^ 2 := by
  have hle : E.map M.ι ≤ (Perm.subtypeCongrHom fun x => x ∈ M.O₁).range := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨k, hk, hxk⟩ := hodd x hx
    exact AltFiveThreeRank.mem_range_subtypeCongrHom_of_forall_mem_iff M.O₁
      (M.mem_iff_apply_mem_of_odd (hE hx) hk hxk)
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [Subgroup.card_map_of_injective M.injective,
    AltFiveThreeRank.card_range_subtypeCongrHom] at hdvd
  have h₁ : Nat.card {a // a ∈ M.O₁} = p := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, M.card₁]
  have h₂ : Nat.card {a // a ∉ M.O₁} = p := by
    rw [← Nat.card_congr (Equiv.subtypeEquivRight fun a => M.mem₂_iff a), Nat.card_eq_fintype_card,
      Fintype.card_coe, M.card₂]
  rwa [h₁, h₂, ← sq] at hdvd

theorem card_dvd_factorial_sq_of_pow_three (M : D2AltModel p A X₀ K e) {E : Subgroup X}
    (hE : E ≤ X₀) (h3 : ∀ x ∈ E, x ^ 3 = 1) : Nat.card E ∣ (Nat.factorial p) ^ 2 :=
  M.card_dvd_factorial_sq_of_odd hE fun x hx => ⟨3, by decide, h3 x hx⟩

theorem pRank_three_le_two_of_not_dvd [Finite X] (M : D2AltModel p A X₀ K e)
    (h : ¬ 3 ^ 3 ∣ (Nat.factorial p) ^ 2) : Open.pRank 3 X₀ ≤ 2 := by
  apply csSup_le'
  rintro k ⟨E, hEX, hE, hcard⟩
  by_contra hk
  refine h ((pow_dvd_pow 3 (by omega : 3 ≤ k)).trans ?_)
  rw [← hcard]
  exact M.card_dvd_factorial_sq_of_pow_three hEX fun x hx => hE.2 x hx

theorem exists_three_cycles (M : D2AltModel p A X₀ K e) (hp : 5 ≤ p) :
    ∃ c : Fin 3 → alternatingGroup (Fin (2 * p)),
      (∀ i, (c i : Perm (Fin (2 * p))).IsThreeCycle) ∧
      (∀ i j, i ≠ j →
        Disjoint (c i : Perm (Fin (2 * p))).support (c j : Perm (Fin (2 * p))).support) ∧
      (c 0 : Perm (Fin (2 * p))) ∈ X₀.map M.ι ∧ (c 1 : Perm (Fin (2 * p))) ∈ X₀.map M.ι := by
  obtain ⟨t₁, ht₁, hc₁⟩ := Finset.exists_subset_card_eq (s := M.O₁) (n := 3)
    (by rw [M.card₁]; omega)
  obtain ⟨t₂, ht₂, hc₂⟩ := Finset.exists_subset_card_eq (s := M.O₂) (n := 3)
    (by rw [M.card₂]; omega)
  obtain ⟨t₃, ht₃, hc₃⟩ := Finset.exists_subset_card_eq (s := (t₁ ∪ t₂)ᶜ) (n := 3) (by
    rw [Finset.card_compl, Fintype.card_fin]
    have := Finset.card_union_le t₁ t₂
    omega)
  obtain ⟨x, hx, hxs⟩ := CFSG.AlternatingAutomorphism.exists_isThreeCycle_support_eq hc₁
  obtain ⟨y, hy, hys⟩ := CFSG.AlternatingAutomorphism.exists_isThreeCycle_support_eq hc₂
  obtain ⟨z, hz, hzs⟩ := CFSG.AlternatingAutomorphism.exists_isThreeCycle_support_eq hc₃
  have hxO : x.support ⊆ M.O₁ := by rw [hxs]; exact ht₁
  have hyO : y.support ⊆ M.O₂ := by rw [hys]; exact ht₂
  have hxy : Disjoint x.support y.support := by
    rw [hxs, hys]
    exact M.disjoint.mono ht₁ ht₂
  have hxz : Disjoint x.support z.support := by
    rw [hxs, hzs]
    exact Finset.disjoint_left.2 fun a ha hb =>
      Finset.mem_compl.1 (ht₃ hb) (Finset.mem_union_left _ ha)
  have hyz : Disjoint y.support z.support := by
    rw [hys, hzs]
    exact Finset.disjoint_left.2 fun a ha hb =>
      Finset.mem_compl.1 (ht₃ hb) (Finset.mem_union_right _ ha)
  let P : Fin 3 → Perm (Fin (2 * p)) := ![x, y, z]
  have hP : ∀ i, (P i).IsThreeCycle := by
    intro i
    fin_cases i
    exacts [hx, hy, hz]
  have hPd : ∀ i j, i ≠ j → Disjoint (P i).support (P j).support := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first
      | exact absurd rfl hij
      | exact hxy | exact hxy.symm | exact hxz | exact hxz.symm | exact hyz | exact hyz.symm
  exact ⟨fun i => ⟨P i, Perm.mem_alternatingGroup.2 (hP i).sign⟩, hP, hPd,
    M.altOn₁ (AltSurvivor.mem_altOn.2
      ⟨hx.sign, fun w hw => Perm.notMem_support.1 fun h => hw (hxO h)⟩),
    M.altOn₂ (AltSurvivor.mem_altOn.2
      ⟨hy.sign, fun w hw => Perm.notMem_support.1 fun h => hw (hyO h)⟩)⟩

theorem forall_mem_iff_of_perfect (M : D2AltModel p A X₀ K e) {J : Subgroup X} (hJX : J ≤ X₀)
    (hJ : ⁅J, J⁆ = J) {j : X} (hj : j ∈ J) (y : Fin (2 * p)) : y ∈ M.O₁ ↔ M.ι j y ∈ M.O₁ := by
  classical
  set Pr : X → Prop := fun x => ∀ z, z ∈ M.O₁ ↔ M.ι x z ∈ M.O₁ with hPr
  have hmul : ∀ x x', Pr x → Pr x' → Pr (x * x') := by
    intro x x' hx hx' z
    rw [map_mul, Perm.mul_apply, ← hx, ← hx']
  have hinv : ∀ x, Pr x → Pr x⁻¹ := by
    intro x hx z
    have h1 := hx ((M.ι x)⁻¹ z)
    have h2 : M.ι x ((M.ι x)⁻¹ z) = z := by simp
    rw [h2] at h1
    rw [map_inv]
    exact h1.symm
  have hcases : ∀ x ∈ J, Pr x ∨ ∀ z, z ∈ M.O₁ ↔ M.ι x z ∉ M.O₁ := by
    intro x hx
    rcases M.preserves _ (Subgroup.mem_map_of_mem M.ι (hJX hx)) with h | h
    · exact Or.inl h
    · refine Or.inr fun z => ?_
      rw [h z, M.mem₂_iff]
  let χ : J →* ℤˣ := MonoidHom.mk' (fun x : J => if Pr (x : X) then 1 else -1) (by
    intro a b
    rw [Subgroup.coe_mul]
    by_cases ha : Pr (a : X)
    · by_cases hb : Pr (b : X)
      · simp [ha, hb, hmul _ _ ha hb]
      · have : ¬ Pr ((a : X) * b) := fun h => hb (by simpa using hmul _ _ (hinv _ ha) h)
        simp [ha, hb, this]
    · by_cases hb : Pr (b : X)
      · have : ¬ Pr ((a : X) * b) := fun h => ha (by simpa using hmul _ _ h (hinv _ hb))
        simp [ha, hb, this]
      · have hab : Pr ((a : X) * b) := by
          rcases hcases a a.2 with h | ea
          · exact absurd h ha
          rcases hcases b b.2 with h | eb
          · exact absurd h hb
          intro z
          rw [map_mul, Perm.mul_apply]
          have := ea (M.ι b z)
          have := eb z
          tauto
        simp [ha, hb, hab])
  have hχ := hom_apply_eq_one_of_isPerfect (Subgroup.isPerfect_iff.mpr hJ) χ ⟨j, hj⟩
  by_contra hne
  have : ¬ Pr j := fun h => hne (h y)
  simp [χ, this] at hχ

theorem le_B_of_perfect [Finite X] (M : D2AltModel p A X₀ K e) {J : Subgroup X} (hJX : J ≤ X₀)
    (hJ : ⁅J, J⁆ = J) : J ≤ M.B := by
  have hP : ∀ j ∈ J, ∀ y, y ∈ M.O₁ ↔ M.ι j y ∈ M.O₁ := fun j hj =>
    M.forall_mem_iff_of_perfect hJX hJ hj
  have hperf : Group.IsPerfect J := Subgroup.isPerfect_iff.mpr hJ
  have hmem : ∀ j : J, M.ι j ∈ (Perm.subtypeCongrHom fun x => x ∈ M.O₁).range := fun j =>
    AltFiveThreeRank.mem_range_subtypeCongrHom_of_forall_mem_iff M.O₁ (hP j j.2)
  let r : J →* (Perm.subtypeCongrHom fun x => x ∈ M.O₁).range :=
    (M.ι.comp J.subtype).codRestrict _ hmem
  let ρ : J →* Perm {a // a ∈ M.O₁} × Perm {a // a ∉ M.O₁} :=
    (MonoidHom.ofInjective
      (Perm.subtypeCongrHom_injective fun x => x ∈ M.O₁)).symm.toMonoidHom.comp r
  have hρ : ∀ j : J, Perm.subtypeCongrHom (fun x => x ∈ M.O₁) (ρ j) = M.ι j := fun j =>
    congrArg Subtype.val ((MonoidHom.ofInjective
      (Perm.subtypeCongrHom_injective fun x => x ∈ M.O₁)).apply_symm_apply (r j))
  intro j hj
  have h1 : Perm.sign (ρ ⟨j, hj⟩).1 = 1 :=
    hom_apply_eq_one_of_isPerfect hperf (Perm.sign.comp ((MonoidHom.fst _ _).comp ρ)) ⟨j, hj⟩
  have h2 : Perm.sign (ρ ⟨j, hj⟩).2 = 1 := by
    have := hom_apply_eq_one_of_isPerfect hperf
      (Perm.sign.comp ((MonoidHom.snd _ _).comp ρ)) ⟨j, hj⟩
    simpa using this
  rw [mem_B_iff, ← hρ ⟨j, hj⟩]
  have hsplit : Perm.subtypeCongrHom (fun x => x ∈ M.O₁) (ρ ⟨j, hj⟩) =
      Perm.subtypeCongrHom (fun x => x ∈ M.O₁) ((ρ ⟨j, hj⟩).1, 1) *
        Perm.subtypeCongrHom (fun x => x ∈ M.O₁) (1, (ρ ⟨j, hj⟩).2) := by
    rw [← map_mul]
    simp
  rw [hsplit]
  refine Subgroup.mul_mem_sup ?_ ?_
  · rw [AltSurvivor.mem_altOn]
    refine ⟨by simp [Perm.subtypeCongrHom]; convert h1, fun x hx => ?_⟩
    simp [Perm.subtypeCongrHom, Perm.subtypeCongr, hx]
  · rw [AltSurvivor.mem_altOn]
    refine ⟨by simp [Perm.subtypeCongrHom]; convert h2, fun x hx => ?_⟩
    have hx' : x ∈ M.O₁ := by
      by_contra hx1
      exact hx ((M.mem₂_iff x).mpr hx1)
    simp [Perm.subtypeCongrHom, Perm.subtypeCongr, hx']

end General

theorem pRank_three_le_two [Finite X] {e : K ≃* alternatingGroup (Fin (2 * 5))}
    (M : D2AltModel 5 A X₀ K e) : Open.pRank 3 X₀ ≤ 2 :=
  M.pRank_three_le_two_of_not_dvd (by decide)

end D2AltModel

end CFSG.AGLEmbeddingD2
