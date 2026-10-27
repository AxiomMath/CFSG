module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerActionLie
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerActionN1Common

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerAction

open CFSG.Open (StatedProj StatedSL StatedScalars)
open CFSG.LocalAnalysis.RankThreeTheoremC.NineSubgroup (dglHom coe_dglHom dglHom_mem_scalars_iff)

private noncomputable def permGL (F : Type) [Field F] (n : ℕ) :
    Equiv.Perm (Fin n) →* GL (Fin n) F :=
  (Matrix.permMatrixHom (n := Fin n) (R := F)).toHomUnits

section Aux

variable {F : Type} [Field F]

private theorem coe_permGL {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ((permGL F n σ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = σ⁻¹.permMatrix F := rfl

private theorem permGL_mul_dglHom {n : ℕ} (σ : Equiv.Perm (Fin n)) (a : Fin n → Fˣ) :
    permGL F n σ * dglHom n a = dglHom n (fun i => a (σ⁻¹ i)) * permGL F n σ := by
  refine Units.ext ?_
  simp only [Units.val_mul, coe_permGL, coe_dglHom]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
    Option.some_inj]
  by_cases h : σ⁻¹ i = j
  · subst h; simp
  · simp only [h, if_false, zero_mul, mul_zero]

private theorem permGL_conj_dglHom {n : ℕ} (σ : Equiv.Perm (Fin n)) (a : Fin n → Fˣ) :
    permGL F n σ * dglHom n a * (permGL F n σ)⁻¹ = dglHom n (fun i => a (σ⁻¹ i)) := by
  rw [mul_inv_eq_iff_eq_mul]
  exact permGL_mul_dglHom σ a

private theorem permGL_inv_conj_dglHom {n : ℕ} (σ : Equiv.Perm (Fin n)) (a : Fin n → Fˣ) :
    (permGL F n σ)⁻¹ * dglHom n a * permGL F n σ = dglHom n (fun i => a (σ i)) := by
  have := permGL_conj_dglHom (F := F) σ⁻¹ a
  rw [map_inv, inv_inv] at this
  simpa using this

private theorem exists_pGroup_diag_perm {p : ℕ} {n : ℕ} (σ : Equiv.Perm (Fin n)) (hσ : σ ^ p = 1)
    (z : Fˣ) (m : ℕ) (hz : z ^ p ^ m = 1) :
    ∃ H : Subgroup (GL (Fin n) F), IsPGroup p H ∧
      (∀ a : Fin n → Fˣ, (∀ i, a i ∈ Subgroup.zpowers z) → dglHom n a ∈ H) ∧
      permGL F n σ ∈ H := by
  set T : Subgroup (Fin n → Fˣ) := Subgroup.pi Set.univ (fun _ => Subgroup.zpowers z) with hT
  set A : Subgroup (GL (Fin n) F) := T.map (dglHom n) with hA
  have hTp : IsPGroup p T := by
    intro x
    refine ⟨m, Subtype.ext (funext fun i => ?_)⟩
    obtain ⟨k, hk⟩ :=
      Subgroup.mem_zpowers_iff.1 ((Subgroup.mem_pi Set.univ).1 x.2 i (Set.mem_univ i))
    simp only [Subgroup.coe_pow, Pi.pow_apply, Subgroup.coe_one, Pi.one_apply]
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]
  have hAp : IsPGroup p A := hTp.map _
  have hconj : ∀ τ : Equiv.Perm (Fin n), ∀ h ∈ A, permGL F n τ * h * (permGL F n τ)⁻¹ ∈ A := by
    rintro τ _ ⟨a, ha, rfl⟩
    rw [permGL_conj_dglHom]
    refine ⟨_, ?_, rfl⟩
    have ha' := (Subgroup.mem_pi Set.univ).1 (SetLike.mem_coe.1 ha)
    exact (Subgroup.mem_pi Set.univ).2 fun i hi => ha' _ (Set.mem_univ _)
  have hnorm : permGL F n σ ∈ Subgroup.normalizer (A : Set (GL (Fin n) F)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hconj σ h, fun hh => ?_⟩
    have := hconj σ⁻¹ _ hh
    simpa [map_inv, mul_assoc] using this
  have hZp : IsPGroup p (Subgroup.zpowers (permGL F n σ)) := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hσ, map_one])
  refine ⟨A ⊔ Subgroup.zpowers (permGL F n σ), hAp.to_sup_of_normal_left' hZp ?_, ?_, ?_⟩
  · rw [Subgroup.zpowers_le]
    exact hnorm
  · intro a ha
    refine Subgroup.mem_sup_left ⟨a, ?_, rfl⟩
    exact (Subgroup.mem_pi Set.univ).2 fun i _ => ha i
  · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

private def pslDiag (n : ℕ) (z : Fˣ) : Fin n → Fˣ := fun i =>
  if i.val = 0 then z else if i.val = 1 then z⁻¹ else 1

private theorem pslDiag_zero {n : ℕ} (h : 0 < n) (z : Fˣ) : pslDiag n z ⟨0, h⟩ = z := by
  simp [pslDiag]

private theorem pslDiag_one {n : ℕ} (h : 1 < n) (z : Fˣ) : pslDiag n z ⟨1, h⟩ = z⁻¹ := by
  simp [pslDiag]

private theorem pslDiag_of_two_le {n : ℕ} {i : Fin n} (h : 2 ≤ i.val) (z : Fˣ) :
    pslDiag n z i = 1 := by
  have h0 : i.val ≠ 0 := by omega
  have h1 : i.val ≠ 1 := by omega
  simp [pslDiag, h0, h1]

private theorem pslDiag_mem {n : ℕ} (z : Fˣ) (i : Fin n) :
    pslDiag n z i ∈ Subgroup.zpowers z := by
  unfold pslDiag
  split_ifs
  · exact Subgroup.mem_zpowers z
  · exact inv_mem (Subgroup.mem_zpowers z)
  · exact one_mem _

private theorem det_dglHom_pslDiag {n : ℕ} (hn : 2 ≤ n) (z : Fˣ) :
    ((dglHom n (pslDiag n z) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1 := by
  rw [coe_dglHom, Matrix.det_diagonal]
  rw [Finset.prod_eq_mul (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ (by simp [Fin.ext_iff])]
  · simp [pslDiag]
  · intro c _ hc
    have h0 : c.val ≠ 0 := fun h => hc.1 (Fin.ext h)
    have h1 : c.val ≠ 1 := fun h => hc.2 (Fin.ext h)
    simp [pslDiag, h0, h1]
  · simp
  · simp

private theorem det_permGL {n : ℕ} (σ : Equiv.Perm (Fin n)) (hσ : Equiv.Perm.sign σ = 1) :
    ((permGL F n σ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1 := by
  rw [coe_permGL, Matrix.det_permutation, Equiv.Perm.sign_inv, hσ]
  simp

private theorem comm_not_mem_scalars {n : ℕ} (σ : Equiv.Perm (Fin n)) (i0 : Fin n)
    (hn : 2 ≤ n) (hi0 : 2 ≤ i0.val) (hi3 : i0.val ≠ 3)
    (hσi0 : (σ i0).val = 0) (hσ0 : (σ ⟨0, by omega⟩).val = 1) (z : Fˣ)
    (hz : z ^ 3 ≠ 1 ∨ (z ≠ 1 ∧ 4 ≤ n)) :
    ((dglHom n (pslDiag n z) : GL (Fin n) F) * permGL F n σ)⁻¹ *
        (permGL F n σ * dglHom n (pslDiag n z)) ∉ StatedScalars (Fin n) F := by
  intro hmem
  have h1 : ((dglHom n (pslDiag n z) : GL (Fin n) F) * permGL F n σ)⁻¹ *
        (permGL F n σ * dglHom n (pslDiag n z)) =
      dglHom n (fun i => (pslDiag n z (σ i))⁻¹ * pslDiag n z i) := by
    have := permGL_inv_conj_dglHom (F := F) σ (pslDiag n z)
    calc _ = ((permGL F n σ)⁻¹ * dglHom n (pslDiag n z) * permGL F n σ)⁻¹ *
          dglHom n (pslDiag n z) := by group
      _ = _ := by
        rw [this, ← map_inv, ← map_mul]
        rfl
  rw [h1, dglHom_mem_scalars_iff] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hσ2 : ∀ j : Fin n, j ≠ i0 → j.val ≠ 0 → 2 ≤ (σ j).val := by
    intro j hj hj0
    have hne0 : (σ j).val ≠ 0 := by
      intro h
      exact hj (σ.injective (Fin.ext (h.trans hσi0.symm)))
    have hne1 : (σ j).val ≠ 1 := by
      intro h
      have := σ.injective (Fin.ext (h.trans hσ0.symm) : σ j = σ ⟨0, by omega⟩)
      exact hj0 (by rw [this])
    omega
  have hc1 := hc ⟨1, by omega⟩
  rw [pslDiag_of_two_le (hσ2 ⟨1, by omega⟩ (fun h => by rw [← h] at hi0; simp at hi0)
    (by simp)), pslDiag_one (by omega)] at hc1
  rcases hz with hz | ⟨hz1, hn4⟩
  · apply hz
    have hc0 := hc ⟨0, by omega⟩
    have hσ0' : σ ⟨0, by omega⟩ = ⟨1, by omega⟩ := Fin.ext hσ0
    rw [hσ0', pslDiag_one (by omega), pslDiag_zero (by omega)] at hc0
    rw [← hc1] at hc0
    simp at hc0
    calc z ^ 3 = z * z * z := pow_three' z
      _ = 1 := by rw [hc0]; simp
  · apply hz1
    have hc3 := hc ⟨3, by omega⟩
    rw [pslDiag_of_two_le (hσ2 ⟨3, by omega⟩ (fun h => hi3 (by rw [← h])) (by simp)),
      pslDiag_of_two_le (by simp)] at hc3
    rw [← hc1] at hc3
    simpa using hc3

private theorem orderOf_cycleRange {n : ℕ} [NeZero n] {i : Fin n} (h0 : i ≠ 0) :
    orderOf (Fin.cycleRange i) = (i : ℕ) + 1 := by
  rw [← Equiv.Perm.lcm_cycleType, Fin.cycleType_cycleRange h0]
  simp

private theorem exists_orderOf_units (F : Type) [Field F] [Finite F] {d : ℕ}
    (hd : d ∣ Nat.card F - 1) : ∃ z : Fˣ, orderOf z = d := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  rw [Nat.card_units] at hg
  exact ⟨g ^ (orderOf g / d), orderOf_pow_orderOf_div (orderOf_pos g).ne' (hg ▸ hd)⟩

private theorem exists_pslDiag_root (F : Type) [Field F] [Finite F] {n p : ℕ} (hp : p.Prime)
    (hpn : p ∣ n) (hn2 : 2 ≤ n) (hpq : p ∣ Nat.card F - 1)
    (hspec : ¬ (n = 3 ∧ p = 3 ∧ ¬ 9 ∣ Nat.card F - 1)) :
    ∃ z : Fˣ, z ^ p ^ 2 = 1 ∧ (z ^ 3 ≠ 1 ∨ (z ≠ 1 ∧ 4 ≤ n)) := by
  by_cases h3 : n = 3 ∧ p = 3
  · obtain ⟨rfl, rfl⟩ := h3
    have h9 : 9 ∣ Nat.card F - 1 := by
      by_contra h
      exact hspec ⟨rfl, rfl, h⟩
    obtain ⟨z, hz⟩ := exists_orderOf_units F h9
    refine ⟨z, ?_, Or.inl fun h => ?_⟩
    · rw [← orderOf_dvd_iff_pow_eq_one, hz]
      norm_num
    · have := orderOf_dvd_of_pow_eq_one h
      rw [hz] at this
      omega
  · obtain ⟨z, hz⟩ := exists_orderOf_units F hpq
    refine ⟨z, ?_, ?_⟩
    · rw [← orderOf_dvd_iff_pow_eq_one, hz]
      exact dvd_pow_self p two_ne_zero
    · by_cases hp3 : p = 3
      · subst hp3
        obtain ⟨k, rfl⟩ := hpn
        right
        refine ⟨fun h => ?_, by omega⟩
        rw [h, orderOf_one] at hz
        omega
      · left
        intro h
        have := orderOf_dvd_of_pow_eq_one h
        rw [hz] at this
        exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 this)

private theorem exists_noncomm_pSubgroup_psl (F : Type) [Field F] [Finite F] {n p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ n) (hn2 : 2 ≤ n) (hpq : p ∣ Nat.card F - 1)
    (hspec : ¬ (n = 3 ∧ p = 3 ∧ ¬ 9 ∣ Nat.card F - 1)) :
    ∃ H : Subgroup (StatedProj (StatedSL n F)), IsPGroup p H ∧
      ∃ a ∈ H, ∃ b ∈ H, a * b ≠ b * a := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hpn' : p ≤ n := Nat.le_of_dvd (by omega) hpn
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨z, hz1, hz2⟩ := exists_pslDiag_root F hp hpn hn2 hpq hspec
  let i0 : Fin n := ⟨p - 1, by omega⟩
  let σ : Equiv.Perm (Fin n) := Fin.cycleRange i0
  have hi0val : i0.val = p - 1 := rfl
  have hi0ne : i0 ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp only [hi0val, Fin.val_zero] at this
    omega
  have hi3 : i0.val ≠ 3 := by
    intro h
    have : p = 4 := by omega
    subst this
    norm_num at hp
  have hσp : σ ^ p = 1 := by
    have h1 : (i0 : ℕ) + 1 = p := by omega
    rw [← orderOf_dvd_iff_pow_eq_one, orderOf_cycleRange hi0ne, h1]
  have hsign : Equiv.Perm.sign σ = 1 := by
    rw [Fin.sign_cycleRange, hi0val]
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
    have : p - 1 = 2 * k := by omega
    rw [this, pow_mul]
    simp
  have hσi0 : (σ i0).val = 0 := by simp [σ]
  have hσ0 : (σ ⟨0, by omega⟩).val = 1 := by
    have hlt : (⟨0, by omega⟩ : Fin n) < i0 := by
      rw [Fin.lt_def]
      simp only [hi0val]
      omega
    exact (Fin.coe_cycleRange_of_lt hlt).trans (by simp)
  obtain ⟨H, hH, hdiag, hperm⟩ := exists_pGroup_diag_perm (F := F) σ hσp z 2 hz1
  have hdSL : dglHom n (pslDiag n z) ∈ StatedSL n F :=
    Subgroup.subset_closure (det_dglHom_pslDiag hn2 z)
  have heSL : permGL F n σ ∈ StatedSL n F := Subgroup.subset_closure (det_permGL σ hsign)
  have hdH := hdiag _ (pslDiag_mem z)
  refine ⟨(H.subgroupOf (StatedSL n F)).map (QuotientGroup.mk' _), hH.comap_subtype.map _,
    QuotientGroup.mk ⟨_, hdSL⟩, ⟨⟨_, hdSL⟩, hdH, rfl⟩, QuotientGroup.mk ⟨_, heSL⟩,
    ⟨⟨_, heSL⟩, hperm, rfl⟩, ?_⟩
  intro hcomm
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hcomm
  exact comm_not_mem_scalars σ i0 hn2 (by omega) hi3 hσi0 hσ0 z hz2
    (by simpa using Subgroup.mem_subgroupOf.1 hcomm)

end Aux

theorem n1PSL_holds : N1PSL := by
  intro K _ _ n ℓ f hmodel p hp hp2 hpn hpq hspec S hS hSi
  obtain ⟨⟨-, -, hn2, -⟩, F, _, _, hF, ⟨e⟩⟩ := hmodel
  haveI : Fact p.Prime := ⟨hp⟩
  have hpq' : p ∣ Nat.card F - 1 := by rw [hF]; exact hpq
  have hspec' : ¬ (n = 3 ∧ p = 3 ∧ ¬ 9 ∣ Nat.card F - 1) := by rw [hF]; exact hspec
  obtain ⟨H, hH, a, ha, b, hb, hab⟩ :=
    exists_noncomm_pSubgroup_psl F hp hp2 hpn hn2 hpq' hspec'
  refine not_isMulCommutative_of_noncomm_pSubgroup (H := H.map e.symm.toMonoidHom)
    (hH.map _) (a := e.symm a) (b := e.symm b) ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ ?_ hS hSi
  intro h
  exact hab (e.symm.injective (by simpa [map_mul] using h))

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerAction
