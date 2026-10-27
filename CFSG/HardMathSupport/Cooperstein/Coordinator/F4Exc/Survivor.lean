module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc.BaseChange
public import CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc.TypeBound
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.F4OffenderPair

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc

section Survivor


variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {k : Type} [Field k] [Algebra K k] [CharP k 2] {V₁ V₂ : Type} [AddCommGroup V₁] [Module k V₁]
  [AddCommGroup V₂] [Module k V₂]

theorem chi_mul_of_scalarK (ρ : Representation k (adjointGroup Tag.F4 K) V₁) {y : V₁} (hy : y ≠ 0)
    {χ : adjointGroup Tag.F4 K → k} (hH : ∀ h ∈ (DF4 K).H, ρ h y = χ h • y)
    {a b : adjointGroup Tag.F4 K} (ha : a ∈ (DF4 K).H) (hb : b ∈ (DF4 K).H) :
    χ (a * b) = χ a * χ b := by
  have h1 := hH (a * b) (mul_mem ha hb)
  rw [map_mul, Module.End.mul_apply, hH b hb, map_smul, hH a ha, smul_smul] at h1
  exact (smul_left_injective k hy h1.symm).trans (mul_comm _ _)

theorem chi_one_of_scalarK (ρ : Representation k (adjointGroup Tag.F4 K) V₁) {y : V₁} (hy : y ≠ 0)
    {χ : adjointGroup Tag.F4 K → k} (hH : ∀ h ∈ (DF4 K).H, ρ h y = χ h • y) : χ 1 = 1 := by
  have h1 := hH 1 (one_mem _)
  rw [map_one, Module.End.one_apply] at h1
  exact (smul_left_injective k hy (h1.symm.trans (one_smul k y).symm))

theorem chi_eq_on_HK (ρ₁ : Representation k (adjointGroup Tag.F4 K) V₁) {y₁ : V₁} (hy₁ : y₁ ≠ 0)
    {χ₁ : adjointGroup Tag.F4 K → k} (h₁ : ∀ h ∈ (DF4 K).H, ρ₁ h y₁ = χ₁ h • y₁)
    (ρ₂ : Representation k (adjointGroup Tag.F4 K) V₂) {y₂ : V₂} (hy₂ : y₂ ≠ 0)
    {χ₂ : adjointGroup Tag.F4 K → k} (h₂ : ∀ h ∈ (DF4 K).H, ρ₂ h y₂ = χ₂ h • y₂)
    (hd : ∀ (i : Fin Tag.F4.rank) (t : Kˣ), χ₁ (dC Tag.F4 K i t) = χ₂ (dC Tag.F4 K i t)) :
    ∀ h ∈ (DF4 K).H, χ₁ h = χ₂ h := by
  let E : Subgroup (adjointGroup Tag.F4 K) :=
    { carrier := {h | h ∈ (DF4 K).H ∧ χ₁ h = χ₂ h}
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
        rw [chi_mul_of_scalarK ρ₁ hy₁ h₁ ha.1 hb.1, chi_mul_of_scalarK ρ₂ hy₂ h₂ ha.1 hb.1,
          ha.2, hb.2]⟩
      one_mem' := ⟨one_mem _, by rw [chi_one_of_scalarK ρ₁ hy₁ h₁, chi_one_of_scalarK ρ₂ hy₂ h₂]⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by
        have e1 := chi_mul_of_scalarK ρ₁ hy₁ h₁ ha.1 (inv_mem ha.1)
        have e2 := chi_mul_of_scalarK ρ₂ hy₂ h₂ ha.1 (inv_mem ha.1)
        rw [mul_inv_cancel, chi_one_of_scalarK ρ₁ hy₁ h₁] at e1
        rw [mul_inv_cancel, chi_one_of_scalarK ρ₂ hy₂ h₂] at e2
        have h0 : χ₁ a ≠ 0 := fun h => by rw [h, zero_mul] at e1; exact zero_ne_one e1.symm
        have : χ₁ a⁻¹ = χ₂ a⁻¹ := by
          rw [ha.2] at e1 h0
          exact mul_left_cancel₀ h0 (e1.symm.trans e2)
        exact this⟩ }
  have hle : (DF4 K).H ≤ E := H_le_of_dC K fun i t => ⟨dC_mem_H i t, hd i t⟩
  exact fun h hh => (hle hh).2

theorem isChevType_congr_chi {ρ : Representation k (adjointGroup Tag.F4 K) V₁} {y : V₁}
    {χ χ' : adjointGroup Tag.F4 K → k} {J : Finset (Fin Tag.F4.rank)}
    (ht : IsChevType Tag.F4 K 2 exists_weyl_neg_F4' ρ y χ' J)
    (h : ∀ h ∈ (DF4 K).H, χ h = χ' h) : IsChevType Tag.F4 K 2 exists_weyl_neg_F4' ρ y χ J := by
  obtain ⟨h1, h2, h3, h4⟩ := ht
  refine ⟨h1, h2, fun x hx => by rw [h3 x hx, h x hx], fun i => ?_⟩
  rw [h4 i]
  refine and_congr ?_ Iff.rfl
  exact forall_congr' fun t => by rw [h _ (dC_mem_H i t)]

theorem survivor_iso {m : ℕ} {ρ : Representation k (adjointGroup Tag.F4 K) (Fin m → k)}
    (hρ : IsSimpleRep ρ) {y : Fin m → k} {χ : adjointGroup Tag.F4 K → k}
    {J : Finset (Fin Tag.F4.rank)} (ht : IsChevType Tag.F4 K 2 exists_weyl_neg_F4' ρ y χ J)
    (hS : F4Surv K χ J) :
    ∃ (j : ℕ) (β : (Fin m → k) ≃ₗ[k] (Idx26 → k)), ∀ (g : adjointGroup Tag.F4 K) (v : Fin m → k),
      β (ρ g v) = bcRep k (m26Phi K j) g (β v) := by
  classical
  obtain ⟨b, s, hs, hJ, hχ⟩ := hS
  have key : ∀ j : ℕ, nodeK j = s → (∀ (i : Fin Tag.F4.rank) (t : Kˣ),
      ∀ χK : adjointGroup Tag.F4 K → K, (∀ h ∈ (DF4 K).H, m26Phi K j h (y26 K) = χK h • y26 K) →
        χK (dC Tag.F4 K i t) = (t : K) ^ (if i = s then 2 ^ b else 0)) →
      ∃ β : (Fin m → k) ≃ₗ[k] (Idx26 → k), ∀ (g : adjointGroup Tag.F4 K) (v : Fin m → k),
        β (ρ g v) = bcRep k (m26Phi K j) g (β v) := by
    intro j hj hχK
    obtain ⟨χK, hχKH⟩ := exists_chi_m26Phi K j
    have htK := m26Phi_isChevType K j χK hχKH
    have htb := isChevType_bcRep (k := k) htK
    have hsimple := isSimpleRep_bcRep (k := k) (isSimpleRep_m26Phi K j) htK
    have hJ' : Finset.univ.erase (nodeK j) = J := by rw [hj, hJ]
    rw [hJ'] at htb
    have hH : ∀ h ∈ (DF4 K).H, χ h = (fun g => algebraMap K k (χK g)) h := by
      refine chi_eq_on_HK ρ ht.2.1 ht.2.2.1 (bcRep k (m26Phi K j)) htb.2.1 htb.2.2.1 ?_
      intro i t
      rw [hχ i t]
      simp only [hχK i t χK hχKH, map_pow]
    have htb' := isChevType_congr_chi htb hH
    obtain ⟨β, hβ⟩ := iso_of_isChevType hρ hsimple ht htb'
    exact ⟨β, hβ⟩
  rcases hs with h0 | h3
  · have hs0 : s = ⟨0, by decide⟩ := Fin.ext h0
    obtain ⟨β, hβ⟩ := key (2 * b + 1) (by rw [hs0]; simp [nodeK]) (by
      intro i t χK hχK
      have := m26Phi_chi_odd K b χK hχK i t
      rw [this]
      have : (i.val = 0) ↔ i = s := by rw [hs0]; exact ⟨fun h => Fin.ext h, fun h => by rw [h]⟩
      simp only [this])
    exact ⟨2 * b + 1, β, hβ⟩
  · have hs3 : s = j3 := Fin.ext h3
    obtain ⟨β, hβ⟩ := key (2 * b) (by rw [hs3]; simp [nodeK]) (by
      intro i t χK hχK
      have := m26Phi_chi_even K b χK hχK i t
      rw [this]
      have : (i.val = 3) ↔ i = s := by rw [hs3]; exact ⟨fun h => Fin.ext h, fun h => by rw [h]⟩
      simp only [this])
    exact ⟨2 * b, β, hβ⟩

theorem card_Idx26 : Fintype.card Idx26 = 26 := by decide

theorem survivor_fixed_bound {m : ℕ} {ρ : Representation k (adjointGroup Tag.F4 K) (Fin m → k)}
    (hρ : IsSimpleRep ρ) {y : Fin m → k} {χ : adjointGroup Tag.F4 K → k}
    {J : Finset (Fin Tag.F4.rank)} (ht : IsChevType Tag.F4 K 2 exists_weyl_neg_F4' ρ y χ J)
    (hS : F4Surv K χ J) (A : Subgroup (adjointGroup Tag.F4 K)) (hne : A ≠ ⊥)
    (hel : ∀ a ∈ A, a ^ 2 = 1) :
    m = 26 ∧ Nat.card A * Nat.card K ^ Module.finrank k (fixSub ρ A) ≤ Nat.card K ^ 25 := by
  classical
  obtain ⟨j, β, hβ⟩ := survivor_iso hρ ht hS
  refine ⟨?_, ?_⟩
  · have := β.finrank_eq
    rw [Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card, card_Idx26] at this
    exact this
  · have h1 : (fixSub ρ A).map β.toLinearMap = fixSub (bcRep k (m26Phi K j)) A := by
      ext w
      simp only [Submodule.mem_map, CFSG.Quasithin.SmithCurtis.mem_fixSub, LinearEquiv.coe_coe]
      constructor
      · rintro ⟨v, hv, rfl⟩ a ha
        rw [← hβ, hv a ha]
      · intro hw
        refine ⟨β.symm w, fun a ha => ?_, by simp⟩
        apply β.injective
        rw [hβ, LinearEquiv.apply_symm_apply, hw a ha]
    have h2 : fixSub (bcRep k (m26Phi K j)) A =
        fixK (k := k) (fun a : A => LinearMap.toMatrix' (m26Phi K j a)) := by
      ext w
      rw [CFSG.Quasithin.SmithCurtis.mem_fixSub, mem_fixK]
      constructor
      · intro h a
        have := h a a.2
        rw [bcRep_apply] at this
        exact this
      · intro h a ha
        rw [bcRep_apply]
        exact h ⟨a, ha⟩
    have h3 : fixF (fun a : A => LinearMap.toMatrix' (m26Phi K j a)) = fix26 K j A := by
      ext w
      rw [mem_fixF]
      constructor
      · intro h a ha
        have := h ⟨a, ha⟩
        simpa [LinearMap.toMatrix'_mulVec] using this
      · intro h a
        simpa [LinearMap.toMatrix'_mulVec] using h a a.2
    have hdim : Module.finrank k (fixSub ρ A) = Module.finrank K (fix26 K j A) := by
      rw [← LinearEquiv.finrank_map_eq β (fixSub ρ A), h1, h2, finrank_fixK, h3]
    have hb := (f4_26_twist_offender_bound_of_fixedSub K (fun A => rfl) j hne hel).1
    have hcard : Nat.card (fix26 K j A) = Nat.card K ^ Module.finrank K (fix26 K j A) :=
      Module.natCard_eq_pow_finrank
    rw [hcard] at hb
    rw [hdim]
    exact hb.trans (Nat.pow_le_pow_right Nat.card_pos (by omega))

end Survivor

end CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc
