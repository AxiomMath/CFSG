module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcCore
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcInner
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2E6Inner

public noncomputable section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.Exc

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.ComponentClassification.CatLeafProof

variable {τ : Tag}

theorem eq_one_of_card_eq_three {K : Type} [Field K] (hK3 : Nat.card K = 3) (φ : K ≃+* K) :
    φ = 1 := by
  obtain ⟨m, hm, hφ⟩ := exists_lt_apply_eq_pow Nat.prime_three le_rfl (by rw [hK3, pow_one]) φ
  have hm0 : m = 0 := by omega
  refine RingEquiv.ext fun s => ?_
  rw [hφ, hm0, pow_zero, pow_one]
  rfl

theorem ringChar_ne_two_of_card_eq_three {K : Type} [Field K] (hK3 : Nat.card K = 3) :
    ringChar K ≠ 2 := by
  have : CharP K 3 := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_three le_rfl (by rw [hK3, pow_one])
  rw [ringChar.eq K 3]
  decide

theorem mem_range_conj_of_uniqueFieldNormalForm_three
    {K : Type} [Field K] (hK3 : Nat.card K = 3) (hNF : UniqueFieldNormalForm τ K)
    (r : MulAut (adjointGroup τ K)) :
    r ∈ (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range := by
  obtain ⟨⟨g, φ⟩, hgφ, -⟩ := hNF r
  have hgφ' : ∀ h : adjointGroup τ K, (r h : ModGL τ K) = (g : ModGL τ K) *
      Units.map (entrywiseHom φ.toRingHom) (h : ModGL τ K) * (g : ModGL τ K)⁻¹ := hgφ
  have hφ := eq_one_of_card_eq_three hK3 φ
  subst hφ
  refine ⟨g, MulEquiv.ext fun h => Subtype.ext ?_⟩
  have hid : Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) (h : ModGL τ K) = h :=
    Units.ext (entrywise_id _)
  rw [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hgφ' h, hid]

theorem outerCoreAt_toral_three
    (hτ : τ = .F4 ∨ τ = .E8) {K : Type} [Field K] [Finite K] (hK3 : Nat.card K = 3)
    {c : Fin τ.rank → Kˣ} (hc : ∀ i, c i = 1 ∨ c i = -1) {i₀ : MulAut (adjointGroup τ K)}
    (hi₀ : ∀ h : adjointGroup τ K,
      (i₀ h : ModGL τ K) = rootDiagUnit τ c * h * (rootDiagUnit τ c)⁻¹) :
    OuterCoreAt i₀ := by
  classical
  have : Finite (ModGL τ K) := finite_modGL
  have hK2 := ringChar_ne_two_of_card_eq_three hK3
  have hNF : UniqueFieldNormalForm τ K := by
    rcases hτ with rfl | rfl
    · exact (odd_F4_and_nonexceptional_G2_automorphism_normal_form Nat.prime_three (by decide)
        le_rfl K (by rw [hK3, pow_one]) .F4 (Or.inl rfl)).1
    · exact uniqueFieldNormalForm_E8 K
  have hinn := mem_range_conj_of_uniqueFieldNormalForm_three hK3 hNF
  have hle : toralCentralizer τ K c ≤ adjointGroup τ K := inf_le_left
  refine Exc.outerCoreAt_of_pPrimeCore center_adjointGroup_eq_bot
    (F := (toralCentralizer τ K c).subgroupOf (adjointGroup τ K)) (fun s => ?_) ?_
    fun a b _ _ => mul_mem (mul_mem (mul_mem (hinn a) (hinn b)) (inv_mem (hinn a)))
      (inv_mem (hinn b))
  · rw [Subgroup.mem_subgroupOf, mem_toralCentralizer, ← Subtype.coe_inj, hi₀]
    exact ⟨fun h => ⟨s.2, h⟩, fun h => h.2⟩
  · refine Exc.pPrimeCore_eq_bot_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle) ?_
    by_cases hc1 : c = 1
    · subst hc1
      have htop : toralCentralizer τ K 1 = adjointGroup τ K := by
        ext g
        rw [mem_toralCentralizer, rootDiagUnit_one, one_mul, inv_one, mul_one]
        exact ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩
      obtain ⟨hsimp, hnab, -⟩ := odd_pinned_Chevalley_p_components τ K hK2
      exact Exc.pPrimeCore_eq_bot_of_mulEquiv (MulEquiv.subgroupCongr htop)
        (Exc.pPrimeCore_eq_bot_of_isSimpleGroup hnab)
    · rcases hτ with rfl | rfl
      · exact pPrimeCore_toralCentralizer_F4 hK2 hc hc1
      · exact pPrimeCore_toralCentralizer_E8 hK2 hc hc1

theorem innerDiagThreeCoreInput_F4_E8
    (hτ : τ = .F4 ∨ τ = .E8) : InnerDiagThreeCoreInput τ := by
  intro K _ _ hK3 α hα _ g a hαg
  have hKodd : Odd (Nat.card K) := by
    rw [hK3]
    decide
  have hτ' : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8 :=
    hτ.elim (fun h => Or.inr (Or.inl h)) fun h => Or.inr (Or.inr (Or.inr h))
  exact outerCoreAt_innerDiag_of_toral hτ' hKodd
    (fun c hc i₀ hi₀ => outerCoreAt_toral_three hτ hK3 hc hi₀) hαg hα

theorem mem_range_conj_E6_three
    {K : Type} [Field K] [Finite K] (hK3 : Nat.card K = 3) (r : MulAut (adjointGroup .E6 K))
    (hr : Odd (orderOf r)) :
    r ∈ (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hKodd : Odd (Nat.card K) := by
    rw [hK3]
    decide
  have hcube : ∀ u : Kˣ, u ^ (3 : ℤ) = u := by
    intro u
    refine Units.ext ?_
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, Units.val_pow_eq_pow_val,
      show (3 : ℕ) = Fintype.card K by rw [← Nat.card_eq_fintype_card, hK3],
      FiniteField.pow_card]
  have hda : ∀ a : Fin Tag.E6.rank → Kˣ, rootDiagUnit .E6 a ∈ adjointGroup .E6 K := by
    intro a
    rw [rootDiagUnit_eq_list_prod_torusElt_adjugate (u := a) fun i => ?_]
    · exact Subgroup.list_prod_mem _ fun x hx => by
        obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
        exact torusElt_mem_adjointGroup j _
    · rw [Matrix.det_transpose, det_cartan_E6]
      exact hcube (a i)
  obtain ⟨g, a, φ, hgaφ⟩ := exists_normalForm_of_odd (Or.inr (Or.inr (Or.inl rfl))) hKodd
    (fun h => absurd h (by decide)) r hr
  have hφ := eq_one_of_card_eq_three hK3 φ
  subst hφ
  refine ⟨⟨_, mul_mem g.2 (hda a)⟩, MulEquiv.ext fun h => Subtype.ext ?_⟩
  have hid : Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) (h : ModGL .E6 K) = h :=
    Units.ext (entrywise_id _)
  change (g : ModGL .E6 K) * rootDiagUnit .E6 a * h * ((g : ModGL .E6 K) * rootDiagUnit .E6 a)⁻¹ =
    (r h : ModGL .E6 K)
  rw [hgaφ h, hid]
  group

theorem innerDiagThreeCoreInput_E6 :
    InnerDiagThreeCoreInput .E6 := by
  intro K _ _ hK3 α hα hα1 g a hαg
  classical
  have : Finite (ModGL Tag.E6 K) := finite_modGL
  have hK2 := ringChar_ne_two_of_card_eq_three hK3
  have hKodd : Odd (Nat.card K) := by
    rw [hK3]
    decide
  have hinn := mem_range_conj_E6_three hK3
  have hcore : ∀ m : Fin Tag.E6.rank → Bool,
      Burgoyne.E2.BurgCoreFor (rootDiagAut .E6 K (bitsTuple m)) →
        OuterCoreAt (rootDiagAut .E6 K (bitsTuple m)) := fun m h =>
    Exc.outerCoreAt_of_pPrimeCore center_adjointGroup_eq_bot
      (F := FixedCommutingProduct.fixedSubgroup _) (fun _ => Iff.rfl) h.1
      fun a b ha hb => mul_mem (mul_mem (mul_mem (hinn a ha) (hinn b hb)) (inv_mem (hinn a ha)))
        (inv_mem (hinn b hb))
  obtain ⟨ψ, b, hb, hψ⟩ := Burgoyne.E2.exists_conj_eq_rootDiagAut_of_innerDiagonal
    (Or.inr (Or.inr (Or.inl rfl))) hKodd hαg hα
  obtain ⟨ρ, hρ, w, hw, -⟩ := exists_conj_toralCentralizer_of_orbitCheck hK2 e6SignOrbit_check hb
  obtain ⟨n, hn⟩ := Burgoyne.E2.exists_conj_rootDiagAut_of_rootChar hw
  have hconj : ((MulAut.conj n)⁻¹ * ψ) * α * ((MulAut.conj n)⁻¹ * ψ)⁻¹ =
      rootDiagAut .E6 K (bitsTuple (listMask (e6SignReps.getD ρ []))) := by
    rw [show ((MulAut.conj n)⁻¹ * ψ) * α * ((MulAut.conj n)⁻¹ * ψ)⁻¹ =
      (MulAut.conj n)⁻¹ * (ψ * α * ψ⁻¹) * MulAut.conj n by group, hψ, hn]
    group
  refine outerCoreAt_of_conj hconj ?_
  rw [Burgoyne.E2.length_e6SignReps] at hρ
  interval_cases ρ
  ·
    exfalso
    have h1 : rootDiagAut .E6 K (bitsTuple (listMask (τ := .E6) (e6SignReps.getD 0 []))) = 1 := by
      rw [Burgoyne.E2.listMask_e6SignReps_zero]
      have : bitsTuple (K := K) (fun _ : Fin (Tag.rank .E6) => false) = 1 := by
        funext j
        simp [bitsTuple]
      rw [this]
      exact (rootDiagAutHom .E6 K).map_one
    rw [h1] at hconj
    apply hα1
    calc α = ((MulAut.conj n)⁻¹ * ψ)⁻¹ * (((MulAut.conj n)⁻¹ * ψ) * α *
          ((MulAut.conj n)⁻¹ * ψ)⁻¹) * ((MulAut.conj n)⁻¹ * ψ) := by group
      _ = 1 := by rw [hconj]; group
  · rw [Burgoyne.E2.listMask_e6SignReps_one]
    exact hcore _ (Burgoyne.E2.burgCoreFor_E6_t1_three hK3)
  · rw [Burgoyne.E2.listMask_e6SignReps_two]
    exact hcore _ (Burgoyne.E2.burgCoreFor_E6_t2 hK2)

end CFSG.ComponentClassification.Foote5.OddLieCore.Exc
