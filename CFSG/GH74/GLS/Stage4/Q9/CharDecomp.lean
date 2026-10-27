module

public import CFSG.CharacterTheory.DihedralTIFusion.InductionIsometry
public import CFSG.CharacterTheory.Blocks.NormTwoNonprincipal
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.Orthogonality
public import CFSG.CharacterTheory.Blocks.NormTwoConnector

public section

open scoped BigOperators Classical

namespace CFSG.GH74.GLS.Stage4.Q9

open CFSG.TwoRankLowerBound.Helpers

theorem decomp_character_involution_int {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) {z : G} (hz : z ^ 2 = 1) :
    ∃ a : ℤ, ρ.character z = a ∧ |a| ≤ (Module.finrank ℂ V : ℤ) := by
  set T : Module.End ℂ V := ρ z with hT
  have hsq : T * T = 1 := by
    rw [hT, ← map_mul, ← pow_two, hz, map_one]
  set P : Module.End ℂ V := (2 : ℂ)⁻¹ • (1 - T) with hP
  have hproduct : (1 - T) * (1 - T) = (2 : ℂ) • (1 - T) := by
    calc
      (1 - T) * (1 - T) = 1 - T - T + T * T := by noncomm_ring
      _ = (2 : ℂ) • (1 - T) := by rw [hsq]; module
  have hidem : IsIdempotentElem P := by
    change P * P = P
    rw [hP, smul_mul_assoc, mul_smul_comm, hproduct, smul_smul, smul_smul]
    congr 1
    field_simp
  have htrace : LinearMap.trace ℂ V P = (Module.finrank ℂ (LinearMap.range P) : ℂ) :=
    (LinearMap.IsIdempotentElem.isProj_range P hidem).trace
  have htrace' : LinearMap.trace ℂ V P =
      (2 : ℂ)⁻¹ * ((Module.finrank ℂ V : ℂ) - ρ.character z) := by
    rw [hP, map_smul, map_sub, LinearMap.trace_one, smul_eq_mul]
    rfl
  have hle : Module.finrank ℂ (LinearMap.range P) ≤ Module.finrank ℂ V := Submodule.finrank_le _
  refine ⟨(Module.finrank ℂ V : ℤ) - 2 * (Module.finrank ℂ (LinearMap.range P) : ℤ), ?_, ?_⟩
  · push_cast
    have h2 := htrace.symm.trans htrace'
    linear_combination 2 * h2
  · rw [abs_le]
    constructor <;> omega

theorem decomp_one_mem_blocksIrr (G : Type) [Group G] : (1 : G → ℂ) ∈ BlocksIrr G := by
  rw [blocksIrr_eq_irreducible_characters]
  exact ⟨principalFiniteComplexRepresentation G,
    principalFiniteComplexRepresentation_isIrreducible G,
    principalFiniteComplexRepresentation_character G⟩

theorem decomp_irr_degree {G : Type} [Group G] {Ψ : G → ℂ} (hΨ : Ψ ∈ BlocksIrr G) :
    ∃ n : ℕ, 1 ≤ n ∧ Ψ 1 = n := by
  have hpos : 0 < (Ψ 1).re := blocksIrr_identity_re_pos ⟨Ψ, hΨ⟩
  obtain ⟨V, _, _, _, ρ, -, rfl⟩ := hΨ
  refine ⟨Module.finrank ℂ V, ?_, Representation.char_one ρ⟩
  rw [Representation.char_one, Complex.natCast_re] at hpos
  exact_mod_cast hpos

theorem decomp_irr_involution {G : Type} [Group G] {z : G} (hz : z ^ 2 = 1) {Ψ : G → ℂ}
    (hΨ : Ψ ∈ BlocksIrr G) :
    ∃ (x : ℕ) (a : ℤ), 1 ≤ x ∧ Ψ 1 = x ∧ Ψ z = a ∧ |a| ≤ (x : ℤ) := by
  obtain ⟨x, hx, hΨx⟩ := decomp_irr_degree hΨ
  obtain ⟨V, _, _, _, ρ, -, rfl⟩ := hΨ
  obtain ⟨a, ha, hbound⟩ := decomp_character_involution_int ρ hz
  have hxd : x = Module.finrank ℂ V := by
    have h := hΨx.symm.trans (Representation.char_one ρ)
    exact_mod_cast h
  refine ⟨x, a, hx, hΨx, ha, ?_⟩
  rw [hxd]
  exact hbound

theorem decomp_norm_two {G : Type} [Group G] [Fintype G] {f : G → ℂ} (hf : f ∈ BlocksVChar G)
    (hnorm : BlocksInnerProduct f f = 2) (hdeg : f 1 = -1) :
    ∃ (Ψ Φ : G → ℂ) (x : ℕ), Ψ ∈ BlocksIrr G ∧ Φ ∈ BlocksIrr G ∧ Ψ ≠ Φ ∧ f = Ψ - Φ ∧
      Ψ 1 = x ∧ Φ 1 = (x : ℂ) + 1 ∧ 1 ≤ x := by
  obtain ⟨χ, ψ, ε, η, hne, hε, hη, hexp⟩ := blocksVChar_norm_two_signed_irreducibles hf hnorm
  obtain ⟨d₁, hd₁, hχd⟩ := decomp_irr_degree χ.2
  obtain ⟨d₂, hd₂, hψd⟩ := decomp_irr_degree ψ.2
  have hid : (-1 : ℂ) = (ε : ℂ) * d₁ + (η : ℂ) * d₂ := by
    have h := congrFun hexp 1
    rw [hdeg, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul] at h
    change _ = (ε : ℂ) * (χ : G → ℂ) 1 + (η : ℂ) * (ψ : G → ℂ) 1 at h
    rw [hχd, hψd] at h
    exact h
  have hid' : (-1 : ℤ) = ε * d₁ + η * d₂ := by exact_mod_cast hid
  rcases hε with rfl | rfl <;> rcases hη with rfl | rfl
  · omega
  · refine ⟨χ, ψ, d₁, χ.2, ψ.2, fun h => hne (Subtype.ext h), ?_, hχd, ?_, hd₁⟩
    · simpa only [Int.cast_one, one_smul, Int.cast_neg, neg_smul, sub_eq_add_neg] using hexp
    · rw [hψd]
      exact_mod_cast (by omega : (d₂ : ℤ) = d₁ + 1)
  · refine ⟨ψ, χ, d₂, ψ.2, χ.2, fun h => hne (Subtype.ext h.symm), ?_, hψd, ?_, hd₂⟩
    · simpa only [Int.cast_one, one_smul, Int.cast_neg, neg_smul, neg_add_eq_sub] using hexp
    · rw [hχd]
      exact_mod_cast (by omega : (d₁ : ℤ) = d₂ + 1)
  · omega

theorem decomp_ne_principal {G : Type} [Group G] [Fintype G] {Ψ Φ : G → ℂ}
    (hΨ : Ψ ∈ BlocksIrr G) (hΦ : Φ ∈ BlocksIrr G) (hne : Ψ ≠ Φ)
    (hpair : BlocksInnerProduct (Ψ - Φ) 1 = 0) : Ψ ≠ 1 ∧ Φ ≠ 1 := by
  have hΨp : BlocksInnerProduct Ψ 1 = if Ψ = 1 then 1 else 0 :=
    blocksInnerProduct_irreducible_principal ⟨Ψ, hΨ⟩
  have hΦp : BlocksInnerProduct Φ 1 = if Φ = 1 then 1 else 0 :=
    blocksInnerProduct_irreducible_principal ⟨Φ, hΦ⟩
  have hsub : BlocksInnerProduct (Ψ - Φ) 1 = BlocksInnerProduct Ψ 1 - BlocksInnerProduct Φ 1 := by
    simp only [BlocksInnerProduct, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, mul_sub]
  have hpair' : (if Ψ = 1 then (1 : ℂ) else 0) - (if Φ = 1 then 1 else 0) = 0 := by
    rw [← hΨp, ← hΦp, ← hsub]
    exact hpair
  have hΨ1 : Ψ ≠ 1 := by
    intro hΨ1
    have hΦ1 : Φ ≠ 1 := fun hΦ1 => hne (hΨ1.trans hΦ1.symm)
    norm_num [hΨ1, hΦ1] at hpair'
  have hΦ1 : Φ ≠ 1 := by
    intro hΦ1
    norm_num [hΦ1, hΨ1] at hpair'
  exact ⟨hΨ1, hΦ1⟩

theorem decomp_norm_three {G : Type} [Group G] [Fintype G] {Θ : G → ℂ} (hΘ : Θ ∈ BlocksVChar G)
    (hnorm : BlocksInnerProduct Θ Θ = 3) (hprin : BlocksInnerProduct Θ 1 = 1)
    (hdeg : Θ 1 = 0) :
    ∃ (Ψ Φ : G → ℂ) (x : ℕ), Ψ ∈ BlocksIrr G ∧ Φ ∈ BlocksIrr G ∧ Ψ ≠ Φ ∧ Ψ ≠ 1 ∧ Φ ≠ 1 ∧
      Θ = 1 + Ψ - Φ ∧ Ψ 1 = x ∧ Φ 1 = (x : ℂ) + 1 ∧ 1 ≤ x := by
  have h1 : (1 : G → ℂ) ∈ BlocksVChar G := blocksVChar_one G
  have hf : Θ - 1 ∈ BlocksVChar G := (BlocksVChar G).sub_mem hΘ h1
  have h11 : BlocksInnerProduct (1 : G → ℂ) 1 = 1 := by
    have h := blocksInnerProduct_irreducible_principal ⟨1, decomp_one_mem_blocksIrr G⟩
    simpa using h
  have hΘ1 : characterPairing Θ 1 = 1 := by
    rw [← blocksInnerProduct_eq_characterPairing Θ h1]
    exact hprin
  have hff : BlocksInnerProduct (Θ - 1) (Θ - 1) = 2 := by
    rw [blocksInnerProduct_eq_characterPairing _ hf, characterPairing_sub_left,
      characterPairing_sub_right, characterPairing_sub_right, characterPairing_comm 1 Θ, hΘ1,
      ← blocksInnerProduct_eq_characterPairing Θ hΘ, hnorm,
      ← blocksInnerProduct_eq_characterPairing 1 h1, h11]
    norm_num
  have hf1 : (Θ - 1) 1 = -1 := by
    simp [hdeg]
  obtain ⟨Ψ, Φ, x, hΨ, hΦ, hne, hfeq, hΨx, hΦx, hx⟩ := decomp_norm_two hf hff hf1
  have hΘeq : Θ = 1 + Ψ - Φ := by
    funext g
    have h := congrFun hfeq g
    simp only [Pi.sub_apply, Pi.one_apply, Pi.add_apply] at h ⊢
    linear_combination h
  have hpair : BlocksInnerProduct (Ψ - Φ) 1 = 0 := by
    rw [← hfeq]
    have h : BlocksInnerProduct (Θ - 1) 1 =
        BlocksInnerProduct Θ 1 - BlocksInnerProduct (1 : G → ℂ) 1 := by
      simp only [BlocksInnerProduct, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, mul_sub]
    rw [h, hprin, h11, sub_self]
  obtain ⟨hΨ1, hΦ1⟩ := decomp_ne_principal hΨ hΦ hne hpair
  exact ⟨Ψ, Φ, x, hΨ, hΦ, hne, hΨ1, hΦ1, hΘeq, hΨx, hΦx, hx⟩

open CFSG.Theory.Character in
theorem decomp_exists_index {G : Type} [Group G] [Finite G] {ι : Type*} [Fintype ι]
    {χ : ι → ConjClassFunction G} (hχ : IsCompleteIrreducibleCharacterFamily χ) {Ψ : G → ℂ}
    (hΨ : Ψ ∈ BlocksIrr G) : ∃ i, ∀ g : G, χ i (ConjClasses.mk g) = Ψ g := by
  obtain ⟨V, _, _, _, ρ, hρ, rfl⟩ := hΨ
  obtain ⟨i, hi⟩ := hχ.2.1 _ (isIrreducibleCharacter_characterClassFunction ρ hρ)
  exact ⟨i, fun g => by rw [hi]; rfl⟩

theorem decomp_sum_bound {G : Type} [Group G] [Finite G] (z : G) {Ψ Φ : G → ℂ}
    (hΨ : Ψ ∈ BlocksIrr G) (hΦ : Φ ∈ BlocksIrr G) (hΨΦ : Ψ ≠ Φ) (hΨ1 : Ψ ≠ 1) (hΦ1 : Φ ≠ 1) :
    1 + Complex.normSq (Ψ z) + Complex.normSq (Φ z) ≤
      (Nat.card {x : G // x * z = z * x} : ℝ) := by
  obtain ⟨ι, hι, χ, hχ, horth⟩ := CFSG.Theory.Character.second_orthogonality (G := G)
  obtain ⟨i₀, h₀⟩ := decomp_exists_index hχ (decomp_one_mem_blocksIrr G)
  obtain ⟨i₁, h₁⟩ := decomp_exists_index hχ hΨ
  obtain ⟨i₂, h₂⟩ := decomp_exists_index hχ hΦ
  have h01 : i₀ ≠ i₁ := by
    rintro rfl
    exact hΨ1 (funext fun g => (h₁ g).symm.trans (h₀ g))
  have h02 : i₀ ≠ i₂ := by
    rintro rfl
    exact hΦ1 (funext fun g => (h₂ g).symm.trans (h₀ g))
  have h12 : i₁ ≠ i₂ := by
    rintro rfl
    exact hΨΦ (funext fun g => (h₁ g).symm.trans (h₂ g))
  have hsum := (horth z z).1 rfl
  have hre : ∑ i, Complex.normSq (χ i (ConjClasses.mk z)) =
      (Nat.card {x : G // x * z = z * x} : ℝ) := by
    have h := congrArg Complex.re hsum
    rw [Complex.re_sum, Complex.natCast_re] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
  have hsub : ({i₀, i₁, i₂} : Finset ι) ⊆ Finset.univ := Finset.subset_univ _
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun i => Complex.normSq (χ i (ConjClasses.mk z))) (fun i _ _ => Complex.normSq_nonneg _)
  rw [hre, Finset.sum_insert (by simp [h01, h02]), Finset.sum_insert (by simp [h12]),
    Finset.sum_singleton, h₀ z, h₁ z, h₂ z] at hle
  simpa [add_assoc] using hle

theorem decomp_main {G : Type} [Group G] [Fintype G] (C : Subgroup G) (S : Set G)
    (hTI : IsTISubset S C) {z : G} (hz2 : orderOf z = 2) (hzS : z ∈ S)
    (hC : C = Subgroup.centralizer ({z} : Set G))
    (θ : C → ℂ) (hθ : θ ∈ BlocksVChar C) (hθS : ∀ c : C, (c : G) ∉ S → θ c = 0)
    (hθθ : BlocksInnerProduct θ θ = 3) (hθ1 : BlocksInnerProduct θ 1 = 1)
    (hθone : θ 1 = 0) (hθz : ∀ h : C, (h : G) = z → θ h = 0) :
    ∃ (Ψ Φ : G → ℂ) (x : ℕ) (a : ℤ), Ψ ∈ BlocksIrr G ∧ Φ ∈ BlocksIrr G ∧ Ψ ≠ Φ ∧ Ψ ≠ 1 ∧
      Φ ≠ 1 ∧ inducedFunction C θ = 1 + Ψ - Φ ∧
      Ψ 1 = x ∧ Φ 1 = (x : ℂ) + 1 ∧ Ψ z = a ∧ Φ z = (a : ℂ) + 1 ∧ 1 ≤ x ∧ |a| ≤ (x : ℤ) ∧
      1 + (a + 1) ^ 2 + a ^ 2 ≤ (Nat.card C : ℤ) := by
  have hclass : BlocksIsClassFunction θ := blocksVChar_isClassFunction hθ
  obtain ⟨hΘv, -, hΘΘ, hΘ1⟩ :=
    CFSG.DihedralTIFusion.supported_virtual_induction_data hTI hθ hθS
  obtain ⟨-, hΘS, -⟩ :=
    CFSG.DihedralTIFusion.ti_supported_induction_isometry hTI hclass hclass hθS hθS
  rw [hθθ] at hΘΘ
  rw [hθ1] at hΘ1
  have hmemC : ∀ x : G, x ∈ C ↔ z * x = x * z := by
    intro x
    rw [hC, Subgroup.mem_centralizer_iff]
    simp
  have hzC : z ∈ C := (hmemC z).mpr rfl
  have hΘz : inducedFunction C θ z = 0 := by
    have h := hΘS ⟨z, hzC⟩ hzS
    exact h.trans (hθz ⟨z, hzC⟩ rfl)
  have hΘ0 : inducedFunction C θ 1 = 0 := by
    simp only [inducedFunction, mul_one, inv_mul_cancel, C.one_mem, ↓reduceDIte]
    change (Nat.card C : ℂ)⁻¹ * ∑ _x : G, θ 1 = 0
    simp only [hθone, Finset.sum_const_zero, mul_zero]
  obtain ⟨Ψ, Φ, x, hΨ, hΦ, hΨΦ, hΨ1, hΦ1, hΘeq, hΨx, hΦx, hx⟩ :=
    decomp_norm_three hΘv hΘΘ hΘ1 hΘ0
  have hz : z ^ 2 = 1 := by
    rw [← hz2]
    exact pow_orderOf_eq_one z
  obtain ⟨x', a, hx', hΨx', hΨz, ha⟩ := decomp_irr_involution hz hΨ
  have hxx : x' = x := by
    have h := hΨx'.symm.trans hΨx
    exact_mod_cast h
  subst hxx
  have hΦz : Φ z = (a : ℂ) + 1 := by
    have h := congrFun hΘeq z
    rw [hΘz, Pi.sub_apply, Pi.add_apply, Pi.one_apply, hΨz] at h
    linear_combination h
  have hcard : Nat.card {y : G // y * z = z * y} = Nat.card C := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun y => ?_)
    rw [hmemC y]
    exact eq_comm
  have hbound := decomp_sum_bound z hΨ hΦ hΨΦ hΨ1 hΦ1
  rw [hcard, hΨz, hΦz] at hbound
  have hn1 : Complex.normSq (a : ℂ) = (a : ℝ) ^ 2 := by
    rw [← Complex.ofReal_intCast, Complex.normSq_ofReal]
    ring
  have hn2 : Complex.normSq ((a : ℂ) + 1) = ((a : ℝ) + 1) ^ 2 := by
    have h : ((a : ℂ) + 1) = (((a : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [h, Complex.normSq_ofReal]
    ring
  rw [hn1, hn2] at hbound
  refine ⟨Ψ, Φ, x', a, hΨ, hΦ, hΨΦ, hΨ1, hΦ1, hΘeq, hΨx, hΦx, hΨz, hΦz, hx, ha, ?_⟩
  have hbound' : (((1 + (a + 1) ^ 2 + a ^ 2 : ℤ)) : ℝ) ≤ (Nat.card C : ℝ) := by
    push_cast
    linarith
  exact_mod_cast hbound'

theorem q9_decomp {G : Type} [Group G] [Fintype G] (C : Subgroup G) [Fintype C] (S : Set G)
    (hTI : IsTISubset S C) {z : G} (hz2 : orderOf z = 2) (hzS : z ∈ S)
    (hC : C = Subgroup.centralizer ({z} : Set G))
    (θ : C → ℂ) (hθ : θ ∈ BlocksVChar C) (hθS : ∀ c : C, (c : G) ∉ S → θ c = 0)
    (hθθ : BlocksInnerProduct θ θ = 3) (hθ1 : BlocksInnerProduct θ 1 = 1)
    (hθone : θ 1 = 0) (hθz : ∀ h : C, (h : G) = z → θ h = 0) :
    ∃ (Ψ Φ : G → ℂ) (x : ℕ) (a : ℤ), Ψ ∈ BlocksIrr G ∧ Φ ∈ BlocksIrr G ∧ Ψ ≠ Φ ∧ Ψ ≠ 1 ∧
      Φ ≠ 1 ∧ inducedFunction C θ = 1 + Ψ - Φ ∧
      Ψ 1 = x ∧ Φ 1 = (x : ℂ) + 1 ∧ Ψ z = a ∧ Φ z = (a : ℂ) + 1 ∧ 1 ≤ x ∧ |a| ≤ (x : ℤ) ∧
      1 + (a + 1) ^ 2 + a ^ 2 ≤ (Nat.card C : ℤ) :=
  decomp_main C S hTI hz2 hzS hC θ hθ hθS (by convert hθθ) (by convert hθ1) hθone hθz

end CFSG.GH74.GLS.Stage4.Q9
