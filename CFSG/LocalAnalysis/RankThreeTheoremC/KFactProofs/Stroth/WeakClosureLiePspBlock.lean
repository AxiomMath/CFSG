module

public import CFSG.GroupTheory.WeirSylow.Symplectic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Open CFSG.GroupTheory.WeirSylow Module

private theorem spBlock_exists_hom {G : Type*} [Group G] {H : Subgroup G} {g : G} (hg : g ∈ H)
    {n : ℕ} [NeZero n] (hn : orderOf g = n) :
    ∃ ρ : Multiplicative (ZMod n) →* H, Function.Injective ρ ∧
      ∀ c, ((ρ c : H) : G) ∈ Subgroup.zpowers g := by
  have hcard : Nat.card (Multiplicative (ZMod n)) = Nat.card (Subgroup.zpowers g) := by
    rw [Nat.card_zpowers, hn, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  let e := mulEquivOfCyclicCardEq hcard
  exact ⟨(Subgroup.inclusion (Subgroup.zpowers_le.2 hg)).comp e.toMonoidHom,
    (Subgroup.inclusion_injective (Subgroup.zpowers_le.2 hg)).comp e.injective,
    fun c => (e c).2⟩

private theorem spBlock_conj_inv_of_mem {G : Type*} [Group G] {J g : G}
    (hJ : J * g * J⁻¹ = g⁻¹) {x : G} (hx : x ∈ Subgroup.zpowers g) :
    J * x * J⁻¹ = x⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  rw [← conj_zpow, hJ, inv_zpow]

private theorem spBlock_fac (q f : ℕ) (hq : 0 < q) :
    (q ^ f + 1) * (q ^ f - 1) = q ^ (2 * f) - 1 := by
  have h1 : 1 ≤ q ^ f := Nat.one_le_pow _ _ hq
  have h2 : 1 ≤ q ^ (2 * f) := Nat.one_le_pow _ _ hq
  zify [h1, h2]
  rw [pow_mul']
  ring

private theorem spBlock_exists_lam {K : Type} [Field K] [Fintype K] {L : Type} [Field L]
    [Algebra K L] [Finite L] {f : ℕ} (hf : 0 < f) (hfL : finrank K L = 2 * f) (σ : L → L)
    (hσ : ∀ x, σ x = x ^ Fintype.card K ^ f) : ∃ lam : Lˣ, (lam : L) * σ lam = -1 := by
  have hq1 : 1 < Fintype.card K ^ f := Nat.one_lt_pow hf.ne' Fintype.one_lt_card
  by_cases hev : Even (Fintype.card K)
  ·
    have h2K : ((2 : ℕ) : K) = 0 := by
      have hchar : ringChar K = 2 := FiniteField.even_card_iff_char_two.2 (Nat.even_iff.1 hev)
      have h := CharP.cast_eq_zero K (ringChar K)
      rwa [hchar] at h
    have h2L : (2 : L) = 0 := by
      have h := congrArg (algebraMap K L) h2K
      rw [map_natCast, map_zero] at h
      exact_mod_cast h
    refine ⟨1, ?_⟩
    rw [Units.val_one, one_mul, hσ, one_pow]
    linear_combination h2L
  ·
    have hodd : Odd (Fintype.card K ^ f) := (Nat.not_even_iff_odd.1 hev).pow
    obtain ⟨s, hs⟩ := hodd
    have hs1 : 0 < s := by omega
    obtain ⟨γ, hγ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Lˣ)
    rw [Nat.card_units, CFSG.GroupTheory.WeirSylow.natCard_eq_pow_finrank (K := K), hfL] at hγ
    obtain ⟨M, hM⟩ : ∃ M, M = s * (Fintype.card K ^ f + 1) := ⟨_, rfl⟩
    have hN : Fintype.card K ^ (2 * f) - 1 = 2 * M := by
      rw [hM, ← spBlock_fac (Fintype.card K) f Fintype.card_pos]
      have hD : Fintype.card K ^ f - 1 = 2 * s := by omega
      rw [hD]
      ring
    have hMpos : 0 < M := by
      rw [hM]
      exact Nat.mul_pos hs1 (Nat.succ_pos _)
    have hsq : γ ^ M * γ ^ M = 1 := by
      rw [← pow_add, show M + M = orderOf γ by omega, pow_orderOf_eq_one]
    have hM1 : γ ^ M ≠ 1 := by
      intro h
      have h2 := orderOf_dvd_of_pow_eq_one h
      rw [hγ] at h2
      have h3 := Nat.le_of_dvd hMpos h2
      omega
    have hneg : ((γ ^ M : Lˣ) : L) = -1 := by
      have hsq' : ((γ ^ M : Lˣ) : L) * ((γ ^ M : Lˣ) : L) = 1 := by
        rw [← Units.val_mul, hsq, Units.val_one]
      rcases mul_self_eq_one_iff.1 hsq' with h | h
      · exact absurd (Units.ext (h.trans Units.val_one.symm)) hM1
      · exact h
    refine ⟨γ ^ s, ?_⟩
    rw [hσ, ← pow_succ', ← Units.val_pow_eq_pow_val, ← pow_mul, ← hM]
    exact hneg

theorem exists_spBlock_split (K : Type) [Field K] {L : Type} [Field L] [Algebra K L] [Finite L]
    {m : ℕ} [NeZero m] (hm : m ∣ Nat.card L - 1) :
    ∃ (S₀ : FormSpace K K) (ρ : Multiplicative (ZMod m) →* S₀.isom) (J₀ : S₀.isom),
      IsSymplecticSpace S₀ ∧ finrank K S₀.V = 2 * finrank K L ∧ Function.Injective ρ ∧
      ∀ c, J₀ * ρ c * J₀⁻¹ = ρ c⁻¹ := by
  obtain ⟨lam, hlam⟩ := exists_ne_zero_dual (K := K) L
  obtain ⟨ζ, hζ⟩ := exists_units_orderOf_eq (L := L) (d := m) hm
  let S₀ : FormSpace K K := ⟨L × L, fun v w => hypSympForm lam v w⟩
  have hS₀ : IsSymplecticSpace S₀ :=
    ⟨hypSympForm lam, fun _ _ => rfl, hypSympForm_isAlt lam, hypSympForm_nondegenerate hlam⟩
  have hmem : prodUnitsHom K L ζ ∈ S₀.isom := fun v w => prodUnitsHom_mem_isometry lam ζ v w
  obtain ⟨ρ, hρ, hrange⟩ := spBlock_exists_hom hmem (n := m)
    (by rw [orderOf_injective _ (prodUnitsHom_injective K L), hζ])
  let J : (L × L) ≃ₗ[K] (L × L) :=
    (LinearEquiv.prodComm K L L).trans ((LinearEquiv.refl K L).prodCongr (LinearEquiv.neg K))
  have hJapp : ∀ v : L × L, J v = (v.2, -v.1) := fun v => rfl
  have hJS : J ∈ S₀.isom := fun v w => by
    show hypSympForm lam (J v) (J w) = hypSympForm lam v w
    simp only [hypSympForm_apply, hJapp, mul_neg, neg_mul, map_neg]
    ring
  have hJg : J * prodUnitsHom K L ζ * J⁻¹ = (prodUnitsHom K L ζ)⁻¹ := by
    rw [← map_inv (prodUnitsHom K L), mul_inv_eq_iff_eq_mul]
    refine LinearEquiv.ext fun v => ?_
    simp only [LinearEquiv.mul_apply, hJapp, prodUnitsHom_apply, inv_inv, mul_neg]
  refine ⟨S₀, ρ, ⟨J, hJS⟩, hS₀, ?_, hρ, fun c => Subtype.ext ?_⟩
  · show finrank K (L × L) = 2 * finrank K L
    rw [Module.finrank_prod, two_mul]
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_inv]
    exact spBlock_conj_inv_of_mem hJg (hrange c)

theorem exists_spBlock_aniso (K : Type) [Field K] [Fintype K] {L : Type} [Field L] [Algebra K L]
    [Finite L] {f : ℕ} (hf : 0 < f) (hfL : finrank K L = 2 * f) {m : ℕ} [NeZero m]
    (hm : m ∣ Fintype.card K ^ f + 1) :
    ∃ (S₀ : FormSpace K K) (ρ : Multiplicative (ZMod m) →* S₀.isom) (J₀ : S₀.isom),
      IsSymplecticSpace S₀ ∧ finrank K S₀.V = finrank K L ∧ Function.Injective ρ ∧
      ∀ c, J₀ * ρ c * J₀⁻¹ = ρ c⁻¹ := by
  obtain ⟨σ, hσdef⟩ : ∃ σ : L ≃ₐ[K] L, σ = FiniteField.frobeniusAlgEquivOfAlgebraic K L ^ f :=
    ⟨_, rfl⟩
  have hσpow : ∀ x : L, σ x = x ^ Fintype.card K ^ f := fun x => by
    rw [hσdef]
    exact frob_pow_apply f x
  have hσσ : ∀ x : L, σ (σ x) = x := fun x => by
    rw [hσdef]
    exact frob_pow_frob_pow hfL x
  let Fix : Submodule K L := LinearMap.ker ((σ : L →ₗ[K] L) - LinearMap.id)
  have hFix : Fix < ⊤ := by
    obtain ⟨x, hx⟩ := exists_pow_ne_self (K := K) (L := L) hf (by rw [hfL]; omega)
    refine lt_top_iff_ne_top.2 fun htop => hx ?_
    have hmem : x ∈ Fix := htop ▸ Submodule.mem_top
    have h0 : σ x - x = 0 := hmem
    rw [hσpow] at h0
    exact sub_eq_zero.1 h0
  obtain ⟨mu, hmu, hFixmu⟩ := Submodule.exists_le_ker_of_lt_top Fix hFix
  have hmu0 : ∀ z, σ z = z → mu z = 0 := fun z hz =>
    hFixmu (show σ z - z = 0 from sub_eq_zero.2 hz)
  have hmuσ : ∀ z, mu (σ z) = -mu z := by
    intro z
    have h := hmu0 (σ z + z) (by rw [map_add, hσσ, add_comm])
    rw [map_add] at h
    exact eq_neg_of_add_eq_zero_left h
  have halt := twistSympForm_isAlt hσσ hmu0
  let S₀ : FormSpace K K := ⟨L, fun x y => twistSympForm mu σ x y⟩
  have hS₀ : IsSymplecticSpace S₀ :=
    ⟨twistSympForm mu σ, fun _ _ => rfl, halt, twistSympForm_nondegenerate hmu hσσ halt⟩
  have hdvd : Fintype.card K ^ f + 1 ∣ Nat.card L - 1 := by
    rw [CFSG.GroupTheory.WeirSylow.natCard_eq_pow_finrank (K := K), hfL]
    exact ⟨_, (spBlock_fac (Fintype.card K) f Fintype.card_pos).symm⟩
  obtain ⟨ζ, hζ⟩ := exists_units_orderOf_eq (L := L) (d := m) (hm.trans hdvd)
  have hζσ : (ζ : L) * σ (ζ : L) = 1 := by
    rw [hσpow, ← pow_succ']
    have h1 : ζ ^ (Fintype.card K ^ f + 1) = 1 :=
      orderOf_dvd_iff_pow_eq_one.1 (by rw [hζ]; exact hm)
    have h2 := congrArg Units.val h1
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at h2
  have hσζ : σ (ζ : L) = ((ζ⁻¹ : Lˣ) : L) := by
    rw [Units.val_inv_eq_inv_val]
    exact eq_inv_of_mul_eq_one_right hζσ
  obtain ⟨lam, hlam⟩ := spBlock_exists_lam hf hfL ⇑σ hσpow
  let Jlin : L ≃ₗ[K] L := σ.toLinearEquiv.trans (DistribMulAction.toModuleAut K L lam)
  have hJlin : ∀ x, Jlin x = (lam : L) * σ x := fun x => rfl
  have hJact : ∀ (u : Lˣ) (x : L), DistribMulAction.toModuleAut K L u x = (u : L) * x :=
    fun u x => rfl
  have hJiso : ∀ x y, twistSympForm mu σ (Jlin x) (Jlin y) = twistSympForm mu σ x y := by
    intro x y
    rw [twistSympForm_apply, twistSympForm_apply, hJlin, hJlin, map_mul σ, hσσ]
    have e1 : (lam : L) * σ x * (σ (lam : L) * y) = -(σ x * y) := by
      linear_combination (σ x * y) * hlam
    have e2 : mu (σ x * y) = -mu (x * σ y) := by
      have h := hmuσ (x * σ y)
      rwa [map_mul σ, hσσ] at h
    rw [e1, map_neg, e2, neg_neg]
  have hJmem : Jlin ∈ S₀.isom := fun x y => hJiso x y
  have hJg : Jlin * DistribMulAction.toModuleAut K L ζ * Jlin⁻¹ =
      (DistribMulAction.toModuleAut K L ζ)⁻¹ := by
    rw [← map_inv (DistribMulAction.toModuleAut K L : Lˣ →* (L ≃ₗ[K] L)), mul_inv_eq_iff_eq_mul]
    refine LinearEquiv.ext fun x => ?_
    simp only [LinearEquiv.mul_apply, hJlin, hJact, map_mul σ, hσζ]
    ring
  have hmem : DistribMulAction.toModuleAut K L ζ ∈ S₀.isom := fun x y =>
    toModuleAut_mem_twist mu σ hζσ x y
  obtain ⟨ρ, hρ, hrange⟩ := spBlock_exists_hom hmem (n := m)
    (by rw [orderOf_toModuleAut, hζ])
  refine ⟨S₀, ρ, ⟨Jlin, hJmem⟩, hS₀, rfl, hρ, fun c => Subtype.ext ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_inv]
  exact spBlock_conj_inv_of_mem hJg (hrange c)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
