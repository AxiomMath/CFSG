module

public import CFSG.LocalAnalysis.SectionRank.ExceptionalEvenCover
public import CFSG.LieType.Steinberg.TwistedD4.Datum
public import CFSG.LieType.Steinberg.TwistedD4.RankOne
public import CFSG.LieType.Steinberg.TwistedD4.Quasisimple
public import CFSG.LieType.Steinberg.TwistedD4.Generation
public import CFSG.LieType.Chevalley.TwistHolds
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate123
public import CFSG.Assembly.Subnormal
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Exceptional.E6E7
public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Steinberg.G2
public import CFSG.LieType.TitsSimplicity
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.SectionRank.OddCover.CubicKernel
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Th.F2Spec
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.SectionRank

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.Simplicity
  CFSG.LieType.RootSystem CFSG.LieType.CurtisTits CFSG.LieType.BorelTits.Weighted

section Longest

variable {τ : Tag} {K : Type} [Field K] [Finite K]

theorem eq_one_of_mem_B_of_commute_nrep
    [CharP K 2] {w₀ : WeylGroup τ}
    (hw₀ : ∀ α : Root τ, (w₀ • α).1 = -α.1) {g : adjointGroup τ K}
    (hg : g ∈ (nativeData τ K).B)
    (hc : nrep τ K w₀ * g * (nrep τ K w₀)⁻¹ = g) : g = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu, h, hh, rfl⟩ := exists_mul_of_mem_B hg
  set n := nrep τ K w₀
  have hUle : (nativeData τ K).U ≤ Uminus τ K w₀ := by
    refine iSup₂_le fun α (hα : 0 < height α.1) => ?_
    refine le_iSup₂_of_le (f := fun (β : Root τ) (_ : 0 < height β.1 ∧ height (w₀ • β).1 < 0) =>
      (nativeRootSubgroups τ K).X β) α ⟨hα, ?_⟩ le_rfl
    rw [hw₀, height_neg]
    omega
  have hu' : n * u * n⁻¹ ∈ Uneg τ K := nrep_conj_mem_Uneg (hUle hu)
  have hh' : n * h * n⁻¹ = h⁻¹ := nrep_conj_of_mem_H hw₀ hh
  have hcon : n * (u * h) * n⁻¹ = (n * u * n⁻¹) * h⁻¹ := by
    rw [← hh']
    group
  rw [hcon] at hc
  have hval : n * u * n⁻¹ = u * h * h := by
    calc n * u * n⁻¹ = (n * u * n⁻¹) * h⁻¹ * h := by group
      _ = u * h * h := by rw [hc]
  have hB : u * h * h ∈ (nativeData τ K).B :=
    mul_mem (mul_mem (RootGroupData.U_le_B hu) (RootGroupData.H_le_B hh))
      (RootGroupData.H_le_B hh)
  have h1 : u * h * h = 1 := by
    have hmem : u * h * h ∈ (nativeData τ K).B ⊓ Uneg τ K := ⟨hB, hval ▸ hu'⟩
    rwa [nativeData_B_inf_Uneg, Subgroup.mem_bot] at hmem
  have hu1 : u = 1 := by
    have huH : u ∈ (nativeData τ K).H := by
      have : u = (h * h)⁻¹ := by rw [eq_inv_iff_mul_eq_one, ← mul_assoc, h1]
      rw [this]
      exact (nativeData τ K).H.inv_mem ((nativeData τ K).H.mul_mem hh hh)
    have hmem : u ∈ (nativeData τ K).H ⊓ (nativeData τ K).U := Subgroup.mem_inf.2 ⟨huH, hu⟩
    rwa [H_inf_U_eq_bot 2, Subgroup.mem_bot] at hmem
  subst hu1
  have hsq : h ^ 2 = 1 := by rw [one_mul] at h1; rw [sq, h1]
  have hcop : Nat.Coprime (Nat.card (nativeData τ K).H) 2 :=
    (nativeRootSubgroups τ K).coprime_card_H 2
  have hord : orderOf h ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  have hord' : orderOf h ∣ Nat.card (nativeData τ K).H := by
    rw [← Subgroup.orderOf_mk h hh]
    exact orderOf_dvd_natCard _
  have h1' : orderOf h = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hord' hcop)
    hord
  rw [orderOf_eq_one_iff] at h1'
  rw [h1', one_mul]

end Longest

section D4Long

noncomputable abbrev d4Long : WeylGroup d4 := (coxeterSystem d4).wordProd braidWordLeft

theorem d4Long_smul_single
    (i : Fin d4.rank) :
    d4Long • (Pi.single i 1 : Fin d4.rank → ℤ) = -Pi.single i 1 := by
  rw [CFSG.LieType.Chevalley.wordProd_smul]
  revert i
  decide +kernel

theorem d4Long_smul
    (v : Fin d4.rank → ℤ) : d4Long • v = -v := by
  have h : weylAction (isFiniteType_cartan d4) d4Long = -LinearMap.id := by
    refine LinearMap.pi_ext fun i x => ?_
    rw [← mul_one x, ← smul_eq_mul, Pi.single_smul, map_smul, map_smul, ← smul_def,
      d4Long_smul_single]
    simp
  rw [smul_def, h]
  rfl

theorem d4Long_smul_root
    (α : Root d4) : (d4Long • α).1 = -α.1 := d4Long_smul α.1

theorem d4Long_mem_relWeylTwist
    : d4Long ∈ relWeylTwist .D4 := by
  rw [mem_relWeylTwist]
  refine ext_single fun k => ?_
  have hk : (Pi.single k 1 : Fin d4.rank → ℤ) = rho (Pi.single (rhoPerm.symm k) 1) := by
    rw [rho_single, Equiv.apply_symm_apply]
  have h := weylTwist_smul_permLattice TwistTag.D4 d4Long (Pi.single (rhoPerm.symm k) 1)
  change weylTwist .D4 d4Long • rho _ = rho _ at h
  rw [hk, h, d4Long_smul, d4Long_smul]
  funext l
  simp [rho, permLattice]

end D4Long

section Center

variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K →+* K}

omit [Finite K] [CharP K 2] in
theorem surjective_of_cube (hσ : ∀ c, σ (σ (σ c)) = c) : Function.Surjective σ :=
  fun c => ⟨σ (σ c), hσ c⟩

theorem twistedGroup_center_eq_bot
    (hσ : ∀ c, σ (σ (σ c)) = c) :
    Subgroup.center (twistedGroup σ) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  set g : adjointGroup d4 K := z.1 with hg
  have hgΓ : g ∈ twistFixed .D4 K σ := twistedGroup_le_twistFixed σ z.2
  have hnorm : (⟨g, hgΓ⟩ : twistFixed .D4 K σ) ∈ Subgroup.normalizer
      (((nativeData d4 K).U.comap (twistFixed .D4 K σ).subtype :
        Subgroup (twistFixed .D4 K σ)) : Set (twistFixed .D4 K σ)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hxc : ((x : twistFixed .D4 K σ) : adjointGroup d4 K) ∈ (nativeData d4 K).U →
        g * x * g⁻¹ = x := fun hx => by
      have hx' : ((x : twistFixed .D4 K σ) : adjointGroup d4 K) ∈ twistedGroup σ :=
        nativeU_inf_twistFixed_le σ ⟨hx, x.2⟩
      have := Subgroup.mem_center_iff.1 hz ⟨_, hx'⟩
      have h' := congrArg Subtype.val this
      simp only [Subgroup.coe_mul] at h'
      rw [hg, ← h', mul_inv_cancel_right]
    constructor
    · intro hx
      change g * x * g⁻¹ ∈ (nativeData d4 K).U
      rw [hxc hx]
      exact hx
    · intro hx
      change g * x * g⁻¹ ∈ (nativeData d4 K).U at hx
      change ((x : twistFixed .D4 K σ) : adjointGroup d4 K) ∈ (nativeData d4 K).U
      by_contra hxU
      have hy : g * x * g⁻¹ ∈ twistFixed .D4 K σ :=
        mul_mem (mul_mem hgΓ x.2) (inv_mem hgΓ)
      have hyc : g * (g * x * g⁻¹) * g⁻¹ = g * x * g⁻¹ := by
        have hy' : g * x * g⁻¹ ∈ twistedGroup σ := nativeU_inf_twistFixed_le σ ⟨hx, hy⟩
        have := Subgroup.mem_center_iff.1 hz ⟨_, hy'⟩
        have h' := congrArg Subtype.val this
        simp only [Subgroup.coe_mul] at h'
        rw [hg, ← h', mul_inv_cancel_right]
      have : (x : adjointGroup d4 K) = g * x * g⁻¹ := by
        have := congrArg (fun y => g⁻¹ * y * g) hyc
        simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] at this
        simpa [mul_assoc] using this.symm
      exact hxU (this ▸ hx)
  have hgB : g ∈ (nativeData d4 K).B :=
    normalizer_le_of_fixedData (nrep d4 K) (nativeData d4 K).B (nativeData d4 K).U
      (twistFixed .D4 K σ) (relWeylTwist .D4) (twistFixed_bruhat .D4 K σ (surjective_of_cube hσ))
      (nativeRootSubgroups d4 K).B_le_normalizer_U
      (by rw [CFSG.LieType.Chevalley.nrep_one]; exact one_mem _)
      (twistFixed_hUw .D4 K σ (surjective_of_cube hσ)) hnorm
  have hn : nrep d4 K d4Long ∈ twistedGroup σ := nrep_mem_twistedGroup σ d4Long_mem_relWeylTwist
  have hc : nrep d4 K d4Long * g * (nrep d4 K d4Long)⁻¹ = g := by
    have := Subgroup.mem_center_iff.1 hz ⟨_, hn⟩
    have h' := congrArg Subtype.val this
    simp only [Subgroup.coe_mul] at h'
    rw [hg, h', mul_inv_cancel_right]
  have h1 := eq_one_of_mem_B_of_commute_nrep d4Long_smul_root hgB hc
  exact Subtype.ext h1

end Center

section Split

variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K →+* K}

omit [Finite K] in
theorem sq_eq_one_of_mem_twistedRootSubgroupD4
    (hσ : ∀ c, σ (σ (σ c)) = c)
    {β : Fin (Tag.rank .G2) → ℤ} (hβ : IsRoot .G2 β) {g : adjointGroup d4 K}
    (hg : g ∈ twistedRootSubgroupD4 σ β) : g ^ 2 = 1 := by
  obtain ⟨α₀, hα₀, hp⟩ := exists_proj_eq hβ
  by_cases hfix : rho α₀ = α₀
  · obtain ⟨c, -, rfl⟩ := (mem_twistedRootSubgroupD4_iff_of_fixed hσ hα₀ hp hfix g).1 hg
    rw [sq, ← Adjoint.xPar_add, CharTwo.add_self_eq_zero, Adjoint.xPar_zero]
  · obtain ⟨c, rfl⟩ := (mem_twistedRootSubgroupD4_iff_of_orbit hσ hα₀ hp hfix g).1 hg
    rw [sq, ← xOrbit_add σ hα₀ hfix, CharTwo.add_self_eq_zero, xOrbit_zero]

omit [Finite K] in
theorem isPGroup_twistedRootGroup
    (hσ : ∀ c, σ (σ (σ c)) = c) {β : Fin (Tag.rank .G2) → ℤ}
    (hβ : β ∈ (twistedDatum σ).roots) : IsPGroup 2 ((twistedDatum σ).rootGroup β) := by
  have hβ' := isRoot_of_mem_twistedDatum_roots σ hβ
  intro x
  refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
  have hx : ((x : twistedGroup σ) : adjointGroup d4 K) ∈ twistedRootSubgroupD4 σ β := x.2
  have := sq_eq_one_of_mem_twistedRootSubgroupD4 hσ hβ' hx
  simpa [pow_one] using this

omit [Finite K] [CharP K 2] in
theorem rankOne_long_le_range
    (hσ : ∀ c, σ (σ (σ c)) = c) :
    rankOne (twistedRootGroup σ) (ng 0) ≤ (slLong σ hσ).range := by
  refine sup_le (fun x hx => ?_) (fun x hx => ?_)
  · have hx' : ((x : twistedGroup σ) : adjointGroup d4 K) ∈
        twistedRootSubgroupD4 σ (Pi.single (ng 0) 1) := hx
    obtain ⟨c, hc, hxc⟩ := (mem_twistedRootSubgroupD4_iff_of_fixed hσ (isRoot_single d4 (nd 2))
      proj_single_two rho_single_two _).1 hx'
    exact ⟨sl2Upper ⟨c, hc⟩, Subtype.ext (by rw [slLong_val, slLongE_upper, hxc])⟩
  · have hx' : ((x : twistedGroup σ) : adjointGroup d4 K) ∈
        twistedRootSubgroupD4 σ (-Pi.single (ng 0) 1) := hx
    obtain ⟨c, hc, hxc⟩ := (mem_twistedRootSubgroupD4_iff_of_fixed hσ
      (isRoot_neg_single d4 (nd 2)) proj_neg_single_two rho_neg_single_two _).1 hx'
    exact ⟨sl2Lower ⟨c, hc⟩, Subtype.ext (by rw [slLong_val, slLongE_lower, hxc])⟩

omit [Finite K] [CharP K 2] in
theorem rankOne_short_le_range_slShort
    (hσ : ∀ c, σ (σ (σ c)) = c) :
    rankOne (twistedRootGroup σ) (ng 1) ≤ (slShort σ hσ).range := by
  refine (rankOne_short_le_range hσ).trans ?_
  rintro _ ⟨y, rfl⟩
  refine ⟨(Adjoint.restrictEquiv (rootOperatorFamily d4) cartan_zero_two) y, ?_⟩
  simp [slShort]

theorem triality_even_central_odd_extension_splitting
    (hσ : ∀ c, σ (σ (σ c)) = c)
    {E : Type*} [Group E] [Finite E] {π : E →* twistedGroup σ} (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card π.ker)) :
    ∃ s : twistedGroup σ →* E, (∀ x, π (s x) = x) ∧
      (∀ τ : twistedGroup σ →* E, (∀ x, π (τ x) = x) → τ = s) ∧
      ∃ e : π.ker × s.range ≃* E, ∀ a, e a = (a.1 : E) * a.2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC : ¬ 2 ∣ Nat.card π.ker := not_two_dvd_of_odd hodd
  have : Finite (fixedField σ) := Subtype.finite
  refine exists_section_mulEquiv_of_existsUnique hker
    (existsUnique_section_of_rankOne_lift (p := 2) (twistedDatum_isCTGroupDatum σ hσ)
      (twistedDatum_steinbergExtras σ hσ) (fun β hβ => isPGroup_twistedRootGroup hσ hβ) hπ hker
      hC fun i => ?_)
  match i with
  | ⟨0, _⟩ =>
    obtain ⟨ρ', hρ', -⟩ := EvenCover.sl2_existsUnique_lift hπ hker hC (slLong σ hσ)
    exact exists_lift_of_injective (slLong_injective hσ) (rankOne_long_le_range hσ)
      fun g => DFunLike.congr_fun hρ' g
  | ⟨1, _⟩ =>
    obtain ⟨ρ', hρ', -⟩ := EvenCover.sl2_existsUnique_lift hπ hker hC (slShort σ hσ)
    exact exists_lift_of_injective (slShort_injective hσ) (rankOne_short_le_range_slShort hσ)
      fun g => DFunLike.congr_fun hρ' g

end Split

theorem center_eq_bot_of_mulEquiv' {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : Subgroup.center G = ⊥) : Subgroup.center H = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hz' : e.symm z ∈ Subgroup.center G := Subgroup.mem_center_iff.2 fun y => by
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, Subgroup.mem_center_iff.1 hz (e y)]
  rw [h, Subgroup.mem_bot] at hz'
  simpa using congrArg e hz'

theorem triality_even_perfect_odd_cover_trivial
    {S : Type} [Group S] {f : ℕ}
    (hS : ChevalleyExceptionalModel S .trialityD4 2 f) {E : Type*} [Group E] [Finite E]
    [Group.IsPerfect E] (π : E →* S) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card π.ker)) : π.ker = ⊥ := by
  obtain ⟨hadm, K, _, _, hK, σ, hσq, ⟨e⟩⟩ := hS
  have hf : 1 ≤ f := hadm.2.1
  have hq : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hK' : Nat.card K = (2 ^ f) ^ 3 := hK
  have : CharP K 2 := charP_two_of_card (f := f * 3) (by rw [hK', ← pow_mul])
  have hσ3 := sigma_three_of_card hK' hσq
  let eD := twistedGroupEquivDerived σ hq hK' hσq
  have hZ := center_eq_bot_of_mulEquiv' eD (twistedGroup_center_eq_bot hσ3)
  let eS : DerivedCentralQuotient (twistedFixedGroup .D4 K σ) ≃* twistedGroup σ :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans eD.symm)
  let ψ : E →* twistedGroup σ := (e.trans eS).toMonoidHom.comp π
  have hψker : ψ.ker = π.ker := ker_mulEquiv_comp π (e.trans eS)
  have hψ : Function.Surjective ψ := (e.trans eS).surjective.comp hπ
  obtain ⟨s, hs, -, -⟩ := triality_even_central_odd_extension_splitting hσ3 hψ (hψker ▸ hC)
    (hψker ▸ hodd)
  rw [← hψker]
  exact ker_eq_bot_of_section_of_perfect ψ (hψker ▸ hC) s hs

theorem catalog_triality_even
    {L : Type} [Group L] [Finite L] (hL : IsQuasisimple L)
    (hSQT : IsStronglyQuasithin L) (hodd : Odd (Nat.card (Subgroup.center L))) {f : ℕ}
    (h : ChevalleyExceptionalModel (L ⧸ Subgroup.center L) .trialityD4 2 f) :
    Subgroup.center L = ⊥ ∧ CatalogStepConclusion L := by
  have : Group.IsPerfect L := hL.1
  exact catalogStepConclusion_of_perfect_odd_cover_trivial hSQT hodd (MulEquiv.refl _)
    fun π hπ hC hπodd => triality_even_perfect_odd_cover_trivial h π hπ hC hπodd

end CFSG.SectionRank
