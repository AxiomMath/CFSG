module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ModelGenActModel
public import CFSG.LieType.Chevalley.TwistedE6NormalForm
public import CFSG.LieType.BorelTits.UnitaryForm
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcThreeTwE6CentralLift
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcTwE6ThreeModel
import CFSG.GH74.Uniqueness.SU.SU7Gen3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ModelGenActLift

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Central

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open CFSG.LieType.Universal.Unitary (antidiag conjTr)
open CFSG.ClassicalInvolution.Phan (Su)
open CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Conc


private theorem ker_chevQuotHom_eq_center {Ω : Type} [Group Ω] {S : Subgroup Ω}
    (hcore : GLAPPrimeCore 3 ↥S = ⊥) : (chevQuotHom 3 S).ker = Subgroup.center ↥S := by
  apply le_antisymm
  · intro x hx
    refine Subgroup.mem_center_iff.2 fun s => ?_
    have hx' : pQuotHom 3 S x ∈ Subgroup.center (PQuot 3 S) := by
      rw [MonoidHom.mem_ker] at hx
      exact (QuotientGroup.eq_one_iff _).1 hx
    have hinj : Function.Injective (pQuotHom 3 S) := by
      rw [← MonoidHom.ker_eq_bot_iff, ker_pQuotHom, hcore]
    apply hinj
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.1 hx' (pQuotHom 3 S s)
  · intro z hz
    rw [MonoidHom.mem_ker]
    refine (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_center_iff.2 fun y => ?_)
    obtain ⟨l, rfl⟩ := pQuotHom_surjective 3 S y
    show pQuotHom 3 S l * pQuotHom 3 S z = pQuotHom 3 S z * pQuotHom 3 S l
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz l]

theorem concA_twistedE6_three_of_center_ne_bot_of_card_le {K : Type} [Field K] [Finite K]
    {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (hK : Nat.card K = (ℓ ^ f) ^ 2) (hf : 1 ≤ f)
    (hℓ2 : ℓ ≠ 2) (h3 : 3 ∣ ℓ ^ f + 1) {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}
    (hS : S.Normal) (hperf : ⁅S, S⁆ = S) (hcore : GLAPPrimeCore 3 ↥S = ⊥)
    (hZ : Subgroup.center ↥S ≠ ⊥)
    (e : PSimple 3 S ≃* ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)))
    (hBle : Nat.card B ≤ 3 ^ 6) : S267ConcA 3 S B := by
  classical
  haveI : Finite ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) := Finite.of_equiv _ e.toEquiv
  obtain ⟨Γ, hΓ, hΓker⟩ := ModelGen.exists_actHom_pSimple hS hperf e
  set π : ↥S →* ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) :=
    e.toMonoidHom.comp (chevQuotHom 3 S) with hπdef
  have hπ : Function.Surjective π := e.surjective.comp (chevQuotHom_surjective 3 S)
  have hΓπ : ∀ (b : Ω) (g : ↥S), Γ b (π g) = π ⟨b * g * b⁻¹, hS.conj_mem _ g.2 _⟩ := hΓ
  have hπker : π.ker = Subgroup.center ↥S := by
    rw [← ker_chevQuotHom_eq_center hcore]
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ e.injective]
  have hZ3 : Nat.card (Subgroup.center ↥S) = 3 :=
    CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.card_center_eq_three (Fact.out : ℓ.Prime) hℓ2 hf h3
      hK (unitaryInvolution K ℓ f) (unitaryInvolution_apply K ℓ f) hperf hcore hZ e
  have hker : Nat.card π.ker = 3 := by rw [hπker, hZ3]
  obtain ⟨ζ, hζ, hσζ, P, hP, c, hc, hct, φ, A₁₂, hιφ, hr₀A₁₂, hA₁₂A, hA₁₂c, hlay⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Outer.modelAGen_twistedE6_three_spec hK hf hℓ2 h3
  obtain ⟨-, hAc, -, hA₁c, hJcomp, hAN, hcent, ht1, ht2, hJt, hAt⟩ :=
    modelAGen_twistedE6_spec_of_inj hK hf hζ hσζ P hP hℓ2 (by norm_num) hc hct
      (by norm_num : 0 < 4) hιφ
  set A := (twE6Phi hK hf hζ hσζ P hP (by norm_num) hc hct φ).range with hA
  have hMel : IsElemAbelian 3 (A.comap π) :=
    CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.isElemAbelian_comap_twE6Phi hK hf hℓ2 h3 hζ hσζ P hP
      hc hct φ hperf hcore e
  set M := (A.comap π).map S.subtype with hM
  have hMel' : IsElemAbelian 3 M := CFSG.SectionRank.isElemAbelian_map hMel S.subtype
  have hW := ModelGen.actData_of_modelAGen_comap hS hπ hker hΓπ (n := 4 + 1) (by norm_num) hAc
    hr₀A₁₂ hA₁₂A hA₁c hA₁₂c hJcomp hAN hcent hlay ht1 ht2 hJt hAt
  have hMC : M ⊓ centModSubgroup 3 S = (Subgroup.center ↥S).map S.subtype := by
    apply le_antisymm
    · rintro x ⟨⟨s, hs, rfl⟩, hxC⟩
      refine ⟨s, Subgroup.mem_center_iff.2 fun g => Subtype.ext ?_, rfl⟩
      exact (ModelGen.comm_of_mem_centMod hS hcore hxC g.2).symm
    · rintro x ⟨z, hz, rfl⟩
      refine ⟨⟨z, ?_, rfl⟩, ?_⟩
      · show π z ∈ A
        have hz' : z ∈ π.ker := hπker ▸ hz
        rw [MonoidHom.mem_ker.1 hz']
        exact A.one_mem
      · refine centMod_iff.1 (centMod_of_mem_centralizer (Subgroup.mem_centralizer_iff.2 ?_))
        intro y hy
        have := Subgroup.mem_center_iff.1 hz ⟨y, hy⟩
        exact (congrArg Subtype.val this : _)
  have hMCc : Nat.card ↥(M ⊓ centModSubgroup 3 S) = 3 := by
    rw [hMC, Subgroup.card_map_of_injective S.subtype_injective, hZ3]
  have hconc : S267ConcA 3 S M :=
    ModelGen.concA_of_actData_pSimple Nat.prime_three (by norm_num) hS hperf hcore hMel' hMCc e
      (fun x => Γ x) (fun x g => (hΓ x g).symm) hW
  have hMc : Nat.card M = 3 ^ 6 := by
    rw [hM, Subgroup.card_map_of_injective S.subtype_injective]
    have h := CFSG.GH74.Uniqueness.SU.SU7.Gen.card_map_mul_card_inf_ker π (A.comap π)
    rw [Subgroup.map_comap_eq_self_of_surjective hπ, inf_eq_right.2 (Subgroup.ker_le_comap π A),
      hker, hAc] at h
    rw [← h]
    norm_num
  obtain ⟨t', hπt', ht'2, ht'c⟩ := ModelGen.exists_involution_lift_commute hS hπ
    (hπker.le) (by rw [hker]; decide) hΓπ ht2
  have ht'1 : (t' : Ω) ≠ 1 := fun h => ht1 (by
    rw [← hπt', show t' = 1 from Subtype.ext h, map_one])
  have hMt : M ≤ Subgroup.centralizer ({(t' : Ω)} : Set Ω) := by
    rintro _ ⟨s, hs, rfl⟩
    refine Subgroup.mem_centralizer_singleton_iff.2 (ht'c s ?_)
    obtain ⟨g, hg⟩ := hπ (twE6T K ℓ f)
    have hst : π s * π g = π g * π s := by
      rw [hg]
      exact Subgroup.mem_centralizer_singleton_iff.1 (hAt hs)
    rw [← hg, hΓπ]
    calc π ⟨(s : Ω) * g * (s : Ω)⁻¹, _⟩ = π s * π g * (π s)⁻¹ := by
          rw [← map_mul, ← map_inv, ← map_mul]
          rfl
      _ = π g := by rw [hst, mul_inv_cancel_right]
  have hMT : M ≤ Subgroup.normalizer (Subgroup.zpowers (t' : Ω) : Set Ω) := by
    intro g hg
    refine ModelGen.mem_normalizer_of_forall_comm fun k hk => ?_
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    exact Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.1 (hMt hg)) n
  obtain ⟨B'', D, J, hB'', hD, hor, hBC, t'', ht''1, ht''2, ht''D, ht''J⟩ := hconc
  refine ⟨B'', D, J, hB'', hD, Or.inr ?_, hBC, t'', ht''1, ht''2, ht''D, ht''J⟩
  rcases hor with rfl | ⟨hle', T', hT', hT'2, hN⟩
  · refine ⟨hBle.trans hMc.ge, Subgroup.zpowers (t' : Ω),
      ModelGen.zpowers_ne_bot_of_ne_one ht'1, ModelGen.isPGroup_two_zpowers_of_sq ?_, hMT⟩
    rw [← Subgroup.coe_pow, ht'2, Subgroup.coe_one]
  · exact ⟨(hBle.trans hMc.ge).trans hle', T', hT', hT'2, hN⟩

theorem concA_twistedE6_three_of_center_ne_bot_of_not_mem_inndiag {K : Type} [Field K]
    [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (hK : Nat.card K = (ℓ ^ f) ^ 2) (hf : 1 ≤ f)
    (hℓ2 : ℓ ≠ 2) (h3 : 3 ∣ ℓ ^ f + 1) {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}
    (hS : S.Normal) (hperf : ⁅S, S⁆ = S) (hcore : GLAPPrimeCore 3 ↥S = ⊥)
    (hZ : Subgroup.center ↥S ≠ ⊥) (hB : IsElemAbelian 3 B) (hBle : Nat.card B ≤ 3 ^ 7)
    (e : PSimple 3 S ≃* ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)))
    {Γ : Ω →* MulAut ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))}
    (hΓ : ∀ (b : Ω) (g : ↥S), Γ b (e (chevQuotHom 3 S g)) =
      e (chevQuotHom 3 S ⟨b * g * b⁻¹, hS.conj_mem _ g.2 _⟩))
    {b : Ω} (hb : b ∈ B)
    (hβ : Γ b ∉ twistedE6Inn K (unitaryInvolution K ℓ f) ⊔
      twistedE6Diag K (unitaryInvolution K ℓ f)) :
    S267ConcA 3 S B := by
  classical
  have hσ : ∀ c, unitaryInvolution K ℓ f c = c ^ (ℓ ^ f) := fun c => unitaryInvolution_apply K ℓ f c
  haveI : Finite ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) := Finite.of_equiv _ e.toEquiv
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨Γ₀, hΓ₀, hΓ₀ker⟩ := ModelGen.exists_actHom_pSimple hS hperf e
  have hΓeq : Γ = Γ₀ := by
    refine MonoidHom.ext fun x => MulEquiv.ext fun y => ?_
    obtain ⟨g, rfl⟩ := (e.surjective.comp (chevQuotHom_surjective 3 S)) y
    exact (hΓ x g).trans (hΓ₀ x g).symm
  have hΓker : Γ.ker = centModSubgroup 3 S := hΓeq ▸ hΓ₀ker
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -, hker, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form (Fact.out : ℓ.Prime) hf K hK
      (unitaryInvolution K ℓ f) hσ
  have hbp : b ^ 3 = 1 := hB.2 b hb
  have hβp : Γ b ^ 3 = 1 := by rw [← map_pow, hbp, map_one]
  have hΘβ : Θ (Γ b) ≠ 1 := fun h => hβ (by rw [← hker]; exact MonoidHom.mem_ker.2 h)
  have hK' : Nat.card K = ℓ ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨d, -, -, r, ε₀, -, ψ', -, hψ'⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.twisted_E6_field_descent_conj_of_prime_order
      (Fact.out : ℓ.Prime) hf K hK' (unitaryInvolution K ℓ f) hσ Θ hΘ hp hp2 (Γ b) hβp hΘβ
  set ε := Θ (Γ b) with hεdef
  have hεo : orderOf ε = 3 := orderOf_eq_prime (by rw [hεdef, ← map_pow, hβp, map_one]) hΘβ
  have hout : fieldActor (unitaryInvolution K ℓ f) ε ∉
      (MulAut.conj : ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) →*
      MulAut ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))).range := by
    rintro ⟨g, hg⟩
    apply hβ
    refine Subgroup.mem_sup_left ⟨ψ'⁻¹ g, MulEquiv.ext fun x => ?_⟩
    have h1 : Γ b = ψ'⁻¹ * fieldActor (unitaryInvolution K ℓ f) ε * ψ' := by
      rw [hεdef, ← hψ']
      group
    rw [h1, ← hg, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply,
      map_mul, map_mul, map_inv, MulAut.inv_apply_self]
  set e' : PSimple 3 S ≃* ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) := e.trans ψ' with he'
  set Γ' : Ω →* MulAut ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) :=
    (MulAut.conj ψ').toMonoidHom.comp Γ
    with hΓ'
  have hΓ'apply : ∀ x y, Γ' x y = ψ' (Γ x (ψ'⁻¹ y)) := fun x y => rfl
  have hΓ'c : ∀ (x : Ω) (g : ↥S), Γ' x (e' (chevQuotHom 3 S g)) =
      e' (chevQuotHom 3 S ⟨x * g * x⁻¹, hS.conj_mem _ g.2 _⟩) := by
    intro x g
    rw [hΓ'apply]
    show ψ' (Γ x (ψ'⁻¹ (ψ' (e (chevQuotHom 3 S g))))) = ψ' (e (chevQuotHom 3 S _))
    rw [MulAut.inv_apply_self, hΓ]
  have hΓ'b : Γ' b = fieldActor (unitaryInvolution K ℓ f) ε := hψ'
  have hΓ'ker : Γ'.ker = centModSubgroup 3 S := by
    rw [← hΓker]
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    show ψ' * Γ x * ψ'⁻¹ = 1 ↔ Γ x = 1
    constructor
    · intro h
      calc Γ x = ψ'⁻¹ * (ψ' * Γ x * ψ'⁻¹) * ψ' := by group
        _ = 1 := by rw [h]; group
    · intro h
      rw [h]
      group
  set π : ↥S →* ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) :=
    e'.toMonoidHom.comp (chevQuotHom 3 S) with hπdef
  have hπ : Function.Surjective π := e'.surjective.comp (chevQuotHom_surjective 3 S)
  have hΓπ : ∀ (x : Ω) (g : ↥S), Γ' x (π g) = π ⟨x * g * x⁻¹, hS.conj_mem _ g.2 _⟩ := hΓ'c
  have hπker : π.ker = Subgroup.center ↥S := by
    rw [← ker_chevQuotHom_eq_center hcore]
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ e'.injective]
  have hZ3 : Nat.card (Subgroup.center ↥S) = 3 :=
    CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.card_center_eq_three (Fact.out : ℓ.Prime) hℓ2 hf h3
      hK (unitaryInvolution K ℓ f) hσ hperf hcore hZ e'
  have hker3 : Nat.card π.ker = 3 := by rw [hπker, hZ3]
  obtain ⟨ζ, hζ, hσζ, P, hP, c, hc, hct, φ, hεζ, hPε, hεc, hφε, hιφ, -, -, -, hAc, hψA, hA₁A, hA₁c,
      hJcomp, hAN, hJψ, hk, hlay, ht1, ht2, hJt, hAt, hψt⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Outer.modelBGen_twistedE6_three_spec hK hf hℓ2 h3
      hεo hout
  set A := (twE6Phi hK hf hζ hσζ P hP hp2 hc hct φ).range with hA
  have hMel : IsElemAbelian 3 (A.comap π) :=
    CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.isElemAbelian_comap_twE6Phi hK hf hℓ2 h3 hζ hσζ P hP
      hc hct φ hperf hcore e'
  set M := (A.comap π).map S.subtype with hM
  have hb' : ∀ g : ↥S, e' (chevQuotHom 3 S ⟨b * g * b⁻¹, hS.conj_mem _ g.2 _⟩) =
      fieldActor (unitaryInvolution K ℓ f) ε (e' (chevQuotHom 3 S g)) := fun g => by
    rw [← hΓ'b, hΓ'c]
  have hbM : ∀ m ∈ M, b * m = m * b := by
    rintro _ ⟨s, hs, rfl⟩
    exact CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.commute_of_mem_comap_twE6Phi hK hf hℓ2 h3 hζ hσζ
      P hP hc hct φ hperf hcore e' hS hεζ hPε hεc hφε hbp hb' hs
  have hMel' : IsElemAbelian 3 M := CFSG.SectionRank.isElemAbelian_map hMel S.subtype
  have hW := ModelGen.actData_of_modelBGen_comap hp hS hπ hker3 hΓπ (n := 4 + 1) (by norm_num)
    hout hAc hA₁A hA₁c hJcomp hAN hJψ hk hlay ht1 ht2 hJt hAt hΓ'b hbp hbM
  have hMC : M ⊓ Γ'.ker = (Subgroup.center ↥S).map S.subtype := by
    rw [hΓ'ker]
    apply le_antisymm
    · rintro x ⟨⟨s, hs, rfl⟩, hxC⟩
      refine ⟨s, Subgroup.mem_center_iff.2 fun g => Subtype.ext ?_, rfl⟩
      exact (ModelGen.comm_of_mem_centMod hS hcore hxC g.2).symm
    · rintro x ⟨z, hz, rfl⟩
      refine ⟨⟨z, ?_, rfl⟩, ?_⟩
      · show π z ∈ A
        have hz' : z ∈ π.ker := hπker ▸ hz
        rw [MonoidHom.mem_ker.1 hz']
        exact A.one_mem
      · refine centMod_iff.1 (centMod_of_mem_centralizer (Subgroup.mem_centralizer_iff.2 ?_))
        intro y hy
        have := Subgroup.mem_center_iff.1 hz ⟨y, hy⟩
        exact (congrArg Subtype.val this : _)
  have hMker : Nat.card ↥(M ⊓ Γ'.ker) = 3 := by
    rw [hMC, Subgroup.card_map_of_injective S.subtype_injective, hZ3]
  have hψp : Γ' b ^ 3 = 1 := by rw [← map_pow, hbp, map_one]
  have hinner : ∀ k : ℕ, k < 3 → Γ' b ^ k ∈ (MulAut.conj :
      ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) →*
        MulAut ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))).range → k = 0 := by
    intro k hk hmem
    by_contra hk0
    rw [hΓ'b] at hψp hmem
    exact ModelGen.pow_not_mem_range_conj hp hψp hout hk hk0 hmem
  have hbout : M.map Γ' ⊓ Subgroup.zpowers (Γ' b) = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨⟨_, ⟨s, -, rfl⟩, rfl⟩, hy⟩
    obtain ⟨k, hk, hky⟩ := ModelGen.exists_pow_lt_of_pow_eq_one (by norm_num) hψp hy
    have hinn : Γ' (S.subtype s) ∈ (MulAut.conj :
        ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) →*
          MulAut ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))).range := by
      refine ⟨π s, MulEquiv.ext fun y => ?_⟩
      obtain ⟨g, rfl⟩ := hπ y
      show π s * π g * (π s)⁻¹ = Γ' (s : Ω) (π g)
      rw [hΓπ, ← map_mul, ← map_inv, ← map_mul]
      rfl
    rw [← hky] at hinn
    have h0 := hinner k hk hinn
    rw [Subgroup.mem_bot, ← hky, h0, pow_zero]
  have hbker : Subgroup.zpowers b ⊓ Γ'.ker = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hy, hyk⟩
    obtain ⟨k, hk, rfl⟩ := ModelGen.exists_pow_lt_of_pow_eq_one (by norm_num) hbp hy
    have h1 : Γ' b ^ k = 1 := by rw [← map_pow]; exact hyk
    have h0 := hinner k hk (by rw [h1]; exact one_mem _)
    rw [Subgroup.mem_bot, h0, pow_zero]
  have hMc : Nat.card M = 3 ^ 6 := by
    rw [hM, Subgroup.card_map_of_injective S.subtype_injective]
    have h := CFSG.GH74.Uniqueness.SU.SU7.Gen.card_map_mul_card_inf_ker π (A.comap π)
    rw [Subgroup.map_comap_eq_self_of_surjective hπ, inf_eq_right.2 (Subgroup.ker_le_comap π A),
      hker3, hAc] at h
    rw [← h]
    norm_num
  have hψo : Nat.card (Subgroup.zpowers (Γ' b)) = 3 := by
    rw [Nat.card_zpowers, hΓ'b]
    refine orderOf_eq_prime (by rw [← hΓ'b, ← map_pow, hbp, map_one]) fun h => hout ⟨1, ?_⟩
    rw [map_one, h]
  have hBle' : Nat.card B ≤ Nat.card M * Nat.card (Subgroup.zpowers (Γ' b)) := by
    rw [hMc, hψo]
    calc Nat.card B ≤ 3 ^ 7 := hBle
      _ = 3 ^ 6 * 3 := by norm_num
  obtain ⟨t', hπt', ht'2, ht'c⟩ := ModelGen.exists_involution_lift_commute hS hπ
    (hπker.le) (by rw [hker3]; decide) hΓπ ht2
  have ht'1 : (t' : Ω) ≠ 1 := fun h => ht1 (by
    rw [← hπt', show t' = 1 from Subtype.ext h, map_one])
  have htM : ∀ m ∈ M, m * (t' : Ω) = t' * m := by
    rintro _ ⟨s, hs, rfl⟩
    refine ht'c s ?_
    obtain ⟨g, hg⟩ := hπ (twE6T K ℓ f)
    have hst : π s * π g = π g * π s := by
      rw [hg]
      exact Subgroup.mem_centralizer_singleton_iff.1 (hAt hs)
    rw [← hg, hΓπ]
    calc π ⟨(s : Ω) * g * (s : Ω)⁻¹, _⟩ = π s * π g * (π s)⁻¹ := by
          rw [← map_mul, ← map_inv, ← map_mul]
          rfl
      _ = π g := by rw [hst, mul_inv_cancel_right]
  have htb : b * (t' : Ω) = t' * b := ht'c b (by rw [hΓ'b]; exact hψt)
  exact ModelGen.concA_of_actData_lift hp hp2 hS hperf hcore hB e' hΓ'c hΓ'ker hMel' hMker hb hbM
    hbout hbker hBle' ht'1 (by rw [← Subgroup.coe_pow, ht'2, Subgroup.coe_one]) htM htb hW

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Central

end
