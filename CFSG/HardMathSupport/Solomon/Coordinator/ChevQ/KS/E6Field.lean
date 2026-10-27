module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.FourUGeneric
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Open
import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04E6F
import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.E6
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.U6Model
import CFSG.Goldschmidt.Steps.G37Transport

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSFourU

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Dickson.I271 Bal209F4Aux
  OuterFourInAux

section Abstract

theorem exists_pow_mul_mem_of_card_le_three_mul {A : Type*} [Group A] [Finite A]
    (D I : Subgroup A) (hD : CFSG.Open.IsElemAbelian 3 D)
    (hle : Nat.card D ≤ 3 * Nat.card ↥(D ⊓ I))
    {φ : A} (hφD : φ ∈ D) (hφI : φ ∉ I) :
    ∀ d ∈ D, ∃ i : ℕ, i < 3 ∧ φ ^ i * d ∈ I := by
  classical
  haveI := hD.1
  have hcomm : ∀ a b : D, a * b = b * a := fun a b => mul_comm' a b
  set N : Subgroup D := (D ⊓ I).subgroupOf D with hN
  haveI hNn : N.Normal := ⟨fun n hn d => by rwa [show d * n * d⁻¹ = n by rw [hcomm d n]; group]⟩
  have hNcard : Nat.card N = Nat.card ↥(D ⊓ I) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : D ⊓ I ≤ D)).toEquiv
  have hmul : Nat.card N * N.index = Nat.card D := Subgroup.card_mul_index N
  have hpos : 0 < Nat.card N := Nat.card_pos
  have hidx3 : N.index ≤ 3 := by
    rw [hNcard] at hpos hmul
    by_contra hcon
    push Not at hcon
    nlinarith
  let φD : D := ⟨φ, hφD⟩
  have hφN : φD ∉ N := fun h => hφI (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 h)).2
  have hidx1 : N.index ≠ 1 := fun h => hφN (Subgroup.index_eq_one.1 h ▸ Subgroup.mem_top _)
  obtain ⟨m, hm⟩ : ∃ m, Nat.card D = 3 ^ m := by
    have hp : IsPGroup 3 D := fun x => ⟨1, Subtype.ext (by simpa using hD.2 x x.2)⟩
    exact (IsPGroup.iff_card.1 hp)
  have hdvd : N.index ∣ 3 ^ m := hm ▸ Subgroup.index_dvd_card N
  have hidx : N.index = 3 := by
    obtain ⟨k, -, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    have hk1 : k ≤ 1 := by
      by_contra h
      push Not at h
      have : 3 ^ 2 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) h
      omega
    interval_cases k
    · exact absurd (by simpa using hk') hidx1
    · simpa using hk'
  have hQcard : Nat.card (D ⧸ N) = 3 := by
    rw [← Subgroup.index_eq_card, hidx]
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hgen : Subgroup.zpowers (QuotientGroup.mk φD : D ⧸ N) = ⊤ := by
    refine zpowers_eq_top_of_prime_card hQcard ?_
    intro h
    exact hφN ((QuotientGroup.eq_one_iff φD).1 h)
  have hφ3 : φ ^ 3 = 1 := by simpa using hD.2 φ hφD
  have hφD3 : φD ^ 3 = 1 := Subtype.ext (by simpa using hφ3)
  have hQφ3 : (QuotientGroup.mk φD : D ⧸ N) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, hφD3]; rfl
  intro d hd
  have hmem : (QuotientGroup.mk (⟨d, hd⟩ : D) : D ⧸ N) ∈
      Subgroup.zpowers (QuotientGroup.mk φD : D ⧸ N) := by
    rw [hgen]; exact Subgroup.mem_top _
  obtain ⟨k, hk, hkq⟩ := Finset.mem_image.1 (mem_zpowers_iff_mem_range_orderOf.1 hmem)
  have hk3 : k < 3 := lt_of_lt_of_le (Finset.mem_range.1 hk)
    (Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hQφ3))
  have hdk : (φD ^ k)⁻¹ * ⟨d, hd⟩ ∈ N := by
    rw [← QuotientGroup.eq, QuotientGroup.mk_pow]
    exact hkq
  have hdkI : (φ ^ k)⁻¹ * d ∈ I := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hdk)).2
  refine ⟨(3 - k) % 3, Nat.mod_lt _ (by norm_num), ?_⟩
  have h : φ ^ ((3 - k) % 3) = (φ ^ k)⁻¹ := by
    interval_cases k
    · simp
    · have h2 : φ ^ ((3 - 1) % 3) = φ ^ 2 := by norm_num
      rw [h2]
      exact eq_inv_of_mul_eq_one_left (by rw [← pow_add]; simpa using hφ3)
    · have h2 : φ ^ ((3 - 2) % 3) = φ ^ 1 := by norm_num
      rw [h2]
      exact eq_inv_of_mul_eq_one_left (by rw [← pow_add]; simpa using hφ3)
  rw [h]
  exact hdkI

theorem orderOf_eq_three_of_odd_ringAut {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ 3) ^ 2) {η : K ≃+* K} (hη1 : η ≠ 1) (hηodd : Odd (orderOf η)) :
    orderOf η = 3 := by
  have hK6 : Nat.card K = 2 ^ 6 := by rw [hK]; norm_num
  have hcard : Nat.card (K ≃+* K) = 6 :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K hK6).1
  have h6 : orderOf η ∣ 6 := hcard ▸ orderOf_dvd_natCard η
  have hle : orderOf η ≤ 6 := Nat.le_of_dvd (by norm_num) h6
  have hne1 : orderOf η ≠ 1 := fun h => hη1 (orderOf_eq_one_iff.1 h)
  have hpos : 0 < orderOf η := orderOf_pos η
  obtain ⟨n, hn⟩ : ∃ n, n = orderOf η := ⟨_, rfl⟩
  rw [← hn] at h6 hle hne1 hpos hηodd ⊢
  interval_cases n
  all_goals first
    | rfl
    | exact absurd rfl hne1
    | exact absurd hηodd (by decide)
    | exact absurd h6 (by decide)

end Abstract

section Certs

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem kd26_twE6Eight (S : Type) [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (d : TauCeti.ValidLieTypeIndex) (hd : IsTwE6EightIndex d.1)
    (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) (D : Subgroup (MulAut S))
    (hD : CFSG.Open.IsElemAbelian 3 D) :
    Nat.card D ≤ 3 * Nat.card ↥(D ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner S) := by
  refine CFSG.LocalAnalysis.GLTheoremA.kd26fE6_holds S hS hna 8 false ?_ ?_ D hD
  · obtain ⟨d₀, hv⟩ := d
    cases d₀ with
    | twistedE6 q =>
      refine ⟨.lie ⟨.twistedE6 q, hv⟩, ?_, ⟨e⟩⟩
      have hq : q.card = 8 := by
        rw [TauCeti.PrimePower.card_def, hd.1, hd.2]; norm_num
      simpa [CFSG.Yardstones.Md0ec50421ce4.onLie, CFSG.LocalAnalysis.GLTheoremA.isE6Eps] using hq
    | _ => exact hd.elim
  · norm_num [CFSG.LocalAnalysis.GLTheoremA.qEps]

open CFSG.LocalAnalysis.GLTheoremA in
theorem inner_of_inndiag_comm_fieldActor {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (h3 : 3 ∣ ℓ ^ f + 1) {η : K ≃+* K} (hη : orderOf η = 3)
    {δ : MulAut (twistedE6RootGroup K σ)} (hδ : δ ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ)
    (hcomm : δ * fieldActor σ η = fieldActor σ η * δ) : δ ∈ twistedE6Inn K σ := by
  classical
  have hσ2 : σ ^ 2 = 1 := by
    obtain ⟨σ', hσ', hord, -⟩ := finite_graph_field_parameter_fields TwistTag.E6 hℓ hf K hK
    have hσσ' : σ' = σ := RingEquiv.ext fun c => by rw [hσ', hσ]
    rw [hσσ'] at hord
    rw [← pow_orderOf_eq_one σ, hord]
    rfl
  have hσσ : ∀ c, σ (σ c) = c :=
    CFSG.SeitzReduction.TwistedE6Pilot.sigma_apply_apply_of_sq_eq_one_twistedE6 hσ2
  have h3K : 3 ∣ Nat.card K - 1 := by
    have hq : ℓ ^ f % 3 = 2 := by omega
    have h1 : (ℓ ^ f) ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hq]
    rw [hK]
    omega
  have hT' := YS04E6F.exists_cube_of_fixed η hη h3K
  obtain ⟨g, u, hδ'⟩ := (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.mem_twJ_iff σ).1 hδ
  rw [hδ'] at hcomm
  have hmat := YS04E6F.eq_of_comm_tw σ η hcomm
  have hdC := YS04E6F.rootDiagUnit_mem_adjointGroup_of_twist η (YS04E6F.hcube_E6 η hT')
    (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twistedE6RootGroup_le σ g.2) _ hmat
  rw [hδ']
  exact YS04E6F.mem_inner_of_diag_mem σ hσσ g u hdC

theorem fieldAutTwE6_model {S : Type} [Group S] {φ : MulAut S} (h : FieldAutTwE6 S φ) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σE : K ≃+* K)
      (eC : S ≃* twistedE6RootGroup K σE) (η : K ≃+* K) (γ : MulAut (twistedE6RootGroup K σE)),
      Nat.card K = (2 ^ 3) ^ 2 ∧ (∀ c, σE c = c ^ (2 ^ 3)) ∧ η ≠ 1 ∧ Odd (orderOf η) ∧
      γ * MulAut.congr eC φ * γ⁻¹ = fieldActor σE η := by
  obtain ⟨K, _, _, σq, e, η, γ, hK, hσq, hη1, hηodd, hent⟩ := h
  have hsurj : Function.Surjective σq := Finite.surjective_of_injective σq.injective
  obtain ⟨σE, hσE⟩ : ∃ σE : K ≃+* K, σE.toRingHom = σq :=
    ⟨RingEquiv.ofBijective σq ⟨σq.injective, hsurj⟩, RingHom.ext fun _ => rfl⟩
  subst hσE
  have hK' : Nat.card K = (2 ^ 3) ^ TwistTag.E6.order := hK
  let eC0 := CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.derivedCentralQuotientEquiv
    (t := TwistTag.E6) (p := 2) (f := 3) Nat.prime_two (by norm_num) hK' σE.toRingHom
    (fun c => hσq c)
  refine ⟨K, inferInstance, inferInstance, σE, e.trans eC0, η, MulAut.congr eC0 γ, hK,
    fun c => hσq c, hη1, hηodd, ?_⟩
  refine MulEquiv.ext fun c => ?_
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (eC0.symm c)
  have hc : c = eC0 (QuotientGroup.mk g) := by
    rw [hg]
    exact (eC0.apply_symm_apply c).symm
  obtain ⟨g', hg'1, hg'2⟩ := hent g
  have hconj : MulAut.congr (e.trans eC0) φ = MulAut.congr eC0 (MulAut.congr e φ) :=
    MulEquiv.ext fun x => rfl
  have hL : (MulAut.congr eC0 γ * MulAut.congr (e.trans eC0) φ * (MulAut.congr eC0 γ)⁻¹) c =
      eC0 ((γ * MulAut.congr e φ * γ⁻¹) (QuotientGroup.mk g)) := by
    rw [hconj, ← map_inv, ← map_mul, ← map_mul, MulAut.congr_apply, hc]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [hL, hg'2]
  refine Subtype.ext ?_
  have hcg : ((c : twistedE6RootGroup K σE) : ModGL TwistTag.E6.tag K) =
      (g : ModGL TwistTag.E6.tag K) := by
    rw [hc]; rfl
  change ((g' : ModGL TwistTag.E6.tag K)) =
    Units.map (entrywiseHom η.toRingHom) (c : ModGL TwistTag.E6.tag K)
  rw [hg'1, hcg]

theorem fieldAutTwE6_of_model {S : Type} [Group S] {φ : MulAut S} {K : Type} [Field K] [Finite K]
    (σE : K ≃+* K) (eC : S ≃* twistedE6RootGroup K σE) (η : K ≃+* K)
    (γ : MulAut (twistedE6RootGroup K σE)) (hK : Nat.card K = (2 ^ 3) ^ 2)
    (hσE : ∀ c, σE c = c ^ (2 ^ 3)) (hη1 : η ≠ 1) (hηodd : Odd (orderOf η))
    (h : γ * MulAut.congr eC φ * γ⁻¹ = fieldActor σE η) : FieldAutTwE6 S φ := by
  have hK' : Nat.card K = (2 ^ 3) ^ TwistTag.E6.order := hK
  let eC0 := CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.derivedCentralQuotientEquiv
    (t := TwistTag.E6) (p := 2) (f := 3) Nat.prime_two (by norm_num) hK' σE.toRingHom
    (fun c => hσE c)
  refine ⟨K, inferInstance, inferInstance, σE.toRingHom, eC.trans eC0.symm, η,
    MulAut.congr eC0.symm γ, hK, fun c => hσE c, hη1, hηodd, ?_⟩
  intro g
  have hconj : MulAut.congr eC0.symm γ * MulAut.congr (eC.trans eC0.symm) φ *
      (MulAut.congr eC0.symm γ)⁻¹ = MulAut.congr eC0.symm (fieldActor σE η) := by
    rw [← h, map_mul, map_mul, map_inv]
    rfl
  obtain ⟨g', hg'⟩ := QuotientGroup.mk_surjective
    (eC0.symm (fieldActor σE η (eC0 (QuotientGroup.mk g))))
  refine ⟨g', ?_, ?_⟩
  · have h1 : eC0 (QuotientGroup.mk g') = fieldActor σE η (eC0 (QuotientGroup.mk g)) := by
      rw [hg', MulEquiv.apply_symm_apply]
    have h2 := congrArg (fun z : twistedE6RootGroup K σE => (z : ModGL TwistTag.E6.tag K)) h1
    exact h2
  · rw [hconj, MulAut.congr_apply, hg']
    rfl

theorem fieldAutTwE6_not_inner {S : Type} [Group S] {φ : MulAut S} (h : FieldAutTwE6 S φ) :
    φ ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner S := by
  obtain ⟨K, _, _, σE, eC, η, γ, hK, hσ, hη1, hηodd, hγ⟩ := fieldAutTwE6_model h
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two
      (by norm_num : 1 ≤ 3) K hK σE hσ
  rintro ⟨s, hs⟩
  have h2 : MulAut.congr eC φ = MulAut.conj (eC s) := by
    refine MulEquiv.ext fun x => ?_
    rw [← hs]
    simp [MulAut.congr_apply]
  have h1 : Θ (fieldActor σE η) = η :=
    hΘ _ 1 1 η (by rw [map_one, map_one, one_mul, one_mul])
  have h3 : Θ (MulAut.conj (eC s)) = 1 :=
    hΘ _ (eC s) 1 1 (by rw [map_one, fieldActor_one, mul_one, mul_one])
  have h4 : Θ (fieldActor σE η) = 1 := by
    rw [← hγ, map_mul, map_mul, map_inv, h2, h3]
    group
  exact hη1 (h1.symm.trans h4)

open CFSG.GH74.GLS.Stage2.Signalizer.Odd87 (innSub)


theorem twE6Eight_autImage_structure {X : Type} [Group X] [Finite X] (K B : Subgroup X)
    (hKc : CFSG.Open.IsComponentOf K ⊤) (hB : IsSCp 3 ⊤ B)
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) (hLie : IsLieQuot ↥K IsTwE6EightIndex)
    (hF : ∃ φ ∈ autImage B K, FieldAutTwE6 (↥K ⧸ Subgroup.center ↥K) φ) :
    ∃ φ ∈ autImage B K, FieldAutTwE6 (↥K ⧸ Subgroup.center ↥K) φ ∧
      φ ∉ innSub (↥K ⧸ Subgroup.center ↥K) ∧
      ∀ d ∈ autImage B K, ∃ i : ℕ, i < 3 ∧ φ ^ i * d ∈ innSub (↥K ⧸ Subgroup.center ↥K) := by
  classical
  obtain ⟨φ, hφD, hφF⟩ := hF
  have hq := hKc.2.2
  have hS : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hq.2
  have hna := (OuterFourInAux.D4FixedAux.isQuasisimple_of_open_aux hq).2.2
  have hel : CFSG.Open.IsElemAbelian 3 (autImage B K) := by
    have hB' : CFSG.Open.IsElemAbelian 3 (B ⊓ Subgroup.normalizer (K : Set X)) :=
      CFSG.LocalAnalysis.GLTheoremA.YS04F.isElemAbelian_of_le' inf_le_left hB.2.1
    exact CFSG.Open.IsElemAbelian.map
      (CFSG.Goldschmidt.SStarTransport.isElemAbelian_subgroupOf hB' _) _
  obtain ⟨d, hd, ⟨e⟩⟩ := hLie
  have hkd := kd26_twE6Eight _ hS hna d hd e (autImage B K) hel
  exact ⟨φ, hφD, hφF, fieldAutTwE6_not_inner hφF,
    exists_pow_mul_mem_of_card_le_three_mul (autImage B K) _ hel hkd hφD
      (fieldAutTwE6_not_inner hφF)⟩

theorem exists_conj_fieldActor_of_commute {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ 3) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ 3))
    {η : K ≃+* K} (hη : orderOf η = 3) {α : MulAut (twistedE6RootGroup K σ)} (hα3 : α ^ 3 = 1)
    (hc : α * fieldActor σ η = fieldActor σ η * α) (hαin : α ∉ twistedE6Inn K σ) :
    ∃ (η' : K ≃+* K) (ψ : MulAut (twistedE6RootGroup K σ)), η' ≠ 1 ∧ Odd (orderOf η') ∧
      ψ * α * ψ⁻¹ = fieldActor σ η' := by
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -, hker, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two
      (by norm_num : 1 ≤ 3) K hK σ hσ
  have hΘα : Θ α ≠ 1 := by
    intro h1
    have hmem : α ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ := by
      rw [← hker]
      exact MonoidHom.mem_ker.2 h1
    exact hαin (inner_of_inndiag_comm_fieldActor Nat.prime_two (by norm_num) hK σ hσ
      (by norm_num) hη hmem hc)
  have hK' : Nat.card K = 2 ^ (2 * 3) := by rw [hK]; norm_num
  obtain ⟨-, -, -, -, -, -, ψ, -, hψ⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.twisted_E6_field_descent_conj_of_prime_order
      Nat.prime_two (by norm_num) K hK' σ hσ Θ hΘ Nat.prime_three (by norm_num) α hα3 hΘα
  refine ⟨Θ α, ψ, hΘα, ?_, hψ⟩
  have hpow : (Θ α) ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
  rw [orderOf_eq_prime hpow hΘα]
  decide

theorem e6FourUField : FourUField IsTwE6EightIndex FieldAutTwE6 := by
  intro X _ _ K B hK hBSC hBN hLie hF
  have hperf : commutator ↥K = ⊤ := hK.2.2.1
  have hBel : IsElemAbelian 3 B := hBSC.2.1
  obtain ⟨φ, hφB, hφF, hφnot, hdec⟩ := twE6Eight_autImage_structure K B hK hBSC hBN hLie hF
  obtain ⟨x, hxN, hxB, rfl⟩ := mem_autImage.1 hφB
  obtain ⟨K', fK', hfin, σE, eC, η, γ, hK64, hσE, hη1, hηodd, hγ⟩ := fieldAutTwE6_model hφF
  have hη3 : orderOf η = 3 := orderOf_eq_three_of_odd_ringAut hK64 hη1 hηodd
  let Ψ : ↥(Subgroup.normalizer (K : Set X)) →* MulAut (twistedE6RootGroup K' σE) :=
    ((MulAut.conj γ).toMonoidHom).comp ((MulAut.congr eC).toMonoidHom.comp (actHom K))
  have hΨ : ∀ n, Ψ n = γ * MulAut.congr eC (actHom K n) * γ⁻¹ := fun n => by
    simp [Ψ, MulAut.conj_apply]
  have hΨx : Ψ ⟨x, hxN⟩ = fieldActor σE η := by rw [hΨ]; exact hγ
  have hinner : ∀ (b : X) (hb : b ∈ B), InnerAt K b ↔
      Ψ ⟨b, hBN hb⟩ ∈ innSub (twistedE6RootGroup K' σE) := by
    intro b hb
    rw [innerAt_iff_congr_mem_innSub hperf eC (hBN hb), hΨ, mem_innSub_iff_conj]
  have hcomm : ∀ (b b' : X) (hb : b ∈ B) (hb' : b' ∈ B),
      Ψ ⟨b, hBN hb⟩ * Ψ ⟨b', hBN hb'⟩ = Ψ ⟨b', hBN hb'⟩ * Ψ ⟨b, hBN hb⟩ := by
    intro b b' hb hb'
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (commute_of_elemAbelian hBel hb hb').eq
  have hcube : ∀ (b : X) (hb : b ∈ B), Ψ ⟨b, hBN hb⟩ ^ 3 = 1 := by
    intro b hb
    rw [← map_pow]
    have : (⟨b, hBN hb⟩ : ↥(Subgroup.normalizer (K : Set X))) ^ 3 = 1 :=
      Subtype.ext (hBel.2 b hb)
    rw [this, map_one]
  refine ⟨x, hxB, ?_, ?_, ?_⟩
  · intro hin
    exact hφnot ((innerAt_iff_congr_mem_innSub hperf (MulEquiv.refl _) hxN).1 hin)
  · intro b hb
    obtain ⟨i, -, hi⟩ := hdec (actHom K ⟨b, hBN hb⟩) (mem_autImage.2 ⟨b, hBN hb, hb, rfl⟩)
    have hyB : x ^ i * b ∈ B := B.mul_mem (B.pow_mem hxB i) hb
    have hyN : x ^ i * b ∈ Subgroup.normalizer (K : Set X) := hBN hyB
    refine ⟨i, (innerAt_iff_congr_mem_innSub hperf (MulEquiv.refl _) hyN).2 ?_⟩
    have e1 : actHom K ⟨x ^ i * b, hyN⟩ = actHom K ⟨x, hxN⟩ ^ i * actHom K ⟨b, hBN hb⟩ := by
      rw [← map_pow, ← map_mul]
      rfl
    rw [e1]
    exact hi
  · intro a ha hanot
    have hψa3 : Ψ ⟨a, hBN ha⟩ ^ 3 = 1 := hcube a ha
    have hψnot : Ψ ⟨a, hBN ha⟩ ∉ twistedE6Inn K' σE := fun hmem => hanot ((hinner a ha).2 hmem)
    have hcσ : Ψ ⟨a, hBN ha⟩ * fieldActor σE η = fieldActor σE η * Ψ ⟨a, hBN ha⟩ := by
      rw [← hΨx]
      exact hcomm a x ha hxB
    obtain ⟨η', ψ, hη'1, hη'odd, hψ⟩ :=
      exists_conj_fieldActor_of_commute hK64 σE hσE hη3 hψa3 hcσ hψnot
    refine fieldAutTwE6_of_model σE eC η' (ψ * γ) hK64 hσE hη'1 hη'odd ?_
    rw [← hψ, hΨ]
    simp only [mul_inv_rev, mul_assoc]

end Certs

end KSFourU

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
