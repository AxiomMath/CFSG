module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotPositionPerfect
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotPositionC
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR4Basic

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.ComponentClassification.OuterAutomorphisms

theorem exists_mulAut_normalForm_E7_E8 {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {f : ℕ} (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = 2 ^ f) :
    ∃ φ : MulAut (adjointGroup τ K),
      (∀ β : MulAut (adjointGroup τ K), ∃ (c : adjointGroup τ K) (k : ℕ),
        β = MulAut.conj c * φ ^ k) ∧
      ∀ n : ℕ, φ ^ n ∈ (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range →
        φ ^ n = 1 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  obtain ⟨-, Θ, hΘ, -, hker, -⟩ :=
    even_E7_E8_exact_inner_field_automorphism_normal_form hf K hK τ hτ
  obtain ⟨fr, -, -, hfr, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hf hK
  have hΘφ : Θ (entrywiseAdjointAut τ fr) = fr :=
    hΘ _ 1 fr fun h => by rw [coe_entrywiseAdjointAut, Subgroup.coe_one, one_mul, inv_one, mul_one]
  refine ⟨entrywiseAdjointAut τ fr, fun β => ?_, fun n hn => ?_⟩
  · have : Finite (K ≃+* K) := Finite.of_injective (fun σ : K ≃+* K => (σ : K → K))
      fun a b h => RingEquiv.ext (congrFun h)
    have hmem : Θ β ∈ zpowers fr := by rw [hfr]; exact mem_top _
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 hmem)
    have hker' : β * (entrywiseAdjointAut τ fr ^ k)⁻¹ ∈ Θ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, hΘφ, hk, mul_inv_cancel]
    rw [hker] at hker'
    obtain ⟨c, hc⟩ := hker'
    exact ⟨c, k, by rw [hc]; group⟩
  · have h1 : entrywiseAdjointAut τ fr ^ n ∈ Θ.ker := by rw [hker]; exact hn
    rw [MonoidHom.mem_ker, map_pow, hΘφ] at h1
    rw [← entrywiseAdjointAut_pow, h1, entrywiseAdjointAut_one]

theorem mem_range_conj_of_sq_eq_one_of_odd_E7_E8 {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {f : ℕ}
    (hf : 1 ≤ f) (hodd : Odd f) (K : Type) [Field K] (hK : Nat.card K = 2 ^ f)
    {α : MulAut (adjointGroup τ K)} (hα : α ^ 2 = 1) :
    α ∈ (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range := by
  obtain ⟨-, Θ, -, -, hker, hinv⟩ :=
    even_E7_E8_exact_inner_field_automorphism_normal_form hf K hK τ hτ
  rcases hinv α hα with h | ⟨heven, -⟩
  · rw [← hker]
    exact h
  · exact absurd heven (Nat.not_even_iff_odd.2 hodd)

theorem outerFusionTwoCentral_of_forall_inner {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : StandardSetting G L) {C : Type*} [Group C] (e : L ≃* C)
    (hinn : ∀ α : MulAut C, α ^ 2 = 1 → α ∈ (MulAut.conj : C →* MulAut C).range)
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    F4Pilot.OuterFusionTwoCentral L t := by
  intro g hsC hsL
  exfalso
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  have htC : t ∈ centralizer (L : Set G) := htK.1
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  set s := g⁻¹ * t * g with hsdef
  have hss : s * s = 1 := by
    calc s * s = g⁻¹ * (t * t) * g := by rw [hsdef]; group
      _ = 1 := by rw [htt, mul_one, inv_mul_cancel]
  have hN : s ∈ normalizer (L : Set G) :=
    centralizer_le_normalizer_of_standard hset.standard htC ht hsC
  set α : MulAut L := L.normalizerMonoidHom ⟨s, hN⟩ with hαdef
  have hα : ∀ l : L, ((α l : L) : G) = s * l * s⁻¹ := fun l =>
    Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨s, hN⟩ l
  have hα2 : α ^ 2 = 1 := by
    refine MulEquiv.ext fun l => Subtype.ext ?_
    rw [sq, MulAut.mul_apply, MulAut.one_apply, hα, hα]
    calc s * (s * (l : G) * s⁻¹) * s⁻¹ = (s * s) * l * (s * s)⁻¹ := by group
      _ = l := by rw [hss, one_mul, inv_one, mul_one]
  obtain ⟨l, hl⟩ := (F4Pilot.conj_mem_range_conj_iff e α).1
    (hinn _ ((F4Pilot.pow_two_conj_eq_one_iff e α).2 hα2))
  refine hsL (F4Pilot.mem_sup_zpowers_of_conj_eq htC ht hKt hsC l.2 fun y hy => ?_)
  have h := congrArg (fun φ : MulAut L => ((φ ⟨y, hy⟩ : L) : G)) hl
  simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h
  rw [h, hα]

theorem outerFusionTwoCentral_of_odd_E8 {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : StandardSetting G L) {f : ℕ} (hf : 1 ≤ f) (hodd : Odd f) {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E8 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    F4Pilot.OuterFusionTwoCentral L t :=
  outerFusionTwoCentral_of_forall_inner hset e
    (fun _ hα => mem_range_conj_of_sq_eq_one_of_odd_E7_E8 (Or.inr rfl) hf hodd K hK hα) ht hKt

theorem exists_conj_eq_mul_twoCentral_E8 {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : StandardSetting G L) {f : ℕ} (hf : 2 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E8 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hC1 : F4Pilot.OuterFusionTwoCentral L t) :
    ∃ g : G, ∃ z ∈ L, g⁻¹ * t * g = t * z ∧ z ≠ 1 ∧
      ∃ U : Sylow 2 L, ∀ u ∈ (U : Subgroup L), (u : G) * z = z * u := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK
  have hf1 : 1 ≤ f := by omega
  have hq : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  have htC : t ∈ centralizer (L : Set G) := htK.1
  have hLt : L ≤ centralizer ({t} : Set G) := le_centralizer_of_mem_centralizer htC
  have hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
    centralizer_le_normalizer_of_standard hset.standard htC ht
  have hnot : ∀ g : G, g⁻¹ * t * g ∉ L := conj_not_mem_of_mulEquiv_E8 hset hq e htC ht
  by_cases hout : ∃ g : G, g⁻¹ * t * g ∈ centralizer ({t} : Set G) ∧
      g⁻¹ * t * g ∉ L ⊔ zpowers t
  · obtain ⟨g, hg1, hg2⟩ := hout
    exact hC1 g hg1 hg2
  · simp only [not_exists, not_and, not_not] at hout
    have : IsSimpleGroup G := hset.simple
    obtain ⟨x₀, hx₀, hgen, hlift⟩ := F4Pilot.exists_gen_of_mulAut hCN hLt hKt
      (F4Pilot.exists_mulAut_normalForm_of_mulEquiv e
        (exists_mulAut_normalForm_E7_E8 (Or.inr rfl) hf1 K hK))
    exact F4Pilot.exists_conj_eq_mul_of_forall_inner
      (F4Pilot.two_lt_card_of_exists_mul_ne hset.nonab) ht hLt hCN hnot hout hx₀ hgen hlift

end CFSG.SeitzReduction.E8Pilot
