module

public import CFSG.RankThree.SteinbergR3ESuzukiInvolutionCentralizers
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Embed

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.LieType.Ree CFSG.EvenSporadicStandard.Solomon78
  CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def SzEightModel : Prop :=
  ∀ (K : Type) [Group K] [Finite K], SuzukiModel K 2 3 →
    (∃ E : Subgroup K, (∀ x ∈ E, x * x = 1) ∧ (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧
      Nat.card E = 8) ∧
    ∀ α : MulAut K, α ≠ 1 → α * α = 1 → ¬ TwoSubgroupsAbelian ↥(fixSubgroup α)

section Suzuki

variable {F : Type} [Field F] [Finite F]

theorem suzukiZ0_facts (hF : Nat.card F = 2 ^ (2 * 1 + 1)) :
    (∀ x ∈ suzukiZ0 1 F, x * x = 1) ∧ (∀ x ∈ suzukiZ0 1 F, ∀ y ∈ suzukiZ0 1 F, x * y = y * x) ∧
      Nat.card (suzukiZ0 1 F) = 8 := by
  have h2 : (2 : F) = 0 := (suzuki_frob_data 1 hF).1
  obtain ⟨-, -, hcoe, -, hcomm, -⟩ := suzuki_unipotent_structure hF
  refine ⟨fun x hx => ?_, hcomm, ?_⟩
  · obtain ⟨v, rfl⟩ := (mem_suzukiZ0_iff hF).1 hx
    rw [suzukiSElt_mul hF, add_zero, zero_pow (by positivity), zero_mul, add_zero, ← two_mul, h2,
      zero_mul, suzukiSElt_zero_zero hF]
  · rw [← SetLike.coe_sort_coe, hcoe,
      Nat.card_range_of_injective (fun v w h => (suzukiSElt_inj.1 h).2), hF]
    norm_num

theorem exists_ne_zero_one (hF : Nat.card F = 2 ^ (2 * 1 + 1)) : ∃ u : F, u ≠ 0 ∧ u ≠ 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have : Fintype F := Fintype.ofFinite F
  have hsub : (Finset.univ : Finset F) ⊆ {0, 1} := by
    intro u _
    by_cases h0 : u = 0
    · simp [h0]
    · simp [hcon u h0]
  have := Finset.card_le_card hsub
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hF] at this
  have h2 := Finset.card_le_two (a := (0 : F)) (b := 1)
  omega

theorem suzukiU_not_commutative (hF : Nat.card F = 2 ^ (2 * 1 + 1)) :
    ∃ x ∈ suzukiU 1 F, ∃ y ∈ suzukiU 1 F, x * y ≠ y * x := by
  classical
  obtain ⟨u, hu0, hu1⟩ := exists_ne_zero_one hF
  refine ⟨suzukiSElt 1 F 1 0, suzukiSElt_mem_suzukiU 1 F 1 0, suzukiSElt 1 F u 0,
    suzukiSElt_mem_suzukiU 1 F u 0, fun h => ?_⟩
  rw [suzukiSElt_mul hF, suzukiSElt_mul hF, suzukiSElt_inj] at h
  have h4 : u ^ 4 = u := by simpa using h.2.symm
  have : Fintype F := Fintype.ofFinite F
  have h8 : u ^ 8 = u := by
    have := FiniteField.pow_card u
    rwa [← Nat.card_eq_fintype_card, hF] at this
  have h2 : u * (u - 1) = 0 := by
    have : u ^ 8 = u ^ 2 := by
      calc u ^ 8 = u ^ 4 * u ^ 4 := by ring
        _ = u * u := by rw [h4]
        _ = u ^ 2 := by ring
    linear_combination this.symm.trans h8
  rcases mul_eq_zero.1 h2 with h | h
  · exact hu0 h
  · exact hu1 (sub_eq_zero.1 h)

theorem sylow_not_commutative (hF : Nat.card F = 2 ^ (2 * 1 + 1))
    (P : Sylow 2 (suzukiGroup 1 F)) : ∃ x ∈ P, ∃ y ∈ P, x * y ≠ y * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_suzukiGroup hF
  let Pu : Sylow 2 (suzukiGroup 1 F) :=
    Sylow.ofCard (suzukiU 1 F) (CFSG.RankThree.card_suzukiU_eq hF)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (suzukiGroup 1 F) Pu P
  obtain ⟨x, hx, y, hy, hxy⟩ := suzukiU_not_commutative hF
  refine ⟨g * x * g⁻¹, ?_, g * y * g⁻¹, ?_, fun h => hxy ?_⟩
  · rw [← hg, CFSG.RankThree.mem_smul_sylow_iff, show g⁻¹ * (g * x * g⁻¹) * g = x by group]
    exact hx
  · rw [← hg, CFSG.RankThree.mem_smul_sylow_iff, show g⁻¹ * (g * y * g⁻¹) * g = y by group]
    exact hy
  · have h' := congrArg (fun z => g⁻¹ * z * g) h
    simpa [mul_assoc] using h'

theorem centralizer_involution (hF : Nat.card F = 2 ^ (2 * 1 + 1)) {z : suzukiGroup 1 F}
    (hz : orderOf z = 2) :
    IsPGroup 2 ↥(Subgroup.centralizer ({z} : Set (suzukiGroup 1 F))) ∧
      ∃ x ∈ Subgroup.centralizer ({z} : Set (suzukiGroup 1 F)),
        ∃ y ∈ Subgroup.centralizer ({z} : Set (suzukiGroup 1 F)), x * y ≠ y * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, -, hCP, -⟩ :=
    (CFSG.RankThree.Suzuki_involution_centralizers_and_inner_odd_centralizers (a := 1)
      (K := F) le_rfl hF).1 z hz
  rw [hCP]
  exact ⟨P.isPGroup', sylow_not_commutative hF P⟩

end Suzuki

section Model


theorem suzukiModel_data {K : Type} [Group K] (h : SuzukiModel K 2 3) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ (2 * 1 + 1) ∧
      Nonempty (K ≃* suzukiGroup 1 F) := by
  obtain ⟨-, a, -, F, _, _, hf, hcard, ⟨e⟩⟩ := h
  have ha : a = 1 := by omega
  subst ha
  exact ⟨F, inferInstance, inferInstance, by rw [hcard], ⟨e⟩⟩

theorem center_eq_bot_of_suzukiModel {K : Type} [Group K] (h : SuzukiModel K 2 3) :
    Subgroup.center K = ⊥ := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := suzukiModel_data h
  obtain ⟨-, -, hsimple⟩ := suzuki_simple (a := 1) le_rfl hF
  have hcenter : Subgroup.center (suzukiGroup 1 F) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (suzukiGroup 1 F)) with
      h | h
    · exact h
    · have h1 := (suzuki_perfect (a := 1) le_rfl hF).1
      rw [(commutator_eq_bot_iff_center_eq_top _).2 h] at h1
      exact absurd h1 bot_ne_top
  have hmap : (Subgroup.center K).map e.toMonoidHom = ⊥ := by
    rw [center_map_equiv, hcenter]
  exact (Subgroup.map_eq_bot_iff_of_injective (f := e.toMonoidHom) (Subgroup.center K)
    e.injective).1 hmap

theorem mem_center_of_conj_eq_one {K : Type} [Group K] {k : K} (h : MulAut.conj k = 1) :
    k ∈ Subgroup.center K := by
  rw [Subgroup.mem_center_iff]
  intro g
  have h3 := congrArg (fun f : MulAut K => f g) h
  simp only [MulAut.conj_apply, MulAut.one_apply] at h3
  calc g * k = (k * g * k⁻¹) * k := by rw [h3]
    _ = k * g := by group

theorem exists_conj_eq_of_involutory {K : Type} [Group K] (hK : SuzukiModel K 2 3)
    {α : MulAut K} (h1 : α ≠ 1) (h2 : α * α = 1) :
    ∃ k : K, orderOf k = 2 ∧ α = MulAut.conj k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd :=
    (CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0} K 2 3 hK).1.2.2
  have hmem : α ∈ inner K := by
    have hα : orderOf (QuotientGroup.mk (s := inner K) α) ∣ 2 :=
      (orderOf_map_dvd (QuotientGroup.mk' (inner K)) α).trans
        (orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h2))
    have hcard : orderOf (QuotientGroup.mk (s := inner K) α) ∣ Nat.card (Outer K) :=
      orderOf_dvd_natCard _
    have h3 : orderOf (QuotientGroup.mk (s := inner K) α) = 1 :=
      Nat.Coprime.eq_one_of_dvd
        (Nat.Coprime.coprime_dvd_left hα (Nat.coprime_two_left.2 hodd)) hcard
    rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
    exact h3
  obtain ⟨k, hk⟩ := hmem
  have hk1 : k ≠ 1 := by
    rintro rfl
    exact h1 (by rw [← hk, map_one])
  have hkk : k * k = 1 := by
    have h3 : MulAut.conj (k * k) = (1 : MulAut K) := by
      rw [map_mul, hk]
      exact h2
    have := mem_center_of_conj_eq_one h3
    rw [center_eq_bot_of_suzukiModel hK, Subgroup.mem_bot] at this
    exact this
  exact ⟨k, orderOf_eq_prime (by rw [pow_two]; exact hkk) hk1, hk.symm⟩

theorem not_twoSubgroupsAbelian_fix {K : Type} [Group K] (hK : SuzukiModel K 2 3)
    {α : MulAut K} (h1 : α ≠ 1) (h2 : α * α = 1) : ¬ TwoSubgroupsAbelian ↥(fixSubgroup α) := by
  obtain ⟨k, hk2, rfl⟩ := exists_conj_eq_of_involutory hK h1 h2
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := suzukiModel_data hK
  have hz : orderOf (e k) = 2 := by rw [MulEquiv.orderOf_eq]; exact hk2
  obtain ⟨hP2, x', hx', y', hy', hxy'⟩ := centralizer_involution hF hz
  have hfix : ∀ y : K, y ∈ fixSubgroup (MulAut.conj k) ↔
      e y ∈ Subgroup.centralizer ({e k} : Set (suzukiGroup 1 F)) := by
    intro y
    rw [Subgroup.mem_centralizer_iff]
    change MulAut.conj k y = y ↔ _
    simp only [MulAut.conj_apply, Set.mem_singleton_iff, forall_eq]
    constructor
    · intro h
      have : e (k * y * k⁻¹) = e y := by rw [h]
      rw [map_mul, map_mul, map_inv] at this
      have h' := congrArg (fun w => w * e k) this
      simpa [mul_assoc] using h'
    · intro h
      apply e.injective
      rw [map_mul, map_mul, map_inv, h]
      group
  intro hab
  have hQ2 : IsPGroup 2 ↥(fixSubgroup (MulAut.conj k)) := by
    intro x
    obtain ⟨n, hn⟩ := hP2 (⟨e x, (hfix x).1 x.2⟩ : ↥(Subgroup.centralizer {e k}))
    refine ⟨n, Subtype.ext (e.injective ?_)⟩
    have := congrArg Subtype.val hn
    simpa [map_pow] using this
  have hcomm := hab ⊤ (hQ2.to_subgroup ⊤)
    ⟨e.symm x', (hfix _).2 (by simpa using hx')⟩ (Subgroup.mem_top _)
    ⟨e.symm y', (hfix _).2 (by simpa using hy')⟩ (Subgroup.mem_top _)
  apply hxy'
  have := congrArg (fun z : ↥(fixSubgroup (MulAut.conj k)) => e (z : K)) hcomm
  simpa using this

theorem szEightModel_proved : SzEightModel := by
  intro K _ _ hK
  refine ⟨?_, fun α h1 h2 => not_twoSubgroupsAbelian_fix hK h1 h2⟩
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := suzukiModel_data hK
  obtain ⟨hsq, hcomm, hcard⟩ := suzukiZ0_facts hF
  refine ⟨(suzukiZ0 1 F).map e.symm.toMonoidHom, ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    show e.symm y * e.symm y = 1
    rw [← map_mul, hsq y hy, map_one]
  · rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    show e.symm y * e.symm z = e.symm z * e.symm y
    rw [← map_mul, ← map_mul, hcomm y hy z hz]
  · rw [Subgroup.card_map_of_injective e.symm.injective]
    exact hcard

end Model

end CFSG.EvenSporadicStandard.Induction
