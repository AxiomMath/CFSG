
module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsLocal
public import CFSG.LocalAnalysis.SectionRank.SporadicCatalogBase
public import CFSG.LocalAnalysis.SectionRank.ExceptionalEvenCatalog

public section

namespace CFSG.SectionRank

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Simplicity

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem center_titsGroup_eq_bot
    (hK : Nat.card K = 2) :
    Subgroup.center (commutator (reeFixed ReeTag.F4 K 0)) = ⊥ := by
  set D := commutator (reeFixed ReeTag.F4 K 0)
  set N : Subgroup (reeFixed ReeTag.F4 K 0) := (Subgroup.center D).map D.subtype
  have hN : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨z, hz, rfl⟩ := hn
    have hgz : g * (z : reeFixed ReeTag.F4 K 0) * g⁻¹ ∈ D :=
      (Subgroup.commutator_normal ⊤ ⊤).conj_mem _ z.2 g
    refine ⟨⟨_, hgz⟩, Subgroup.mem_center_iff.2 fun d => ?_, rfl⟩
    have hd : g⁻¹ * (d : reeFixed ReeTag.F4 K 0) * g ∈ D := by
      have := (Subgroup.commutator_normal ⊤ ⊤).conj_mem _ d.2 g⁻¹
      rwa [inv_inv] at this
    have hc := Subgroup.mem_center_iff.1 hz ⟨_, hd⟩
    have hc' := congrArg Subtype.val hc
    simp only [Subgroup.coe_mul] at hc'
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    calc (d : reeFixed ReeTag.F4 K 0) * (g * z * g⁻¹) =
        g * ((g⁻¹ * d * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * d * g)) * g⁻¹ := by rw [hc']
      _ = g * z * g⁻¹ * d := by group
  rcases (titsData K hK).le_of_normal hK N with h | h
  · rw [eq_bot_iff]
    intro z hz
    have : (z : reeFixed ReeTag.F4 K 0) ∈ N := ⟨z, hz, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).2 (Subtype.ext this)
  · exfalso
    obtain ⟨x, y, -, -, -, hxy, -⟩ := Tits_sylow3_cubic_witness (K := K) hK
    have hx : (x : reeFixed ReeTag.F4 K 0) ∈ N := h x.2
    obtain ⟨z, hz, hzx⟩ := hx
    have hzx' : z = x := Subtype.ext hzx
    rw [hzx'] at hz
    apply hxy
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.1 hz y).symm

omit [Finite K] [CharP K ReeTag.F4.prime] in
theorem exists_mulEquiv_titsGroup_of_model
    {S : Type} [Group S] {p f : ℕ}
    (h : ReeTitsModel S .Tits p f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K ReeTag.F4.prime),
      Nat.card K = 2 ∧ Nonempty (S ≃* commutator (reeFixed ReeTag.F4 K 0)) := by
  obtain ⟨⟨-, -, -, hp, hf1⟩, a, hf, hmodel⟩ := h
  subst hp
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmodel
  have ha : a = 0 := by omega
  subst ha
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK2 : Nat.card K = 2 := by rw [hK, hf1, pow_one]
  have hc : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have hc' : CharP K ReeTag.F4.prime := hc
  have e' := e.trans (CFSG.LieType.BorelTits.derivedCentralQuotientEquiv _
    ((MulEquiv.subgroupCongr (reeFixedGroup_eq_map_reeFixed ReeTag.F4 K 0)).trans
      ((reeFixed ReeTag.F4 K 0).equivMapOfInjective _ Subtype.val_injective).symm))
  exact ⟨K, inferInstance, inferInstance, hc', hK2, ⟨e'.trans
    ((QuotientGroup.quotientMulEquivOfEq (center_titsGroup_eq_bot hK2)).trans
      QuotientGroup.quotientBot)⟩⟩

theorem Tits_perfect_odd_cover_trivial
    (hK : Nat.card K = 2) {E : Type*} [Group E] [Finite E]
    [Group.IsPerfect E] (π : E →* commutator (reeFixed ReeTag.F4 K 0))
    (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E)
    (hodd : Odd (Nat.card π.ker)) : π.ker = ⊥ := by
  have hdvd := TitsOrder.Tits_commutator_card_dvd (K := K) hK
  have hfac : 35942400 = (2 ^ 12 * 3 ^ 3 * 5 ^ 2) * [13].prod := by norm_num
  refine ker_eq_bot_of_sylow_kernel_eq_bot π hπ hC hodd fun r hr hr2 hsq _ Cp => ?_
  by_cases h3 : r = 3
  · subst h3
    obtain ⟨x, y, h, hx, hy, hz, hzx, hzy, hQ, hhx, hhy, hhz⟩ :=
      Tits_sylow3_cubic_witness (K := K) hK
    exact OddCover.cubic_extraspecial_sylow_central_kernel π hπ hC hx hy hz hzx hzy hQ
      (fun h4 => absurd (h4.trans hdvd) (by decide)) hhx hhy hhz (by decide +revert) Cp
  by_cases h5 : r = 5
  · subst h5
    obtain ⟨x, y, h, hx, hy, hxy, hQ, hhx, hhy⟩ := Tits_sylow5_square_witness (K := K) hK
    exact sylow_kernel_eq_bot_of_square_witness π hπ hC hx hy hxy hQ
      (fun h4 => absurd (h4.trans hdvd) (by decide)) hhx hhy (by decide +revert) Cp
  · exfalso
    have hsq' := hsq.trans hdvd
    rw [hfac] at hsq'
    exact not_sq_dvd_of_factorization hr (Nat.Coprime.mul_right (Nat.Coprime.mul_right
      (coprime_pow_of_ne hr Nat.prime_two hr2 _) (coprime_pow_of_ne hr Nat.prime_three h3 _))
      (coprime_pow_of_ne hr (by norm_num) h5 _)) _ (by norm_num) (by decide) hsq'

theorem catalog_tits :
    TitsCatalogHyp := by
  intro L _ _ hL hSQT hodd f h
  have : Group.IsPerfect L := hL.1
  obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_titsGroup_of_model h
  exact (catalogStepConclusion_of_perfect_odd_cover_trivial hSQT hodd e
    fun π hπ hC hπodd => Tits_perfect_odd_cover_trivial hK π hπ hC hπodd).2

end CFSG.SectionRank
