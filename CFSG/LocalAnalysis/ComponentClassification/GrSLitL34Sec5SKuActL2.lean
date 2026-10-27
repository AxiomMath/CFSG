module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SKuAct
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsOddFour

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.GH74.KGroups Equiv
open CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.UnbalancedCorr
open scoped commutatorElement

theorem exists_fixed_orderOf_two {E : Type*} [Group E] [Finite E] (β : MulAut E)
    (hβ : β * β = 1) (hE : Even (Nat.card E)) : ∃ k : E, orderOf k = 2 ∧ β k = k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := zpowers β with hK
  let : MulAction K E := MulAction.compHom E K.subtype
  have hK2 : IsPGroup 2 K := by
    have hdvd : orderOf β ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, hβ])
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  let F : Subgroup E :=
    { carrier := {e | β e = e}
      mul_mem' := fun {a b} (ha : β a = a) (hb : β b = b) =>
        show β (a * b) = a * b by rw [map_mul, ha, hb]
      one_mem' := map_one β
      inv_mem' := fun {a} (ha : β a = a) => show β a⁻¹ = a⁻¹ by rw [map_inv, ha] }
  have hset : MulAction.fixedPoints K E = (F : Set E) := by
    ext e
    rw [MulAction.mem_fixedPoints]
    constructor
    · intro h
      exact h ⟨β, mem_zpowers β⟩
    · intro h g
      have hst : β ∈ MulAction.stabilizer (MulAut E) e := by
        rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
        exact h
      exact (zpowers_le.mpr hst) g.2
  have hmod := hK2.card_modEq_card_fixedPoints E
  rw [hset] at hmod
  have hF : 2 ∣ Nat.card F := by
    have h1 : Nat.card E % 2 = 0 := Nat.even_iff.mp hE
    have h2 : Nat.card ↥(F : Set E) % 2 = 0 := hmod ▸ h1
    exact Nat.dvd_of_mod_eq_zero h2
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' 2 hF
  exact ⟨k, by rw [Subgroup.orderOf_coe, hk], k.2⟩

variable {G : Type} [Group G] [Finite G]

theorem card_not_odd_of_isPComponent {C J : Subgroup G} (hJC : J ≤ C)
    (hJ : IsPComponent 2 (J.subgroupOf C)) : ¬ Odd (Nat.card J) := by
  intro hodd
  apply GrS4.not_le_coreActionKernel_self hJC hJ
  have htop : (⊤ : Subgroup J) ≤ pPrimeCore 2 J :=
    le_pPrimeCore_of_normal_coprime inferInstance (Nat.coprime_two_left.mpr (by rwa [card_top]))
  intro g hg
  refine mem_coreActionKernel.mpr ⟨le_normalizer hg, fun j hj => ?_⟩
  exact ⟨⟨j⁻¹ * g⁻¹ * j * g, mul_mem (mul_mem (mul_mem (inv_mem hj) (inv_mem hg)) hj) hg⟩,
    htop (mem_top _), rfl⟩

theorem not_commutator_le_of_l2
    {a x : G}
    {J Y : Subgroup G} (htri : GSUnbalancingTriple a x J)
    (hcase : IsL2Type 5 (J ⧸ pPrimeCore 2 J) ∨ IsL2Type 7 (J ⧸ pPrimeCore 2 J))
    (hYodd : Odd (Nat.card Y)) (hYN : Y ≤ normalizer (J : Set G)) (hJY : ¬ ⁅J, Y⁆ ≤ oddIn J) :
    ¬ ⁅J ⊓ centralizer ({x} : Set G), Y⁆ ≤ oddIn J := by
  intro hle
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hx2, -, hxJ', -⟩ := triple_facts htri
  have hxN : x ∈ normalizer (J : Set G) := mem_normalizer_of_closure hxJ' (Set.mem_singleton x)
  obtain ⟨n, M, hF⟩ := exists_l2Model (J := J) hcase
  have hEven : Even (Nat.card (Jhat J)) := by
    obtain ⟨-, -, -, hJa, hJc, -, -⟩ := htri
    rcases Nat.even_or_odd (Nat.card (Jhat J)) with h | h
    · exact h
    · exfalso
      apply card_not_odd_of_isPComponent hJa hJc
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥J)]
      exact h.mul (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
  have hβ2 : betaHat J hxN * betaHat J hxN = 1 :=
    MulEquiv.ext fun e => betaHat_betaHat J hxN hx2 e
  obtain ⟨k, hko, hkx⟩ := exists_fixed_orderOf_two (betaHat J hxN) hβ2 hEven
  obtain ⟨j, hjk, hjx⟩ := exists_fixed_lift hxN hx2 hkx
  have hjc : (j : G) ∈ centralizer ({x} : Set G) := mem_centralizer_of_conj_eq (by
    have := congrArg Subtype.val hjx
    rwa [coe_conjJ] at this)
  have hk2 : ((M.e k : M.P) : Perm (Fin n)) * (M.e k : M.P) = 1 := by
    have h0 : k ^ orderOf k = 1 := pow_orderOf_eq_one k
    rw [hko] at h0
    have h1 : k * k = 1 := by rw [← pow_two]; exact h0
    rw [← Subgroup.coe_mul, ← map_mul, h1, map_one]
    rfl
  have hk1 : ((M.e k : M.P) : Perm (Fin n)) ≠ 1 := by
    intro h1
    have h2 : M.e k = 1 := Subtype.ext h1
    rw [map_eq_one_iff _ M.e.injective] at h2
    rw [h2, orderOf_one] at hko
    exact absurd hko (by norm_num)
  have hρ : ∀ y (hy : y ∈ Y), rhoM M (hYN hy) = 1 := by
    intro y hy
    have hyN := hYN hy
    have hky : betaHat J hyN k = k := by
      rw [← hjk, betaHat_jq, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      have h1 : ⁅(j : G)⁻¹, y⁻¹⁆⁻¹ ∈ oddIn J := inv_mem (hle (commutator_mem_commutator
        (mem_inf.mpr ⟨inv_mem j.2, inv_mem hjc⟩) (inv_mem hy)))
      obtain ⟨o, ho, hoe⟩ := h1
      have hj' : (conjJ J hyN j)⁻¹ * j = o := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjJ]
        rw [Subgroup.coe_subtype] at hoe
        rw [hoe, commutatorElement_def]
        group
      rw [hj']
      exact ho
    have hcomm : rhoM M hyN * ((M.e k : M.P) : Perm (Fin n)) =
        ((M.e k : M.P) : Perm (Fin n)) * rhoM M hyN := by
      have h1 := rhoM_spec M hyN k
      rw [hky] at h1
      calc rhoM M hyN * ((M.e k : M.P) : Perm (Fin n)) =
          rhoM M hyN * ((M.e k : M.P) : Perm (Fin n)) * (rhoM M hyN)⁻¹ * rhoM M hyN := by
            group
        _ = ((M.e k : M.P) : Perm (Fin n)) * rhoM M hyN := by rw [← h1]
    have h16 := hF.inner _ (M.e k).2 hk2 hk1 _ (rhoM_mem M hyN) hcomm
    have hpow : rhoM M hyN ^ orderOf y = 1 := by
      rw [← rhoM_pow M hyN]
      exact rhoM_one M _ (pow_orderOf_eq_one y)
    have hyodd : Odd (orderOf y) := hYodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard Y hy)
    have hcop : Nat.Coprime 2 (orderOf (rhoM M hyN)) :=
      (Nat.coprime_two_left.mpr hyodd).coprime_dvd_right (orderOf_dvd_of_pow_eq_one hpow)
    exact eq_one_of_coprime_of_pow (k := 4) hcop (by
      rw [show (2 : ℕ) ^ 4 = 16 by norm_num]
      exact h16)
  apply hJY
  rw [← closure_conj_commutator_eq_commutator J Y, closure_le]
  rintro _ ⟨j', hj', y, hy, rfl⟩
  exact comm_mem_oddIn_of_rhoM M (hYN hy) (hρ y hy) hj'

end CFSG.ComponentClassification.GrSLit.L34Facts

namespace CFSG.ComponentClassification.GrSLit.GrS5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem l34KuActionL25_holds :
    L34KuActionL25 :=
  fun _ _ _ _ _ _ _ htri h5 hYodd hYN _ hJY =>
    L34Facts.not_commutator_le_of_l2 htri (.inl h5) hYodd hYN hJY

theorem l34KuActionL27_holds :
    L34KuActionL27 :=
  fun _ _ _ _ _ _ _ htri h7 hYodd hYN _ hJY =>
    L34Facts.not_commutator_le_of_l2 htri (.inr h7) hYodd hYN hJY

theorem l34Sec5KuOddStep_of_actionL34
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) (h34 : L34KuActionL34) : L34Sec5KuOddStep :=
  l34Sec5KuOddStep_of_action hS hU hheld hSol hGW hMax
    ⟨l34KuActionL25_holds, l34KuActionL27_holds, h34⟩

end CFSG.ComponentClassification.GrSLit.GrS5S
