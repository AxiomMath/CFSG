module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L129Aux
public import CFSG.GroupTheory.QuasiDihedralFusion.Basic
public import CFSG.Dihedral.DisconnectedInvolutionGraph.CoprimeSylow
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der7
public import CFSG.GH74.GLS.TwoThin.Basic

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Bender.Thm1

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.L127

section Syl

variable {G : Type} [Group G] [Finite G]

theorem sylow_of_maximal_invariant_in {S K R : Subgroup G} (hS2 : IsPGroup 2 ↥S)
    (hKodd : Odd (Nat.card ↥K)) (hRK : R ≤ K) (hR3 : IsPGroup 3 ↥R)
    (hSK : S ≤ normalizer (K : Set G)) (hSR : S ≤ normalizer (R : Set G))
    (hmax : ∀ W : Subgroup G, W ≤ K → IsPGroup 3 ↥W → S ≤ normalizer (W : Set G) → R ≤ W → W = R) :
    Nat.card ↥(R.subgroupOf K) = 3 ^ (Nat.card ↥K).factorization 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let φ : ↥S →* MulAut ↥K := K.normalizerMonoidHom.comp (Subgroup.inclusion hSK)
  let _ : MulDistribMulAction ↥S ↥K := MulDistribMulAction.compHom ↥K φ
  have hsmul : ∀ (a : ↥S) (x : ↥K), ((a • x : ↥K) : G) = (a : G) * x * (a : G)⁻¹ := fun a x => rfl
  have hcop : ¬ 2 ∣ Nat.card ↥K := by
    intro h
    exact (Nat.not_even_iff_odd.mpr hKodd) (even_iff_two_dvd.mpr h)
  have hR' : IsPGroup 3 ↥(R.subgroupOf K) := hR3.comap_of_injective K.subtype K.subtype_injective
  have hinv : CFSG.DisconnectedInvolutionGraph.Helpers.InvariantSubgroup (A := ↥S)
      (R.subgroupOf K) := by
    intro a x hx
    rw [Subgroup.mem_subgroupOf, hsmul]
    exact (Subgroup.mem_normalizer_iff.mp (hSR a.2) x).mp hx
  obtain ⟨P, hRP, hPinv⟩ :=
    CFSG.DisconnectedInvolutionGraph.Helpers.coprime_pgroup_invariant_sylow_containment 2 3 hS2 hcop
      (R.subgroupOf K) hR' hinv
  have hP3 : IsPGroup 3 ↥((P : Subgroup ↥K).map K.subtype) := P.isPGroup'.map _
  have hPK : (P : Subgroup ↥K).map K.subtype ≤ K := Subgroup.map_subtype_le _
  have hSP : S ≤ normalizer (((P : Subgroup ↥K).map K.subtype : Subgroup G) : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨_, hPinv ⟨a, ha⟩ p hp, (hsmul ⟨a, ha⟩ p).symm⟩
    · rintro ⟨p, hp, hph⟩
      have h1 := hPinv ⟨a, ha⟩⁻¹ p hp
      refine ⟨_, h1, ?_⟩
      have h2 := hsmul (⟨a, ha⟩⁻¹) p
      simp only [Subgroup.coe_inv] at h2
      show (((⟨a, ha⟩ : ↥S)⁻¹ • p : ↥K) : G) = h
      rw [h2]
      have : (p : G) = a * h * a⁻¹ := hph
      rw [this]
      group
  have hRP' : R ≤ (P : Subgroup ↥K).map K.subtype := fun x hx => ⟨⟨x, hRK hx⟩, hRP hx, rfl⟩
  have hEq := hmax _ hPK hP3 hSP hRP'
  have hPeq : (P : Subgroup ↥K) = R.subgroupOf K := by
    rw [← hEq]
    exact (Subgroup.comap_map_eq_self_of_injective K.subtype_injective _).symm
  rw [← hPeq]
  exact P.card_eq_multiplicity

theorem card_inf_sylow {K O R : Subgroup G} (hOK : O ≤ K) (hRK : R ≤ K)
    (hO : (O.subgroupOf K).Normal)
    (hR : Nat.card ↥(R.subgroupOf K) = 3 ^ (Nat.card ↥K).factorization 3) :
    Nat.card ↥((R ⊓ O).subgroupOf O) = 3 ^ (Nat.card ↥O).factorization 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let S : Sylow 3 ↥K := Sylow.ofCard (R.subgroupOf K) hR
  let P : Sylow 3 ↥(O.subgroupOf K) := CFSG.QuasiDihedralFusion.sylowInfNormal S (O.subgroupOf K)
  have h1 : Nat.card ↥(P : Subgroup ↥(O.subgroupOf K)) =
      3 ^ (Nat.card ↥(O.subgroupOf K)).factorization 3 := P.card_eq_multiplicity
  have hcardO : Nat.card ↥(O.subgroupOf K) = Nat.card ↥O :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOK).toEquiv
  have hPcard : Nat.card ↥(P : Subgroup ↥(O.subgroupOf K)) = Nat.card ↥((R ⊓ O).subgroupOf O) := by
    have e1 : Nat.card ↥((R ⊓ O).subgroupOf O) = Nat.card ↥(R ⊓ O) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    have e2 : Nat.card ↥(P : Subgroup ↥(O.subgroupOf K)) = Nat.card ↥((R ⊓ O).subgroupOf K) := by
      have hP : (P : Subgroup ↥(O.subgroupOf K)) = (R.subgroupOf K).subgroupOf (O.subgroupOf K) := rfl
      rw [hP, ← Subgroup.inf_subgroupOf_right (R.subgroupOf K) (O.subgroupOf K)]
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
      rw [show R.subgroupOf K ⊓ O.subgroupOf K = (R ⊓ O).subgroupOf K from rfl]
    have e3 : Nat.card ↥((R ⊓ O).subgroupOf K) = Nat.card ↥(R ⊓ O) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hRK)).toEquiv
    rw [e1, e2, e3]
  rw [← hPcard, h1, hcardO]

theorem odd_card_sup_of_normalizes {O R : Subgroup G} (hRN : R ≤ normalizer (O : Set G))
    (hO : Odd (Nat.card ↥O)) (hR3 : IsPGroup 3 ↥R) : Odd (Nat.card ↥(O ⊔ R)) := by
  refine CFSG.GH74.GLS.Stage2.Bender.Thm2.L129.odd_card_of_forall_odd_orderOf fun x => ?_
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right R O hRN
  have hx : (x : G) ∈ (↑(R ⊔ O) : Set G) := by rw [sup_comm]; exact x.2
  rw [hset] at hx
  obtain ⟨r, hr, o, ho, hxe⟩ := Set.mem_mul.1 hx
  obtain ⟨a, ha⟩ := hR3 ⟨r, hr⟩
  have hra : r ^ (3 ^ a) = 1 := congrArg Subtype.val ha
  have hpow : ∀ n : ℕ, ∃ o' ∈ O, (r * o) ^ n = r ^ n * o' := by
    intro n
    induction n with
    | zero => exact ⟨1, O.one_mem, by simp⟩
    | succ n ih =>
      obtain ⟨o', ho', h⟩ := ih
      refine ⟨r⁻¹ * o' * r * o, ?_, ?_⟩
      · refine O.mul_mem ?_ ho
        have := (Subgroup.mem_normalizer_iff.mp (hRN (R.inv_mem hr)) o').mp ho'
        simpa [mul_assoc] using this
      · rw [pow_succ, h, pow_succ]
        group
  obtain ⟨o', ho', hpo⟩ := hpow (3 ^ a)
  rw [hra, one_mul] at hpo
  have hodd' : Odd (orderOf o') := by
    have h1 : orderOf (⟨o', ho'⟩ : ↥O) ∣ Nat.card ↥O := orderOf_dvd_natCard _
    have h2 : orderOf (⟨o', ho'⟩ : ↥O) = orderOf o' := (Subgroup.orderOf_coe (⟨o', ho'⟩ : ↥O)).symm
    rw [← h2]
    exact Odd.of_dvd_nat hO h1
  have hxK : orderOf (x : G) ∣ 3 ^ a * orderOf o' := by
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [pow_mul, ← hxe, hpo]
    exact pow_orderOf_eq_one o'
  have hox : orderOf x = orderOf (x : G) := (Subgroup.orderOf_coe x).symm
  rw [hox]
  exact Odd.of_dvd_nat (Odd.mul (Odd.pow (by decide)) hodd') hxK

theorem inf_sylow_of_maximal {S M R : Subgroup G} (hSM : S ≤ M) (hS2 : IsPGroup 2 ↥S) (hRM : R ≤ M)
    (hR3 : IsPGroup 3 ↥R) (hSR : S ≤ normalizer (R : Set G))
    (hmax : ∀ W : Subgroup G, W ≤ M → IsPGroup 3 ↥W → S ≤ normalizer (W : Set G) → R ≤ W → W = R) :
    Nat.card ↥((R ⊓ pPrimeCoreOf 2 M).subgroupOf (pPrimeCoreOf 2 M)) =
      3 ^ (Nat.card ↥(pPrimeCoreOf 2 M)).factorization 3 := by
  have hOM : pPrimeCoreOf 2 M ≤ M := CFSG.GH74.GLS.TwoThin.pPrimeCoreOf_le M
  have hMO : M ≤ normalizer ((pPrimeCoreOf 2 M : Subgroup G) : Set G) := le_normalizer_pPrimeCoreOf M
  have hOodd : Odd (Nat.card ↥(pPrimeCoreOf 2 M)) := odd_card_pPrimeCoreOf M
  have hRN : R ≤ normalizer ((pPrimeCoreOf 2 M : Subgroup G) : Set G) := hRM.trans hMO
  have hKodd : Odd (Nat.card ↥(pPrimeCoreOf 2 M ⊔ R)) := odd_card_sup_of_normalizes hRN hOodd hR3
  have hKM : pPrimeCoreOf 2 M ⊔ R ≤ M := sup_le hOM hRM
  have hSO : S ≤ normalizer ((pPrimeCoreOf 2 M : Subgroup G) : Set G) := hSM.trans hMO
  have hSK : S ≤ normalizer ((pPrimeCoreOf 2 M ⊔ R : Subgroup G) : Set G) := fun s hs =>
    Subgroup.inf_normalizer_le_normalizer_sup (pPrimeCoreOf 2 M) R ⟨hSO hs, hSR hs⟩
  have hKO : ((pPrimeCoreOf 2 M).subgroupOf (pPrimeCoreOf 2 M ⊔ R)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
      (sup_le Subgroup.le_normalizer hRN)
  have hRS := sylow_of_maximal_invariant_in hS2 hKodd le_sup_right hR3 hSK hSR
    (fun W hWK hW3 hSW hRW => hmax W (hWK.trans hKM) hW3 hSW hRW)
  exact card_inf_sylow le_sup_left le_sup_right hKO hRS

end Syl

end CFSG.GH74.GLS.Stage2.Bender.Thm2.L127
