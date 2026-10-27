module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.CentralizerCondition
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.CGT.PushingUpLit.ThmOne

open CFSG
open scoped commutatorElement

variable {L : Type*} [Group L]

variable (L) in
theorem pCore_quotient_by_pCore_eq_bot (p : ℕ) : pCore p (L ⧸ pCore p L) = ⊥ := by
  set N : Subgroup L := pCore p L with hN
  set K : Subgroup L := (pCore p (L ⧸ N)).comap (QuotientGroup.mk' N) with hK
  have hKp : IsPGroup p K := by
    rintro ⟨k, hk⟩
    obtain ⟨a, ha⟩ := (pCore_isPGroup (G := L ⧸ N) (p := p)) ⟨_, hk⟩
    have h1 : k ^ p ^ a ∈ N := by
      have := congrArg Subtype.val ha
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
      rwa [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    obtain ⟨b, hb⟩ := (pCore_isPGroup (G := L) (p := p)) ⟨_, h1⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have := congrArg Subtype.val hb
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
    rw [pow_add, pow_mul]
    exact this
  have hKN : K ≤ N := le_sSup ⟨inferInstance, hKp⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hKN hx

variable [Finite L]

theorem eq_bot_of_isPGroup_of_le_fittingSubgroup (h2 : pCore 2 L = ⊥) {S : Subgroup L}
    (hS : IsPGroup 2 S) (hSF : S ≤ fittingSubgroup L) : S = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := (hS.comap_subtype (K := fittingSubgroup L)).exists_le_sylow
  have hle : (T : Subgroup (fittingSubgroup L)).map (fittingSubgroup L).subtype ≤ pCore 2 L :=
    Sylow.map_le_pCore inferInstance inferInstance 2 T
  rw [h2] at hle
  rw [eq_bot_iff]
  intro s hs
  exact hle ⟨⟨s, hSF hs⟩, hT (show (⟨s, hSF hs⟩ : fittingSubgroup L) ∈
    S.subgroupOf (fittingSubgroup L) from hs), rfl⟩

theorem eq_one_of_mem_fittingSubgroup_of_pow (h2 : pCore 2 L = ⊥) {c : L}
    (hc : c ∈ fittingSubgroup L) {k : ℕ} (hk : c ^ 2 ^ k = 1) : c = 1 := by
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
  have hZ : IsPGroup 2 (Subgroup.zpowers c) :=
    IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
  have h := eq_bot_of_isPGroup_of_le_fittingSubgroup h2 hZ (Subgroup.zpowers_le.mpr hc)
  rwa [Subgroup.zpowers_eq_bot] at h

theorem le_pCore_of_isSubnormal_of_isPGroup {p : ℕ} [Fact p.Prime] {S : Subgroup L}
    (hS : S.IsSubnormal) (hp : IsPGroup p S) : S ≤ pCore p L := by
  have h := LocalCores.prime_set_core_subnormal_intersection {q : Nat.Primes | q.val = p} hS
  rw [← pCore_eq_piCore ↥S p, ← pCore_eq_piCore L p] at h
  have htop : pCore p ↥S = ⊤ :=
    top_unique (le_sSup ⟨inferInstance, hp.of_equiv Subgroup.topEquiv.symm⟩)
  rw [htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  exact h.le.trans inf_le_right

theorem mem_centralizer_of_commutator_mem_normalizer (h2 : pCore 2 L = ⊥) {P : Subgroup L}
    (hP : IsPGroup 2 P) {f : L} (hf : f ∈ fittingSubgroup L)
    (h : ∀ p ∈ P, ⁅f, p⁆ ∈ Subgroup.normalizer (P : Set L)) :
    f ∈ Subgroup.centralizer (P : Set L) := by
  rw [Subgroup.mem_centralizer_iff]
  intro p hp
  have hF : ∀ a ∈ fittingSubgroup L, ⁅a, p⁆ ∈ fittingSubgroup L := fun a ha => by
    rw [show ⁅a, p⁆ = a * (p * a⁻¹ * p⁻¹) by rw [commutatorElement_def]; group]
    exact mul_mem ha ((fittingSubgroup_normal (G := L)).conj_mem _ (inv_mem ha) p)
  have hcF := hF f hf
  have hcp : ⁅⁅f, p⁆, p⁆ ∈ P := by
    rw [commutatorElement_def ⁅f, p⁆ p]
    exact mul_mem ((Subgroup.mem_normalizer_iff.mp (h p hp) p).mp hp) (inv_mem hp)
  obtain ⟨j, hj⟩ := hP ⟨_, hcp⟩
  have hcp1 : ⁅⁅f, p⁆, p⁆ = 1 :=
    eq_one_of_mem_fittingSubgroup_of_pow h2 (hF _ hcF) (k := j)
      (by simpa using congrArg Subtype.val hj)
  have hcomm : Commute ⁅f, p⁆ p := commutatorElement_eq_one_iff_mul_comm.mp hcp1
  have hfp : f * p * f⁻¹ = ⁅f, p⁆ * p := by rw [commutatorElement_def]; group
  obtain ⟨k, hk⟩ := hP ⟨p, hp⟩
  have hpk : p ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hpow : f * p ^ 2 ^ k * f⁻¹ = ⁅f, p⁆ ^ 2 ^ k * p ^ 2 ^ k := by
    rw [← conj_pow, hfp, hcomm.mul_pow]
  rw [hpk, mul_one, mul_one, mul_inv_cancel] at hpow
  have hc1 : ⁅f, p⁆ = 1 := eq_one_of_mem_fittingSubgroup_of_pow h2 hcF hpow.symm
  exact (commutatorElement_eq_one_iff_mul_comm.mp hc1).symm

theorem odd_card_fittingSubgroup_of_pCore_two_eq_bot (h2 : pCore 2 L = ⊥) :
    Odd (Nat.card (fittingSubgroup L)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro hdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := fittingSubgroup L) 2 hdvd
  have hx2 : (x : L) ^ 2 ^ 1 = 1 := by
    rw [pow_one, ← Subgroup.coe_pow, ← hx, pow_orderOf_eq_one, Subgroup.coe_one]
  have hx1 : (x : L) = 1 := eq_one_of_mem_fittingSubgroup_of_pow h2 x.2 hx2
  have : x = 1 := Subtype.ext hx1
  rw [this, orderOf_one] at hx
  exact absurd hx (by norm_num)

theorem commutator_fittingSubgroup_eq_bot_of_le_centralizer (h2 : pCore 2 L = ⊥)
    {P Y : Subgroup L} (hP : IsPGroup 2 P) (hYF : Y ≤ fittingSubgroup L)
    (hYP : Y ≤ Subgroup.centralizer (P : Set L))
    (h : ∀ f ∈ fittingSubgroup L, f ∈ Subgroup.centralizer (Y : Set L) →
      f ∈ Subgroup.centralizer (P : Set L)) :
    ⁅fittingSubgroup L, P⁆ = ⊥ := by
  have hsmul : ∀ (a : P) (x : fittingSubgroup L), ((a • x : fittingSubgroup L) : L) =
      (a : L) * x * (a : L)⁻¹ := fun a x =>
    Subgroup.conjMulDistribMulActionOfNormal_smul_coe P (fittingSubgroup L) a x
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hcop : Nat.Coprime (Nat.card P) (Nat.card (fittingSubgroup L)) := by
    rw [hn]
    exact (Nat.coprime_two_left.mpr (odd_card_fittingSubgroup_of_pCore_two_eq_bot h2)).pow_left n
  have hfix : ∀ x : fittingSubgroup L, (x : L) ∈ Subgroup.centralizer (P : Set L) →
      x ∈ fixedPointSubgroup P (fittingSubgroup L) := by
    intro x hx
    rw [FixedPoints.mem_subgroup]
    intro a
    apply Subtype.ext
    rw [hsmul, Subgroup.mem_centralizer_iff.mp hx _ a.2, mul_inv_cancel_right]
  have hC : Subgroup.centralizer (fixedPointSubgroup P (fittingSubgroup L) : Set _) ≤
      fixedPointSubgroup P (fittingSubgroup L) := by
    intro x hx
    refine hfix x (h x x.2 (Subgroup.mem_centralizer_iff.mpr fun y hy => ?_))
    have hyF := hfix ⟨y, hYF hy⟩ (hYP hy)
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hx _ hyF)
  have htriv := actsTrivially_of_nilpotent_coprime_and_centralizer_fixedPointSubgroup
    (G := fittingSubgroup L) (A := P) inferInstance hcop hC
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro f hf p hp
  have hconj : p * f * p⁻¹ = f := by
    simpa [hsmul] using congrArg Subtype.val (htriv ⟨p, hp⟩ ⟨f, hf⟩)
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  calc f * p = p * f * p⁻¹ * p := by rw [hconj]
    _ = p * f := by group

theorem commutator_eq_bot_of_isComponent_of_le_normalizer {J P : Subgroup L}
    (hJ : IsComponent J) (hP : IsPGroup 2 P) (hJP : J ≤ Subgroup.normalizer (P : Set L)) :
    ⁅J, P⁆ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJK : J ≤ J ⊔ P := le_sup_left
  have hPn : (P.subgroupOf (J ⊔ P)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (sup_le hJP Subgroup.le_normalizer)
  have : Group.IsNilpotent (P.subgroupOf (J ⊔ P)) := (hP.comap_subtype).isNilpotent
  have h := (LocalCores.component_solvable_centralizer inferInstance hPn.isSubnormal).1 _
    (LocalCores.component_overgroup hJ hJK)
  have h' := LocalCores.commutator_inf_eq_bot_of_subgroupOf hJK h
  rwa [inf_eq_left.mpr le_sup_right] at h'

theorem eq_bot_of_commutator_eq_bot (h2 : pCore 2 L = ⊥) {P : Subgroup L} (hP : IsPGroup 2 P)
    (hE : ∀ J : Subgroup L, IsComponent J → ⁅J, P⁆ = ⊥) (hF : ⁅fittingSubgroup L, P⁆ = ⊥) :
    P = ⊥ := by
  have hstar : generalizedFitting L ≤ Subgroup.centralizer (P : Set L) :=
    sup_le (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hF)
      (sSup_le fun J hJ => Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hE J hJ))
  have hcent : Subgroup.centralizer (generalizedFitting L : Set L) ≤ fittingSubgroup L := by
    have := ComponentClassification.GeneralizedFitting.centralizer_le_fitting L
    rw [← generalizedFitting_eq_componentClassification] at this
    exact this
  exact eq_bot_of_isPGroup_of_le_fittingSubgroup h2 hP
    ((Subgroup.le_centralizer_iff.mp hstar).trans hcent)

end CFSG.CGT.PushingUpLit.ThmOne
