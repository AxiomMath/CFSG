module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieL1
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCU

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.EndOddLin

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.U
open CFSG.ComponentClassification.Burgoyne.C (uBlockProjEquiv subsingleton_statedSU_of_le_one
  statedSUCongr uBlock_mono isSolvable_SL_two_of_card_three commutator_le_uBlock_sup
  isSubnormal_map_mk le_map_commutator_of_perfect_mk)
open CFSG.ComponentClassification.Burgoyne.PSL (signMat compInd)
open CFSG.ComponentClassification.CatLeafProof.EndOddCore
open scoped MatrixGroups commutatorElement

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ}

theorem two_ne_zero_of_unitary (hu : UnitaryFieldData p f K) (hp2 : p ≠ 2) : (2 : K) ≠ 0 := by
  have : Fact p.Prime := ⟨hu.prime⟩
  have := hu.charP
  intro e
  have e' : ((2 : ℕ) : K) = 0 := by exact_mod_cast e
  rw [CharP.cast_eq_zero_iff K p] at e'
  have := Nat.le_of_dvd (by norm_num) e'
  have := hu.prime.two_le
  exact hp2 (by omega)

variable [Finite K]

theorem quatBlock_uBlock (hu : UnitaryFieldData p f K) (hp2 : p ≠ 2) {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = p ^ f) (e₂ : StatedSU 2 (p ^ f) K ≃* SL(2, F))
    {I : Finset (Fin n)} {k : Fin n} (hk : k ∉ I) :
    QuatBlock ((uBlock p f K I).map (projH (StatedSU n (p ^ f) K))) := by
  have : Fact p.Prime := ⟨hu.prime⟩
  have hFc : ringChar F ≠ 2 := by
    have : Fintype F := Fintype.ofFinite F
    have : CharP F p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
    rw [ringChar.eq F p]
    exact hp2
  set e := uBlockProjEquiv (K := K) (p := p) (f := f) hk with he
  have hq3 : 3 ≤ p ^ f := by
    have hodd : Odd (p ^ f) := (hu.prime.odd_of_ne_two hp2).pow
    have : 2 ≤ p ^ f := le_trans hu.prime.two_le (Nat.le_self_pow (by have := hu.one_le; omega) p)
    obtain ⟨j, hj⟩ := hodd
    omega
  have eI : ∀ {m : ℕ} (hm : I.card = m), (uBlock p f K I).map (projH (StatedSU n (p ^ f) K)) ≃*
      StatedSU m (p ^ f) K := fun hm =>
    (e.symm.trans (uBlockEquiv hu I).symm).trans (statedSUCongr hm)
  by_cases h1 : I.card ≤ 1
  · have := subsingleton_statedSU_of_le_one hu (K := K) h1
    have : Subsingleton ((uBlock p f K I).map (projH (StatedSU n (p ^ f) K))) :=
      (eI rfl).injective.subsingleton
    exact quatBlock_of_isSolvable inferInstance
  by_cases h23 : I.card = 2 ∧ p ^ f = 3
  · have hs : Group.IsSolvable SL(2, F) := isSolvable_SL_two_of_card_three (by rw [hF, h23.2])
    have e3 := (eI h23.1).trans e₂
    exact quatBlock_of_isSolvable
      (Group.isSolvable_of_isSolvable_injective (f := e3.toMonoidHom) e3.injective)
  have hI2 : 2 ≤ I.card := by omega
  have hq : 3 ≤ I.card ∨ 5 ≤ p ^ f := by
    by_contra hcon
    push Not at hcon
    have hodd : Odd (p ^ f) := (hu.prime.odd_of_ne_two hp2).pow
    obtain ⟨j, hj⟩ := hodd
    exact h23 ⟨by omega, by omega⟩
  have hqs : IsQuasisimple ((uBlock p f K I).map (projH (StatedSU n (p ^ f) K))) :=
    LocalCores.isQuasisimple_of_mulEquiv e (isQuasisimple_uBlock hu hp2 hI2 hq)
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < I.card)
  have hsub : ({a, b} : Finset (Fin n)) ⊆ I := by
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact ha
    · rw [Finset.mem_singleton.1 hy]
      exact hb
  let φ : SL(2, F) →* (uBlock p f K I).map (projH (StatedSU n (p ^ f) K)) :=
    e.toMonoidHom.comp ((Subgroup.inclusion (uBlock_mono (p := p) (f := f) (K := K) hsub)).comp
      ((uBlockEquiv hu ({a, b} : Finset (Fin n))).toMonoidHom.comp
        (((statedSUCongr (Finset.card_pair hab)).trans e₂).symm.toMonoidHom)))
  have hφ : Function.Injective φ :=
    e.injective.comp ((Subgroup.inclusion_injective
      (uBlock_mono (p := p) (f := f) (K := K) hsub)).comp
      ((uBlockEquiv hu _).injective.comp ((statedSUCongr _).trans e₂).symm.injective))
  obtain ⟨H, ⟨eH⟩⟩ := exists_quaternion_of_injective_SL hFc φ hφ
  exact quatBlock_of_quat hqs H eH

theorem false_of_config_psu_split (hu : UnitaryFieldData p f K) (hp2 : p ≠ 2) {F : Type}
    [Field F] [Finite F] (hF : Nat.card F = p ^ f) (e₂ : StatedSU 2 (p ^ f) K ≃* SL(2, F))
    {J : Finset (Fin n)} {a b : Fin n} (ha : a ∈ J) (hb : b ∉ J) {l : K} (hl : l ≠ 0)
    {A : StatedSU n (p ^ f) K}
    (hA : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = l • signMat K J)
    {L D : Subgroup (StatedProj (StatedSU n (p ^ f) K))} (h : Config (projH _ A) L D) : False := by
  have h2 := two_ne_zero_of_unitary hu hp2
  have hcent : ∀ g : StatedSU n (p ^ f) K, g ∈ centralizer ({A} : Set _) ↔
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * compInd K J =
        compInd K J * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    intro g
    rw [mem_centralizer_singleton_iff]
    constructor
    · intro hg
      have h' := congrArg (fun u : StatedSU n (p ^ f) K =>
        ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) hg
      simp only [Subgroup.coe_mul, Units.val_mul] at h'
      rw [hA, Matrix.mul_smul, Matrix.smul_mul] at h'
      exact ((Burgoyne.PSL.commute_signMat_iff h2 J _).1 (smul_right_injective _ hl h').symm).symm
    · intro hg
      apply Subtype.ext
      apply Units.ext
      change ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      rw [hA, Matrix.mul_smul, Matrix.smul_mul,
        ((Burgoyne.PSL.commute_signMat_iff h2 J _).2 hg.symm).symm]
  have hZ := scalars_subgroupOf_le_center (H := StatedSU n (p ^ f) K)
  have hsub : ∀ {I : Finset (Fin n)}, (I = J ∨ I = Jᶜ) →
      (uBlock p f K I).map (QuotientGroup.mk' _) ≤
          centralizer ({QuotientGroup.mk' _ A} : Set (StatedProj (StatedSU n (p ^ f) K))) ∧
        (((uBlock p f K I).map (QuotientGroup.mk' _)).subgroupOf
          (centralizer ({QuotientGroup.mk' _ A} :
            Set (StatedProj (StatedSU n (p ^ f) K))))).IsSubnormal := by
    intro I hI
    refine isSubnormal_map_mk hZ A (fun g hg => (hcent g).2 ?_) ?_
    · exact commute_compInd_of_or' hI (commute_compInd_of_mem_uBlock hg) |>.symm
    · intro B hB g hg
      have hBc := (hcent B).1 hB
      have hBI : compInd K I * ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * compInd K I :=
        commute_compInd_of_or hI hBc.symm
      refine conj_mem_uBlock (D := ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
        (Di := (((B⁻¹ : StatedSU n (p ^ f) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
        ?_ ?_ hBI hg rfl
      · rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one]
      · rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one]
  have hperf : ∀ L' : Subgroup (StatedProj (StatedSU n (p ^ f) K)),
      L' ≤ centralizer ({QuotientGroup.mk' _ A} : Set _) → ⁅L', L'⁆ = L' →
      L' ≤ (uBlock p f K J).map (QuotientGroup.mk' _) ⊔
        (uBlock p f K Jᶜ).map (QuotientGroup.mk' _) := by
    intro L' hL hp
    refine (le_map_commutator_of_perfect_mk hZ A hL hp).trans ?_
    rw [← Subgroup.map_sup]
    exact map_mono (commutator_le_uBlock_sup hu J fun g hg => (hcent g).1 hg)
  have haJ : a ∉ Jᶜ := by simpa using ha
  exact false_of_config_blocks h (hsub (Or.inl rfl)).1 (hsub (Or.inr rfl)).1
    (hsub (Or.inl rfl)).2 (hsub (Or.inr rfl)).2 hperf (quatBlock_uBlock hu hp2 hF e₂ hb)
    (quatBlock_uBlock hu hp2 hF e₂ haJ)

end CFSG.ComponentClassification.CatLeafProof.EndOddLin
