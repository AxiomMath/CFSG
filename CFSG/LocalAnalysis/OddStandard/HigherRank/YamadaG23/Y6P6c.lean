module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YCtx
import CFSG.Mathlib.Decide.Bounded
public import CFSG.ClassicalInvolution.Asc77.WP1Section18
public import CFSG.ClassicalInvolution.Asc77.WP1Section6
public import CFSG.ClassicalInvolution.Balance.QNineFuzzyFree
public import CFSG.ClassicalInvolution.Balance.Theorem5Models
public import CFSG.ClassicalInvolution.ModelFacts.Orth15D4Ord
public import CFSG.ClassicalInvolution.ModelFacts.Orth15Std
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Cover
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Q81Step6
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4CoverCore
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitAschbacherCore
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitAschbacherOne
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma49Setup
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma49Tools
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm46
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516CL4
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeModel
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C3Tools2
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1FourGroup
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1RowAlt
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Count
public import CFSG.LocalAnalysis.ComponentClassification.HeldBalStatements
public import CFSG.LocalAnalysis.ComponentClassification.TBLitCoreBasics
public import CFSG.LocalAnalysis.ComponentClassification.TBLitStepFour
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFxDef
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSkel
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.G23Facts
public import CFSG.LocalAnalysis.OddStandard.OddLieHarris82Simple
public import CFSG.Open.GeneralizedFittingSelfCentralizing
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.Sporadic.HeldB.AllFixed
public import Certificates.Certificate7233Base
import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6P6cPack

public section

open scoped Pointwise

namespace CFSG.OddStandard.HigherRank.YamadaG23

private def c1 : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 1 2

private def c2 : Equiv.Perm (Fin 6) := Equiv.swap 3 4 * Equiv.swap 4 5

private def p0List : Finset (Equiv.Perm (Fin 6)) :=
  (Finset.univ : Finset (Fin 3 × Fin 3)).image (fun p => c1 ^ (p.1 : ℕ) * c2 ^ (p.2 : ℕ))

private theorem p0List_mul (i j k l : Fin 3) :
    (c1 ^ (i : ℕ) * c2 ^ (j : ℕ)) * (c1 ^ (k : ℕ) * c2 ^ (l : ℕ)) ∈ p0List := by
  revert i j k l
  decide +kernel

private theorem p0List_inv (i j : Fin 3) :
    (c1 ^ (i : ℕ) * c2 ^ (j : ℕ))⁻¹ ∈ p0List := by
  revert i j
  decide +kernel

private theorem mul_mem_p0List {a b : Equiv.Perm (Fin 6)} (ha : a ∈ p0List) (hb : b ∈ p0List) :
    a * b ∈ p0List := by
  rw [p0List] at ha hb
  obtain ⟨⟨i, j⟩, -, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨⟨k, l⟩, -, rfl⟩ := Finset.mem_image.mp hb
  exact p0List_mul i j k l

private theorem inv_mem_p0List {a : Equiv.Perm (Fin 6)} (ha : a ∈ p0List) : a⁻¹ ∈ p0List := by
  rw [p0List] at ha
  obtain ⟨⟨i, j⟩, -, rfl⟩ := Finset.mem_image.mp ha
  exact p0List_inv i j

private def P0 : Subgroup (Equiv.Perm (Fin 6)) where
  carrier := ↑p0List
  one_mem' := Finset.mem_coe.mp (by decide +kernel)
  mul_mem' := by
    intro a b ha hb
    exact Finset.mem_coe.mp (mul_mem_p0List (Finset.mem_coe.mp ha) (Finset.mem_coe.mp hb))
  inv_mem' := by
    intro a ha
    exact Finset.mem_coe.mp (inv_mem_p0List (Finset.mem_coe.mp ha))

private theorem P0_card : Nat.card ↥P0 = 9 := by
  change Nat.card {x : Equiv.Perm (Fin 6) // x ∈ p0List} = 9
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h1 : CFSG.Permutation.FinPack.enc c1 = 5517345 := by decide +kernel
  have h2 : CFSG.Permutation.FinPack.enc c2 = 3490320 := by decide +kernel
  rw [CFSG.Permutation.FinPack.card_filter_of_iff (· ∈ p0List)
    (fun c => CFSG.Permutation.FinPack.memK c Y6Pack.p0C) (Y6Pack.mem_fam_iff c1 c2 h1 h2)]
  decide +kernel

private instance : DecidablePred (· ∈ blockStab) := fun τ =>
  decidable_of_iff (∀ i j : Fin 6, i.val / 3 = j.val / 3 ↔ (τ i).val / 3 = (τ j).val / 3)
    (by simp [blockStab])

open scoped CFSG.Decide.Bounded in
private theorem p0_conj_or_disjoint (τ : Equiv.Perm (Fin 6)) :
    (∀ x ∈ p0List, τ * x * τ⁻¹ ∈ p0List) ∨
      (∀ x ∈ p0List, x ≠ 1 → τ * x * τ⁻¹ ∉ p0List) := by
  have h1 : CFSG.Permutation.FinPack.enc c1 = 5517345 := by decide +kernel
  have h2 : CFSG.Permutation.FinPack.enc c2 = 3490320 := by decide +kernel
  exact Y6Pack.conj_or_disjoint_of p0List (Y6Pack.mem_fam_iff c1 c2 h1 h2) τ

open scoped CFSG.Decide.Bounded in
private theorem p0_normalizer_le (τ : Equiv.Perm (Fin 6))
    (h : ∀ x ∈ p0List, τ * x * τ⁻¹ ∈ p0List) : τ ∈ blockStab := by
  have h1 : CFSG.Permutation.FinPack.enc c1 = 5517345 := by decide +kernel
  have h2 : CFSG.Permutation.FinPack.enc c2 = 3490320 := by decide +kernel
  exact Y6Pack.normalizer_le_of p0List (Y6Pack.mem_fam_iff c1 c2 h1 h2)
    (Y6Pack.surj_fam c1 c2 h1 h2) τ h

private theorem normalizer_P0_le_blockStab :
    Subgroup.normalizer (P0 : Set (Equiv.Perm (Fin 6))) ≤ blockStab := by
  intro τ hτ
  apply p0_normalizer_le τ
  intro x hx
  have hxP : x ∈ P0 := Finset.mem_coe.mpr hx
  have := (Subgroup.mem_set_normalizer_iff.mp hτ x).mp hxP
  exact Finset.mem_coe.mp this

private theorem conj_sigma_tau (σ d a : Equiv.Perm (Fin 6)) :
    MulAut.conj d (MulAut.conj σ a) = MulAut.conj σ (MulAut.conj (σ⁻¹ * d * σ) a) := by
  simp only [MulAut.conj_apply]
  group

private theorem mulAut_conj_smul_eq_map (σ : Equiv.Perm (Fin 6))
    (H : Subgroup (Equiv.Perm (Fin 6))) :
    MulAut.conj σ • H = H.map (MulAut.conj σ).toMonoidHom := rfl

theorem y6_blockStab_card : Nat.card ↥blockStab = 72 := by
  change Nat.card {σ : Equiv.Perm (Fin 6) //
    ∀ i j : Fin 6, i.val / 3 = j.val / 3 ↔ (σ i).val / 3 = (σ j).val / 3} = 72
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
    CFSG.Permutation.FinPack.card_filter_of_iff
      (fun σ : Equiv.Perm (Fin 6) =>
        ∀ i j : Fin 6, i.val / 3 = j.val / 3 ↔ (σ i).val / 3 = (σ j).val / 3)
      (fun c => Y6Pack.bsP (CFSG.Permutation.FinPack.decK 6 c)) fun σ => by
        rw [CFSG.Permutation.FinPack.decK_enc Y6Pack.h6, Y6Pack.bsP, decide_eq_true_iff]]
  decide +kernel

theorem y6_order72_conj {D : Subgroup (Equiv.Perm (Fin 6))} (hD : Nat.card ↥D = 72) :
    ∃ σ : Equiv.Perm (Fin 6), D = blockStab.map (MulAut.conj σ).toMonoidHom := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hGcard : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
    rw [Nat.card_perm]; simp [Nat.factorial]
  have hP0grp : IsPGroup 3 P0 := IsPGroup.of_card (n := 2) (by rw [P0_card]; norm_num)
  have hP0index : ¬ 3 ∣ P0.index := by
    have h := P0.index_mul_card
    rw [P0_card, hGcard] at h
    have : P0.index = 80 := by omega
    rw [this]; norm_num
  let P0syl : Sylow 3 (Equiv.Perm (Fin 6)) := hP0grp.toSylow hP0index
  obtain ⟨Pd, hPdcard⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥D) 3 (n := 2)
    (by rw [hD]; norm_num)
  let P' : Subgroup (Equiv.Perm (Fin 6)) := Pd.map D.subtype
  have hP'card : Nat.card ↥P' = 9 := by
    rw [Subgroup.card_map_of_injective D.subtype_injective, hPdcard]; norm_num
  have hP'grp : IsPGroup 3 P' := IsPGroup.of_card (n := 2) (by rw [hP'card]; norm_num)
  have hP'index : ¬ 3 ∣ P'.index := by
    have h := P'.index_mul_card
    rw [hP'card, hGcard] at h
    have : P'.index = 80 := by omega
    rw [this]; norm_num
  let P'syl : Sylow 3 (Equiv.Perm (Fin 6)) := hP'grp.toSylow hP'index
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (Equiv.Perm (Fin 6)) P0syl P'syl
  have hP'eq : P' = P0.map (MulAut.conj σ).toMonoidHom := by
    have h := congrArg (fun S : Sylow 3 (Equiv.Perm (Fin 6)) =>
      (S : Subgroup (Equiv.Perm (Fin 6)))) hσ
    simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe, P0syl, P'syl,
      mulAut_conj_smul_eq_map] at h
    exact h.symm
  have hP'le : P' ≤ D := Subgroup.map_subtype_le Pd
  have hN'le : Subgroup.normalizer (P' : Set (Equiv.Perm (Fin 6))) ≤
      blockStab.map (MulAut.conj σ).toMonoidHom := by
    rw [hP'eq]
    calc Subgroup.normalizer (P0.map (MulAut.conj σ).toMonoidHom)
        = (Subgroup.normalizer (P0 : Set (Equiv.Perm (Fin 6)))).map
            (MulAut.conj σ).toMonoidHom :=
          (Subgroup.map_normalizer_eq_of_bijective (H := P0)
            (f := (MulAut.conj σ).toMonoidHom) (MulEquiv.bijective (MulAut.conj σ))).symm
      _ ≤ blockStab.map (MulAut.conj σ).toMonoidHom :=
          Subgroup.map_mono normalizer_P0_le_blockStab
  have hDleN' : D ≤ Subgroup.normalizer (P' : Set (Equiv.Perm (Fin 6))) := by
    intro d hd
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    by_contra hne
    have hQcard : Nat.card ↥(P'.map (MulAut.conj d).toMonoidHom) = 9 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj d).injective, hP'card]
    have hQleD : P'.map (MulAut.conj d).toMonoidHom ≤ D := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      exact D.mul_mem (D.mul_mem hd (hP'le hx)) (D.inv_mem hd)
    have hdisj : Disjoint P' (P'.map (MulAut.conj d).toMonoidHom) := by
      rw [Subgroup.disjoint_def]
      intro y hy hyQ
      by_contra hy1
      rcases p0_conj_or_disjoint (σ⁻¹ * d * σ) with h1 | h2
      · have hQleP' : P'.map (MulAut.conj d).toMonoidHom ≤ P' := by
          intro z hz
          obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz
          rw [hP'eq] at hx
          obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
          change MulAut.conj d (MulAut.conj σ a) ∈ P'
          rw [conj_sigma_tau, hP'eq]
          exact Subgroup.mem_map.mpr
            ⟨MulAut.conj (σ⁻¹ * d * σ) a,
              Finset.mem_coe.mpr (h1 a (Finset.mem_coe.mp ha)), rfl⟩
        exact absurd (Subgroup.eq_of_le_of_card_ge hQleP'
          (by rw [hQcard, hP'card])) hne
      · rw [hP'eq] at hy
        obtain ⟨a, ha, hay⟩ := Subgroup.mem_map.mp hy
        obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hyQ
        rw [hP'eq] at hz
        obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hz
        simp only [MulEquiv.coe_toMonoidHom] at hay hzy
        have hb1 : b ≠ 1 := by
          intro hb0
          apply hy1
          rw [← hzy, hb0]; simp
        have hthis : MulAut.conj σ a = MulAut.conj σ (MulAut.conj (σ⁻¹ * d * σ) b) := by
          rw [hay, ← hzy, conj_sigma_tau]
        have haeq : a = MulAut.conj (σ⁻¹ * d * σ) b := (MulAut.conj σ).injective hthis
        have haeq' : (σ⁻¹ * d * σ) * b * (σ⁻¹ * d * σ)⁻¹ = a := by
          rw [haeq, MulAut.conj_apply]
        exact h2 b (Finset.mem_coe.mp hb) hb1 (by rw [haeq']; exact Finset.mem_coe.mp ha)
    have hinj : Function.Injective (fun p : ↥P' × ↥(P'.map (MulAut.conj d).toMonoidHom) =>
        (⟨(p.1 : Equiv.Perm (Fin 6)) * (p.2 : Equiv.Perm (Fin 6)),
          D.mul_mem (hP'le p.1.2) (hQleD p.2.2)⟩ : ↥D)) := by
      intro p q hpq
      have hpq' : (p.1 : Equiv.Perm (Fin 6)) * p.2 = (q.1 : _) * q.2 := Subtype.ext_iff.mp hpq
      exact Subgroup.mul_injective_of_disjoint hdisj hpq'
    have h81 : 81 ≤ Nat.card ↥D := by
      have h := Nat.card_le_card_of_injective _ hinj
      rw [Nat.card_prod, hP'card, hQcard] at h
      simpa using h
    omega
  refine ⟨σ, ?_⟩
  refine Subgroup.eq_of_le_of_card_ge (hDleN'.trans hN'le) ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj σ).injective, y6_blockStab_card, hD]

end CFSG.OddStandard.HigherRank.YamadaG23
