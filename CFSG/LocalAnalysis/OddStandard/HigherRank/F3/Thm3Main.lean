module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.Thm3Cover
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.Thm3Diag
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.Thm3Pair
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.Thm3Lift

public section

namespace CFSG.OddStandard.HigherRank.F3

open Subgroup CFSG CFSG.Open CFSG.ComponentClassification.HarrisLit
open CFSG.GH74.GLS.TwoThin

theorem not_mem_of_isMTypeSchur (hT1 : Harris82Theorem1KProper) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog G) (hcat : ¬ Blueprint.Catalog G) {w : G}
    (hw2 : orderOf w = 2) {K : Subgroup ↥(centralizer ({w} : Set G))} (hKc : IsTwoComponent K)
    (hM : IsMTypeSchur 3 ↥K) :
    (⟨w, mem_centralizer_singleton_iff.mpr rfl⟩ : ↥(centralizer ({w} : Set G))) ∉ K := by
  intro hwK
  have hJ := T23.isTwoComponentIn_map_subtype hKc
  have hwJ : w ∈ K.map (centralizer ({w} : Set G)).subtype := ⟨_, hwK, rfl⟩
  let e := K.equivMapOfInjective _ (subtype_injective (centralizer ({w} : Set G)))
  exact not_isMTypeSchur_of_kProper hT1 hnonab hK hcat hw2 hJ hwJ Nat.prime_three (by norm_num)
    (T23.isMTypeSchur_of_mulEquiv e hM)

theorem false_of_diag (hT1 : Harris82Theorem1KProper) (hT2 : Theorem2ClassB) {G : Type}
    [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog G) (hcat : ¬ Blueprint.Catalog G) {w t : G}
    (hw2 : orderOf w = 2) (ht2 : orderOf t = 2) (htM : t ∈ centralizer {w})
    {J : Subgroup G} (hJ : IsTwoComponentIn J (centralizer {w} ⊓ centralizer {t}))
    (hM : IsMTypeSchur 3 ↥J) (hS : ClassBShape ↥J) (hP : ¬ PartialCentre ↥J) (hwJ : w ∈ J)
    {K₀ K₁ : Subgroup ↥(centralizer ({w} : Set G))} (hK₀ : IsTwoComponent K₀)
    (hK₁ : K₁ = K₀.map (MulAut.conj (⟨t, htM⟩ : ↥(centralizer ({w} : Set G)))).toMonoidHom)
    (hne : K₁ ≠ K₀)
    (hLeq : J.subgroupOf (centralizer {w}) =
      centralizerResidual (K₀ ⊔ K₁) (⟨t, htM⟩ : ↥(centralizer ({w} : Set G)))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set t' : ↥(centralizer ({w} : Set G)) := ⟨t, htM⟩ with ht'def
  set z : ↥(centralizer ({w} : Set G)) := ⟨w, mem_centralizer_singleton_iff.mpr rfl⟩ with hzdef
  have ht'2 : orderOf t' = 2 := by rw [Subgroup.orderOf_mk]; exact ht2
  have hzz : z * z = 1 := Subtype.ext (by
    change w * w = 1
    rw [← sq, ← hw2, pow_orderOf_eq_one])
  have hzc : z ∈ center ↥(centralizer ({w} : Set G)) :=
    mem_center_iff.mpr fun g => Subtype.ext (mem_centralizer_singleton_iff.mp g.2)
  have hJM : J ≤ centralizer ({w} : Set G) := hJ.1.trans inf_le_left
  set R := centralizerResidual (K₀ ⊔ K₁) t' with hRdef
  let e : ↥J ≃* ↥R := (subgroupOfEquivOfLe hJM).symm.trans (MulEquiv.subgroupCongr hLeq)
  have hMR : IsMTypeSchur 3 ↥R := T23.isMTypeSchur_of_mulEquiv e hM
  have hSR : ClassBShape ↥R := ClassBShape.of_mulEquiv e hS
  have hPR : ¬ PartialCentre ↥R := fun h => hP ((partialCentre_iff_of_mulEquiv e).mpr h)
  obtain ⟨⟨eφ⟩, hMK₀, hSK₀⟩ := cover_of_diag ht'2 hK₀ hK₁ hne rfl hMR hSR hPR
  have hK₁c : IsTwoComponent K₁ := by
    rw [hK₁]
    exact L219.isTwoComponent_map_conj hK₀ t'
  have hMK₁ : IsMTypeSchur 3 ↥K₁ := by
    rw [hK₁]
    exact T23.isMTypeSchur_of_mulEquiv (K₀.equivMapOfInjective _ (MulAut.conj t').injective) hMK₀
  have hzK₀ : z ∉ K₀ := not_mem_of_isMTypeSchur hT1 hnonab hK hcat hw2 hK₀ hMK₀
  have hzK₁ : z ∉ K₁ := not_mem_of_isMTypeSchur hT1 hnonab hK hcat hw2 hK₁c hMK₁
  have hI := inf_map_barMk_eq_bot ht'2 hK₀ hK₁ hne rfl ⟨eφ⟩
  set Y₀ := K₀.map (barMk ↥(centralizer ({w} : Set G))) with hY₀def
  set Y₁ := K₁.map (barMk ↥(centralizer ({w} : Set G))) with hY₁def
  have hY₀c : IsComponent Y₀ :=
    isComponent_map_barMk ((L219.isTwoComponent_iff_twoComponents K₀).mp hK₀)
  have hY₁c : IsComponent Y₁ :=
    isComponent_map_barMk ((L219.isTwoComponent_iff_twoComponents K₁).mp hK₁c)
  have hY₀₁ : Y₀ ≠ Y₁ := by
    intro h
    rw [← h, inf_idem] at hI
    haveI := LocalCores.isQuasisimple_nontrivial hY₀c.1
    exact (Subgroup.nontrivial_iff_ne_bot _).mp this hI
  have hz : z ∈ K₀ ⊔ K₁ := by
    have hzJ : z ∈ J.subgroupOf (centralizer ({w} : Set G)) := hwJ
    rw [hLeq] at hzJ
    exact (centralizerResidual_le.trans inf_le_left) hzJ
  obtain ⟨k, hkk, hk1, hkz, hzk1, hkY₀, hkY₀c, hzkY₁, hzkY₁c⟩ :=
    exists_involution_over hzc hzz hK₀ hK₁c hY₀₁ hI hz hzK₀ hzK₁
  have hk2' : orderOf k = 2 := orderOf_eq_prime (by rw [sq]; exact hkk) hk1
  have hk2 : orderOf (k : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hk2'
  have hzk : (z * k) * (z * k) = 1 := by
    have hc : k * z = z * k := mem_center_iff.mp hzc k
    calc (z * k) * (z * k) = z * (k * z) * k := by group
      _ = z * (z * k) * k := by rw [hc]
      _ = (z * z) * (k * k) := by group
      _ = 1 := by rw [hzz, hkk, one_mul]
  have hzk2 : orderOf ((z * k : ↥(centralizer ({w} : Set G))) : G) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [sq]; exact hzk) hzk1
  obtain ⟨J₁, hJ₁, hkJ₁, ⟨e₁⟩⟩ := exists_lift_component hk2 hY₀c hkY₀ hkY₀c
  obtain ⟨J₂, hJ₂, hzkJ₂, -⟩ := exists_lift_component (k := z * k) hzk2 hY₁c hzkY₁ hzkY₁c
  obtain ⟨e₀⟩ := nonempty_bar_equiv_map_barMk hK₀
  have eJ : ↥J₁ ⧸ pPrimeCore 2 ↥J₁ ≃* ↥K₀ ⧸ pPrimeCore 2 ↥K₀ := e₁.trans e₀.symm
  have hMJ₁ : IsMTypeSchur 3 ↥J₁ := T1.isMTypeSchur_of_bar_equiv hMK₀ hJ₁.2.2 eJ.symm
  have hSJ₁ : ClassBShape ↥J₁ := classBShape_of_bar_equiv eJ.symm hSK₀
  exact false_of_four_group hT2 hnonab hK hcat hw2 hk2 (mem_centralizer_singleton_iff.mp k.2).symm
    (fun h => hkz (Subtype.ext h)) hJ₁ hJ₂ hkJ₁ hzkJ₂ hMJ₁ hSJ₁

theorem theorem3Full_of (hT1 : Harris82Theorem1KProper) (hT2 : Theorem2ClassB) :
    Theorem3Full := by
  intro G _ _ _ hnonab hK hcat W hW2 hW4 J hJ hM hS hP _ w hw hw1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hwJ, hwW⟩ := mem_inf.mp hw
  have hw2 : orderOf w = 2 := orderOf_eq_prime (by rw [sq]; exact hW2 w hwW) hw1
  obtain ⟨t, htW, htw⟩ : ∃ t ∈ W, t ∉ zpowers w := by
    by_contra h
    push Not at h
    have hle := Subgroup.card_le_of_le (show W ≤ zpowers w from fun x hx => h x hx)
    rw [hW4, Nat.card_zpowers, hw2] at hle
    omega
  obtain ⟨-, ht2, htM, hCW⟩ := L35.centralizer_eq_inf hW2 hW4 hwW hw1 htW htw
  have hJ' : IsTwoComponentIn J (centralizer {w} ⊓ centralizer {t}) := hCW ▸ hJ
  obtain ⟨K₀, hK₀, hKeq, hcases⟩ := T23.exists_pumpup ht2 htM hJ'
  rcases hcases with ⟨hfix, -⟩ | ⟨hne, hLeq⟩
  ·
    rw [hKeq, hfix, sup_idem]
    exact T23.isTwoComponentIn_map_subtype hK₀
  · exact (false_of_diag hT1 hT2 hnonab hK hcat hw2 ht2 htM hJ' hM hS hP hwJ hK₀ rfl hne
      hLeq).elim

end CFSG.OddStandard.HigherRank.F3
