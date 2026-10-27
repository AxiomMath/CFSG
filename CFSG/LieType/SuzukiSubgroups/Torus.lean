module

public import CFSG.LieType.SuzukiSubgroups.Main
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf14BenderSz
import CFSG.GroupTheory.CyclicSylowNormalOddComplement
import CFSG.Holt.StarCase.Lemma27Basic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsSzPointAction
import CFSG.LocalAnalysis.WeakClosure81.SzStructureFacts
import CFSG.Permutation.UnitaryThreeRecognition.Orbits
import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini

public section

namespace CFSG.LieType.SuzukiSubgroups

open CFSG.Open Subgroup

section FourGroup

open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {n : ℕ} {H : Type} [Group H] [Finite H]

private theorem four_eq_or_eq_of_three_fixed {α : Type} [Finite α] {p : α → Prop}
    (h2 : Nat.card {x : α // p x} ≤ 2) {a b c : α} (ha : p a) (hb : p b) (hc : p c)
    (hbc : b ≠ c) : a = b ∨ a = c := by
  classical
  by_contra h
  push_neg at h
  have hlt : 2 < Nat.card {x : α // p x} := by
    haveI : Finite {x : α // p x} := Subtype.finite
    haveI : Fintype {x : α // p x} := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Fintype.two_lt_card_iff]
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩,
      fun he => h.1 (congrArg Subtype.val he),
      fun he => h.2 (congrArg Subtype.val he),
      fun he => hbc (congrArg Subtype.val he)⟩
  omega

private theorem four_normalizer_case (hH : CFSG.Quasithin.IsSz n H)
    (T : CFSG.GroupTheory.SuzukiTorusData H (2 ^ n))
    {Q₁ Q₂ Q : Sylow 2 H} (hne : Q₁ ≠ Q₂) {Y : Subgroup H}
    (hK : normalizer ((Q₁ : Subgroup H) : Set H) ⊓
      normalizer ((Q₂ : Subgroup H) : Set H) ≤ Y)
    (hYQ : Y ≤ normalizer ((Q : Subgroup H) : Set H)) {y : H} (hy : y ∈ Y)
    (hyQ : y • Q₁ = Q₂) : False := by
  let K : Subgroup H := CFSG.GroupTheory.SuzukiTorusData.torus Q₁ Q₂
  have hKle : K ≤ Y := hK
  have hKcard : Nat.card K = 2 ^ n - 1 := T.torus_card hne
  have hn3 : 3 ≤ n := (odd_and_three_le_of_isSz hH).2
  have h1lt : 1 < Nat.card K := by
    rw [hKcard]
    have h := Nat.pow_le_pow_of_le (a := 2) (by norm_num) hn3
    omega
  haveI : Nontrivial K := Finite.one_lt_card_iff_nontrivial.mp h1lt
  obtain ⟨k, hk1⟩ := exists_ne (1 : K)
  have hkK : (k : H) ∈ CFSG.GroupTheory.SuzukiTorusData.torus Q₁ Q₂ := k.2
  have hkQ : (k : H) • Q = Q :=
    Sylow.smul_eq_iff_mem_normalizer.mpr (hYQ (hKle k.2))
  have hkQ₁ : (k : H) • Q₁ = Q₁ :=
    Sylow.smul_eq_iff_mem_normalizer.mpr
      (CFSG.GroupTheory.SuzukiTorusData.torus_le_normalizer_left (U₂ := Q₂) hkK)
  have hkQ₂ : (k : H) • Q₂ = Q₂ :=
    Sylow.smul_eq_iff_mem_normalizer.mpr
      (CFSG.GroupTheory.SuzukiTorusData.torus_le_normalizer_right (U₁ := Q₁) hkK)
  have hk1' : (k : H) ≠ 1 := fun h => hk1 (Subtype.ext (by simpa using h))
  have hle2 : Nat.card {P : Sylow 2 H // (k : H) • P = P} ≤ 2 :=
    T.fixes_le_two (k : H) hk1'
  have hyQfix : y • Q = Q :=
    Sylow.smul_eq_iff_mem_normalizer.mpr (hYQ hy)
  rcases four_eq_or_eq_of_three_fixed hle2 hkQ hkQ₁ hkQ₂ hne with hQ₁ | hQ₂
  · refine hne ?_
    calc Q₁ = Q := hQ₁.symm
      _ = y • Q := hyQfix.symm
      _ = y • Q₁ := by rw [hQ₁]
      _ = Q₂ := hyQ
  · refine hne ?_
    have h : y • Q₁ = y • Q₂ := by
      rw [hyQ, ← hQ₂]
      exact hyQfix.symm
    exact smul_left_cancel y h

private theorem four_isSz_case (hH : CFSG.Quasithin.IsSz n H)
    (T : CFSG.GroupTheory.SuzukiTorusData H (2 ^ n))
    {Q₁ Q₂ : Sylow 2 H} (hne : Q₁ ≠ Q₂) {Y : Subgroup H}
    (hK : normalizer ((Q₁ : Subgroup H) : Set H) ⊓
      normalizer ((Q₂ : Subgroup H) : Set H) ≤ Y)
    {k : ℕ} (hk : k ∣ n) (hkn : k < n) (hSz : CFSG.Quasithin.IsSz k Y) : False := by
  let K : Subgroup H := CFSG.GroupTheory.SuzukiTorusData.torus Q₁ Q₂
  have hKcyc : IsCyclic K := T.torus_isCyclic hne
  have hKcard : Nat.card K = 2 ^ n - 1 := T.torus_card hne
  obtain ⟨g, hg⟩ := hKcyc.exists_ofOrder_eq_natCard
  have hgord : orderOf g = 2 ^ n - 1 := by rw [hg, hKcard]
  let gY : Y := ⟨(g : H), hK g.2⟩
  have hgYord : orderOf gY = orderOf g :=
    (Subgroup.orderOf_coe gY).symm.trans (Subgroup.orderOf_coe g)
  exact orderOf_ne_two_pow_sub_one_of_isSz hSz (odd_and_three_le_of_isSz hH).1 hk hkn gY
    (hgYord.trans hgord)

theorem eq_top_of_elemAbelian_four_le
    (hH : CFSG.Quasithin.IsSz n H) {Q₁ Q₂ : Sylow 2 H} (hne : Q₁ ≠ Q₂) {Y : Subgroup H}
    (hK : normalizer ((Q₁ : Subgroup H) : Set H) ⊓ normalizer ((Q₂ : Subgroup H) : Set H) ≤ Y)
    {y : H} (hy : y ∈ Y) (hyQ : y • Q₁ = Q₂) {E : Subgroup H} (hEY : E ≤ Y)
    (hE : IsElemAbelian 2 E) (hE4 : Nat.card E = 4) : Y = ⊤ := by
  by_contra hY
  have hT : CFSG.GroupTheory.SuzukiTorusData H (2 ^ n) :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.szPointActionFacts_holds H n
      (CFSG.GH74.Filter.lieModel_of_suzuki hH)
  rcases le_normalizer_or_isSz hH hY hEY hE hE4 with ⟨Q, hYQ⟩ | ⟨k, hk, hkn, hSz⟩
  · exact four_normalizer_case hH hT hne hK hYQ hy hyQ
  · exact four_isSz_case hH hT hne hK hk hkn hSz

end FourGroup

private theorem oddTorus_two_pow_ge_eight {X : Type} [Group X] {n : ℕ}
    (hH : CFSG.Quasithin.IsSz n X) : 8 ≤ 2 ^ n := by
  obtain ⟨-, a, ha, _, _, _, rfl, _, _⟩ := hH
  have h3 : 3 ≤ 2 * a + 1 := by omega
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) h3

private theorem oddTorus_even_two_pow {X : Type} [Group X] {n : ℕ}
    (hH : CFSG.Quasithin.IsSz n X) : Even (2 ^ n) := by
  obtain ⟨-, a, ha, _, _, _, rfl, _, _⟩ := hH
  exact Even.pow_of_ne_zero (by norm_num : Even 2) (by omega : 2 * a + 1 ≠ 0)

private theorem oddTorus_three_fixed {X : Type} [Group X] [Finite X] {q : ℕ}
    (T : CFSG.GroupTheory.SuzukiTorusData X q) {k : X} (hk : k ≠ 1)
    {P Q R : Sylow 2 X} (hP : k • P = P) (hQ : k • Q = Q) (hR : k • R = R)
    (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R) : False := by
  haveI : Finite (Sylow 2 X) := CFSG.GroupTheory.SuzukiTorusData.sylow_finite
  have hle := T.fixes_le_two k hk
  have h3 : 3 ≤ Nat.card {S : Sylow 2 X // k • S = S} := by
    let f : Fin 3 → {S : Sylow 2 X // k • S = S} :=
      ![⟨P, hP⟩, ⟨Q, hQ⟩, ⟨R, hR⟩]
    have hf : Function.Injective f := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [f]
    simpa using Nat.card_le_card_of_injective f hf
  omega

private theorem oddTorus_stabilizer_map_eq_inf {X : Type} [Group X] (W : Subgroup X)
    (P : Sylow 2 X) :
    (MulAction.stabilizer W P).map W.subtype =
      W ⊓ Subgroup.normalizer ((P : Subgroup X) : Set X) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : y • P = P := MulAction.mem_stabilizer_iff.mp hy
    exact ⟨y.2, Sylow.smul_eq_iff_mem_normalizer.mp (by simpa [Subgroup.smul_def] using hy')⟩
  · rintro ⟨hxW, hxN⟩
    refine ⟨⟨x, hxW⟩, ?_, rfl⟩
    change (⟨x, hxW⟩ : W) ∈ MulAction.stabilizer W P
    rw [MulAction.mem_stabilizer_iff]
    simpa [Subgroup.smul_def] using Sylow.smul_eq_iff_mem_normalizer.mpr hxN

private theorem oddTorus_stabilizer_card_eq_inf {X : Type} [Group X] (W : Subgroup X)
    (P : Sylow 2 X) :
    Nat.card (MulAction.stabilizer W P) =
      Nat.card ↥(W ⊓ Subgroup.normalizer ((P : Subgroup X) : Set X)) := by
  have h := Subgroup.card_map_of_injective (K := MulAction.stabilizer W P) W.subtype_injective
  rw [oddTorus_stabilizer_map_eq_inf] at h
  exact h.symm

private theorem oddTorus_stabilizer_dvd {X : Type} [Group X]
    [Finite X] {n : ℕ} (hH : CFSG.Quasithin.IsSz n X) {W : Subgroup X}
    (hW : Odd (Nat.card W)) (P : Sylow 2 X) :
    Nat.card ↥(W ⊓ Subgroup.normalizer ((P : Subgroup X) : Set X)) ∣ 2 ^ n - 1 := by
  have hdW : Nat.card ↥(W ⊓ Subgroup.normalizer ((P : Subgroup X) : Set X)) ∣ Nat.card W :=
    Subgroup.card_dvd_of_le inf_le_left
  have hdN : Nat.card ↥(W ⊓ Subgroup.normalizer ((P : Subgroup X) : Set X)) ∣
      Nat.card (Subgroup.normalizer ((P : Subgroup X) : Set X)) :=
    Subgroup.card_dvd_of_le inf_le_right
  have hN : Nat.card (Subgroup.normalizer ((P : Subgroup X) : Set X)) =
      (2 ^ n) ^ 2 * (2 ^ n - 1) := card_normalizer_sylow_of_isSz hH P
  rw [hN] at hdN
  have hodd : Odd (Nat.card ↥(W ⊓ Subgroup.normalizer ((P : Subgroup X) : Set X))) :=
    hW.of_dvd_nat hdW
  have hcop2 : Nat.Coprime
      (Nat.card ↥(W ⊓ Subgroup.normalizer ((P : Subgroup X) : Set X))) 2 :=
    hodd.coprime_two_left.symm
  have hcop : Nat.Coprime
      (Nat.card ↥(W ⊓ Subgroup.normalizer ((P : Subgroup X) : Set X))) ((2 ^ n) ^ 2) := by
    have hpow2 : (2 ^ n) ^ 2 = 2 ^ (2 * n) := by
      conv_lhs => rw [← pow_mul]
      congr 1
      omega
    rw [hpow2]
    exact Nat.Coprime.pow_right _ hcop2
  exact hcop.dvd_of_dvd_mul_left hdN

private theorem oddTorus_stabilizer_eq_torus {X : Type}
    [Group X] [Finite X] {n : ℕ} (hH : CFSG.Quasithin.IsSz n X)
    (T : CFSG.GroupTheory.SuzukiTorusData X (2 ^ n))
    {Q₁ Q₂ : Sylow 2 X} (hne : Q₁ ≠ Q₂) {W : Subgroup X}
    (hKW : CFSG.GroupTheory.SuzukiTorusData.torus Q₁ Q₂ ≤ W) (hW : Odd (Nat.card W)) :
    W ⊓ Subgroup.normalizer ((Q₁ : Subgroup X) : Set X) =
        CFSG.GroupTheory.SuzukiTorusData.torus Q₁ Q₂ ∧
      W ⊓ Subgroup.normalizer ((Q₂ : Subgroup X) : Set X) =
        CFSG.GroupTheory.SuzukiTorusData.torus Q₁ Q₂ := by
  have hKcard : Nat.card ↥(CFSG.GroupTheory.SuzukiTorusData.torus Q₁ Q₂) = 2 ^ n - 1 :=
    T.torus_card hne
  constructor
  · have hle : CFSG.GroupTheory.SuzukiTorusData.torus Q₁ Q₂ ≤
        W ⊓ Subgroup.normalizer ((Q₁ : Subgroup X) : Set X) :=
      le_inf hKW CFSG.GroupTheory.SuzukiTorusData.torus_le_normalizer_left
    have hdvd : Nat.card ↥(W ⊓ Subgroup.normalizer ((Q₁ : Subgroup X) : Set X)) ∣
        2 ^ n - 1 := oddTorus_stabilizer_dvd hH hW Q₁
    have hdvdK : Nat.card ↥(CFSG.GroupTheory.SuzukiTorusData.torus Q₁ Q₂) ∣
        Nat.card ↥(W ⊓ Subgroup.normalizer ((Q₁ : Subgroup X) : Set X)) :=
      Subgroup.card_dvd_of_le hle
    have hcard : Nat.card ↥(W ⊓ Subgroup.normalizer ((Q₁ : Subgroup X) : Set X)) =
        Nat.card ↥(CFSG.GroupTheory.SuzukiTorusData.torus Q₁ Q₂) := by
      rw [hKcard]
      exact Nat.dvd_antisymm hdvd (by rwa [hKcard] at hdvdK)
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard])).symm
  · have hle : CFSG.GroupTheory.SuzukiTorusData.torus Q₁ Q₂ ≤
        W ⊓ Subgroup.normalizer ((Q₂ : Subgroup X) : Set X) :=
      le_inf hKW CFSG.GroupTheory.SuzukiTorusData.torus_le_normalizer_right
    have hdvd : Nat.card ↥(W ⊓ Subgroup.normalizer ((Q₂ : Subgroup X) : Set X)) ∣
        2 ^ n - 1 := oddTorus_stabilizer_dvd hH hW Q₂
    have hdvdK : Nat.card ↥(CFSG.GroupTheory.SuzukiTorusData.torus Q₁ Q₂) ∣
        Nat.card ↥(W ⊓ Subgroup.normalizer ((Q₂ : Subgroup X) : Set X)) :=
      Subgroup.card_dvd_of_le hle
    have hcard : Nat.card ↥(W ⊓ Subgroup.normalizer ((Q₂ : Subgroup X) : Set X)) =
        Nat.card ↥(CFSG.GroupTheory.SuzukiTorusData.torus Q₁ Q₂) := by
      rw [hKcard]
      exact Nat.dvd_antisymm hdvd (by rwa [hKcard] at hdvdK)
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard])).symm

private theorem oddTorus_no_smul {X : Type} [Group X]
    [Finite X] {n : ℕ} (hH : CFSG.Quasithin.IsSz n X)
    (T : CFSG.GroupTheory.SuzukiTorusData X (2 ^ n))
    {Q₁ Q₂ : Sylow 2 X} (hne : Q₁ ≠ Q₂) {W : Subgroup X}
    (hKW : CFSG.GroupTheory.SuzukiTorusData.torus Q₁ Q₂ ≤ W) (hW : Odd (Nat.card W))
    {h : X} (hhW : h ∈ W) (hsmul : h • Q₁ = Q₂) : False := by
  obtain ⟨hWQ1, -⟩ := oddTorus_stabilizer_eq_torus hH T hne hKW hW
  have hQ1fix : ∀ k ∈ CFSG.GroupTheory.SuzukiTorusData.torus Q₁ Q₂, k • Q₁ = Q₁ :=
    fun k hk =>
      Sylow.smul_eq_iff_mem_normalizer.mpr
        (CFSG.GroupTheory.SuzukiTorusData.torus_le_normalizer_left hk)
  have hQ2fix : ∀ k ∈ CFSG.GroupTheory.SuzukiTorusData.torus Q₁ Q₂, k • Q₂ = Q₂ :=
    fun k hk =>
      Sylow.smul_eq_iff_mem_normalizer.mpr
        (CFSG.GroupTheory.SuzukiTorusData.torus_le_normalizer_right hk)
  have hsmul_inv : h⁻¹ • Q₂ = Q₁ := by
    have h := congrArg (fun P : Sylow 2 X => h⁻¹ • P) hsmul
    simpa [smul_smul] using h.symm
  have hKcard : Nat.card ↥(CFSG.GroupTheory.SuzukiTorusData.torus Q₁ Q₂) = 2 ^ n - 1 :=
    CFSG.GroupTheory.SuzukiTorusData.torus_card T hne
  have hpow8 : 8 ≤ 2 ^ n := oddTorus_two_pow_ge_eight hH
  have hKgt : 1 < Nat.card ↥(CFSG.GroupTheory.SuzukiTorusData.torus Q₁ Q₂) := by
    rw [hKcard]; omega
  haveI : Nontrivial ↥(CFSG.GroupTheory.SuzukiTorusData.torus Q₁ Q₂) :=
    Finite.one_lt_card_iff_nontrivial.mp hKgt
  obtain ⟨k, hkne⟩ := exists_ne (1 : ↥(CFSG.GroupTheory.SuzukiTorusData.torus Q₁ Q₂))
  have hkH : (k : X) ≠ 1 := fun h1 => hkne (Subtype.ext h1)
  have hconj_mem : h⁻¹ * (k : X) * h ∈
      CFSG.GroupTheory.SuzukiTorusData.torus Q₁ Q₂ := by
    have hmemW : h⁻¹ * (k : X) * h ∈ W :=
      mul_mem (mul_mem (inv_mem hhW) (hKW k.2)) hhW
    have hmemN : h⁻¹ * (k : X) * h ∈
        Subgroup.normalizer ((Q₁ : Subgroup X) : Set X) := by
      refine Sylow.smul_eq_iff_mem_normalizer.mp ?_
      calc (h⁻¹ * (k : X) * h) • Q₁
          = (h⁻¹ * (k : X) * h) • (h⁻¹ • Q₂) := by rw [hsmul_inv]
        _ = ((h⁻¹ * (k : X) * h) * h⁻¹) • Q₂ :=
              (mul_smul (h⁻¹ * (k : X) * h) h⁻¹ Q₂).symm
        _ = (h⁻¹ * (k : X)) • Q₂ := by
              rw [show (h⁻¹ * (k : X) * h) * h⁻¹ = h⁻¹ * (k : X) by group]
        _ = h⁻¹ • ((k : X) • Q₂) := by rw [mul_smul]
        _ = h⁻¹ • Q₂ := by rw [hQ2fix (k : X) k.2]
        _ = Q₁ := hsmul_inv
    have hmem : h⁻¹ * (k : X) * h ∈
        W ⊓ Subgroup.normalizer ((Q₁ : Subgroup X) : Set X) := ⟨hmemW, hmemN⟩
    rwa [hWQ1] at hmem
  have hfixh : (k : X) • (h • Q₂) = h • Q₂ := by
    calc (k : X) • (h • Q₂)
        = ((k : X) * h) • Q₂ := by rw [mul_smul]
      _ = (h * (h⁻¹ * (k : X) * h)) • Q₂ := by
            rw [show (k : X) * h = h * (h⁻¹ * (k : X) * h) by group]
      _ = h • ((h⁻¹ * (k : X) * h) • Q₂) := by rw [mul_smul]
      _ = h • Q₂ := by rw [hQ2fix _ hconj_mem]
  have hQ₂ne : h • Q₂ ≠ Q₂ := by
    intro hfix
    exact hne (smul_left_cancel h (hsmul.trans hfix.symm))
  have hmem : h • Q₂ = Q₁ := by
    by_contra hne1
    exact oddTorus_three_fixed T hkH (hQ1fix (k : X) k.2) (hQ2fix (k : X) k.2) hfixh
      hne (Ne.symm hne1) hQ₂ne.symm
  have hodd : Odd (orderOf h) := hW.of_dvd_nat (Subgroup.orderOf_dvd_natCard W hhW)
  have hfix₁ : h • Q₁ = Q₁ :=
    CFSG.Holt.StarLemma27.smul_eq_of_odd_orderOf hodd hne (Or.inr hsmul) (Or.inl hmem)
  exact hne (hfix₁.symm.trans hsmul)

private theorem oddTorus_dvd_orbit_sub_one {X : Type} [Group X] [Finite X] {n : ℕ}
    (T : CFSG.GroupTheory.SuzukiTorusData X (2 ^ n))
    {Q₁ Q₂ : Sylow 2 X} (hne : Q₁ ≠ Q₂) {W : Subgroup X}
    (hKW : CFSG.GroupTheory.SuzukiTorusData.torus Q₁ Q₂ ≤ W)
    (hQ₂ : Q₂ ∉ MulAction.orbit W Q₁) :
    Nat.card ↥(CFSG.GroupTheory.SuzukiTorusData.torus Q₁ Q₂) ∣
      Nat.card (MulAction.orbit W Q₁) - 1 := by
  classical
  haveI : Finite (Sylow 2 X) := CFSG.GroupTheory.SuzukiTorusData.sylow_finite
  let O : Set (Sylow 2 X) := MulAction.orbit W Q₁
  have hQ₁O : Q₁ ∈ O := MulAction.mem_orbit_self Q₁
  let K : Subgroup X := CFSG.GroupTheory.SuzukiTorusData.torus Q₁ Q₂
  have hKQ1 : K ≤ Subgroup.normalizer ((Q₁ : Subgroup X) : Set X) :=
    CFSG.GroupTheory.SuzukiTorusData.torus_le_normalizer_left
  have hKQ2 : K ≤ Subgroup.normalizer ((Q₂ : Subgroup X) : Set X) :=
    CFSG.GroupTheory.SuzukiTorusData.torus_le_normalizer_right
  let α := ↥(O \ {Q₁})
  letI : MulAction K α :=
    { smul := fun k P =>
        ⟨k • (P : Sylow 2 X), by
          constructor
          · obtain ⟨w, hw⟩ := MulAction.mem_orbit_iff.mp P.2.1
            refine MulAction.mem_orbit_iff.mpr
              ⟨⟨(k : X) * (w : X), mul_mem (hKW k.2) w.2⟩, ?_⟩
            change ((k : X) * (w : X)) • Q₁ = (k : X) • (P : Sylow 2 X)
            have hwX : (w : X) • Q₁ = (P : Sylow 2 X) := hw
            rw [← hwX, mul_smul]
          · intro hkQ
            have hPne : (P : Sylow 2 X) ≠ Q₁ := by simpa using P.2.2
            apply hPne
            have hkQ' : (k : X) • (P : Sylow 2 X) = Q₁ := by
              simpa [Subgroup.smul_def] using hkQ
            have h1 : (k : X)⁻¹ • ((k : X) • (P : Sylow 2 X)) = (k : X)⁻¹ • Q₁ := by
              rw [hkQ']
            rw [smul_smul, inv_mul_cancel, one_smul] at h1
            rw [h1]
            exact Sylow.smul_eq_iff_mem_normalizer.mpr (inv_mem (hKQ1 k.2))⟩
      one_smul := fun P => Subtype.ext (one_smul K (P : Sylow 2 X))
      mul_smul := fun k l P => Subtype.ext (mul_smul k l (P : Sylow 2 X)) }
  have hfree : ∀ P : α, MulAction.stabilizer K P = ⊥ := by
    intro P
    rw [eq_bot_iff]
    intro k hk
    have hkfix : (k : X) • (P : Sylow 2 X) = (P : Sylow 2 X) := by
      have hkP : k • P = P := MulAction.mem_stabilizer_iff.mp hk
      have h := congrArg (fun Q : α => (Q : Sylow 2 X)) hkP
      change (k : K) • (P : Sylow 2 X) = (P : Sylow 2 X) at h
      simpa [Subgroup.smul_def] using h
    have hk1 : k = 1 := by
      by_contra hkne
      have hkH : (k : X) ≠ 1 := fun h1 => hkne (Subtype.ext h1)
      have hPne : (P : Sylow 2 X) ≠ Q₁ := by simpa using P.2.2
      have hPQ₂ : (P : Sylow 2 X) ≠ Q₂ := fun h => hQ₂ (h ▸ P.2.1)
      exact oddTorus_three_fixed T hkH
        (Sylow.smul_eq_iff_mem_normalizer.mpr (hKQ1 k.2))
        (Sylow.smul_eq_iff_mem_normalizer.mpr (hKQ2 k.2))
        hkfix hne (Ne.symm hPne) hPQ₂.symm
    simpa [hk1]
  have hdvd : Nat.card K ∣ Nat.card α :=
    CFSG.UnitaryThreeRecognition.card_dvd_of_stabilizer_eq_bot hfree
  have hα : Nat.card α = Nat.card O - 1 := by
    change Nat.card ↥(O \ {Q₁}) = Nat.card O - 1
    rw [Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_of_mem hQ₁O, Nat.card_coe_set_eq]
  rw [hα] at hdvd
  have hKcard : Nat.card K = 2 ^ n - 1 :=
    CFSG.GroupTheory.SuzukiTorusData.torus_card T hne
  rw [hKcard] at hdvd
  rw [show Nat.card ↥(CFSG.GroupTheory.SuzukiTorusData.torus Q₁ Q₂) = 2 ^ n - 1 from
    CFSG.GroupTheory.SuzukiTorusData.torus_card T hne]
  simpa [O] using hdvd

private theorem oddTorus_w_dvd_orbit {X : Type} [Group X]
    [Finite X] {n : ℕ} (hH : CFSG.Quasithin.IsSz n X)
    (T : CFSG.GroupTheory.SuzukiTorusData X (2 ^ n))
    {Q₁ Q₂ : Sylow 2 X} (hne : Q₁ ≠ Q₂) {W : Subgroup X}
    (hKW : CFSG.GroupTheory.SuzukiTorusData.torus Q₁ Q₂ ≤ W) (hW : Odd (Nat.card W))
    (P : Sylow 2 X) :
    Nat.card (MulAction.orbit W Q₁) ∣ Nat.card (MulAction.orbit W P) := by
  obtain ⟨hWQ1, -⟩ := oddTorus_stabilizer_eq_torus hH T hne hKW hW
  have hcardW : Nat.card W = Nat.card (MulAction.orbit W Q₁) * (2 ^ n - 1) := by
    have hOS := Subgroup.card_mul_index (MulAction.stabilizer W Q₁)
    rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq, mul_comm] at hOS
    rw [oddTorus_stabilizer_card_eq_inf, hWQ1,
      show Nat.card ↥(CFSG.GroupTheory.SuzukiTorusData.torus Q₁ Q₂) = 2 ^ n - 1 from
        CFSG.GroupTheory.SuzukiTorusData.torus_card T hne] at hOS
    exact hOS.symm
  have hOSp := Subgroup.card_mul_index (MulAction.stabilizer W P)
  rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq, mul_comm,
    oddTorus_stabilizer_card_eq_inf] at hOSp
  have hdvd : Nat.card ↥(W ⊓ Subgroup.normalizer ((P : Subgroup X) : Set X)) ∣
      2 ^ n - 1 := oddTorus_stabilizer_dvd hH hW P
  obtain ⟨e, he⟩ := hdvd
  rw [hcardW, he] at hOSp
  have hdpos : 0 < Nat.card ↥(W ⊓ Subgroup.normalizer ((P : Subgroup X) : Set X)) :=
    Nat.card_pos
  have hrhs : Nat.card (MulAction.orbit W Q₁) *
      (Nat.card ↥(W ⊓ Subgroup.normalizer ((P : Subgroup X) : Set X)) * e) =
      (Nat.card (MulAction.orbit W Q₁) * e) *
        Nat.card ↥(W ⊓ Subgroup.normalizer ((P : Subgroup X) : Set X)) := by ring
  have hcancel : Nat.card (MulAction.orbit W P) =
      Nat.card (MulAction.orbit W Q₁) * e := by
    apply Nat.eq_of_mul_eq_mul_right hdpos
    rw [hOSp, hrhs]
  exact ⟨e, hcancel⟩

private theorem oddTorus_w_dvd_card_sylow {X : Type} [Group X]
    [Finite X] {n : ℕ} (hH : CFSG.Quasithin.IsSz n X)
    (T : CFSG.GroupTheory.SuzukiTorusData X (2 ^ n))
    {Q₁ Q₂ : Sylow 2 X} (hne : Q₁ ≠ Q₂) {W : Subgroup X}
    (hKW : CFSG.GroupTheory.SuzukiTorusData.torus Q₁ Q₂ ≤ W) (hW : Odd (Nat.card W)) :
    Nat.card (MulAction.orbit W Q₁) ∣ (2 ^ n) ^ 2 + 1 := by
  haveI : Finite (Sylow 2 X) := CFSG.GroupTheory.SuzukiTorusData.sylow_finite
  haveI : Fintype (MulAction.orbitRel.Quotient W (Sylow 2 X)) := Fintype.ofFinite _
  have hcard : Nat.card (Sylow 2 X) =
      ∑ ω : MulAction.orbitRel.Quotient W (Sylow 2 X),
        Nat.card (MulAction.orbit W ω.out) := by
    rw [Nat.card_congr (MulAction.selfEquivSigmaOrbits W (Sylow 2 X)), Nat.card_sigma]
  have hsum : Nat.card (MulAction.orbit W Q₁) ∣
      ∑ ω : MulAction.orbitRel.Quotient W (Sylow 2 X),
        Nat.card (MulAction.orbit W ω.out) :=
    Finset.dvd_sum (fun ω _ => oddTorus_w_dvd_orbit hH T hne hKW hW ω.out)
  rw [← T.card_points, hcard]
  exact hsum

private theorem oddTorus_arith {q w : ℕ} (hq : Even q) (hq4 : 4 ≤ q) (hw : 0 < w)
    (hdiv : w ∣ q ^ 2 + 1) (hmod : q - 1 ∣ w - 1) : w = 1 := by
  obtain ⟨c, hc⟩ := hdiv
  by_contra hw1
  have hwge : q ≤ w := by
    obtain ⟨k, hk⟩ := hmod
    have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · rw [hk0, mul_zero] at hk
        omega
      · exact hkpos
    have hle : q - 1 ≤ w - 1 := by
      rw [hk]
      exact Nat.le_mul_of_pos_right (q - 1) hkpos
    omega
  have hcpos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with hc0 | hcpos
    · rw [hc0, mul_zero] at hc
      omega
    · exact hcpos
  have hcle : c ≤ q := by
    by_contra hcq
    push Not at hcq
    have h1 : q * (q + 1) ≤ q * c := Nat.mul_le_mul_left q (by omega)
    have h2 : q * c ≤ w * c := Nat.mul_le_mul_right c hwge
    have h3 : q * (q + 1) ≤ q ^ 2 + 1 := by
      calc q * (q + 1) ≤ q * c := h1
        _ ≤ w * c := h2
        _ = q ^ 2 + 1 := hc.symm
    nlinarith
  have hqmod : q ≡ 1 [MOD q - 1] := by
    have h := (Nat.modEq_iff_dvd' (by omega : 1 ≤ q)).2 (dvd_refl (q - 1))
    exact h.symm
  have hq2mod : q ^ 2 + 1 ≡ 2 [MOD q - 1] := by
    have h1 : q ^ 2 ≡ 1 [MOD q - 1] := by simpa using hqmod.pow 2
    simpa using h1.add (Nat.ModEq.refl 1)
  have hmodw : w ≡ 1 [MOD q - 1] :=
    ((Nat.modEq_iff_dvd' (by omega : 1 ≤ w)).2 hmod).symm
  have hcmod : c ≡ 2 [MOD q - 1] := by
    have h1 : c ≡ w * c [MOD q - 1] := by
      simpa using (hmodw.mul_right c).symm
    have h2 : w * c ≡ 2 [MOD q - 1] := by
      rw [← hc]
      exact hq2mod
    exact h1.trans h2
  have hcres : c % (q - 1) = 2 := by
    have h := hcmod
    rwa [Nat.ModEq, Nat.mod_eq_of_lt (by omega : 2 < q - 1)] at h
  have hdecomp : c = c / (q - 1) * (q - 1) + 2 := by
    have h := (Nat.div_add_mod' c (q - 1)).symm
    rwa [hcres] at h
  have hquot_lt : c / (q - 1) < 2 := by
    have hqlt : q < 2 * (q - 1) := by omega
    exact (Nat.div_lt_iff_lt_mul (by omega : 0 < q - 1)).mpr (by omega)
  have hquot_le : c / (q - 1) ≤ 1 := Nat.lt_succ_iff.mp hquot_lt
  have hquot_cases : c / (q - 1) = 0 ∨ c / (q - 1) = 1 :=
    Nat.le_one_iff_eq_zero_or_eq_one.mp hquot_le
  have hc2 : c = 2 := by
    rcases hquot_cases with h0 | h1
    · rw [h0] at hdecomp
      simpa using hdecomp
    · rw [h1] at hdecomp
      omega
  have hodd : Odd (q ^ 2 + 1) := by
    have hqeven : Even (q ^ 2) := hq.pow_of_ne_zero (by norm_num : 2 ≠ 0)
    simpa using hqeven.add_one
  have heven : Even (q ^ 2 + 1) := by
    rw [hc, hc2]
    simpa [Nat.mul_comm] using even_two_mul w
  exact (Nat.not_even_iff_odd.mpr hodd) heven

theorem eq_torus_of_odd_card {n : ℕ} {H : Type} [Group H]
    [Finite H]
    (hH : CFSG.Quasithin.IsSz n H) {Q₁ Q₂ : Sylow 2 H}
    (hne : Q₁ ≠ Q₂) {W : Subgroup H}
    (hK : normalizer ((Q₁ : Subgroup H) : Set H) ⊓ normalizer ((Q₂ : Subgroup H) : Set H) ≤ W)
    (hW : Odd (Nat.card W)) :
    W = normalizer ((Q₁ : Subgroup H) : Set H) ⊓ normalizer ((Q₂ : Subgroup H) : Set H) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T : CFSG.GroupTheory.SuzukiTorusData H (2 ^ n) :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.szPointActionFacts_holds H n
      (CFSG.GH74.Filter.lieModel_of_suzuki hH)
  haveI : Finite (Sylow 2 H) := CFSG.GroupTheory.SuzukiTorusData.sylow_finite
  have hKW : CFSG.GroupTheory.SuzukiTorusData.torus Q₁ Q₂ ≤ W := hK
  obtain ⟨hWQ1, -⟩ := oddTorus_stabilizer_eq_torus hH T hne hKW hW
  have hQ₂ : Q₂ ∉ MulAction.orbit W Q₁ := by
    rintro ⟨h, hh⟩
    exact oddTorus_no_smul hH T hne hKW hW h.2 hh
  have hdiv1 : 2 ^ n - 1 ∣ Nat.card (MulAction.orbit W Q₁) - 1 := by
    have h := oddTorus_dvd_orbit_sub_one T hne hKW hQ₂
    simpa [show Nat.card ↥(CFSG.GroupTheory.SuzukiTorusData.torus Q₁ Q₂) = 2 ^ n - 1 from
      CFSG.GroupTheory.SuzukiTorusData.torus_card T hne] using h
  have hdiv2 : Nat.card (MulAction.orbit W Q₁) ∣ (2 ^ n) ^ 2 + 1 :=
    oddTorus_w_dvd_card_sylow hH T hne hKW hW
  have hwpos : 0 < Nat.card (MulAction.orbit W Q₁) := by
    haveI : Nonempty (MulAction.orbit W Q₁) := ⟨⟨Q₁, MulAction.mem_orbit_self Q₁⟩⟩
    exact Nat.card_pos
  have hEven : Even (2 ^ n) := oddTorus_even_two_pow hH
  have h4 : 4 ≤ 2 ^ n := by have := oddTorus_two_pow_ge_eight hH; omega
  have hw1 : Nat.card (MulAction.orbit W Q₁) = 1 :=
    oddTorus_arith hEven h4 hwpos hdiv2 hdiv1
  have hcardW : Nat.card W = 2 ^ n - 1 := by
    have hOS := Subgroup.card_mul_index (MulAction.stabilizer W Q₁)
    rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq, mul_comm] at hOS
    rw [oddTorus_stabilizer_card_eq_inf, hWQ1,
      show Nat.card ↥(CFSG.GroupTheory.SuzukiTorusData.torus Q₁ Q₂) = 2 ^ n - 1 from
        CFSG.GroupTheory.SuzukiTorusData.torus_card T hne] at hOS
    rw [← hOS, hw1, one_mul]
  have hKcard : Nat.card ↥(CFSG.GroupTheory.SuzukiTorusData.torus Q₁ Q₂) = 2 ^ n - 1 :=
    CFSG.GroupTheory.SuzukiTorusData.torus_card T hne
  have hEq : CFSG.GroupTheory.SuzukiTorusData.torus Q₁ Q₂ = W :=
    Subgroup.eq_of_le_of_card_ge hKW (by rw [hcardW, hKcard])
  exact hEq.symm

private theorem noFour_pow_mul (r : ℕ) (hr : 3 ≤ r) :
    2 * 2 ^ (r - 3) = 2 ^ (r - 2) := by
  rw [← pow_succ']
  congr 1
  omega

private def noFour_zmodMulPow (r : ℕ) (hr : 3 ≤ r) :
    ZMod 4 →+ ZMod (2 * 2 ^ (r - 2)) :=
  ZMod.lift 4 ⟨(Int.castAddHom (ZMod (2 * 2 ^ (r - 2)))).comp
      (AddMonoidHom.mulRight ((2 ^ (r - 3) : ℕ) : ℤ)), by
    show (((4 : ℤ) * ((2 ^ (r - 3) : ℕ) : ℤ) : ℤ) : ZMod (2 * 2 ^ (r - 2))) = 0
    have h4 : (4 : ℕ) * 2 ^ (r - 3) = 2 * 2 ^ (r - 2) := by
      calc (4 : ℕ) * 2 ^ (r - 3) = 2 * (2 * 2 ^ (r - 3)) := by ring
        _ = 2 * 2 ^ (r - 2) := by rw [noFour_pow_mul r hr]
    rw [show ((4 : ℤ) * ((2 ^ (r - 3) : ℕ) : ℤ) : ℤ) = ((2 * 2 ^ (r - 2) : ℕ) : ℤ) by
      exact_mod_cast h4]
    rw [Int.cast_natCast]
    exact ZMod.natCast_self _
  ⟩

private theorem noFour_zmodMulPow_intCast (r : ℕ) (hr : 3 ≤ r) (m : ℤ) :
    noFour_zmodMulPow r hr (m : ZMod 4) =
      ((m * (2 ^ (r - 3) : ℕ) : ℤ) : ZMod (2 * 2 ^ (r - 2))) := by
  unfold noFour_zmodMulPow
  rw [ZMod.lift_coe]
  rfl

private theorem noFour_zmodMulPow_two (r : ℕ) (hr : 3 ≤ r) :
    noFour_zmodMulPow r hr ((2 : ℕ) : ZMod 4) =
      ((2 ^ (r - 2) : ℕ) : ZMod (2 * 2 ^ (r - 2))) := by
  rw [show ((2 : ℕ) : ZMod 4) = ((2 : ℤ) : ZMod 4) by norm_num,
    noFour_zmodMulPow_intCast]
  rw [show ((2 : ℤ) * ((2 ^ (r - 3) : ℕ) : ℤ) : ℤ) = ((2 * 2 ^ (r - 3) : ℕ) : ℤ) by
    push_cast
    ring]
  rw [noFour_pow_mul r hr]
  norm_num

private theorem noFour_zmodMulPow_injective (r : ℕ) (hr : 3 ≤ r) :
    Function.Injective (noFour_zmodMulPow r hr) := by
  unfold noFour_zmodMulPow
  rw [ZMod.lift_injective]
  intro m hm
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.mulRight_apply, Int.coe_castAddHom] at hm
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hm
  have hpow : 2 * 2 ^ (r - 2) = 4 * 2 ^ (r - 3) := by
    calc 2 * 2 ^ (r - 2) = 2 * (2 * 2 ^ (r - 3)) := by rw [noFour_pow_mul r hr]
      _ = 4 * 2 ^ (r - 3) := by ring
  have hm' : (4 * 2 ^ (r - 3) : ℤ) ∣ m * (2 ^ (r - 3) : ℕ) := by
    simpa [hpow] using hm
  have hk0 : ((2 ^ (r - 3) : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast (pow_pos (by norm_num : (0:ℕ) < 2) (r - 3)).ne'
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact (mul_dvd_mul_iff_right hk0).mp hm'

private def noFour_quaternionFunPow (r : ℕ) (hr : 3 ≤ r) (q : QuaternionGroup 2) :
    QuaternionGroup (2 ^ (r - 2)) :=
  match q with
  | QuaternionGroup.a i => QuaternionGroup.a (noFour_zmodMulPow r hr i)
  | QuaternionGroup.xa i => QuaternionGroup.xa (noFour_zmodMulPow r hr i)

@[simp] private theorem noFour_quaternionFunPow_a (r : ℕ) (hr : 3 ≤ r) (i : ZMod 4) :
    noFour_quaternionFunPow r hr (QuaternionGroup.a i) =
      QuaternionGroup.a (noFour_zmodMulPow r hr i) := rfl

@[simp] private theorem noFour_quaternionFunPow_xa (r : ℕ) (hr : 3 ≤ r) (i : ZMod 4) :
    noFour_quaternionFunPow r hr (QuaternionGroup.xa i) =
      QuaternionGroup.xa (noFour_zmodMulPow r hr i) := rfl

private def noFour_quaternionEmbedPow (r : ℕ) (hr : 3 ≤ r) :
    QuaternionGroup 2 →* QuaternionGroup (2 ^ (r - 2)) where
  toFun := noFour_quaternionFunPow r hr
  map_one' := by
    rw [QuaternionGroup.one_def, noFour_quaternionFunPow_a, map_zero]
    exact QuaternionGroup.a_zero
  map_mul' := by
    rintro (i | i) (j | j)
    · rw [QuaternionGroup.a_mul_a, noFour_quaternionFunPow_a, noFour_quaternionFunPow_a,
        noFour_quaternionFunPow_a, QuaternionGroup.a_mul_a, map_add]
    · rw [QuaternionGroup.a_mul_xa, noFour_quaternionFunPow_a, noFour_quaternionFunPow_xa,
        noFour_quaternionFunPow_xa, QuaternionGroup.a_mul_xa, map_sub]
    · rw [QuaternionGroup.xa_mul_a, noFour_quaternionFunPow_xa, noFour_quaternionFunPow_a,
        noFour_quaternionFunPow_xa, QuaternionGroup.xa_mul_a, map_add]
    · rw [QuaternionGroup.xa_mul_xa, noFour_quaternionFunPow_xa, noFour_quaternionFunPow_xa,
        noFour_quaternionFunPow_a, QuaternionGroup.xa_mul_xa]
      congr 1
      rw [map_sub, map_add, noFour_zmodMulPow_two r hr]

@[simp] private theorem noFour_quaternionEmbedPow_a (r : ℕ) (hr : 3 ≤ r) (i : ZMod 4) :
    noFour_quaternionEmbedPow r hr (QuaternionGroup.a i) =
      QuaternionGroup.a (noFour_zmodMulPow r hr i) := rfl

@[simp] private theorem noFour_quaternionEmbedPow_xa (r : ℕ) (hr : 3 ≤ r) (i : ZMod 4) :
    noFour_quaternionEmbedPow r hr (QuaternionGroup.xa i) =
      QuaternionGroup.xa (noFour_zmodMulPow r hr i) := rfl

private theorem noFour_quaternionEmbedPow_injective (r : ℕ) (hr : 3 ≤ r) :
    Function.Injective (noFour_quaternionEmbedPow r hr) := by
  intro x y h
  cases x <;> cases y <;>
    simp only [noFour_quaternionEmbedPow_a, noFour_quaternionEmbedPow_xa] at h
  · exact congrArg _ (noFour_zmodMulPow_injective r hr (QuaternionGroup.a.inj h))
  · nomatch h
  · nomatch h
  · exact congrArg _ (noFour_zmodMulPow_injective r hr (QuaternionGroup.xa.inj h))

theorem exists_normal_odd_of_not_four {n : ℕ} {H : Type}
    [Group H] [Finite H] (hH : CFSG.Quasithin.IsSz n H) {Y : Subgroup H}
    (h4 : ∀ E : Subgroup H, E ≤ Y → IsElemAbelian 2 E → Nat.card E ≠ 4) :
    ∃ W : Subgroup H, W ≤ Y ∧ (∀ g ∈ Y, ∀ w ∈ W, g * w * g⁻¹ ∈ W) ∧ Odd (Nat.card W) ∧
      ∀ g ∈ Y, Odd (orderOf g) → g ∈ W := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hY : ¬ CFSG.BenderSuzuki.PFchapter1section1.TwoRankAtLeastTwo ↥Y := by
    rintro ⟨E', hcard, hsq⟩
    let E : Subgroup H := E'.map Y.subtype
    have hEY : E ≤ Y := by
      rintro - ⟨x, -, rfl⟩
      exact x.2
    have hcardE : Nat.card E = 4 := by
      rw [Subgroup.card_map_of_injective Y.subtype_injective, hcard]
    have hsqE : ∀ x ∈ E, x ^ 2 = 1 := by
      rintro x ⟨e, he, rfl⟩
      have he2 : e ^ 2 = 1 := congrArg Subtype.val (hsq ⟨e, he⟩)
      rw [← map_pow, he2, map_one]
    have hcomm : IsMulCommutative E :=
      IsMulCommutative.of_comm fun a b =>
        (Commute.of_orderOf_dvd_two (fun x : E => by
          rw [← Subgroup.orderOf_coe]
          exact orderOf_dvd_of_pow_eq_one (hsqE (x : H) x.2)) a b).eq
    exact h4 E hEY ⟨hcomm, hsqE⟩ hcardE
  obtain ⟨S⟩ := Sylow.nonempty (p := 2) (G := ↥Y)
  rcases CFSG.BenderSuzuki.sylowTwo_cyclic_or_quaternion_of_not_twoRank hY S with
    hcyc | ⟨r, hr3, ⟨eQ⟩⟩
  · obtain ⟨-, -, -, ⟨hKnorm, hKodd, hKindex, -⟩, -⟩ :=
      CFSG.cyclic_sylow_normal_odd_complement S hcyc
    haveI : (pPrimeCore 2 ↥Y).Normal := hKnorm
    refine ⟨(pPrimeCore 2 ↥Y).map Y.subtype, ?_, ?_, ?_, ?_⟩
    · rintro - ⟨x, -, rfl⟩
      exact x.2
    · rintro g hg w ⟨x, hx, rfl⟩
      have hmem : (⟨g, hg⟩ : ↥Y) * x * (⟨g, hg⟩ : ↥Y)⁻¹ ∈ pPrimeCore 2 ↥Y :=
        hKnorm.conj_mem x hx ⟨g, hg⟩
      have heq : Y.subtype ((⟨g, hg⟩ : ↥Y) * x * (⟨g, hg⟩ : ↥Y)⁻¹) =
          g * Y.subtype x * g⁻¹ := by
        simp
      rw [← heq]
      exact Subgroup.mem_map_of_mem Y.subtype hmem
    · rw [Subgroup.card_map_of_injective Y.subtype_injective]
      exact hKodd
    · intro g hg hgodd
      let g' : ↥Y := ⟨g, hg⟩
      have hg'odd : Odd (orderOf g') := by
        rw [← Subgroup.orderOf_coe]
        exact hgodd
      let q : ↥Y ⧸ pPrimeCore 2 ↥Y := (g' : ↥Y ⧸ pPrimeCore 2 ↥Y)
      have hqodd : Odd (orderOf q) := by
        have h := hg'odd.of_dvd_nat (orderOf_map_dvd (QuotientGroup.mk' (pPrimeCore 2 ↥Y)) g')
        simpa [q] using h
      have hquotcard : Nat.card (↥Y ⧸ pPrimeCore 2 ↥Y) = Nat.card (S : Subgroup ↥Y) := by
        rw [← Subgroup.index_eq_card, hKindex]
      obtain ⟨m, hm⟩ := S.isPGroup'.exists_card_eq
      have hdvd : orderOf q ∣ 2 ^ m := by
        rw [← hm, ← hquotcard]
        exact orderOf_dvd_natCard q
      have hcop : Nat.Coprime (orderOf q) (2 ^ m) :=
        Nat.Coprime.pow_right m (Nat.coprime_two_right.mpr hqodd)
      have hone : orderOf q = 1 := by
        rw [← Nat.dvd_one]
        exact hcop.dvd_of_dvd_mul_left (by simpa using hdvd)
      have hq1 : q = 1 := orderOf_eq_one_iff.mp hone
      have hmemK : g' ∈ pPrimeCore 2 ↥Y :=
        (QuotientGroup.eq_one_iff g').mp (by simpa [q] using hq1)
      exact Subgroup.mem_map_of_mem Y.subtype hmemK
  · obtain ⟨a, ha, -, ⟨eH⟩⟩ := exists_mulEquiv_sz hH
    let ψ : QuaternionGroup 2 →* ↥(Sz a) :=
      eH.toMonoidHom.comp (Y.subtype.comp ((S : Subgroup ↥Y).subtype.comp
        (eQ.symm.toMonoidHom.comp (noFour_quaternionEmbedPow r hr3))))
    have hψ : Function.Injective ψ :=
      eH.injective.comp (Y.subtype_injective.comp ((S : Subgroup ↥Y).subtype_injective.comp
        (eQ.symm.injective.comp (noFour_quaternionEmbedPow_injective r hr3))))
    exfalso
    exact CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE.BenderSz.no_q8_sz ha ψ hψ

private theorem odd_card_inf_normalizer {n : ℕ} {H : Type} [Group H] [Finite H]
    (hH : CFSG.Quasithin.IsSz n H) {Q₁ Q₂ : Sylow 2 H} (hne : Q₁ ≠ Q₂) :
    Odd (Nat.card (normalizer ((Q₁ : Subgroup H) : Set H) ⊓
      normalizer ((Q₂ : Subgroup H) : Set H) : Subgroup H)) := by
  have T := CFSG.LocalAnalysis.UniquenessCase.UC22.szPointActionFacts_holds H n
    (CFSG.GH74.Filter.lieModel_of_suzuki hH)
  have hc := CFSG.GroupTheory.SuzukiTorusData.torus_card T hne
  have hn : 1 ≤ n := by
    obtain ⟨-, a, ha, -, -, -, rfl, -⟩ := hH
    omega
  change Odd (Nat.card (CFSG.GroupTheory.SuzukiTorusData.torus Q₁ Q₂))
  rw [hc]
  have hev : Even (2 ^ n) := (Nat.even_pow' (by omega)).2 even_two
  obtain ⟨m, hm⟩ := hev
  have h2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  exact ⟨m - 1, by omega⟩

theorem eq_top_or_le_normalizer_torus
    {n : ℕ} {H : Type} [Group H] [Finite H]
    (hH : CFSG.Quasithin.IsSz n H) {Q₁ Q₂ : Sylow 2 H} (hne : Q₁ ≠ Q₂) {Y : Subgroup H}
    (hK : normalizer ((Q₁ : Subgroup H) : Set H) ⊓ normalizer ((Q₂ : Subgroup H) : Set H) ≤ Y)
    {y : H} (hy : y ∈ Y) (hyQ : y • Q₁ = Q₂) :
    Y = ⊤ ∨ Y ≤ normalizer ((normalizer ((Q₁ : Subgroup H) : Set H) ⊓
      normalizer ((Q₂ : Subgroup H) : Set H) : Subgroup H) : Set H) := by
  by_cases h4 : ∃ E : Subgroup H, E ≤ Y ∧ IsElemAbelian 2 E ∧ Nat.card E = 4
  · obtain ⟨E, hEY, hE, hE4⟩ := h4
    exact Or.inl (eq_top_of_elemAbelian_four_le hH hne hK hy hyQ hEY hE hE4)
  · right
    have h4' : ∀ E : Subgroup H, E ≤ Y → IsElemAbelian 2 E → Nat.card E ≠ 4 :=
      fun E hEY hE hE4 => h4 ⟨E, hEY, hE, hE4⟩
    obtain ⟨W, -, hWn, hWo, hWodd⟩ := exists_normal_odd_of_not_four hH h4'
    have hKW : normalizer ((Q₁ : Subgroup H) : Set H) ⊓ normalizer ((Q₂ : Subgroup H) : Set H)
        ≤ W := by
      intro k hk
      refine hWodd k (hK hk) ?_
      have hd : orderOf k ∣ Nat.card (normalizer ((Q₁ : Subgroup H) : Set H) ⊓
          normalizer ((Q₂ : Subgroup H) : Set H) : Subgroup H) := by
        rw [← Subgroup.orderOf_mk k hk]
        exact orderOf_dvd_natCard _
      exact (odd_card_inf_normalizer hH hne).of_dvd_nat hd
    have hWK := eq_torus_of_odd_card hH hne hKW hWo
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [← hWK]
    constructor
    · intro hh
      exact hWn g hg h hh
    · intro hh
      have := hWn g⁻¹ (Y.inv_mem hg) _ hh
      simpa [mul_assoc] using this

end CFSG.LieType.SuzukiSubgroups

end
