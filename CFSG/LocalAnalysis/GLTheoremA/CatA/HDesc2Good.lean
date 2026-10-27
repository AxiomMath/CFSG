module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2Base
public import CFSG.GroupTheory.QuasisimpleCenterDivisibility

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HDesc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.KD264Lie TauCeti
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer innAutDerived)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

@[expose] def GoodSubAt (p : ℕ) (d : ValidLieTypeIndex) (k : ℕ) : Prop :=
  ∀ [Finite (CFSGIndex.lie d).Group], p ∣ Nat.card (CFSGIndex.lie d).Group →
    ∀ (A : Subgroup (MulAut (CFSGIndex.lie d).Group)),
    IsElemAbelian p A → p ^ (k + 1) ≤ Nat.card A →
    ∀ T : Subgroup (CFSGIndex.lie d).Group, IsPGroup 2 T → T ≠ ⊥ →
      (∀ α ∈ A, T.map α.toMonoidHom = T) → ∃ F ≤ A, Nat.card F = p ^ k ∧ IsGood p F

@[expose] def GoodSubAtLow (p : ℕ) (d : ValidLieTypeIndex) (k : ℕ) : Prop :=
  ∀ [Finite (CFSGIndex.lie d).Group], p ∣ Nat.card (CFSGIndex.lie d).Group →
    ∀ (A : Subgroup (MulAut (CFSGIndex.lie d).Group)),
    IsElemAbelian p A → p ^ (k + 1) ≤ Nat.card A →
    (∀ kk : ℕ, i5LowBound p d.1 kk → p ^ kk ≤ Nat.card A) →
    ∀ T : Subgroup (CFSGIndex.lie d).Group, IsPGroup 2 T → T ≠ ⊥ →
      (∀ α ∈ A, T.map α.toMonoidHom = T) → ∃ F ≤ A, Nat.card F = p ^ k ∧ IsGood p F

section KLevel

variable {Y : Type} [Group Y] [Finite Y]

theorem dvd_card_lie_of_khyp {p : ℕ} (hp : p.Prime) {K B : Subgroup Y} (h : KHyp p K B)
    (d : ValidLieTypeIndex) (e : ↥K ⧸ Subgroup.center ↥K ≃* (CFSGIndex.lie d).Group) :
    p ∣ Nat.card (CFSGIndex.lie d).Group := by
  have hpdvdK : p ∣ Nat.card ↥K := by
    by_contra hpdvd
    haveI hntQ : Nontrivial (↥K ⧸ Subgroup.center ↥K) := h.qs.2.toNontrivial
    haveI hntK : Nontrivial ↥K :=
      (QuotientGroup.mk'_surjective (Subgroup.center ↥K)).nontrivial
    have hcop : Nat.Coprime p (Nat.card ↥(⊤ : Subgroup ↥K)) := by
      rw [Subgroup.card_top, hp.coprime_iff_not_dvd]
      exact hpdvd
    have htopbot : (⊤ : Subgroup ↥K) = ⊥ :=
      (CFSG.pPrimeCore_eq_bot_iff (p := p) (G := ↥K)).1 h.core ⊤ inferInstance hcop
    have hsub : Subsingleton ↥K := by
      refine ⟨fun a b => ?_⟩
      have ha : a ∈ (⊥ : Subgroup ↥K) := by rw [← htopbot]; exact Subgroup.mem_top a
      have hb : b ∈ (⊥ : Subgroup ↥K) := by rw [← htopbot]; exact Subgroup.mem_top b
      rw [Subgroup.mem_bot] at ha hb
      rw [ha, hb]
    exact not_subsingleton ↥K hsub
  rw [← Nat.card_congr e.toEquiv]
  exact CFSG.dvd_card_quotient_center_of_quasisimple
    ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).2 h.qs))
    hp hpdvdK

theorem kConcl_of_good_subgroup {p : ℕ} (hp : p.Prime) {K B : Subgroup Y} (h : KHyp p K B)
    (hBN : B ≤ Subgroup.normalizer (K : Set Y)) {S : Type} [Group S] [Finite S]
    (e : ↥K ⧸ Subgroup.center ↥K ≃* S) {F : Subgroup (MulAut S)}
    (hFA : F ≤ (kd264Rho hBN e).range)
    (hcard : Nat.card F * Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) = p ^ 3)
    (hgood : IsGood p F) : KConcl p K B := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hperf : Group.IsPerfect ↥K := Group.isPerfect_def.mpr h.qs.1
  set Ft : Subgroup Y := (F.comap (kd264Rho hBN e)).map B.subtype with hFt
  have hker : Nat.card (kd264Rho hBN e).ker =
      Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) := by
    rw [ker_kd264Rho hperf hBN]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := B ⊓ Subgroup.centralizer (K : Set Y))
        (K := B) inf_le_left).toEquiv
  have hcomp : Nat.card (F.comap (kd264Rho hBN e)) =
      Nat.card F * Nat.card (kd264Rho hBN e).ker := by
    have h' := CFSG.GorensteinWalter.card_map_eq_card_mul_card_ker
      (kd264Rho hBN e) (F.comap (kd264Rho hBN e))
    rw [Subgroup.map_comap_eq_self hFA,
      inf_eq_right.mpr (Subgroup.ker_le_comap (f := kd264Rho hBN e) F)] at h'
    exact h'
  have hFtcard : Nat.card Ft = p ^ 3 := by
    calc Nat.card Ft = Nat.card (F.comap (kd264Rho hBN e)) :=
        Subgroup.card_map_of_injective B.subtype_injective
      _ = Nat.card F * Nat.card (kd264Rho hBN e).ker := hcomp
      _ = p ^ 3 := by rw [hker]; exact hcard
  have hFtB : Ft ≤ B := Subgroup.map_subtype_le _
  exact ⟨Ft, hFtB, isElemAbelian_mono h.elem hFtB, hFtcard,
    kd264LiftGood_holds hp Y K B hBN S e F hFA hgood⟩

theorem kConcl_of_goodSub {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K B : Subgroup Y}
    (h : KHyp p K B) (d : ValidLieTypeIndex) [Finite (CFSGIndex.lie d).Group]
    (e : ↥K ⧸ Subgroup.center ↥K ≃* (CFSGIndex.lie d).Group) {k : ℕ} (hk : k ≤ 2)
    (hS : GoodSubAt p d k)
    (hc : Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) = p ^ (3 - k)) : KConcl p K B := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hBN := le_normalizer_of_normal (B := B) h.normal
  have hperf : Group.IsPerfect ↥K := Group.isPerfect_def.mpr h.qs.1
  have hmul := card_range_kd264Rho_mul hperf hBN e
  have hA := isElemAbelian_range h.elem hBN e
  have hcard : p ^ (k + 1) ≤ Nat.card (kd264Rho hBN e).range := by
    have h4 := h.card
    rw [← hmul, hc] at h4
    have h5 : p ^ (k + 1) * p ^ (3 - k) = p ^ 4 := by
      rw [← pow_add]
      congr 1
      omega
    have : p ^ (k + 1) * p ^ (3 - k) ≤ Nat.card (kd264Rho hBN e).range * p ^ (3 - k) := by
      rw [h5]; exact h4
    exact Nat.le_of_mul_le_mul_right this (pow_pos hp.pos _)
  obtain ⟨T', hT2, hT, hAT⟩ := exists_stable_two_subgroup hp hp2 h hBN e
  obtain ⟨F, hFA, hFcard, hFgood⟩ := hS (dvd_card_lie_of_khyp hp h d e) _ hA hcard T' hT2 hT hAT
  refine kConcl_of_good_subgroup hp h hBN e hFA ?_ hFgood
  rw [hFcard, hc, ← pow_add]
  congr 1
  omega

theorem solvesAt_of_goodSub {p : ℕ} (d : ValidLieTypeIndex) (h1 : GoodSubAt p d 1)
    (h2 : GoodSubAt p d 2) : SolvesAt p d := by
  intro hp hp2 Y _ _ K B h he hc
  obtain ⟨e⟩ := he
  haveI : Finite (CFSGIndex.lie d).Group := Finite.of_equiv _ e.toEquiv
  have hBN := le_normalizer_of_normal (B := B) h.normal
  obtain ⟨-, c, hc2, hcc⟩ := card_range_ge hp h hBN e hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply h.cent
    rw [pow_zero] at hcc
    exact Subgroup.card_eq_one.1 hcc
  left
  rcases (by omega : c = 1 ∨ c = 2) with rfl | rfl
  · exact kConcl_of_goodSub hp hp2 h d e (k := 2) (by norm_num) h2 hcc
  · exact kConcl_of_goodSub hp hp2 h d e (k := 1) (by norm_num) h1 hcc

theorem kConcl_of_goodSubLow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hLow : KD264LiftLow p)
    {K B : Subgroup Y} (h : KHyp p K B) (d : ValidLieTypeIndex) [Finite (CFSGIndex.lie d).Group]
    (e : ↥K ⧸ Subgroup.center ↥K ≃* (CFSGIndex.lie d).Group) {k : ℕ} (hk : k ≤ 2)
    (hS : GoodSubAtLow p d k)
    (hc : Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) = p ^ (3 - k)) : KConcl p K B := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hBN := le_normalizer_of_normal (B := B) h.normal
  have hperf : Group.IsPerfect ↥K := Group.isPerfect_def.mpr h.qs.1
  have hmul := card_range_kd264Rho_mul hperf hBN e
  have hA := isElemAbelian_range h.elem hBN e
  have hcard : p ^ (k + 1) ≤ Nat.card (kd264Rho hBN e).range := by
    have h4 := h.card
    rw [← hmul, hc] at h4
    have h5 : p ^ (k + 1) * p ^ (3 - k) = p ^ 4 := by
      rw [← pow_add]
      congr 1
      omega
    have : p ^ (k + 1) * p ^ (3 - k) ≤ Nat.card (kd264Rho hBN e).range * p ^ (3 - k) := by
      rw [h5]; exact h4
    exact Nat.le_of_mul_le_mul_right this (pow_pos hp.pos _)
  obtain ⟨m, hm⟩ := exists_card_eq_pow_of_isElemAbelian hp hA
  have hlow : ∀ kk : ℕ, i5LowBound p d.1 kk → p ^ kk ≤ Nat.card (kd264Rho hBN e).range := by
    intro kk hkk
    rw [hm]
    exact Nat.pow_le_pow_right hp.pos (hLow Y K B hBN d e m h.qs h.elem h.maxrank hm kk hkk)
  obtain ⟨T', hT2, hT, hAT⟩ := exists_stable_two_subgroup hp hp2 h hBN e
  obtain ⟨F, hFA, hFcard, hFgood⟩ :=
    hS (dvd_card_lie_of_khyp hp h d e) _ hA hcard hlow T' hT2 hT hAT
  refine kConcl_of_good_subgroup hp h hBN e hFA ?_ hFgood
  rw [hFcard, hc, ← pow_add]
  congr 1
  omega

theorem solvesAt_of_goodSubLow {p : ℕ} (hLow : KD264LiftLow p) (d : ValidLieTypeIndex)
    (h1 : GoodSubAtLow p d 1) (h2 : GoodSubAtLow p d 2) : SolvesAt p d := by
  intro hp hp2 Y _ _ K B h he hc
  obtain ⟨e⟩ := he
  haveI : Finite (CFSGIndex.lie d).Group := Finite.of_equiv _ e.toEquiv
  have hBN := le_normalizer_of_normal (B := B) h.normal
  obtain ⟨-, c, hc2, hcc⟩ := card_range_ge hp h hBN e hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply h.cent
    rw [pow_zero] at hcc
    exact Subgroup.card_eq_one.1 hcc
  left
  rcases (by omega : c = 1 ∨ c = 2) with rfl | rfl
  · exact kConcl_of_goodSubLow hp hp2 hLow h d e (k := 2) (by norm_num) h2 hcc
  · exact kConcl_of_goodSubLow hp hp2 hLow h d e (k := 1) (by norm_num) h1 hcc

end KLevel

end CFSG.LocalAnalysis.GLTheoremA.HDesc
