module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeSymThreeBase
import CFSG.GroupTheory.PCore.PrimeCoreImages
import CFSG.Mathlib.GroupTheory.PermCommute
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.SymThree

open Equiv

theorem eq_one_of_mem_inf_center {Q : Type*} [Group Q] {C Y : Subgroup Q}
    (hC : C ≤ Subgroup.center Q) (eY : Y ≃* Perm (Fin 3)) {y : Q} (hyY : y ∈ Y) (hyC : y ∈ C) :
    y = 1 := by
  have hcomm : ∀ h : Perm (Fin 3), eY ⟨y, hyY⟩ * h = h * eY ⟨y, hyY⟩ := by
    intro h
    have h1 := Subgroup.mem_center_iff.1 (hC hyC) (eY.symm h : Q)
    have h2 : (eY.symm h) * (⟨y, hyY⟩ : Y) = (⟨y, hyY⟩ : Y) * (eY.symm h) :=
      Subtype.ext h1
    have h3 := congrArg eY h2
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h3
    exact h3.symm
  have h4 : eY ⟨y, hyY⟩ = 1 := CFSG.perm_eq_one_of_forall_commute (by simp) hcomm
  exact congrArg Subtype.val (eY.injective (h4.trans (map_one eY).symm))

theorem exists_mul_of_central {Q : Type*} [Group Q] [Finite Q] {C : Subgroup Q}
    (hC : C ≤ Subgroup.center Q) (hC3 : Nat.card C = 3) (hQ : Nat.card Q = 18)
    {Y : Subgroup Q} (eY : Y ≃* Perm (Fin 3)) (q : Q) : ∃ y ∈ Y, ∃ c ∈ C, y * c = q := by
  let μ : Y × C → Q := fun p => (p.1 : Q) * (p.2 : Q)
  have hinj : Function.Injective μ := by
    rintro ⟨y, c⟩ ⟨y', c'⟩ h
    have h1 : (y' : Q)⁻¹ * y = (c' : Q) * (c : Q)⁻¹ := by
      have h2 : (y : Q) * c = y' * c' := h
      calc (y' : Q)⁻¹ * y = (y' : Q)⁻¹ * (y * c) * (c : Q)⁻¹ := by group
        _ = (c' : Q) * (c : Q)⁻¹ := by rw [h2]; group
    have hY : (y' : Q)⁻¹ * y ∈ Y := Y.mul_mem (Y.inv_mem y'.2) y.2
    have hC' : (y' : Q)⁻¹ * y ∈ C := by rw [h1]; exact C.mul_mem c'.2 (C.inv_mem c.2)
    have h3 : (y' : Q)⁻¹ * y = 1 := eq_one_of_mem_inf_center hC eY hY hC'
    have h4 : (c' : Q) * (c : Q)⁻¹ = 1 := h1.symm.trans h3
    have hyy : y = y' := Subtype.ext (inv_mul_eq_one.1 h3).symm
    have hcc : c' = c := Subtype.ext (mul_inv_eq_one.1 h4)
    exact Prod.ext hyy hcc.symm
  have hbij : Function.Bijective μ := by
    refine hinj.bijective_of_nat_card_le ?_
    have h18 : Nat.card (Y × C) = 18 := by
      rw [Nat.card_prod, card_eq_six_of_mulEquiv eY, hC3]
    omega
  obtain ⟨⟨y, c⟩, hyc⟩ := hbij.2 q
  exact ⟨y, y.2, c, c.2, hyc⟩

theorem eq_of_central_aux {Q : Type*} [Group Q] [Finite Q] {C : Subgroup Q}
    (hC : C ≤ Subgroup.center Q) (hC3 : Nat.card C = 3) (hQ : Nat.card Q = 18)
    {X W : Subgroup Q} (eX : X ≃* Perm (Fin 3)) (eW : W ≃* Perm (Fin 3)) : X = W := by
  have hinv : ∀ u ∈ W, u * u = 1 → u ∈ X := by
    intro u _ hu
    obtain ⟨x, hx, c, hc, rfl⟩ := exists_mul_of_central hC hC3 hQ eX u
    have hcomm : c * x = x * c := (Subgroup.mem_center_iff.1 (hC hc) x).symm
    have h1 : c * c = (x * x)⁻¹ := by
      have h2 : x * c * (x * c) = x * x * (c * c) := by
        calc x * c * (x * c) = x * (c * x) * c := by group
          _ = x * (x * c) * c := by rw [hcomm]
          _ = x * x * (c * c) := by group
      rw [h2] at hu
      exact eq_inv_of_mul_eq_one_right hu
    have hcX : c * c ∈ X := by rw [h1]; exact X.inv_mem (X.mul_mem hx hx)
    have hcC : c * c ∈ C := C.mul_mem hc hc
    have hcc : c * c = 1 := eq_one_of_mem_inf_center hC eX hcX hcC
    have hc3 : c ^ 3 = 1 := by
      have h : (⟨c, hc⟩ : C) ^ Nat.card C = 1 := pow_card_eq_one'
      rw [hC3] at h
      exact congrArg Subtype.val h
    have hc1 : c = 1 := by
      calc c = c ^ 3 * (c * c)⁻¹ := by group
        _ = 1 := by rw [hc3, hcc]; group
    rw [hc1, mul_one]
    exact hx
  have hZ : (X.subgroupOf W).map eW.toMonoidHom = ⊤ := by
    rw [eq_top_iff, ← Equiv.Perm.closure_isSwap]
    refine (Subgroup.closure_le _).2 ?_
    intro s hs
    obtain ⟨a, b, hab, rfl⟩ := hs
    have hww : ((eW.symm (swap a b) : W) : Q) * ((eW.symm (swap a b) : W) : Q) = 1 := by
      have h := congrArg eW.symm (swap_mul_self a b)
      rw [map_mul, map_one] at h
      exact congrArg Subtype.val h
    refine ⟨eW.symm (swap a b), ?_, by simp⟩
    exact hinv _ (eW.symm (swap a b)).2 hww
  have hWX : W ≤ X := by
    intro w hw
    have hmem : eW ⟨w, hw⟩ ∈ (X.subgroupOf W).map eW.toMonoidHom := by
      rw [hZ]
      trivial
    obtain ⟨w', hw', hww'⟩ := hmem
    have : w' = ⟨w, hw⟩ := eW.injective hww'
    rw [this] at hw'
    exact hw'
  have hX6 := card_eq_six_of_mulEquiv eX
  have hW6 := card_eq_six_of_mulEquiv eW
  exact (Subgroup.eq_of_le_of_card_ge hWX (by omega)).symm

theorem card_central_cover {R : Type*} [Group R] [Finite R] (f : R →* Perm (Fin 4))
    (hf : Function.Surjective f) (hcard : Nat.card f.ker = 3) : Nat.card R = 72 := by
  have h := Subgroup.card_ker_mul_card_of_surjective hf
  rw [hcard, Nat.card_perm, Nat.card_fin] at h
  have h24 : (4 : ℕ).factorial = 24 := rfl
  omega

theorem four_le_card_pCore_of_central_cover {R : Type*} [Group R] [Finite R]
    (f : R →* Perm (Fin 4)) (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center R)
    (hcard : Nat.card f.ker = 3) : 4 ≤ Nat.card (CFSG.pCore 2 R) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR := card_central_cover f hf hcard
  have hpker : IsPGroup 3 f.ker := IsPGroup.of_card (n := 1) (by rw [hcard]; norm_num)
  have himg := CFSG.central_p_kernel_prime_core_image (p := 3) f hf hker hpker
  have hV : kleinFourS4 ≤ CFSG.pPrimeCore 3 (Perm (Fin 4)) :=
    le_sSup ⟨inferInstance, by rw [card_kleinFourS4]; norm_num⟩
  have hTcop : Nat.Coprime 3 (Nat.card (CFSG.pPrimeCore 3 R)) := CFSG.pPrimeCore_coprime_card
  have hTdvd : Nat.card (CFSG.pPrimeCore 3 R) ∣ 8 * 9 := by
    have h := Subgroup.card_subgroup_dvd_card (CFSG.pPrimeCore 3 R)
    rwa [hR] at h
  have hT8 : Nat.card (CFSG.pPrimeCore 3 R) ∣ 2 ^ 3 :=
    Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_right 2 hTcop.symm) hTdvd
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hT8
  have hT2 : IsPGroup 2 (CFSG.pPrimeCore 3 R) := IsPGroup.of_card (n := i) hi
  have hTle : CFSG.pPrimeCore 3 R ≤ CFSG.pCore 2 R := le_sSup ⟨inferInstance, hT2⟩
  have h4 : 4 ≤ Nat.card ((CFSG.pPrimeCore 3 R).map f) := by
    rw [← himg]
    have h := Subgroup.card_le_of_le hV
    rwa [card_kleinFourS4] at h
  have h5 : Nat.card ((CFSG.pPrimeCore 3 R).map f) ≤ Nat.card (CFSG.pPrimeCore 3 R) :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd (f := f) (H := CFSG.pPrimeCore 3 R))
  exact h4.trans (h5.trans (Subgroup.card_le_of_le hTle))

theorem eq_of_central_cover {R : Type*} [Group R] [Finite R] (f : R →* Perm (Fin 4))
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center R) (hcard : Nat.card f.ker = 3)
    {X W : Subgroup (R ⧸ CFSG.pCore 2 R)} (eX : X ≃* Perm (Fin 3)) (eW : W ≃* Perm (Fin 3)) :
    X = W := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR := card_central_cover f hf hcard
  have hO4 := four_le_card_pCore_of_central_cover f hf hker hcard
  have hQO : Nat.card R = Nat.card (R ⧸ CFSG.pCore 2 R) * Nat.card (CFSG.pCore 2 R) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := 2) (G := R))
  have h6 : 6 ∣ Nat.card (R ⧸ CFSG.pCore 2 R) := by
    rw [← card_eq_six_of_mulEquiv eX]
    exact Subgroup.card_subgroup_dvd_card X
  obtain ⟨b, hb⟩ := h6
  have hdvd : 2 ^ a ∣ 72 := by
    have h := Subgroup.card_subgroup_dvd_card (CFSG.pCore 2 R)
    rwa [ha, hR] at h
  have ha6 : a ≤ 6 := by
    by_contra hcon
    have h128 : 2 ^ 7 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  rw [ha] at hO4 hQO
  have hQ18 : Nat.card (R ⧸ CFSG.pCore 2 R) = 18 := by
    interval_cases a <;> omega
  let C : Subgroup (R ⧸ CFSG.pCore 2 R) := f.ker.map (QuotientGroup.mk' (CFSG.pCore 2 R))
  have hC : C ≤ Subgroup.center (R ⧸ CFSG.pCore 2 R) := by
    rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    induction g using QuotientGroup.induction_on with
    | H r =>
      rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subgroup.mem_center_iff.1 (hker hk) r
  have hinj : Function.Injective ((QuotientGroup.mk' (CFSG.pCore 2 R)).comp f.ker.subtype) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, hx⟩ h
    have hxO : x ∈ CFSG.pCore 2 R := (QuotientGroup.eq_one_iff x).1 h
    have h3 : x ^ 3 = 1 := by
      have h' : (⟨x, hx⟩ : f.ker) ^ Nat.card f.ker = 1 := pow_card_eq_one'
      rw [hcard] at h'
      exact congrArg Subtype.val h'
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (G := R) ⟨x, hxO⟩
    have hk' : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have h1 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    have h2 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
    exact Subtype.ext (orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h1 h2))
  have hrange : ((QuotientGroup.mk' (CFSG.pCore 2 R)).comp f.ker.subtype).range = C := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hC3 : Nat.card C = 3 := by
    rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hcard]
  exact eq_of_central_aux hC hC3 hQ18 eX eW

end CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.SymThree
