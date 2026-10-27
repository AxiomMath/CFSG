module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGOutZetaBDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGOutZetaDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.U43 CFSG.ClassicalInvolution
open scoped commutatorElement

private theorem zetaBHub_lift_comp {A B : Type*} [Group A] [Group B] {ι : Type*}
    (φ : A →* B) (eh : ι → A) :
    FreeGroup.lift (fun i => φ (eh i)) = φ.comp (FreeGroup.lift eh) :=
  FreeGroup.ext_hom _ _ fun i => by simp

private theorem zetaBHub_lift_apply {A B : Type*} [Group A] [Group B] {ι : Type*}
    (φ : A →* B) (eh : ι → A) (w : FreeGroup ι) :
    FreeGroup.lift (fun i => φ (eh i)) w = φ (FreeGroup.lift eh w) := by
  rw [zetaBHub_lift_comp]
  rfl

private theorem zetaBHub_conj_pow_mul_inv {G : Type*} [Group G] {w a b : G} (m n : ℕ)
    (ha : w * a * w⁻¹ = a⁻¹) (hb : w * b * w⁻¹ = b⁻¹) (hab : a * b = b * a) :
    w * (a ^ m * b ^ n) * w⁻¹ = (a ^ m * b ^ n)⁻¹ := by
  have ha' : w * a ^ m * w⁻¹ = (a ^ m)⁻¹ := by
    rw [← conj_pow (i := m), ha, inv_pow]
  have hb' : w * b ^ n * w⁻¹ = (b ^ n)⁻¹ := by
    rw [← conj_pow (i := n), hb, inv_pow]
  rw [mul_inv_rev, ← ha', ← hb', (Commute.pow_pow hab m n).eq]
  group

theorem asc82FactZetaInv6_of_parts
    (hCore : ZetaCore)
    (hData : ZetaOmegaData) (hCorr : ZetaCorrect) (hInv : ZetaInvert) :
    Asc82FactZetaInv6 := by
  classical
  intro G _ _ L hL V _ _ _ Q hQ φ hcov w o hact hdet hsn x hx
  obtain ⟨hqs, hZcard, hmodel⟩ := hL
  haveI hperf : Group.IsPerfect ↥L := hqs.1
  let O : Subgroup ↥L := CFSG.oddCore ↥L
  let Z : Subgroup ↥L := Subgroup.center ↥L
  have hne : O ≠ ⊤ := by
    intro htop
    haveI : Subsingleton (↥L ⧸ O) := (QuotientGroup.subsingleton_iff).mpr htop
    have h1 : Nat.card (Subgroup.center (↥L ⧸ O)) ≤ 1 :=
      Finite.card_le_one_iff_subsingleton.mpr inferInstance
    have h2 : Nat.card (Subgroup.center (↥L ⧸ O)) = 2 := hZcard
    omega
  have hOpen : CFSG.Open.IsQuasisimple ↥L := ⟨hqs.1.commutator_eq_top, hqs.2.1⟩
  have hOZ : O ≤ Z :=
    CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hOpen O hne
  have hK : φ.ker ≤ Z := by rw [hcov.ker_eq]; exact hOZ
  have hcomap : (Subgroup.center (omegaGroup hQ)).comap φ = Z :=
    CFSG.ComponentClassification.Quasisimple.center_comap_of_central_kernel
      φ hcov.surjective hK
  let φ' : ↥L →* OGroup Q := (Subgroup.subtype (omegaGroup hQ)).comp φ
  have hφ'ker : φ'.ker ≤ Subgroup.center ↥L := by
    have hker_eq : φ'.ker = φ.ker :=
      MonoidHom.ker_comp_of_injective φ (Subgroup.subtype (omegaGroup hQ))
        (Subgroup.subtype_injective (omegaGroup hQ))
    rw [hker_eq]
    exact hK
  let π : ↥L →* ↥L ⧸ O := QuotientGroup.mk' O
  have hcenter : Z.map π = Subgroup.center (↥L ⧸ O) := by
    refine CFSG.ComponentClassification.Quasisimple.center_map_of_central_kernel π
      (QuotientGroup.mk'_surjective O) ?_
    rw [show π.ker = O from QuotientGroup.ker_mk' O]
    exact hOZ
  let ee : ↥L ⧸ Z ≃* (↥L ⧸ O) ⧸ Subgroup.center (↥L ⧸ O) :=
    (QuotientGroup.quotientQuotientEquivQuotient (N := O) (M := Z) hOZ).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hcenter)
  have hmodelL : CFSG.Blueprint.LieModel (↥L ⧸ Z) .PSU 4 3 1 :=
    hmodel.of_mulEquiv ee.symm
  obtain ⟨A, B, g, hgdet1, hgdet2, hrelcent, hwgAB, hAncent, hpair⟩ :=
    hData hQ hcov.finrank_eq hcov.quadSign_eq
  obtain ⟨ω, hω⟩ :=
    hCorr G L φ hcov.surjective w o hact hdet hsn g hgdet1 hgdet2
  let w' : G := w * (ω : G)
  have hw'norm : w' ∈ Subgroup.normalizer (L : Set G) := by
    simpa only [w'] using
      mul_mem hact.1 (Subgroup.le_normalizer (H := L) ω.2)
  have hω'' : ∀ l l' : ↥L, (l' : G) = w' * (l : G) * w'⁻¹ →
      φ' l' = g * φ' l * g⁻¹ := by
    intro l l' hl
    exact hω l l' (by simpa only [w'] using hl)
  obtain ⟨ah, hah⟩ := hcov.surjective A
  obtain ⟨bh, hbh⟩ := hcov.surjective B
  let eh : Fin 2 → ↥L := ![ah, bh]
  have heh0 : eh 0 = ah := rfl
  have hφeh : (fun i => φ (eh i)) = ![A, B] := by
    funext i
    fin_cases i <;>
      simp [eh, hah, hbh, Matrix.cons_val_zero, Matrix.cons_val_one]
  let q : ↥L →* ↥L ⧸ Z := QuotientGroup.mk' Z
  have hkerZ : q.ker = Z := QuotientGroup.ker_mk' Z
  have hq_eq_one : ∀ y : ↥L, q y = 1 ↔ y ∈ Z := fun y =>
    (MonoidHom.mem_ker (f := q) (x := y)).symm.trans (by rw [hkerZ])
  have hmemZ_iff : ∀ y : ↥L, y ∈ Z ↔ φ y ∈ Subgroup.center (omegaGroup hQ) := by
    intro y
    rw [← hcomap]
    exact Subgroup.mem_comap
  have hq_eq_iff : ∀ a b : ↥L, q a = q b ↔ a⁻¹ * b ∈ Z := by
    intro a b
    rw [← hq_eq_one (a⁻¹ * b), map_mul, map_inv, inv_mul_eq_one]
  have hrel : ∀ r ∈ wordSet rels, FreeGroup.lift (fun i => q (eh i)) r = 1 := by
    intro r hr
    rw [zetaBHub_lift_apply q eh r]
    exact (hq_eq_one (FreeGroup.lift eh r)).mpr
      ((hmemZ_iff (FreeGroup.lift eh r)).mpr (by
        rw [← zetaBHub_lift_apply φ eh r, hφeh]
        exact hrelcent r hr))
  have hne0 : q (eh 0) ≠ 1 := by
    intro h1
    have hmem : φ (eh 0) ∈ Subgroup.center (omegaGroup hQ) :=
      (hmemZ_iff (eh 0)).mp ((hq_eq_one (eh 0)).mp h1)
    rw [heh0, hah] at hmem
    exact hAncent hmem
  have hwg : ∀ i, FreeGroup.lift (fun j => q (eh j)) (zW i) = q (eh i) := by
    intro i
    rw [zetaBHub_lift_apply q eh (zW i)]
    refine (hq_eq_iff (FreeGroup.lift eh (zW i)) (eh i)).mpr ?_
    refine (hmemZ_iff _).mpr ?_
    rw [map_mul, map_inv]
    have h1 : φ (FreeGroup.lift eh (zW i)) = ![A, B] i := by
      rw [← zetaBHub_lift_apply φ eh (zW i), hφeh]
      exact hwgAB i
    have h2 : φ (eh i) = ![A, B] i := congrFun hφeh i
    rw [h1, h2, inv_mul_cancel]
    exact Subgroup.one_mem _
  let u : Fin 2 → ↥L := fun k => FreeGroup.lift (zCanon eh) (FreeGroup.mk (zU k))
  let v : Fin 2 → ↥L := fun k => FreeGroup.lift (zCanon eh) (FreeGroup.mk (zV k))
  have hφe : (fun i => φ (zCanon eh i)) = ![A, B] := by
    funext i
    have h1 : φ (zCanon eh i) = FreeGroup.lift (fun j => φ (eh j)) (zW i) := by
      change φ (FreeGroup.lift eh (zW i)) =
        FreeGroup.lift (fun j => φ (eh j)) (zW i)
      exact (zetaBHub_lift_apply φ eh (zW i)).symm
    rw [h1, hφeh]
    exact hwgAB i
  have hφu : ∀ k, φ' (u k) =
      ((FreeGroup.lift ![A, B] (FreeGroup.mk (zU k)) : omegaGroup hQ) : OGroup Q) := by
    intro k
    change ((φ (FreeGroup.lift (zCanon eh) (FreeGroup.mk (zU k))) : omegaGroup hQ) :
        OGroup Q) =
      ((FreeGroup.lift ![A, B] (FreeGroup.mk (zU k)) : omegaGroup hQ) : OGroup Q)
    rw [← zetaBHub_lift_apply φ (zCanon eh) (FreeGroup.mk (zU k)), hφe]
  have hφv : ∀ k, φ' (v k) =
      ((FreeGroup.lift ![A, B] (FreeGroup.mk (zV k)) : omegaGroup hQ) : OGroup Q) := by
    intro k
    change ((φ (FreeGroup.lift (zCanon eh) (FreeGroup.mk (zV k))) : omegaGroup hQ) :
        OGroup Q) =
      ((FreeGroup.lift ![A, B] (FreeGroup.mk (zV k)) : omegaGroup hQ) : OGroup Q)
    rw [← zetaBHub_lift_apply φ (zCanon eh) (FreeGroup.mk (zV k)), hφe]
  have hInv_k : ∀ k, ⁅u k, v k⁆ ∈ φ'.ker ∧
      w' * ((⁅u k, v k⁆ : ↥L) : G) * w'⁻¹ = (((⁅u k, v k⁆ : ↥L) : G))⁻¹ := by
    intro k
    exact hInv L φ' hφ'ker w' hw'norm g hω'' (u k) (v k)
      (by rw [hφu k, hφv k]; exact (hpair k).1)
      (by rw [hφu k]; exact (hpair k).2.1)
      (by rw [hφv k]; exact (hpair k).2.2)
  have hc : ∀ k, zComm (zCanon eh) k ∈ q.ker := by
    intro k
    rw [hkerZ]
    have heq : zComm (zCanon eh) k = ⁅u k, v k⁆ := rfl
    rw [heq]
    exact hφ'ker (hInv_k k).1
  have hqker : q.ker ≤ Subgroup.center ↥L := by
    rw [hkerZ]
  obtain ⟨hexp12, hgen3⟩ :=
    hCore q (QuotientGroup.mk'_surjective Z) hqker
      hperf.commutator_eq_top hmodelL eh hrel hne0 hwg hc
  change x ∈ O.map L.subtype at hx
  obtain ⟨x', hx'O, hx'x⟩ := Subgroup.mem_map.mp hx
  have hx'qker : x' ∈ q.ker := by rw [hkerZ]; exact hOZ hx'O
  have hx12 : x' ^ 12 = 1 := hexp12 x' hx'qker
  have hOddO : Odd (Nat.card O) := CFSG.ComponentClassification.OddCore.odd_card ↥L
  have hx'ord_dvd : orderOf x' ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O hx'O
  have hodd_x' : Odd (orderOf x') := hOddO.of_dvd_nat hx'ord_dvd
  have hx'12dvd : orderOf x' ∣ 12 := orderOf_dvd_iff_pow_eq_one.mpr hx12
  have hcop4 : Nat.Coprime (orderOf x') 4 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact (Nat.coprime_pow_right_iff (by norm_num) _ 2).mpr hodd_x'.coprime_two_right
  have hx'3dvd : orderOf x' ∣ 3 := by
    have h : orderOf x' ∣ 4 * 3 := by simpa using hx'12dvd
    exact hcop4.dvd_of_dvd_mul_left h
  have hx'3 : x' ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp hx'3dvd
  obtain ⟨i, j, hx'eq⟩ := hgen3 x' hx'qker hx'3
  let C : Fin 2 → G := fun k => ((zComm (zCanon eh) k : ↥L) : G)
  have hωc : ∀ k, (ω : G) * C k * (ω : G)⁻¹ = C k := by
    intro k
    have hcent : zComm (zCanon eh) k ∈ Subgroup.center ↥L := hφ'ker (hInv_k k).1
    have hcommL : (ω : ↥L) * zComm (zCanon eh) k =
        zComm (zCanon eh) k * (ω : ↥L) :=
      Subgroup.mem_center_iff.mp hcent ω
    have hcommG : (ω : G) * C k = C k * (ω : G) := by
      simpa [C] using congrArg (Subgroup.subtype L) hcommL
    rw [hcommG]
    group
  have hwC : ∀ k, w * C k * w⁻¹ = (C k)⁻¹ := by
    intro k
    have h := (hInv_k k).2
    have h' : (w * (ω : G)) * C k * (w * (ω : G))⁻¹ = (C k)⁻¹ := by
      simpa only [C, w', zComm, u, v] using h
    have hkey : (w * (ω : G)) * C k * (w * (ω : G))⁻¹ = w * C k * w⁻¹ := by
      rw [show (w * (ω : G)) * C k * (w * (ω : G))⁻¹ =
        w * ((ω : G) * C k * (ω : G)⁻¹) * w⁻¹ by group, hωc k]
    rwa [hkey] at h'
  have hC01 : C 0 * C 1 = C 1 * C 0 := by
    have hcent0 : zComm (zCanon eh) 0 ∈ Subgroup.center ↥L := hφ'ker (hInv_k 0).1
    have hcL : zComm (zCanon eh) 0 * zComm (zCanon eh) 1 =
        zComm (zCanon eh) 1 * zComm (zCanon eh) 0 :=
      (Subgroup.mem_center_iff.mp hcent0 (zComm (zCanon eh) 1)).symm
    simpa [C] using congrArg (Subgroup.subtype L) hcL
  rw [← hx'x, hx'eq]
  simp only [map_mul, map_pow]
  exact zetaBHub_conj_pow_mul_inv (4 * (i : ℕ)) (4 * (j : ℕ)) (hwC 0) (hwC 1) hC01

end CFSG.OddStandard.SmallF3.Omega
