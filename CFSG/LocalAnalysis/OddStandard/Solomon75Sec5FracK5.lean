module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FracPerf
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5OneSmall
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5OneZ

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS CFSG.ComponentClassification.CatalogueBPrimeJoin
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {n : ℕ}

theorem mem_centralizerSection_of_piece {M : Subgroup X}
    (hM : IsDoubleCoverOfAlt (↥M ⧸ pPrimeCore 2 ↥M) n)
    {u : X} (huM : u ∈ M) (hu2 : u * u = 1) {E : Subgroup X}
    (hEM : E ≤ M ⊓ centralizer ({u} : Set X))
    (hE : IsPComponent 2 (E.subgroupOf (M ⊓ centralizer ({u} : Set X)))) (huE : u ∈ E) :
    u ∈ centralizerSection M (pPrimeCoreOf 2 M) := by
  classical
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  set O : Subgroup ↥M := pPrimeCore 2 ↥M with hO
  let C := AhatData.CoverSetup.ofCover hM
  let q : ↥M →* (↥M ⧸ O) := QuotientGroup.mk' O
  let uM : ↥M := ⟨u, huM⟩
  have huM2 : uM * uM = 1 := Subtype.ext hu2
  set ū : ↥M ⧸ O := q uM with hū
  have hnc : C.ρ ū ≠ 1 := by
    intro h1
    apply hcon
    have hcen : ū ∈ Subgroup.center (↥M ⧸ O) := (C.ρ_eq_one_iff).1 h1
    have hc : CentModOdd M u := by
      intro a ha
      have h2 : q ⁅(⟨a, ha⟩ : ↥M), uM⁆ = 1 := by
        rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.1 hcen _)
      have hmem : ⁅a, u⁆ ∈ M := by
        simp only [commutatorElement_def]
        exact M.mul_mem (M.mul_mem (M.mul_mem ha huM) (M.inv_mem ha)) (M.inv_mem huM)
      exact mem_oddCoreOf_iff.2 ⟨hmem, (QuotientGroup.eq_one_iff _).1 h2⟩
    exact mem_QOf_iff.2 ⟨Subgroup.le_normalizer huM, hc⟩
  have hτ2 : C.ρ ū * C.ρ ū = 1 := by
    rw [← map_mul, hū, ← map_mul, huM2, map_one, map_one]
  obtain ⟨k, hk⟩ := exists_support_card_of_mul_self hτ2
  have hk1 : 1 ≤ k := by
    by_contra h0
    have hk0 : k = 0 := by omega
    rw [hk0, mul_zero, Finset.card_eq_zero, Equiv.Perm.support_eq_empty_iff] at hk
    exact hnc hk
  have hind := C.induces_conj ū
  obtain ⟨hkn, g, hg, hind'⟩ := hind.exists_std hτ2 hk
  set C' := C.conjPerm g with hC'
  set F : Subgroup (↥M ⧸ O) := AhatData.fixSub (MulAut.conj ū) with hF
  have hFeq : F = centralizer ({ū} : Set (↥M ⧸ O)) := AhatData.fixSub_conj ū
  set X₁ : Subgroup ↥M := (centralizer ({u} : Set X)).subgroupOf M with hX₁
  set E₁ : Subgroup ↥M := E.subgroupOf M with hE₁
  have hEc : E ≤ centralizer ({u} : Set X) := hEM.trans inf_le_right
  have hEM' : E ≤ M := hEM.trans inf_le_left
  have hE₁X : E₁ ≤ X₁ := Subgroup.subgroupOf_mono M hEc
  have hE₁comp : IsPComponent 2 (E₁.subgroupOf X₁) := by
    have h1 : IsPComponent 2 (E.subgroupOf (centralizer ({u} : Set X) ⊓ M)) := by
      rwa [inf_comm] at hE
    exact (isPComponent_subgroupOf_subgroupOf_iff hEc hEM').2 h1
  have hker : ¬ 2 ∣ Nat.card q.ker := by
    show ¬ 2 ∣ Nat.card (QuotientGroup.mk' O).ker
    rw [QuotientGroup.ker_mk']
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 pPrimeCore_coprime_card
  have hXq : X₁.map q = F := by
    rw [hFeq]
    have hT : IsPGroup 2 ↥(Subgroup.zpowers uM) := isPGroup_zpowers_of_mul_self huM2
    have : Fact (IsPGroup 2 ↥(Subgroup.zpowers uM)) := ⟨hT⟩
    have h := centralizer_map_quotient_eq_map_centralizer 2 (Subgroup.zpowers uM) O
      pPrimeCore_normal pPrimeCore_coprime_card
    simp only at h
    rw [Subgroup.zpowers_eq_closure, MonoidHom.map_closure, Set.image_singleton] at h
    simp only [Subgroup.centralizer_closure] at h
    rw [hX₁, ← centralizer_singleton_subgroup huM]
    exact h.symm
  have hĒ : IsPComponent 2 ((E₁.map q).subgroupOf F) := by
    have := ComponentClassification.GSThmB.OddQuot.isPComponent_map q hker hE₁X hE₁comp
    rwa [hXq] at this
  have hĒF : E₁.map q ≤ F := hXq ▸ Subgroup.map_mono hE₁X
  have hEq : IsTwoGenQuasi ↥(E₁.map q) :=
    (isTwoGenQuasi_subgroupOf_iff hĒF).1 (isPComponent_two_iff.1 hĒ).2
  let ρX : ↥F →* Perm (Fin n) := C'.ρ.comp F.subtype
  let Y : Subgroup ↥F := (invSwapGrp (stdInv n k hkn) stdInv_mul_self).comap ρX
  have hρXσ : ∀ x : ↥F, ρX x * stdInv n k hkn = stdInv n k hkn * ρX x := fun x =>
    hind'.ρ_comm_of_mem_fixSub x.2
  have hYn : Y.Normal := by
    refine ⟨fun y hy x => ?_⟩
    rw [Subgroup.mem_comap] at hy ⊢
    rw [map_mul, map_mul, map_inv]
    exact invSwapGrp_conj_mem stdInv_mul_self (hρXσ x) hy
  have hYp : IsPGroup 2 ↥Y := by
    intro y
    refine ⟨2, ?_⟩
    have h1 : ρX y * ρX y = 1 := invSwapGrp_mul_self stdInv_mul_self y.2
    have h2 : C'.ρ (((y : ↥F) : ↥M ⧸ O)) * C'.ρ (((y : ↥F) : ↥M ⧸ O)) = 1 := h1
    have h3 : ((y : ↥F) : ↥M ⧸ O) * ((y : ↥F) : ↥M ⧸ O) ∈ Subgroup.center (↥M ⧸ O) :=
      C'.sq_mem_center h2
    have h4 := C'.sq_of_mem_center h3
    apply Subtype.ext
    apply Subtype.ext
    show ((y : ↥F) : ↥M ⧸ O) ^ 2 ^ 2 = 1
    calc ((y : ↥F) : ↥M ⧸ O) ^ 2 ^ 2
        = (((y : ↥F) : ↥M ⧸ O) * ((y : ↥F) : ↥M ⧸ O)) *
          (((y : ↥F) : ↥M ⧸ O) * ((y : ↥F) : ↥M ⧸ O)) := by simp [pow_succ, mul_assoc]
      _ = 1 := h4
  set Z' : Subgroup (↥M ⧸ O) := Y.map F.subtype with hZ'
  have hZN : Z' ≤ F := Subgroup.map_subtype_le _
  have hZsub : Z'.subgroupOf F = Y :=
    Subgroup.comap_map_eq_self_of_injective F.subtype_injective Y
  have hNZ : F ≤ normalizer (Z' : Set (↥M ⧸ O)) := by
    have : (Z'.subgroupOf F).Normal := by rw [hZsub]; exact hYn
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hZN).1 this
  have hZp : IsPGroup 2 ↥Z' :=
    hYp.of_equiv (Subgroup.equivMapOfInjective Y F.subtype F.subtype_injective)
  have hcentr : E₁.map q ≤ centralizer (Z' : Set (↥M ⧸ O)) :=
    le_centralizer_of_isPCompIn_of_normal_pgroup ⟨hĒF, hĒ⟩ hZN hNZ hZp
  set Ē : Subgroup (↥M ⧸ O) := E₁.map q with hĒdef
  have hūĒ : ū ∈ Ē := Subgroup.mem_map_of_mem q (show uM ∈ E₁ from huE)
  have huū : ū * ū = 1 := by rw [hū, ← map_mul, huM2, map_one]
  have hR : Odd (Nat.card (pPrimeCore 2 ↥Ē)) := Nat.coprime_two_left.1 pPrimeCore_coprime_card
  obtain ⟨P, hPperf, hxP⟩ := exists_perfect_subgroup_of_cover (E := ↥Ē) (R := pPrimeCore 2 ↥Ē) hR
    (commutator_top_sup_pPrimeCore hEq) (x := ⟨ū, hūĒ⟩)
    ⟨1, Subtype.ext (by simpa [pow_two] using huū)⟩
  set P' : Subgroup (↥M ⧸ O) := P.map Ē.subtype with hP'
  have hP'perf : ⁅P', P'⁆ = P' := by rw [hP', ← Subgroup.map_commutator, hPperf]
  have hP'Ē : P' ≤ Ē := Subgroup.map_subtype_le _
  have hūP' : ū ∈ P' := ⟨⟨ū, hūĒ⟩, hxP, rfl⟩
  have hPF : P' ≤ AhatData.fixSub (MulAut.conj ū) := hP'Ē.trans hĒF
  have hPY : ∀ p ∈ P', ∀ y ∈ AhatData.fixSub (MulAut.conj ū),
      C'.ρ y ∈ invSwapGrp (stdInv n k hkn) stdInv_mul_self → p * y = y * p := by
    intro p hp y hy hρy
    have hyZ : y ∈ Z' := ⟨⟨y, hy⟩, (show (⟨y, hy⟩ : ↥F) ∈ Y from hρy), rfl⟩
    exact (Subgroup.mem_centralizer_iff.1 (hcentr (hP'Ē hp)) y hyZ).symm
  have hxρ : C'.ρ ū = stdInv n k hkn := by rw [hC', C.ρ_conjPerm g ū]; exact hg
  exact hind'.false_of_perfect hPF hP'perf hPY hūP' hxρ hk1

end CFSG.OddStandard.Solomon75
