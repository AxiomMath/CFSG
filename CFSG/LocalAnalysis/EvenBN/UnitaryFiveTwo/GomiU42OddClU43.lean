module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClPSU
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClMain
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSUOrder

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup Matrix CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.CatLeafProof (nonempty_mulEquiv_primeFormP_of_lieModel')
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput lieOrderNumerator)

theorem u42_card_primeFormP_four {K : Type} [Field K] (h : UnitaryFieldData 3 1 K) :
    Nat.card (primeFormP h (idGram K 4)) = 3265920 := by
  have h1 : Nat.card (primeFormP h (idGram K 4)) * Nat.gcd 4 (3 ^ 1 + 1) =
      lieOrderNumerator .PSU 4 (3 ^ 1) :=
    CFSG.HardMathSupport.Lang.Coordinator.card_primeFormP_one_mul_gcd h (n := 4) (by norm_num)
  have h2 : lieOrderNumerator .PSU 4 (3 ^ 1) = 13063680 := by decide
  rw [h2] at h1
  have h3 : Nat.gcd 4 (3 ^ 1 + 1) = 4 := by norm_num
  rw [h3] at h1
  omega


theorem u42_detU_pow_four {K : Type} [Field K] (h : UnitaryFieldData 3 1 K)
    (x : ↥(primeFormUnitary h (idGram K 4))) :
    (((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det) ^ 4 = 1 := by
  obtain ⟨hmem, -⟩ := u42_N₁ h (by norm_num : 1 ≤ 4)
  have hN : h.norm ((u42DetU h 4 x : Kˣ) : K) = 1 := by
    rw [← hmem, ← u42_unitaryDet_toLinU h x]
    exact ⟨_, rfl⟩
  rw [h.norm_eq_pow, u42DetU_apply, GeneralLinearGroup.val_det_apply] at hN
  simpa using hN

theorem gomiU42NoU43 : GomiU42NoU43 := by
  intro X _ _ J D E a h hm
  haveI := h.normal
  have hadm : StatedLieAdmissible .PSU 4 3 1 := hm.admissible
  obtain ⟨K, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_primeFormP_of_lieModel' hadm hm
  haveI : Finite K := hK.finite
  have hC : IsPrimeFormGram (1 : GL (Fin 4) K) := isPrimeFormGram_one
  have hq : ¬((4 : ℕ) = 3 ∧ 3 ^ 1 = 2) := by norm_num
  have hn : 3 ≤ 4 := by norm_num
  have hσ : orderOf (MulAut.conjNormal a : MulAut ↥D) = 2 := h.fixedRoot_conjNormal.1
  obtain ⟨-, -, A, φ, hφ, hσeq, g, hdet, hcomm⟩ := u42_psu_concrete hK hn
    (MulAut.congr e (MulAut.conjNormal a)) ((u42OrderOf_congr e _).trans hσ)
    (h.u42Hyp.congr e _ _)
  let κ : X →* MulAut (primeFormP hK (idGram K 4)) :=
    (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal : X →* MulAut ↥D)
  have hκinj : Function.Injective κ := fun x y hxy =>
    h.conjNormal_injective ((MulAut.congr e).injective hxy)
  have hκD : ∀ d : ↥D, κ (d : X) = MulAut.conj (e d) := fun d => by
    change MulAut.congr e (MulAut.conjNormal (d : X)) = _
    rw [MulAut.conjNormal_val, u42Congr_conj_eq]
  have hD : Nat.card ↥D = 3265920 := by
    rw [Nat.card_congr e.toEquiv]
    exact u42_card_primeFormP_four hK
  let ϕ := primeFormFieldFactor hK hC hn hq
  have hϕc : ∀ B : ↥(primeFormUnitary hK (idGram K 4)), ϕ (primeFormConjHom hK (idGram K 4) B) = 1 := by
    intro B
    have e1 := primeFormFieldFactor_apply hK hC hn hq B 1
    rwa [map_one, mul_one] at e1
  have hϕΨ : ∀ (B : ↥(primeFormUnitary hK (idGram K 4))) (ψ : K ≃+* K),
      ϕ (primeFormPsi hK hC ⟨B, ψ⟩) = ψ := fun B ψ => primeFormFieldFactor_psi hK hC hn hq ⟨B, ψ⟩
  have hinn : ∀ α ∈ inner (primeFormP hK (idGram K 4)), ∃ d : ↥D, κ (d : X) = α := by
    rintro α ⟨y, rfl⟩
    exact ⟨e.symm y, by rw [hκD, MulEquiv.apply_symm_apply]⟩
  have hinnϕ : ∀ α ∈ inner (primeFormP hK (idGram K 4)), ϕ α = 1 := by
    intro α hα
    obtain ⟨s, rfl⟩ := (mem_inner_primeFormP hK (idGram K 4) α).1 hα
    exact hϕc _
  have hAut : Nat.card (K ≃+* K) = 2 := by
    have := (card_ringAut_and_isCyclic hK.prime K hK.card).1
    simpa using this
  have hinS : ∀ B : ↥(primeFormUnitary hK (idGram K 4)), ((B : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1 →
      primeFormConjHom hK (idGram K 4) B ∈ inner (primeFormP hK (idGram K 4)) := fun B hB =>
    (mem_inner_primeFormP hK (idGram K 4) _).2 ⟨⟨(B : GL (Fin 4) K), B.2, hB⟩, rfl⟩
  have hex : ∃ B : ↥(primeFormUnitary hK (idGram K 4)),
      primeFormConjHom hK (idGram K 4) B ∈ κ.range ∧
        ((B : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = -1 := by
    by_contra hno
    push Not at hno
    have hdet1 : ∀ B : ↥(primeFormUnitary hK (idGram K 4)),
        primeFormConjHom hK (idGram K 4) B ∈ κ.range →
          ((B : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1 := by
      intro B hB
      by_contra hne1
      have h4 := u42_detU_pow_four hK B
      have hsq : ((B : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det ^ 2 = 1 ∨
          ((B : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det ^ 2 = -1 := by
        have h5 : (((B : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det ^ 2 - 1) *
            (((B : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det ^ 2 + 1) = 0 := by
          linear_combination h4
        rcases mul_eq_zero.mp h5 with h6 | h6
        · left
          linear_combination h6
        · right
          linear_combination h6
      rcases hsq with h6 | h6
      · have h7 : (((B : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det - 1) *
            (((B : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det + 1) = 0 := by
          linear_combination h6
        rcases mul_eq_zero.mp h7 with h8 | h8
        · exact hne1 (by linear_combination h8)
        · exact hno B hB (by linear_combination h8)
      · refine hno (B * B) ?_ ?_
        · rw [map_mul]
          exact mul_mem hB hB
        · change ((((B : GL (Fin 4) K) * (B : GL (Fin 4) K) : GL (Fin 4) K)) :
            Matrix (Fin 4) (Fin 4) K).det = -1
          rw [Units.val_mul, Matrix.det_mul]
          linear_combination h6
    have hker : ∀ x : X, ϕ (κ x) = 1 → x ∈ D := by
      intro x hx
      have hx' : κ x ∈ primeFormD hK (idGram K 4) := by
        rw [← ker_primeFormFieldFactor hK hC hn hq]
        exact hx
      obtain ⟨B, hB⟩ := hx'
      obtain ⟨d, hd⟩ := hinn _ (hinS B (hdet1 B ⟨x, hB.symm⟩))
      have hxd : x = (d : X) := hκinj (hB.symm.trans hd.symm)
      rw [hxd]
      exact d.2
    have hle : (ϕ.comp κ).ker ≤ D := fun x hx => hker x hx
    have h1 : Nat.card ↥(ϕ.comp κ).ker ∣ Nat.card ↥D := Subgroup.card_dvd_of_le hle
    have h2 : Nat.card ↥(ϕ.comp κ).range ∣ 2 :=
      hAut ▸ Subgroup.card_subgroup_dvd_card _
    have h3 : Nat.card X = Nat.card ↥(ϕ.comp κ).ker * Nat.card ↥(ϕ.comp κ).range :=
      u42_card_eq_ker_mul_range (ϕ.comp κ)
    have h4 : Nat.card X ∣ 3265920 * 2 := by
      rw [h3]
      rw [hD] at h1
      exact Nat.mul_dvd_mul h1 h2
    exact absurd (h.two_pow_nine_dvd.trans h4) (by norm_num)
  obtain ⟨B₁, hB₁Y, hB₁det⟩ := hex
  have hgY : primeFormConjHom hK (idGram K 4) g ∈ κ.range := by
    have h1 : primeFormConjHom hK (idGram K 4) (g * B₁⁻¹) ∈ inner (primeFormP hK (idGram K 4)) := by
      apply hinS
      have e1 : ((GeneralLinearGroup.det ((g : GL (Fin 4) K) * (B₁ : GL (Fin 4) K)⁻¹) : Kˣ) : K) =
          ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det *
            (((B₁ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det)⁻¹ := by
        rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val,
          GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_det_apply]
      rw [GeneralLinearGroup.val_det_apply] at e1
      change ((((g : GL (Fin 4) K) * (B₁ : GL (Fin 4) K)⁻¹ : GL (Fin 4) K)) :
        Matrix (Fin 4) (Fin 4) K).det = 1
      rw [e1, hdet, hB₁det]
      norm_num
    obtain ⟨d, hd⟩ := hinn _ h1
    have e2 : primeFormConjHom hK (idGram K 4) g =
        primeFormConjHom hK (idGram K 4) (g * B₁⁻¹) * primeFormConjHom hK (idGram K 4) B₁ := by
      rw [← map_mul]
      congr 1
      group
    rw [e2]
    exact mul_mem ⟨d, hd⟩ hB₁Y
  obtain ⟨x, hx⟩ := hgY
  have hxa : x ∈ Subgroup.centralizer ({a} : Set X) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply hκinj
    rw [map_mul, map_mul, hx]
    exact hcomm.symm
  have hφne : φ ≠ 1 := by
    intro h1
    obtain ⟨c₀, hc₀⟩ := hK.exists_bar_ne
    apply hc₀
    rw [← hφ c₀, h1]
    rfl
  set C := Subgroup.centralizer ({a} : Set X) with hCdef
  let ρ : ↥C →* (K ≃+* K) := (ϕ.comp κ).comp C.subtype
  have haC : a ∈ C := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hρa : ρ ⟨a, haC⟩ = φ := by
    change ϕ (κ a) = φ
    change ϕ (MulAut.congr e (MulAut.conjNormal a)) = φ
    rw [hσeq]
    exact hϕΨ A φ
  have hρrange : Nat.card ↥ρ.range = 2 := by
    have h1 : Nat.card ↥ρ.range ∣ 2 := hAut ▸ Subgroup.card_subgroup_dvd_card _
    have h2 : Nat.card ↥ρ.range ≠ 1 := by
      intro hone
      have hbot : ρ.range = ⊥ := (Subgroup.card_eq_one).1 hone
      have h3 : ρ ⟨a, haC⟩ ∈ ρ.range := ⟨_, rfl⟩
      rw [hbot, Subgroup.mem_bot, hρa] at h3
      exact hφne h3
    rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h4 | h4
    · exact absurd h4 h2
    · exact h4
  have hCcard : Nat.card ↥C = 51840 := h.card_centralizer
  have hkerρ : Nat.card ↥ρ.ker = 25920 := by
    have h1 := u42_card_eq_ker_mul_range ρ
    rw [hCcard, hρrange] at h1
    omega
  have hJC : J ≤ C := by
    rw [hCdef, ← h.sup_eq]
    exact le_sup_right
  have hJker : J.subgroupOf C ≤ ρ.ker := by
    intro y hy
    rw [MonoidHom.mem_ker]
    have hyD : (y : X) ∈ D := h.le_D hy
    change ϕ (κ (y : X)) = 1
    rw [show κ (y : X) = κ ((⟨(y : X), hyD⟩ : ↥D) : X) from rfl, hκD]
    exact hinnϕ _ ⟨e ⟨y, hyD⟩, rfl⟩
  have hJcard : Nat.card ↥(J.subgroupOf C) = 25920 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJC).toEquiv]
    exact h.card_J
  have hker_eq : J.subgroupOf C = ρ.ker :=
    Subgroup.eq_of_le_of_card_ge hJker (by rw [hkerρ, hJcard])
  have hxJ : x ∈ J := by
    have h1 : (⟨x, hxa⟩ : ↥C) ∈ ρ.ker := by
      rw [MonoidHom.mem_ker]
      change ϕ (κ x) = 1
      rw [hx]
      exact hϕc g
    rw [← hker_eq] at h1
    exact h1
  have hcg : primeFormConjHom hK (idGram K 4) g ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (primeFormP hK (idGram K 4)) := by
    rw [← hx, show κ x = κ ((⟨x, h.le_D hxJ⟩ : ↥D) : X) from rfl, hκD]
    exact ⟨_, rfl⟩
  obtain ⟨s, hs⟩ := (mem_inner_primeFormP hK (idGram K 4) _).1 hcg
  set sU : ↥(primeFormUnitary hK (idGram K 4)) := ⟨(s : GL (Fin 4) K), s.2.1⟩ with hsU
  have h1 : primeFormConjHom hK (idGram K 4) (sU⁻¹ * g) = 1 := by
    rw [map_mul, map_inv, hs]
    exact inv_mul_cancel _
  have h2 : primeFormPsi hK hC ⟨sU⁻¹ * g, 1⟩ = 1 := by
    rw [primeFormPsi_apply, map_one, mul_one]
    exact h1
  obtain ⟨-, cc, hcc, hu⟩ := (primeFormPsi_eq_one_iff hK hC hn _).1 h2
  have h3 : GeneralLinearGroup.det ((sU⁻¹ * g : ↥(primeFormUnitary hK (idGram K 4))) :
      GL (Fin 4) K) = GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 4) cc) :=
    congrArg _ hu
  rw [GeneralLinearGroup.det_scalar, Fintype.card_fin, Subgroup.coe_mul, Subgroup.coe_inv, map_mul,
    map_inv] at h3
  have hsdet : GeneralLinearGroup.det (sU : GL (Fin 4) K) = 1 := Units.ext s.2.2
  rw [hsdet, inv_one, one_mul] at h3
  have h4 : ((GeneralLinearGroup.det (g : GL (Fin 4) K) : Kˣ) : K) = (cc : K) ^ 4 := by
    rw [h3]
    simp
  rw [GeneralLinearGroup.val_det_apply, hdet] at h4
  rw [hK.norm_eq_pow] at hcc
  have h5 : (-1 : K) = 1 := by
    rw [h4]
    simpa using hcc
  exact two_ne_zero_of_odd hK (by norm_num) (by linear_combination -h5)

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
