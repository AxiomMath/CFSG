module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59Fus
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59R6
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59Base

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33
  CFSG.ComponentClassification.AschbacherTheorem5.DeltaLocal

section Cent2

variable {G : Type} [Group G] [Finite G]

theorem fz59_cent2 {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}
    (hctx : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 2) :
    ∀ P : Subgroup G, IsPGroup 2 P → P ≤ centralizer ({t} : Set G) → Nat.card P ≤ 2 ^ 7 := by
  intro P hP hPle
  have hSc : Nat.card S = 2 ^ 7 := by rw [hctx.card_S, hK]; norm_num
  have hrel := Subgroup.relIndex_mul_card (H := S) (K := invCent t)
  rw [inf_eq_left.mpr hctx.le_invCent, hSc] at hrel
  have hdvd : Nat.card P ∣ Nat.card (invCent t) := Subgroup.card_dvd_of_le hPle
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hodd : Odd (S.relIndex (invCent t)) :=
    Nat.not_even_iff_odd.mp (by simpa [even_iff_two_dvd] using hctx.relIndex_odd)
  have hcop : Nat.Coprime (2 ^ k) (S.relIndex (invCent t)) :=
    (Nat.coprime_two_left.mpr hodd).pow_left k
  rw [hk, ← hrel] at hdvd
  have hdvd' : 2 ^ k ∣ 2 ^ 7 := hcop.dvd_of_dvd_mul_left hdvd
  rw [hk]
  exact Nat.le_of_dvd (by positivity) hdvd'

end Cent2

section CentZ

theorem fz59_card_ker_le {H K : Type*} [Group H] [Group K] (θ : H →* K) {a b : H}
    (ha : θ a ^ 3 = 1) (ha1 : θ a ≠ 1) (hb : θ b ^ 2 = 1) (hb1 : θ b ≠ 1) {m : ℕ}
    (hH : Nat.card H = 6 * m) (hm : 0 < m) : Nat.card θ.ker ≤ m := by
  have hprod := Subgroup.card_ker_mul_card_range θ
  have h3 : 3 ∣ Nat.card θ.range := by
    have := Subgroup.orderOf_dvd_natCard θ.range (θ.mem_range.mpr ⟨a, rfl⟩)
    rwa [orderOf_eq_prime ha ha1] at this
  have h2 : 2 ∣ Nat.card θ.range := by
    have := Subgroup.orderOf_dvd_natCard θ.range (θ.mem_range.mpr ⟨b, rfl⟩)
    rwa [orderOf_eq_prime hb hb1] at this
  have h6 : 2 * 3 ∣ Nat.card θ.range := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
  obtain ⟨c, hc⟩ := h6
  rw [hH, hc] at hprod
  have hcpos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · rw [h0] at hprod
      omega
    · exact h0
  have hkc : Nat.card θ.ker * c = m := by nlinarith
  calc Nat.card θ.ker ≤ Nat.card θ.ker * c := Nat.le_mul_of_pos_right _ hcpos
    _ = m := hkc

variable {G : Type} [Group G] [Finite G]

private theorem fz59_card_Z2xSigma4 : Nat.card FzZ2xSigma4 = 48 := by
  rw [Nat.card_prod]
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial, ZMod.card]

theorem fz59_card_N2
    [IsSimpleGroup G] {t : G} {L S : Subgroup G}
    {x₁ x₂ lam rho tau : G} (hr4 : FzAssumptionII G) (hctx : Ctx t L S x₁ x₂ lam rho tau)
    (hK : Nat.card (twoCore t) = 2) : Nat.card ↥(fzN2 t x₁ x₂) = 2 ^ 9 * 3 := by
  obtain ⟨f, hf, hker⟩ := fzl_35b G t L S x₁ x₂ lam rho tau hr4 hctx hK
  have hW_le_N2 : ctxW t x₁ x₂ ≤ fzN2 t x₁ x₂ := Subgroup.le_normalizer
  have hWker : Nat.card f.ker = 32 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW_le_N2).toEquiv]
    exact fzl_card_W hctx hK
  have h1 := Subgroup.card_ker_mul_card_of_surjective hf
  rw [hWker, fz59_card_Z2xSigma4] at h1
  omega

private theorem fz59_N2_le_normalizer_Z {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}
    (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 2) :
    fzN2 t x₁ x₂ ≤ normalizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨fun hz => fzl_conj_Z h hK hn hz, fun hz => ?_⟩
  have := fzl_conj_Z h hK ((fzN2 t x₁ x₂).inv_mem hn) hz
  simpa [mul_assoc] using this

theorem fz59_cz_of_card {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}
    (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 2)
    (hN2 : Nat.card ↥(fzN2 t x₁ x₂) = 2 ^ 9 * 3) (hR : Nat.card (fzR t x₁ x₂) = 2 ^ 8) :
    ∀ n ∈ fzN2 t x₁ x₂, (∀ z ∈ fourGrp x₁ x₂, n * z * n⁻¹ = z) → n ∈ fzR t x₁ x₂ := by
  intro n hn hnz
  let θ : ↥(fzN2 t x₁ x₂) →* MulAut ↥(fourGrp x₁ x₂) :=
    (Subgroup.normalizerMonoidHom (fourGrp x₁ x₂)).comp
      (Subgroup.inclusion (fz59_N2_le_normalizer_Z h hK))
  have hθ : ∀ (m : ↥(fzN2 t x₁ x₂)) (z : ↥(fourGrp x₁ x₂)),
      ((θ m z : ↥(fourGrp x₁ x₂)) : G) = (m : G) * z * (m : G)⁻¹ := fun m z => rfl
  have hθker : ∀ m : ↥(fzN2 t x₁ x₂),
      m ∈ θ.ker ↔ ∀ z ∈ fourGrp x₁ x₂, (m : G) * z * (m : G)⁻¹ = z := by
    intro m
    rw [MonoidHom.mem_ker]
    constructor
    · intro h1 z hz
      have := congrArg
        (fun φ : MulAut ↥(fourGrp x₁ x₂) => ((φ ⟨z, hz⟩ : ↥(fourGrp x₁ x₂)) : G)) h1
      simpa [hθ] using this
    · intro h1
      ext z
      rw [hθ]
      exact h1 z z.2
  have hz1mem : x₁ ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hz1ne : x₁ ^ 2 ≠ 1 := (fzl_z1_ne_z2 h).2.1
  have hrho := fzl_rho_Z h
  have hlam := fzl_lam_Z h
  let a : ↥(fzN2 t x₁ x₂) := ⟨rho, hrho.1⟩
  let b : ↥(fzN2 t x₁ x₂) := ⟨lam, hlam.1⟩
  have ha3 : θ a ^ 3 = 1 := by
    rw [← map_pow]
    have : a ^ 3 = 1 := Subtype.ext hrho.2.2.1
    rw [this, map_one]
  have hb2 : θ b ^ 2 = 1 := by
    rw [← map_pow]
    have : b ^ 2 = 1 := Subtype.ext hlam.2.2.1
    rw [this, map_one]
  have ha1 : θ a ≠ 1 := by
    intro h1
    have h2 := (hθker a).mp (by rw [MonoidHom.mem_ker]; exact h1) (x₁ ^ 2) hz1mem
    exact hrho.2.2.2 (x₁ ^ 2) hz1mem hz1ne h2
  have hb1 : θ b ≠ 1 := by
    intro h1
    have h2 := (hθker b).mp (by rw [MonoidHom.mem_ker]; exact h1) (x₁ ^ 2) hz1mem
    have h3 : lam * x₁ ^ 2 * lam⁻¹ = x₂ ^ 2 := hlam.2.2.2.1
    exact (fzl_z1_ne_z2 h).1 (h2.symm.trans h3)
  have hcard : Nat.card θ.ker ≤ 2 ^ 8 :=
    fz59_card_ker_le θ ha3 ha1 hb2 hb1 (m := 2 ^ 8) (by rw [hN2]; norm_num) (by norm_num)
  have hle : fzR t x₁ x₂ ≤ fzN2 t x₁ x₂ := fzl_R_le_N2 t x₁ x₂
  have hker_le : (fzR t x₁ x₂).subgroupOf (fzN2 t x₁ x₂) ≤ θ.ker := by
    intro r hr
    rw [hθker]
    exact fzl_R_Z h hK r (Subgroup.mem_subgroupOf.mp hr)
  have hRcard : Nat.card ((fzR t x₁ x₂).subgroupOf (fzN2 t x₁ x₂)) = 2 ^ 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    exact hR
  have heq : (fzR t x₁ x₂).subgroupOf (fzN2 t x₁ x₂) = θ.ker :=
    Subgroup.eq_of_le_of_card_ge hker_le (by rw [hRcard]; exact hcard)
  have hmem : (⟨n, hn⟩ : ↥(fzN2 t x₁ x₂)) ∈ θ.ker := (hθker _).mpr hnz
  rw [← heq] at hmem
  exact Subgroup.mem_subgroupOf.mp hmem

theorem fz59_cz
    [IsSimpleGroup G] {t : G} {L S T₂ : Subgroup G}
    {x₁ x₂ lam rho tau : G} (hr4 : FzAssumptionII G) (hctx : Ctx t L S x₁ x₂ lam rho tau)
    (hK : Nat.card (twoCore t) = 2) (hT : IsFzT2 t x₁ x₂ S T₂) :
    ∀ n ∈ fzN2 t x₁ x₂, (∀ z ∈ fourGrp x₁ x₂, n * z * n⁻¹ = z) → n ∈ fzR t x₁ x₂ :=
  fz59_cz_of_card hctx hK (fz59_card_N2 hr4 hctx hK)
    (fz37R_of_35b fzl_35b G t L S T₂ x₁ x₂ lam rho tau hr4 hctx hK hT).1

end CentZ

theorem fz59_base_of_ctx
    (hEven : Fz59Even) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] {t : G} {L S T₂ : Subgroup G} {x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ : G}
    (hr4 : FzAssumptionII G) (hctx : Ctx t L S x₁ x₂ lam rho tau)
    (hK : Nat.card (twoCore t) = 2) (hT : IsFzT2 t x₁ x₂ S T₂) (hns : ¬ FzSylow T₂)
    (hsh : FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂) (hbd : ¬ 2 ^ 11 ∣ Nat.card G) :
    Fz59Base t tau lam rho x₁ x₂ a₁₂ a₂₂ a₃₂ T₂ where
  str := fzl59f_str hr4 hctx hK hT
  shape := hsh
  T2_le := hT.le_N2
  T2_p := hT.isPGroup
  rho_N2 := hctx.rho_normalizes
  N2_nrm_R := fzl_R_normal t x₁ x₂
  cz := fz59_cz hr4 hctx hK hT
  cent2 := fz59_cent2 hctx hK
  fus := fun h44 e he => fz59Fus_holds G t L S x₁ x₂ lam rho tau hr4 hctx hK h44 e he
  bound := hbd
  even := hEven G t L S T₂ x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ hr4 hctx hK hT hns hsh

end CFSG.OddStandard.SmallF3.FritzII
