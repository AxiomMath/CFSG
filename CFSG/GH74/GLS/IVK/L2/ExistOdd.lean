module

public import CFSG.GH74.GLS.IVK.L2.DihedralAux2
public import CFSG.GH74.GLS.IVK.L2.FixedCentralizer
public import CFSG.GH74.GLS.IVK.L2.FieldProj
public import CFSG.GH74.GLS.IVK.L2.ExistArith

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.GorensteinWalter

section Orders

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K] (e : K ≃* L2 F)

omit [Finite K] in
theorem card_mulAut_eq :
    Nat.card (MulAut K) = Nat.card (innDiagSub e) * Nat.card (fieldAutSub e) := by
  have hker : (fieldProj e).ker = innDiagSub e := by
    ext x
    rw [MonoidHom.mem_ker, mem_innDiagSub_iff]
  have hrange : (fieldProj e).range = ⊤ := by
    rw [MonoidHom.range_eq_top]
    intro σ
    exact ⟨fieldAutHom e σ, fieldProj_fieldAutHom e σ⟩
  have h1 := Subgroup.card_ker_mul_card_range (fieldProj e)
  rw [hker, hrange, Subgroup.card_top] at h1
  rw [← h1]
  congr 1
  exact Nat.card_congr (MonoidHom.ofInjective (fieldAutHom_injective e)).toEquiv

omit [Finite K] in
theorem card_innDiagSub_q (hF : L2Field F) :
    Nat.card (innDiagSub e) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  rw [card_innDiagSub e hF, card_eq_of_L2Field e hF]
  have hq := hF.1
  have h2 : 2 ∣ Nat.card F * (Nat.card F ^ 2 - 1) := by
    have : Odd (Nat.card F ^ 2) := hq.pow
    have := Nat.odd_iff.mp this
    exact Dvd.dvd.mul_left (by omega) _
  exact Nat.mul_div_cancel' h2

end Orders

section OddCase

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K] (e : K ≃* L2 F)

theorem exists_notation_of_odd (hF : L2Field F) (hodd : Odd (Nat.card (fieldAutSub e))) :
    Nonempty (L2Notation e) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcyc : IsCyclic ↥(fieldAutSub e) := isCyclic_fieldAutSub e
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := ↥(fieldAutSub e))
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : MulAut K, g₀ = (γ : MulAut K) := ⟨_, rfl⟩
  have hg₀F : g₀ ∈ fieldAutSub e := hg₀ ▸ γ.2
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀ : F ≃+* F, fieldAutHom e σ₀ = g₀ := hg₀F
  have hFpow : ∀ φ ∈ fieldAutSub e, ∃ k : ℤ, φ = g₀ ^ k := by
    intro φ hφ
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hγ ⟨φ, hφ⟩)
    exact ⟨k, by rw [hg₀]; exact (congrArg Subtype.val hk).symm⟩
  set A : Subgroup (MulAut K) := centralizer ({g₀} : Set (MulAut K)) ⊓ innDiagSub e with hA
  have hAcomm : ∀ x ∈ A, ∀ φ ∈ fieldAutSub e, x * φ = φ * x := by
    intro x hx φ hφ
    obtain ⟨k, rfl⟩ := hFpow φ hφ
    have hx0 : x * g₀ = g₀ * x := Subgroup.mem_centralizer_singleton_iff.mp hx.1
    exact ((Commute.zpow_right (show Commute x g₀ from hx0) k))
  have hFo : Nat.card (fieldAutSub e) = orderOf σ₀ := by
    have h1 : orderOf γ = Nat.card ↥(fieldAutSub e) := orderOf_eq_card_of_forall_mem_zpowers hγ
    have h2 : orderOf g₀ = orderOf γ := by rw [hg₀]; exact Subgroup.orderOf_coe γ
    rw [← h1, ← h2, ← hσ₀]
    exact orderOf_injective (fieldAutHom e) (fieldAutHom_injective e) σ₀
  have hσodd : Odd (orderOf σ₀) := hFo ▸ hodd
  have hq₁ : Nat.card (fixedField σ₀) ^ orderOf σ₀ = Nat.card F := fixedField_card_pow σ₀
  have hq₁odd : Odd (Nat.card (fixedField σ₀)) := odd_card_fixedField σ₀ hF.1
  have hq₁1 : 1 < Nat.card (fixedField σ₀) := one_lt_card_fixedField σ₀
  have hAcard : Nat.card A =
      Nat.card (fixedField σ₀) * (Nat.card (fixedField σ₀) ^ 2 - 1) := by
    rw [hA, ← hσ₀]
    exact card_centralizer_fieldAut e σ₀
  have hAle : A ≤ innDiagSub e := inf_le_right
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have hqpos : 0 < Nat.card F := Nat.card_pos
  have hq2 : Nat.card F ^ 2 - 1 ≠ 0 := by
    have := hF.2
    have : 1 < Nat.card F ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  have hv2 : (Nat.card A).factorization 2 = (Nat.card (MulAut K)).factorization 2 := by
    rw [Nat.factorization_def _ Nat.prime_two, Nat.factorization_def _ Nat.prime_two, hAcard,
      card_mulAut_eq e, card_innDiagSub_q e hF]
    have h1 := padicValNat_card_odd hq₁odd hq₁1 hσodd
    rw [hq₁] at h1
    rw [← h1, padicValNat.mul (Nat.mul_ne_zero hqpos.ne' hq2) (Nat.card_pos.ne'), hFo]
    have : padicValNat 2 (orderOf σ₀) = 0 := by
      apply padicValNat.eq_zero_of_not_dvd
      exact hσodd.not_two_dvd_nat
    rw [this, add_zero]
  obtain ⟨T₀'⟩ : Nonempty (Sylow 2 ↥A) := Sylow.nonempty
  obtain ⟨T₀, hT₀⟩ : ∃ T₀ : Subgroup (MulAut K), T₀ = (T₀' : Subgroup ↥A).map A.subtype := ⟨_, rfl⟩
  have hT₀A : T₀ ≤ A := by
    rw [hT₀]; exact Subgroup.map_subtype_le _
  have hT₀card : Nat.card T₀ = 2 ^ (Nat.card (MulAut K)).factorization 2 := by
    rw [hT₀, Subgroup.card_map_of_injective A.subtype_injective, Sylow.card_eq_multiplicity T₀', hv2]
  obtain ⟨T, hT⟩ : ∃ T : Sylow 2 (MulAut K), (T : Subgroup (MulAut K)) = T₀ :=
    ⟨Sylow.ofCard T₀ hT₀card, rfl⟩
  have hTA : (T : Subgroup (MulAut K)) ≤ A := hT ▸ hT₀A
  have hTD : (T : Subgroup (MulAut K)) ≤ innDiagSub e := hTA.trans hAle
  have hTcard : Nat.card (T : Subgroup (MulAut K)) = 2 * 2 ^ (Nat.card K).factorization 2 := by
    rw [Sylow.card_eq_multiplicity T, card_mulAut_eq e, card_innDiagSub e hF]
    have hFne : Nat.card (fieldAutSub e) ≠ 0 := Nat.card_pos.ne'
    rw [Nat.factorization_mul (by omega) hFne, Nat.factorization_mul (by norm_num) hKpos.ne']
    simp only [Finsupp.add_apply]
    have h2 : (Nat.card (fieldAutSub e)).factorization 2 = 0 := by
      rw [Nat.factorization_def _ Nat.prime_two]
      apply padicValNat.eq_zero_of_not_dvd
      exact hodd.not_two_dvd_nat
    have h3 : (2 : ℕ).factorization 2 = 1 := by
      rw [Nat.factorization_def _ Nat.prime_two]; exact padicValNat_self
    rw [h2, h3]
    ring
  have hTnot : ¬ (T : Subgroup (MulAut K)) ≤ innAut K := by
    intro hle
    have hdvd : Nat.card (T : Subgroup (MulAut K)) ∣ Nat.card (innAut K) :=
      Subgroup.card_dvd_of_le hle
    rw [hTcard, card_innAut e] at hdvd
    have h1 : 2 ^ ((Nat.card K).factorization 2 + 1) ∣ Nat.card K := by
      rw [pow_succ, mul_comm]; exact hdvd
    have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hKpos.ne').mp h1
    omega
  obtain ⟨m, hm, ⟨φ⟩⟩ := dihedral_of_sylow_inf_innDiag e hF T
  have hTinf : (T : Subgroup (MulAut K)) ⊓ innDiagSub e = (T : Subgroup (MulAut K)) :=
    inf_eq_left.mpr hTD
  let φ' : ↥(T : Subgroup (MulAut K)) ≃* DihedralGroup (2 ^ m) :=
    (MulEquiv.subgroupCongr hTinf).symm.trans φ
  obtain ⟨t, htT, ht2, htI⟩ : ∃ t ∈ (T : Subgroup (MulAut K)), orderOf t = 2 ∧ t ∉ innAut K := by
    by_contra hcon
    push Not at hcon
    exact hTnot (DihedralAux.le_of_involutions_le (T : Subgroup (MulAut K)) (innAut K) φ' hcon)
  have hTcomm : ∀ x ∈ (T : Subgroup (MulAut K)), ∀ φ ∈ fieldAutSub e, x * φ = φ * x :=
    fun x hx φ hφ => hAcomm x (hTA hx) φ hφ
  refine ⟨{
    T := T
    t := t
    t_mem := htT
    t_order := ht2
    t_mem_diag := hTD htT
    t_not_mem_inn := htI
    T_inv := ?_
    R_cent := ?_
    F_odd_cent := ?_
    four_cent := ?_ }⟩
  · intro φ hφ
    exact Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr (fun x hx => hTcomm x hx φ hφ))
  · rintro f ⟨-, hfF⟩ hf2
    exfalso
    have := Subgroup.orderOf_dvd_natCard _ hfF
    rw [hf2] at this
    exact hodd.not_two_dvd_nat this
  · intro f hf _ x hx
    exact hTcomm x hx f hf
  · obtain ⟨m', hm', ⟨d⟩⟩ := dihedral_of_sylow_inf_innAut e hF T
    obtain ⟨V, hVle, hV⟩ := exists_kleinFour_le_of_dihedral_subgroup_mulEquiv _ hm' d
    have := hV
    have hEA : IsElementaryAbelian 2 ↥V :=
      { toIsMulCommutative := IsKleinFour.isMulCommutative
        exponent_dvd_p := by rw [hV.exponent_two] }
    refine ⟨V, hVle, ⟨hEA, hV.card_four⟩, ?_⟩
    intro φ hφ u hu
    exact (hTcomm u (hVle hu).1 φ hφ).symm

end OddCase

end CFSG.GH74.GLS.IVK
