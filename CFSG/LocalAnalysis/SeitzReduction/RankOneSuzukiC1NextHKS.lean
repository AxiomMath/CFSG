module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiC1NextStab
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiUEight

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace SzC1Next

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f a : ℕ} {t : G} {T : Subgroup G}
  {d : G} {V U U₁ : Subgroup G} {k : ℕ} {K : Type} [Field K] [Fintype K] [CharP K 2]
  {u v : G → K} {κ : K} (H : SzC1Next G L f a t T d V U U₁ k K u v κ)
include H

theorem normalizer_U_le_normalizer_szA₁ :
    normalizer (U : Set G) ≤ normalizer (szA₁ (szT₁ L T) : Set G) := fun n hn =>
  mem_normalizer_iff.mpr fun b => ⟨fun hb => H.stage.conj_mem_szA₁_of_normalizer H.mu hn hb,
    fun hb => by
      have := H.stage.conj_mem_szA₁_of_normalizer H.mu (inv_mem hn) hb
      rwa [show n⁻¹ * (n * b * n⁻¹) * n⁻¹⁻¹ = b by group] at this⟩

theorem v_eq_iff_szA₁ : ∀ x ∈ szA₁ (szT₁ L T), ∀ x' ∈ szA₁ (szT₁ L T),
    v x = v x' ↔ x⁻¹ * x' ∈ (⊥ : Subgroup G) := by
  intro x hx x' hx'
  rw [mem_bot, inv_mul_eq_one]
  refine ⟨fun hv => H.coords.inj _ (szA₁_le _ hx) _ (szA₁_le _ hx') ?_ hv, fun h => h ▸ rfl⟩
  rw [H.coords.u_eq_zero_of_mem_szA₁ H.stage.ha H.card_K' hx,
    H.coords.u_eq_zero_of_mem_szA₁ H.stage.ha H.card_K' hx']

noncomputable def betaA : normalizer (U : Set G) → AddAut K :=
  secAddAut H.normalizer_U_le_normalizer_szA₁ (SzRCoords2.le_normalizer_bot _)
    (H.coords.exists_v_eq H.stage.ha H.card_K') H.v_eq_iff_szA₁
    (fun _ hx _ hx' => H.coords.v_mul_szA₁ H.stage.ha H.card_K' hx hx')

theorem betaA_apply (n : normalizer (U : Set G)) {b : G} (hb : b ∈ szA₁ (szT₁ L T)) :
    H.betaA n (v b) = v ((n : G) * b * (n : G)⁻¹) :=
  secAddAut_apply _ _ _ _ _ n hb

noncomputable def betaT :
    normalizer (U : Set G) → AddAut K :=
  secAddAut (H.stage.normalizer_U_le_normalizer_T₁ H.card_K H.coords H.mu H.lam H.nu)
    H.normalizer_U_le_normalizer_szA₁
    (fun w => by
      obtain ⟨x, hx, hu, -⟩ := H.coords.surj w 0
      exact ⟨x, hx, hu⟩)
    (H.coords.u_eq_iff H.stage.ha H.card_K') (fun x hx x' hx' => (H.coords.mul x hx x' hx').1)

theorem betaT_apply
    (n : normalizer (U : Set G)) {y : G} (hy : y ∈ szT₁ L T) :
    H.betaT n (u y) = u ((n : G) * y * (n : G)⁻¹) :=
  secAddAut_apply _ _ _ _ _ n hy

theorem perm_eq
    (n : normalizer (U : Set G)) (s : K) : H.perm n s = H.betaA n s + H.perm n 0 := by
  conv_lhs => rw [← H.sec_X s]
  conv_rhs => rw [← H.sec_X s]
  rw [H.perm_apply n (H.sec_mem s), H.perm_zero n, conj_pow,
    H.betaA_apply n (H.stage.pow_mem_szA₁_V₁ H.card_K H.coords (H.sec_mem s))]

theorem betaA_pow
    (n : normalizer (U : Set G)) (x : K) :
    H.betaA n (x ^ (2 ^ (a + 1) + 1)) = H.betaT n x ^ (2 ^ (a + 1) + 1) := by
  obtain ⟨y, hy, hyu, -⟩ := H.coords.surj x 0
  have hny : (n : G) * y * (n : G)⁻¹ ∈ szT₁ L T :=
    (mem_normalizer_iff.mp (H.stage.normalizer_U_le_normalizer_T₁ H.card_K H.coords H.mu H.lam
      H.nu n.2) y).mp hy
  rw [← hyu, ← (H.coords.sq hy).2, H.betaA_apply n (H.coords.sq_mem_szA₁ H.stage.ha H.card_K' hy),
    H.betaT_apply n hy, ← conj_pow, (H.coords.sq hny).2]


section HKS


theorem exists_regular (hU : ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = U) :
    ∃ E : Subgroup (Equiv.Perm K), E ≤ H.perm.range ∧ (E.subgroupOf H.perm.range).Normal ∧
      (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ (∀ x ∈ E, x ^ 2 = 1) ∧ Nat.card E = 2 ^ f ∧
      (∀ β γ : K, ∃! e : E, (e : Equiv.Perm K) β = γ) ∧ ∀ e ∈ E, ∀ c, e c = e 0 + c := by
  have : IsSimpleGroup G := H.stage.start.setting.1
  have hf2 : 2 ≤ f := by have := H.stage.ha; rw [H.stage.hfa]; omega
  have hY : normalizer (U : Set G) ≠ ⊤ := by
    intro htop
    have hnorm : U.Normal := normalizer_eq_top_iff.mp htop
    rcases hnorm.eq_bot_or_eq_top with hbot | htop'
    · have hcard := H.stage.card_U
      rw [hbot, Subgroup.card_bot] at hcard
      have : 0 < (2 ^ f) ^ (k + 3) := by positivity
      omega
    · exact hU ⟨H.stage.isPGroup_U.toSylow (by rw [htop', Subgroup.index_top]; norm_num), rfl⟩
  have hcardK : Nat.card K = 2 ^ f := by rw [Nat.card_eq_fintype_card, H.card_K]
  obtain ⟨hodd, hdvd⟩ := H.perm_stabilizer
  rcases odd_stabilizer_two_transitive_kProper_of_dvd H.stage.start.setting.2.2.1 hY
    H.perm H.perm.range le_rfl (H.perm_two_transitive hU) (by omega) hcardK 0 hodd hdvd with
    ⟨E, hEN, hEnorm, hEab, hE2, hEcard, hreg⟩ | ⟨hf3, -, h168, hsimple, -⟩
  · refine ⟨E, hEN, hEnorm, hEab, hE2, hEcard, hreg, ?_⟩
    have hA2 : IsPGroup 2 E := IsPGroup.of_card hEcard
    have haff : ∀ x ∈ E, ∃ ℓ : K →+ K, ∀ c, x c = x 0 + ℓ c := by
      intro x hx
      obtain ⟨n, rfl⟩ := hEN hx
      exact H.perm_affine n
    set δn : normalizer (U : Set G) := ⟨d⁻¹, inv_mem H.stage.d_mem_normalizer_U⟩ with hδn
    have hδA : ∀ x ∈ E, (H.perm δn)⁻¹ * x * H.perm δn ∈ E := by
      intro x hx
      have hδN : (H.perm δn)⁻¹ ∈ H.perm.range := inv_mem ⟨δn, rfl⟩
      have := hEnorm.conj_mem ⟨x, hEN hx⟩ (mem_subgroupOf.mpr hx) ⟨_, hδN⟩
      rw [mem_subgroupOf] at this
      simpa using this
    exact SzC1.translation_of_affine H.card_K hf2 H.gen_mu hA2 haff H.perm_d_inv hδA
  · exfalso
    have ha1 : a = 1 := by have := H.stage.hfa; omega
    have hK8 : Nat.card K = 8 := by rw [hcardK, hf3]; norm_num
    have hθ : 2 ^ (a + 1) + 1 = 5 := by rw [ha1]; norm_num
    refine false_of_affine_card_range_eq_168 hK8 H.perm (Equiv.refl K) H.betaA
      (fun n => H.perm n 0) (fun n S => H.perm_eq n S) h168 hsimple
      (Or.inl fun n => ⟨H.betaT n, fun x => ?_⟩)
    have := H.betaA_pow n x
    rwa [hθ] at this

end HKS

end SzC1Next

end CFSG.SeitzReduction.RankOne
