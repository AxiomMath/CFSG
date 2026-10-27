module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S3c2a

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup
open CFSG.OddStandard.SmallF3.HarrisU33.L34

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


theorem pCoreOf_eq_of_normal_max {p : ℕ} (H U : Subgroup G) (hUH : U ≤ H)
    (hnorm : ∀ h ∈ H, ∀ u ∈ U, h * u * h⁻¹ ∈ U) (hU : IsPGroup p U)
    (hmax : ∀ R : Subgroup G, R ≤ H → (∀ h ∈ H, ∀ r ∈ R, h * r * h⁻¹ ∈ R) →
      IsPGroup p R → R ≤ U) :
    CFSG.Open.pCoreOf p H = U := by
  apply le_antisymm
  ·
    have hcore : CFSG.pCore p ↥H ≤ U.subgroupOf H := by
      change sSup {K : Subgroup ↥H | K.Normal ∧ IsPGroup p K} ≤ U.subgroupOf H
      refine sSup_le ?_
      rintro K ⟨hKn, hKp⟩ x hx
      have hK'map : K.map H.subtype ≤ U := by
        refine hmax (K.map H.subtype) (Subgroup.map_subtype_le K) ?_ (hKp.map H.subtype)
        intro h hh r hr
        rw [Subgroup.mem_map] at hr ⊢
        obtain ⟨k, hk, rfl⟩ := hr
        exact ⟨⟨h, hh⟩ * k * ⟨h, hh⟩⁻¹, hKn.conj_mem k hk ⟨h, hh⟩, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr (hK'map (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩))
    calc CFSG.Open.pCoreOf p H = (CFSG.pCore p ↥H).map H.subtype := rfl
      _ ≤ (U.subgroupOf H).map H.subtype := Subgroup.map_mono hcore
      _ = U := Subgroup.map_subgroupOf_eq_of_le hUH
  ·
    have hUcore : U.subgroupOf H ≤ CFSG.pCore p ↥H := by
      change U.subgroupOf H ≤ sSup {K : Subgroup ↥H | K.Normal ∧ IsPGroup p K}
      refine le_sSup ⟨?_, ?_⟩
      · rw [Subgroup.normal_subgroupOf_iff_le_normalizer hUH]
        intro u hu
        rw [Subgroup.mem_normalizer_iff]
        intro h
        refine ⟨fun hh => hnorm u hu h hh, ?_⟩
        intro hh
        have h' := hnorm u⁻¹ (inv_mem hu) (u * h * u⁻¹) hh
        rwa [show u⁻¹ * (u * h * u⁻¹) * (u⁻¹)⁻¹ = h by group] at h'
      · change IsPGroup p (U.comap H.subtype)
        exact hU.comap_subtype
    calc U = (U.subgroupOf H).map H.subtype := (Subgroup.map_subgroupOf_eq_of_le hUH).symm
      _ ≤ (CFSG.pCore p ↥H).map H.subtype := Subgroup.map_mono hUcore
      _ = CFSG.Open.pCoreOf p H := rfl

theorem pCoreOf_eq_ctxPL (ha : Ctx4A t L S x₁ x₂ lam rho tau) (σ : Sig4 t tau x₁ x₂) :
    CFSG.Open.pCoreOf 2 (ctxLO t tau x₁ x₂) = ctxPL t tau x₁ x₂ := by
  refine pCoreOf_eq_of_normal_max (p := 2) (ctxLO t tau x₁ x₂) (ctxPL t tau x₁ x₂)
    (normal_ctxPL ha).1 (normal_ctxPL ha).2
    (IsPGroup.of_card (card_ctxPL_sig ha σ)) ?_
  intro R hRL hRnorm hRp r hr
  rw [mem_ctxPL_iff ha σ (hRL hr)]
  let L1 := ctxLO t tau x₁ x₂
  let R' : Subgroup ↥L1 := R.subgroupOf L1
  let N' : Subgroup (Equiv.Perm (Fin 4)) := R'.map σ.φ
  have hR'normal : R'.Normal := by
    show (R.subgroupOf (ctxLO t tau x₁ x₂)).Normal
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hRL]
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hRnorm x hx y hy, ?_⟩
    intro hy
    have h' := hRnorm x⁻¹ (inv_mem hx) (x * y * x⁻¹) hy
    rwa [show x⁻¹ * (x * y * x⁻¹) * (x⁻¹)⁻¹ = y by group] at h'
  have hN'normal : N'.Normal := Subgroup.Normal.map hR'normal σ.φ σ.surj
  have hno3 : ∀ c ∈ N', c ^ 3 = 1 → c = 1 := by
    intro c hcN hc3
    rw [Subgroup.mem_map] at hcN
    obtain ⟨y, hy, rfl⟩ := hcN
    have hyR : (y : G) ∈ R := Subgroup.mem_subgroupOf.mp hy
    obtain ⟨k, hk⟩ := hRp ⟨(y : G), hyR⟩
    have hyk : y ^ 2 ^ k = 1 := by
      apply Subtype.ext
      have hv := congrArg Subtype.val hk
      simpa [Subgroup.coe_pow] using hv
    have hcy : (σ.φ y) ^ 2 ^ k = 1 := by
      rw [← map_pow, hyk, map_one]
    have hdvd3 : orderOf (σ.φ y) ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hc3
    have hdvd2 : orderOf (σ.φ y) ∣ 2 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hcy
    have hcop : Nat.Coprime 3 (2 ^ k) := by
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · norm_num
      · rw [Nat.coprime_pow_right_iff hk0]; norm_num
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvd3 hdvd2)
  have hNle : N' ≤ klein4 := by
    haveI : N'.Normal := hN'normal
    exact normal_le_klein4 N' hno3
  exact hNle (show σ.φ ⟨r, hRL hr⟩ ∈ N' from
    Subgroup.mem_map.mpr ⟨⟨r, hRL hr⟩, Subgroup.mem_subgroupOf.mpr hr, rfl⟩)

theorem LO_eq_sup (ha : Ctx4A t L S x₁ x₂ lam rho tau) (σ : Sig4 t tau x₁ x₂) :
    ctxLO t tau x₁ x₂ = ctxPL t tau x₁ x₂ ⊔ closure {rho, lam * t} := by
  have h3 : rho ^ 3 = 1 := by rw [← ha.ord_rho]; exact pow_orderOf_eq_one rho
  have ha3 : rho * rho * rho ∈ ctxPL t tau x₁ x₂ := by
    rw [show rho * rho * rho = rho ^ 3 from (pow_three' rho).symm, h3]
    exact one_mem _
  have h6 : Nat.card (ctxLO t tau x₁ x₂) = 6 * Nat.card (ctxPL t tau x₁ x₂) := by
    rw [card_LO_of_sig ha σ, card_ctxPL_sig ha σ]
    norm_num
  exact (sup_closure_eq_of_index_six (ctxLO t tau x₁ x₂) (ctxPL t tau x₁ x₂)
    (normal_ctxPL ha).1 (normal_ctxPL ha).2 h6 (rho_mem_LO ha) (lamt_mem_LO ha)
    ha3 (rho_not_mem_ctxPL ha) (lamt_sq_mem_ctxPL ha) (lamt_not_mem_ctxPL ha)).symm

theorem syl_ctxPL (ha : Ctx4A t L S x₁ x₂ lam rho tau) (σ : Sig4 t tau x₁ x₂) :
    IsSylowIn 2 (ctxPL t tau x₁ x₂ ⊔ zpowers (lam * t)) (ctxLO t tau x₁ x₂) := by
  let K := ctxPL t tau x₁ x₂ ⊔ zpowers (lam * t)
  let L1 := ctxLO t tau x₁ x₂
  have hbN : ∀ n ∈ ctxPL t tau x₁ x₂, (lam * t) * n * (lam * t)⁻¹ ∈ ctxPL t tau x₁ x₂ :=
    fun n hn => (normal_ctxPL ha).2 (lam * t) (lamt_mem_LO ha) n hn
  have hKle : K ≤ L1 :=
    sup_le (normal_ctxPL ha).1 (zpowers_le.mpr (lamt_mem_LO ha))
  have hcardK : Nat.card K = 2 ^ 11 := by
    have h := card_sup_zpowers_of_sq (ctxPL t tau x₁ x₂) hbN
      (lamt_sq_mem_ctxPL ha) (lamt_not_mem_ctxPL ha)
    rw [card_ctxPL_sig ha σ] at h
    exact h.trans (by norm_num)
  refine ⟨hKle, IsPGroup.of_card hcardK, ?_⟩
  intro hdvd
  have hcardL : Nat.card L1 = 3 * 2 ^ 11 := card_LO_of_sig ha σ
  have hrel := Subgroup.relIndex_mul_card (H := K) (K := L1)
  rw [inf_eq_left.mpr hKle] at hrel
  rw [hcardK, hcardL] at hrel
  have hidx : K.relIndex L1 = 3 := Nat.mul_right_cancel (by norm_num) hrel
  rw [hidx] at hdvd
  exact (by norm_num : ¬ 2 ∣ 3) hdvd

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
