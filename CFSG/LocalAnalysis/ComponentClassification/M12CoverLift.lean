module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverLiftClasses
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverSylowSplit
public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasASplit
public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasBComplementLifting

public section

namespace CFSG.ComponentClassification.M12Cover

open CFSG.Blueprint

variable {L : Type*} [Group L] {t : L}

private theorem eq_or_eq_mul_of_map_eq {M : Type*} [Group M] {π : L →* M} (ht : orderOf t = 2)
    (hker : π.ker = Subgroup.zpowers t) {v w : L} (h : π w = π v) : w = v ∨ w = v * t := by
  have hmem : v⁻¹ * w ∈ Subgroup.zpowers t := by
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  rcases eq_one_or_eq_of_mem_zpowers ht hmem with h1 | h1
  · left
    rw [inv_mul_eq_one] at h1
    exact h1.symm
  · right
    rw [← h1]
    group

private theorem exists_conj_of_map_eq_conj {M : Type*} [Group M] {π : L →* M}
    (hπ : Function.Surjective π) {v : L} {g T : M} (hv : g * T * g⁻¹ = π v) :
    ∃ k u : L, π u = T ∧ k * u * k⁻¹ = v := by
  obtain ⟨k, rfl⟩ := hπ g
  refine ⟨k, k⁻¹ * v * k, ?_, by group⟩
  rw [map_mul, map_mul, map_inv, ← hv]
  group

private theorem orderOf_conj_eq (k u : L) : orderOf (k * u * k⁻¹) = orderOf u := by
  rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]

private theorem orderOf_eq_four_of_sq (ht : orderOf t = 2) {w : L} (hw : w ^ 2 = t) :
    orderOf w = 4 := by
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    exact absurd ht (by norm_num)
  have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := w) (by rw [pow_one, hw]; exact ht1)
    (by rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, hw, ← ht, pow_orderOf_eq_one])
  rw [h]
  norm_num

theorem orderOf_lift_elemR [Finite L] (ht : orderOf t = 2) (htZ : t ∈ Subgroup.center L)
    (π : L →* NativeSporadic.M12) (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.zpowers t) {u : L} (hu : π u = elemR) : orderOf u = 2 := by
  obtain ⟨-, hDD, -, hz2, hzc, -, hW, hWD, -, hr1, -, -, hWsq, -, ⟨P, hP⟩, hinv, -, hh⟩ :=
    ctss_m12_pinned_central_involution_fusion_for_fixed_section.2.2.2.2.2.1
  have hrW : elemR ∈ fusionW := by
    rw [hW]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  have hrD : elemR ∈ fixedD := hWD hrW
  have hr2 : orderOf elemR = 2 := orderOf_eq_prime (hWsq _ hrW) hr1
  refine (CentralCover.central_double_cover_splits_over_perfect_factor_from_involution_fusion π
    hπ hker ht htZ (Subgroup.isPerfect_iff.2 hDD) P ?_ hrD ?_ hzc hz2 ⟨elemH, hh⟩).2.2 u
    (hu ▸ hrD) (hu ▸ hr2)
  · intro w hw
    rw [hP, Subgroup.mem_subgroupOf] at hw
    exact Subtype.ext (by simpa using hWsq _ hw)
  · intro q hq hq2
    obtain ⟨c, hc, rfl⟩ := hinv q hq hq2
    exact ⟨c, hc, rfl⟩

theorem orderOf_lift_of_fixedCount_four [Finite L] (ht : orderOf t = 2)
    (htZ : t ∈ Subgroup.center L) (π : L →* NativeSporadic.M12) (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.zpowers t) {v : L} (hv2 : orderOf (π v) = 2)
    (hv4 : fixedCount (π v) = 4) : orderOf v = 2 := by
  obtain ⟨g, hg⟩ := conj_elemR_of_fixedCount_four (π v) hv2 hv4
  obtain ⟨k, u, hu, rfl⟩ := exists_conj_of_map_eq_conj hπ hg
  rw [orderOf_conj_eq]
  exact orderOf_lift_elemR ht htZ π hπ hker hu

theorem exists_isComplement'_of_forall_lift [Finite L] (ht : orderOf t = 2)
    (htZ : t ∈ Subgroup.center L) (π : L →* NativeSporadic.M12) (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.zpowers t)
    (hall : ∀ e : L, orderOf (π e) = 2 → orderOf e = 2) :
    ∃ B : Subgroup L, Subgroup.IsComplement' (Subgroup.zpowers t) B := by
  set S' : Subgroup NativeSporadic.M12 := S.subgroupOf NativeSporadic.M12
  set E : Subgroup L := S'.comap π with hE
  set ρ : E →* S' := π.subgroupComap S'
  have hπt : π t = 1 := by
    have h : t ∈ π.ker := hker ▸ Subgroup.mem_zpowers t
    exact h
  have htE : t ∈ E := by
    change π t ∈ S'
    rw [hπt]
    exact one_mem _
  set tE : E := ⟨t, htE⟩
  have htE2 : orderOf tE = 2 := (Subgroup.orderOf_coe tE).symm.trans ht
  have htEZ : tE ∈ Subgroup.center E :=
    Subgroup.mem_center_iff.2 fun g => Subtype.ext (Subgroup.mem_center_iff.1 htZ g)
  have hkerρ : ρ.ker = Subgroup.zpowers tE := by
    ext e
    rw [MonoidHom.mem_ker]
    constructor
    · intro he
      have hπe : (e : L) ∈ π.ker := MonoidHom.mem_ker.2 (congrArg Subtype.val he)
      rw [hker] at hπe
      rcases eq_one_or_eq_of_mem_zpowers ht hπe with h | h
      · rw [show e = 1 from Subtype.ext h]
        exact one_mem _
      · rw [show e = tE from Subtype.ext h]
        exact Subgroup.mem_zpowers tE
    · intro he
      rcases eq_one_or_eq_of_mem_zpowers htE2 he with rfl | rfl
      · exact map_one ρ
      · exact Subtype.ext hπt
  have hinv : ∀ e : E, orderOf (ρ e) = 2 → orderOf e = 2 := by
    intro e he
    rw [← Subgroup.orderOf_coe] at he ⊢
    exact hall e he
  obtain ⟨σ, hσ⟩ := splits_of_involution_lifts_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe S_le_M12) ρ (π.subgroupComap_surjective S' hπ) htE2 htEZ
    hkerρ hinv
  have hπσ : ∀ q : S', π (σ q : L) = q := fun q => congrArg Subtype.val (hσ q)
  set K : Subgroup L := (E.subtype.comp σ).range
  have hNK : Subgroup.zpowers t ⊓ K = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxN, q, rfl⟩
    have h1 : π (σ q : L) = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      exact hxN
    have hq : q = 1 := Subtype.ext ((hπσ q).symm.trans h1)
    rw [Subgroup.mem_bot, hq, map_one]
  have hsup : Subgroup.zpowers t ⊔ K = E := by
    apply le_antisymm
    · refine sup_le (Subgroup.zpowers_le.2 htE) ?_
      rintro _ ⟨q, rfl⟩
      exact (σ q).2
    · intro x hx
      set y : L := (σ (ρ ⟨x, hx⟩) : L) with hy
      have hmem : x * y⁻¹ ∈ Subgroup.zpowers t := by
        rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hy, hπσ]
        exact mul_inv_cancel (π x)
      have hyK : y ∈ K := ⟨ρ ⟨x, hx⟩, rfl⟩
      have hx' : x = x * y⁻¹ * y := by group
      rw [hx']
      exact mul_mem (Subgroup.mem_sup_left hmem) (Subgroup.mem_sup_right hyK)
  have hidx : S'.index = 1485 := relIndex_S_M12
  have hcop : Nat.Coprime E.index (Nat.card (Subgroup.zpowers t)) := by
    rw [hE, Subgroup.index_comap_of_surjective S' hπ, hidx, Nat.card_zpowers, ht]
    norm_num
  have : (Subgroup.zpowers t).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.2 htZ)
  obtain ⟨B, -, -, hB⟩ :=
    CentralCover.abelian_normal_coprime_index_complement_lifting hcop hNK hsup
  exact ⟨B, hB⟩

theorem not_isComplement'_of_perfect (hL : commutator L = ⊤) (ht : orderOf t = 2)
    (B : Subgroup L) (hB : Subgroup.IsComplement' (Subgroup.zpowers t) B) : False := by
  have hidx : B.index = 2 := by rw [hB.index_eq_card, Nat.card_zpowers, ht]
  have hcomm : commutator L ≤ B := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [commutatorElement_def, Subgroup.mul_mem_iff_of_index_two hidx,
      Subgroup.mul_mem_iff_of_index_two hidx, Subgroup.mul_mem_iff_of_index_two hidx,
      inv_mem_iff, inv_mem_iff]
    tauto
  rw [hL, top_le_iff] at hcomm
  have htB : t ∈ B := hcomm ▸ Subgroup.mem_top t
  have h1 : t = 1 := Subgroup.disjoint_def.1 hB.disjoint (Subgroup.mem_zpowers t) htB
  rw [h1, orderOf_one] at ht
  exact absurd ht (by norm_num)

theorem sq_lift_elemZ [Finite L] (hL : commutator L = ⊤) (ht : orderOf t = 2)
    (htZ : t ∈ Subgroup.center L) (π : L →* NativeSporadic.M12) (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.zpowers t) {v : L} (hv : π v = elemZ) : v ^ 2 = t := by
  have hz2 : elemZ ^ 2 = 1 := by rw [← orderOf_elemZ, pow_orderOf_eq_one]
  have hz1 : elemZ ≠ 1 := by
    intro h
    have := orderOf_elemZ
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  have hmem : v ^ 2 ∈ Subgroup.zpowers t := by
    rw [← hker, MonoidHom.mem_ker, map_pow, hv, hz2]
  rcases eq_one_or_eq_of_mem_zpowers ht hmem with h1 | h1
  · exfalso
    have ht2 : t ^ 2 = 1 := by rw [← ht, pow_orderOf_eq_one]
    obtain ⟨B, hB⟩ := exists_isComplement'_of_forall_lift ht htZ π hπ hker fun e he => by
      rcases m12_involution_conj_elemR_or_elemZ (π e) he with ⟨g, hg⟩ | ⟨g, hg⟩
      · obtain ⟨k, u, hu, rfl⟩ := exists_conj_of_map_eq_conj hπ hg
        rw [orderOf_conj_eq]
        exact orderOf_lift_elemR ht htZ π hπ hker hu
      · obtain ⟨k, u, hu, rfl⟩ := exists_conj_of_map_eq_conj hπ hg
        rw [orderOf_conj_eq]
        have hu2 : u ^ 2 = 1 := by
          rcases eq_or_eq_mul_of_map_eq ht hker (hu.trans hv.symm) with rfl | rfl
          · exact h1
          · rw [(show Commute v t from Subgroup.mem_center_iff.1 htZ v).mul_pow, h1, ht2,
              one_mul]
        refine orderOf_eq_prime hu2 fun hu1 => hz1 ?_
        rw [← hu, hu1, map_one]
    exact not_isComplement'_of_perfect hL ht B hB
  · exact h1

theorem m12_double_cover_involution_lift_orders {L : Type*} [Group L] [Finite L]
    (hLq : CFSG.Assembly.IsQuasisimple L) {t : L} (ht : orderOf t = 2)
    (hZ : Subgroup.center L = Subgroup.zpowers t)
    (π : L →* CFSG.Blueprint.NativeSporadic.M12) (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.zpowers t) :
    (∀ q : CFSG.Blueprint.NativeSporadic.M12, orderOf q = 2 →
        fixedCount q = 4 ∨ fixedCount q = 0) ∧
    (∀ v : L, orderOf (π v) = 2 → fixedCount (π v) = 4 → orderOf v = 2) ∧
    (∀ v : L, orderOf (π v) = 2 → fixedCount (π v) = 0 → v ^ 2 = t ∧ orderOf v = 4) := by
  have htZ : t ∈ Subgroup.center L := hZ ▸ Subgroup.mem_zpowers t
  refine ⟨fixedCount_of_orderOf_eq_two, fun v hv2 hv4 =>
    orderOf_lift_of_fixedCount_four ht htZ π hπ hker hv2 hv4, fun v hv2 hv0 => ?_⟩
  obtain ⟨g, hg⟩ := conj_elemZ_of_fixedCount_zero (π v) hv2 hv0
  obtain ⟨k, u, hu, rfl⟩ := exists_conj_of_map_eq_conj hπ hg
  have hsq : (k * u * k⁻¹) ^ 2 = t := by
    rw [conj_pow, sq_lift_elemZ hLq.1 ht htZ π hπ hker hu, Subgroup.mem_center_iff.1 htZ k,
      mul_inv_cancel_right]
  exact ⟨hsq, orderOf_eq_four_of_sq ht hsq⟩

end CFSG.ComponentClassification.M12Cover
