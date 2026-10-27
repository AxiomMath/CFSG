module

public import CFSG.LargeExtraspecial.S3Two
public import CFSG.LargeExtraspecial.Types

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith
  CFSG.RankThree.OrthogonalInvolutions
open scoped commutatorElement

private theorem transvection_aux {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}
    (hq : q.polarBilin.Nondegenerate) {t : V ≃ₗ[ZMod 2] V}
    (ht : t ∈ TauCeti.QuadraticMap.orthogonalGroup q) {c : V} (hc : c ≠ 0)
    (hspan : commSpace t = ZMod 2 ∙ c) : t * t = 1 ∧ t c = c ∧ q c = 1 := by
  have hmem : ∀ v, ∃ a : ZMod 2, a • c = t v - v := fun v =>
    Submodule.mem_span_singleton.mp (hspan ▸ sub_mem_commSpace t v)
  have htc : t c = c := by
    obtain ⟨a, ha⟩ := hmem c
    rcases zmod2_cases a with rfl | rfl
    · rw [zero_smul, eq_comm, sub_eq_zero] at ha
      exact ha
    · exfalso
      rw [one_smul, eq_sub_iff_add_eq, add_self_vec (ZMod 2)] at ha
      exact hc (t.injective (by rw [← ha, map_zero]))
  have htt : t * t = 1 := by
    refine LinearEquiv.ext fun v => ?_
    obtain ⟨a, ha⟩ := hmem v
    have hv : t v = v + a • c := by rw [ha]; abel
    rw [LinearEquiv.mul_apply, hv, map_add, map_smul, htc, hv, add_assoc,
      ← two_smul (ZMod 2) (a • c), show (2 : ZMod 2) = 0 from rfl, zero_smul, add_zero,
      LinearEquiv.coe_one, id]
  refine ⟨htt, htc, ?_⟩
  rcases zmod2_cases (q c) with h0 | h1
  · exfalso
    apply hc
    refine hq.1 c fun v => ?_
    rw [polarBilin_apply_apply, polar_comm]
    obtain ⟨a, ha⟩ := hmem v
    rcases zmod2_cases a with rfl | rfl
    ·
      rw [zero_smul, eq_comm, sub_eq_zero] at ha
      have hfix : v ∈ fixSpace t := mem_fixSpace.mpr ha
      rw [fixSpace_eq_orthogonal_commSpace hq ht htt, hspan,
        LinearMap.BilinForm.mem_orthogonal_iff] at hfix
      have := hfix c (Submodule.mem_span_singleton_self c)
      rwa [polarBilin_apply_apply, polar_comm] at this
    ·
      rw [one_smul] at ha
      have hv : t v = v + c := by rw [ha]; abel
      have h := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup ht v
      rw [hv, map_add_eq, h0, add_zero] at h
      have h' : q v + polar q v c - q v = 0 := by rw [h, sub_self]
      rwa [add_sub_cancel_left] at h'
  · exact h1

namespace Setting

variable {G : Type*} [Group G] [Finite G] (S : Setting G)

theorem aschbacher_8_6 {x : G} (hxM : x ∈ S.M) (hdim : finrank (ZMod 2) (S.commQt x) = 1) :
    (∀ c ∈ S.commQt x, c ≠ 0 → S.q c = 1) ∧
      ∃ c ∈ S.QG, c ^ 2 = S.z ∧ ⁅zpowers x, S.QG⁆ = zpowers c := by
  set t := (S.ρ ⟨x, hxM⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) with ht
  have hcomm : S.commQt x = commSpace t := S.commQt_of_mem hxM
  have hne : S.commQt x ≠ ⊥ := fun h => by
    rw [h, finrank_bot] at hdim
    exact absurd hdim (by norm_num)
  obtain ⟨c₀, hc₀, hc₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hspan : S.commQt x = ZMod 2 ∙ c₀ := by
    refine (Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).mpr hc₀)
      ?_).symm
    rw [finrank_span_singleton hc₀0, hdim]
  obtain ⟨htt, -, hqc⟩ := transvection_aux S.q_nondegenerate (S.ρ_mem_O _) hc₀0
    (hcomm ▸ hspan)
  have hmem01 : ∀ v ∈ S.commQt x, v = 0 ∨ v = c₀ := by
    intro v hv
    rw [hspan] at hv
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rcases zmod2_cases a with rfl | rfl
    · exact Or.inl (zero_smul _ _)
    · exact Or.inr (one_smul _ _)
  refine ⟨fun c hc hc0 => ?_, ?_⟩
  · rcases hmem01 c hc with rfl | rfl
    · exact absurd rfl hc0
    · exact hqc
  obtain ⟨ĉ, hĉQ, hĉc⟩ := S.exists_cl c₀
  have hĉ2 : ĉ ^ 2 = S.z :=
    (S.sq_eq_one_or_z hĉQ).resolve_left ((S.q_cl_eq_one_iff hĉQ).mp (hĉc ▸ hqc))
  have hz : S.z ∈ zpowers ĉ := ⟨2, by
    change ĉ ^ (2 : ℤ) = S.z
    rw [zpow_two, ← pow_two, hĉ2]⟩
  have hĉmem : ĉ ∈ zpowers ĉ := mem_zpowers ĉ
  have hpre : ∀ y ∈ S.QG, S.cl y ∈ S.commQt x → y ∈ zpowers ĉ := by
    intro y hy hyc
    rcases hmem01 _ hyc with h | h
    · rcases (S.cl_eq_zero_iff hy).mp h with rfl | rfl
      · exact one_mem _
      · exact hz
    · rcases (S.cl_eq_cl_iff hĉQ hy).mp (hĉc.trans h.symm) with rfl | rfl
      · exact hĉmem
      · exact mul_mem hĉmem hz
  refine ⟨ĉ, hĉQ, hĉ2, le_antisymm ?_ ?_⟩
  · rw [commutator_le]
    intro a ha y hy
    obtain ⟨k, rfl⟩ := ha
    have haM : x ^ k ∈ S.M := zpow_mem hxM k
    have hρ : S.ρ ⟨x ^ k, haM⟩ = S.ρ ⟨x, hxM⟩ ^ k := by
      rw [← map_zpow]
      rfl
    have hcQ : x ^ k * y * (x ^ k)⁻¹ * y⁻¹ ∈ S.QG := S.commutator_mem_QG haM hy
    rw [commutatorElement_def]
    refine hpre _ hcQ ?_
    rw [S.cl_commutator haM hy, hρ]
    have htt' : S.ρ ⟨x, hxM⟩ * S.ρ ⟨x, hxM⟩ = 1 := Subtype.ext htt
    rcases (mem_zpowers_iff_of_mul_self htt').mp (mem_zpowers_iff.mpr ⟨k, rfl⟩) with h | h
    · rw [h]
      simp
    · rw [h, hcomm]
      exact sub_mem_commSpace t _
  · obtain ⟨y, hy, hyc⟩ := (S.mem_commQt_iff hxM).mp (hspan ▸ Submodule.mem_span_singleton_self c₀)
    have hmem : x * y * x⁻¹ * y⁻¹ ∈ ⁅zpowers x, S.QG⁆ := by
      have := commutator_mem_commutator (mem_zpowers x) hy
      rwa [commutatorElement_def] at this
    have hcQ := S.commutator_mem_QG hxM hy
    rw [zpowers_le]
    rcases (S.cl_eq_cl_iff hĉQ hcQ).mp (hĉc.trans hyc.symm) with h | h
    · rw [← h]
      exact hmem
    ·
      have hz' : S.z ∈ ⁅zpowers x, S.QG⁆ := by
        have h2 : (x * y * x⁻¹ * y⁻¹) ^ 2 = S.z := by
          rw [h, pow_two, mul_assoc, ← mul_assoc S.z, ← S.z_comm_QG hĉQ, mul_assoc ĉ,
            S.z_mul_z, mul_one, ← pow_two, hĉ2]
        rw [← h2]
        exact pow_mem hmem 2
      have : ĉ = x * y * x⁻¹ * y⁻¹ * S.z := by rw [h, mul_assoc, S.z_mul_z, mul_one]
      rw [this]
      exact mul_mem hmem hz'

theorem aschbacher_8_6_cyclic {x : G} (hxM : x ∈ S.M)
    (hdim : finrank (ZMod 2) (S.commQt x) = 1) :
    IsCyclic (⁅zpowers x, S.QG⁆ : Subgroup G) ∧
      Nat.card (⁅zpowers x, S.QG⁆ : Subgroup G) = 4 := by
  obtain ⟨-, c, hcQ, hc2, heq⟩ := S.aschbacher_8_6 hxM hdim
  rw [heq]
  refine ⟨isCyclic_zpowers c, ?_⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.card_zpowers]
  refine orderOf_eq_prime_pow (n := 1) (p := 2) ?_ ?_
  · rw [pow_one, hc2]
    exact S.z_ne_one
  · exact S.pow_four_eq_one hcQ

theorem relIndex_mul_card_clSub {X : Subgroup G} (hX : X ≤ S.QG) (hz : S.z ∈ X) :
    X.relIndex S.QG * 2 ^ finrank (ZMod 2) (S.clSub X) = 2 ^ finrank (ZMod 2) S.Qt := by
  have h := relIndex_mul_card X S.QG
  have hcard : Nat.card X = 2 * 2 ^ finrank (ZMod 2) (S.clSub X) := by
    rw [← S.card_submodule, ← S.card_clPre, S.clPre_clSub hX hz]
  rw [inf_eq_left.mpr hX, hcard, S.card_QG_eq, S.card_Qt] at h
  refine Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) ?_
  rw [← h]
  ring

theorem aschbacher_4_5 {x : G} (hxM : x ∈ S.M) (hx2 : x ^ 2 = 1) (hxQ : x ∉ S.QG)
    {Y : Subgroup G} (hYQ : Y ≤ S.QG) (hY : Y.relIndex S.QG ≤ 4)
    (hxY : ∀ y ∈ Y, x * y = y * x) :
    S.IsTypeAOn ⟨x, hxM⟩ 2 ∨ S.IsTypeBOn ⟨x, hxM⟩ 1 := by
  set t := (S.ρ ⟨x, hxM⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) with ht
  set C := S.QG ⊓ centralizer ({x} : Set G) with hC
  have hzC : S.z ∈ C := ⟨S.z_mem_QG, mem_centralizer_singleton_iff.mpr (S.z_comm hxM).symm⟩
  have hYC : Y ≤ C := fun y hy => ⟨hYQ hy, mem_centralizer_singleton_iff.mpr (hxY y hy).symm⟩
  have hYne : Y.relIndex S.QG ≠ 0 := fun h0 => by
    have h := relIndex_mul_card Y S.QG
    rw [h0, zero_mul, S.card_QG_eq, S.card_Qt] at h
    exact absurd h.symm (by positivity)
  have hCi : C.relIndex S.QG ≤ 4 := (relIndex_le_of_le_left hYC hYne).trans hY
  have h1 := S.relIndex_mul_card_clSub (inf_le_left : C ≤ S.QG) hzC
  have hle : S.clSub C ≤ S.fixQt x := S.clSub_centralizer_le_fixQt hxM
  have h2 := finrank_commSpace_add_finrank_fixSpace t
  rw [← S.fixQt_of_mem hxM, ← S.commQt_of_mem hxM] at h2
  have h3 := Submodule.finrank_mono hle
  have h4 : finrank (ZMod 2) S.Qt ≤ finrank (ZMod 2) (S.clSub C) + 2 := by
    have h5 : 2 ^ finrank (ZMod 2) S.Qt ≤ 2 ^ (finrank (ZMod 2) (S.clSub C) + 2) := by
      rw [← h1, pow_add, mul_comm]
      exact Nat.mul_le_mul_left _ (hCi.trans (by norm_num))
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h5
  have htne : t ≠ 1 := fun h => hxQ ((S.ρ_eq_one_iff ⟨x, hxM⟩).mp (Subtype.ext h))
  have hd1 : 1 ≤ finrank (ZMod 2) (S.commQt x) := by
    rw [S.commQt_of_mem hxM]
    exact one_le_finrank_commSpace htne
  have htt := S.ρ_mul_self hxM hx2
  have hO : ∀ v, S.q (t v) = S.q v :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (S.ρ_mem_O ⟨x, hxM⟩)
  rcases Nat.lt_or_ge (finrank (ZMod 2) (S.commQt x)) 2 with hd | hd
  · right
    refine ⟨hO, htt, ?_, ⟨0, rfl⟩⟩
    rw [← S.commQt_of_mem hxM]
    omega
  · left
    have hd2 : finrank (ZMod 2) (S.commQt x) = 2 := by omega
    have hfix : S.fixQt x = S.clSub C :=
      (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm
    refine ⟨hO, htne, htt, ?_, ?_⟩
    · rw [← S.commQt_of_mem hxM]
      exact hd2
    · intro v hv
      rw [← S.commQt_of_mem hxM] at hv
      exact S.q_eq_zero_of_mem_commQt hxM hx2 hfix v hv

theorem aschbacher_4_5_of_finrank_eq_two {x : G} (hxM : x ∈ S.M) (hx2 : x ^ 2 = 1)
    (hdim : finrank (ZMod 2) (S.commQt x) = 2) {Y : Subgroup G} (hYQ : Y ≤ S.QG)
    (hY : Y.relIndex S.QG ≤ 4) (hxY : ∀ y ∈ Y, x * y = y * x) :
    S.IsTypeAOn ⟨x, hxM⟩ 2 := by
  have hxQ : x ∉ S.QG := fun h => by
    have h1 : S.ρ ⟨x, hxM⟩ = 1 := (S.ρ_eq_one_iff ⟨x, hxM⟩).mpr h
    have h0 : commSpace (1 : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      obtain ⟨w, rfl⟩ := mem_commSpace.mp hv
      simp
    rw [S.commQt_of_mem hxM, h1, OneMemClass.coe_one, h0, finrank_bot] at hdim
    exact absurd hdim (by norm_num)
  rcases S.aschbacher_4_5 hxM hx2 hxQ hYQ hY hxY with h | h
  · exact h
  · exfalso
    have := h.2.2.1
    rw [← S.commQt_of_mem hxM, hdim] at this
    exact absurd this (by norm_num)

end Setting

end CFSG.LargeExtraspecial
