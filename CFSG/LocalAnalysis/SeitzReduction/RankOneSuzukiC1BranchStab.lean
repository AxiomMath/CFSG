module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiC1BranchNu

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

namespace SzStart

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem card_normalizer_szT₁_inf_centralizer_dvd_of_card_sylow
    (h : SzStart G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    Nat.card (normalizer (szT₁ L T : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) ∣
      2 * (2 ^ f) ^ 2 * ((2 ^ f - 1) * f) := by
  have hst := h.setting.standardSetting
  have hHN := (CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality
    hst.standard h.mem h.inv).1
  have hCt := (inf_centralizer_eq_zpowers_of_card_sylow_eq_two hst.standard hS2 h.mem h.inv
    (hst.core t h.inv)).le
  have hML : normalizer (szT₁ L T : Set G) ⊓ centralizer ({t} : Set G) ≤
      normalizer (L : Set G) := inf_le_right.trans hHN
  have hkey := card_dvd_card_sup_mul_card_outer hML inf_le_left inf_le_right h.mem hCt
    (szT₁_le_right L T)
  have hdisj : (normalizer (szT₁ L T : Set G) ⊓ L) ⊓ zpowers t = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hxt⟩ := mem_inf.mp hx
    rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hxt with rfl | rfl
    · exact one_mem _
    · exact absurd (mem_inf.mp hx1).2 (h.not_mem_of_card_sylow hS2)
  rw [card_sup_zpowers_of_disjoint (centralizer_le inf_le_right h.mem) h.inv hdisj,
    h.card_normalizer_szT₁_inf_of_card_sylow hS2] at hkey
  refine hkey.trans ?_
  have hout := card_outer_dvd_of_lieModel_twistedB2 h.model
  calc (2 ^ f) ^ 2 * (2 ^ f - 1) * 2 * Nat.card (Outer L) ∣ (2 ^ f) ^ 2 * (2 ^ f - 1) * 2 * f :=
        Nat.mul_dvd_mul_left _ hout
    _ = 2 * (2 ^ f) ^ 2 * ((2 ^ f - 1) * f) := by ring

theorem card_normalizer_szT₁_inf_centralizer_dvd
    (h : SzStart G L f t T) :
    Nat.card (normalizer (szT₁ L T : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) ∣
      2 * (2 ^ f) ^ 2 * ((2 ^ f - 1) * f) :=
  h.card_normalizer_szT₁_inf_centralizer_dvd_of_card_sylow h.card_sylow

end SzStart

namespace SzC1Stage

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f a : ℕ} {t : G} {T : Subgroup G}
  {d : G} {V U U₁ : Subgroup G} {k : ℕ}

theorem mem_U₁_mul_centralizer
    (h : SzC1Stage G L f a t T d V U U₁ k) (hμ : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)))
    (hν : ∃ w₀ ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), (w₀ * t) ^ 2 ≠ 1) {y : G}
    (hyU : y ∈ normalizer (U : Set G)) (hyT : y ∈ normalizer (szT₁ L T : Set G)) :
    ∃ u ∈ U₁, u⁻¹ * y ∈ centralizer ({t} : Set G) := by
  obtain ⟨K, _, _, _, uu, v, κ, hK, hc, hκ⟩ := h.coords
  have hxU : y * t * y⁻¹ ∈ U := (mem_normalizer_iff.mp hyU t).mp h.t_mem_U
  have hwU₁ := (h.mem_or_mul_t_mem hxU).resolve_left (h.conj_not_mem_U₁ y)
  have hxC : y * t * y⁻¹ ∈ centralizer (szT₁ L T : Set G) := by
    refine mem_centralizer_iff.mpr fun z hz => ?_
    have hz' : y⁻¹ * z * y ∈ szT₁ L T := by
      simpa using (mem_normalizer_iff.mp (inv_mem hyT) z).mp hz
    have e := h.t_comm hz'
    calc z * (y * t * y⁻¹) = y * ((y⁻¹ * z * y) * t) * y⁻¹ := by group
      _ = y * (t * (y⁻¹ * z * y)) * y⁻¹ := by rw [e]
      _ = y * t * y⁻¹ * z := by group
  have hw : y * t * y⁻¹ * t ∈ U₁ ⊓ centralizer (szT₁ L T : Set G) :=
    mem_inf.mpr ⟨hwU₁, mul_mem hxC h.start.mem_centralizer_szT₁⟩
  have hw1 : (y * t * y⁻¹ * t * t) ^ 2 = 1 := by
    rw [mul_assoc (y * t * y⁻¹) t t, h.t_mul_self, mul_one, sq,
      show y * t * y⁻¹ * (y * t * y⁻¹) = y * (t * t) * y⁻¹ by group, h.t_mul_self, mul_one,
      mul_inv_cancel]
  have hwV := h.mem_V_of_sq_eq_one hK hc hκ hμ hlam hν hw hw1
  have hwV' : y * t * y⁻¹ * t⁻¹ ∈ V := by
    rw [h.t_inv]
    exact hwV
  obtain ⟨u, hu, huσ⟩ := h.exists_comm_t_eq hK hc hκ hwV'
  refine ⟨u, hu, mem_centralizer_singleton_iff.mpr ?_⟩
  have e : u * t * u⁻¹ = y * t * y⁻¹ := by
    calc u * t * u⁻¹ = (u * t * u⁻¹ * t⁻¹) * t := by group
      _ = (y * t * y⁻¹ * t⁻¹) * t := by rw [huσ]
      _ = y * t * y⁻¹ := by group
  calc u⁻¹ * y * t = u⁻¹ * (y * t * y⁻¹) * y := by group
    _ = u⁻¹ * (u * t * u⁻¹) * y := by rw [e]
    _ = t * (u⁻¹ * y) := by group

theorem card_normalizer_inf_dvd
    (h : SzC1Stage G L f a t T d V U U₁ k) (hμ : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)))
    (hν : ∃ w₀ ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), (w₀ * t) ^ 2 ≠ 1) :
    Nat.card (normalizer (U : Set G) ⊓ normalizer (szT₁ L T : Set G) : Subgroup G) ∣
      Nat.card U * ((2 ^ f - 1) * f) := by
  obtain ⟨K, _, _, _, uu, v, κ, hK, hc, hκ⟩ := h.coords
  set Y := normalizer (U : Set G) ⊓ normalizer (szT₁ L T : Set G) with hY
  set M := Y ⊓ centralizer ({t} : Set G) with hM
  have hU₁Y : U₁ ≤ Y := le_inf (h.U₁_le.trans le_normalizer)
    (fun x hx => mem_normalizer_of_forall_inv_mul_mul_mem fun y hy => by
      simpa using h.conj_T₁_mem (inv_mem (h.U₁_le hx)) hy)
  have hMN : M ≤ normalizer (U₁ : Set G) := fun x hx =>
    mem_normalizer_of_forall_inv_mul_mul_mem fun w hw => by
      simpa using h.conj_mem_U₁_of_normalizer hμ (inv_mem (mem_inf.mp (mem_inf.mp hx).1).1) hw
  have hYeq : M ⊔ U₁ = Y := by
    refine le_antisymm (sup_le inf_le_left hU₁Y) fun y hy => ?_
    obtain ⟨u, hu, huy⟩ := h.mem_U₁_mul_centralizer hμ hlam hν (mem_inf.mp hy).1
      (mem_inf.mp hy).2
    have hu' : u⁻¹ * y ∈ M := mem_inf.mpr ⟨mul_mem (inv_mem (hU₁Y hu)) hy, huy⟩
    have e : y = u * (u⁻¹ * y) := by group
    rw [e]
    exact mul_mem (mem_sup_right hu) (mem_sup_left hu')
  have hinf : M ⊓ U₁ = szT₁ L T := by
    refine le_antisymm (fun x hx => h.mem_T₁_of_comm (mem_inf.mp hx).2
      (mem_centralizer_singleton_iff.mp (mem_inf.mp (mem_inf.mp hx).1).2)) ?_
    refine le_inf (le_inf (h.T₁_le_U₁.trans hU₁Y) fun y hy => ?_) h.T₁_le_U₁
    exact mem_centralizer_singleton_iff.mpr (h.t_comm hy)
  have h1 := SzC1.relIndex_sup_eq_relIndex_inf hMN
  rw [hYeq, hinf] at h1
  have h2 := relIndex_mul_card (H := U₁) (K := Y)
  rw [inf_of_le_left hU₁Y, h1] at h2
  have h3 := relIndex_mul_card (H := szT₁ L T) (K := M)
  rw [inf_of_le_left (le_inf (le_inf (h.T₁_le_U₁.trans hU₁Y) fun y hy =>
    mem_centralizer_singleton_iff.mpr (h.t_comm hy)) le_rfl |>.trans inf_le_left)] at h3
  have hMdvd : Nat.card M ∣ 2 * (2 ^ f) ^ 2 * ((2 ^ f - 1) * f) :=
    (Subgroup.card_dvd_of_le (le_inf (inf_le_left.trans inf_le_right) inf_le_right)).trans
      h.start.card_normalizer_szT₁_inf_centralizer_dvd
  have hT₁ := h.card_T₁ hK hc
  have hUU₁ : Nat.card U = 2 * Nat.card U₁ := by rw [h.card_U, h.card_U₁]
  have hidx : (szT₁ L T).relIndex M ∣ 2 * ((2 ^ f - 1) * f) := by
    have hq : 0 < (2 ^ f) ^ 2 := by positivity
    refine Nat.dvd_of_mul_dvd_mul_left hq ?_
    rw [← hT₁]
    calc Nat.card (szT₁ L T) * (szT₁ L T).relIndex M = Nat.card M := by rw [← h3, mul_comm]
      _ ∣ 2 * (2 ^ f) ^ 2 * ((2 ^ f - 1) * f) := hMdvd
      _ = Nat.card (szT₁ L T) * (2 * ((2 ^ f - 1) * f)) := by rw [hT₁]; ring
  rw [← h2, hUU₁]
  calc (szT₁ L T).relIndex M * Nat.card U₁ ∣ 2 * ((2 ^ f - 1) * f) * Nat.card U₁ :=
        Nat.mul_dvd_mul_right hidx _
    _ = 2 * Nat.card U₁ * ((2 ^ f - 1) * f) := by ring

theorem not_two_dvd_relIndex
    (h : SzC1Stage G L f a t T d V U U₁ k) (hμ : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)))
    (hν : ∃ w₀ ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), (w₀ * t) ^ 2 ≠ 1) :
    ¬ 2 ∣ U.relIndex (normalizer (U : Set G) ⊓ normalizer (szT₁ L T : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := normalizer (U : Set G) ⊓ normalizer (szT₁ L T : Set G) with hY
  have hUY : U ≤ Y := le_inf le_normalizer (fun x hx =>
    mem_normalizer_of_forall_inv_mul_mul_mem fun y hy => by
      simpa using h.conj_T₁_mem (inv_mem hx) hy)
  intro h2
  have hU2 : IsPGroup 2 (U.subgroupOf Y) := h.isPGroup_U.comap_subtype
  obtain ⟨Q, hUQ⟩ := hU2.exists_le_sylow
  have hQ2 : IsPGroup 2 ((Q : Subgroup Y).map Y.subtype) := Q.isPGroup'.map _
  have hUQ' : U ≤ (Q : Subgroup Y).map Y.subtype := fun x hx =>
    ⟨⟨x, hUY hx⟩, hUQ (mem_subgroupOf.mpr hx), rfl⟩
  have hQN : (Q : Subgroup Y).map Y.subtype ≤ normalizer (szT₁ L T : Set G) :=
    (map_subtype_le _).trans inf_le_right
  have heq := h.eq_of_le_normalizer_T₁ hμ hlam hν hQ2 hUQ' hQN
  have hQU : (Q : Subgroup Y) = U.subgroupOf Y := by
    ext x
    constructor
    · intro hx
      exact mem_subgroupOf.mpr (heq ▸ ⟨x, hx, rfl⟩)
    · intro hx
      exact hUQ hx
  have hidx := Q.not_dvd_index
  rw [hQU] at hidx
  exact hidx h2

end SzC1Stage

end CFSG.SeitzReduction.RankOne
