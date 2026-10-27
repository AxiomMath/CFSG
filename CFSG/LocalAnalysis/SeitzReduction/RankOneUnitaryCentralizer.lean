module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryCentralizerAut

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.Blueprint CFSG.GH74.Uniqueness.Bender
open scoped commutatorElement

section Dihedral

variable {m : ℕ}

theorem dihedral_exists_r_of_pow_odd {g : DihedralGroup m} {b : ℕ} (hg : g ^ b = 1)
    (hb : Odd b) : ∃ i, g = DihedralGroup.r i := by
  rcases g with i | i
  · exact ⟨i, rfl⟩
  · exfalso
    have h1 : orderOf (DihedralGroup.sr i) ∣ b := orderOf_dvd_of_pow_eq_one hg
    rw [DihedralGroup.orderOf_sr] at h1
    exact (Nat.not_even_iff_odd.mpr hb) (even_iff_two_dvd.mpr h1)

end Dihedral

theorem centralizer_szA_le_centralizer {G : Type} [Group G] (L T : Subgroup G) (t : G) :
    centralizer (szA L T t : Set G) ≤ centralizer ({t} : Set G) :=
  centralizer_le (Set.singleton_subset_iff.mpr (mem_szA_right L T t))

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem centralizer_szA_le_normalizer (h : U3Start G L f t T) :
    centralizer (szA L T t : Set G) ≤ normalizer (L : Set G) :=
  (centralizer_szA_le_centralizer L T t).trans
    (CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality
      h.setting.standardSetting.standard h.mem h.inv).1

theorem mem_sup_of_forall_conj_eq_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {c y : G}
    (hc : c ∈ centralizer ({t} : Set G)) (hy : y ∈ szT₁ L T)
    (hcy : ∀ x ∈ L, c * x * c⁻¹ = y * x * y⁻¹) : c ∈ szT₁ L T ⊔ zpowers t := by
  have hst := h.setting.standardSetting
  have hCH : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t :=
    inf_centralizer_eq_zpowers_of_card_sylow_eq_two hst.standard hS2 h.mem h.inv (hst.core t h.inv)
  have hyL : y ∈ L := szT₁_le_right L T hy
  have hyt : y ∈ centralizer ({t} : Set G) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp h.mem y hyL)
  have hk : y⁻¹ * c ∈ zpowers t := by
    rw [← hCH]
    refine mem_inf.mpr ⟨mem_centralizer_iff.mpr fun x hx => ?_, mul_mem (inv_mem hyt) hc⟩
    calc x * (y⁻¹ * c) = y⁻¹ * (y * x * y⁻¹) * c := by group
      _ = y⁻¹ * (c * x * c⁻¹) * c := by rw [hcy x hx]
      _ = y⁻¹ * c * x := by group
  have e : c = y * (y⁻¹ * c) := by group
  rw [e]
  exact mul_mem (mem_sup_left hy) (mem_sup_right hk)

theorem exists_aut_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    ∃ (e : ℕ) (Q : Sylow 2 L), BenderType L f 3 e ∧
      (∀ y : L, y ∈ (Q : Subgroup L) ↔ (y : G) ∈ szT₁ L T) ∧
      (∀ y : L, y ∈ rootCenter (Q : Subgroup L) ↔ (y : G) ∈ szA₁ (szT₁ L T)) ∧
      ∃ ψ : centralizer (szA L T t : Set G) →* MulAut L,
        (∀ c y, ((ψ c y : L) : G) = (c : G) * (y : G) * (c : G)⁻¹) ∧
        (∀ c, ψ c ∈ autCentralizer (rootCenter (Q : Subgroup L))) ∧
        ∀ c, ψ c ∈ (Q : Subgroup L).map (MulAut.conj : L →* MulAut L) ↔
          (c : G) ∈ szT₁ L T ⊔ zpowers t := by
  obtain ⟨e, Q, hB, hmemQ, hmemZ⟩ := h.exists_bender_of_card_sylow hS2
  set ψ : centralizer (szA L T t : Set G) →* MulAut L :=
    L.normalizerMonoidHom.comp (inclusion h.centralizer_szA_le_normalizer) with hψdef
  have hψ : ∀ c y, ((ψ c y : L) : G) = (c : G) * (y : G) * (c : G)⁻¹ := fun c y =>
    normalizerMonoidHom_apply_apply_coe L _ y
  refine ⟨e, Q, hB, hmemQ, hmemZ, ψ, hψ, fun c z hz => Subtype.ext ?_, fun c => ⟨?_, ?_⟩⟩
  · rw [hψ]
    have hzA : (z : G) ∈ szA L T t := szA₁_le_szA L T t ((hmemZ z).mp hz)
    rw [← mem_centralizer_iff.mp c.2 _ hzA, mul_inv_cancel_right]
  · rintro ⟨y, hyQ, hyc⟩
    refine h.mem_sup_of_forall_conj_eq_of_card_sylow hS2
      (centralizer_szA_le_centralizer L T t c.2) ((hmemQ y).mp hyQ) fun x hx => ?_
    have := congrArg (fun σ : MulAut L => ((σ ⟨x, hx⟩ : L) : G)) hyc
    simp only [MulAut.conj_apply, coe_mul, coe_inv] at this
    rw [this, hψ]
  · intro hc
    obtain ⟨a, ha, z, hz, haz⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ hc
    have haL : a ∈ L := szT₁_le_right L T ha
    refine ⟨⟨a, haL⟩, (hmemQ _).mpr ha, MulEquiv.ext fun y => Subtype.ext ?_⟩
    have hzy : (y : G) * z = z * y := commute_of_mem_zpowers hz (mem_centralizer_iff.mp h.mem y y.2)
    rw [hψ, ← haz]
    simp only [MulAut.conj_apply, coe_mul, coe_inv]
    calc a * (y : G) * a⁻¹ = a * ((y : G) * z) * z⁻¹ * a⁻¹ := by group
      _ = a * z * y * (a * z)⁻¹ := by rw [hzy]; group

theorem card_szT₁_sup_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    Nat.card (szT₁ L T ⊔ zpowers t : Subgroup G) = 2 * (2 ^ f) ^ 3 := by
  obtain ⟨-, -, -, -, hdisj, -⟩ := h.start_of_card_sylow hS2
  obtain ⟨hcard, -⟩ := h.facts_of_card_sylow hS2
  rw [card_sup_zpowers_of_disjoint h.mem_centralizer_szT₁ h.inv hdisj, hcard, mul_comm]

theorem sq_mul_eq_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {y a : G}
    (hy : y ∈ szT₁ L T ⊔ zpowers t) (ha : a ∈ szA L T t) :
    (y * a) ^ 2 = y ^ 2 ∧ y ^ 2 ∈ szA₁ (szT₁ L T) := by
  obtain ⟨-, haSq, hAC, -⟩ := h.szA_facts_of_card_sylow hS2
  obtain ⟨-, -, -, hsq, -⟩ := h.facts_of_card_sylow hS2
  have hay : a * y = y * a := (mem_centralizer_iff.mp (hAC ha) y hy).symm
  refine ⟨?_, ?_⟩
  · rw [(Commute.symm hay).mul_pow, haSq a ha, mul_one]
  · obtain ⟨b, hb, z, hz, rfl⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ hy
    have hbz : Commute b z :=
      commute_of_mem_zpowers hz (mem_centralizer_iff.mp h.mem_centralizer_szT₁ b hb)
    have hz2 : z ^ 2 = 1 := by
      rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hz with rfl | rfl
      · exact one_pow 2
      · exact h.sq_eq_one
    rw [hbz.mul_pow, hz2, mul_one]
    exact hsq b hb

theorem mem_sup_of_forall_mem_szA₁_of_card_sylow
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    {c : G} (hc : c ∈ centralizer (szA L T t : Set G))
    (hcT : ∀ y ∈ szT₁ L T, y⁻¹ * (c * y * c⁻¹) ∈ szA₁ (szT₁ L T)) :
    c ∈ szT₁ L T ⊔ zpowers t := by
  obtain ⟨e, Q, hB, hmemQ, hmemZ, ψ, hψ, hψC, hψQ⟩ := h.exists_aut_of_card_sylow hS2
  refine (hψQ ⟨c, hc⟩).mp
    (mem_map_conj_of_forall_mem_rootCenter_unitary hB Q (hψC _) fun x hx => ?_)
  rw [hmemZ, coe_mul, coe_inv, hψ]
  exact hcT x ((hmemQ x).mp hx)

end U3Start

end CFSG.SeitzReduction.RankOne
