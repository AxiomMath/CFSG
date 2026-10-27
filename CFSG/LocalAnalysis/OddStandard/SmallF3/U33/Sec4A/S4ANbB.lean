module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ANbA

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup
open scoped Pointwise commutatorElement

namespace S4A

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem n4_zpowers_t_comm (h : L41GPh5 t L S x₁ x₂ lam rho) {p g : G} (hp : p ∈ zpowers t)
    (hg : g ∈ L) : p * g = g * p := by
  have hP : twoCore t = zpowers t := h.p2
  rw [← hP] at hp
  exact twoCore_commute h.hyp p hp g hg

theorem n4_tF_le_W (h : L41GPh5 t L S x₁ x₂ lam rho) :
    zpowers t ⊔ fourGrp x₁ x₂ ≤ ctxW t x₁ x₂ := by
  have hP : twoCore t = zpowers t := h.p2
  refine sup_le ?_ ((pt_four_le_base x₁ x₂).trans le_sup_right)
  rw [← hP]
  exact le_sup_left

theorem n4_cent_O2_rho (h : L41GPh5 t L S x₁ x₂ lam rho) :
    l41O2 t x₁ x₂ ⊓ centralizer ({rho} : Set G) = zpowers t := by
  have hP : twoCore t = zpowers t := h.p2
  apply le_antisymm
  · intro q hq
    obtain ⟨hqO, hqC⟩ := Subgroup.mem_inf.mp hq
    have hqc : q * rho = rho * q := Subgroup.mem_centralizer_singleton_iff.mp hqC
    have hc : q * rho * q⁻¹ * rho⁻¹ ∈ ctxW t x₁ x₂ := by
      have e : q * rho * q⁻¹ * rho⁻¹ = 1 := by
        rw [hqc]
        group
      rw [e]
      exact Subgroup.one_mem _
    have hqW := n4_O_comm_rho h.toL41GPh3 hqO hc
    have hmem : q ∈ ctxW t x₁ x₂ ⊓ centralizer ({rho} : Set G) := ⟨hqW, hqC⟩
    rwa [h.cent_rho, hP] at hmem
  · refine Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
    · exact n4_W_le_O h.toL41GPh3 (Subgroup.mem_sup_left h.hyp.mem_twoCore)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (mem_invCent_iff.mp (L_le_invCent h.hyp h.rho_mem)).symm

theorem n4_cent_O2bar_rho (h : L41GPh5 t L S x₁ x₂ lam rho) :
    {q | q ∈ l41O2 t x₁ x₂ ∧ ⁅q, rho⁆ ∈ fourGrp x₁ x₂} =
      ((zpowers t ⊔ fourGrp x₁ x₂ : Subgroup G) : Set G) := by
  have hP : twoCore t = zpowers t := h.p2
  have hρL : rho ∈ L := h.rho_mem
  have hFL : ∀ f ∈ fourGrp x₁ x₂, f ∈ L := fun f hf => pt_four_le_L h.toCtx0 hf
  have hcomm : ∀ a ∈ zpowers t, ∀ b ∈ fourGrp x₁ x₂, a * b = b * a :=
    fun a ha b hb => n4_zpowers_t_comm h ha (hFL b hb)
  ext q
  constructor
  · rintro ⟨hqO, hqF⟩
    have hFW : fourGrp x₁ x₂ ≤ ctxW t x₁ x₂ := (pt_four_le_base x₁ x₂).trans le_sup_right
    have hqW : q ∈ ctxW t x₁ x₂ :=
      n4_O_comm_rho h.toL41GPh3 hqO (hFW hqF)
    obtain ⟨p, hp, b, hb, rfl⟩ := (mem_sup_iff_of_commute (pt_comm_base h.toCtx0)).mp hqW
    have hpz : p ∈ zpowers t := by rwa [← hP]
    have hbL : b ∈ L := pt_base_le_L h.toCtx0 hb
    have hbr : ⁅b, rho⁆ ∈ L := by
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hbL hρL)
        (Subgroup.inv_mem _ hbL)) (Subgroup.inv_mem _ hρL)
    have e := n4_comm_mul_of_comm (n4_zpowers_t_comm h hpz hρL) (n4_zpowers_t_comm h hpz hbr)
    rw [e] at hqF
    have hbF : b ∈ fourGrp x₁ x₂ := n4_base_mem_four h.toL41GPh3 hb hqF
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hpz) (Subgroup.mem_sup_right hbF)
  · intro hq
    obtain ⟨p, hp, f, hf, rfl⟩ := (mem_sup_iff_of_commute hcomm).mp hq
    have hqW : p * f ∈ ctxW t x₁ x₂ := n4_tF_le_W h hq
    have hρN : rho ∈ l41N t x₁ x₂ := n4_K_le_N h.toL41GPh1 (Subgroup.subset_closure (by simp))
    refine ⟨n4_W_le_O h.toL41GPh3 hqW, ?_⟩
    have hfr : ⁅f, rho⁆ ∈ fourGrp x₁ x₂ := by
      have e0 : ⁅f, rho⁆ = f * (rho * f⁻¹ * rho⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [e0]
      exact Subgroup.mul_mem _ hf
        ((n4_normal_F2 h.toL41GPh3).2 rho hρN f⁻¹ (Subgroup.inv_mem _ hf))
    have e := n4_comm_mul_of_comm (n4_zpowers_t_comm h hp hρL)
      (hcomm p hp _ hfr)
    rw [e]
    exact hfr

theorem n4_conj_zpowers_t (h : L41GPh5 t L S x₁ x₂ lam rho) {m : G} (hm : m ∈ l41N t x₁ x₂)
    {p : G} (hp : p ∈ zpowers t) : ∃ u ∈ fourGrp x₁ x₂, m * p * m⁻¹ = p * u := by
  have hmt : m * t * m⁻¹ ∈ t • (fourGrp x₁ x₂ : Set G) := by
    rw [← h.normalizerFacts.orbit_t]
    exact ⟨m, hm, rfl⟩
  obtain ⟨f', hf', hmt'⟩ := n4_mem_smul_iff.mp hmt
  have hc : Commute t f' :=
    n4_zpowers_t_comm h (Subgroup.mem_zpowers t) (pt_four_le_L h.toCtx0 hf')
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
  refine ⟨f' ^ k, Subgroup.zpow_mem _ hf' k, ?_⟩
  rw [← conj_zpow, hmt']
  exact hc.mul_zpow k

theorem n4_center_Nbar (h : L41GPh5 t L S x₁ x₂ lam rho) :
    {n | n ∈ l41N t x₁ x₂ ∧ ∀ m ∈ l41N t x₁ x₂, ⁅n, m⁆ ∈ fourGrp x₁ x₂} =
      ((zpowers t ⊔ fourGrp x₁ x₂ : Subgroup G) : Set G) := by
  have hP : twoCore t = zpowers t := h.p2
  have hρL : rho ∈ L := h.rho_mem
  have hFL : ∀ f ∈ fourGrp x₁ x₂, f ∈ L := fun f hf => pt_four_le_L h.toCtx0 hf
  have hcomm : ∀ a ∈ zpowers t, ∀ b ∈ fourGrp x₁ x₂, a * b = b * a :=
    fun a ha b hb => n4_zpowers_t_comm h ha (hFL b hb)
  have hFW : fourGrp x₁ x₂ ≤ ctxW t x₁ x₂ := (pt_four_le_base x₁ x₂).trans le_sup_right
  have hρN : rho ∈ l41N t x₁ x₂ := n4_K_le_N h.toL41GPh1 (Subgroup.subset_closure (by simp))
  ext n
  constructor
  · rintro ⟨hnN, hc⟩
    have hnW : n ∈ ctxW t x₁ x₂ := n4_center_W h.toL41GPh3 hnN (fun m hm => hFW (hc m hm))
    obtain ⟨p, hp, b, hb, rfl⟩ := (mem_sup_iff_of_commute (pt_comm_base h.toCtx0)).mp hnW
    have hpz : p ∈ zpowers t := by rwa [← hP]
    have hbL : b ∈ L := pt_base_le_L h.toCtx0 hb
    have hbr : ⁅b, rho⁆ ∈ L := by
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hbL hρL)
        (Subgroup.inv_mem _ hbL)) (Subgroup.inv_mem _ hρL)
    have e := n4_comm_mul_of_comm (n4_zpowers_t_comm h hpz hρL) (n4_zpowers_t_comm h hpz hbr)
    have hbρ := hc rho hρN
    rw [e] at hbρ
    have hbF : b ∈ fourGrp x₁ x₂ := n4_base_mem_four h.toL41GPh3 hb hbρ
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hpz) (Subgroup.mem_sup_right hbF)
  · intro hn
    obtain ⟨p, hp, f, hf, rfl⟩ := (mem_sup_iff_of_commute hcomm).mp hn
    have hnW : p * f ∈ ctxW t x₁ x₂ := n4_tF_le_W h hn
    refine ⟨n4_W_le_N h.toL41GPh1 hnW, fun m hm => ?_⟩
    obtain ⟨u, hu, hmp⟩ := n4_conj_zpowers_t h hm hp
    have hf₁ : m * f * m⁻¹ ∈ fourGrp x₁ x₂ := (n4_normal_F2 h.toL41GPh3).2 m hm f hf
    have e : ⁅p * f, m⁆ = p * (f * (m * f * m⁻¹)⁻¹ * u⁻¹) * p⁻¹ := by
      calc ⁅p * f, m⁆ = (p * f) * (m * (p * f)⁻¹ * m⁻¹) := by
            rw [commutatorElement_def]
            group
        _ = (p * f) * (m * p * m⁻¹ * (m * f * m⁻¹))⁻¹ := by group
        _ = (p * f) * (p * u * (m * f * m⁻¹))⁻¹ := by rw [hmp]
        _ = p * (f * (m * f * m⁻¹)⁻¹ * u⁻¹) * p⁻¹ := by group
    have hw : f * (m * f * m⁻¹)⁻¹ * u⁻¹ ∈ fourGrp x₁ x₂ :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hf (Subgroup.inv_mem _ hf₁)) (Subgroup.inv_mem _ hu)
    have hpw := hcomm p hp _ hw
    have e2 : p * (f * (m * f * m⁻¹)⁻¹ * u⁻¹) * p⁻¹ = f * (m * f * m⁻¹)⁻¹ * u⁻¹ := by
      calc p * (f * (m * f * m⁻¹)⁻¹ * u⁻¹) * p⁻¹
          = ((f * (m * f * m⁻¹)⁻¹ * u⁻¹) * p) * p⁻¹ := by rw [hpw]
        _ = f * (m * f * m⁻¹)⁻¹ * u⁻¹ := by group
    rw [e, e2]
    exact hw

theorem l41_nbar_of (h : L41GPh6 t L S x₁ x₂ lam rho) : L41NbarFacts t x₁ x₂ rho where
  center_Nbar := n4_center_Nbar h.toL41GPh5
  cent_O2_rho := n4_cent_O2_rho h.toL41GPh5
  cent_O2bar_rho := n4_cent_O2bar_rho h.toL41GPh5

end S4A

theorem l41_nbar_holds : L41NbarStmt :=
  fun h => S4A.l41_nbar_of h.toG

end CFSG.OddStandard.SmallF3.HarrisU33
