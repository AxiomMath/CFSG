module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4SC
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Wreath
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.WreathB

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem mem_sup_of_normalizes {A C : Subgroup G} (hC : ∀ c ∈ C, ∀ a ∈ A, c * a * c⁻¹ ∈ A)
    {g : G} (hg : g ∈ A ⊔ C) : ∃ a ∈ A, ∃ c ∈ C, g = a * c := by
  rw [Subgroup.sup_eq_closure] at hg
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
      rcases hg with hg | hg
      · exact ⟨g, hg, 1, one_mem _, (mul_one g).symm⟩
      · exact ⟨1, one_mem _, g, hg, (one_mul g).symm⟩
  | one => exact ⟨1, one_mem _, 1, one_mem _, (mul_one 1).symm⟩
  | mul x y _ _ ihx ihy =>
      obtain ⟨a, ha, c, hc, rfl⟩ := ihx
      obtain ⟨a', ha', c', hc', rfl⟩ := ihy
      refine ⟨a * (c * a' * c⁻¹), mul_mem ha (hC c hc a' ha'), c * c', mul_mem hc hc', ?_⟩
      group
  | inv x _ ihx =>
      obtain ⟨a, ha, c, hc, rfl⟩ := ihx
      refine ⟨c⁻¹ * a⁻¹ * c⁻¹⁻¹, ?_, c⁻¹, inv_mem hc, ?_⟩
      · exact hC c⁻¹ (inv_mem hc) a⁻¹ (inv_mem ha)
      · group

namespace Z4Pre

variable (hp : Z4Pre t L S x₁ x₂ lam rho tau)
include hp

theorem card_B : Nat.card (baseGrp x₁ x₂) = 16 := hp.wreath.baseGrp_eq.2.2

theorem card_V : Nat.card (fourGrp x₁ x₂) = 4 := hp.wreath.fourGrp_eq_omega.2.2

theorem B_comm_t : ∀ b ∈ baseGrp x₁ x₂, b * t = t * b := by
  have hE : ∀ x : G, x ∈ closure {t, tau, x₁, x₂} → x * t = t * x := fun x hx => by
    rw [← hp.cent_E] at hx
    exact (mem_centralizer_iff.mp hx.2 t (subset_closure (by simp))).symm
  have hx₁ := hE x₁ (subset_closure (by simp))
  have hx₂ := hE x₂ (subset_closure (by simp))
  have hcent : baseGrp x₁ x₂ ≤ centralizer ({t} : Set G) := by
    rw [baseGrp, Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact mem_centralizer_iff.mpr fun h hh => by rw [Set.mem_singleton_iff.mp hh]; exact hx₁.symm
    · exact mem_centralizer_iff.mpr fun h hh => by rw [Set.mem_singleton_iff.mp hh]; exact hx₂.symm
  intro b hb
  exact (mem_centralizer_iff.mp (hcent hb) t (Set.mem_singleton t)).symm

theorem tau_conj_B : ∀ b ∈ baseGrp x₁ x₂, tau * b * tau⁻¹ ∈ baseGrp x₁ x₂ := by
  intro b hb
  induction hb using Subgroup.closure_induction with
  | mem g hg =>
      rcases hg with rfl | rfl
      · rw [hp.tau_x₁]; exact inv_mem (subset_closure (by simp))
      · rw [hp.tau_x₂]; exact inv_mem (subset_closure (by simp))
  | one => simp
  | mul x y _ _ ihx ihy =>
      have : tau * (x * y) * tau⁻¹ = (tau * x * tau⁻¹) * (tau * y * tau⁻¹) := by group
      rw [this]; exact mul_mem ihx ihy
  | inv x _ ihx =>
      have : tau * x⁻¹ * tau⁻¹ = (tau * x * tau⁻¹)⁻¹ := by group
      rw [this]; exact inv_mem ihx

theorem t_conj_B {b : G} (hb : b ∈ baseGrp x₁ x₂) : t * b * t⁻¹ = b := by
  rw [← hp.B_comm_t b hb, mul_assoc, mul_inv_cancel, mul_one]

theorem tt_conj_B : ∀ c ∈ closure {t, tau}, ∀ b ∈ baseGrp x₁ x₂, c * b * c⁻¹ ∈ baseGrp x₁ x₂ := by
  intro c hc b hb
  have hc4 := (S4B.mem_closure_pair_of_invol hp.t_mul_self hp.tau_mul_self hp.t_comm_tau).mp hc
  rcases hc4 with h | h | h | h
  · rw [h]; simpa using hb
  · rw [h, hp.t_conj_B hb]; exact hb
  · rw [h]; exact hp.tau_conj_B b hb
  · have h1 : t * tau * b * (t * tau)⁻¹ = t * (tau * b * tau⁻¹) * t⁻¹ := by group
    rw [h, h1, hp.t_conj_B (hp.tau_conj_B b hb)]
    exact hp.tau_conj_B b hb

theorem CQ_t : ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) = baseGrp x₁ x₂ := by
  apply le_antisymm
  · rintro q ⟨hqQ, hqt⟩
    have hqt' : t * q = q * t := mem_centralizer_iff.mp hqt t (Set.mem_singleton t)
    have hE : ctxE t x₁ x₂ ≤ centralizer ({q} : Set G) := by
      rw [ctxE, Subgroup.closure_le]
      intro e he
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      rcases he with h | h | h
      · rw [h]; exact hqt'
      · rw [h]; exact (hp.Q_comm q hqQ _ (hp.V_le_Q hp.y_mem_V)).symm
      · rw [h]; exact (hp.Q_comm q hqQ _ (hp.V_le_Q hp.z_mem_V)).symm
    have hqK : q ∈ closure ({t, tau, x₁, x₂} : Set G) := by
      rw [← hp.cent_E]
      refine ⟨hp.Q_le_O hqQ, mem_centralizer_iff.mpr fun e he => ?_⟩
      exact (mem_centralizer_iff.mp (hE he) q (Set.mem_singleton q)).symm
    have hK : closure ({t, tau, x₁, x₂} : Set G) ≤ baseGrp x₁ x₂ ⊔ closure {t, tau} := by
      rw [Subgroup.closure_le]
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with h | h | h | h
      · rw [h]; exact mem_sup_right (subset_closure (by simp))
      · rw [h]; exact mem_sup_right (subset_closure (by simp))
      · rw [h]; exact mem_sup_left (subset_closure (by simp))
      · rw [h]; exact mem_sup_left (subset_closure (by simp))
    obtain ⟨b, hb, c, hc, hqbc⟩ :=
      mem_sup_of_normalizes (fun c hc a ha => hp.tt_conj_B c hc a ha) (hK hqK)
    have hcQ : c ∈ ctxQ t tau x₁ x₂ rho := by
      have h : c = b⁻¹ * q := by rw [hqbc]; group
      rw [h]; exact mul_mem (inv_mem (hp.base_le_Q hb)) hqQ
    have hcCO : c ∈ ctxCO t tau x₁ x₂ rho := by rw [hp.CO_rho]; exact hc
    have hcC : c ∈ centralizer ({rho} : Set G) :=
      (show c ∈ ctxO t tau x₁ x₂ ⊓ centralizer ({rho} : Set G) from hcCO).2
    have hc1 : c = 1 := by
      have h : c ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({rho} : Set G) := ⟨hcQ, hcC⟩
      rw [hp.CQ_rho] at h
      exact mem_bot.mp h
    rw [hqbc, hc1, mul_one]; exact hb
  · intro b hb
    exact ⟨hp.base_le_Q hb, mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff.mp hh]; exact (hp.B_comm_t b hb).symm⟩

theorem V_le_B : fourGrp x₁ x₂ ≤ baseGrp x₁ x₂ := by
  rw [hp.wreath.fourGrp_eq_omega.1, Subgroup.closure_le]
  exact fun a ha => ha.1

theorem B_inf_Y : baseGrp x₁ x₂ ⊓ ctxYq t tau x₁ x₂ rho = fourGrp x₁ x₂ := by
  apply le_antisymm
  · rintro a ⟨haB, haY⟩
    have ha2 : a ^ 2 = 1 := ((hp.mem_Y_iff a).mp haY).2
    rw [hp.wreath.fourGrp_eq_omega.1]
    exact subset_closure ⟨haB, ha2⟩
  · intro v hv
    exact ⟨hp.V_le_B hv, hp.V_le_Y hv⟩

theorem CY_t : ctxYq t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) = fourGrp x₁ x₂ := by
  apply le_antisymm
  · rintro a ⟨haY, hat⟩
    have haQ : a ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) := ⟨hp.Y_le_Q haY, hat⟩
    rw [hp.CQ_t] at haQ
    have h : a ∈ baseGrp x₁ x₂ ⊓ ctxYq t tau x₁ x₂ rho := ⟨haQ, haY⟩
    rwa [hp.B_inf_Y] at h
  · intro v hv
    exact ⟨hp.V_le_Y hv, mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff.mp hh]; exact hp.t_comm_V v hv⟩

theorem comm_t_eq_one_iff {a : G} (ha : a ∈ ctxYq t tau x₁ x₂ rho) :
    z4Comm t a = 1 ↔ a ∈ fourGrp x₁ x₂ := by
  rw [hp.comm_eq_one_iff]
  constructor
  · intro h
    rw [← hp.CY_t]
    exact ⟨ha, mem_centralizer_iff.mpr fun g hg => by rw [Set.mem_singleton_iff.mp hg]; exact h⟩
  · intro hv
    exact hp.t_comm_V a hv

theorem exists_comm_eq : ∀ v ∈ fourGrp x₁ x₂, ∃ a ∈ ctxYq t tau x₁ x₂ rho, z4Comm t a = v := by
  obtain ⟨N, hNY, hNmem, hNimg, hNcard⟩ := S4B.exists_comm_image
    (A := ctxYq t tau x₁ x₂ rho) hp.Y_comm (g := t)
    (fun a ha => hp.normal_Y.2 t hp.t_mem_M a ha)
  have hNV : N ≤ fourGrp x₁ x₂ := by
    intro n hn
    obtain ⟨a, ha, hn'⟩ := hNimg n hn
    have h := hp.comm_mem hp.t_mem_X (hp.Y_le_O ha)
    have h2 : a * t * a⁻¹ * t⁻¹ = (z4Comm t a)⁻¹ := by unfold z4Comm; group
    rw [hn', h2]
    exact inv_mem h
  have hcardC : Nat.card ↥(ctxYq t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G)) = 4 := by
    rw [hp.CY_t]; exact hp.card_V
  have hN4 : Nat.card N = 4 := by
    rw [hp.card_Y, hcardC] at hNcard
    omega
  have hNeq : N = fourGrp x₁ x₂ :=
    Subgroup.eq_of_le_of_card_ge hNV (by rw [hN4, hp.card_V])
  intro v hv
  have hv' : v⁻¹ ∈ N := by rw [hNeq]; exact inv_mem hv
  obtain ⟨a, ha, hav⟩ := hNimg v⁻¹ hv'
  refine ⟨a, ha, ?_⟩
  have h2 : z4Comm t a = (a * t * a⁻¹ * t⁻¹)⁻¹ := by unfold z4Comm; group
  rw [h2, ← hav, inv_inv]

end Z4Pre

end CFSG.OddStandard.SmallF3.HarrisU33
