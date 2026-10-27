module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S0a

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup
open scoped Pointwise commutatorElement
open CFSG.OddStandard.SmallF3.HarrisU33.L34

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


variable (hc : Ctx4Q t L S x₁ x₂ lam rho tau)
include hc

omit hc in
theorem mem_zpowers_eq_one_or_eq {z g : G} (hz : z * z = 1) (hg : g ∈ zpowers z) :
    g = 1 ∨ g = z := by
  let H : Subgroup G :=
    { carrier := {g : G | g = 1 ∨ g = z}
      one_mem' := Or.inl rfl
      mul_mem' := by
        rintro a b (rfl | rfl) (rfl | rfl)
        · exact Or.inl (by simp)
        · exact Or.inr (by simp)
        · exact Or.inr (by simp)
        · exact Or.inl (by rw [hz])
      inv_mem' := by
        rintro a (rfl | rfl)
        · exact Or.inl (by simp)
        · exact Or.inr (by rw [inv_eq_of_mul_eq_one_right hz]) }
  exact (Subgroup.zpowers_le.mpr (show z ∈ H from Or.inr rfl)) hg

theorem s_facts {s : G} (hs : s = t ∨ s = tau ∨ s = t * tau) :
    s * s = 1 ∧ s ∈ ctxO t tau x₁ x₂ ∧ (∀ u ∈ closure ({t, tau} : Set G), s * u = u * s) ∧
      rho * s = s * rho ∧ lam * s = s * lam := by
  haveI : IsMulCommutative ↥(closure ({t, tau} : Set G)) :=
    (elemAbelian_closure_pair hc.t_mul_self hc.tau_mul_self hc.t_comm_tau).1
  have htT : t ∈ closure ({t, tau} : Set G) := subset_closure (by simp)
  have htauT : tau ∈ closure ({t, tau} : Set G) := subset_closure (by simp)
  have httauT : t * tau ∈ closure ({t, tau} : Set G) := mul_mem htT htauT
  have hcomm_of (a : G) (ha : a ∈ closure ({t, tau} : Set G)) :
      ∀ u ∈ closure ({t, tau} : Set G), a * u = u * a :=
    fun u hu => congrArg Subtype.val (mul_comm' ⟨a, ha⟩ ⟨u, hu⟩)
  rcases hs with hst | hst | hst
  · rw [hst]
    exact ⟨hc.t_mul_self, hc.t_mem_O, hcomm_of t htT, hc.rho_comm_t, (t_comm_lam hc).symm⟩
  · rw [hst]
    exact ⟨hc.tau_mul_self, hc.tau_mem_O, hcomm_of tau htauT, hc.rho_comm_tau, lam_comm_tau hc⟩
  · rw [hst]
    refine ⟨?_, mul_mem hc.t_mem_O hc.tau_mem_O, hcomm_of (t * tau) httauT, ?_, ?_⟩
    · calc (t * tau) * (t * tau) = (t * tau) ^ 2 := (pow_two _).symm
        _ = t ^ 2 * tau ^ 2 := Commute.mul_pow hc.t_comm_tau 2
        _ = 1 := by rw [pow_two, pow_two, hc.t_mul_self, hc.tau_mul_self, one_mul]
    · calc rho * (t * tau) = (rho * t) * tau := by group
        _ = (t * rho) * tau := by rw [hc.rho_comm_t]
        _ = t * (rho * tau) := by group
        _ = t * (tau * rho) := by rw [hc.rho_comm_tau]
        _ = (t * tau) * rho := by group
    · calc lam * (t * tau) = (lam * t) * tau := by group
        _ = (t * lam) * tau := by rw [← t_comm_lam hc]
        _ = t * (lam * tau) := by group
        _ = t * (tau * lam) := by rw [lam_comm_tau hc]
        _ = (t * tau) * lam := by group

theorem comm_le_V {s : G} (hs1 : s * s = 1) (hsO : s ∈ ctxO t tau x₁ x₂) :
    ⁅ctxQ t tau x₁ x₂ rho, zpowers s⁆ ≤ fourGrp x₁ x₂ := by
  rw [Subgroup.commutator_le]
  intro b hb g hg
  rcases mem_zpowers_eq_one_or_eq hs1 hg with rfl | rfl
  · simp [commutatorElement_def]
  · rw [commutatorElement_def]
    exact comm_Q_O_mem_V hc hb hsO

theorem comm_rho_inv {s : G} (hρs : rho * s = s * rho) :
    ∀ c ∈ ⁅ctxQ t tau x₁ x₂ rho, zpowers s⁆,
      rho * c * rho⁻¹ ∈ ⁅ctxQ t tau x₁ x₂ rho, zpowers s⁆ := by
  intro c hcmem
  rw [Subgroup.commutator_def] at hcmem ⊢
  induction hcmem using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := hx
      have h1 : rho * g₁ * rho⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
        hc.normal_Q.2 rho hc.rho_mem_M g₁ hg₁
      have h2 : rho * g₂ * rho⁻¹ ∈ zpowers s := by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg₂
        rw [← hk]
        have hfix : rho * s ^ k * rho⁻¹ = s ^ k := by
          rw [← conj_zpow, show rho * s * rho⁻¹ = s by rw [hρs]; group]
        rw [hfix]
        exact zpow_mem (Subgroup.mem_zpowers s) k
      have h3 : ⁅rho * g₁ * rho⁻¹, rho * g₂ * rho⁻¹⁆ ∈
          ⁅ctxQ t tau x₁ x₂ rho, zpowers s⁆ :=
        Subgroup.commutator_mem_commutator h1 h2
      have heq : rho * ⁅g₁, g₂⁆ * rho⁻¹ = ⁅rho * g₁ * rho⁻¹, rho * g₂ * rho⁻¹⁆ := by
        rw [commutatorElement_def, commutatorElement_def]
        group
      rw [heq]
      exact h3
  | one => simp
  | mul x y _ _ ihx ihy =>
      rw [show rho * (x * y) * rho⁻¹ = (rho * x * rho⁻¹) * (rho * y * rho⁻¹) by group]
      exact mul_mem ihx ihy
  | inv x _ ih =>
      rw [show rho * x⁻¹ * rho⁻¹ = (rho * x * rho⁻¹)⁻¹ by group]
      exact inv_mem ih

theorem eq_V_of_rho_inv {C : Subgroup G} (hCV : C ≤ fourGrp x₁ x₂) (hne : C ≠ ⊥)
    (hinv : ∀ c ∈ C, rho * c * rho⁻¹ ∈ C) : C = fourGrp x₁ x₂ := by
  obtain ⟨c, hcC, hc1⟩ := Or.resolve_left (Subgroup.bot_or_exists_ne_one C) hne
  have hc'C : rho * c * rho⁻¹ ∈ C := hinv c hcC
  have hc'1 : rho * c * rho⁻¹ ≠ 1 := by
    intro h
    apply hc1
    calc c = rho⁻¹ * (rho * c * rho⁻¹) * rho := by group
      _ = rho⁻¹ * 1 * rho := by rw [h]
      _ = 1 := by group
  have hc'ne : rho * c * rho⁻¹ ≠ c := by
    intro h
    have hcomm : c * rho = rho * c := by
      have h2 : rho * c = c * rho := by
        calc rho * c = rho * c * rho⁻¹ * rho := by group
          _ = c * rho := by rw [h]
      exact h2.symm
    have hmem : c ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({rho} : Set G) :=
      ⟨hc.V_le_Q (hCV hcC), Subgroup.mem_centralizer_singleton_iff.mpr hcomm⟩
    rw [hc.CQ_rho] at hmem
    exact hc1 (mem_bot.mp hmem)
  have hsub : ({1, c, rho * c * rho⁻¹} : Set G) ⊆ (C : Set G) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact C.one_mem
    · exact hcC
    · exact hc'C
  have hncard3 : ({1, c, rho * c * rho⁻¹} : Set G).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (show (1 : G) ∉ ({c, rho * c * rho⁻¹} : Set G) by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨Ne.symm hc1, Ne.symm hc'1⟩),
      Set.ncard_insert_of_notMem (show c ∉ ({rho * c * rho⁻¹} : Set G) by
          simp only [Set.mem_singleton_iff]
          exact Ne.symm hc'ne),
      Set.ncard_singleton]
  have hle : 3 ≤ Nat.card C := by
    have h := Set.ncard_le_ncard hsub
    rw [hncard3] at h
    rw [← Nat.card_coe_set_eq] at h
    exact h
  have hdvd : Nat.card C ∣ 4 := by
    have h := Subgroup.card_dvd_of_le hCV
    rwa [card_fourGrp hc] at h
  have hcardC : Nat.card C = 4 := by
    have hle4 : Nat.card C ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases Nat.card C <;> omega
  apply Subgroup.eq_of_le_of_card_ge hCV
  rw [card_fourGrp hc, hcardC]

theorem comm_ne_bot {s : G} (hs : s = t ∨ s = tau ∨ s = t * tau)
    (hmove : ∃ m ∈ ctxM t tau x₁ x₂, m * s * m⁻¹ ≠ s) :
    ⁅ctxQ t tau x₁ x₂ rho, zpowers s⁆ ≠ ⊥ := by
  by_contra hbot
  have hsf := s_facts hc hs
  have hcentral : ctxM t tau x₁ x₂ ≤ centralizer ({s} : Set G) := by
    rw [hc.M_eq]
    refine sup_le ?_ ?_
    · rw [hc.O_eq_Q]
      refine sup_le ?_ ?_
      · intro b hb
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hmem := Subgroup.commutator_mem_commutator hb (Subgroup.mem_zpowers s)
        rw [hbot, Subgroup.mem_bot, commutatorElement_def] at hmem
        calc b * s = b * s * b⁻¹ * s⁻¹ * (s * b) := by group
          _ = 1 * (s * b) := by rw [hmem]
          _ = s * b := by rw [one_mul]
      · intro u hu
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hsf.2.2.1 u hu).symm
    · rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hsf.2.2.2.1
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hsf.2.2.2.2
  obtain ⟨m, hmM, hm⟩ := hmove
  have hms : s * m = m * s :=
    Subgroup.mem_centralizer_iff.mp (hcentral hmM) s (Set.mem_singleton s)
  exact hm (by rw [← hms]; group)

theorem comm_eq_V {s : G} (hs : s = t ∨ s = tau ∨ s = t * tau)
    (hmove : ∃ m ∈ ctxM t tau x₁ x₂, m * s * m⁻¹ ≠ s) :
    ⁅ctxQ t tau x₁ x₂ rho, zpowers s⁆ = fourGrp x₁ x₂ := by
  have hsf := s_facts hc hs
  exact eq_V_of_rho_inv hc (comm_le_V hc hsf.1 hsf.2.1)
    (comm_ne_bot hc hs hmove) (comm_rho_inv hc hsf.2.2.2.1)

theorem t_moved : ∃ m ∈ ctxM t tau x₁ x₂, m * t * m⁻¹ ≠ t := by
  have hy : x₁ ^ 2 ∈ fourGrp x₁ x₂ := subset_closure (by simp)
  have hty : t * (x₁ ^ 2) ∈ t • (fourGrp x₁ x₂ : Set G) :=
    ⟨x₁ ^ 2, hy, by simp [smul_eq_mul]⟩
  rw [← hc.tM] at hty
  obtain ⟨m, hmM, hm⟩ := hty
  refine ⟨m, hmM, ?_⟩
  intro heq
  apply hc.y_ne_one
  have hcontra : t * (x₁ ^ 2) = t := by rw [← hm, heq]
  exact mul_left_cancel (a := t) (by rw [hcontra, mul_one])

theorem tau_moved : ∃ m ∈ ctxM t tau x₁ x₂, m * tau * m⁻¹ ≠ tau := by
  have hy : x₁ ^ 2 ∈ fourGrp x₁ x₂ := subset_closure (by simp)
  have hty : tau * (x₁ ^ 2) ∈ tau • (fourGrp x₁ x₂ : Set G) :=
    ⟨x₁ ^ 2, hy, by simp [smul_eq_mul]⟩
  rw [← hc.tauM] at hty
  obtain ⟨m, hmM, hm⟩ := hty
  refine ⟨m, hmM, ?_⟩
  intro heq
  apply hc.y_ne_one
  have hcontra : tau * (x₁ ^ 2) = tau := by rw [← hm, heq]
  exact mul_left_cancel (a := tau) (by rw [hcontra, mul_one])

theorem ttau_moved : ∃ m ∈ ctxM t tau x₁ x₂, m * (t * tau) * m⁻¹ ≠ t * tau := by
  have hy : x₁ ^ 2 ∈ fourGrp x₁ x₂ := subset_closure (by simp)
  have hty : (t * tau) * (x₁ ^ 2) ∈ (t * tau) • (fourGrp x₁ x₂ : Set G) :=
    ⟨x₁ ^ 2, hy, by simp [smul_eq_mul]⟩
  rw [← hc.ttauM] at hty
  obtain ⟨m, hmM, hm⟩ := hty
  refine ⟨m, hmM, ?_⟩
  intro heq
  apply hc.y_ne_one
  have hcontra : (t * tau) * (x₁ ^ 2) = t * tau := by rw [← hm, heq]
  exact mul_left_cancel (a := t * tau) (by rw [hcontra, mul_one])

theorem comm_t_eq : ⁅ctxQ t tau x₁ x₂ rho, zpowers t⁆ = fourGrp x₁ x₂ :=
  comm_eq_V hc (Or.inl rfl) (t_moved hc)

theorem comm_tau_eq : ⁅ctxQ t tau x₁ x₂ rho, zpowers tau⁆ = fourGrp x₁ x₂ :=
  comm_eq_V hc (Or.inr (Or.inl rfl)) (tau_moved hc)

theorem comm_ttau_eq : ⁅ctxQ t tau x₁ x₂ rho, zpowers (t * tau)⁆ = fourGrp x₁ x₂ :=
  comm_eq_V hc (Or.inr (Or.inr rfl)) (ttau_moved hc)

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
