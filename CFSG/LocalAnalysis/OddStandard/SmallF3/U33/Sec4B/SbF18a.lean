module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbB18t
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbB18h
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbFL18b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbE17c
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbB18e

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

private lemma isElemAbelian_zpowers_of_mul_self {a : G} (ha : a * a = 1) :
    CFSG.Open.IsElemAbelian 2 (zpowers a) := by
  have ha2 : a ^ 2 = 1 := by rwa [pow_two]
  have haz : a ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast]
    exact ha2
  refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
  · intro x y
    apply Subtype.ext
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp x.2
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp y.2
    show (x : G) * (y : G) = (y : G) * (x : G)
    rw [← hm, ← hn, ← zpow_add, ← zpow_add, add_comm]
  · intro x hx
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hx
    show (x : G) ^ 2 = 1
    rw [← hm, pow_two, ← zpow_add, show m + m = 2 * m by ring, zpow_mul a 2 m, haz, one_zpow]

private lemma conj_t_sq (hc : Ctx13 t L S x₁ x₂ lam rho tau om) (g : G) :
    (g * t * g⁻¹) * (g * t * g⁻¹) = 1 := by
  have ht2 : t * t = 1 := by
    have h := (ctx13_relations hc).1
    simpa [pow_two] using h
  calc (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
    _ = 1 := by rw [ht2]; group

private lemma closure_tauom_sq (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) {a : G}
    (ha : a ∈ closure ({tau, om} : Set G)) : a * a = 1 := by
  obtain ⟨ht2, ht1, hom2, htau2, htau_not, ht_tau, hom_t⟩ := ctx13_relations hc.toCtx13
  have htau2' : tau * tau = 1 := by rw [← pow_two]; exact htau2
  have hom2' : om * om = 1 := by rw [← pow_two]; exact hom2
  have htau_om : tau * om = om * tau := (om_tau_comm ht2 hom2 htau2 ht_tau hom_t).symm
  rcases (mem_closure_pair_of_invol htau2' hom2' htau_om).mp ha with rfl | rfl | rfl | rfl
  · simp
  · exact htau2'
  · exact hom2'
  · calc (tau * om) * (tau * om) = tau * (om * tau) * om := by group
      _ = tau * (tau * om) * om := by rw [htau_om]
      _ = (tau * tau) * (om * om) := by group
      _ = 1 := by rw [htau2', hom2', mul_one]

private lemma closure_tauom_comm_Xi_mem_Y (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮)
    {a : G} (ha : a ∈ closure ({tau, om} : Set G)) {x : G}
    (hx : x ∈ ctxXi t tau x₁ x₂ rho) :
    a * x * a⁻¹ * x⁻¹ ∈ ctxYq t tau x₁ x₂ rho := by
  obtain ⟨ht2, ht1, hom2, htau2, htau_not, ht_tau, hom_t⟩ := ctx13_relations hc.toCtx13
  have htau2' : tau * tau = 1 := by rw [← pow_two]; exact htau2
  have hom2' : om * om = 1 := by rw [← pow_two]; exact hom2
  have htau_om : tau * om = om * tau := (om_tau_comm ht2 hom2 htau2 ht_tau hom_t).symm
  have hτK : tau ∈ ctxK t tau x₁ x₂ rho := (l17_mem_K hc.toCtx13).2.1
  have hτx : tau * x * tau⁻¹ * x⁻¹ ∈ ctxYq t tau x₁ x₂ rho := by
    have h := (ctxYq t tau x₁ x₂ rho).inv_mem (l18_comm_tau_mem_Y hc hx)
    rwa [show (x * tau * x⁻¹ * tau⁻¹)⁻¹ = tau * x * tau⁻¹ * x⁻¹ by group] at h
  have hωx : om * x * om⁻¹ * x⁻¹ ∈ ctxYq t tau x₁ x₂ rho := by
    have h := (ctxYq t tau x₁ x₂ rho).inv_mem (l18_comm_om_mem_Y hc hx)
    rwa [show (x * om * x⁻¹ * om⁻¹)⁻¹ = om * x * om⁻¹ * x⁻¹ by group] at h
  have hτωx : (tau * om) * x * (tau * om)⁻¹ * x⁻¹ ∈ ctxYq t tau x₁ x₂ rho := by
    have hconj : tau * (om * x * om⁻¹ * x⁻¹) * tau⁻¹ ∈ ctxYq t tau x₁ x₂ rho :=
      l17_K_normalizes_Y hc.toCtx13 tau hτK _ hωx
    have hprod := (ctxYq t tau x₁ x₂ rho).mul_mem hconj hτx
    rwa [show tau * (om * x * om⁻¹ * x⁻¹) * tau⁻¹ * (tau * x * tau⁻¹ * x⁻¹)
        = (tau * om) * x * (tau * om)⁻¹ * x⁻¹ by group] at hprod
  rcases (mem_closure_pair_of_invol htau2' hom2' htau_om).mp ha with rfl | rfl | rfl | rfl
  · simp
  · exact hτx
  · exact hωx
  · exact hτωx

private lemma fl18_apply (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) {g : G} (hg2 : g * g = 1)
    (hgK : g ∈ ctxK t tau x₁ x₂ rho)
    (hCY : Nat.card {y : G // y ∈ ctxYq t tau x₁ x₂ rho ∧ g * y = y * g} ≤ 4)
    {D : Subgroup G} (hDΞ : D ≤ ctxXi t tau x₁ x₂ rho)
    (hD : ∀ x ∈ ctxXi t tau x₁ x₂ rho,
      g * x * g⁻¹ * x⁻¹ ∈ ctxYq t tau x₁ x₂ rho → x ∈ D)
    (hDcard : Nat.card D ≤ 64) :
    ∀ x ∈ ctxXi t tau x₁ x₂ rho, (g * x) * (g * x) = 1 →
      ∃ p ∈ ctxXi t tau x₁ x₂ rho, g * x = p * g * p⁻¹ := by
  have hXiC : ctxXi t tau x₁ x₂ rho ≤ ctxCY t tau x₁ x₂ rho := by
    rw [l18_C_eq_Xi_sup hc]
    exact le_sup_left
  have hYc : ∀ y ∈ ctxYq t tau x₁ x₂ rho, ∀ x ∈ ctxXi t tau x₁ x₂ rho,
      x * y = y * x := by
    intro y hy x hx
    have hxcent : x ∈ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) :=
      (Subgroup.mem_inf.mp (hXiC hx)).2
    exact (Subgroup.mem_centralizer_iff.mp hxcent y hy).symm
  have hY2 : ∀ y ∈ ctxYq t tau x₁ x₂ rho, y * y = 1 := by
    intro y hy
    have h := (l17_Y_elem hc.toCtx13).2 y hy
    rwa [pow_two] at h
  exact fl_cls2 (Ξ := ctxXi t tau x₁ x₂ rho) (Y := ctxYq t tau x₁ x₂ rho) (D := D)
    hg2 ((l18_Xi_normal hc.toCtx13).2 g hgK)
    (l17_K_normalizes_Y hc.toCtx13 g hgK)
    (ctxYq_le_ctxQ.trans (l18_Q_le_Xi hc.toCtx13)) hYc hY2
    (l18_Xi_special hc).1 (by rw [l18_card_Xi hc]; norm_num) (l17_card_Y hc.toCtx13)
    hCY hDΞ hD hDcard

theorem l18_mem_C (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) {e : G} :
    e ∈ ctxCY t tau x₁ x₂ rho ↔
      ∃ m ∈ ctxXi t tau x₁ x₂ rho, ∃ a ∈ closure ({tau, om} : Set G), e = m * a := by
  have hKcl : closure ({tau, om} : Set G) ≤ ctxK t tau x₁ x₂ rho := by
    rw [Subgroup.closure_le]
    rintro z (hz : z ∈ ({tau, om} : Set G))
    rcases hz with rfl | rfl
    · exact (l17_mem_K hc.toCtx13).2.1
    · exact (l17_mem_K hc.toCtx13).2.2.1
  have hXN := l18_Xi_normal hc.toCtx13
  rw [l18_C_eq_Xi_sup hc]
  refine mem_sup_iff_of_normalizes (H := ctxXi t tau x₁ x₂ rho)
    (K := closure ({tau, om} : Set G)) ?_
  intro k hk h hh
  exact hXN.2 k (hKcl hk) h hh

theorem l18_F1 (hc : Ctx13 t L S x₁ x₂ lam rho tau om) (g : G) :
    g * t * g⁻¹ ∉ ctxCY t tau x₁ x₂ rho := by
  intro hmem
  have hu2 : (g * t * g⁻¹) * (g * t * g⁻¹) = 1 := conj_t_sq hc g
  have huC : g * t * g⁻¹ ∈ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) :=
    (Subgroup.mem_inf.mp hmem).2
  have hucomm : ∀ y ∈ ctxYq t tau x₁ x₂ rho, y * (g * t * g⁻¹) = (g * t * g⁻¹) * y :=
    fun y hy => Subgroup.mem_centralizer_iff.mp huC y hy
  have huNotY : g * t * g⁻¹ ∉ ctxYq t tau x₁ x₂ rho := l17_tG_not_mem_Y hc g
  have hcomm : ∀ y ∈ ctxYq t tau x₁ x₂ rho,
      ∀ z ∈ zpowers (g * t * g⁻¹), y * z = z * y := by
    intro y hy z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (show Commute y (g * t * g⁻¹) from hucomm y hy).zpow_right k
  let B : Subgroup G := ctxYq t tau x₁ x₂ rho ⊔ zpowers (g * t * g⁻¹)
  have hBe : CFSG.Open.IsElemAbelian 2 B :=
    isElemAbelian_sup (l17_Y_elem hc) (isElemAbelian_zpowers_of_mul_self hu2) hcomm
  have hBcard : Nat.card ↥B = 32 := by
    have hcard := card_sup_zpowers_of_commute (T := ctxYq t tau x₁ x₂ rho)
      (lam := g * t * g⁻¹) (by rw [pow_two]; exact hu2) huNotY hucomm
    have hB : B = ctxYq t tau x₁ x₂ rho ⊔ zpowers (g * t * g⁻¹) := rfl
    rw [hB, hcard, l17_card_Y hc]
  have hBcent : B ≤ centralizer ({g * t * g⁻¹} : Set G) := by
    intro x hx
    have hxu : x * (g * t * g⁻¹) = (g * t * g⁻¹) * x := by
      haveI : IsMulCommutative ↥B := hBe.1
      have huB : g * t * g⁻¹ ∈ B :=
        Subgroup.mem_sup_right (Subgroup.mem_zpowers (g * t * g⁻¹))
      exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥B) (⟨g * t * g⁻¹, huB⟩ : ↥B))
    exact Subgroup.mem_centralizer_singleton_iff.mpr hxu
  have hbound : Nat.card B ≤ 16 :=
    c17_card_elemAbelian_conj_le (hc := hc.toCtx11.toCtx10) (g := g) hBcent hBe
  rw [hBcard] at hbound
  omega

theorem l18_fl_t (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) {x : G}
    (hx : x ∈ ctxXi t tau x₁ x₂ rho) (h2 : (t * x) * (t * x) = 1) :
    ∃ p ∈ ctxXi t tau x₁ x₂ rho, t * x = p * t * p⁻¹ := by
  have ht2 : t * t = 1 := by
    have h := (ctx13_relations hc.toCtx13).1
    rwa [pow_two] at h
  exact fl18_apply hc ht2 (l17_mem_K hc.toCtx13).1 (l17_card_CY_t hc.toCtx13)
    (D := ctxQ t tau x₁ x₂ rho) (l18_Q_le_Xi hc.toCtx13)
    (fun y hy h => l18_Dt_le_Q hc hy h)
    (le_of_eq (IsZ4Z4E4.card hc.q_iso)) x hx h2

theorem l18_fl_ttau (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) {x : G}
    (hx : x ∈ ctxXi t tau x₁ x₂ rho) (h2 : ((t * tau) * x) * ((t * tau) * x) = 1) :
    ∃ p ∈ ctxXi t tau x₁ x₂ rho, (t * tau) * x = p * (t * tau) * p⁻¹ := by
  obtain ⟨ht2, ht1, hom2, htau2, htau_not, ht_tau, hom_t⟩ := ctx13_relations hc.toCtx13
  have ht2' : t * t = 1 := by rw [← pow_two]; exact ht2
  have htau2' : tau * tau = 1 := by rw [← pow_two]; exact htau2
  have htK : t ∈ ctxK t tau x₁ x₂ rho := (l17_mem_K hc.toCtx13).1
  have htauK : tau ∈ ctxK t tau x₁ x₂ rho := (l17_mem_K hc.toCtx13).2.1
  have hg2 : (t * tau) * (t * tau) = 1 := by
    calc (t * tau) * (t * tau) = (t * tau) * (tau * t) := by rw [← ht_tau]
      _ = t * (tau * tau) * t := by group
      _ = 1 := by rw [htau2', mul_one, ht2']
  have hD : ∀ x ∈ ctxXi t tau x₁ x₂ rho,
      (t * tau) * x * (t * tau)⁻¹ * x⁻¹ ∈ ctxYq t tau x₁ x₂ rho →
        x ∈ ctxQ t tau x₁ x₂ rho := by
    intro x hx hmem
    apply l18_Dt_le_Q hc hx
    have hτx : tau * x * tau⁻¹ * x⁻¹ ∈ ctxYq t tau x₁ x₂ rho := by
      have h := (ctxYq t tau x₁ x₂ rho).inv_mem (l18_comm_tau_mem_Y hc hx)
      rwa [show (x * tau * x⁻¹ * tau⁻¹)⁻¹ = tau * x * tau⁻¹ * x⁻¹ by group] at h
    have hconj : t * (tau * x * tau⁻¹ * x⁻¹) * t⁻¹ ∈ ctxYq t tau x₁ x₂ rho :=
      l17_K_normalizes_Y hc.toCtx13 t htK _ hτx
    have hid : (t * tau) * x * (t * tau)⁻¹ * x⁻¹
        = (t * (tau * x * tau⁻¹ * x⁻¹) * t⁻¹) * (t * x * t⁻¹ * x⁻¹) := by group
    have hprod : (t * (tau * x * tau⁻¹ * x⁻¹) * t⁻¹) * (t * x * t⁻¹ * x⁻¹)
        ∈ ctxYq t tau x₁ x₂ rho := by
      rw [← hid]; exact hmem
    have h := (ctxYq t tau x₁ x₂ rho).mul_mem
      ((ctxYq t tau x₁ x₂ rho).inv_mem hconj) hprod
    rwa [show (t * (tau * x * tau⁻¹ * x⁻¹) * t⁻¹)⁻¹ *
        ((t * (tau * x * tau⁻¹ * x⁻¹) * t⁻¹) * (t * x * t⁻¹ * x⁻¹))
        = t * x * t⁻¹ * x⁻¹ by group] at h
  exact fl18_apply hc hg2 ((ctxK t tau x₁ x₂ rho).mul_mem htK htauK)
    (l17_card_CY_ttau hc.toCtx13) (D := ctxQ t tau x₁ x₂ rho) (l18_Q_le_Xi hc.toCtx13)
    hD (le_of_eq (IsZ4Z4E4.card hc.q_iso)) x hx h2

theorem l18_fl_lam (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) {a : G}
    (ha : a ∈ closure ({tau, om} : Set G)) {x : G} (hx : x ∈ ctxXi t tau x₁ x₂ rho)
    (h2 : ((lam * a) * x) * ((lam * a) * x) = 1) :
    ∃ p ∈ ctxXi t tau x₁ x₂ rho, (lam * a) * x = p * (lam * a) * p⁻¹ := by
  obtain ⟨D, hDΞ, hDprop, hDcard⟩ := l18_exists_D_lam hc
  have hlam2 : lam * lam = 1 := by
    have h := (ctx13_lam_facts hc.toCtx13).1
    rwa [pow_two] at h
  have ha2 : a * a = 1 := closure_tauom_sq hc ha
  have hlamK : lam ∈ ctxK t tau x₁ x₂ rho := (l17_mem_K hc.toCtx13).2.2.2.1
  have hKcl : closure ({tau, om} : Set G) ≤ ctxK t tau x₁ x₂ rho := by
    rw [Subgroup.closure_le]
    rintro z (hz : z ∈ ({tau, om} : Set G))
    rcases hz with rfl | rfl
    · exact (l17_mem_K hc.toCtx13).2.1
    · exact (l17_mem_K hc.toCtx13).2.2.1
  have hcomm : a * lam = lam * a := by
    have hcent : closure ({tau, om} : Set G) ≤ centralizer ({lam} : Set G) := by
      rw [Subgroup.closure_le]
      rintro z (hz : z ∈ ({tau, om} : Set G))
      rcases hz with rfl | rfl
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (l17_lam_comm hc.toCtx13).2.1.symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (l17_lam_comm hc.toCtx13).2.2.symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hcent ha)
  have hg2 : (lam * a) * (lam * a) = 1 := by
    calc (lam * a) * (lam * a) = lam * (a * lam) * a := by group
      _ = lam * (lam * a) * a := by rw [hcomm]
      _ = (lam * lam) * (a * a) := by group
      _ = 1 := by rw [hlam2, ha2, mul_one]
  have hD : ∀ x ∈ ctxXi t tau x₁ x₂ rho,
      (lam * a) * x * (lam * a)⁻¹ * x⁻¹ ∈ ctxYq t tau x₁ x₂ rho → x ∈ D := by
    intro x hx hmem
    apply hDprop x hx
    have haxY : a * x * a⁻¹ * x⁻¹ ∈ ctxYq t tau x₁ x₂ rho :=
      closure_tauom_comm_Xi_mem_Y hc ha hx
    have hconj : lam * (a * x * a⁻¹ * x⁻¹) * lam⁻¹ ∈ ctxYq t tau x₁ x₂ rho :=
      l17_K_normalizes_Y hc.toCtx13 lam hlamK _ haxY
    have hid : (lam * a) * x * (lam * a)⁻¹ * x⁻¹
        = (lam * (a * x * a⁻¹ * x⁻¹) * lam⁻¹) * (lam * x * lam⁻¹ * x⁻¹) := by group
    have hprod : (lam * (a * x * a⁻¹ * x⁻¹) * lam⁻¹) * (lam * x * lam⁻¹ * x⁻¹)
        ∈ ctxYq t tau x₁ x₂ rho := by
      rw [← hid]; exact hmem
    have h := (ctxYq t tau x₁ x₂ rho).mul_mem
      ((ctxYq t tau x₁ x₂ rho).inv_mem hconj) hprod
    rwa [show (lam * (a * x * a⁻¹ * x⁻¹) * lam⁻¹)⁻¹ *
        ((lam * (a * x * a⁻¹ * x⁻¹) * lam⁻¹) * (lam * x * lam⁻¹ * x⁻¹))
        = lam * x * lam⁻¹ * x⁻¹ by group] at h
  exact fl18_apply hc hg2 ((ctxK t tau x₁ x₂ rho).mul_mem hlamK (hKcl ha))
    (l17_card_CY_lam_a hc.toCtx13 ha) (D := D) hDΞ hD hDcard x hx h2

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
