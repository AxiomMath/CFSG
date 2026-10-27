module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbE17a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17FL
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbA17g
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbF17E32

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

theorem l17_fl_ctx (hc : Ctx17 t L S x₁ x₂ lam rho tau om 𝒮) {g : G} (hg2 : g * g = 1)
    (hgK : g ∈ ctxK t tau x₁ x₂ rho)
    (hcY : Nat.card {y : G // y ∈ ctxYq t tau x₁ x₂ rho ∧ g * y = y * g} ≤ 4) :
    ∀ x ∈ ctxP t tau x₁ x₂ rho, (g * x) * (g * x) = 1 →
      ∃ p ∈ ctxP t tau x₁ x₂ rho, g * x = p * g * p⁻¹ := by
  have hcard : Nat.card (ctxP t tau x₁ x₂ rho) = 256 := by
    rw [(l17_card_P hc).1]
    norm_num
  have hYP : ctxYq t tau x₁ x₂ rho ≤ ctxP t tau x₁ x₂ rho :=
    ctxYq_le_ctxQ.trans (l17_Q_le_P hc.toCtx13)
  exact fl_group (P := ctxP t tau x₁ x₂ rho) (Y := ctxYq t tau x₁ x₂ rho)
    (l17_P_comm hc) (l17_exp_four hc) hYP (l17_omega hc) hcard hg2
    (fun x hx => (l17_P_normal hc.toCtx13).2 g hgK x hx) hcY

theorem l17_card_CY_t (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    Nat.card {y : G // y ∈ ctxYq t tau x₁ x₂ rho ∧ t * y = y * t} ≤ 4 := by
  let f : {y : G // y ∈ ctxYq t tau x₁ x₂ rho ∧ t * y = y * t} →
      ↥(fourGrp x₁ x₂) := fun y =>
    ⟨y.1, by
      have hmem : y.1 ∈ ctxYq t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) :=
        Subgroup.mem_inf.mpr
          ⟨y.2.1, Subgroup.mem_centralizer_singleton_iff.mpr y.2.2.symm⟩
      rwa [hc.Y_cent.1] at hmem⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have h : (a.1 : G) = b.1 := by
      simpa only using congrArg (fun z : ↥(fourGrp x₁ x₂) => (z : G)) hab
    exact Subtype.ext h
  calc Nat.card {y : G // y ∈ ctxYq t tau x₁ x₂ rho ∧ t * y = y * t}
      ≤ Nat.card ↥(fourGrp x₁ x₂) := Nat.card_le_card_of_injective f hinj
    _ = 4 := l17_card_V hc

theorem l17_card_CY_ttau (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    Nat.card {y : G // y ∈ ctxYq t tau x₁ x₂ rho ∧ (t * tau) * y = y * (t * tau)} ≤ 4 := by
  let f : {y : G // y ∈ ctxYq t tau x₁ x₂ rho ∧ (t * tau) * y = y * (t * tau)} →
      ↥(fourGrp x₁ x₂) := fun y =>
    ⟨y.1, by
      have hmem : y.1 ∈ ctxYq t tau x₁ x₂ rho ⊓ centralizer ({t * tau} : Set G) :=
        Subgroup.mem_inf.mpr
          ⟨y.2.1, Subgroup.mem_centralizer_singleton_iff.mpr y.2.2.symm⟩
      rwa [hc.Y_cent.2] at hmem⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have h : (a.1 : G) = b.1 := by
      simpa only using congrArg (fun z : ↥(fourGrp x₁ x₂) => (z : G)) hab
    exact Subtype.ext h
  calc Nat.card {y : G // y ∈ ctxYq t tau x₁ x₂ rho ∧ (t * tau) * y = y * (t * tau)}
      ≤ Nat.card ↥(fourGrp x₁ x₂) := Nat.card_le_card_of_injective f hinj
    _ = 4 := l17_card_V hc

theorem l17_card_CY_lam_a (hc : Ctx13 t L S x₁ x₂ lam rho tau om) {a : G}
    (ha : a ∈ closure ({tau, om} : Set G)) :
    Nat.card {y : G // y ∈ ctxYq t tau x₁ x₂ rho ∧ (lam * a) * y = y * (lam * a)} ≤ 4 := by
  have haE0 : a ∈ ctxE0 t tau x₁ x₂ rho om := Subgroup.mem_sup_right ha
  have haC : a ∈ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) :=
    l17_E0_le_cent hc haE0
  let f : {y : G // y ∈ ctxYq t tau x₁ x₂ rho ∧ (lam * a) * y = y * (lam * a)} →
      ↥(ctxYq t tau x₁ x₂ rho ⊓ centralizer ({lam} : Set G)) := fun y =>
    ⟨y.1, Subgroup.mem_inf.mpr ⟨y.2.1, Subgroup.mem_centralizer_singleton_iff.mpr (by
      have hay : a * y.1 = y.1 * a :=
        (Subgroup.mem_centralizer_iff.mp haC y.1 y.2.1).symm
      have h1 : lam * y.1 * a = y.1 * lam * a := by
        calc lam * y.1 * a = lam * (y.1 * a) := by group
          _ = lam * (a * y.1) := by rw [← hay]
          _ = lam * a * y.1 := by group
          _ = y.1 * (lam * a) := y.2.2
          _ = y.1 * lam * a := by group
      exact (mul_right_cancel h1).symm)⟩⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have h : (a.1 : G) = b.1 := by
      simpa only using congrArg
        (fun z : ↥(ctxYq t tau x₁ x₂ rho ⊓ centralizer ({lam} : Set G)) => (z : G)) hab
    exact Subtype.ext h
  calc Nat.card {y : G // y ∈ ctxYq t tau x₁ x₂ rho ∧ (lam * a) * y = y * (lam * a)}
      ≤ Nat.card ↥(ctxYq t tau x₁ x₂ rho ⊓ centralizer ({lam} : Set G)) :=
        Nat.card_le_card_of_injective f hinj
    _ = 4 := l17_card_CY_lam hc

theorem l17_F1 (hc : Ctx13 t L S x₁ x₂ lam rho tau om) (g : G) :
    g * t * g⁻¹ ∉ ctxE0 t tau x₁ x₂ rho om := by
  intro hmem
  have hu2 : (g * t * g⁻¹) * (g * t * g⁻¹) = 1 := conj_t_sq hc g
  have huC : g * t * g⁻¹ ∈ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) :=
    l17_E0_le_cent hc hmem
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

theorem l17_F2 (hc : Ctx17 t L S x₁ x₂ lam rho tau om 𝒮) (g : G) {e : G}
    (he : e ∈ ctxE0 t tau x₁ x₂ rho om) : g * t * g⁻¹ ≠ lam * e := by
  intro hge
  obtain ⟨p, hpP, a, haCl, rfl⟩ := (l17_mem_E0 hc.toCtx13).mp he
  obtain ⟨ht2, ht1, hom2, htau2, htau_not, ht_tau, hom_t⟩ := ctx13_relations hc.toCtx13
  have hom_tau : om * tau = tau * om := om_tau_comm ht2 hom2 htau2 ht_tau hom_t
  have htau_om : tau * om = om * tau := hom_tau.symm
  have htau2' : tau * tau = 1 := by rw [← pow_two]; exact htau2
  have hom2' : om * om = 1 := by rw [← pow_two]; exact hom2
  have ha_cases := (mem_closure_pair_of_invol htau2' hom2' htau_om).mp haCl
  have haa : a * a = 1 := by
    rcases ha_cases with rfl | rfl | rfl | rfl
    · simp
    · exact htau2'
    · exact hom2'
    · calc (tau * om) * (tau * om) = tau * (om * tau) * om := by group
        _ = tau * (tau * om) * om := by rw [hom_tau]
        _ = (tau * tau) * (om * om) := by group
        _ = 1 := by rw [htau2', hom2', one_mul]
  have haCent : a ∈ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) :=
    l17_E0_le_cent hc.toCtx13 (Subgroup.mem_sup_right haCl)
  obtain ⟨htK, htauK, homK, hlamK, hrhoK⟩ := l17_mem_K hc.toCtx13
  have haK : a ∈ ctxK t tau x₁ x₂ rho := by
    rcases ha_cases with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact htauK
    · exact homK
    · exact (ctxK t tau x₁ x₂ rho).mul_mem htauK homK
  have haInvK : a⁻¹ ∈ ctxK t tau x₁ x₂ rho := (ctxK t tau x₁ x₂ rho).inv_mem haK
  have hxP : a⁻¹ * p * a ∈ ctxP t tau x₁ x₂ rho := by
    have := (l17_P_normal hc.toCtx13).2 a⁻¹ haInvK p hpP
    simpa using this
  have hlam2 : lam ^ 2 = 1 := (ctx13_lam_facts hc.toCtx13).1
  have hlam2' : lam * lam = 1 := by rw [← pow_two]; exact hlam2
  have hlt : lam * tau = tau * lam := (l17_lam_comm hc.toCtx13).2.1
  have hlo : lam * om = om * lam := (l17_lam_comm hc.toCtx13).2.2
  have hlam_a_comm : lam * a = a * lam := by
    rcases ha_cases with rfl | rfl | rfl | rfl
    · simp
    · exact hlt
    · exact hlo
    · calc lam * (tau * om) = (lam * tau) * om := by group
        _ = (tau * lam) * om := by rw [hlt]
        _ = tau * (lam * om) := by group
        _ = tau * (om * lam) := by rw [hlo]
        _ = (tau * om) * lam := by group
  have hcomm_a : a * lam = lam * a := hlam_a_comm.symm
  have hg0sq : (lam * a) * (lam * a) = 1 := by
    calc (lam * a) * (lam * a) = lam * (a * lam) * a := by group
      _ = lam * (lam * a) * a := by rw [hcomm_a]
      _ = (lam * lam) * (a * a) := by group
      _ = 1 := by rw [hlam2', haa, one_mul]
  have hg0K : lam * a ∈ ctxK t tau x₁ x₂ rho :=
    (ctxK t tau x₁ x₂ rho).mul_mem hlamK haK
  have hg0x : (lam * a) * (a⁻¹ * p * a) = g * t * g⁻¹ := by
    calc (lam * a) * (a⁻¹ * p * a) = lam * p * a := by group
      _ = lam * (p * a) := by group
      _ = g * t * g⁻¹ := hge.symm
  have hu2 : (g * t * g⁻¹) * (g * t * g⁻¹) = 1 := conj_t_sq hc.toCtx13 g
  have hg0xsq : ((lam * a) * (a⁻¹ * p * a)) * ((lam * a) * (a⁻¹ * p * a)) = 1 := by
    rw [hg0x]; exact hu2
  have hcY : Nat.card {y : G // y ∈ ctxYq t tau x₁ x₂ rho ∧ (lam * a) * y = y * (lam * a)} ≤ 4 :=
    l17_card_CY_lam_a hc.toCtx13 haCl
  obtain ⟨p', hp'P, hp'eq⟩ :=
    l17_fl_ctx hc hg0sq hg0K hcY (a⁻¹ * p * a) hxP hg0xsq
  have h1 : p' * (lam * a) * p'⁻¹ = g * t * g⁻¹ := by rw [← hp'eq, hg0x]
  have hconj : (p'⁻¹ * g) * t * (p'⁻¹ * g)⁻¹ = lam * a := by
    calc (p'⁻¹ * g) * t * (p'⁻¹ * g)⁻¹ = p'⁻¹ * (g * t * g⁻¹) * p' := by group
      _ = p'⁻¹ * (p' * (lam * a) * p'⁻¹) * p' := by rw [← h1]
      _ = lam * a := by group
  obtain ⟨B, hclB, hBe, hB32⟩ := l17_E32 hc.toCtx13
  have hlamB : lam ∈ closure ({tau, om, lam} : Set G) := Subgroup.subset_closure (by simp)
  have haB : a ∈ closure ({tau, om, lam} : Set G) :=
    Subgroup.closure_mono (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      tauto) haCl
  have hlam_a_B : lam * a ∈ B := B.mul_mem (hclB hlamB) (hclB haB)
  have hBcent : B ≤ centralizer ({lam * a} : Set G) := by
    intro x hx
    haveI : IsMulCommutative ↥B := hBe.1
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥B) (⟨lam * a, hlam_a_B⟩ : ↥B)))
  have hAc : B ≤ centralizer ({(p'⁻¹ * g) * t * (p'⁻¹ * g)⁻¹} : Set G) := by
    rw [hconj]
    exact hBcent
  have hbound : Nat.card B ≤ 16 :=
    c17_card_elemAbelian_conj_le (hc := hc.toCtx11.toCtx10) (g := p'⁻¹ * g) hAc hBe
  omega

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
