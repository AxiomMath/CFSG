module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13i

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G}

theorem c13_t_cent_B (hc : Ctx11 t L S x₁ x₂ lam rho tau) :
    ∀ b ∈ baseGrp x₁ x₂, t * b * t⁻¹ = b := by
  intro b hb
  have hB_le_C : baseGrp x₁ x₂ ≤ centralizer ({t} : Set G) := by
    rw [← l12_CQ_t hc]
    exact inf_le_right
  have hbt : b * t = t * b := Subgroup.mem_centralizer_singleton_iff.mp (hB_le_C hb)
  rw [← hbt]
  group

theorem c13_ttau_data (hc : Ctx13A t L S x₁ x₂ lam rho tau om) :
    t * tau ∈ ctxM t tau x₁ x₂ ∧ (t * tau) * (t * tau) = 1 := by
  have ht := c13_t_data hc
  have htau := c13_tau_data hc
  refine ⟨Subgroup.mul_mem _ ht.1 htau.1, ?_⟩
  have htt : t * tau = tau * t :=
    (S4A.mem_invCent_iff.mp (hc.le_invCent hc.tau_mem)).symm
  calc (t * tau) * (t * tau) = t * (tau * t) * tau := by group
    _ = t * (t * tau) * tau := by rw [← htt]
    _ = (t * t) * (tau * tau) := by group
    _ = 1 := by rw [ht.2.1, htau.2.1, mul_one]

theorem c13_Q_B_V' (hc : Ctx13C t L S x₁ x₂ lam rho tau om) {v₀ : G}
    (hv₀Y : v₀ ∈ ctxYq t tau x₁ x₂ rho) (hv₀V : v₀ ∉ fourGrp x₁ x₂)
    (hσ : (lam * t) * v₀ * (lam * t)⁻¹ = v₀) :
    ctxQ t tau x₁ x₂ rho = baseGrp x₁ x₂ ⊔ orbitGrp rho v₀ ∧
      baseGrp x₁ x₂ ⊓ orbitGrp rho v₀ = ⊥ := by
  obtain ⟨hle, -, -, -, -, hinf, hsup, -⟩ := c13_V'_props hc hv₀Y hv₀V hσ
  obtain ⟨hBY, hQ⟩ := c13_Q_eq_sup hc.toCtx13B
  have hVB : fourGrp x₁ x₂ ≤ baseGrp x₁ x₂ := by
    rw [← hBY]
    exact inf_le_left
  have hBinfV' : baseGrp x₁ x₂ ⊓ orbitGrp rho v₀ = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    rw [Subgroup.mem_inf] at hx
    have hxY : x ∈ ctxYq t tau x₁ x₂ rho := hle hx.2
    have hxV : x ∈ fourGrp x₁ x₂ := by
      have h : x ∈ baseGrp x₁ x₂ ⊓ ctxYq t tau x₁ x₂ rho := ⟨hx.1, hxY⟩
      rwa [hBY] at h
    have hxbot : x ∈ orbitGrp rho v₀ ⊓ fourGrp x₁ x₂ := ⟨hx.2, hxV⟩
    rw [hinf] at hxbot
    exact Subgroup.mem_bot.mp hxbot
  refine ⟨?_, hBinfV'⟩
  apply le_antisymm
  · calc ctxQ t tau x₁ x₂ rho = baseGrp x₁ x₂ ⊔ ctxYq t tau x₁ x₂ rho := hQ
      _ = baseGrp x₁ x₂ ⊔ (fourGrp x₁ x₂ ⊔ orbitGrp rho v₀) := by rw [← hsup]
      _ ≤ baseGrp x₁ x₂ ⊔ orbitGrp rho v₀ :=
          sup_le le_sup_left (sup_le (hVB.trans le_sup_left) le_sup_right)
  · exact sup_le hc.base_le_Q (hle.trans ctxYq_le_ctxQ)

theorem c13_t_triv_QV (hc : Ctx13C t L S x₁ x₂ lam rho tau om) :
    ∀ q ∈ ctxQ t tau x₁ x₂ rho, q⁻¹ * (t * q * t⁻¹) ∈ fourGrp x₁ x₂ := by
  intro q hq
  obtain ⟨-, hQ⟩ := c13_Q_eq_sup hc.toCtx13B
  have hBY_comm : ∀ h ∈ baseGrp x₁ x₂, ∀ k ∈ ctxYq t tau x₁ x₂ rho, h * k = k * h :=
    fun h hh k hk => hc.Q_comm h (hc.base_le_Q hh) k (ctxYq_le_ctxQ hk)
  have hsplit : q ∈ baseGrp x₁ x₂ ⊔ ctxYq t tau x₁ x₂ rho := by
    rw [← hQ]
    exact hq
  obtain ⟨b, hbB, a, haY, hba⟩ := exists_mul_of_sup hBY_comm hsplit
  have ht := c13_t_data hc.toCtx13A
  have htb : t * b * t⁻¹ = b := c13_t_cent_B hc.toCtx11 b hbB
  have htaV : a⁻¹ * (t * a * t⁻¹) ∈ fourGrp x₁ x₂ :=
    c13_triv_YV hc.toCtx13B ht.1 ht.2.1 ht.2.2 a haY
  have hkey : t * (b * a) * t⁻¹ = b * (t * a * t⁻¹) := by
    calc t * (b * a) * t⁻¹ = (t * b * t⁻¹) * (t * a * t⁻¹) := by group
      _ = b * (t * a * t⁻¹) := by rw [htb]
  rw [hba, hkey]
  convert htaV using 1
  group

theorem c13_mem_CQ_ttau (hc : Ctx13C t L S x₁ x₂ lam rho tau om) {q : G}
    (hq : q ∈ ctxQ t tau x₁ x₂ rho) :
    q ∈ centralizer ({t * tau} : Set G) ↔ t * q * t⁻¹ = q⁻¹ := by
  have ht2 : t * t = 1 := (c13_t_data hc.toCtx13A).2.1
  have hconjA : ∀ x : G, t * (x * t) * t = t * x := by
    intro x
    rw [show t * (x * t) * t = t * x * (t * t) by group, ht2, mul_one]
  have hconjB : ∀ x : G, t * (t * x) * t = x * t := by
    intro x
    rw [show t * (t * x) * t = (t * t) * x * t by group, ht2, one_mul]
  have htauq : tau * q = q⁻¹ * tau := by
    have h := hc.tau_inv_Q q hq
    calc tau * q = (tau * q * tau⁻¹) * tau := by group
      _ = q⁻¹ * tau := by rw [h]
  constructor
  · intro hmem
    have hqt : q * (t * tau) = (t * tau) * q :=
      Subgroup.mem_centralizer_singleton_iff.mp hmem
    have hkey : q * t = t * q⁻¹ := by
      have h : q * t * tau = t * q⁻¹ * tau := by
        calc q * t * tau = q * (t * tau) := by group
          _ = (t * tau) * q := hqt
          _ = t * (tau * q) := by group
          _ = t * (q⁻¹ * tau) := by rw [htauq]
          _ = t * q⁻¹ * tau := by group
      exact mul_right_cancel h
    have hgoal : t * q = q⁻¹ * t := by
      have h := congrArg (fun x => t * x * t) hkey
      rwa [hconjA q, hconjB q⁻¹] at h
    rw [hgoal]
    group
  · intro h
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have h2 : t * q = q⁻¹ * t := by
      calc t * q = (t * q * t⁻¹) * t := by group
        _ = q⁻¹ * t := by rw [h]
    have hkey : q * t = t * q⁻¹ := by
      have hh := congrArg (fun x => t * x * t) h2
      rwa [hconjB q, hconjA q⁻¹] at hh
    calc q * (t * tau) = q * t * tau := by group
      _ = t * q⁻¹ * tau := by rw [hkey]
      _ = t * (q⁻¹ * tau) := by group
      _ = t * (tau * q) := by rw [htauq.symm]
      _ = (t * tau) * q := by group

theorem c13_card_CQ_ttau (hc : Ctx13C t L S x₁ x₂ lam rho tau om) :
    Nat.card ↥(ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * tau} : Set G)) = 16 := by
  have hg2 : (t * tau) * (t * tau) = 1 := (c13_ttau_data hc.toCtx13A).2
  have hgM : t * tau ∈ ctxM t tau x₁ x₂ := (c13_ttau_data hc.toCtx13A).1
  have hgQ : ∀ a ∈ ctxQ t tau x₁ x₂ rho,
      (t * tau) * a * (t * tau)⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
    fun a ha => hc.normal_Q.2 (t * tau) hgM a ha
  obtain ⟨hmem, hcard⟩ := comm_zpowers_inv (A := ctxQ t tau x₁ x₂ rho) hc.Q_comm hg2 hgQ
  have hkey : ∀ a ∈ ctxQ t tau x₁ x₂ rho,
      a * (t * tau) * a⁻¹ * (t * tau)⁻¹ = a * (t * a * t⁻¹) := by
    intro a ha
    have htau : tau * a⁻¹ * tau⁻¹ = a := by
      have h := hc.tau_inv_Q a⁻¹ (Subgroup.inv_mem _ ha)
      simpa using h
    rw [mul_inv_rev]
    calc a * (t * tau) * a⁻¹ * (tau⁻¹ * t⁻¹)
        = a * t * (tau * a⁻¹ * tau⁻¹) * t⁻¹ := by group
      _ = a * t * a * t⁻¹ := by rw [htau]
      _ = a * (t * a * t⁻¹) := by group
  have hle : ⁅ctxQ t tau x₁ x₂ rho, zpowers (t * tau)⁆ ≤ fourGrp x₁ x₂ := by
    intro n hn
    obtain ⟨a, ha, rfl⟩ := (hmem n).mp hn
    rw [hkey a ha]
    have h1 : a * (t * a * t⁻¹) = a ^ 2 * (a⁻¹ * (t * a * t⁻¹)) := by group
    rw [h1]
    exact Subgroup.mul_mem _ (hc.sq_V a ha) (c13_t_triv_QV hc a ha)
  have hge : fourGrp x₁ x₂ ≤ ⁅ctxQ t tau x₁ x₂ rho, zpowers (t * tau)⁆ := by
    rw [fourGrp, Subgroup.closure_le]
    intro v hv
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    have hx1B : x₁ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
    have hx2B : x₂ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
    rcases hv with rfl | rfl
    · refine (hmem _).mpr ⟨x₁, hc.base_le_Q hx1B, ?_⟩
      rw [hkey x₁ (hc.base_le_Q hx1B)]
      have h := c13_t_cent_B hc.toCtx11 x₁ hx1B
      rw [h, ← pow_two]
    · refine (hmem _).mpr ⟨x₁ * x₂, hc.base_le_Q (Subgroup.mul_mem _ hx1B hx2B), ?_⟩
      rw [hkey (x₁ * x₂) (hc.base_le_Q (Subgroup.mul_mem _ hx1B hx2B))]
      have h := c13_t_cent_B hc.toCtx11 (x₁ * x₂) (Subgroup.mul_mem _ hx1B hx2B)
      rw [h, ← pow_two]
  have hEq : ⁅ctxQ t tau x₁ x₂ rho, zpowers (t * tau)⁆ = fourGrp x₁ x₂ :=
    le_antisymm hle hge
  rw [hEq, hc.wreath.fourGrp_eq_omega.2.2, l12_card_Q hc.toCtx11] at hcard
  have h64 : (2 : ℕ) ^ 6 = 4 * 16 := by norm_num
  rw [h64] at hcard
  omega

theorem c13_CQ_ttau (hc : Ctx13C t L S x₁ x₂ lam rho tau om) {v₀ v₂ : G}
    (hv₀Y : v₀ ∈ ctxYq t tau x₁ x₂ rho) (hv₀V : v₀ ∉ fourGrp x₁ x₂)
    (hσ : (lam * t) * v₀ * (lam * t)⁻¹ = v₀) (hv₂ : v₂ ∈ orbitGrp rho v₀)
    (ht : t * v₂ * t⁻¹ = v₂ * x₁ ^ 2) :
    ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * tau} : Set G) =
      closure ({x₁ * v₂, x₂ * v₀ * v₂} : Set G) := by
  obtain ⟨hleY, -, hcardV', -, -, -, hsupY, -⟩ := c13_V'_props hc hv₀Y hv₀V hσ
  have hv₂Y : v₂ ∈ ctxYq t tau x₁ x₂ rho := hleY hv₂
  have hv₀V' : v₀ ∈ orbitGrp rho v₀ := Subgroup.subset_closure (by simp)
  have hv₂2 : v₂ * v₂ = 1 := by
    have h := (mem_ctxYq_iff hc.q_iso v₂).mp hv₂Y
    simpa [pow_two] using h.2
  have hv₂i : v₂⁻¹ = v₂ := inv_eq_of_mul_eq_one_right hv₂2
  have hv₀2 : v₀ * v₀ = 1 := by
    have h := (mem_ctxYq_iff hc.q_iso v₀).mp hv₀Y
    simpa [pow_two] using h.2
  have hv₀i : v₀⁻¹ = v₀ := inv_eq_of_mul_eq_one_right hv₀2
  have hx1B : x₁ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hx2B : x₂ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hx1Q : x₁ ∈ ctxQ t tau x₁ x₂ rho := hc.base_le_Q hx1B
  have hx2Q : x₂ ∈ ctxQ t tau x₁ x₂ rho := hc.base_le_Q hx2B
  have hv₀Q : v₀ ∈ ctxQ t tau x₁ x₂ rho := ctxYq_le_ctxQ hv₀Y
  have hv₂Q : v₂ ∈ ctxQ t tau x₁ x₂ rho := ctxYq_le_ctxQ hv₂Y
  have hyQ : x₁ ^ 2 ∈ ctxQ t tau x₁ x₂ rho := Subgroup.pow_mem _ hx1Q 2
  have hzQ : (x₁ * x₂) ^ 2 ∈ ctxQ t tau x₁ x₂ rho :=
    Subgroup.pow_mem _ (Subgroup.mul_mem _ hx1Q hx2Q) 2
  have htx1 : t * x₁ * t⁻¹ = x₁ := c13_t_cent_B hc.toCtx11 x₁ hx1B
  have htx2 : t * x₂ * t⁻¹ = x₂ := c13_t_cent_B hc.toCtx11 x₂ hx2B
  have hv0t : t * v₀ * t⁻¹ = v₀ * (x₁ * x₂) ^ 2 := c13_v0_t hc hv₀Y hv₀V hσ
  have hx1four : x₁ ^ 4 = 1 := by simpa [hc.wreath.ord_x₁] using pow_orderOf_eq_one x₁
  have hx2four : x₂ ^ 4 = 1 := by simpa [hc.wreath.ord_x₂] using pow_orderOf_eq_one x₂
  have hx1_inv : x₁ ^ 3 = x₁⁻¹ := by
    rw [← mul_eq_one_iff_eq_inv, ← pow_succ]
    simpa using hx1four
  have hx2_inv : x₂ ^ 3 = x₂⁻¹ := by
    rw [← mul_eq_one_iff_eq_inv, ← pow_succ]
    simpa using hx2four
  have key_a : t * (x₁ * v₂) * t⁻¹ = (x₁ * v₂)⁻¹ := by
    calc t * (x₁ * v₂) * t⁻¹ = (t * x₁ * t⁻¹) * (t * v₂ * t⁻¹) := by group
      _ = x₁ * (v₂ * x₁ ^ 2) := by rw [htx1, ht]
      _ = x₁ * (x₁ ^ 2 * v₂) := by rw [hc.Q_comm v₂ hv₂Q (x₁ ^ 2) hyQ]
      _ = x₁ ^ 3 * v₂ := by group
      _ = x₁⁻¹ * v₂ := by rw [hx1_inv]
      _ = (x₁ * v₂)⁻¹ := by
            rw [mul_inv_rev, hv₂i]
            exact hc.Q_comm x₁⁻¹ (Subgroup.inv_mem _ hx1Q) v₂ hv₂Q
  have hzy : (x₁ * x₂) ^ 2 * (x₁ ^ 2) = x₂ ^ 2 := by
    rw [hc.Q_comm ((x₁ * x₂) ^ 2) hzQ (x₁ ^ 2) hyQ, ← hc.wreath.x₂_sq]
  have hR : (x₂ * v₀ * v₂)⁻¹ = v₂ * v₀ * x₂⁻¹ := by
    rw [mul_inv_rev, mul_inv_rev, hv₂i, hv₀i]
    group
  have key_b : t * (x₂ * v₀ * v₂) * t⁻¹ = (x₂ * v₀ * v₂)⁻¹ := by
    haveI : IsMulCommutative ↥(ctxQ t tau x₁ x₂ rho) :=
      IsMulCommutative.of_comm (fun a b => Subtype.ext (hc.Q_comm a.1 a.2 b.1 b.2))
    have hsub : (⟨x₂, hx2Q⟩ : ↥(ctxQ t tau x₁ x₂ rho)) *
          (⟨v₀, hv₀Q⟩ * ⟨(x₁ * x₂) ^ 2, hzQ⟩) * (⟨v₂, hv₂Q⟩ * ⟨x₁ ^ 2, hyQ⟩) =
        (⟨v₂, hv₂Q⟩ : ↥(ctxQ t tau x₁ x₂ rho)) * ⟨v₀, hv₀Q⟩ *
          (⟨x₂, hx2Q⟩ : ↥(ctxQ t tau x₁ x₂ rho))⁻¹ := by
      have hzy' : (⟨(x₁ * x₂) ^ 2, hzQ⟩ : ↥(ctxQ t tau x₁ x₂ rho)) * ⟨x₁ ^ 2, hyQ⟩ =
          (⟨x₂, hx2Q⟩ : ↥(ctxQ t tau x₁ x₂ rho)) ^ 2 := by
        apply Subtype.ext
        exact hzy
      have hx2cube : (⟨x₂, hx2Q⟩ : ↥(ctxQ t tau x₁ x₂ rho)) *
          (⟨x₂, hx2Q⟩ : ↥(ctxQ t tau x₁ x₂ rho)) ^ 2 =
          (⟨x₂, hx2Q⟩ : ↥(ctxQ t tau x₁ x₂ rho))⁻¹ := by
        apply Subtype.ext
        show x₂ * x₂ ^ 2 = x₂⁻¹
        rw [show x₂ * x₂ ^ 2 = x₂ ^ 3 by group, hx2_inv]
      calc (⟨x₂, hx2Q⟩ : ↥(ctxQ t tau x₁ x₂ rho)) *
            (⟨v₀, hv₀Q⟩ * ⟨(x₁ * x₂) ^ 2, hzQ⟩) * (⟨v₂, hv₂Q⟩ * ⟨x₁ ^ 2, hyQ⟩)
          = (⟨v₂, hv₂Q⟩ : ↥(ctxQ t tau x₁ x₂ rho)) *
              (⟨v₀, hv₀Q⟩ * ((⟨x₂, hx2Q⟩ : ↥(ctxQ t tau x₁ x₂ rho)) *
                ((⟨(x₁ * x₂) ^ 2, hzQ⟩ : ↥(ctxQ t tau x₁ x₂ rho)) *
                  ⟨x₁ ^ 2, hyQ⟩))) := by
            ac_rfl
        _ = (⟨v₂, hv₂Q⟩ : ↥(ctxQ t tau x₁ x₂ rho)) *
              (⟨v₀, hv₀Q⟩ * ((⟨x₂, hx2Q⟩ : ↥(ctxQ t tau x₁ x₂ rho)) *
                (⟨x₂, hx2Q⟩ : ↥(ctxQ t tau x₁ x₂ rho)) ^ 2)) := by rw [hzy']
        _ = (⟨v₂, hv₂Q⟩ : ↥(ctxQ t tau x₁ x₂ rho)) *
              (⟨v₀, hv₀Q⟩ * (⟨x₂, hx2Q⟩ : ↥(ctxQ t tau x₁ x₂ rho))⁻¹) := by
            rw [hx2cube]
        _ = (⟨v₂, hv₂Q⟩ : ↥(ctxQ t tau x₁ x₂ rho)) * ⟨v₀, hv₀Q⟩ *
              (⟨x₂, hx2Q⟩ : ↥(ctxQ t tau x₁ x₂ rho))⁻¹ := by group
    have hG : x₂ * (v₀ * (x₁ * x₂) ^ 2) * (v₂ * x₁ ^ 2) = v₂ * v₀ * x₂⁻¹ :=
      congrArg Subtype.val hsub
    calc t * (x₂ * v₀ * v₂) * t⁻¹
        = x₂ * (v₀ * (x₁ * x₂) ^ 2) * (v₂ * x₁ ^ 2) := by
          rw [show t * (x₂ * v₀ * v₂) * t⁻¹ =
            (t * x₂ * t⁻¹) * (t * v₀ * t⁻¹) * (t * v₂ * t⁻¹) by group, htx2, hv0t, ht]
      _ = v₂ * v₀ * x₂⁻¹ := hG
      _ = (x₂ * v₀ * v₂)⁻¹ := hR.symm
  have hgen1Q : x₁ * v₂ ∈ ctxQ t tau x₁ x₂ rho := Subgroup.mul_mem _ hx1Q hv₂Q
  have hgen2Q : x₂ * v₀ * v₂ ∈ ctxQ t tau x₁ x₂ rho :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hx2Q hv₀Q) hv₂Q
  have hH'C : closure ({x₁ * v₂, x₂ * v₀ * v₂} : Set G) ≤
      ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * tau} : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨hgen1Q, (c13_mem_CQ_ttau hc hgen1Q).mpr key_a⟩
    · exact ⟨hgen2Q, (c13_mem_CQ_ttau hc hgen2Q).mpr key_b⟩
  have hH'Q : closure ({x₁ * v₂, x₂ * v₀ * v₂} : Set G) ≤ ctxQ t tau x₁ x₂ rho :=
    hH'C.trans inf_le_left
  have hV'Q : orbitGrp rho v₀ ≤ ctxQ t tau x₁ x₂ rho := hleY.trans ctxYq_le_ctxQ
  have hx1_sup : x₁ ∈ closure ({x₁ * v₂, x₂ * v₀ * v₂} : Set G) ⊔ orbitGrp rho v₀ := by
    have h : (x₁ * v₂) * v₂⁻¹ = x₁ := by rw [hv₂i, mul_assoc, hv₂2, mul_one]
    rw [← h]
    exact Subgroup.mul_mem_sup (Subgroup.subset_closure (by simp))
      (Subgroup.inv_mem _ hv₂)
  have hx2_sup : x₂ ∈ closure ({x₁ * v₂, x₂ * v₀ * v₂} : Set G) ⊔ orbitGrp rho v₀ := by
    have hv0v2V' : v₀ * v₂ ∈ orbitGrp rho v₀ := Subgroup.mul_mem _ hv₀V' hv₂
    have h : (x₂ * v₀ * v₂) * (v₀ * v₂)⁻¹ = x₂ := by
      rw [mul_inv_rev, hv₂i, hv₀i]
      calc (x₂ * v₀ * v₂) * (v₂ * v₀) = x₂ * (v₀ * (v₂ * v₂) * v₀) := by group
        _ = x₂ * (v₀ * v₀) := by rw [hv₂2]; group
        _ = x₂ := by rw [hv₀2, mul_one]
    rw [← h]
    exact Subgroup.mul_mem_sup (Subgroup.subset_closure (by simp))
      (Subgroup.inv_mem _ hv0v2V')
  have hQle : ctxQ t tau x₁ x₂ rho ≤
      closure ({x₁ * v₂, x₂ * v₀ * v₂} : Set G) ⊔ orbitGrp rho v₀ := by
    rw [(c13_Q_B_V' hc hv₀Y hv₀V hσ).1]
    refine sup_le ?_ le_sup_right
    rw [baseGrp, Subgroup.closure_le]
    intro x hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hx1_sup
    · exact hx2_sup
  have hsup_eq : closure ({x₁ * v₂, x₂ * v₀ * v₂} : Set G) ⊔ orbitGrp rho v₀ =
      ctxQ t tau x₁ x₂ rho := le_antisymm (sup_le hH'Q hV'Q) hQle
  have hcomm : ∀ h ∈ closure ({x₁ * v₂, x₂ * v₀ * v₂} : Set G),
      ∀ k ∈ orbitGrp rho v₀, h * k = k * h :=
    fun h hh k hk => hc.Q_comm h (hH'Q hh) k (hV'Q hk)
  have hcardsup := card_sup_mul_card_inf
    (H := closure ({x₁ * v₂, x₂ * v₀ * v₂} : Set G)) (K := orbitGrp rho v₀) hcomm
  rw [hsup_eq, IsZ4Z4E4.card hc.q_iso, hcardV'] at hcardsup
  have hH'card : Nat.card ↥(closure ({x₁ * v₂, x₂ * v₀ * v₂} : Set G)) =
      16 * Nat.card ↥(closure ({x₁ * v₂, x₂ * v₀ * v₂} : Set G) ⊓ orbitGrp rho v₀) := by
    omega
  have hpos : 0 < Nat.card ↥(closure ({x₁ * v₂, x₂ * v₀ * v₂} : Set G) ⊓ orbitGrp rho v₀) := by
    haveI : Nonempty ↥(closure ({x₁ * v₂, x₂ * v₀ * v₂} : Set G) ⊓ orbitGrp rho v₀) :=
      ⟨⟨1, Subgroup.mem_inf.mpr ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩⟩⟩
    exact Nat.card_pos
  have hge : 16 ≤ Nat.card ↥(closure ({x₁ * v₂, x₂ * v₀ * v₂} : Set G)) := by
    rw [hH'card]
    exact Nat.le_mul_of_pos_right 16 hpos
  have hCcard : Nat.card ↥(ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * tau} : Set G)) = 16 :=
    c13_card_CQ_ttau hc
  exact (Subgroup.eq_of_le_of_card_ge hH'C (by rw [hCcard]; exact hge)).symm

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
