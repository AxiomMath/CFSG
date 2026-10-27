module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18Cj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18e
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18c
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP15

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

private lemma k18m_zpow_eq_one_or_self {a : G} (ha : a * a = 1) (m : ℤ) :
    a ^ m = 1 ∨ a ^ m = a := by
  have h2 : a ^ (2 : ℕ) = 1 := by rw [pow_two, ha]
  have hm : a ^ m = a ^ (m % (2 : ℤ)) := zpow_eq_zpow_emod' m h2
  rcases Int.emod_two_eq_zero_or_one m with h | h
  · left; rw [hm, h]; simp
  · right; rw [hm, h]; simp

private lemma k18m_zpowers_sup_le_centralizer_zpowers {a b c : G}
    (ha : a * c = c * a) (hb : b * c = c * b) :
    Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤
      Subgroup.centralizer (Subgroup.zpowers c : Set G) := by
  refine sup_le ?_ ?_
  · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((Commute.zpow_right (show Commute a c from ha) n).eq).symm
  · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((Commute.zpow_right (show Commute b c from hb) n).eq).symm

private lemma k18m_tau_comm_om (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    tau * om = om * tau := by
  have hcent : tau ∈ Subgroup.centralizer (ctxCO t tau x₁ x₂ rho : Set G) := by
    have hmem : tau ∈ (ctxCO t tau x₁ x₂ rho ⊓
        Subgroup.centralizer (ctxCO t tau x₁ x₂ rho : Set G) : Subgroup G) := by
      rw [hc.CO_center]
      exact Subgroup.mem_zpowers tau
    exact hmem.2
  have hom : om ∈ ctxCO t tau x₁ x₂ rho := by
    rw [hc.CO_eq]
    exact Subgroup.subset_closure (by simp)
  exact (Subgroup.mem_centralizer_iff.mp hcent om hom).symm

private lemma k18m_t_om_conj (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    t * om * t⁻¹ = om * tau := by
  have ht2 : t * t = 1 := by
    have := (ctx13_relations hc).1
    simpa [pow_two] using this
  have h1 : om * t * om⁻¹ = t * tau := (ctx13_relations hc).2.2.2.2.2.2
  have h3 : tau * om = om * tau := k18m_tau_comm_om hc
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  rw [htinv]
  have homt : om * t = t * tau * om := by
    have h := congrArg (· * om) h1
    simpa [mul_assoc] using h
  calc t * om * t = t * (om * t) := by group
    _ = t * (t * tau * om) := by rw [homt]
    _ = tau * om := by
        rw [show t * (t * tau * om) = (t * t) * tau * om by group, ht2]
        group
    _ = om * tau := h3

theorem comm_le_of_abelian_mod {N A B : Subgroup G}
    (hN : ∀ g ∈ A ⊔ B, ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (hAA : ∀ a ∈ A, ∀ a' ∈ A, a * a' * a⁻¹ * a'⁻¹ ∈ N)
    (hBB : ∀ b ∈ B, ∀ b' ∈ B, b * b' * b⁻¹ * b'⁻¹ ∈ N)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ * b⁻¹ ∈ N) :
    ⁅A ⊔ B, A ⊔ B⁆ ≤ N := by
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  have hg₁' : g₁ ∈ Subgroup.closure ((A : Set G) ∪ (B : Set G)) := by
    rwa [Subgroup.sup_eq_closure] at hg₁
  have hg₂' : g₂ ∈ Subgroup.closure ((A : Set G) ∪ (B : Set G)) := by
    rwa [Subgroup.sup_eq_closure] at hg₂
  refine Subgroup.closure_induction₂ (k := (A : Set G) ∪ (B : Set G))
    (p := fun x y _ _ => ⁅x, y⁆ ∈ N) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hg₁' hg₂'
  · intro x y hx hy
    rcases hx with hxA | hxB <;> rcases hy with hyA | hyB
    · exact hAA x hxA y hyA
    · exact hAB x hxA y hyB
    · exact (commutatorElement_inv y x) ▸ N.inv_mem (hAB y hyA x hxB)
    · exact hBB x hxB y hyB
  · intro x hx
    rw [commutatorElement_one_left]
    exact N.one_mem
  · intro x hx
    rw [commutatorElement_one_right]
    exact N.one_mem
  · intro x y z hx hy hz hxz hyz
    rw [commutatorElement_mul_left_eq_conj_mul]
    have hxAB : x ∈ A ⊔ B := by
      rw [Subgroup.sup_eq_closure]; exact hx
    have h1 : x * ⁅y, z⁆ * x⁻¹ ∈ N := hN x hxAB ⁅y, z⁆ hyz
    exact N.mul_mem h1 hxz
  · intro y z x hy hz hx hxy hxz
    rw [commutatorElement_mul_right_eq_mul_conj]
    have hyAB : y ∈ A ⊔ B := by
      rw [Subgroup.sup_eq_closure]; exact hy
    have h : y * ⁅x, z⁆ * y⁻¹ ∈ N := hN y hyAB ⁅x, z⁆ hxz
    simpa [mul_assoc] using N.mul_mem hxy h
  · intro x y hx hy hxy
    rw [commutatorElement_inv_left]
    have hxAB : x ∈ A ⊔ B := by
      rw [Subgroup.sup_eq_closure]; exact hx
    have hba : ⁅y, x⁆ ∈ N := (commutatorElement_inv x y) ▸ N.inv_mem hxy
    simpa only [inv_inv] using hN x⁻¹ (Subgroup.inv_mem _ hxAB) ⁅y, x⁆ hba
  · intro x y hx hy hxy
    rw [commutatorElement_inv_right]
    have hyAB : y ∈ A ⊔ B := by
      rw [Subgroup.sup_eq_closure]; exact hy
    have hba : ⁅y, x⁆ ∈ N := (commutatorElement_inv x y) ▸ N.inv_mem hxy
    simpa only [inv_inv] using hN y⁻¹ (Subgroup.inv_mem _ hyAB) ⁅y, x⁆ hba

theorem k18_QT_normal (hc : Ctx18 t L S x₁ x₂ lam rho tau om 𝒮) :
    NormalIn (ctxQ t tau x₁ x₂ rho ⊔ zpowers tau) (ctxK t tau x₁ x₂ rho) := by
  have hc13 := hc.toCtx13
  have hτK : tau ∈ ctxK t tau x₁ x₂ rho := (l17_mem_K hc13).2.1
  refine ⟨sup_le hc13.normal_Q_K.1 (Subgroup.zpowers_le.mpr hτK), ?_⟩
  intro k hk x hx
  have hτ2 : tau * tau = 1 := by
    have := (ctx13_relations hc13).2.2.2.1
    simpa [pow_two] using this
  set c : G := tau⁻¹ * (k * tau * k⁻¹) with hcdef
  have hcK : c ∈ ctxK t tau x₁ x₂ rho :=
    mul_mem (inv_mem hτK) (mul_mem (mul_mem hk hτK) (inv_mem hk))
  have hccent : c ∈ Subgroup.centralizer (ctxQ t tau x₁ x₂ rho : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hq' : k⁻¹ * q * k ∈ ctxQ t tau x₁ x₂ rho := by
      simpa only [inv_inv] using
        hc13.normal_Q_K.2 k⁻¹ ((ctxK t tau x₁ x₂ rho).inv_mem hk) q hq
    have hconj1 : (k * tau * k⁻¹) * q * (k * tau * k⁻¹)⁻¹ = q⁻¹ := by
      have htauq : tau * (k⁻¹ * q * k) * tau⁻¹ = (k⁻¹ * q * k)⁻¹ :=
        hc13.tau_inv_Q (k⁻¹ * q * k) hq'
      have hkq : k * (k⁻¹ * q * k) * k⁻¹ = q := by group
      have hkinv : k * (k⁻¹ * q * k)⁻¹ * k⁻¹ = q⁻¹ := by
        rw [← hkq]; group
      calc (k * tau * k⁻¹) * q * (k * tau * k⁻¹)⁻¹
          = k * (tau * (k⁻¹ * q * k) * tau⁻¹) * k⁻¹ := by group
        _ = k * (k⁻¹ * q * k)⁻¹ * k⁻¹ := by rw [htauq]
        _ = q⁻¹ := hkinv
    have hqinv : tau⁻¹ * q⁻¹ * tau = q := by
      have htau_inv : tau⁻¹ = tau := inv_eq_of_mul_eq_one_right hτ2
      have h := hc13.tau_inv_Q q⁻¹ (Subgroup.inv_mem _ hq)
      rw [htau_inv] at h ⊢
      simpa [inv_inv] using h
    have h : c * q * c⁻¹ = q := by
      rw [hcdef]
      calc (tau⁻¹ * (k * tau * k⁻¹)) * q * (tau⁻¹ * (k * tau * k⁻¹))⁻¹
          = tau⁻¹ * ((k * tau * k⁻¹) * q * (k * tau * k⁻¹)⁻¹) * tau := by group
        _ = tau⁻¹ * q⁻¹ * tau := by rw [hconj1]
        _ = q := hqinv
    have hcq : c * q = q * c := by
      calc c * q = c * q * c⁻¹ * c := by group
        _ = q * c := by rw [h]
    exact hcq.symm
  have hcQ : c ∈ ctxQ t tau x₁ x₂ rho := by
    rw [← hc.P_eq]
    exact ⟨hcK, hccent⟩
  have hkτ : k * tau * k⁻¹ = tau * c := by
    rw [hcdef]; group
  have hmem : k * tau * k⁻¹ ∈ ctxQ t tau x₁ x₂ rho ⊔ zpowers tau := by
    rw [hkτ]
    exact (ctxQ t tau x₁ x₂ rho ⊔ Subgroup.zpowers tau).mul_mem
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers tau)) (Subgroup.mem_sup_left hcQ)
  have hmapQ : cj k (ctxQ t tau x₁ x₂ rho) ≤ ctxQ t tau x₁ x₂ rho := by
    intro y hy
    have hy' : k⁻¹ * y * k ∈ ctxQ t tau x₁ x₂ rho := (mem_cj (H := _)).mp hy
    have h := hc13.normal_Q_K.2 k hk (k⁻¹ * y * k) hy'
    convert h using 1
    group
  have hmapZ : cj k (Subgroup.zpowers tau) ≤ ctxQ t tau x₁ x₂ rho ⊔ zpowers tau := by
    rw [cj, MonoidHom.map_zpowers]
    refine Subgroup.zpowers_le.mpr ?_
    simpa [MulAut.conj_apply] using hmem
  have hNle : cj k (ctxQ t tau x₁ x₂ rho ⊔ zpowers tau) ≤
      ctxQ t tau x₁ x₂ rho ⊔ zpowers tau := by
    rw [cj_sup]
    exact sup_le (hmapQ.trans le_sup_left) hmapZ
  exact hNle (conj_mem_cj hx)

theorem k18_card_QT (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    Nat.card ↥(ctxQ t tau x₁ x₂ rho ⊔ zpowers tau) = 2 ^ 7 := by
  have hτ2p : tau ^ 2 = 1 := (ctx13_relations hc).2.2.2.1
  have hτ2 : tau * tau = 1 := by simpa [pow_two] using hτ2p
  have hτQ : tau ∉ ctxQ t tau x₁ x₂ rho := Ctx13.tau_not_mem_Q hc
  have hτ1 : tau ≠ 1 := fun h => hτQ (h ▸ Subgroup.one_mem _)
  have hK : ∀ k ∈ Subgroup.zpowers tau, ∀ h ∈ ctxQ t tau x₁ x₂ rho,
      k * h * k⁻¹ ∈ ctxQ t tau x₁ x₂ rho := by
    intro k hk h hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    rcases k18m_zpow_eq_one_or_self hτ2 n with hn | hn
    · rw [hn]; simpa using hh
    · rw [hn, hc.tau_inv_Q h hh]; exact Subgroup.inv_mem _ hh
  have hHK : ctxQ t tau x₁ x₂ rho ⊓ Subgroup.zpowers tau = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxQ, hxZ⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxZ
    rcases k18m_zpow_eq_one_or_self hτ2 n with hn | hn
    · rw [hn]
    · rw [hn] at hxQ; exact absurd hxQ hτQ
  have hcardQ : Nat.card (ctxQ t tau x₁ x₂ rho) = 2 ^ 6 := by
    rw [IsZ4Z4E4.card hc.q_iso]; norm_num
  have hcardτ : Nat.card (Subgroup.zpowers tau) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hτ2p hτ1
  rw [card_sup_eq_mul (H := ctxQ t tau x₁ x₂ rho) (K := Subgroup.zpowers tau) hK hHK,
    hcardQ, hcardτ]
  norm_num

theorem k18_comm_tom (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    ∀ d ∈ closure ({t, om} : Set G), ∀ d' ∈ closure ({t, om} : Set G),
      d * d' * d⁻¹ * d'⁻¹ ∈ zpowers tau := by
  have ht2 : t * t = 1 := by
    have := (ctx13_relations hc).1
    simpa [pow_two] using this
  have hom2 : om * om = 1 := by
    have := (ctx13_relations hc).2.2.1
    simpa [pow_two] using this
  have hτ2 : tau * tau = 1 := by
    have := (ctx13_relations hc).2.2.2.1
    simpa [pow_two] using this
  have htτ : t * tau = tau * t := (ctx13_relations hc).2.2.2.2.2.1
  have hτom : tau * om = om * tau := k18m_tau_comm_om hc
  have htτom : t * om * t⁻¹ = om * tau := k18m_t_om_conj hc
  have hcent : Subgroup.zpowers t ⊔ Subgroup.zpowers om ≤
      Subgroup.centralizer (Subgroup.zpowers tau : Set G) :=
    k18m_zpowers_sup_le_centralizer_zpowers htτ hτom.symm
  have hN : ∀ g ∈ Subgroup.zpowers t ⊔ Subgroup.zpowers om,
      ∀ n ∈ Subgroup.zpowers tau, g * n * g⁻¹ ∈ Subgroup.zpowers tau := by
    intro g hg n hn
    have hcomm : n * g = g * n :=
      Subgroup.mem_centralizer_iff.mp (hcent hg) n hn
    have h : g * n * g⁻¹ = n := by rw [← hcomm]; group
    rwa [h]
  have hAA : ∀ a ∈ Subgroup.zpowers t, ∀ a' ∈ Subgroup.zpowers t,
      a * a' * a⁻¹ * a'⁻¹ ∈ Subgroup.zpowers tau := by
    intro a ha a' ha'
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha'
    change ⁅t ^ m, t ^ n⁆ ∈ Subgroup.zpowers tau
    rw [(Commute.zpow_zpow_self (a := t) (m := m) (n := n)).commutator_eq]
    exact Subgroup.one_mem _
  have hBB : ∀ b ∈ Subgroup.zpowers om, ∀ b' ∈ Subgroup.zpowers om,
      b * b' * b⁻¹ * b'⁻¹ ∈ Subgroup.zpowers tau := by
    intro b hb b' hb'
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb'
    change ⁅om ^ m, om ^ n⁆ ∈ Subgroup.zpowers tau
    rw [(Commute.zpow_zpow_self (a := om) (m := m) (n := n)).commutator_eq]
    exact Subgroup.one_mem _
  have hAB : ∀ a ∈ Subgroup.zpowers t, ∀ b ∈ Subgroup.zpowers om,
      a * b * a⁻¹ * b⁻¹ ∈ Subgroup.zpowers tau := by
    intro a ha b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    change ⁅t ^ m, om ^ n⁆ ∈ Subgroup.zpowers tau
    rcases k18m_zpow_eq_one_or_self ht2 m with hm | hm <;>
      rcases k18m_zpow_eq_one_or_self hom2 n with hn | hn <;>
      rw [hm, hn]
    · rw [show ⁅(1 : G), (1 : G)⁆ = 1 by simp]
      exact Subgroup.one_mem _
    · rw [show ⁅(1 : G), om⁆ = 1 by simp]
      exact Subgroup.one_mem _
    · rw [show ⁅t, (1 : G)⁆ = 1 by simp]
      exact Subgroup.one_mem _
    · have htom : ⁅t, om⁆ = tau := by
        rw [commutatorElement_def, htτom]
        have h4 : om * tau = tau * om := hτom.symm
        calc om * tau * om⁻¹ = tau * om * om⁻¹ := by rw [h4]
          _ = tau := by group
      rw [htom]
      exact Subgroup.mem_zpowers tau
  have hmain : ⁅Subgroup.zpowers t ⊔ Subgroup.zpowers om,
      Subgroup.zpowers t ⊔ Subgroup.zpowers om⁆ ≤ Subgroup.zpowers tau :=
    comm_le_of_abelian_mod (N := Subgroup.zpowers tau)
      (A := Subgroup.zpowers t) (B := Subgroup.zpowers om) hN hAA hBB hAB
  have hcl : Subgroup.zpowers t ⊔ Subgroup.zpowers om = closure ({t, om} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
    congr 1
  intro d hd d' hd'
  rw [← hcl] at hd hd'
  exact hmain (Subgroup.commutator_mem_commutator hd hd')

theorem k18_comm_Xi_tom (hc : Ctx18A t L S x₁ x₂ lam rho tau om 𝒮) :
    ∀ ξ ∈ ctxXi t tau x₁ x₂ rho, ∀ d ∈ closure ({t, om} : Set G),
      ξ * d * ξ⁻¹ * d⁻¹ ∈ ctxQ t tau x₁ x₂ rho := by
  have hc13 := hc.toCtx13
  have hclK : closure ({t, om} : Set G) ≤ ctxK t tau x₁ x₂ rho := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with hxt | hxom
    · rw [hxt]; exact (l17_mem_K hc13).1
    · rw [hxom]; exact (l17_mem_K hc13).2.2.1
  intro ξ hξ d hd
  refine Subgroup.closure_induction (k := ({t, om} : Set G))
    (p := fun d _ => ξ * d * ξ⁻¹ * d⁻¹ ∈ ctxQ t tau x₁ x₂ rho) ?_ ?_ ?_ ?_ hd
  · intro x hx
    rcases hx with hxt | hxom
    · rw [hxt]
      exact k18_comm_Xi_R hc13 ξ hξ t
        (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
    · rw [hxom]
      exact k18A_comm_Xi_C hc ξ hξ om
        (l18_QA_le_C hc13 (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))))
  · have h : ξ * 1 * ξ⁻¹ * 1⁻¹ = (1 : G) := by group
    rw [h]
    exact Subgroup.one_mem _
  · intro x y hx hy hpx hpy
    have hconj : x * (ξ * y * ξ⁻¹ * y⁻¹) * x⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
      hc13.normal_Q_K.2 x (hclK hx) _ hpy
    have heq : ξ * (x * y) * ξ⁻¹ * (x * y)⁻¹ =
        (ξ * x * ξ⁻¹ * x⁻¹) * (x * (ξ * y * ξ⁻¹ * y⁻¹) * x⁻¹) := by group
    rw [heq]
    exact Subgroup.mul_mem _ hpx hconj
  · intro x hx hpx
    have hconj : x⁻¹ * (ξ * x * ξ⁻¹ * x⁻¹)⁻¹ * x ∈ ctxQ t tau x₁ x₂ rho := by
      simpa only [inv_inv] using
        hc13.normal_Q_K.2 x⁻¹ ((ctxK t tau x₁ x₂ rho).inv_mem (hclK hx)) _
          (Subgroup.inv_mem _ hpx)
    have heq : ξ * x⁻¹ * ξ⁻¹ * (x⁻¹)⁻¹ =
        x⁻¹ * (ξ * x * ξ⁻¹ * x⁻¹)⁻¹ * x := by group
    rw [heq]
    exact hconj

theorem k18_OK_derived_le (hc : Ctx18A t L S x₁ x₂ lam rho tau om 𝒮) :
    ⁅ctxOK t tau x₁ x₂ rho, ctxOK t tau x₁ x₂ rho⁆ ≤ ctxQ t tau x₁ x₂ rho ⊔ zpowers tau := by
  have hc13 := hc.toCtx13
  have hQT : NormalIn (ctxQ t tau x₁ x₂ rho ⊔ zpowers tau) (ctxK t tau x₁ x₂ rho) :=
    k18_QT_normal hc.toCtx18
  have hN : ∀ g ∈ ctxXi t tau x₁ x₂ rho ⊔ closure ({t, om} : Set G),
      ∀ n ∈ ctxQ t tau x₁ x₂ rho ⊔ zpowers tau,
      g * n * g⁻¹ ∈ ctxQ t tau x₁ x₂ rho ⊔ zpowers tau := by
    intro g hg n hn
    have hgOK : g ∈ ctxOK t tau x₁ x₂ rho := by
      rw [k18_OK_eq_Xi_tom hc13]; exact hg
    exact hQT.2 g ((l18_OK_normal (t := t) (tau := tau) (x₁ := x₁) (x₂ := x₂)
      (rho := rho)).1 hgOK) n hn
  have hAA : ∀ a ∈ ctxXi t tau x₁ x₂ rho, ∀ a' ∈ ctxXi t tau x₁ x₂ rho,
      a * a' * a⁻¹ * a'⁻¹ ∈ ctxQ t tau x₁ x₂ rho ⊔ zpowers tau := by
    intro a ha a' ha'
    exact Subgroup.mem_sup_left ((k18_Xi_quot_elem hc.toCtx18).1 a ha a' ha')
  have hBB : ∀ b ∈ closure ({t, om} : Set G), ∀ b' ∈ closure ({t, om} : Set G),
      b * b' * b⁻¹ * b'⁻¹ ∈ ctxQ t tau x₁ x₂ rho ⊔ zpowers tau := by
    intro b hb b' hb'
    exact Subgroup.mem_sup_right (k18_comm_tom hc13 b hb b' hb')
  have hAB : ∀ a ∈ ctxXi t tau x₁ x₂ rho, ∀ b ∈ closure ({t, om} : Set G),
      a * b * a⁻¹ * b⁻¹ ∈ ctxQ t tau x₁ x₂ rho ⊔ zpowers tau := by
    intro a ha b hb
    exact Subgroup.mem_sup_left (k18_comm_Xi_tom hc a ha b hb)
  rw [k18_OK_eq_Xi_tom hc13]
  exact comm_le_of_abelian_mod (N := ctxQ t tau x₁ x₂ rho ⊔ zpowers tau)
    (A := ctxXi t tau x₁ x₂ rho) (B := closure ({t, om} : Set G)) hN hAA hBB hAB

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
