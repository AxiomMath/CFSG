module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbB18g
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbD18a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbB18d
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbB18f
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP15

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

private lemma Xi_cent_Y (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) :
    ∀ y ∈ ctxYq t tau x₁ x₂ rho, ∀ x ∈ ctxXi t tau x₁ x₂ rho, x * y = y * x := by
  intro y hy x hx
  have hxC : x ∈ ctxCY t tau x₁ x₂ rho := l18_Xi_le_C hc hx
  have hcen : x ∈ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) :=
    (Subgroup.mem_inf.mp hxC).2
  exact (Subgroup.mem_centralizer_iff.mp hcen y hy).symm

private lemma Q_le_Dsub (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) :
    ctxQ t tau x₁ x₂ rho ≤
      Dsub (ctxXi t tau x₁ x₂ rho) (ctxYq t tau x₁ x₂ rho) (Xi_cent_Y hc) t := by
  intro q hq
  exact ⟨l18_Q_le_Xi hc.toCtx13 hq,
    l17_V_le_Y hc.toCtx13 (l18_comm_t_Q_mem_V hc.toCtx13 hq)⟩

private lemma t_rho_comm (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) :
    t * rho = rho * t := by
  have htC : t ∈ centralizer ({rho} : Set G) := by
    have ht : t ∈ closure ({t, om} : Set G) ⊔ zpowers rho :=
      Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
    rw [← hc.CK_rho] at ht
    exact (Subgroup.mem_inf.mp ht).2
  exact (Subgroup.mem_centralizer_iff.mp htC rho (by simp)).symm

private lemma Dsub_rho_mem (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) {z : G}
    (hz : z ∈ Dsub (ctxXi t tau x₁ x₂ rho) (ctxYq t tau x₁ x₂ rho) (Xi_cent_Y hc) t) :
    rho * z * rho⁻¹ ∈
      Dsub (ctxXi t tau x₁ x₂ rho) (ctxYq t tau x₁ x₂ rho) (Xi_cent_Y hc) t := by
  have hρK : rho ∈ ctxK t tau x₁ x₂ rho := (l17_mem_K hc.toCtx13).2.2.2.2
  refine ⟨(l18_Xi_normal hc.toCtx13).2 rho hρK z hz.1, ?_⟩
  have hconj : rho * (t * z * t⁻¹ * z⁻¹) * rho⁻¹ ∈ ctxYq t tau x₁ x₂ rho :=
    l17_K_normalizes_Y hc.toCtx13 rho hρK _ hz.2
  convert hconj using 1
  have hconj_t : rho * t * rho⁻¹ = t := by rw [← t_rho_comm hc]; group
  have hid : ⁅t, rho * z * rho⁻¹⁆ = rho * ⁅t, z⁆ * rho⁻¹ := by
    rw [conjugate_commutatorElement, hconj_t]
  simpa only [commutatorElement_def] using hid

private lemma conj_t_mem_smul (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮)
    (hDall : ∀ m ∈ ctxXi t tau x₁ x₂ rho,
      t * m * t⁻¹ * m⁻¹ ∈ ctxYq t tau x₁ x₂ rho) {k : G}
    (hk : k ∈ ctxK t tau x₁ x₂ rho) :
    k * t * k⁻¹ ∈ t • (ctxYq t tau x₁ x₂ rho : Set G) ∪
      (t * tau) • (ctxYq t tau x₁ x₂ rho : Set G) := by
  obtain ⟨m, hm, hmcase⟩ := l18_t_conj_decomp hc hk
  have htK : t ∈ ctxK t tau x₁ x₂ rho := (l17_mem_K hc.toCtx13).1
  have htauK : tau ∈ ctxK t tau x₁ x₂ rho := (l17_mem_K hc.toCtx13).2.1
  have hnorm := l17_K_normalizes_Y hc.toCtx13
  have hcY : m * t * m⁻¹ * t⁻¹ ∈ ctxYq t tau x₁ x₂ rho := by
    have h := (ctxYq t tau x₁ x₂ rho).inv_mem (hDall m hm)
    convert h using 1
    group
  rcases hmcase with h | h
  · left
    have hyY : t⁻¹ * (m * t * m⁻¹ * t⁻¹) * t ∈ ctxYq t tau x₁ x₂ rho := by
      simpa using hnorm t⁻¹ ((ctxK t tau x₁ x₂ rho).inv_mem htK) _ hcY
    have heq : t * (t⁻¹ * (m * t * m⁻¹ * t⁻¹) * t) = m * t * m⁻¹ := by group
    rw [h, ← heq]
    exact Set.smul_mem_smul_set hyY
  · right
    have hdY : m * tau * m⁻¹ * tau⁻¹ ∈ ctxYq t tau x₁ x₂ rho := l18_comm_tau_mem_Y hc hm
    have htdY : t * (m * tau * m⁻¹ * tau⁻¹) * t⁻¹ ∈ ctxYq t tau x₁ x₂ rho :=
      hnorm t htK _ hdY
    have heY : (m * t * m⁻¹ * t⁻¹) * (t * (m * tau * m⁻¹ * tau⁻¹) * t⁻¹) ∈
        ctxYq t tau x₁ x₂ rho :=
      (ctxYq t tau x₁ x₂ rho).mul_mem hcY htdY
    have httauK : t * tau ∈ ctxK t tau x₁ x₂ rho :=
      (ctxK t tau x₁ x₂ rho).mul_mem htK htauK
    have hyY : (t * tau)⁻¹ *
        ((m * t * m⁻¹ * t⁻¹) * (t * (m * tau * m⁻¹ * tau⁻¹) * t⁻¹)) * (t * tau) ∈
        ctxYq t tau x₁ x₂ rho := by
      simpa using hnorm (t * tau)⁻¹ ((ctxK t tau x₁ x₂ rho).inv_mem httauK) _ heY
    have heq : (t * tau) * ((t * tau)⁻¹ *
        ((m * t * m⁻¹ * t⁻¹) * (t * (m * tau * m⁻¹ * tau⁻¹) * t⁻¹)) * (t * tau)) =
        m * (t * tau) * m⁻¹ := by group
    rw [h, ← heq]
    exact Set.smul_mem_smul_set hyY

private lemma D_eq_Xi_contra (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮)
    (hDall : ∀ m ∈ ctxXi t tau x₁ x₂ rho,
      t * m * t⁻¹ * m⁻¹ ∈ ctxYq t tau x₁ x₂ rho) : False := by
  obtain ⟨V', v₁, v₂, hV'⟩ := hc.data_V
  unfold Ctx13V at hV'
  obtain ⟨_, _, hQeq, _, _, _, hYeq, _, _, _, _, hv2mem, _, _, _, _, hCentTtau, _, _⟩ := hV'
  let q₀ : G := x₁ * v₂
  have hx1base : x₁ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hx1Q : x₁ ∈ ctxQ t tau x₁ x₂ rho := hc.base_le_Q hx1base
  have hv2Q : v₂ ∈ ctxQ t tau x₁ x₂ rho := by
    rw [hQeq]; exact Subgroup.mem_sup_right hv2mem
  have hq0Q : q₀ ∈ ctxQ t tau x₁ x₂ rho := (ctxQ t tau x₁ x₂ rho).mul_mem hx1Q hv2Q
  have hv2Y : v₂ ∈ ctxYq t tau x₁ x₂ rho := by
    rw [hYeq]; exact Subgroup.mem_sup_right hv2mem
  have hq0cen : q₀ ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * tau} : Set G) := by
    rw [hCentTtau]
    exact Subgroup.subset_closure (by simp [q₀])
  have hq0comm : (t * tau) * q₀ = q₀ * (t * tau) :=
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hq0cen).2 (t * tau) (by simp)
  have hq0tau : tau * q₀ * tau⁻¹ = q₀⁻¹ := hc.tau_inv_Q q₀ hq0Q
  have ht2 : t * t = 1 := by simpa [pow_two] using (ctx13_relations hc.toCtx13).1
  have htau2 : tau * tau = 1 := by
    simpa [pow_two] using (ctx13_relations hc.toCtx13).2.2.2.1
  have htq_ne : t * q₀ ≠ 1 := by
    intro h1
    have htQ : t ∈ ctxQ t tau x₁ x₂ rho := by
      have ht_eq : t = q₀⁻¹ := eq_inv_of_mul_eq_one_left h1
      exact ht_eq.symm ▸ ((ctxQ t tau x₁ x₂ rho).inv_mem hq0Q)
    have htP : t ∈ ctxP t tau x₁ x₂ rho := l17_Q_le_P hc.toCtx13 htQ
    exact (ctx13_relations hc.toCtx13).2.1 (l17_CP_rho hc.toCtx13 t htP (t_rho_comm hc))
  have htq_sq : (t * q₀) ^ 2 = 1 := by
    have hqt : q₀ * t = t * q₀⁻¹ := by
      have htau_inv : tau⁻¹ = tau := inv_eq_of_mul_eq_one_right htau2
      have hconj : tau * q₀ * tau = q₀⁻¹ := by simpa [htau_inv] using hq0tau
      calc q₀ * t = q₀ * t * (tau * tau) := by rw [htau2, mul_one]
        _ = (q₀ * (t * tau)) * tau := by group
        _ = ((t * tau) * q₀) * tau := by rw [← hq0comm]
        _ = t * (tau * q₀ * tau) := by group
        _ = t * q₀⁻¹ := by rw [hconj]
    rw [pow_two]
    calc t * q₀ * (t * q₀) = t * (q₀ * t) * q₀ := by group
      _ = t * (t * q₀⁻¹) * q₀ := by rw [hqt]
      _ = (t * t) * (q₀⁻¹ * q₀) := by group
      _ = 1 := by rw [ht2, inv_mul_cancel, mul_one]
  have htq_inv : t * q₀ ∈ InvIn (t • (ctxQ t tau x₁ x₂ rho : Set G)) :=
    ⟨Set.mem_smul_set.mpr ⟨q₀, hq0Q, rfl⟩, htq_sq, htq_ne⟩
  have htq_conj : t * q₀ ∈ conjIn (ctxK t tau x₁ x₂ rho) t := by
    rw [hc.tK]
    exact Or.inl htq_inv
  simp only [conjIn, Set.mem_setOf_eq] at htq_conj
  obtain ⟨k, hkK, hkt⟩ := htq_conj
  have hmem := conj_t_mem_smul hc hDall hkK
  rw [hkt] at hmem
  rcases hmem with hmem | hmem
  · obtain ⟨a, ha, haeq⟩ := Set.mem_smul_set.mp hmem
    have haeq' : t * a = t * q₀ := haeq
    have haq : a = q₀ := mul_left_cancel haeq'
    have hq0Y : q₀ ∈ ctxYq t tau x₁ x₂ rho := haq ▸ ha
    have hx1Y : x₁ ∈ ctxYq t tau x₁ x₂ rho := by
      have hx1eq : x₁ = q₀ * v₂⁻¹ := by simp only [q₀]; group
      have h : q₀ * v₂⁻¹ ∈ ctxYq t tau x₁ x₂ rho :=
        (ctxYq t tau x₁ x₂ rho).mul_mem hq0Y ((ctxYq t tau x₁ x₂ rho).inv_mem hv2Y)
      exact hx1eq.symm ▸ h
    exact (l17_yz_ne hc.toCtx13).1 ((mem_ctxYq_iff hc.q_iso x₁).mp hx1Y).2
  · obtain ⟨a, ha, haeq⟩ := Set.mem_smul_set.mp hmem
    have haeq' : (t * tau) * a = t * q₀ := haeq
    have h2 : tau * a = q₀ := by
      apply mul_left_cancel (a := t)
      calc t * (tau * a) = (t * tau) * a := by group
        _ = t * q₀ := haeq'
    have htauQ : tau ∈ ctxQ t tau x₁ x₂ rho := by
      have h3 : tau = q₀ * a⁻¹ := by rw [← h2]; group
      have h : q₀ * a⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
        (ctxQ t tau x₁ x₂ rho).mul_mem hq0Q
          ((ctxQ t tau x₁ x₂ rho).inv_mem (ctxYq_le_ctxQ ha))
      exact h3.symm ▸ h
    exact Ctx13.tau_not_mem_Q hc.toCtx13 htauQ

theorem l18_Dt_le_Q (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) {x : G}
    (hx : x ∈ ctxXi t tau x₁ x₂ rho) (hD : t * x * t⁻¹ * x⁻¹ ∈ ctxYq t tau x₁ x₂ rho) :
    x ∈ ctxQ t tau x₁ x₂ rho := by
  classical
  let D : Subgroup G :=
    Dsub (ctxXi t tau x₁ x₂ rho) (ctxYq t tau x₁ x₂ rho) (Xi_cent_Y hc) t
  have hQD : ctxQ t tau x₁ x₂ rho ≤ D := Q_le_Dsub hc
  have hDXi : D ≤ ctxXi t tau x₁ x₂ rho := Dsub_le
  have hxD : x ∈ D := ⟨hx, hD⟩
  have hQXi : (ctxQ t tau x₁ x₂ rho).relIndex (ctxXi t tau x₁ x₂ rho) = 4 := by
    have h := Subgroup.relIndex_mul_card (H := ctxQ t tau x₁ x₂ rho)
      (K := ctxXi t tau x₁ x₂ rho)
    rw [inf_eq_left.mpr (l18_Q_le_Xi hc.toCtx13)] at h
    rw [l18_card_Xi hc, IsZ4Z4E4.card hc.q_iso] at h
    norm_num at h
    omega
  have hQρ : ∀ q ∈ ctxQ t tau x₁ x₂ rho, rho * q * rho⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
    fun q hq => hc.normal_Q_K.2 rho ((l17_mem_K hc.toCtx13).2.2.2.2) q hq
  have hDρ : ∀ z ∈ D, rho * z * rho⁻¹ ∈ D := fun z hz => Dsub_rho_mem hc hz
  have hfix : ∀ z ∈ D, rho * z * rho⁻¹ = z → z = 1 := by
    intro z hz hzfix
    have hzΞ : z ∈ ctxXi t tau x₁ x₂ rho := hz.1
    have hzC : z ∈ centralizer ({rho} : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr (fun a ha => ?_)
      rw [Set.mem_singleton_iff] at ha
      subst ha
      calc a * z = (a * z * a⁻¹) * a := by group
        _ = z * a := by rw [hzfix]
    have hzbot : z ∈ ctxXi t tau x₁ x₂ rho ⊓ centralizer ({rho} : Set G) := ⟨hzΞ, hzC⟩
    rw [l18_Xi_cap_cent_rho hc] at hzbot
    exact Subgroup.mem_bot.mp hzbot
  have hρ3 : rho ^ 3 = 1 := by
    rw [← hc.ord_rho]
    exact pow_orderOf_eq_one rho
  have hQmod : Nat.card (ctxQ t tau x₁ x₂ rho) % 3 = 1 := by
    rw [IsZ4Z4E4.card hc.q_iso]
  have hmod : (ctxQ t tau x₁ x₂ rho).relIndex D % 3 = 1 :=
    relIndex_mod_three hQD hρ3 hDρ hQρ hfix hQmod
  have hdvd : (ctxQ t tau x₁ x₂ rho).relIndex D ∣
      (ctxQ t tau x₁ x₂ rho).relIndex (ctxXi t tau x₁ x₂ rho) :=
    ⟨D.relIndex (ctxXi t tau x₁ x₂ rho), by
      exact (Subgroup.relIndex_mul_relIndex (ctxQ t tau x₁ x₂ rho) D
        (ctxXi t tau x₁ x₂ rho) hQD hDXi).symm⟩
  have hmem : (ctxQ t tau x₁ x₂ rho).relIndex D ∈ ({1, 2, 4} : Finset ℕ) := by
    have hdvd' : (ctxQ t tau x₁ x₂ rho).relIndex D ∣ 2 ^ 2 := by
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num]
      rwa [hQXi] at hdvd
    obtain ⟨j, hj, hj2⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd'
    interval_cases j <;> simp_all
  have hcases : (ctxQ t tau x₁ x₂ rho).relIndex D = 1 ∨
      (ctxQ t tau x₁ x₂ rho).relIndex D = 4 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h
    · exact Or.inl h
    · exfalso
      rw [h] at hmod
      norm_num at hmod
    · exact Or.inr h
  rcases hcases with h1 | h4
  · exact Subgroup.relIndex_eq_one.mp h1 hxD
  · exact (D_eq_Xi_contra hc (by
      have hrel : D.relIndex (ctxXi t tau x₁ x₂ rho) = 1 := by
        have h := Subgroup.relIndex_mul_relIndex (ctxQ t tau x₁ x₂ rho) D
          (ctxXi t tau x₁ x₂ rho) hQD hDXi
        rw [h4, hQXi] at h
        omega
      have hD_eq : D = ctxXi t tau x₁ x₂ rho :=
        le_antisymm hDXi (Subgroup.relIndex_eq_one.mp hrel)
      intro m hm
      have hmD : m ∈ D := by rw [hD_eq]; exact hm
      exact hmD.2)).elim

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
