module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutCoprime
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbB18b

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

private theorem fixSub_conj_le_centralizer {H : Type*} [Group H] (g : H) :
    Outside.fixSub (MulAut.conj g) ≤ Subgroup.centralizer ({g} : Set H) := by
  intro x hx
  rw [Outside.mem_fixSub, MulAut.conj_apply] at hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  rw [hy]
  have h : g * x = x * g := by
    have h' := congrArg (· * g) hx
    simpa [mul_assoc] using h'
  exact h

theorem l18_comm_t_Q_mem_V (hc : Ctx13 t L S x₁ x₂ lam rho tau om) {q : G}
    (hq : q ∈ ctxQ t tau x₁ x₂ rho) : t * q * t⁻¹ * q⁻¹ ∈ fourGrp x₁ x₂ := by
  have ht2 : t * t = 1 := by
    have h := (ctx13_relations hc).1
    simpa [pow_two] using h
  have hqR : q ∈ ctxR t tau x₁ x₂ := by
    rw [l17_R_eq hc]
    exact Subgroup.mem_sup_left hq
  have hmem : q * t * q⁻¹ ∈ conjIn (ctxR t tau x₁ x₂) t := ⟨q, hqR, rfl⟩
  rw [hc.tR, Set.mem_smul_set] at hmem
  obtain ⟨v, hvV, hv⟩ := hmem
  rw [inv_eq_of_mul_eq_one_right ht2]
  have heq : t * q * t * q⁻¹ = v := by
    calc t * q * t * q⁻¹ = t * (q * t * q⁻¹) := by group
      _ = t * (t * v) := by rw [← hv, smul_eq_mul]
      _ = v := by rw [← mul_assoc, ht2, one_mul]
  rw [heq]
  exact hvV

theorem l18_Xi_cap_R (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) :
    ctxXi t tau x₁ x₂ rho ⊓ (ctxQ t tau x₁ x₂ rho ⊔ closure {t, tau}) =
      ctxQ t tau x₁ x₂ rho := by
  classical
  set R' : Subgroup G := ctxQ t tau x₁ x₂ rho ⊔ closure ({t, tau} : Set G) with hR'def
  set H : Subgroup G := ctxXi t tau x₁ x₂ rho ⊓ R' with hHdef
  have hQH : ctxQ t tau x₁ x₂ rho ≤ H := by
    rw [hHdef]
    exact le_inf (l18_Q_le_Xi hc.toCtx13) le_sup_left
  have hcardQ : Nat.card (ctxQ t tau x₁ x₂ rho) = 2 ^ 6 := by
    rw [IsZ4Z4E4.card hc.toCtx13.q_iso]; norm_num
  have hcardR : Nat.card R' = 2 ^ 8 := by
    rw [hR'def, ← l17_R_eq hc.toCtx13]
    exact hc.toCtx13.card_R
  have hleR : H ≤ R' := by rw [hHdef]; exact inf_le_right
  have hHpg : IsPGroup 2 H := by
    rw [hHdef]
    exact (l18_Xi_pgroup hc.toCtx13).to_le inf_le_left
  have hHinv : ∀ h ∈ H, MulAut.conj rho h ∈ H := by
    intro h hh
    rw [hHdef] at hh ⊢
    obtain ⟨hhΞ, hhR⟩ := Subgroup.mem_inf.mp hh
    have hrhoK : rho ∈ ctxK t tau x₁ x₂ rho := (l17_mem_K hc.toCtx13).2.2.2.2
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h := (l18_Xi_normal hc.toCtx13).2 rho hrhoK h hhΞ
      simpa [MulAut.conj_apply] using h
    · have h := (Subgroup.mem_set_normalizer_iff.mp hrhoK h).mp hhR
      simpa [MulAut.conj_apply] using h
  have hρ3 : (MulAut.conj rho) ^ 3 = 1 := by
    have hrho3 : rho ^ 3 = 1 := by
      rw [← hc.toCtx13.ord_rho]; exact pow_orderOf_eq_one rho
    calc (MulAut.conj rho) ^ 3 = MulAut.conj (rho ^ 3) := (map_pow _ _ _).symm
      _ = MulAut.conj (1 : G) := by rw [hrho3]
      _ = 1 := map_one _
  have hmod := Outside.card_mod_three_fix (MulAut.conj rho) hρ3 H hHinv
  have hfixbot : H ⊓ Outside.fixSub (MulAut.conj rho) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxH, hxfix⟩ := Subgroup.mem_inf.mp hx
    have hxΞ : x ∈ ctxXi t tau x₁ x₂ rho := (Subgroup.mem_inf.mp (hHdef ▸ hxH)).1
    have hxcent : x ∈ centralizer ({rho} : Set G) := fixSub_conj_le_centralizer rho hxfix
    have hmem : x ∈ ctxXi t tau x₁ x₂ rho ⊓ centralizer ({rho} : Set G) :=
      Subgroup.mem_inf.mpr ⟨hxΞ, hxcent⟩
    have hxbot : x ∈ (⊥ : Subgroup G) := by
      rwa [l18_Xi_cap_cent_rho hc] at hmem
    simpa using hxbot
  have hmod1 : Nat.card H % 3 = 1 := by
    rw [hfixbot, Subgroup.card_bot] at hmod
    simpa using hmod
  have hcardH : Nat.card H = 2 ^ 6 := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hHpg
    have hk6 : 6 ≤ k := by
      have h : 2 ^ 6 ≤ 2 ^ k := by
        rw [← hk, ← hcardQ]
        exact Subgroup.card_le_of_le hQH
      exact (Nat.pow_le_pow_iff_right (le_refl 2)).mp h
    have hk8 : k ≤ 8 := by
      have h : 2 ^ k ≤ 2 ^ 8 := by
        rw [← hk, ← hcardR]
        exact Subgroup.card_le_of_le hleR
      exact (Nat.pow_le_pow_iff_right (le_refl 2)).mp h
    have hk_vals : k = 6 ∨ k = 7 ∨ k = 8 := by omega
    rcases hk_vals with rfl | rfl | rfl
    · exact hk
    · exfalso
      have h := hmod1
      rw [hk] at h
      norm_num at h
    · exfalso
      have hcardH8 : Nat.card H = 2 ^ 8 := hk
      have hEq : H = R' := by
        apply Subgroup.eq_of_le_of_card_ge hleR
        rw [hcardH8, hcardR]
      have htR : t ∈ R' := by
        rw [hR'def]
        exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
      have htH : t ∈ H := by rw [hEq]; exact htR
      have htΞ : t ∈ ctxXi t tau x₁ x₂ rho := (Subgroup.mem_inf.mp (hHdef ▸ htH)).1
      have hcl : closure ({t, tau} : Set G) ≤ centralizer ({rho} : Set G) := by
        rw [← hc.toCtx13.CR_rho]; exact inf_le_right
      have htcent : t ∈ centralizer ({rho} : Set G) :=
        hcl (Subgroup.subset_closure (by simp))
      have htbot : t ∈ (⊥ : Subgroup G) := by
        have hmem : t ∈ ctxXi t tau x₁ x₂ rho ⊓ centralizer ({rho} : Set G) :=
          Subgroup.mem_inf.mpr ⟨htΞ, htcent⟩
        rwa [l18_Xi_cap_cent_rho hc] at hmem
      have ht1 : t = 1 := by simpa using htbot
      exact (ctx13_relations hc.toCtx13).2.1 ht1
  exact (Subgroup.eq_of_le_of_card_ge hQH (by rw [hcardH, hcardQ])).symm

theorem l18_comm_Xi_R_mem_Q (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) {m r : G}
    (hm : m ∈ ctxXi t tau x₁ x₂ rho) (hr : r ∈ ctxQ t tau x₁ x₂ rho ⊔ closure {t, tau}) :
    m * r * m⁻¹ * r⁻¹ ∈ ctxQ t tau x₁ x₂ rho := by
  have hmK : m ∈ ctxK t tau x₁ x₂ rho :=
    hc.sylow.1 (l18_Xi_le_sylow hc.toCtx18S hm)
  have hRleK : (ctxQ t tau x₁ x₂ rho ⊔ closure ({t, tau} : Set G)) ≤
      ctxK t tau x₁ x₂ rho := Subgroup.le_normalizer
  have hrK : r ∈ ctxK t tau x₁ x₂ rho := hRleK hr
  have hconjΞ : r * m⁻¹ * r⁻¹ ∈ ctxXi t tau x₁ x₂ rho :=
    (l18_Xi_normal hc.toCtx13).2 r hrK m⁻¹ (inv_mem hm)
  have hmrΞ : m * r * m⁻¹ * r⁻¹ ∈ ctxXi t tau x₁ x₂ rho := by
    have h := mul_mem hm hconjΞ
    simpa [mul_assoc] using h
  have hmrR : m * r * m⁻¹ ∈ (ctxQ t tau x₁ x₂ rho ⊔ closure ({t, tau} : Set G)) :=
    (Subgroup.mem_set_normalizer_iff.mp hmK r).mp hr
  have hmrR' : m * r * m⁻¹ * r⁻¹ ∈
      (ctxQ t tau x₁ x₂ rho ⊔ closure ({t, tau} : Set G)) := mul_mem hmrR (inv_mem hr)
  have hmem : m * r * m⁻¹ * r⁻¹ ∈
      ctxXi t tau x₁ x₂ rho ⊓ (ctxQ t tau x₁ x₂ rho ⊔ closure {t, tau}) :=
    Subgroup.mem_inf.mpr ⟨hmrΞ, hmrR'⟩
  rwa [l18_Xi_cap_R hc] at hmem

theorem l18_comm_Xi_Q_mem_V (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) {m q : G}
    (hm : m ∈ ctxXi t tau x₁ x₂ rho) (hq : q ∈ ctxQ t tau x₁ x₂ rho) :
    m * q * m⁻¹ * q⁻¹ ∈ fourGrp x₁ x₂ := by
  have ht2 : t * t = 1 := by
    have h := (ctx13_relations hc.toCtx13).1
    simpa [pow_two] using h
  have hcommQ : ∀ a ∈ ctxQ t tau x₁ x₂ rho, ∀ b ∈ ctxQ t tau x₁ x₂ rho, a * b = b * a :=
    fun a ha b hb => IsZ4Z4E4.comm hc.toCtx13.q_iso ha hb
  have hcommY : ∀ a ∈ ctxYq t tau x₁ x₂ rho, ∀ b ∈ ctxYq t tau x₁ x₂ rho, a * b = b * a :=
    fun a ha b hb => IsZ4Z4E4.comm hc.toCtx13.q_iso (ctxYq_le_ctxQ ha) (ctxYq_le_ctxQ hb)
  let v : G := t * q * t⁻¹ * q⁻¹
  have hvV : v ∈ fourGrp x₁ x₂ := l18_comm_t_Q_mem_V hc.toCtx13 hq
  have hvY : v ∈ ctxYq t tau x₁ x₂ rho := l17_V_le_Y hc.toCtx13 hvV
  have hvQ : v ∈ ctxQ t tau x₁ x₂ rho := ctxYq_le_ctxQ hvY
  have hv_eq : t * q * t⁻¹ = v * q := by
    show t * q * t⁻¹ = (t * q * t⁻¹ * q⁻¹) * q
    group
  let q₁ : G := m⁻¹ * t * (m⁻¹)⁻¹ * t⁻¹
  have hq₁Q : q₁ ∈ ctxQ t tau x₁ x₂ rho :=
    l18_comm_Xi_R_mem_Q hc (inv_mem hm)
      (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
  have hq₁_eq : t * m * t⁻¹ = m * q₁ := by
    show t * m * t⁻¹ = m * (m⁻¹ * t * (m⁻¹)⁻¹ * t⁻¹)
    group
  have hmC : m ∈ ctxCY t tau x₁ x₂ rho := l18_Xi_le_C hc hm
  have hmcent : m ∈ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) :=
    (Subgroup.mem_inf.mp hmC).2
  have hmv : m * v = v * m := ((Subgroup.mem_centralizer_iff.mp hmcent) v hvY).symm
  have hcY : m * q * m⁻¹ * q⁻¹ ∈ ctxYq t tau x₁ x₂ rho :=
    l18_comm_mem_Y hc.toCtx13 hmC hq
  have htc : t * (m * q * m⁻¹ * q⁻¹) * t⁻¹ = m * q * m⁻¹ * q⁻¹ := by
    calc t * (m * q * m⁻¹ * q⁻¹) * t⁻¹
        = (t * m * t⁻¹) * (t * q * t⁻¹) * (t * m * t⁻¹)⁻¹ * (t * q * t⁻¹)⁻¹ := by
          group
      _ = (m * q₁) * (v * q) * (m * q₁)⁻¹ * (v * q)⁻¹ := by rw [hq₁_eq, hv_eq]
      _ = v * (m * q * m⁻¹ * q⁻¹) * v⁻¹ := by
            have e1 : q₁ * v = v * q₁ := hcommQ q₁ hq₁Q v hvQ
            have e2 : q₁ * q = q * q₁ := hcommQ q₁ hq₁Q q hq
            have e3 : m * v = v * m := hmv
            calc (m * q₁) * (v * q) * (m * q₁)⁻¹ * (v * q)⁻¹
                = m * q₁ * v * q * q₁⁻¹ * m⁻¹ * q⁻¹ * v⁻¹ := by group
              _ = m * (q₁ * v) * q * q₁⁻¹ * m⁻¹ * q⁻¹ * v⁻¹ := by group
              _ = m * (v * q₁) * q * q₁⁻¹ * m⁻¹ * q⁻¹ * v⁻¹ := by rw [e1]
              _ = m * v * (q₁ * q) * q₁⁻¹ * m⁻¹ * q⁻¹ * v⁻¹ := by group
              _ = m * v * (q * q₁) * q₁⁻¹ * m⁻¹ * q⁻¹ * v⁻¹ := by rw [e2]
              _ = m * v * q * m⁻¹ * q⁻¹ * v⁻¹ := by group
              _ = (m * v) * q * m⁻¹ * q⁻¹ * v⁻¹ := by group
              _ = (v * m) * q * m⁻¹ * q⁻¹ * v⁻¹ := by rw [e3]
              _ = v * (m * q * m⁻¹ * q⁻¹) * v⁻¹ := by group
      _ = m * q * m⁻¹ * q⁻¹ := by
            have hvc : v * (m * q * m⁻¹ * q⁻¹) = (m * q * m⁻¹ * q⁻¹) * v :=
              hcommY v hvY (m * q * m⁻¹ * q⁻¹) hcY
            rw [hvc]; group
  have hcent : m * q * m⁻¹ * q⁻¹ ∈ centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have h : t * (m * q * m⁻¹ * q⁻¹) = (m * q * m⁻¹ * q⁻¹) * t := by
      have h' := congrArg (· * t) htc
      simpa [mul_assoc] using h'
    exact h
  have hmem : m * q * m⁻¹ * q⁻¹ ∈
      ctxYq t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) :=
    Subgroup.mem_inf.mpr ⟨hcY, hcent⟩
  rw [hc.toCtx13.Y_cent.1] at hmem
  exact hmem

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
