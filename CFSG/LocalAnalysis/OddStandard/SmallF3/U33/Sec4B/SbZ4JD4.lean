module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JD3

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H] {Q Y V V' B : Subgroup H} {ρ t τ l y z v₁ v₂ : H}

namespace ZJData

variable (h : ZJData Q Y V V' B ρ t τ l y z v₁ v₂) include h

theorem fixed_coset_gen {K : Subgroup H} (hKQ : K ≤ Q) (hρK : ∀ k ∈ K, ρ * k * ρ⁻¹ ∈ K)
    (hKn : ∀ g k : H, k ∈ K → g * k * g⁻¹ ∈ K) {g : H} (hg : ρ * g * ρ⁻¹ * g⁻¹ ∈ K) :
    ∃ k ∈ K, ρ * (g * k) * ρ⁻¹ = g * k := by
  have hwK : g⁻¹ * ρ * g * ρ⁻¹ ∈ K := by
    have h1 := hKn g⁻¹ (ρ * g * ρ⁻¹ * g⁻¹) hg
    rwa [show g⁻¹ * (ρ * g * ρ⁻¹ * g⁻¹) * (g⁻¹)⁻¹ = g⁻¹ * ρ * g * ρ⁻¹ from by group] at h1
  let f : ↥K → ↥K := fun k =>
    ⟨(k : H) * (ρ * (k : H) * ρ⁻¹)⁻¹,
      K.mul_mem k.2 (K.inv_mem (hρK (k : H) k.2))⟩
  have hf_inj : Function.Injective f := by
    intro k₁ k₂ hk
    apply Subtype.ext
    have hval : (k₁ : H) * (ρ * (k₁ : H) * ρ⁻¹)⁻¹
        = (k₂ : H) * (ρ * (k₂ : H) * ρ⁻¹)⁻¹ := congrArg Subtype.val hk
    have hA : (k₁ : H) * ρ * (k₁ : H)⁻¹ * ρ⁻¹
        = (k₂ : H) * ρ * (k₂ : H)⁻¹ * ρ⁻¹ := by
      have h := hval
      rw [mul_inv_rev, inv_inv] at h
      simpa [mul_assoc] using h
    have hcomm : ρ * ((k₂ : H)⁻¹ * (k₁ : H)) * ρ⁻¹ = (k₂ : H)⁻¹ * (k₁ : H) := by
      have h4 : (k₂ : H)⁻¹ * ((k₁ : H) * ρ * (k₁ : H)⁻¹ * ρ⁻¹)
          = ρ * (k₂ : H)⁻¹ * ρ⁻¹ := by
        rw [hA]
        group
      have h5 := congrArg (fun x => x * (ρ * (k₁ : H) * ρ⁻¹)) h4
      simpa [mul_assoc] using h5.symm
    have haK : (k₂ : H)⁻¹ * (k₁ : H) ∈ K := K.mul_mem (K.inv_mem k₂.2) k₁.2
    have ha1 : (k₂ : H)⁻¹ * (k₁ : H) = 1 := h.rho_fpf_Q _ (hKQ haK) hcomm
    exact (inv_mul_eq_one.mp ha1).symm
  have hf_surj : Function.Surjective f := Finite.injective_iff_surjective.mp hf_inj
  obtain ⟨k, hk⟩ := hf_surj ⟨g⁻¹ * ρ * g * ρ⁻¹, hwK⟩
  refine ⟨(k : H), k.2, ?_⟩
  have hfq : (k : H) * (ρ * (k : H) * ρ⁻¹)⁻¹ = g⁻¹ * ρ * g * ρ⁻¹ :=
    congrArg Subtype.val hk
  have h1 : g * ((k : H) * (ρ * (k : H) * ρ⁻¹)⁻¹) = ρ * g * ρ⁻¹ := by
    have h := congrArg (fun x => g * x) hfq
    simpa [mul_assoc] using h
  have h2 : g * (k : H) = ρ * (g * (k : H)) * ρ⁻¹ := by
    have h3 := congrArg (fun x => x * (ρ * (k : H) * ρ⁻¹)) h1
    simpa [mul_assoc] using h3
  exact h2.symm

variable {Mh : Subgroup H} (hMh : IsZJMh y z v₁ v₂ Mh) include hMh

variable {Mc : Subgroup H} (hMc : IsZJMc ρ Q Mh Mc) include hMc

theorem Mc_fpf {K : Subgroup H} (hKQ : K ≤ Q) (hρK : ∀ k ∈ K, ρ * k * ρ⁻¹ ∈ K)
    (hKn : ∀ g k : H, k ∈ K → g * k * g⁻¹ ∈ K) {m : H} (hm : m ∈ Mc)
    (hc : ρ * m * ρ⁻¹ * m⁻¹ ∈ K) : m ∈ K := by
  obtain ⟨k, hk, hfix⟩ := h.fixed_coset_gen hKQ hρK hKn hc
  have hkQ : k ∈ Q := hKQ hk
  have hmk : m * k ∈ Mc := Mc.mul_mem hm (h.Q_le_Mc hMh hMc hkQ)
  have h1 : m * k = 1 := h.cent_rho_Mc hMh hMc hmk hfix
  have hm_eq : m = k⁻¹ := eq_inv_of_mul_eq_one_left h1
  rw [hm_eq]
  exact K.inv_mem hk

theorem Mc_fpf_Q {m : H} (hm : m ∈ Mc) (hc : ρ * m * ρ⁻¹ * m⁻¹ ∈ Q) : m ∈ Q := by
  exact h.Mc_fpf hMh hMc (K := Q) le_rfl h.rho_norm_Q h.normal_Q hm hc

theorem Mc_fpf_Y {m : H} (hm : m ∈ Mc) (hc : ρ * m * ρ⁻¹ * m⁻¹ ∈ Y) : m ∈ Y := by
  exact h.Mc_fpf hMh hMc (K := Y) h.Y_le_Q h.rho_norm_Y h.normal_Y hm hc

theorem Mc_fpf_V {m : H} (hm : m ∈ Mc) (hc : ρ * m * ρ⁻¹ * m⁻¹ ∈ V) : m ∈ V := by
  exact h.Mc_fpf hMh hMc (K := V)
    (fun x hx => h.Y_le_Q (by rw [h.Y_eq]; exact Subgroup.mem_sup_left hx))
    h.rho_norm_V h.normal_V hm hc

theorem Mc_le_closure {m : H} (hm : m ∈ Mc) (hmQ : m ∉ Q) :
    Mc ≤ closure ({m, ρ * m * ρ⁻¹} : Set H) ⊔ Q := by
  let m' : H := ρ * m * ρ⁻¹
  let T : Subgroup H := closure ({m, m'} : Set H) ⊔ Q
  have hm' : m' ∈ Mc := h.Mc_conj_rho hMh hMc hm
  have hQT : Q ≤ T := le_sup_right
  have hmT : m ∈ T := Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
  have hm'T : m' ∈ T := Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
  have hTMc : T ≤ Mc := by
    refine sup_le ((Subgroup.closure_le Mc).mpr ?_) (h.Q_le_Mc hMh hMc)
    rintro x (rfl | rfl)
    · exact hm
    · exact hm'
  have hm'Q : m' ∉ Q := by
    intro hq
    apply hmQ
    have h1 : ρ⁻¹ * m' * ρ ∈ Q := by
      have h := h.normal_Q ρ⁻¹ m' hq
      simpa using h
    rwa [show ρ⁻¹ * m' * ρ = m from by simp only [m']; group] at h1
  have hIdxMc : Q.relIndex Mc = 4 := by
    have hQMc : Q ≤ Mc := h.Q_le_Mc hMh hMc
    have hcardQsub : Nat.card (Q.subgroupOf Mc) = 64 := by
      have hEq := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQMc).toEquiv
      rw [h.card_Q] at hEq
      exact hEq
    have hmul := Subgroup.card_mul_index (Q.subgroupOf Mc)
    rw [hcardQsub, h.card_Mc hMh hMc] at hmul
    change (Q.subgroupOf Mc).index = 4
    omega
  have hprod : Q.relIndex T * T.relIndex Mc = 4 := by
    rw [← hIdxMc]
    exact Subgroup.relIndex_mul_relIndex Q T Mc hQT hTMc
  have hrel1 : Q.relIndex T ≠ 1 := by
    intro h1
    exact hmQ ((Subgroup.relIndex_eq_one.mp h1) hmT)
  have hrel2 : Q.relIndex T ≠ 2 := by
    intro h2
    obtain ⟨a, haT, ha⟩ := Subgroup.relIndex_eq_two_iff.mp h2
    have hmaQ : m * a ∈ Q := by
      have hh := ha m hmT
      rw [xor_iff_or_and_not_and] at hh
      rcases hh.1 with h | h
      · exact h
      · exact absurd h hmQ
    have hm'aQ : m' * a ∈ Q := by
      have hh := ha m' hm'T
      rw [xor_iff_or_and_not_and] at hh
      rcases hh.1 with h | h
      · exact h
      · exact absurd h hm'Q
    have hInvMem : (m * a)⁻¹ * (m' * a) ∈ Q := Q.mul_mem (Q.inv_mem hmaQ) hm'aQ
    have hconj : a⁻¹ * (m⁻¹ * m') * a ∈ Q := by
      have he : (m * a)⁻¹ * (m' * a) = a⁻¹ * (m⁻¹ * m') * a := by group
      rwa [he] at hInvMem
    have hm'mQ : m⁻¹ * m' ∈ Q := by
      have h1 := h.normal_Q a (a⁻¹ * (m⁻¹ * m') * a) hconj
      rwa [show a * (a⁻¹ * (m⁻¹ * m') * a) * a⁻¹ = m⁻¹ * m' from by group] at h1
    have hmm'Q : m' * m⁻¹ ∈ Q := by
      have h1 := h.normal_Q m (m⁻¹ * m') hm'mQ
      rwa [show m * (m⁻¹ * m') * m⁻¹ = m' * m⁻¹ from by group] at h1
    exact hmQ (h.Mc_fpf_Q hMh hMc hm (by simpa [m'] using hmm'Q))
  have hQT4 : Q.relIndex T = 4 := by
    have hdvd : Q.relIndex T ∣ 4 := ⟨T.relIndex Mc, hprod.symm⟩
    have hle : Q.relIndex T ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    have hne0 : Q.relIndex T ≠ 0 := by
      intro h0
      rw [h0] at hprod
      omega
    obtain ⟨c, hc⟩ := hdvd
    interval_cases Q.relIndex T <;> omega
  have hTrel1 : T.relIndex Mc = 1 := by
    rw [hQT4] at hprod
    omega
  have hle : Mc ≤ T := Subgroup.relIndex_eq_one.mp hTrel1
  simpa [T, m'] using hle

end ZJData

end CFSG.OddStandard.SmallF3.HarrisU33.S4B