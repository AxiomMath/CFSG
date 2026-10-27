module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCK
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzRTr
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.Thompson
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.S3Gen
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCQDef

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33 CFSG.GH74.GLS.Stage1.Thm6.Sec13

variable {G : Type} [Group G]

theorem fzc_sy3_conj_mem_sup {N : Subgroup G} {u s : G} (hu : u * u ∈ N)
    (huN : ∀ x ∈ N, u * x * u⁻¹ ∈ N) (hsN : ∀ x ∈ N, s * x * s⁻¹ ∈ N) (hsu : s * u = u * s) :
    ∀ x ∈ N ⊔ zpowers u, s * x * s⁻¹ ∈ N ⊔ zpowers u := by
  intro x hx
  obtain ⟨n, hn, hxn | hxn⟩ := (mem_sup_zpowers_sq hu huN).1 hx
  · rw [hxn]
    exact mem_sup_left (hsN n hn)
  · rw [hxn]
    have e : s * (n * u) * s⁻¹ = (s * n * s⁻¹) * u := by
      calc s * (n * u) * s⁻¹ = (s * n * s⁻¹) * (s * u) * s⁻¹ := by group
        _ = (s * n * s⁻¹) * (u * s) * s⁻¹ := by rw [hsu]
        _ = (s * n * s⁻¹) * u := by group
    rw [e]
    exact (N ⊔ zpowers u).mul_mem (mem_sup_left (hsN n hn)) (mem_sup_right (mem_zpowers u))

theorem fzc_sy3_mul_conj_mem {N : Subgroup G} {a b s : G} (ha : a * a ∈ N)
    (haN : ∀ x ∈ N, a * x * a⁻¹ ∈ N) (hb : b * b ∈ N) (hbN : ∀ x ∈ N, b * x * b⁻¹ ∈ N)
    (hab : a * b = b * a) (hsN : ∀ x ∈ N, s * x * s⁻¹ ∈ N) (hsa : s * a = a * s)
    (hsb : s * b = b * s) : ∀ m ∈ (N ⊔ zpowers a) ⊔ zpowers b, m * (s * m * s⁻¹) ∈ N := by
  intro m hm
  have hsa' : s * a * s⁻¹ = a := by rw [hsa]; group
  have hsb' : s * b * s⁻¹ = b := by rw [hsb]; group
  have hb1 : b * b ∈ N ⊔ zpowers a := mem_sup_left hb
  obtain ⟨m₁, hm₁, hmm | hmm⟩ :=
    (mem_sup_zpowers_sq hb1 (fzc_sy3_conj_mem_sup ha haN hbN hab.symm)).1 hm <;> rw [hmm] <;>
    obtain ⟨n, hn, hmn | hmn⟩ := (mem_sup_zpowers_sq ha haN).1 hm₁ <;> rw [hmn]
  · exact N.mul_mem hn (hsN n hn)
  · have e : n * a * (s * (n * a) * s⁻¹) = n * (a * (s * n * s⁻¹) * a⁻¹) * (a * a) := by
      calc n * a * (s * (n * a) * s⁻¹) = n * a * ((s * n * s⁻¹) * (s * a * s⁻¹)) := by group
        _ = n * a * ((s * n * s⁻¹) * a) := by rw [hsa']
        _ = n * (a * (s * n * s⁻¹) * a⁻¹) * (a * a) := by group
    rw [e]
    exact N.mul_mem (N.mul_mem hn (haN _ (hsN n hn))) ha
  · have e : n * b * (s * (n * b) * s⁻¹) = n * (b * (s * n * s⁻¹) * b⁻¹) * (b * b) := by
      calc n * b * (s * (n * b) * s⁻¹) = n * b * ((s * n * s⁻¹) * (s * b * s⁻¹)) := by group
        _ = n * b * ((s * n * s⁻¹) * b) := by rw [hsb']
        _ = n * (b * (s * n * s⁻¹) * b⁻¹) * (b * b) := by group
    rw [e]
    exact N.mul_mem (N.mul_mem hn (hbN _ (hsN n hn))) hb
  · have e : n * a * b * (s * (n * a * b) * s⁻¹) =
        n * (a * (b * (s * n * s⁻¹) * b⁻¹) * a⁻¹) * ((a * a) * (b * b)) := by
      calc n * a * b * (s * (n * a * b) * s⁻¹)
          = n * a * b * ((s * n * s⁻¹) * (s * a * s⁻¹) * (s * b * s⁻¹)) := by group
        _ = n * a * b * ((s * n * s⁻¹) * a * b) := by rw [hsa', hsb']
        _ = n * (a * (b * (s * n * s⁻¹) * b⁻¹) * a⁻¹) * (a * (b * a) * b) := by group
        _ = n * (a * (b * (s * n * s⁻¹) * b⁻¹) * a⁻¹) * ((a * a) * (b * b)) := by
          rw [← hab]; group
    rw [e]
    exact N.mul_mem (N.mul_mem hn (haN _ (hbN _ (hsN n hn)))) (N.mul_mem ha hb)

variable [Finite G]

theorem fzc_sy3_a_core [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    {P V : Subgroup G} {t q lam : G} (hV : FzSylow V)
    (hVeq : V = (P ⊔ zpowers q) ⊔ zpowers lam) (hq4 : orderOf q = 4) (hqt : q ^ 2 = t)
    (hlam2 : lam * lam = 1) (hqlam : q * lam = lam * q)
    (hqP : ∀ x ∈ P, q * x * q⁻¹ ∈ P) (hlP : ∀ x ∈ P, lam * x * lam⁻¹ ∈ P)
    (hPq : P ⊓ zpowers q = ⊥) (hlR : lam ∉ P ⊔ zpowers q)
    (hK : ∀ g : G, g * t * g⁻¹ ∉ P) : False := by
  have hq4' : q ^ 4 = 1 := by rw [← hq4]; exact pow_orderOf_eq_one q
  have htq : t = q * q := by rw [← hqt, pow_two]
  have htt : t * t = 1 := by
    rw [← hq4', htq]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have htP : ∀ x ∈ P, t * x * t⁻¹ ∈ P := by
    intro x hx
    have e : t * x * t⁻¹ = q * (q * x * q⁻¹) * q⁻¹ := by rw [htq]; group
    rw [e]
    exact hqP _ (hqP x hx)
  have htnP : t ∉ P := by simpa using hK 1
  have htlam : t * lam = lam * t := by
    rw [htq]
    calc q * q * lam = q * (q * lam) := by group
      _ = q * (lam * q) := by rw [hqlam]
      _ = (q * lam) * q := by group
      _ = (lam * q) * q := by rw [hqlam]
      _ = lam * (q * q) := by group
  have hqt' : q * t = t * q := by rw [htq]; group
  have htt1 : t * t ∈ P := by rw [htt]; exact P.one_mem
  have hll : lam * lam ∈ P := by rw [hlam2]; exact P.one_mem
  have hlP1 : ∀ x ∈ P ⊔ zpowers t, lam * x * lam⁻¹ ∈ P ⊔ zpowers t :=
    fzc_sy3_conj_mem_sup htt1 htP hlP htlam.symm
  have hqP1 : ∀ x ∈ P ⊔ zpowers t, q * x * q⁻¹ ∈ P ⊔ zpowers t :=
    fzc_sy3_conj_mem_sup htt1 htP hqP hqt'
  have hll1 : lam * lam ∈ P ⊔ zpowers t := mem_sup_left hll
  have hqM : ∀ x ∈ (P ⊔ zpowers t) ⊔ zpowers lam, q * x * q⁻¹ ∈ (P ⊔ zpowers t) ⊔ zpowers lam :=
    fzc_sy3_conj_mem_sup hll1 hlP1 hqP1 hqlam
  have hqq : q * q ∈ (P ⊔ zpowers t) ⊔ zpowers lam := by
    rw [← htq]
    exact mem_sup_left (mem_sup_right (mem_zpowers t))
  have htR : t ∈ P ⊔ zpowers q := by
    rw [htq]
    exact mul_mem (mem_sup_right (mem_zpowers q)) (mem_sup_right (mem_zpowers q))
  have hP1R : P ⊔ zpowers t ≤ P ⊔ zpowers q := sup_le le_sup_left (zpowers_le.2 htR)
  have hqnM : q ∉ (P ⊔ zpowers t) ⊔ zpowers lam := by
    intro hqM'
    obtain ⟨m₁, hm₁, hq1 | hq1⟩ := (mem_sup_zpowers_sq hll1 hlP1).1 hqM'
    · obtain ⟨p, hp, hq2 | hq2⟩ := (mem_sup_zpowers_sq htt1 htP).1 hm₁
      · have h1 : q ∈ P ⊓ zpowers q := ⟨by rw [hq1, hq2]; exact hp, mem_zpowers q⟩
        rw [hPq, mem_bot] at h1
        rw [h1, orderOf_one] at hq4
        norm_num at hq4
      · have h1 : q * t⁻¹ ∈ P ⊓ zpowers q := by
          refine ⟨?_, ?_⟩
          · rw [hq1, hq2]
            simpa using hp
          · rw [htq]
            exact (zpowers q).mul_mem (mem_zpowers q)
              ((zpowers q).inv_mem ((zpowers q).mul_mem (mem_zpowers q) (mem_zpowers q)))
        rw [hPq, mem_bot, mul_inv_eq_one] at h1
        have h2 : orderOf t = 2 := by
          apply orderOf_eq_prime
          · rw [pow_two, htt]
          · intro h3
            exact htnP (h3 ▸ P.one_mem)
        rw [h1, h2] at hq4
        norm_num at hq4
    · apply hlR
      have e : lam = m₁⁻¹ * q := by rw [hq1]; group
      rw [e]
      exact mul_mem (inv_mem (hP1R hm₁)) (mem_sup_right (mem_zpowers q))
  have hVM : V = ((P ⊔ zpowers t) ⊔ zpowers lam) ⊔ zpowers q := by
    rw [hVeq]
    apply le_antisymm
    · refine sup_le (sup_le ?_ le_sup_right) ?_
      · exact le_sup_left.trans (le_sup_left.trans le_sup_left)
      · exact (le_sup_right : zpowers lam ≤ (P ⊔ zpowers t) ⊔ zpowers lam).trans le_sup_left
    · exact sup_le (sup_le (hP1R.trans le_sup_left) le_sup_right) (le_sup_right.trans le_sup_left)
  have hMV : (P ⊔ zpowers t) ⊔ zpowers lam ≤ V := by rw [hVM]; exact le_sup_left
  have hqV : q ∈ V := by rw [hVM]; exact mem_sup_right (mem_zpowers q)
  have hrel : ((P ⊔ zpowers t) ⊔ zpowers lam).relIndex V = 2 := by
    have hc := card_sup_zpowers_sq hqq hqM hqnM
    have h1 := Subgroup.relIndex_mul_card (H := (P ⊔ zpowers t) ⊔ zpowers lam)
      (K := ((P ⊔ zpowers t) ⊔ zpowers lam) ⊔ zpowers q)
    rw [inf_eq_left.mpr le_sup_left, hc] at h1
    have hpos : 0 < Nat.card ↥((P ⊔ zpowers t) ⊔ zpowers lam) := Nat.card_pos
    rw [hVM]
    exact Nat.eq_of_mul_eq_mul_right hpos h1
  have hPM : ∀ m ∈ (P ⊔ zpowers t) ⊔ zpowers lam, m * (q * m * q⁻¹) ∈ P :=
    fzc_sy3_mul_conj_mem htt1 htP hll hlP htlam hqP hqt' hqlam
  have hPM1 : ∀ m ∈ (P ⊔ zpowers t) ⊔ zpowers lam, m * m ∈ P := by
    intro m hm
    have h1 := fzc_sy3_mul_conj_mem (s := 1) htt1 htP hll hlP htlam
      (fun x hx => by simpa using hx) (by group) (by group) m hm
    simpa using h1
  have hinv : ∀ v ∈ V, v * v = 1 → v ∈ (P ⊔ zpowers t) ⊔ zpowers lam := by
    intro v hv hv2
    rw [hVM] at hv
    obtain ⟨m, hm, rfl | rfl⟩ := (mem_sup_zpowers_sq hqq hqM).1 hv
    · exact hm
    · exfalso
      apply htnP
      have e : t = (m * (q * m * q⁻¹))⁻¹ * (m * q * (m * q)) := by rw [htq]; group
      rw [e, hv2, mul_one]
      exact P.inv_mem (hPM m hm)
  have hpow : ∀ (g : G) (k : ℕ), g⁻¹ * q ^ (2 * k) * g ∈ V →
      g⁻¹ * q ^ (2 * k) * g ∈ (P ⊔ zpowers t) ⊔ zpowers lam := by
    intro g k hg
    refine hinv _ hg ?_
    have e : g⁻¹ * q ^ (2 * k) * g * (g⁻¹ * q ^ (2 * k) * g) = g⁻¹ * (q ^ 4) ^ k * g := by
      rw [← pow_mul, show 4 * k = 2 * k + 2 * k by ring, pow_add]
      group
    rw [e, hq4', one_pow]
    group
  have hconj : ∀ g : G, g⁻¹ * q * g ∉ (P ⊔ zpowers t) ⊔ zpowers lam := by
    intro g hg
    apply hK g⁻¹
    have e : g⁻¹ * t * g⁻¹⁻¹ = (g⁻¹ * q * g) * (g⁻¹ * q * g) := by rw [htq]; group
    rw [e]
    exact hPM1 _ hg
  exact CFSG.EvenSporadicStandard.TwoHS.false_of_thompson_pow hnab hV.1 hV.2 hMV hrel hqV hqnM
    hpow hconj

theorem fzc_sy3_a_of {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}
    (h : FzCCtx G t L S x₁ x₂ lam rho) (hq : FzCQFacts t S x₁ x₂ lam rho)
    (hr : Nat.card (twoCore t) = 4) (hV : FzSylow (l41V S t x₁ x₂))
    (ht : t ∉ fzP t x₁ x₂ rho) : False := by
  haveI := h.simple
  have hctx := h.ctx
  obtain ⟨q, hKq, hq4, hqt⟩ := hq.K_four hr
  have hlam2 : lam * lam = 1 := by
    have h1 := pow_orderOf_eq_one lam
    rw [hctx.wreath.ord_lam] at h1
    simpa [pow_two] using h1
  have hqK : q ∈ twoCore t := by rw [hKq]; exact mem_zpowers q
  have hKR : twoCore t ≤ fzR t x₁ x₂ := by
    rw [hq.R_eq_PK]
    exact le_sup_right
  have hPR : fzP t x₁ x₂ rho ≤ fzR t x₁ x₂ := by
    rw [hq.R_eq_PK]
    exact le_sup_left
  have hqlam : q * lam = lam * q := by
    have hqC : q ∈ Subgroup.centralizer (L : Set G) := by
      have h1 := hqK
      rw [← hctx.hyp.centralizer_eq] at h1
      exact h1.1
    have hlamL : lam ∈ L := by
      have h1 : lam ∈ wreathGrp x₁ x₂ lam := subset_closure (by simp)
      rw [← hctx.inf_eq] at h1
      exact h1.2
    exact (Subgroup.mem_centralizer_iff.1 hqC lam hlamL).symm
  have hRq : fzR t x₁ x₂ = fzP t x₁ x₂ rho ⊔ zpowers q := by rw [hq.R_eq_PK, hKq]
  have hP2 : IsPGroup 2 (fzP t x₁ x₂ rho) := hV.1.to_le (hPR.trans hq.R_le_V)
  refine fzc_sy3_a_core (fzr_nonabelian_of_wreath hctx.wreath) hV ?_ hq4 hqt hlam2 hqlam
    (hq.P_normal_R q (hKR hqK)) hq.lam_norm_P ?_ ?_ ?_
  · rw [hq.V_eq, hRq]
  · rw [← hKq]
    exact hq.inf_P_K_of_not_mem ht
  · rw [← hRq]
    exact hq.lam_not_mem_R
  · intro g hg
    exact fzc_core42_of h hq.not_conj_z hP2 hq.rho_norm_P hq.lam_norm_P (hq.P_fpf_of_not_mem ht) g
      (mem_sup_left hg)

end CFSG.OddStandard.SmallF3.FritzII
