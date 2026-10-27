module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterRestCard

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace U3C1OuterConf

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T R₂ D V : Subgroup G} {k : ℕ}

section UOne


theorem outerRest_chi_pow (hcf : U3C1OuterConf G L f t T R₂ D V k) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) (hk : 2 ≤ k) {u : G}
    (hu : u ∈ u3C1U L T V t) {r : G} (hr : r ∈ V) :
    r⁻¹ * (u * r * u⁻¹) ∈ V ∧ (r⁻¹ * (u * r * u⁻¹)) ^ 2 ^ k = 1 := by
  have hur : u * r * u⁻¹ ∈ V :=
    (mem_normalizer_iff.mp (hcf.normalizer_szR_le h hS2 hk hu.1).2.1 r).mp hr
  refine ⟨mul_mem (inv_mem hr) hur, ?_⟩
  rw [(Commute.mul_pow (hcf.comm _ (inv_mem hr) _ hur) _), conj_pow,
    U3Start.conj_szA₁_of_mem_u3C1U hu (hcf.outerRest_pow_mem_szA₁ hr), inv_pow, inv_mul_cancel]

theorem outerRest_sq_mem_sup (hcf : U3C1OuterConf G L f t T R₂ D V k) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) (hk : 2 ≤ k) {u : G}
    (hu : u ∈ u3C1U L T V t) : u ^ 2 ∈ szT₁ L T ⊔ V := by
  obtain ⟨htT, -⟩ := h.start_of_card_sylow hS2
  obtain ⟨-, hA₁card, -, -, -, hsqA₁, -⟩ := h.facts_of_card_sylow hS2
  have ht2 : t * t = 1 := by rw [← sq, h.sq_eq_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hVc : ∀ y ∈ szT₁ L T, ∀ u ∈ V, y * u = u * y := fun y hy u hu =>
    mem_centralizer_iff.mp (hcf.le_centralizer hu) y hy
  have htN : t ∈ normalizer ((szT₁ L T ⊔ V : Subgroup G) : Set G) :=
    h.sup_le_normalizer_sup_szT₁ hS2 hVc hcf.T_le (mem_sup_left htT)
  have huY : u ∈ normalizer (szR (szT₁ L T) V t : Set G) := hu.1
  have huA : ∀ b ∈ szA₁ (szT₁ L T), u * b * u⁻¹ = b := fun b hb =>
    U3Start.conj_szA₁_of_mem_u3C1U hu hb
  have hπ2 : outerRestPt t k (u ^ 2) = 1 := by
    rw [sq, hcf.outerRestPt_mul_of_conj h hS2 hk huY huY huA, ← sq,
      hsqA₁ _ (hcf.outerRestPt_mem h hS2 hk huY)]
  have hu2 : u ^ 2 ∈ u3C1U L T V t ⊓ outerRestStab L T V t :=
    mem_inf.mpr ⟨pow_mem hu 2, (hcf.mem_outerRestStab_iff h hS2 hk).mpr ⟨pow_mem huY 2, hπ2⟩⟩
  rw [hcf.outerRest_u3C1U_inf_stab h hS2 hk] at hu2
  rcases outerStep_mem_or_mul_mem ht2 htN hu2 with h1 | h1
  · exact h1
  exfalso
  have hinvV : ∀ r ∈ V, u ^ 2 * r * (u ^ 2)⁻¹ = r⁻¹ := by
    intro r hr
    have htr : t⁻¹ * r * t = r⁻¹ := by
      rw [htinv]; nth_rewrite 2 [← htinv]; exact hcf.inv r hr
    calc u ^ 2 * r * (u ^ 2)⁻¹ = (u ^ 2 * t) * (t⁻¹ * r * t) * (u ^ 2 * t)⁻¹ := by group
      _ = (u ^ 2 * t) * r⁻¹ * (u ^ 2 * t)⁻¹ := by rw [htr]
      _ = r⁻¹ := by rw [hcf.commute_of_mem_sup h1 (inv_mem hr), mul_inv_cancel_right]
  have h3 : 2 < Nat.card (szA₁ (szT₁ L T)) := by
    rw [hA₁card]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.two_le
  obtain ⟨b, hbA, -, -, hb1, -, -⟩ := exists_two_ne_one h3
  obtain ⟨r, hr, hrb⟩ := hcf.outerRest_exists_pow_eq h hS2 hbA
  apply hb1
  rw [← hrb]
  obtain ⟨hcV, hc1⟩ := hcf.outerRest_chi_pow h hS2 hk hu hr
  set c := r⁻¹ * (u * r * u⁻¹) with hcdef
  obtain ⟨s, hs, hs2⟩ := hcf.outerRest_exists_sq h hS2 hcV hc1
  obtain ⟨hc'V, hc'1⟩ := hcf.outerRest_chi_pow h hS2 hk hu hs
  set c' := s⁻¹ * (u * s * u⁻¹) with hc'def
  have hus : u * s * u⁻¹ = s * c' := by rw [hc'def]; group
  have hur : u * r * u⁻¹ = r * s ^ 2 := by rw [hs2, hcdef]; group
  have e1 : u ^ 2 * r * (u ^ 2)⁻¹ = r * s ^ 2 * (s * c') ^ 2 := by
    calc u ^ 2 * r * (u ^ 2)⁻¹ = u * (u * r * u⁻¹) * u⁻¹ := by rw [sq]; group
      _ = u * (r * s ^ 2) * u⁻¹ := by rw [hur]
      _ = (u * r * u⁻¹) * (u * s * u⁻¹) ^ 2 := by rw [sq, sq]; group
      _ = r * s ^ 2 * (s * c') ^ 2 := by rw [hur, hus]
  have e2 : r⁻¹ = r * s ^ 2 * (s ^ 2 * c' ^ 2) := by
    rw [← hinvV r hr, e1, (Commute.mul_pow (hcf.comm _ hs _ hc'V) 2)]
  have hs2V : s ^ 2 ∈ V := pow_mem hs 2
  set w := r * s ^ 2 * c' with hw
  have hwV : w ∈ V := mul_mem (mul_mem hr hs2V) hc'V
  have hw2 : w ^ 2 = 1 := by
    have e3 : w ^ 2 = r ^ 2 * (s ^ 2) ^ 2 * c' ^ 2 := by
      rw [hw, (Commute.mul_pow (hcf.comm _ (mul_mem hr hs2V) _ hc'V) 2),
        (Commute.mul_pow (hcf.comm _ hr _ hs2V) 2)]
    have e4 : r * r⁻¹ = r ^ 2 * (s ^ 2) ^ 2 * c' ^ 2 := by
      rw [e2]; simp only [sq, mul_assoc]
    rw [e3, ← e4, mul_inv_cancel]
  have hwk : w ^ 2 ^ k = 1 := by
    obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [hj, pow_succ', pow_mul, hw2, one_pow]
  have e5 : w ^ 2 ^ k = r ^ 2 ^ k := by
    rw [hw, (Commute.mul_pow (hcf.comm _ (mul_mem hr hs2V) _ hc'V) _),
      (Commute.mul_pow (hcf.comm _ hr _ hs2V) _), hs2, hc1, hc'1, mul_one, mul_one]
  rw [← e5, hwk]

theorem outerRest_comm_mem_sup (hcf : U3C1OuterConf G L f t T R₂ D V k) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) (hk : 2 ≤ k) :
    ∀ x ∈ u3C1U L T V t, ∀ y ∈ u3C1U L T V t, x * y * x⁻¹ * y⁻¹ ∈ szT₁ L T ⊔ V := by
  intro x hx y hy
  have hyN : y ∈ normalizer ((szT₁ L T ⊔ V : Subgroup G) : Set G) :=
    (hcf.normalizer_szR_le h hS2 hk hy.1).1
  have e : x * y * x⁻¹ * y⁻¹ = (x * y) ^ 2 * (y⁻¹ * (x ^ 2)⁻¹ * y) * (y ^ 2)⁻¹ := by
    simp only [sq]; group
  rw [e]
  refine mul_mem (mul_mem (hcf.outerRest_sq_mem_sup h hS2 hk (mul_mem hx hy)) ?_)
    (inv_mem (hcf.outerRest_sq_mem_sup h hS2 hk hy))
  exact (mem_normalizer_iff''.mp hyN _).mp (inv_mem (hcf.outerRest_sq_mem_sup h hS2 hk hx))

theorem outerRest_fix (hcf : U3C1OuterConf G L f t T R₂ D V k) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) (hk : 2 ≤ k) {d : G}
    (hdY : d ∈ normalizer (szR (szT₁ L T) V t : Set G)) (hdt : d * t = t * d)
    (htr : ∀ b ∈ szA₁ (szT₁ L T), ∀ b' ∈ szA₁ (szT₁ L T), b ≠ 1 → b' ≠ 1 →
      ∃ n : ℕ, (d ^ n)⁻¹ * b * d ^ n = b') :
    ∀ w ∈ u3C1U L T V t, w⁻¹ * (d⁻¹ * w * d) ∈ szT₁ L T ⊔ V →
      w ∈ szT₁ L T ⊔ V ∨ t⁻¹ * w ∈ szT₁ L T ⊔ V := by
  obtain ⟨htT, -⟩ := h.start_of_card_sylow hS2
  have ht2 : t * t = 1 := by rw [← sq, h.sq_eq_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hVc : ∀ y ∈ szT₁ L T, ∀ u ∈ V, y * u = u * y := fun y hy u hu =>
    mem_centralizer_iff.mp (hcf.le_centralizer hu) y hy
  have htN : t ∈ normalizer ((szT₁ L T ⊔ V : Subgroup G) : Set G) :=
    h.sup_le_normalizer_sup_szT₁ hS2 hVc hcf.T_le (mem_sup_left htT)
  intro w hw hwd
  have hdU : d ∈ normalizer (u3C1U L T V t : Set G) := hcf.le_normalizer_u3C1U_of_two_le h hS2 hk hdY
  have hdw : d⁻¹ * w * d ∈ u3C1U L T V t := (mem_normalizer_iff''.mp hdU w).mp hw
  have hwY : w ∈ normalizer (szR (szT₁ L T) V t : Set G) := hw.1
  have hwA : ∀ b ∈ szA₁ (szT₁ L T), w⁻¹ * b * w⁻¹⁻¹ = b := fun b hb =>
    U3Start.conj_szA₁_of_mem_u3C1U (inv_mem hw) hb
  have hzR : w⁻¹ * (d⁻¹ * w * d) ∈ szR (szT₁ L T) V t := sup_le_szR _ _ _ hwd
  have hz1 : outerRestPt t k (w⁻¹ * (d⁻¹ * w * d)) = 1 :=
    ((hcf.mem_outerRestStab_iff h hS2 hk).mp (szR_le_outerRestStab h hzR)).2
  have hπd1 : outerRestPt t k d = 1 := outerRestPt_of_comm hdt
  have hπd2 : outerRestPt t k d⁻¹ = 1 := outerRestPt_of_comm (Commute.inv_left hdt).eq
  have hπd : outerRestPt t k (d⁻¹ * w * d) = d⁻¹ * outerRestPt t k w * d := by
    rw [mul_assoc, hcf.outerRestPt_mul h hS2 hk (inv_mem hdY) (mul_mem hwY hdY),
      hcf.outerRestPt_mul h hS2 hk hwY hdY, hπd1, hπd2]
    group
  have hπinv : outerRestPt t k w⁻¹ = (outerRestPt t k w)⁻¹ := by
    rw [hcf.outerRestPt_inv h hS2 hk hwY]
    have := hwA _ (inv_mem (hcf.outerRestPt_mem h hS2 hk hwY))
    rwa [inv_inv] at this
  rw [hcf.outerRestPt_mul_of_conj h hS2 hk (inv_mem hwY) hdw.1 hwA, hπd, hπinv] at hz1
  have hw1 : outerRestPt t k w = 1 := by
    refine h.outerData_eq_one_of_conj_eq hS2 htr (hcf.outerRestPt_mem h hS2 hk hwY) ?_
    have := mul_eq_one_iff_eq_inv.mp hz1
    rwa [inv_inv] at this
  have hwR : w ∈ szR (szT₁ L T) V t := by
    rw [← hcf.outerRest_u3C1U_inf_stab h hS2 hk]
    exact mem_inf.mpr ⟨hw, (hcf.mem_outerRestStab_iff h hS2 hk).mpr ⟨hwY, hw1⟩⟩
  rcases outerStep_mem_or_mul_mem ht2 htN hwR with h1 | h1
  · exact Or.inl h1
  · right
    rw [show t⁻¹ * w = t⁻¹ * (w * t) * t⁻¹⁻¹ by rw [htinv]; group]
    exact (mem_normalizer_iff.mp (inv_mem htN) _).mp h1

theorem outerRest_exists_U₁ (hcf : U3C1OuterConf G L f t T R₂ D V k) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) (hk : 2 ≤ k) {d : G}
    (hC : U3C1CartanFpf L T D d) :
    ∃ U₁ : Subgroup G, U₁ ≤ u3C1U L T V t ∧ u3C1U L T V t ≤ normalizer (U₁ : Set G) ∧
      U₁ ⊔ zpowers t = u3C1U L T V t ∧ t ∉ U₁ ∧ U₁ ⊓ szR (szT₁ L T) V t = szT₁ L T ⊔ V ∧
      D ≤ normalizer (U₁ : Set G) ∧ T ≤ normalizer (U₁ : Set G) ∧ szT₁ L T ⊔ V ≤ U₁ := by
  obtain ⟨htT, -⟩ := h.start_of_card_sylow hS2
  have ht2 : t * t = 1 := by rw [← sq, h.sq_eq_one]
  have hVc : ∀ y ∈ szT₁ L T, ∀ u ∈ V, y * u = u * y := fun y hy u hu =>
    mem_centralizer_iff.mp (hcf.le_centralizer hu) y hy
  have htN : t ∈ normalizer ((szT₁ L T ⊔ V : Subgroup G) : Set G) :=
    h.sup_le_normalizer_sup_szT₁ hS2 hVc hcf.T_le (mem_sup_left htT)
  have hHU : szT₁ L T ⊔ V ≤ u3C1U L T V t := (sup_le_szR _ _ _).trans (hcf.szR_le_u3C1U h hS2)
  have hUH : u3C1U L T V t ≤ normalizer ((szT₁ L T ⊔ V : Subgroup G) : Set G) := fun u hu =>
    (hcf.normalizer_szR_le h hS2 hk hu.1).1
  have hUN := hcf.le_normalizer_u3C1U_of_two_le h hS2 hk
  have hcomm := hcf.outerRest_comm_mem_sup h hS2 hk
  have hsq : ∀ x ∈ u3C1U L T V t, x ^ 2 ∈ szT₁ L T ⊔ V := fun x hx =>
    hcf.outerRest_sq_mem_sup h hS2 hk hx
  have hdD := hC.mem
  have hdL : d ∈ L := hC.le hdD
  have hdt : d * t = t * d := mem_centralizer_iff.mp h.mem d hdL
  have hdT : d ∈ normalizer (szT₁ L T : Set G) := hC.le_normalizer hdD
  have hdY : d ∈ normalizer (szR (szT₁ L T) V t : Set G) :=
    mem_normalizer_szR_of hdT (hcf.D_le hdD) hdt
  have hdU : d ∈ normalizer (u3C1U L T V t : Set G) := hUN hdY
  have hdH : d ∈ normalizer ((szT₁ L T ⊔ V : Subgroup G) : Set G) :=
    (hcf.normalizer_szR_le h hS2 hk hdY).1
  have hodd : Odd (orderOf d) := Odd.of_dvd_nat hC.odd (Subgroup.orderOf_dvd_natCard D hdD)
  have htU : t ∈ u3C1U L T V t := hcf.szR_le_u3C1U h hS2 (mem_szR_right _ _ _)
  have htH : t ∉ szT₁ L T ⊔ V := hcf.outerRest_t_not_mem h hS2 hk
  have hfix := hcf.outerRest_fix h hS2 hk hdY hdt hC.trans
  obtain ⟨U₁, hHU₁, hU₁U, hUU₁, htU₁, hsupU₁, hdU₁⟩ :=
    exists_complement_of_coprime hHU hUH hcomm hsq hdU hdH hodd htU htH hdt hfix
  have hinf : U₁ ⊓ szR (szT₁ L T) V t = szT₁ L T ⊔ V := by
    refine le_antisymm (fun x hx => ?_) (le_inf hHU₁ (sup_le_szR _ _ _))
    obtain ⟨hxU₁, hxR⟩ := mem_inf.mp hx
    rcases outerStep_mem_or_mul_mem ht2 htN hxR with h1 | h1
    · exact h1
    · exfalso
      apply htU₁
      rw [show t = x⁻¹ * (x * t) by group]
      exact mul_mem (inv_mem hxU₁) (hHU₁ h1)
  have hDU₁ : D ≤ normalizer (U₁ : Set G) := fun x hx => by
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp (hC.le_zpowers hx)
    exact zpow_mem hdU₁ n
  have hTY := hcf.outerRest_T_le h hS2
  have hmN : ∀ m ∈ T, (∀ x ∈ D, m * x * m⁻¹ ∈ D) → m ∈ normalizer (U₁ : Set G) := by
    intro m hmT hmD
    have hmY := hTY hmT
    have hmt : m * t = t * m := mem_centralizer_singleton_iff.mp (h.le hmT)
    set X := U₁.comap (MulAut.conj m).toMonoidHom with hXdef
    have hmemX : ∀ y, y ∈ X ↔ m * y * m⁻¹ ∈ U₁ := fun y => by
      rw [hXdef, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hXU : X ≤ u3C1U L T V t := fun y hy => by
      have h1 := hU₁U ((hmemX y).mp hy)
      have h2 := (mem_normalizer_iff''.mp (hUN hmY) _).mp h1
      rwa [show m⁻¹ * (m * y * m⁻¹) * m = y by group] at h2
    have htX : t ∉ X := fun ht => htU₁ (by
      have := (hmemX t).mp ht
      rwa [show m * t * m⁻¹ = t by rw [hmt, mul_inv_cancel_right]] at this)
    have hdX : d ∈ normalizer (X : Set G) := by
      refine mem_normalizer_of_forall_inv_mul_mul_mem fun y hy => (hmemX _).mpr ?_
      have hmd : m * d * m⁻¹ ∈ normalizer (U₁ : Set G) := hDU₁ (hmD d hdD)
      have h1 := (mem_normalizer_iff''.mp hmd _).mp ((hmemX y).mp hy)
      rwa [show (m * d * m⁻¹)⁻¹ * (m * y * m⁻¹) * (m * d * m⁻¹) = m * (d⁻¹ * y * d) * m⁻¹ by
        group] at h1
    have hHX : szT₁ L T ⊔ V ≤ X := fun z hz => (hmemX z).mpr
      (hHU₁ ((mem_normalizer_iff.mp (hcf.normalizer_szR_le h hS2 hk hmY).1 z).mp hz))
    have hle := outerData_le_of_complement hcomm hdt htU hfix hXU htX hdX hHX hHU₁ hU₁U hsupU₁
      hdU₁
    refine mem_normalizer_of_forall_inv_mul_mul_mem fun x hx => hle ((hmemX _).mpr ?_)
    rwa [show m * (m⁻¹ * x * m) * m⁻¹ = x by group]
  have hTU₁ : T ≤ normalizer (U₁ : Set G) := by
    intro s hs
    obtain ⟨n, hnT₁, hnD⟩ := hC.conj s hs
    have hm := hmN (n⁻¹ * s) (mul_mem (inv_mem (szT₁_le_left L T hnT₁)) hs) hnD
    have hn : n ∈ normalizer (U₁ : Set G) :=
      Subgroup.le_normalizer (hHU₁ (mem_sup_left hnT₁))
    rw [show s = n * (n⁻¹ * s) by group]
    exact mul_mem hn hm
  exact ⟨U₁, hU₁U, hUU₁, hsupU₁, htU₁, hinf, hDU₁, hTU₁, hHU₁⟩

end UOne

end U3C1OuterConf

end CFSG.SeitzReduction.RankOne
