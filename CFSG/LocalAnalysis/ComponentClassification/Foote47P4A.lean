module

public import CFSG.LocalAnalysis.ComponentClassification.Foote47P4Aut
public import CFSG.LocalAnalysis.ComponentClassification.Foote47Prop27

public section

namespace CFSG.ComponentClassification.Foote47

open CFSG Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

namespace P4Data

variable {M T S P : Subgroup G} {t z w : G}

theorem commutator_centralizer_le_innerAct (h : FooteSec4 G L) (hOut : FooteL2OutAbelian)
    (d : P4Data L M T S P t z w) :
    ⁅centralizer ({z} : Set G), centralizer ({z} : Set G)⁆ ≤ innerAct (footeF L z) := by
  obtain ⟨Q₀, hd⟩ := d.c.hd
  have dz := zData_of h d.c.hv.hM d.c.hTsyl hd.hz hd.hzT hd.hzc
  obtain ⟨-, ⟨ε⟩⟩ := isSimpleGroup_quotient_of_mem_footeFamilyOf h.hGA h.hGC h.hSA
    h.footeFamilyType h.hrank2 dz.hKmax.1 dz.hKF
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact commutator_mem_innerAct hOut h.footeFamilyType ε (dz.centralizer_le_normalizer h ha)
    (dz.centralizer_le_normalizer h hb)

theorem false_of_outer (h : FooteSec4 G L) (hOut : FooteL2OutAbelian)
    (hFI : FooteFourgroupInner) (hCI : Foote47CentralInvolution) (d : P4Data L M T S P t z w)
    (hA : ∀ g : G, Valid P t z w g → g * t * g⁻¹ ∉ innerAct (footeF L t)) {g : G}
    (hg : Valid P t z w g) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q₀, hd⟩ := d.c.hd
  obtain ⟨n, hnT, -, hn⟩ := hd.hn
  obtain ⟨-, ⟨εt⟩⟩ := d.quotient_t h
  have htt : t * t = 1 := by rw [← sq, ← d.c.hv.ht]; exact pow_orderOf_eq_one t
  have hzz : z * z = 1 := by rw [← sq, ← hd.hz]; exact pow_orderOf_eq_one z
  have hww : w * w = 1 := by rw [← sq, ← d.hw]; exact pow_orderOf_eq_one w
  have hzt : z * t = t * z := (hd.hzc t d.c.htT).symm
  have hwt : w * t = t * w := (d.hwc t (d.T_le_S d.c.htT)).symm
  have hwz : w * z = z * w := (d.hwc z (d.T_le_S hd.hzT)).symm
  have ht1 : t ≠ 1 := fun h1 => by have := d.c.hv.ht; rw [h1, orderOf_one] at this; omega
  have hz1 : z ≠ 1 := fun h1 => by have := hd.hz; rw [h1, orderOf_one] at this; omega
  have hw1 : w ≠ 1 := fun h1 => by have := d.hw; rw [h1, orderOf_one] at this; omega
  have hsq : ∀ {a : G}, a * a = 1 → a ^ 2 = 1 := fun {a} ha => by rw [sq]; exact ha
  have hord : ∀ {a : G}, a * a = 1 → a ≠ 1 → orderOf a = 2 := fun {a} ha ha1 =>
    orderOf_eq_prime (hsq ha) ha1
  have hPN := d.P_le_normalizer h
  have hgz := Valid.not_mem_centralizer h d hg
  have hc2 : ∀ {a : G}, a * a = 1 → (g * a * g⁻¹) * (g * a * g⁻¹) = 1 := fun {a} ha => by
    rw [show g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ by group, ha]; group
  have hcc : ∀ {a b : G}, a * b = b * a →
      (g * a * g⁻¹) * (g * b * g⁻¹) = (g * b * g⁻¹) * (g * a * g⁻¹) := fun {a b} hab => by
    rw [show g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ by group, hab]; group
  have hcm : ∀ a b : G, (g * a * g⁻¹) * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := fun a b => by
    group
  have hcne : ∀ {a b : G}, a ≠ b → g * a * g⁻¹ ≠ g * b * g⁻¹ := fun {a b} hab h1 => hab (by
    have h2 := congrArg (fun x => g⁻¹ * x * g) h1
    simp only [show ∀ x : G, g⁻¹ * (g * x * g⁻¹) * g = x from fun x => by group] at h2
    exact h2)
  have hc1 : ∀ {a : G}, a ≠ 1 → g * a * g⁻¹ ≠ 1 := fun {a} ha h1 => ha (by
    have h2 := congrArg (fun x => g⁻¹ * x * g) h1
    simp only [show g⁻¹ * (g * a * g⁻¹) * g = a by group, mul_one, inv_mul_cancel] at h2
    exact h2)
  obtain ⟨ts, hts⟩ : ∃ x, x = g * t * g⁻¹ := ⟨_, rfl⟩
  obtain ⟨zs, hzs⟩ : ∃ x, x = g * z * g⁻¹ := ⟨_, rfl⟩
  obtain ⟨ws, hws⟩ : ∃ x, x = g * w * g⁻¹ := ⟨_, rfl⟩
  have htsP : ts ∈ P := hts ▸ hg.ht
  have hzsP : zs ∈ P := hzs ▸ hg.hz
  have hwsP : ws ∈ P := hws ▸ hg.hw
  have hts2 : ts * ts = 1 := hts ▸ hc2 htt
  have hzs2 : zs * zs = 1 := hzs ▸ hc2 hzz
  have hws2 : ws * ws = 1 := hws ▸ hc2 hww
  have hts1 : ts ≠ 1 := hts ▸ hc1 ht1
  have hzs1 : zs ≠ 1 := hzs ▸ hc1 hz1
  have hws1 : ws ≠ 1 := hws ▸ hc1 hw1
  have hzsts : zs ≠ ts := by rw [hzs, hts]; exact hcne hd.t_ne_z.symm
  have hwt' : w ≠ t := fun h1 => (d.not_isConj_t).2.1 (h1 ▸ IsConj.refl t)
  have hwsts : ws ≠ ts := by rw [hws, hts]; exact hcne hwt'
  have htzc : ts * zs = zs * ts := by rw [hts, hzs]; exact hcc hzt.symm
  have htwc : ts * ws = ws * ts := by rw [hts, hws]; exact hcc hwt.symm
  have hzwc : zs * ws = ws * zs := by rw [hzs, hws]; exact hcc hwz.symm
  have htsI : ts ∉ innerAct (footeF L t) := hts ▸ hA g hg
  have htzI : ts * zs ∉ innerAct (footeF L t) := by
    obtain ⟨hv, heq⟩ := Valid.mul_inv d hg hnT hn
    rw [hts, hzs, ← heq]
    exact hA _ hv
  obtain ⟨htz', htw', htzw'⟩ := d.not_isConj_t
  have htz := d.isConj_t_tz
  have htwtzw := d.isConj_tw_tzw
  have hzzs : IsConj z zs := hzs ▸ isConj_conj z g
  have hwws : IsConj w ws := hws ▸ isConj_conj w g
  have htwtws : IsConj (t * w) (ts * ws) := by rw [hts, hws, hcm]; exact isConj_conj _ g
  have hzwzws : IsConj (z * w) (zs * ws) := by rw [hzs, hws, hcm]; exact isConj_conj _ g
  have htzwtzws : IsConj (t * z * w) (zs * (ts * ws)) := by
    rw [hzs, hts, hws, hcm, hcm, show z * (t * w) = t * z * w by rw [← mul_assoc, hzt]]
    exact isConj_conj _ g
  have hfour : ∀ {a b : G}, a * a = 1 → b * b = 1 → a ≠ 1 → b ≠ 1 → b ≠ a → a * b = b * a →
      a ∈ P → b ∈ P → a ∉ innerAct (footeF L t) →
        b ∈ innerAct (footeF L t) ∨ a * b ∈ innerAct (footeF L t) := by
    intro a b ha hb ha1 hb1 hba hab haP hbP haI
    have hV := isKleinFour_sup_zpowers (hsq ha) (hsq hb) ha1 hb1 hba hab
    obtain ⟨v, hv, hv1, hvI⟩ := exists_mem_innerAct_of_card_four hFI h.footeFamilyType εt
      (sup_le (zpowers_le.mpr (hPN haP)) (zpowers_le.mpr (hPN hbP)))
      (fun v hv => by rw [← sq]; exact sq_eq_one_of_isKleinFour hV hv) hV.card_four
    rcases mem_of_isKleinFour hV (mem_sup_left (mem_zpowers a)) (mem_sup_right (mem_zpowers b))
      hv ha1 hb1 hba.symm with h1 | h1 | h1 | h1
    · exact absurd h1 hv1
    · exact absurd (h1 ▸ hvI) haI
    · exact Or.inl (h1 ▸ hvI)
    · exact Or.inr (h1 ▸ hvI)
  have hzQ : z ∈ T ⊓ centralizer ({t} : Set G) :=
    mem_inf.mpr ⟨hd.hzT, mem_centralizer_singleton_iff.mpr hzt⟩
  have htQ : t ∈ T ⊓ centralizer ({t} : Set G) :=
    mem_inf.mpr ⟨d.c.htT, mem_centralizer_singleton_iff.mpr rfl⟩
  have hqQ : ∀ {q : G}, (q = t ∨ q = t * z) → q ∈ T ⊓ centralizer ({t} : Set G) := by
    intro q hq
    rcases hq with h1 | h1 <;> rw [h1]
    · exact htQ
    · exact mul_mem htQ hzQ
  have hcy : ∀ {x y q : G}, x = y * (q * w) * y⁻¹ → IsConj (q * w) x := fun {x y q} hx =>
    isConj_iff.mpr ⟨y, hx.symm⟩
  have hzsI : zs ∈ innerAct (footeF L t) := by
    rcases hfour hts2 hzs2 hts1 hzs1 hzsts htzc htsP hzsP htsI with h1 | h1
    · exact h1
    · exact absurd h1 htzI
  obtain ⟨q, u, hq, huR, hqu, hzq⟩ : ∃ q u : G, (q = t ∨ q = t * z) ∧ u ∈ P ⊓ footeF L t ∧
      zs = q * u ∧ IsConj z (q * w) := by
    rcases d.inv_cases h hzsP hzsI (hord hzs2 hzs1) with h1 | ⟨q, u, hq, huR, -, hqu, y, -, -, hy⟩
    · exfalso
      rcases h1 with h1 | h1 | h1
      · apply hgz
        rw [mem_centralizer_singleton_iff]
        calc g * z = g * z * g⁻¹ * g := by group
          _ = z * g := by rw [← hzs, h1]
      · exact htz' (h1 ▸ hzzs).symm
      · exact htz' (htz.trans (h1 ▸ hzzs).symm)
    · have hzq : IsConj z (q * w) := hzzs.trans (hcy hy).symm
      rcases hq with h1 | h1 | h1 | h1
      · rw [h1, one_mul] at hzq; exact absurd hzq d.hzw
      · rw [h1] at hzq; exact absurd hzq d.hzzw
      · exact ⟨q, u, Or.inl h1, huR, hqu, hzq⟩
      · exact ⟨q, u, Or.inr h1, huR, hqu, hzq⟩
  have hztw : IsConj z (t * w) := by
    rcases hq with h1 | h1 <;> rw [h1] at hzq
    · exact hzq
    · exact hzq.trans htwtzw.symm
  have hztzw : IsConj z (t * z * w) := hztw.trans htwtzw
  have hqQ' := hqQ hq
  have hq2 : q * q = 1 := by
    rcases hq with h1 | h1 <;> rw [h1]
    · exact htt
    · rw [show t * z * (t * z) = (t * t) * (z * z) by
        rw [mul_assoc t z, ← mul_assoc z t z, hzt]; group, htt, hzz, one_mul]
  have htws2 : (ts * ws) * (ts * ws) = 1 := by
    rw [show ts * ws * (ts * ws) = ts * (ws * ts) * ws by group, ← htwc,
      show ts * (ts * ws) * ws = (ts * ts) * (ws * ws) by group, hts2, hws2, one_mul]
  have htws1 : ts * ws ≠ 1 := fun h1 => hwsts (by
    have h2 : ws = ts⁻¹ * (ts * ws) := by group
    rw [h2, h1, mul_one, inv_eq_of_mul_eq_one_right hts2])
  have hQR : ∀ {q' v : G}, (q' = t ∨ q' = t * z) → v ∈ P ⊓ footeF L t →
      (q * u) * (q' * v) = (q * q') * (u * v) := by
    intro q' v hq' hv
    rw [show q * u * (q' * v) = q * (u * q') * v by group, ← d.comm_QR (hqQ hq') huR]
    group
  have hzuv : ∀ {c v : G}, (c = 1 ∨ c = z) → v ∈ P ⊓ footeF L t →
      (c * v) * (c * v) = 1 → IsConj z (c * v) → c * v = z := by
    intro c v hc hv hcv2 hzcv
    have hcQ : c ∈ T ⊓ centralizer ({t} : Set G) := by
      rcases hc with h1 | h1 <;> rw [h1]
      · exact one_mem _
      · exact hzQ
    have hcc2 : c * c = 1 := by
      rcases hc with h1 | h1 <;> rw [h1]
      · group
      · exact hzz
    have hv2 : v * v = 1 := by
      have h2 : (c * v) * (c * v) = (c * c) * (v * v) := by
        rw [show c * v * (c * v) = c * (v * c) * v by group, ← d.comm_QR hcQ hv]; group
      rw [h2, hcc2, one_mul] at hcv2
      exact hcv2
    by_cases hv1 : v = 1
    · rw [hv1, mul_one] at hzcv ⊢
      rcases hc with h1 | h1
      · rw [h1] at hzcv
        exact absurd (isConj_one_right.mp hzcv.symm) hz1
      · exact h1
    · exfalso
      obtain ⟨y, -, hyC, hy⟩ := d.exists_conj_w h hv (hord hv2 hv1)
      have hcw : IsConj (c * w) (c * v) := by
        refine isConj_iff.mpr ⟨y, ?_⟩
        have hyc : y * c = c * y := (mem_centralizer_iff.mp hyC c hcQ).symm
        rw [hy]
        calc y * (c * w) * y⁻¹ = (y * c) * w * y⁻¹ := by group
          _ = (c * y) * w * y⁻¹ := by rw [hyc]
          _ = c * (y * w * y⁻¹) := by group
      rcases hc with h1 | h1 <;> rw [h1] at hcw hzcv
      · simp only [one_mul] at hcw hzcv
        exact d.hzw (hzcv.trans hcw.symm)
      · exact d.hzzw (hzcv.trans hcw.symm)
  rcases hfour hts2 hws2 hts1 hws1 hwsts htwc htsP hwsP htsI with hwsI | htwsI
  ·
    obtain ⟨v, hvR, hwsv⟩ : ∃ v ∈ P ⊓ footeF L t, ws = v := by
      rcases d.inv_cases h hwsP hwsI (hord hws2 hws1) with h1 |
        ⟨q', v, hq', hvR, -, hqv, y, -, -, hy⟩
      · exfalso
        rcases h1 with h1 | h1 | h1
        · exact d.hzw (h1 ▸ hwws).symm
        · exact htw' (h1 ▸ hwws).symm
        · exact htw' (htz.trans (h1 ▸ hwws).symm)
      · have hwq : IsConj w (q' * w) := hwws.trans (hcy hy).symm
        rcases hq' with h1 | h1 | h1 | h1
        · rw [h1, one_mul] at hqv; exact ⟨v, hvR, hqv⟩
        · rw [h1] at hwq; exact absurd hwq d.hwzw
        · rw [h1] at hwq; exact absurd (hztw.trans hwq.symm) d.hzw
        · rw [h1] at hwq; exact absurd (hztzw.trans hwq.symm) d.hzw
    have hzws : zs * ws = q * (u * v) := by rw [hqu, hwsv, mul_assoc]
    have huvR : u * v ∈ P ⊓ footeF L t := mul_mem huR hvR
    have hzws2 : (zs * ws) * (zs * ws) = 1 := by
      rw [show zs * ws * (zs * ws) = zs * (ws * zs) * ws by group, ← hzwc,
        show zs * (zs * ws) * ws = (zs * zs) * (ws * ws) by group, hzs2, hws2, one_mul]
    have huv2 : (u * v) * (u * v) = 1 := by
      have h2 : (zs * ws) * (zs * ws) = (q * q) * ((u * v) * (u * v)) := by
        rw [hzws, show q * (u * v) * (q * (u * v)) = q * ((u * v) * q) * (u * v) by group,
          ← d.comm_QR hqQ' huvR]
        group
      rw [h2, hq2, one_mul] at hzws2
      exact hzws2
    by_cases huv1 : u * v = 1
    · rw [huv1, mul_one] at hzws
      have h2 : IsConj t (z * w) := by
        rcases hq with h1 | h1 <;> rw [h1] at hzws
        · exact (hzws ▸ hzwzws).symm
        · exact htz.trans (hzws ▸ hzwzws).symm
      exact htzw' h2
    · obtain ⟨y, -, hyC, hy⟩ := d.exists_conj_w h huvR (hord huv2 huv1)
      have hqw : IsConj (q * w) (zs * ws) := by
        refine isConj_iff.mpr ⟨y, ?_⟩
        have hyq : y * q = q * y := (mem_centralizer_iff.mp hyC q hqQ').symm
        rw [hzws, hy]
        calc y * (q * w) * y⁻¹ = (y * q) * w * y⁻¹ := by group
          _ = (q * y) * w * y⁻¹ := by rw [hyq]
          _ = q * (y * w * y⁻¹) := by group
      exact d.hzzw ((hzq.trans hqw).trans hzwzws.symm)
  ·
    have hzc : g⁻¹ * z * g = t * w ∨ g⁻¹ * z * g = t * z * w := by
      have hztws : IsConj z (ts * ws) := hztw.trans htwtws
      rcases d.inv_cases h (mul_mem htsP hwsP) htwsI (hord htws2 htws1) with h1 |
        ⟨q', v, hq', hvR, -, hqv, y, -, -, hy⟩
      · rcases h1 with h1 | h1 | h1
        · left
          have h2 : g * (t * w) * g⁻¹ = z := by rw [← hcm, ← hts, ← hws, h1]
          rw [← h2]
          group
        · exact absurd (h1 ▸ hztws).symm htz'
        · exact absurd (htz.trans (h1 ▸ hztws).symm) htz'
      · have hzq' : IsConj z (q' * w) := hztws.trans (hcy hy).symm
        have hq'' : q' = t ∨ q' = t * z := by
          rcases hq' with h1 | h1 | h1 | h1
          · rw [h1, one_mul] at hzq'; exact absurd hzq' d.hzw
          · rw [h1] at hzq'; exact absurd hzq' d.hzzw
          · exact Or.inl h1
          · exact Or.inr h1
        have h4 : zs * (ts * ws) = (q * q') * (u * v) := by
          rw [hqu, hqv]
          exact hQR hq'' hvR
        have hqq' : q * q' = 1 ∨ q * q' = z := by
          rcases hq with h1 | h1 <;> rcases hq'' with h2 | h2 <;> rw [h1, h2]
          · exact Or.inl htt
          · right; rw [← mul_assoc, htt, one_mul]
          · right; rw [mul_assoc, hzt, ← mul_assoc, htt, one_mul]
          · left
            rw [show t * z * (t * z) = (t * t) * (z * z) by
              rw [mul_assoc t z, ← mul_assoc z t z, hzt]; group, htt, hzz, one_mul]
        have hzc' : zs * (ts * ws) = (ts * ws) * zs := by
          rw [← mul_assoc, ← htzc, mul_assoc, hzwc, ← mul_assoc]
        have htzws2 : (zs * (ts * ws)) * (zs * (ts * ws)) = 1 := by
          rw [show zs * (ts * ws) * (zs * (ts * ws)) = zs * ((ts * ws) * zs) * (ts * ws) by group,
            ← hzc', show zs * (zs * (ts * ws)) * (ts * ws) = (zs * zs) * ((ts * ws) * (ts * ws))
              by group, hzs2, htws2, one_mul]
        have h5 := hzuv hqq' (mul_mem huR hvR) (h4 ▸ htzws2) (h4 ▸ hztzw.trans htzwtzws)
        right
        have h6 : g * (t * z * w) * g⁻¹ = z := by
          rw [show t * z * w = z * (t * w) by rw [← mul_assoc, hzt], ← hcm, ← hcm, ← hzs, ← hts,
            ← hws, h4, h5]
        calc g⁻¹ * z * g = g⁻¹ * (g * (t * z * w) * g⁻¹) * g := by rw [h6]
          _ = t * z * w := by group
    have hPz : ∀ p ∈ P, g * p * g⁻¹ ∈ centralizer ({z} : Set G) := by
      intro p hp
      have hpS := d.P_le_S hp
      have hpz' : p * (g⁻¹ * z * g) = (g⁻¹ * z * g) * p := by
        rcases hzc with h2 | h2 <;> rw [h2]
        · rw [← mul_assoc, d.t_comm hp, mul_assoc, d.hwc p hpS, mul_assoc]
        · rw [show p * (t * z * w) = (p * t) * z * w by group, d.t_comm hp,
            show t * p * z * w = t * (p * z) * w by group, d.z_comm hpS,
            show t * (z * p) * w = t * z * (p * w) by group, d.hwc p hpS]
          group
      rw [mem_centralizer_singleton_iff]
      calc g * p * g⁻¹ * z = g * (p * (g⁻¹ * z * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * z * g) * p) * g⁻¹ := by rw [hpz']
        _ = z * (g * p * g⁻¹) := by group
    have hwP' := d.w_mem_commutator h hCI htsP hts2 htsI
    have hwsC : ws ∈ ⁅centralizer ({z} : Set G), centralizer ({z} : Set G)⁆ := by
      have h2 : (⁅P, P⁆).map (MulAut.conj g).toMonoidHom ≤
          ⁅centralizer ({z} : Set G), centralizer ({z} : Set G)⁆ := by
        rw [Subgroup.map_commutator]
        have h3 : P.map (MulAut.conj g).toMonoidHom ≤ centralizer ({z} : Set G) := by
          rintro _ ⟨p, hp, rfl⟩
          exact hPz p hp
        exact commutator_mono h3 h3
      rw [hws]
      exact h2 ⟨w, hwP', rfl⟩
    have hwsK := d.commutator_centralizer_le_innerAct h hOut hwsC
    have hwsF : ws ∈ innerAct (footeF L t) :=
      d.mem_innerAct_t_of_mem_innerAct_z h (d.c.hPsyl.le hwsP) hwsK
    apply htsI
    have h2 : ts = (ts * ws) * ws⁻¹ := by group
    rw [h2]
    exact mul_mem htwsI (inv_mem hwsF)

end P4Data

end CFSG.ComponentClassification.Foote47
