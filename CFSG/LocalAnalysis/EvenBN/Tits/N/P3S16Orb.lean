module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3S16Set

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open Subgroup CFSG.Open CFSG.Sporadic.Schreier.Tits
open scoped Pointwise

section S16Orb

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


theorem conj_mem_Cv {g k : G} (hg : g ∈ Hg d) (hk : k ∈ Cv d) : g * k * g⁻¹ ∈ Cv d := by
  have hgN : g ∈ normalizer (d.s56V : Set G) := hg
  have hkN : k ∈ normalizer (d.s56V : Set G) := Cv_le_Hg hk
  have hN : g * k * g⁻¹ ∈ normalizer (d.s56V : Set G) := mul_mem (mul_mem hgN hkN) (inv_mem hgN)
  refine (actFun_eq_one_iff d.s56V hN).1 ?_
  rw [actFun_conj d.s56V hgN hkN, (actFun_eq_one_iff d.s56V hkN).2 hk, mul_one, mul_inv_cancel]

theorem mem_Hs_iff {θ : MulAut ↥d.s56V} : θ ∈ Hs d ↔ ∃ h ∈ Hg d, star d h = θ := by
  unfold Hs img
  rw [mem_imgIn_iff]
  exact ⟨fun ⟨g, hg, _, e⟩ => ⟨g, hg, e⟩, fun ⟨g, hg, e⟩ => ⟨g, hg, hg, e⟩⟩

theorem star_inv_mul_mem (h49 : d.Thm49Statement) (hd : d.Hyp) {h₁ h₂ κ : G} (hh₁ : h₁ ∈ Hg d)
    (hh₂ : h₂ ∈ Hg d) (hκ : κ ∈ Cv d)
    (e : h₂ * d.t * h₂⁻¹ = κ * (h₁ * d.t * h₁⁻¹) * κ⁻¹) :
    (star d h₂)⁻¹ * star d h₁ ∈ img d (CMt d) := by
  have hh₁N : h₁ ∈ normalizer (d.s56V : Set G) := hh₁
  have hh₂N : h₂ ∈ normalizer (d.s56V : Set G) := hh₂
  have hκN : κ ∈ normalizer (d.s56V : Set G) := Cv_le_Hg hκ
  have hc : h₂⁻¹ * κ * h₁ ∈ Hg d :=
    mul_mem (mul_mem (inv_mem hh₂) (Cv_le_Hg hκ)) hh₁
  have hcN : h₂⁻¹ * κ * h₁ ∈ normalizer (d.s56V : Set G) := hc
  have hct : (h₂⁻¹ * κ * h₁) * d.t = d.t * (h₂⁻¹ * κ * h₁) := by
    have h1 : (h₂⁻¹ * κ * h₁) * d.t * (h₂⁻¹ * κ * h₁)⁻¹ = d.t := by
      calc (h₂⁻¹ * κ * h₁) * d.t * (h₂⁻¹ * κ * h₁)⁻¹
          = h₂⁻¹ * (κ * (h₁ * d.t * h₁⁻¹) * κ⁻¹) * h₂ := by group
        _ = h₂⁻¹ * (h₂ * d.t * h₂⁻¹) * h₂ := by rw [e]
        _ = d.t := by group
    calc (h₂⁻¹ * κ * h₁) * d.t = ((h₂⁻¹ * κ * h₁) * d.t * (h₂⁻¹ * κ * h₁)⁻¹) * (h₂⁻¹ * κ * h₁) := by
          group
      _ = d.t * (h₂⁻¹ * κ * h₁) := by rw [h1]
  have hcM : h₂⁻¹ * κ * h₁ ∈ CMt d :=
    Hg_inf_centralizer_le_CMt h49 hd ⟨hc, mem_centralizer_singleton_iff.2 hct⟩
  have hstar : actFun d.s56V (h₂⁻¹ * κ * h₁) = (star d h₂)⁻¹ * star d h₁ := by
    rw [actFun_mul d.s56V (mul_mem (inv_mem hh₂N) hκN) hh₁N, actFun_mul d.s56V (inv_mem hh₂N) hκN,
      actFun_inv d.s56V hh₂N, (actFun_eq_one_iff d.s56V hκN).2 hκ, mul_one]
    rfl
  rw [← hstar]
  exact actFun_mem_imgIn hcM hcN

theorem star_mem_img_CMt_iff (h49 : d.Thm49Statement) (hd : d.Hyp) {h : G} (hh : h ∈ Hg d) :
    star d h ∈ img d (CMt d) ↔ ∃ k ∈ Cv d, h * d.t * h⁻¹ = k * d.t * k⁻¹ := by
  constructor
  · intro hmem
    obtain ⟨m, hm, hmN, hmh⟩ := (mem_imgIn_iff d.s56V (CMt d)).1 hmem
    have hhN : h ∈ normalizer (d.s56V : Set G) := hh
    have hmM : m ∈ d.M := hm.1
    have hmt : m * d.t = d.t * m := mem_centralizer_singleton_iff.1 hm.2
    have hmH : m ∈ Hg d := M_le_Hg h49 hd hmM
    have hκ : m⁻¹ * h ∈ Cv d := (actFun_eq_iff d.s56V hmN hhN).1 hmh
    refine ⟨h * m⁻¹, ?_, ?_⟩
    · have : h * m⁻¹ = m * (m⁻¹ * h) * m⁻¹ := by group
      rw [this]
      exact conj_mem_Cv hmH hκ
    · have hmt' : m⁻¹ * d.t * m = d.t := by
        calc m⁻¹ * d.t * m = m⁻¹ * (d.t * m) := by group
          _ = m⁻¹ * (m * d.t) := by rw [hmt]
          _ = d.t := by group
      calc h * d.t * h⁻¹ = h * (m⁻¹ * d.t * m) * h⁻¹ := by rw [hmt']
        _ = h * m⁻¹ * d.t * (h * m⁻¹)⁻¹ := by group
  · rintro ⟨k, hk, e⟩
    have h1 := star_inv_mul_mem h49 hd (h₁ := 1) (h₂ := h) (κ := k) (one_mem _) hh hk
      (by rw [e]; group)
    have h2 : star d 1 = 1 := actFun_one d.s56V
    rw [h2, mul_one] at h1
    exact (inv_mem_iff).1 h1

theorem exists_conj_of_mem_Th (h49 : d.Thm49Statement) (hd : d.Hyp) {θ : MulAut ↥d.s56V}
    (hθ : θ ∈ centralizer ({star d d.t} : Set (MulAut ↥d.s56V)) ⊓ Hs d) :
    ∃ h ∈ Hg d, star d h = θ ∧ ∃ k ∈ Cv d, h * d.t * h⁻¹ = k * d.t := by
  obtain ⟨hθC, hθH⟩ := hθ
  obtain ⟨h, hh, rfl⟩ := mem_Hs_iff.1 hθH
  have hhN : h ∈ normalizer (d.s56V : Set G) := hh
  have htH : d.t ∈ normalizer (d.s56V : Set G) := t_mem_Hg h49 hd
  have hx : h * d.t * h⁻¹ ∈ normalizer (d.s56V : Set G) :=
    mul_mem (mul_mem hhN htH) (inv_mem hhN)
  have hcomm : star d h * star d d.t = star d d.t * star d h := mem_centralizer_singleton_iff.1 hθC
  have h1 : actFun d.s56V (h * d.t * h⁻¹) = actFun d.s56V d.t := by
    rw [actFun_conj d.s56V hhN htH]
    show star d h * star d d.t * (star d h)⁻¹ = star d d.t
    rw [hcomm]
    group
  have h2 : (h * d.t * h⁻¹)⁻¹ * d.t ∈ Cv d := (actFun_eq_iff d.s56V hx htH).1 h1
  refine ⟨h, hh, rfl, d.t * ((h * d.t * h⁻¹)⁻¹ * d.t)⁻¹ * d.t⁻¹,
    t_mul_Cv_mul_inv h49 hd (inv_mem h2), ?_⟩
  group

theorem OrbSet_conj_mem {S : Subgroup G} (hSK : S ≤ Cv d) (hSt : ∀ s ∈ S, d.t * s * d.t⁻¹ ∈ S)
    {x s : G} (hx : x ∈ OrbSet d S) (hs : s ∈ S) : s * x * s⁻¹ ∈ OrbSet d S := by
  obtain ⟨⟨h, hh, rfl⟩, s₁, hs₁, hxs⟩ := hx
  refine ⟨⟨s * h, mul_mem (Cv_le_Hg (hSK hs)) hh, by group⟩, s * s₁ * (d.t * s⁻¹ * d.t⁻¹),
    mul_mem (mul_mem hs hs₁) (hSt s⁻¹ (inv_mem hs)), ?_⟩
  rw [hxs]
  group

theorem exists_conj_b (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) {S : Subgroup G}
    (hS : fusionIsSylowIn 2 S (Cv d)) (hSt : ∀ s ∈ S, d.t * s * d.t⁻¹ ∈ S) {b : G}
    (hb : ∀ x ∈ OrbSet d S, (∃ s ∈ S, s * d.t * s⁻¹ = x) ∨ ∃ s ∈ S, s * b * s⁻¹ = x) {h : G}
    (hh : h ∈ Hg d) {k₀ : G} (hk₀ : k₀ ∈ Cv d) (hx : h * d.t * h⁻¹ = k₀ * d.t)
    (hnot : star d h ∉ img d (CMt d)) : ∃ κ ∈ Cv d, h * d.t * h⁻¹ = κ * b * κ⁻¹ := by
  have ht2 := hd.t_mul_self
  have hu2 : (h * d.t * h⁻¹) * (h * d.t * h⁻¹) = 1 := by
    calc (h * d.t * h⁻¹) * (h * d.t * h⁻¹) = h * (d.t * d.t) * h⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  obtain ⟨k, hk, s, hs, hks⟩ := exists_conj_mem_St hS hSt ht2 (t_not_mem_Cv h49 hd hz)
    (fun k hk => t_mul_Cv_mul_inv h49 hd hk) hu2 ⟨k₀, hk₀, hx⟩
  have hO : s * d.t ∈ OrbSet d S :=
    ⟨⟨k * h, mul_mem (Cv_le_Hg hk) hh, by rw [← hks]; group⟩, s, hs, rfl⟩
  have hSK : S ≤ Cv d := hS.1
  rcases hb _ hO with ⟨σ, hσ, hσe⟩ | ⟨σ, hσ, hσe⟩
  · exfalso
    refine hnot ((star_mem_img_CMt_iff h49 hd hh).2 ⟨k⁻¹ * σ, mul_mem (inv_mem hk) (hSK hσ), ?_⟩)
    calc h * d.t * h⁻¹ = k⁻¹ * (k * (h * d.t * h⁻¹) * k⁻¹) * k := by group
      _ = k⁻¹ * (σ * d.t * σ⁻¹) * k := by rw [hks, hσe]
      _ = k⁻¹ * σ * d.t * (k⁻¹ * σ)⁻¹ := by group
  · refine ⟨k⁻¹ * σ, mul_mem (inv_mem hk) (hSK hσ), ?_⟩
    calc h * d.t * h⁻¹ = k⁻¹ * (k * (h * d.t * h⁻¹) * k⁻¹) * k := by group
      _ = k⁻¹ * (σ * b * σ⁻¹) * k := by rw [hks, hσe]
      _ = k⁻¹ * σ * b * (k⁻¹ * σ)⁻¹ := by group

theorem coset_lemma (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) {S : Subgroup G}
    (hS : fusionIsSylowIn 2 S (Cv d)) (hSt : ∀ s ∈ S, d.t * s * d.t⁻¹ ∈ S) {b : G}
    (hb : ∀ x ∈ OrbSet d S, (∃ s ∈ S, s * d.t * s⁻¹ = x) ∨ ∃ s ∈ S, s * b * s⁻¹ = x)
    {θ θ' : MulAut ↥d.s56V}
    (hθ : θ ∈ centralizer ({star d d.t} : Set (MulAut ↥d.s56V)) ⊓ Hs d)
    (hθ' : θ' ∈ centralizer ({star d d.t} : Set (MulAut ↥d.s56V)) ⊓ Hs d)
    (hθΞ : θ ∉ img d (CMt d)) (hθ'Ξ : θ' ∉ img d (CMt d)) : θ⁻¹ * θ' ∈ img d (CMt d) := by
  obtain ⟨h, hh, rfl, k₀, hk₀, hx⟩ := exists_conj_of_mem_Th h49 hd hθ
  obtain ⟨h', hh', rfl, k₀', hk₀', hx'⟩ := exists_conj_of_mem_Th h49 hd hθ'
  obtain ⟨κ, hκ, hκe⟩ := exists_conj_b h49 hd hz hS hSt hb hh hk₀ hx hθΞ
  obtain ⟨κ', hκ', hκe'⟩ := exists_conj_b h49 hd hz hS hSt hb hh' hk₀' hx' hθ'Ξ
  have hmem := star_inv_mul_mem h49 hd (h₁ := h) (h₂ := h') (κ := κ' * κ⁻¹) hh hh'
    (mul_mem hκ' (inv_mem hκ)) (by
      rw [hκe, hκe']
      group)
  have := inv_mem hmem
  rwa [mul_inv_rev, inv_inv] at this

theorem img_CMt_le_Th (h49 : d.Thm49Statement) (hd : d.Hyp) :
    img d (CMt d) ≤ centralizer ({star d d.t} : Set (MulAut ↥d.s56V)) ⊓ Hs d := by
  refine (imgIn_mono d.s56V (show CMt d ≤ Hg d ⊓ centralizer ({d.t} : Set G) from
    le_inf (CMt_le_Hg h49 hd) inf_le_right)).trans ?_
  exact imgIn_inf_centralizer_le d.s56V (Hg d) d.t

theorem exists_mem_Th_not_Xi (h49 : d.Thm49Statement) (hd : d.Hyp) {S : Subgroup G} {b : G}
    (hSK : S ≤ Cv d) (hbO : b ∈ OrbSet d S) (hbt : ¬ ∃ s ∈ S, s * d.t * s⁻¹ = b)
    (hK : (∃ k ∈ Cv d, k * d.t * k⁻¹ = b) → ∃ s ∈ S, s * d.t * s⁻¹ = b) :
    ∃ θ ∈ centralizer ({star d d.t} : Set (MulAut ↥d.s56V)) ⊓ Hs d, θ ∉ img d (CMt d) := by
  obtain ⟨⟨h, hh, hhb⟩, s₀, hs₀, hbs⟩ := hbO
  have hhN : h ∈ normalizer (d.s56V : Set G) := hh
  have htH : d.t ∈ normalizer (d.s56V : Set G) := t_mem_Hg h49 hd
  have hs₀N : s₀ ∈ normalizer (d.s56V : Set G) := Cv_le_Hg (hSK hs₀)
  refine ⟨star d h, Subgroup.mem_inf.2 ⟨?_, actFun_mem_imgIn hh hhN⟩, fun hmem => hbt (hK ?_)⟩
  · rw [mem_centralizer_singleton_iff]
    have h1 : actFun d.s56V (h * d.t * h⁻¹) = actFun d.s56V (s₀ * d.t) := by rw [hhb, hbs]
    rw [actFun_conj d.s56V hhN htH, actFun_mul d.s56V hs₀N htH,
      (actFun_eq_one_iff d.s56V hs₀N).2 (hSK hs₀), one_mul] at h1
    show star d h * star d d.t = star d d.t * star d h
    have h1' : star d h * star d d.t * (star d h)⁻¹ = star d d.t := h1
    calc star d h * star d d.t = (star d h * star d d.t * (star d h)⁻¹) * star d h := by group
      _ = star d d.t * star d h := by rw [h1']
  · obtain ⟨k, hk, hke⟩ := (star_mem_img_CMt_iff h49 hd hh).1 hmem
    exact ⟨k, hk, by rw [← hke, hhb]⟩

theorem odd_orderOf_of_mem_oddCoreSub {Γ : Type*} [Group Γ] [Finite Γ] {K : Subgroup Γ} {o : Γ}
    (ho : o ∈ oddCoreSub K) : Odd (orderOf o) := by
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 ho
  have hodd : Odd (Nat.card (standardComponentOddCore ↥K)) :=
    CFSG.ComponentClassification.OddCore.odd_card_sSup _ (Set.toFinite _) (fun _ h => h.1)
      (fun _ h => h.2)
  have h1 : orderOf k ∣ Nat.card (standardComponentOddCore ↥K) := by
    have := orderOf_dvd_natCard (⟨k, hk⟩ : ↥(standardComponentOddCore ↥K))
    rwa [Subgroup.orderOf_mk] at this
  have h2 : orderOf (K.subtype k) = orderOf k := orderOf_injective K.subtype K.subtype_injective k
  rw [h2]
  exact hodd.of_dvd_nat h1

theorem trans_of_oddCore (h49 : d.Thm49Statement) (hd : d.Hyp) (h10 : Node10 d z₀) (h12 : Node12 d z₀)
    {S : Subgroup G} (hS : fusionIsSylowIn 2 S (Cv d))
    (hK : Cv d = oddCoreSub (Cv d) ⊔ d.s56V) : Trans S (OrbSet d S) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVK : d.s56V ≤ Cv d := V_le_Cv h10
  have hVc : ∀ v ∈ d.s56V, ∀ k ∈ Cv d, v * k = k * v := fun v hv k hk =>
    (Subgroup.mem_centralizer_iff.1 hk) v hv
  have hSV : S ≤ d.s56V := by
    intro s hs
    have hsK : s ∈ Cv d := hS.1 hs
    have hOle : oddCoreSub (Cv d) ≤ Cv d := Subgroup.map_subtype_le _
    have hON : oddCoreSub (Cv d) ≤ normalizer (d.s56V : Set G) := fun o ho =>
      Subgroup.centralizer_le_normalizer _ (hOle ho)
    have hset := Subgroup.coe_mul_of_left_le_normalizer_right (oddCoreSub (Cv d)) d.s56V hON
    have hs' : s ∈ ((oddCoreSub (Cv d) : Set G) * (d.s56V : Set G)) := by
      rw [← hset, ← hK]
      exact hsK
    obtain ⟨o, ho, v, hv, hov⟩ := hs'
    have hov : o * v = s := hov
    obtain ⟨n, hn⟩ := hS.2.1 ⟨s, hs⟩
    have hsn : s ^ (2 ^ n) = 1 := congrArg Subtype.val hn
    have hvsq : v * v = 1 := h10.sq_V hv
    have hov' : o = s * v⁻¹ := by rw [← hov]; group
    have hcomm : Commute s v⁻¹ := by
      have := hVc v⁻¹ (inv_mem hv) s hsK
      exact this.symm
    have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvsq
    have hvpow : v ^ (2 ^ (n + 1)) = 1 := by
      rw [pow_succ', pow_mul, pow_two, hvsq, one_pow]
    have ho1 : o ^ (2 ^ (n + 1)) = 1 := by
      rw [hov', hcomm.mul_pow, hvinv, hvpow, mul_one, pow_succ, pow_mul, hsn, one_pow]
    have hord : orderOf o ∣ 2 ^ (n + 1) := orderOf_dvd_of_pow_eq_one ho1
    have hodd := odd_orderOf_of_mem_oddCoreSub ho
    have hcop : Nat.Coprime (orderOf o) (2 ^ (n + 1)) :=
      Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hodd)
    have h1 : orderOf o = 1 := Nat.Coprime.eq_one_of_dvd hcop hord
    have : o = 1 := orderOf_eq_one_iff.1 h1
    rw [← hov, this, one_mul]
    exact hv
  have hV2 : IsPGroup 2 d.s56V := IsPGroup.of_card (n := 10) h10.card_V
  have hVS : d.s56V ≤ S := by
    have := hS.2.2 d.s56V hVK hV2 hSV
    exact this.le
  have hconj : ∀ x ∈ OrbSet d S, ∃ v ∈ d.s56V, v * d.t * v⁻¹ = x := by
    intro x hx
    obtain ⟨hxsq, s, hs, hxs⟩ := OrbSet_facts hd hx
    have hsV : s ∈ d.s56V := hSV hs
    have ht2 := hd.t_mul_self
    have hss : s * s = 1 := h10.sq_V hsV
    have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
    have hts : s * d.t = d.t * s := by
      have h1 : s * d.t * (s * d.t) = 1 := by rw [← hxs]; exact hxsq
      have h2 : d.t * s * d.t⁻¹ = s⁻¹ := by
        have hti : d.t⁻¹ = d.t := inv_eq_of_mul_eq_one_right ht2
        rw [hti]
        have h3 : s * (d.t * s * d.t) = 1 := by
          calc s * (d.t * s * d.t) = s * d.t * (s * d.t) := by group
            _ = 1 := h1
        exact eq_inv_of_mul_eq_one_right h3
      rw [hsinv] at h2
      calc s * d.t = (d.t * s * d.t⁻¹) * d.t := by rw [h2]
        _ = d.t * s := by group
    have hsE : s ∈ d.E := by
      rw [E_eq_V_inf_Ct h49 hd]
      exact ⟨hsV, mem_centralizer_singleton_iff.2 hts⟩
    have hmem : x ∈ {x | ∃ v ∈ d.s56V, v * d.t * v⁻¹ = x} := by
      rw [h12.1.2]
      exact ⟨s, hsE, by rw [hxs, hts]⟩
    exact hmem
  intro a ha b hb
  obtain ⟨v, hv, rfl⟩ := hconj a ha
  obtain ⟨v', hv', rfl⟩ := hconj b hb
  exact ⟨v' * v⁻¹, mul_mem (hVS hv') (inv_mem (hVS hv)), by group⟩

end S16Orb

end CFSG.LocalAnalysis.EvenBN.Tits.N
