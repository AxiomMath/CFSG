module

public import CFSG.GH74.GLS.C3.Layer1.BkP46W

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.C3.Layer1.Back
open scoped commutatorElement

variable {G : Type} [Group G]

theorem isSylowOf_of_maximal [Finite G] {P H : Subgroup G} (hP : IsPGroup 2 ↥P) (hPH : P ≤ H)
    (hmax : ∀ B : Subgroup G, P ≤ B → B ≤ H → IsPGroup 2 ↥B → B = P) : IsSylowOf 2 P H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPsub : IsPGroup 2 ↥(P.subgroupOf H) := hP.comap_subtype
  obtain ⟨S₁, hS₁⟩ := hPsub.exists_le_sylow
  have hT₁ : IsSylowOf 2 ((S₁ : Subgroup ↥H).map H.subtype) H := ⟨S₁, rfl⟩
  have hPT₁ : P ≤ (S₁ : Subgroup ↥H).map H.subtype := by
    intro t ht
    exact ⟨⟨t, hPH ht⟩, hS₁ (Subgroup.mem_subgroupOf.2 ht), rfl⟩
  have heq := hmax _ hPT₁ hT₁.le hT₁.isPGroup
  rw [heq] at hT₁
  exact hT₁

theorem exists_conj_of_coset [Finite G] {C W B₁ B₂ : Subgroup G}
    (hn : ∀ c ∈ C, ∀ w ∈ W, c * w * c⁻¹ ∈ W) (hodd : Odd (Nat.card ↥W)) {s u : G}
    (hsC : s ∈ C) (hs : s ∈ B₁) (hB₁ : IsPGroup 2 ↥B₁) (huB : u ∈ B₂) (hB₂ : IsPGroup 2 ↥B₂)
    (hsu : s⁻¹ * u ∈ W) : ∃ g : G, g * u * g⁻¹ = s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs2 : IsPGroup 2 ↥(zpowers s) := hB₁.to_le (zpowers_le.2 hs)
  have hu2 : IsPGroup 2 ↥(zpowers u) := hB₂.to_le (zpowers_le.2 huB)
  have hzN : zpowers s ≤ normalizer (W : Set G) := by
    rw [zpowers_le]
    exact mem_normalizer_of_two_sided (fun w hw => hn s hsC w hw) (fun w hw => by
      simpa using hn s⁻¹ (C.inv_mem hsC) w hw)
  have hS : IsSylowOf 2 (zpowers s) (zpowers s ⊔ W) := isSylowOf_two_sup_of_odd hs2 hzN hodd
  have huH : u ∈ zpowers s ⊔ W := by
    have e : u = s * (s⁻¹ * u) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (mem_zpowers s)) (Subgroup.mem_sup_right hsu)
  obtain ⟨g, hgH, hgu⟩ := Th2.exists_cj_le_of_isSylowOf hS (zpowers_le.2 huH) hu2
  have hgu' : g * u * g⁻¹ ∈ zpowers s := hgu ⟨u, mem_zpowers u, rfl⟩
  refine ⟨g, ?_⟩
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right (zpowers s) W hzN] at hgH
  obtain ⟨sj, hsj, w₁, hw₁, rfl⟩ := hgH
  have hsjC : sj ∈ C := (zpowers_le.2 hsC) hsj
  have hw₀ := hsu
  set w₀ : G := s⁻¹ * u with hw₀def
  have hw₁' : s⁻¹ * w₁ * s ∈ W := by
    have := hn s⁻¹ (C.inv_mem hsC) w₁ hw₁
    simpa using this
  have hcomm : sj * s = s * sj := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hsj
    exact (Commute.self_zpow s k).eq.symm
  have hmem : sj * w₁ * u * (sj * w₁)⁻¹ = s * (sj * ((s⁻¹ * w₁ * s) * w₀ * w₁⁻¹) * sj⁻¹) := by
    have hu' : u = s * w₀ := by rw [hw₀def]; group
    calc sj * w₁ * u * (sj * w₁)⁻¹ = sj * w₁ * (s * w₀) * w₁⁻¹ * sj⁻¹ := by rw [hu']; group
      _ = sj * (s * (s⁻¹ * w₁ * s)) * w₀ * w₁⁻¹ * sj⁻¹ := by group
      _ = (sj * s) * ((s⁻¹ * w₁ * s) * w₀ * w₁⁻¹) * sj⁻¹ := by group
      _ = (s * sj) * ((s⁻¹ * w₁ * s) * w₀ * w₁⁻¹) * sj⁻¹ := by rw [hcomm]
      _ = s * (sj * ((s⁻¹ * w₁ * s) * w₀ * w₁⁻¹) * sj⁻¹) := by group
  have hw₂ : sj * ((s⁻¹ * w₁ * s) * w₀ * w₁⁻¹) * sj⁻¹ ∈ W :=
    hn sj hsjC _ (W.mul_mem (W.mul_mem hw₁' hw₀) (W.inv_mem hw₁))
  rw [hmem] at hgu'
  have hbot : W ⊓ zpowers s = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have h1 : orderOf z ∣ Nat.card ↥W := Subgroup.orderOf_dvd_natCard _ hz.1
    have h2 : orderOf z ∣ Nat.card ↥(zpowers s) := Subgroup.orderOf_dvd_natCard _ hz.2
    obtain ⟨k, hk⟩ := hs2.exists_card_eq
    rw [hk] at h2
    have hcop : Nat.Coprime (orderOf z) 2 := Nat.coprime_two_right.2 (Odd.of_dvd_nat hodd h1)
    have h3 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k hcop) h2
    exact Subgroup.mem_bot.2 (orderOf_eq_one_iff.1 h3)
  have hz : s⁻¹ * (s * (sj * ((s⁻¹ * w₁ * s) * w₀ * w₁⁻¹) * sj⁻¹)) ∈ W ⊓ zpowers s := by
    refine ⟨by simpa using hw₂, ?_⟩
    exact Subgroup.mul_mem _ ((zpowers s).inv_mem (mem_zpowers s)) hgu'
  rw [hbot, Subgroup.mem_bot] at hz
  have : sj * ((s⁻¹ * w₁ * s) * w₀ * w₁⁻¹) * sj⁻¹ = 1 := by simpa using hz
  rw [hmem, this]
  group


theorem aconfigW_five_E_le_R' [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}
    (h : IsAConfigW 5 x K T Q S a) {E : Subgroup G} (hET : E ≤ T)
    (hEel : CFSG.IsElementaryAbelian 2 ↥E) (hE : 9 ≤ Nat.card ↥E) : E ≤ (T ⊓ K) ⊔ Q := by
  obtain ⟨y, hyT, hyy, hyR, hTcases, q₀, hq₀, hyq₀⟩ := aconfigW_five_y h
  obtain ⟨p, hp, hyp⟩ := aconfigW_five_y_nontriv h hyT hyR
  have hCy := aconfigW_five_card_centralizer_R h hyT ⟨p, hp, hyp⟩ ⟨q₀, hq₀, hyq₀⟩
  exact aconfigW_five_E_le_R h hTcases hCy hET hEel hE

theorem aconfigW_five_cent_T_R [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}
    (h : IsAConfigW 5 x K T Q S a) {c : G} (hcT : c ∈ T)
    (hc : ∀ r ∈ (T ⊓ K) ⊔ Q, c * r = r * c) : c ∈ (T ⊓ K) ⊔ Q := by
  obtain ⟨y, hyT, hyy, hyR, hTcases, q₀, hq₀, hyq₀⟩ := aconfigW_five_y h
  obtain ⟨p, hp, hyp⟩ := aconfigW_five_y_nontriv h hyT hyR
  obtain ⟨hRel, hRcard⟩ := aconfigW_five_R h
  obtain ⟨hRc, hRs⟩ := forall_of_isElementaryAbelian hRel
  rcases hTcases c hcT with h1 | ⟨r, hr, rfl⟩
  · exact h1
  · exfalso
    apply hyp
    have hpR : p ∈ (T ⊓ K) ⊔ Q := Subgroup.mem_sup_left hp
    have h2 := hc p hpR
    have h3 : r * y * p = r * (y * p) := by group
    have h4 : p * (r * y) = r * (p * y) := by
      calc p * (r * y) = (p * r) * y := by group
        _ = (r * p) * y := by rw [hRc p hpR r hr]
        _ = r * (p * y) := by group
    rw [h3, h4] at h2
    exact (mul_left_cancel h2)

theorem aconfigW_five_R_sylow_centralizer [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}
    (h : IsAConfigW 5 x K T Q S a) :
    IsSylowOf 2 ((T ⊓ K) ⊔ Q) (centralizer ((((T ⊓ K) ⊔ Q : Subgroup G)) : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hRel, hRcard⟩ := aconfigW_five_R h
  obtain ⟨hRc, hRs⟩ := forall_of_isElementaryAbelian hRel
  have hR2 : IsPGroup 2 ↥((T ⊓ K) ⊔ Q) := CFSG.IsElementaryAbelian.isPGroup 2 _
  have hRT : (T ⊓ K) ⊔ Q ≤ T := sup_le inf_le_left h.Q_le_T
  have hRC : (T ⊓ K) ⊔ Q ≤ centralizer ((((T ⊓ K) ⊔ Q : Subgroup G)) : Set G) := fun r hr =>
    mem_centralizer_iff.2 fun r' hr' => (hRc r' hr' r hr)
  refine isSylowOf_of_maximal hR2 hRC (fun B hRB hBC hB2 => ?_)
  have hxR : x ∈ (T ⊓ K) ⊔ Q := Subgroup.mem_sup_right h.x_mem_Q
  have hBx : B ≤ centralizer ({x} : Set G) := fun b hb =>
    mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 (hBC hb) x hxR).symm)
  obtain ⟨g, hgC, hgB⟩ := Th2.exists_cj_le_of_isSylowOf h.sylowT hBx hB2
  have hgRT : Th2.cj g ((T ⊓ K) ⊔ Q) ≤ T :=
    (Subgroup.map_mono hRB).trans hgB |>.trans le_rfl
  have hcard16 : Nat.card ↥(Th2.cj g ((T ⊓ K) ⊔ Q)) = 16 := by
    unfold Th2.cj
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hRcard]
  have hgRR : Th2.cj g ((T ⊓ K) ⊔ Q) ≤ (T ⊓ K) ⊔ Q :=
    aconfigW_five_E_le_R' h hgRT (isElementaryAbelian_cj g hRel) (by rw [hcard16]; norm_num)
  have heq : Th2.cj g ((T ⊓ K) ⊔ Q) = (T ⊓ K) ⊔ Q :=
    Subgroup.eq_of_le_of_card_ge hgRR (by rw [hcard16, hRcard])
  have hle : Th2.cj g B ≤ (T ⊓ K) ⊔ Q := by
    intro z hz
    refine aconfigW_five_cent_T_R h (hgB hz) (fun r hr => ?_)
    obtain ⟨b, hb, rfl⟩ := hz
    have hr' : r ∈ Th2.cj g ((T ⊓ K) ⊔ Q) := by rw [heq]; exact hr
    obtain ⟨r₀, hr₀, rfl⟩ := hr'
    have := mem_centralizer_iff.1 (hBC hb) r₀ hr₀
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * b * g⁻¹ * (g * r₀ * g⁻¹) = g * (b * r₀) * g⁻¹ := by group
      _ = g * (r₀ * b) * g⁻¹ := by rw [this]
      _ = g * r₀ * g⁻¹ * (g * b * g⁻¹) := by group
  have hcardB : Nat.card ↥B ≤ Nat.card ↥((T ⊓ K) ⊔ Q) := by
    have h1 : Nat.card ↥(Th2.cj g B) = Nat.card ↥B := by
      unfold Th2.cj
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    rw [← h1]
    exact Subgroup.card_le_of_le hle
  exact (Subgroup.eq_of_le_of_card_ge hRB hcardB).symm

end CFSG.GH74.GLS.C3.Layer1.Bk
