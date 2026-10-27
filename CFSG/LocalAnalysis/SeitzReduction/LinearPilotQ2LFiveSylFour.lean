module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSylData
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSylAct

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial LinearFlag

section TypeFree

variable {G : Type} [Group G]

theorem isPGroup_zpowers_of_pow_two_pow_eq_one {g : G} {n : ℕ} (h : g ^ 2 ^ n = 1) :
    IsPGroup 2 (zpowers g) := by
  rintro ⟨x, hx⟩
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
  refine ⟨n, Subtype.ext ?_⟩
  change (g ^ k) ^ 2 ^ n = 1
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h, one_zpow]

theorem mul_self_notMem_of_notMem {S₀ S₁ : Subgroup G} (hidx : S₀.relIndex S₁ = 2) {d : G} (hdS₀ : d ∈ normalizer (S₀ : Set G))
    (hdS₁ : d ∈ normalizer (S₁ : Set G)) (hdd : d * d ∈ S₁) (hdd₀ : d * d ∉ S₀) {h : G}
    (hh : h ∈ S₁ ⊔ zpowers d) (hhS : h ∉ S₁) : h * h ∉ S₀ := by
  have ha : h * d ∈ S₁ := by
    rcases mem_or_mul_mem_of_mem_sup_zpowers_of_mul_self_mem hdS₁ hdd hh with h1 | h1
    · exact absurd h1 hhS
    · exact h1
  set a := h * d with hadef
  have hb : d⁻¹ * a * d ∈ S₁ := inv_mul_mul_mem_of_mem_normalizer hdS₁ ha
  have hc : (d * d)⁻¹ ∈ S₁ := inv_mem hdd
  have hc₀ : (d * d)⁻¹ ∉ S₀ := fun h' => hdd₀ (by simpa using inv_mem h')
  have hab : a ∈ S₀ ↔ d⁻¹ * a * d ∈ S₀ := by
    constructor
    · exact fun h' => inv_mul_mul_mem_of_mem_normalizer hdS₀ h'
    · intro h'
      have h1 := (mem_normalizer_iff.1 hdS₀ _).1 h'
      have h2 : d * (d⁻¹ * a * d) * d⁻¹ = a := by group
      rwa [h2] at h1
  have hidx' : (S₀.subgroupOf S₁).index = 2 := hidx
  have key : ∀ x y : S₁, ((x * y : S₁) : G) ∈ S₀ ↔ ((x : G) ∈ S₀ ↔ (y : G) ∈ S₀) := by
    intro x y
    have h1 := mul_mem_iff_of_index_two hidx' (a := x) (b := y)
    simpa only [mem_subgroupOf] using h1
  have hhh : h * h = a * (d⁻¹ * a * d) * (d * d)⁻¹ := by rw [hadef]; group
  intro hsq
  rw [hhh] at hsq
  have h1 := (key ⟨a * (d⁻¹ * a * d), mul_mem ha hb⟩ ⟨(d * d)⁻¹, hc⟩).1 hsq
  have h2 := key ⟨a, ha⟩ ⟨d⁻¹ * a * d, hb⟩
  simp only [Subgroup.coe_mul] at h1 h2
  exact hc₀ (h1.1 (h2.2 hab))

end TypeFree

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem false_of_mul_self_mul_mem
    (hset : SeitzSetting G L)
    {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 2) (e : L ≃* projectiveSL 5 K)
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (c : Fin 5) {W₁ : Subgroup G} (hW₁c : Nat.card W₁ = 2 ^ 8) (hW₁2 : ∀ w ∈ W₁, w * w = 1)
    (hW₁t : W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c))
    (htN : t ∈ normalizer (W₁ : Set G))
    (hLN : modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G))
    {Kc : Subgroup (seitzHat W₁)} (hfield : IsFieldTypeComponentAtNOne e t c W₁ htN Kc)
    {S₀ Q₀ : Subgroup G} (hS₀p : IsPGroup 2 S₀) (hS₀N : S₀ ≤ seitzTilde W₁ Kc)
    (htS₀ : t ∈ normalizer (S₀ : Set G)) (hQL : Q₀ ≤ L) (hQc : Nat.card Q₀ = 2 ^ 10)
    (hQS : Q₀ ≤ S₀)
    (hThom : ∀ x ∈ S₀, x * t * (x * t) = 1 → ∃ z ∈ S₀, x * t = z * t * z⁻¹)
    {d : G} (hdC : d ∈ centralizer ({t} : Set G)) (hdS₀ : d ∈ normalizer (S₀ : Set G))
    (hdS : d ∉ S₀ ⊔ zpowers t) (hdd4 : d * d * t ∈ Q₀) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup G := hset.1
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  have hdt : d * t = t * d := mem_centralizer_singleton_iff.1 hdC
  have hconj := not_conj_mem_seitzTilde hset hK e ht hKt c hW₁c hW₁2 hW₁t htN hLN hfield
  have htS₀' : t ∉ S₀ := fun h => hconj 1 (by simpa using hS₀N h)
  set S₁ : Subgroup G := S₀ ⊔ zpowers t with hS₁def
  have hS₁p : IsPGroup 2 S₁ :=
    isPGroup_sup_zpowers_of_mem_normalizer hS₀p htS₀ (isPGroup_zpowers_two_of_mul_self ht2)
  have htS₁ : t ∈ S₁ := mem_sup_right (mem_zpowers t)
  have hdN₁ : d ∈ normalizer (S₁ : Set G) :=
    mem_normalizer_sup_of_mem_of_mem_normalizer hdS₀ (mem_normalizer_zpowers_of_mul_eq_mul hdt.symm)
  have hdd' : d * d = d * d * t * t := by rw [mul_assoc (d * d) t t, ht2, mul_one]
  have hddQt : d * d ∈ Q₀ ⊔ zpowers t := by
    rw [hdd']
    exact mul_mem (mem_sup_left hdd4) (mem_sup_right (mem_zpowers t))
  have hdd : d * d ∈ S₁ := sup_le_sup_right hQS _ hddQt
  have hdd₀ : d * d ∉ S₀ := fun h => htS₀' (by
    have h1 : t = (d * d)⁻¹ * (d * d * t) := by group
    rw [h1]
    exact mul_mem (inv_mem h) (hQS hdd4))
  set S : Subgroup G := S₁ ⊔ zpowers d with hSdef
  have hSp : IsPGroup 2 S := isPGroup_sup_zpowers_of_mul_self_mem hS₁p hdN₁ hdd
  have hrel : S₁.relIndex S = 2 := relIndex_sup_zpowers_eq_two_of_mul_self_mem hdS hdN₁ hdd
  have hrel₀ : S₀.relIndex S₁ = 2 := relIndex_sup_zpowers_eq_two_of_not_mem htS₀' htS₀ ht2
  have hsq : ∀ h ∈ S, h ∉ S₁ → h * h ∉ S₀ := fun h hh hhS =>
    mul_self_notMem_of_notMem hrel₀ hdS₀ hdN₁ hdd hdd₀ hh hhS
  obtain ⟨hdQ, hdL, -⟩ := graph_element_facts hset hK e ht hKt c hW₁t htN Kc hS₀p hS₀N htS₀ hQL
    hQc hQS hdC hdN₁ hdS hdd
  have hle : Q₀ ⊔ zpowers t ⊔ zpowers d ≤ S :=
    sup_le_sup_right (sup_le_sup_right hQS _) _
  have hmax := maximal_inf_centralizer hset hK e ht hKt hQL hQc hdC hdQ
    (fun h => hdS (sup_le_sup_right hQS _ h)) hddQt hle
  have hodd : ¬ 2 ∣ S.index := by
    refine not_two_dvd_index_of_forall_conj hSp hmax fun s hsN _ => ?_
    have htS : t ∈ S := mem_sup_left htS₁
    have hyS : s * t * s⁻¹ ∈ S := (mem_normalizer_iff.1 hsN t).1 htS
    have hy2 : s * t * s⁻¹ * (s * t * s⁻¹) = 1 := by
      calc s * t * s⁻¹ * (s * t * s⁻¹) = s * (t * t) * s⁻¹ := by group
        _ = 1 := by rw [ht2]; group
    have hyS₁ : s * t * s⁻¹ ∈ S₁ := by
      by_contra h
      exact hsq _ hyS h (by rw [hy2]; exact one_mem _)
    have hyt : s * t * s⁻¹ * t ∈ S₀ := by
      rcases CFSG.SeitzReduction.mem_or_mul_mem_of_mem_sup_zpowers ht2 htS₀ hyS₁ with h | h
      · exact absurd (hS₀N h) (by simpa using hconj s⁻¹)
      · exact h
    have h3 : s * t * s⁻¹ * t * t = s * t * s⁻¹ := by rw [mul_assoc _ t t, ht2, mul_one]
    obtain ⟨z, hzS₀, hz⟩ := hThom _ hyt (by rw [h3]; exact hy2)
    rw [h3] at hz
    exact ⟨z, mem_sup_left (mem_sup_left hzS₀), hz⟩
  have hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
    CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard hset.standardSetting.standard htC ht
  have htL : t ∉ L := by
    intro h
    have h1 : t ∈ L ⊓ zpowers t := mem_inf.2 ⟨h, mem_zpowers t⟩
    rw [inf_zpowers_eq_bot hset.center_eq_bot htC ht, mem_bot] at h1
    rw [h1, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have ht1 : t ≠ 1 := fun h => htL (h ▸ L.one_mem)
  obtain ⟨l, hl, hyy⟩ := exists_mul_self_mem_zpowers hset hK e ht hKt hdC hdL
  set y := l⁻¹ * d with hydef
  have hyt : y * y = t := by
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hyy
    rw [← zpow_mod_orderOf, ht, Nat.cast_ofNat] at hk
    rcases Int.emod_two_eq_zero_or_one k with h0 | h0
    · exfalso
      rw [h0, zpow_zero] at hk
      have hdl : d * l⁻¹ * d⁻¹ ∈ L := (mem_normalizer_iff.1 (hCN hdC) _).1 (inv_mem hl)
      have h1 : d * d = (d * l⁻¹ * d⁻¹)⁻¹ * l * (y * y) := by rw [hydef]; group
      rw [← hk, mul_one] at h1
      have h2 : d * d ∈ L := by rw [h1]; exact mul_mem (inv_mem hdl) hl
      apply htL
      have h3 : t = (d * d)⁻¹ * (d * d * t) := by group
      rw [h3]
      exact mul_mem (inv_mem h2) (hQL hdd4)
    · rw [h0, zpow_one] at hk
      exact hk.symm
  have hlt : l ∈ centralizer ({t} : Set G) :=
    mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 htC) l hl)
  have hyC : y ∈ centralizer ({t} : Set G) := mul_mem (inv_mem hlt) hdC
  have hyp : IsPGroup 2 (zpowers y) := by
    refine isPGroup_zpowers_of_pow_two_pow_eq_one (n := 2) ?_
    rw [show (2 : ℕ) ^ 2 = 2 + 2 from rfl, pow_add, sq, hyt, ht2]
  obtain ⟨w, hwC, hwx⟩ := exists_conj_mem_of_maximal (hSp.to_le inf_le_left) inf_le_right hmax
    hyC hyp
  set x := w⁻¹ * y * w with hxdef
  have hxS : x ∈ S := (mem_inf.1 hwx).1
  have hwt : w * t = t * w := mem_centralizer_singleton_iff.1 hwC
  have hxx : x * x = t := by
    calc x * x = w⁻¹ * (y * y) * w := by rw [hxdef]; group
      _ = w⁻¹ * (t * w) := by rw [hyt, mul_assoc]
      _ = t := by rw [← hwt]; group
  have hxS₁ : x ∉ S₁ := by
    intro hx
    have hxL := sup_inf_centralizer_le_sup hset hK e ht hKt c hW₁t htN Kc
      (mem_inf.2 ⟨sup_le_sup_right hS₀N _ hx, (mem_inf.1 hwx).2⟩)
    have hwN : w ∈ normalizer ((L ⊔ zpowers t : Subgroup G) : Set G) :=
      mem_normalizer_sup_of_mem_of_mem_normalizer (hCN hwC)
        (mem_normalizer_zpowers_of_mul_eq_mul hwt.symm)
    have hyL : y ∈ L ⊔ zpowers t := by
      have h1 := (mem_normalizer_iff.1 hwN x).1 hxL
      have h2 : w * x * w⁻¹ = y := by rw [hxdef]; group
      rwa [h2] at h1
    apply hdL
    have h3 : d = l * y := by rw [hydef]; group
    rw [h3]
    exact mul_mem (mem_sup_left hl) hyL
  have hxo : orderOf x = 2 ^ 2 := by
    refine orderOf_eq_prime_pow (p := 2) (n := 1) ?_ ?_
    · rw [pow_one, sq, hxx]
      exact ht1
    · rw [show (2 : ℕ) ^ (1 + 1) = 2 + 2 from rfl, pow_add, sq, hxx, ht2]
  have hmin : ∀ y' ∈ S, y' ∉ S₁ → IsPGroup 2 (zpowers y') → orderOf x ≤ orderOf y' := by
    intro y' hy'S hy'S₁ hy'p
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hy'p
    rw [Nat.card_zpowers] at hk
    rw [hxo, hk]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    by_contra hlt2
    interval_cases k
    · rw [pow_zero, orderOf_eq_one_iff] at hk
      exact hy'S₁ (hk ▸ one_mem _)
    · have h1 : y' ^ 2 = 1 := by rw [← pow_one 2, ← hk, pow_orderOf_eq_one]
      rw [sq] at h1
      exact hsq _ hy'S hy'S₁ (by rw [h1]; exact one_mem _)
  have hfus : ∀ g : G, g⁻¹ * x * g ∉ S₁ := by
    intro g hg
    have h1 := mul_self_mem_of_mem_sup_zpowers ht2 htS₀ hg
    have h2 : g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
    rw [h2, hxx] at h1
    exact hconj g (hS₀N h1)
  obtain ⟨N, hN, hNidx⟩ :=
    F4Pilot.exists_normal_index_two_of_not_fused_of_relIndex_eq_two hrel hodd hxS hxS₁ hxo
      hmin hfus
  have hG2 : 2 < Nat.card G := by
    have h1 := Subgroup.card_le_card_group L
    rw [Nat.card_congr e.toEquiv, card_projectiveSL_five_of_card_two hK] at h1
    omega
  exact CFSG.SeitzReduction.not_exists_normal_index_two_of_simple hG2 ⟨N, hN, hNidx⟩

end Setting

end CFSG.SeitzReduction.LinearPilot
