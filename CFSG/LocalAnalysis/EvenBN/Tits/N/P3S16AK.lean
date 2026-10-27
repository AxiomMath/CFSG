module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3S16AP
public import CFSG.Goldschmidt.Steps.Balance
public import CFSG.LocalAnalysis.EvenBN.Tits.N.Defs

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.S16A

open Subgroup CFSG.Open

section OddCore

variable {Γ : Type*} [Group Γ]

def conjEquiv {K : Subgroup Γ} {g : Γ} (hg : g ∈ normalizer (K : Set Γ)) : ↥K ≃* ↥K where
  toFun k := ⟨g * k * g⁻¹, (mem_normalizer_iff.1 hg k).1 k.2⟩
  invFun k := ⟨g⁻¹ * k * g, by simpa using (mem_normalizer_iff.1 (inv_mem hg) k).1 k.2⟩
  left_inv k := Subtype.ext (by simp [mul_assoc])
  right_inv k := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp only [coe_mul]; group)

theorem oddCoreSub_conj {K : Subgroup Γ} {g o : Γ} (hg : g ∈ normalizer (K : Set Γ))
    (ho : o ∈ oddCoreSub K) : g * o * g⁻¹ ∈ oddCoreSub K := by
  obtain ⟨o₀, ho₀, rfl⟩ := ho
  have h1 : standardComponentOddCore ↥K = CFSG.pPrimeCore 2 ↥K :=
    CFSG.Goldschmidt.goldschmidtOddCore_eq_pPrimeCore ↥K
  have hmap := CFSG.pPrimeCore_map_iso 2 (conjEquiv hg)
  rw [← h1] at hmap
  have : conjEquiv hg o₀ ∈ standardComponentOddCore ↥K := by
    rw [← hmap]
    exact ⟨o₀, ho₀, rfl⟩
  exact ⟨conjEquiv hg o₀, this, rfl⟩

variable [Finite Γ]

theorem odd_card_oddCoreSub (K : Subgroup Γ) : Odd (Nat.card (oddCoreSub K)) :=
  CFSG.Goldschmidt.Balance.odd_card_oddCoreOf K

theorem eq_one_of_mem_of_isPGroup {K P : Subgroup Γ} (hP : IsPGroup 2 P) {o : Γ} (hoP : o ∈ P)
    (hoO : o ∈ oddCoreSub K) : o = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨o, hoP⟩
  have h1 : orderOf o ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  have h2 : orderOf o ∣ Nat.card (oddCoreSub K) :=
    Subgroup.orderOf_dvd_natCard _ hoO
  have h3 : Odd (orderOf o) := (odd_card_oddCoreSub K).of_dvd_nat h2
  have h4 : Nat.Coprime (orderOf o) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_left.2 h3).symm
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd h4 h1)

end OddCore

section KLevel

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem mem_zpowers_cases {a b : Γ} (ha : a * a = 1) (hb : b ∈ zpowers a) : b = 1 ∨ b = a := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hb
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [zpow_mul, zpow_two, ha, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, zpow_two, ha, one_zpow, one_mul]

structure KHyp (K V S : Subgroup Γ) (t : Γ) : Prop where
  V_elem : IsElemAbelian 2 V
  V_le : V ≤ K
  V_central : ∀ v ∈ V, ∀ k ∈ K, v * k = k * v
  t_sq : t * t = 1
  t_notMem : t ∉ K
  t_normK : t ∈ normalizer (K : Set Γ)
  t_normV : t ∈ normalizer (V : Set Γ)
  V_trans : ∀ w ∈ V, t * w * t⁻¹ = w → ∃ v ∈ V, w = v * (t * v⁻¹ * t⁻¹)
  card_le : Nat.card ↥(K ⊓ centralizer ({t} : Set Γ)) ≤
    2 * Nat.card ↥(V ⊓ centralizer ({t} : Set Γ))
  S_sylow : fusionIsSylowIn 2 S K
  S_inv : ∀ s ∈ S, t * s * t⁻¹ ∈ S

variable {K V S : Subgroup Γ} {t : Γ}

theorem KHyp.S_le (h : KHyp K V S t) : S ≤ K := h.S_sylow.1

theorem KHyp.t_notMem_S (h : KHyp K V S t) : t ∉ S := fun hts => h.t_notMem (h.S_le hts)

theorem KHyp.V_pGroup (h : KHyp K V S t) : IsPGroup 2 V := fun g =>
  ⟨1, by
    apply Subtype.ext
    simpa using h.V_elem.2 g g.2⟩

theorem KHyp.V_le_S (h : KHyp K V S t) : V ≤ S := by
  have hc : ∀ v ∈ V, ∀ y ∈ S, v * y * v⁻¹ = y := fun v hv y hy => by
    rw [h.V_central v hv y (h.S_le hy)]
    group
  have hVN : V ≤ normalizer (S : Set Γ) := fun v hv => by
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [hc v hv x hx]
      exact hx
    · intro hx
      have h1 := hc v⁻¹ (Subgroup.inv_mem V hv) _ hx
      have h2 : v⁻¹ * (v * x * v⁻¹) * v⁻¹⁻¹ = x := by group
      rw [h2] at h1
      rw [h1]
      exact hx
  have hsup : IsPGroup 2 (V ⊔ S : Subgroup Γ) := h.V_pGroup.to_sup_of_normal_right' h.S_sylow.2.1 hVN
  have := h.S_sylow.2.2 (V ⊔ S) (sup_le h.V_le h.S_le) hsup le_sup_right
  exact this ▸ le_sup_left

theorem KHyp.t_normS (h : KHyp K V S t) : t ∈ normalizer (S : Set Γ) := by
  rw [mem_normalizer_iff]
  intro x
  refine ⟨h.S_inv x, fun hx => ?_⟩
  have h1 := h.S_inv _ hx
  have e : t * (t * x * t⁻¹) * t⁻¹ = x := by
    calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t * t)⁻¹ := by group
      _ = x := by rw [h.t_sq]; group
  rwa [e] at h1

theorem KHyp.zpowers_le_normalizer (h : KHyp K V S t) : zpowers t ≤ normalizer (S : Set Γ) := by
  rw [zpowers_le]
  exact h.t_normS

theorem KHyp.mem_P (h : KHyp K V S t) {x : Γ} :
    x ∈ S ⊔ zpowers t ↔ x ∈ S ∨ ∃ s ∈ S, x = s * t := by
  have hcoe := coe_mul_of_right_le_normalizer_left S (zpowers t) h.zpowers_le_normalizer
  show x ∈ ((S ⊔ zpowers t : Subgroup Γ) : Set Γ) ↔ _
  rw [hcoe]
  constructor
  · rintro ⟨s, hs, z, hz, rfl⟩
    rcases mem_zpowers_cases h.t_sq hz with rfl | rfl
    · left
      simpa using hs
    · right
      exact ⟨s, hs, rfl⟩
  · rintro (hx | ⟨s, hs, rfl⟩)
    · exact ⟨x, hx, 1, one_mem _, by simp⟩
    · exact ⟨s, hs, t, mem_zpowers t, rfl⟩

theorem KHyp.isPGroup_P (h : KHyp K V S t) : IsPGroup 2 ↥(S ⊔ zpowers t) := by
  have hz : IsPGroup 2 (zpowers t) := fun g => ⟨1, by
    apply Subtype.ext
    rcases mem_zpowers_cases h.t_sq g.2 with h1 | h1
    · simp [h1]
    · rw [pow_one, Subgroup.coe_pow, sq, h1]
      simpa using h.t_sq⟩
  exact h.S_sylow.2.1.to_sup_of_normal_left' hz h.zpowers_le_normalizer

theorem card_subgroupOf_inf_centralizer {P A : Subgroup Γ} (hAP : A ≤ P) {t : Γ} (htP : t ∈ P) :
    Nat.card ↥(A.subgroupOf P ⊓ centralizer ({(⟨t, htP⟩ : ↥P)} : Set ↥P)) =
      Nat.card ↥(A ⊓ centralizer ({t} : Set Γ)) := by
  have hle : A ⊓ centralizer ({t} : Set Γ) ≤ P := inf_le_left.trans hAP
  have heq : A.subgroupOf P ⊓ centralizer ({(⟨t, htP⟩ : ↥P)} : Set ↥P) =
      (A ⊓ centralizer ({t} : Set Γ)).subgroupOf P := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff,
      Subtype.ext_iff, Subgroup.coe_mul]
  rw [heq]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv

theorem KHyp.pHyp (h : KHyp K V S t) :
    PHyp (S.subgroupOf (S ⊔ zpowers t)) (V.subgroupOf (S ⊔ zpowers t))
      (⟨t, mem_sup_right (mem_zpowers t)⟩ : ↥(S ⊔ zpowers t)) := by
  haveI := h.V_elem.1
  have htP : t ∈ S ⊔ zpowers t := mem_sup_right (mem_zpowers t)
  have hSP : S ≤ S ⊔ zpowers t := le_sup_left
  have hVP : V ≤ S ⊔ zpowers t := h.V_le_S.trans hSP
  refine
    { isPGroup := h.isPGroup_P
      index_two := ?_
      t_notMem := fun hmem => h.t_notMem_S (Subgroup.mem_subgroupOf.1 hmem)
      t_sq := Subtype.ext h.t_sq
      V_elem := ⟨inferInstance, fun x hx => Subtype.ext (by simpa using h.V_elem.2 x hx)⟩
      V_le := fun x hx => Subgroup.mem_subgroupOf.2 (h.V_le_S (Subgroup.mem_subgroupOf.1 hx))
      V_central := fun v hv s hs => Subtype.ext
        (h.V_central v hv s (h.S_le (Subgroup.mem_subgroupOf.1 hs)))
      t_normV := fun v hv => Subgroup.mem_subgroupOf.2
        ((mem_normalizer_iff.1 h.t_normV v).1 (Subgroup.mem_subgroupOf.1 hv))
      V_trans := ?_
      card_le := ?_ }
  · rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨t, htP⟩, fun b => ?_⟩
    rcases h.mem_P.1 b.2 with hb | ⟨s, hs, hbs⟩
    · refine Or.inr ⟨Subgroup.mem_subgroupOf.2 hb, fun hbt => h.t_notMem_S ?_⟩
      have := Subgroup.mem_subgroupOf.1 hbt
      have h2 := S.mul_mem (S.inv_mem hb) this
      simpa using h2
    · have hbS : ¬ (b : Γ) ∈ S := fun hb => h.t_notMem_S (by
        have := S.mul_mem (S.inv_mem hs) (hbs ▸ hb)
        simpa using this)
      refine Or.inl ⟨Subgroup.mem_subgroupOf.2 ?_, fun hb => hbS (Subgroup.mem_subgroupOf.1 hb)⟩
      show (b : Γ) * t ∈ S
      rw [hbs, mul_assoc, h.t_sq, mul_one]
      exact hs
  · intro w hw hwt
    have hw' : (w : Γ) ∈ V := Subgroup.mem_subgroupOf.1 hw
    have hwt' : t * (w : Γ) * t⁻¹ = w := congrArg Subtype.val hwt
    obtain ⟨v, hv, hvw⟩ := h.V_trans w hw' hwt'
    exact ⟨⟨v, hVP hv⟩, Subgroup.mem_subgroupOf.2 hv, Subtype.ext hvw⟩
  · rw [card_subgroupOf_inf_centralizer hSP htP, card_subgroupOf_inf_centralizer hVP htP]
    exact (Subgroup.card_le_of_le (inf_le_inf_right _ h.S_le)).trans h.card_le

theorem KHyp.exists_gen (h : KHyp K V S t) [(V.subgroupOf (S ⊔ zpowers t)).Normal]
    (hcyc : IsCyclic ↥((S.subgroupOf (S ⊔ zpowers t)).map
      (QuotientGroup.mk' (V.subgroupOf (S ⊔ zpowers t))))) : ∃ g ∈ S, S = zpowers g ⊔ V := by
  obtain ⟨g₀, hg₀, heq⟩ := exists_gen_of_cyclic h.pHyp hcyc
  have hSP : S ≤ S ⊔ zpowers t := le_sup_left
  have hVP : V ≤ S ⊔ zpowers t := h.V_le_S.trans hSP
  have hgS : (g₀ : Γ) ∈ S := Subgroup.mem_subgroupOf.1 hg₀
  refine ⟨g₀, hgS, le_antisymm ?_ (sup_le (zpowers_le.2 hgS) h.V_le_S)⟩
  intro s hs
  have h1 : s ∈ ((S.subgroupOf (S ⊔ zpowers t)).map (S ⊔ zpowers t).subtype) := by
    rw [Subgroup.subgroupOf_map_subtype]
    exact ⟨hs, hSP hs⟩
  rw [heq, Subgroup.map_sup, MonoidHom.map_zpowers, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.2 hVP] at h1
  exact h1

end KLevel

end CFSG.LocalAnalysis.EvenBN.Tits.N.S16A
