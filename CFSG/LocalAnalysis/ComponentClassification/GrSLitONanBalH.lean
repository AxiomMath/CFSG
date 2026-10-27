module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitONanBalL34
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitONanBalOne

public section

namespace CFSG.ComponentClassification.GrSLit.ONanBal

open Subgroup CFSG.OddStandard CFSG.OddStandard.ONanRec CFSG.OddStandard.ONanRec.F2
  CFSG.OddStandard.ONanRec.F2.AlpE CFSG.ABGLocalTools

theorem alpFrame_of_injective {M N : Type*} [Group M] [Group N] (f : M →* N)
    (hf : Function.Injective f) {a1 a2 a3 a4 a5 : M}
    (h : AlpFrame (f a1) (f a2) (f a3) (f a4) (f a5)) : AlpFrame a1 a2 a3 a4 a5 where
  v1_four := hf (by simp only [map_pow, map_one]; exact h.v1_four)
  v2_four := hf (by simp only [map_pow, map_one]; exact h.v2_four)
  v3_four := hf (by simp only [map_pow, map_one]; exact h.v3_four)
  t_two := hf (by simp only [map_pow, map_one]; exact h.t_two)
  c12 := hf (by simp only [map_mul]; exact h.c12)
  c13 := hf (by simp only [map_mul]; exact h.c13)
  c23 := hf (by simp only [map_mul]; exact h.c23)
  s_four := hf (by simp only [map_pow, map_mul]; exact h.s_four)
  s_t := hf (by simp only [map_mul, map_inv]; exact h.s_t)
  s_v1 := hf (by simp only [map_mul, map_inv]; exact h.s_v1)
  s_v2 := hf (by simp only [map_mul, map_inv]; exact h.s_v2)
  s_v3 := hf (by simp only [map_mul, map_inv]; exact h.s_v3)
  t_v1 := hf (by simp only [map_mul, map_inv]; exact h.t_v1)
  t_v2 := hf (by simp only [map_mul, map_inv]; exact h.t_v2)
  t_v3 := hf (by simp only [map_mul, map_inv]; exact h.t_v3)

theorem mem_closure_subtype_iff {G : Type*} [Group G] {H : Subgroup G} (S : Set H) (y : H) :
    y ∈ closure S ↔ (y : G) ∈ closure (((↑) : H → G) '' S) := by
  rw [← Subgroup.mem_map_iff_mem H.subtype_injective (K := closure S), MonoidHom.map_closure]
  rfl

section Sub

variable {G : Type} [Group G] {H : Subgroup G} (a b c d e y : H)

theorem mem_alpW_subtype : y ∈ alpW a b c ↔ (y : G) ∈ alpW (a : G) b c := by
  rw [alpW, alpW, mem_closure_subtype_iff]
  simp [Set.image_insert_eq]

theorem mem_alpP_subtype : y ∈ alpP a b c d e ↔ (y : G) ∈ alpP (a : G) b c d e := by
  rw [alpP, alpP, mem_closure_subtype_iff]
  simp [Set.image_insert_eq]

theorem coe_xel_subtype : ((xel a b c : H) : G) = xel (a : G) b c := by
  simp [xel]

end Sub

variable {G : Type} [Group G] [Finite G] {v1 v2 v3 s t : G}

local notation "𝔵" => xel v1 v2 v3
local notation "𝔷" => invRep v1 v2 v3 s t 0

theorem sig0E_v2sq : sig0E (gen 1 ^ 2) = gen 0 ^ 2 * gen 1 ^ 2 := by decide

theorem v2sq_mem_WEL : gen 1 ^ 2 ∈ WEL := by decide

theorem noIdx_of_le (D : FusCtx G v1 v2 v3 s t) {H : Subgroup G}
    (hH : normalizer (alpW v1 v2 v3 : Set G) ≤ H) (N : Subgroup H) (hN : N.Normal) :
    N.index ≠ 2 := by
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPH : alpP v1 v2 v3 s t ≤ H := D.P_le_normalizer_W.trans hH
  have hVH : normalizer (alpV v1 v2 v3 : Set G) ≤ H := fun n hn => hH (D.normalizer_V_le_W hn)
  set N' := N.map H.subtype with hN'
  have hmem : ∀ g (hg : g ∈ H), g ∈ N' ↔ (⟨g, hg⟩ : H) ∈ N := by
    intro g hg
    constructor
    · rintro ⟨n, hn, hng⟩
      have e : (⟨g, hg⟩ : H) = n := Subtype.ext hng.symm
      rwa [e]
    · intro h
      exact ⟨_, h, rfl⟩
  have hsq : ∀ g ∈ H, g * g ∈ N' := fun g hg =>
    (hmem _ (mul_mem hg hg)).2 (mul_self_mem_of_index_two h2 ⟨g, hg⟩)
  have hmul : ∀ a ∈ H, ∀ b ∈ H, (a * b ∈ N' ↔ (a ∈ N' ↔ b ∈ N')) := by
    intro a ha b hb
    rw [hmem _ (mul_mem ha hb), hmem _ ha, hmem _ hb]
    exact mul_mem_iff_of_index_two h2 (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
  have hconj : ∀ a ∈ H, ∀ b ∈ H, (a * b * a⁻¹ ∈ N' ↔ b ∈ N') := by
    intro a ha b hb
    rw [hmem _ (mul_mem (mul_mem ha hb) (inv_mem ha)), hmem _ hb]
    constructor
    · intro h
      have h1 := hN.conj_mem _ h (⟨a, ha⟩ : H)⁻¹
      have e : (⟨a, ha⟩ : H)⁻¹ * ⟨a * b * a⁻¹, mul_mem (mul_mem ha hb) (inv_mem ha)⟩ *
          (⟨a, ha⟩ : H)⁻¹⁻¹ = ⟨b, hb⟩ := Subtype.ext (by
        show a⁻¹ * (a * b * a⁻¹) * a⁻¹⁻¹ = b
        group)
      rwa [e] at h1
    · intro h
      exact hN.conj_mem _ h ⟨a, ha⟩
  have hmemP : ∀ {g : G}, g ∈ ({v1, v2, v3, s, t} : Set G) → g ∈ H := fun hg =>
    hPH (subset_closure hg)
  have hv1H : v1 ∈ H := hmemP (by simp)
  have hv2H : v2 ∈ H := hmemP (by simp)
  have hv3H : v3 ∈ H := hmemP (by simp)
  have hsH : s ∈ H := hmemP (by simp)
  have htH : t ∈ H := hmemP (by simp)
  have hv1V : v1 ∈ alpV v1 v2 v3 := subset_closure (by simp)
  have hv2V : v2 ∈ alpV v1 v2 v3 := subset_closure (by simp)
  have hWN : alpW v1 v2 v3 ≤ N' := by
    rw [alpW, closure_le]
    rintro _ (rfl | rfl | rfl) <;> rw [pow_two]
    · exact hsq v1 hv1H
    · exact hsq v2 hv2H
    · exact hsq v3 hv3H
  obtain ⟨n, hnV, hact⟩ := D.exists_normalizer_V_actsAs sig0E sig0E_W sig0E_invol sig0E_mul
  have hnH : n ∈ H := hVH hnV
  have hv2sq : n * (v2 * v2) * n⁻¹ = v1 * v1 * (v2 * v2) := by
    have h := hact (gen 1 ^ 2) v2sq_mem_WEL
    rw [sig0E_v2sq] at h
    simp only [map_mul, map_pow, AlpEmb.φ_v1, AlpEmb.φ_v2] at h
    rw [pow_two, pow_two] at h
    exact h
  set a := n * v2 * n⁻¹ with ha
  have haV : a ∈ alpV v1 v2 v3 := (mem_normalizer_iff.1 hnV v2).1 hv2V
  have ha2 : a * a = v1 * v1 * (v2 * v2) := by
    rw [← hv2sq, ha]
    group
  have hv12 : v1 * v2 = v2 * v1 := D.fr.c12
  have haW : a * (v1 * v2)⁻¹ ∈ alpW v1 v2 v3 := by
    rw [D.mem_W_iff]
    have hV12 : (v1 * v2)⁻¹ ∈ alpV v1 v2 v3 := inv_mem (mul_mem hv1V hv2V)
    refine ⟨mul_mem haV hV12, ?_⟩
    have hc := D.comm_V haV hV12
    have h12 : (v1 * v2) * (v1 * v2) = v1 * v1 * (v2 * v2) := by
      calc v1 * v2 * (v1 * v2) = v1 * (v2 * v1) * v2 := by group
        _ = v1 * (v1 * v2) * v2 := by rw [hv12]
        _ = v1 * v1 * (v2 * v2) := by group
    calc a * (v1 * v2)⁻¹ * (a * (v1 * v2)⁻¹) = a * ((v1 * v2)⁻¹ * a) * (v1 * v2)⁻¹ := by group
      _ = a * (a * (v1 * v2)⁻¹) * (v1 * v2)⁻¹ := by rw [hc]
      _ = (a * a) * ((v1 * v2) * (v1 * v2))⁻¹ := by group
      _ = 1 := by rw [ha2, h12, mul_inv_cancel]
  have haH : a ∈ H := mul_mem (mul_mem hnH hv2H) (inv_mem hnH)
  have hwH : a * (v1 * v2)⁻¹ ∈ H := mul_mem haH (inv_mem (mul_mem hv1H hv2H))
  have e1 : a ∈ N' ↔ v2 ∈ N' := hconj n hnH v2 hv2H
  have e2 : a ∈ N' ↔ v1 * v2 ∈ N' := by
    have e : a = a * (v1 * v2)⁻¹ * (v1 * v2) := by group
    rw [e, hmul _ hwH _ (mul_mem hv1H hv2H)]
    exact ⟨fun h => h.1 (hWN haW), fun h => ⟨fun _ => h, fun _ => hWN haW⟩⟩
  have e3 : v1 * v2 ∈ N' ↔ (v1 ∈ N' ↔ v2 ∈ N') := hmul v1 hv1H v2 hv2H
  have e4 : v2 ∈ N' ↔ v1 ∈ N' := by
    have h := hconj s⁻¹ (inv_mem hsH) v1 hv1H
    rwa [inv_inv, D.fr.s_v1] at h
  have hv1N : v1 ∈ N' := by tauto
  have hv2N : v2 ∈ N' := e4.2 hv1N
  have hv3N : v3 ∈ N' := by
    have h := hconj s⁻¹ (inv_mem hsH) v2 hv2H
    rw [inv_inv, D.fr.s_v2] at h
    exact h.2 hv2N
  have hVN : alpV v1 v2 v3 ≤ N' := by
    rw [alpV, closure_le]
    rintro _ (rfl | rfl | rfl)
    · exact hv1N
    · exact hv2N
    · exact hv3N
  have hKH : centralizer (alpW v1 v2 v3 : Set G) ≤ H := (centralizer_le_normalizer _).trans hH
  have hCW : centralizer (alpW v1 v2 v3 : Set G) ≤ N' := by
    have := hN
    set K' := (centralizer (alpW v1 v2 v3 : Set G)).subgroupOf H with hK'
    set V' := (alpV v1 v2 v3).subgroupOf H with hV'
    have hV'K' : V' ≤ N ⊓ K' := by
      intro v hv
      refine mem_inf.2 ⟨?_, mem_subgroupOf.2 (D.V_le_centralizer_W (mem_subgroupOf.1 hv))⟩
      have := (hmem v v.2).1 (hVN (mem_subgroupOf.1 hv))
      exact this
    have hodd : ¬ 2 ∣ V'.relIndex K' := by
      rw [hV', hK', Subgroup.relIndex_subgroupOf hKH]
      exact (isSylowOf_iff.1 D.isSylowOf_V_centralizer_W).2.2
    have hri := Subgroup.relIndex_mul_relIndex V' (N ⊓ K') K' hV'K' inf_le_right
    have hdvd : (N ⊓ K').relIndex K' ∣ 2 := by
      rw [Subgroup.inf_relIndex_right, ← h2]
      exact Subgroup.relIndex_dvd_index_of_normal N K'
    have h1 : (N ⊓ K').relIndex K' = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
      · exact h
      · exfalso
        apply hodd
        rw [← hri, h]
        exact dvd_mul_left 2 _
    rw [Subgroup.relIndex_eq_one] at h1
    intro c hc
    exact (hmem c (hKH hc)).2 (h1 (mem_subgroupOf.2 hc)).1
  have hCV : centralizer (alpV v1 v2 v3 : Set G) ≤ N' :=
    (centralizer_le (D.W_le_V : (alpW v1 v2 v3 : Set G) ⊆ alpV v1 v2 v3)).trans hCW
  have hs2N : s ^ 2 ∈ N' := by
    rw [pow_two]
    exact hsq s hsH
  obtain ⟨n₁, hn₁, hc₁⟩ := D.exists_s2_of_t
  have htN : t ∈ N' := by
    have h1 : n₁⁻¹ * t * n₁ ∈ N' := by
      have e : n₁⁻¹ * t * n₁ = s ^ 2 * ((s ^ 2)⁻¹ * (n₁⁻¹ * t * n₁)) := by group
      rw [e]
      exact mul_mem hs2N (hCV hc₁)
    have h := hconj n₁⁻¹ (inv_mem (hVH hn₁)) t htH
    rw [inv_inv] at h
    exact h.1 h1
  obtain ⟨n₂, hn₂, hc₂⟩ := D.exists_s2_of_st
  have hstN : s * t ∈ N' := by
    have h1 : n₂ * (s * t) * n₂⁻¹ ∈ N' := by
      have e : n₂ * (s * t) * n₂⁻¹ = s ^ 2 * ((s ^ 2)⁻¹ * (n₂ * (s * t) * n₂⁻¹)) := by group
      rw [e]
      exact mul_mem hs2N (hCV hc₂)
    exact (hconj n₂ (hVH hn₂) (s * t) (mul_mem hsH htH)).1 h1
  have hsN : s ∈ N' := ((hmul s hsH t htH).1 hstN).2 htN
  have hPN : alpP v1 v2 v3 s t ≤ N' := by
    rw [alpP, closure_le]
    rintro _ (rfl | rfl | rfl | rfl | rfl)
    · exact hv1N
    · exact hv2N
    · exact hv3N
    · exact hsN
    · exact htN
  have hP'N : (alpP v1 v2 v3 s t).subgroupOf H ≤ N := fun y hy =>
    (hmem y y.2).1 (hPN (mem_subgroupOf.1 hy))
  have h3 : N.index ∣ (alpP v1 v2 v3 s t).relIndex H := Subgroup.index_dvd_of_le hP'N
  have h4 : (alpP v1 v2 v3 s t).relIndex H ∣ (alpP v1 v2 v3 s t).index :=
    Subgroup.relIndex_dvd_index_of_le hPH
  exact D.not_two_dvd_index_P (h2 ▸ h3.trans h4)

theorem oneClass_and_centralizer_x_le
    (D : FusCtx G v1 v2 v3 s t) (hF : ThmC.ThmCFull) (hone : OneClass G) {H : Subgroup G}
    (hH : normalizer (alpW v1 v2 v3 : Set G) ≤ H) (hθ : theta 𝔵 ≤ H) {a g : G}
    (ha : a ∈ alpW v1 v2 v3) (hg : g ∈ H) (hgP : g * a * g⁻¹ ∈ alpP v1 v2 v3 s t)
    (hgW : g * a * g⁻¹ ∉ alpW v1 v2 v3) : OneClass H ∧ centralizer ({𝔵} : Set G) ≤ H := by
  have hPH : alpP v1 v2 v3 s t ≤ H := D.P_le_normalizer_W.trans hH
  have hm : ∀ {y : G}, y ∈ ({v1, v2, v3, s, t} : Set G) → y ∈ H :=
    fun hy => hPH (subset_closure hy)
  set w1 : H := ⟨v1, hm (by simp)⟩ with hw1
  set w2 : H := ⟨v2, hm (by simp)⟩ with hw2
  set w3 : H := ⟨v3, hm (by simp)⟩ with hw3
  set ws : H := ⟨s, hm (by simp)⟩ with hws
  set wt : H := ⟨t, hm (by simp)⟩ with hwt
  have hfr : AlpFrame w1 w2 w3 ws wt :=
    alpFrame_of_injective H.subtype H.subtype_injective D.fr
  have hz : orderOf (w1 ^ 2 * w3 ^ 2) = 2 := by
    rw [← orderOf_injective H.subtype H.subtype_injective (w1 ^ 2 * w3 ^ 2)]
    simp only [map_mul, map_pow]
    exact D.orderOf_rep 0
  have hPle : (D.P : Subgroup G) ≤ H := by
    rw [D.hP]
    exact hPH
  have hP' : ((D.P.subtype hPle : Sylow 2 H) : Subgroup H) = alpP w1 w2 w3 ws wt := by
    ext y
    rw [Sylow.coe_subtype, mem_subgroupOf, D.hP, mem_alpP_subtype]
  let DH : FusCtx H w1 w2 w3 ws wt :=
    { fr := hfr
      E := hfr.emb' hz alpBound_cert
      hF := f2Check_cert
      P := D.P.subtype hPle
      hP := hP'
      noIdx := noIdx_of_le D hH }
  have haH : a ∈ H := hPH (D.W_le_P ha)
  have honeH : OneClass H := by
    refine oneClass_of_not_closed DH
      ⟨⟨a, haH⟩, (mem_alpW_subtype w1 w2 w3 ⟨a, haH⟩).2 ha, (⟨g, hg⟩ : H)⁻¹, ?_, ?_⟩
    · rw [mem_alpP_subtype]
      simpa using hgP
    · rw [mem_alpW_subtype]
      simpa using hgW
  have hcH := card_centralizer_x DH hF honeH
  have hcG := card_centralizer_x D hF hone
  set x' : H := xel w1 w2 w3 with hx'
  have hx'e : (x' : G) = 𝔵 := coe_xel_subtype w1 w2 w3
  set Cx' := centralizer ({x'} : Set H) with hCx'
  have hmapC : Cx'.map H.subtype ≤ centralizer ({𝔵} : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ centralizer ({x'} : Set H) := hy
    rw [mem_centralizer_singleton_iff] at hy' ⊢
    rw [← hx'e]
    exact congrArg Subtype.val hy'
  have hcardA : Nat.card ((theta 𝔵).subgroupOf H) = Nat.card (theta 𝔵) :=
    Nat.card_congr (subgroupOfEquivOfLe hθ).toEquiv
  have hAC : (theta 𝔵).subgroupOf H ≤ Cx' := by
    intro y hy
    show y ∈ centralizer ({x'} : Set H)
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    have h1 := mem_centralizer_singleton_iff.1 (theta_le_centralizer 𝔵 (mem_subgroupOf.1 hy))
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hx'e]
    exact h1
  have hA : (theta 𝔵).subgroupOf H ≤ theta x' := by
    set B := ((theta 𝔵).subgroupOf H).subgroupOf Cx' with hB
    have hBn : B.Normal := by
      refine ⟨fun b hb c => ?_⟩
      rw [mem_subgroupOf, mem_subgroupOf] at hb ⊢
      have hc : ((c : H) : G) ∈ centralizer ({𝔵} : Set G) := hmapC ⟨c, c.2, rfl⟩
      exact conj_mem_oddCore_map (le_normalizer hc) hb
    have hBo : Odd (Nat.card B) := by
      rw [hB, Nat.card_congr (subgroupOfEquivOfLe hAC).toEquiv, hcardA]
      exact odd_card_theta 𝔵
    have hBle : B ≤ pPrimeCore 2 Cx' := le_sSup ⟨hBn, Nat.coprime_two_left.2 hBo⟩
    intro y hy
    exact ⟨⟨y, hAC hy⟩, hBle (mem_subgroupOf.2 hy), rfl⟩
  have h1 : Nat.card (theta 𝔵) ≤ Nat.card (theta x') := hcardA ▸ card_le_of_le hA
  have heq : Cx'.map H.subtype = centralizer ({𝔵} : Set G) := by
    apply eq_of_le_of_card_ge hmapC
    rw [card_map_of_injective H.subtype_injective, hcH, hcG]
    exact Nat.mul_le_mul_left _ h1
  refine ⟨honeH, fun y hy => ?_⟩
  rw [← heq] at hy
  obtain ⟨y', -, rfl⟩ := hy
  exact y'.2

end CFSG.ComponentClassification.GrSLit.ONanBal
