module

import CFSG.LocalAnalysis.EvenSporadicStandard.J1.FirstStage
public import CFSG.LocalAnalysis.EvenSporadicStandard.ReeStd.RCCases

public section

namespace CFSG.EvenSporadicStandard.ReeStd

open Subgroup CFSG.EvenSporadicStandard

variable {G : Type} [Group G] [Finite G]

theorem exists_isPGroup_of_normal {A V X : Subgroup G} (hV : IsPGroup 2 V) (hVA : V ≤ A)
    (hAN : A ≤ normalizer (V : Set G)) (hX : IsPGroup 2 X) (hXA : X ≤ A) :
    ∃ T : Subgroup G, IsPGroup 2 T ∧ V ≤ T ∧ X ≤ T ∧ T ≤ A ∧ Odd (T.relIndex A) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : (V.subgroupOf A).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVA).2 hAN
  obtain ⟨Q, hQ⟩ := (hX.comap_subtype (K := A)).exists_le_sylow
  have hVp : IsPGroup 2 (V.subgroupOf A) := hV.comap_subtype
  have hVQ : V.subgroupOf A ≤ (Q : Subgroup A) := hVp.le_sylow_of_normal Q
  refine ⟨(Q : Subgroup A).map A.subtype, Q.isPGroup'.map _, ?_, ?_, ?_, ?_⟩
  · intro v hv
    exact ⟨⟨v, hVA hv⟩, hVQ hv, rfl⟩
  · intro p hp
    exact ⟨⟨p, hXA hp⟩, hQ hp, rfl⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · have hrel : ((Q : Subgroup A).map A.subtype).relIndex A = (Q : Subgroup A).index := by
      rw [Subgroup.relIndex, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective A.subtype_injective]
    rw [hrel]
    exact Nat.not_even_iff_odd.mp fun h => Q.not_dvd_index (even_iff_two_dvd.mp h)

theorem LocalSetting.conj_mem_V_of_first_stage (H : LocalSetting G) (h0 : Stage H H.V H.E) (hV : 2 ∣ H.V.index)
    (hcase : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ H.RC H.V → P ≤ H.V) {x : G}
    (hxN : x ∈ normalizer (H.V : Set G)) (hc : IsConj H.z x) : x ∈ H.V := by
  by_contra hxV
  have hx2 : x * x = 1 := H.sq_of_isConj hc
  have h2 : ∀ y : G, y * y = 1 → y ∈ H.RC H.V → y ∈ H.V := fun y hy2 hyR =>
    hcase (zpowers y) (isPGroup_zpowers (k := 1) (by rw [pow_one, pow_two]; exact hy2))
      (zpowers_le.2 hyR) (mem_zpowers y)
  have hRD : H.RC H.V = H.DC H.V := by
    rw [h0.RC_eq_of_forall_le hV hcase]
    exact sup_eq_left.2 h0.V_le_DC
  have hNE : (normalizer (H.V : Set G) : Subgroup G) ≤ normalizer (H.E : Set G) := fun n hn =>
    mem_normalizer_iff.2 fun e => ⟨fun he => h0.N_conj_E hn he, fun he => by
      have := h0.N_conj_E (inv_mem hn) he
      simpa [mul_assoc] using this⟩
  set N : Subgroup G := normalizer (H.V : Set G) with hN
  let ρ : N →* MulAut H.E := H.E.normalizerMonoidHom.comp (Subgroup.inclusion hNE)
  have hρ : ∀ (n : N) (e : H.E), ((ρ n e : H.E) : G) = (n : G) * e * (n : G)⁻¹ :=
    fun n e => rfl
  have hker : ∀ n : N, ρ n = 1 ↔ (n : G) ∈ H.RC H.V := by
    intro n
    constructor
    · intro h1
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 fun e he => ?_, n.2⟩
      have h2 : (n : G) * e * (n : G)⁻¹ = e := by
        have := congrArg (fun α : MulAut H.E => ((α ⟨e, he⟩ : H.E) : G)) h1
        simpa [hρ] using this
      calc e * (n : G) = ((n : G) * e * (n : G)⁻¹) * (n : G) := by rw [h2]
        _ = (n : G) * e := by group
    · intro h1
      obtain ⟨hc1, -⟩ := Subgroup.mem_inf.1 h1
      refine MulEquiv.ext fun e => Subtype.ext ?_
      rw [hρ]
      have := Subgroup.mem_centralizer_iff.1 hc1 e e.2
      calc (n : G) * e * (n : G)⁻¹ = (e * (n : G)) * (n : G)⁻¹ := by rw [this]
        _ = e := by group
  have hDpos : 0 < Nat.card (H.DC H.V) := Nat.card_pos
  have hNcard : Nat.card N = 168 * Nat.card (H.DC H.V) := by
    have := h0.card_N hV
    rw [H.card_E] at this
    omega
  have hkercard : Nat.card ρ.ker = Nat.card (H.DC H.V) := by
    rw [← hRD]
    refine Nat.card_congr ⟨fun n => ⟨(n.1 : G), (hker n.1).1 n.2⟩,
      fun v => ⟨⟨v, v.2.2⟩, (hker _).2 v.2⟩, ?_, ?_⟩
    · intro n
      rfl
    · intro v
      rfl
  have hAut : Nat.card (MulAut H.E) = 168 :=
    J1Std.card_mulAut_of_elemAbelian_eight H.card_E (fun a b => Subtype.ext (H.E_comm a.2 b.2))
      (fun a => Subtype.ext (H.sq_E a.1 a.2))
  have hrange : Nat.card ρ.range = 168 := by
    have h1 := Subgroup.card_ker_mul_card_range ρ
    rw [hkercard, hNcard] at h1
    exact Nat.eq_of_mul_eq_mul_left hDpos (h1.trans (mul_comm _ _))
  have hsurj : Function.Surjective ρ := by
    have : ρ.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hrange, hAut])
    exact MonoidHom.range_eq_top.1 this
  set X : N := ⟨x, hxN⟩ with hX
  have hα1 : ρ X ≠ 1 := fun h1 => hxV (h2 x hx2 ((hker X).1 h1))
  have hα2 : ρ X * ρ X = 1 := by
    rw [← map_mul]
    have e : X * X = 1 := Subtype.ext hx2
    rw [e, map_one]
  obtain ⟨P, hPcard, hαP, hPC⟩ := J1Std.exists_card_eight_centralizing hAut
    (fun a b ha hb ha2 hb2 => J1Std.isConj_of_involutions H.card_E
      (fun a b => Subtype.ext (H.E_comm a.2 b.2)) (fun a => Subtype.ext (H.sq_E a.1 a.2))
      ha hb ha2 hb2) hα1 hα2
  set Q' : Subgroup N := P.comap ρ with hQ'
  have hQ'card : Nat.card Q' = 8 * Nat.card (H.DC H.V) := by
    have h1 := Subgroup.card_mul_index Q'
    have h2 : Q'.index = P.index := Subgroup.index_comap_of_surjective P hsurj
    have h3 := Subgroup.card_mul_index P
    rw [hPcard, hAut] at h3
    have h4 : P.index = 21 := by omega
    rw [h2, h4, hNcard] at h1
    omega
  set A : Subgroup G := Q'.map N.subtype with hA
  have hAcard : Nat.card A = 8 * Nat.card (H.DC H.V) := by
    rw [hA, Subgroup.card_map_of_injective N.subtype_injective, hQ'card]
  have hAN : A ≤ normalizer (H.V : Set G) := by
    rintro _ ⟨n, -, rfl⟩
    exact n.2
  have hVA : H.V ≤ A := fun v hv => Subgroup.mem_map.2 ⟨⟨v, le_normalizer hv⟩, by
    show ρ ⟨v, le_normalizer hv⟩ ∈ P
    rw [(hker _).2 (h0.S_le_RC hv)]
    exact one_mem P, rfl⟩
  have hxA : x ∈ A := Subgroup.mem_map.2 ⟨X, Subgroup.mem_comap.2 hαP, rfl⟩
  have hxp : IsPGroup 2 (zpowers x) :=
    isPGroup_zpowers (k := 1) (by rw [pow_one, pow_two]; exact hx2)
  obtain ⟨Q, hQp, hVQ, hxQ', hQA, hQodd⟩ :=
    exists_isPGroup_of_normal h0.pgroup hVA hAN hxp (zpowers_le.2 hxA)
  have hxQ : x ∈ Q := hxQ' (mem_zpowers x)
  have hQcard : Nat.card Q = 128 := by
    have h1 := Subgroup.relIndex_mul_card (H := Q) (K := A)
    rw [inf_eq_left.2 hQA] at h1
    obtain ⟨a, ha⟩ := hQp.exists_card_eq
    refine eq_of_odd_mul_eq ⟨a, ha⟩ ⟨7, by norm_num⟩ hQodd h0.odd_relIndex_V_DC ?_
    calc Nat.card Q * Q.relIndex A = Q.relIndex A * Nat.card Q := mul_comm _ _
      _ = Nat.card A := h1
      _ = 8 * Nat.card (H.DC H.V) := hAcard
      _ = 8 * (H.V.relIndex (H.DC H.V) * 16) := by rw [h0.card_DC]
      _ = 128 * H.V.relIndex (H.DC H.V) := by ring
  have hcomm : ∀ t ∈ Q, ∃ w ∈ H.V, t * x * t⁻¹ = w * x ∧ x * w = w * x := by
    intro t ht
    obtain ⟨t', ht', rfl⟩ := hQA ht
    have hρt : ρ t' ∈ P := ht'
    have hcm : ρ t' * ρ X = ρ X * ρ t' := by
      have := hPC hρt
      rw [Subgroup.mem_centralizer_singleton_iff] at this
      exact this
    set u : N := t' * X * t'⁻¹ * X⁻¹ with hu
    have hu1 : ρ u = 1 := by
      have e1 : ρ X⁻¹ = ρ X := by
        rw [map_inv]
        exact inv_eq_of_mul_eq_one_right hα2
      rw [hu, map_mul, map_mul, map_mul, map_inv, e1]
      calc ρ t' * ρ X * (ρ t')⁻¹ * ρ X = (ρ X * ρ t') * (ρ t')⁻¹ * ρ X := by rw [hcm]
        _ = ρ X * ρ X := by group
        _ = 1 := hα2
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
    have huQ : (u : G) ∈ Q := by
      have : (t' : G) * x * (t' : G)⁻¹ * x⁻¹ ∈ Q :=
        mul_mem (mul_mem (mul_mem ht hxQ) (inv_mem ht)) (inv_mem hxQ)
      exact this
    have hwV : (u : G) ∈ H.V :=
      hcase (zpowers (u : G)) (hQp.to_le (zpowers_le.2 huQ)) (zpowers_le.2 ((hker u).1 hu1))
        (mem_zpowers _)
    have hw2 := H.V_sq hwV
    have hwx : (u : G) * x = (t' : G) * x * (t' : G)⁻¹ := by
      show (t' : G) * x * (t' : G)⁻¹ * x⁻¹ * x = _
      group
    have hy2 : ((u : G) * x) * ((u : G) * x) = 1 := by
      rw [hwx]
      calc (t' : G) * x * (t' : G)⁻¹ * ((t' : G) * x * (t' : G)⁻¹)
          = (t' : G) * (x * x) * (t' : G)⁻¹ := by group
        _ = 1 := by rw [hx2]; group
    refine ⟨(u : G), hwV, hwx.symm, ?_⟩
    have e1 : (u : G) * (x * (u : G)) * x = 1 := by
      simpa [mul_assoc] using hy2
    calc x * (u : G) = (u : G)⁻¹ * ((u : G) * (x * (u : G)) * x) * x⁻¹ := by group
      _ = (u : G)⁻¹ * x⁻¹ := by rw [e1]; group
      _ = (u : G) * x := by
        rw [inv_eq_of_mul_eq_one_right hw2, hxinv]
  set D : Subgroup G := H.V ⊓ centralizer ({x} : Set G) with hD
  have hDE : D ≤ H.E := by
    intro d hd
    by_contra hdE
    have hdV : d ∈ H.V := hd.1
    have hdx : d * x = x * d := Subgroup.mem_centralizer_singleton_iff.1 hd.2
    have hdc : IsConj H.z d := h0.conj d hdV hdE
    have hP : IsPGroup 2 (centralizer ({d} : Set G) ⊓ Q : Subgroup G) := hQp.to_inf_right
    have hle : H.V ≤ centralizer ({d} : Set G) ⊓ Q := le_inf (fun v hv =>
      Subgroup.mem_centralizer_singleton_iff.2 (H.V_comm hv hdV)) hVQ
    have hcard := (H.star_conj hdc hP inf_le_left).1
    have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [H.card_V]; exact hcard)
    have hxmem : x ∈ centralizer ({d} : Set G) ⊓ Q :=
      ⟨Subgroup.mem_centralizer_singleton_iff.2 hdx.symm, hxQ⟩
    apply hxV
    rw [heq]
    exact hxmem
  have hD4 : Nat.card D ≤ 4 := by
    have hdvd : Nat.card D ∣ 8 := H.card_E ▸ Subgroup.card_dvd_of_le hDE
    have hne : Nat.card D ≠ 8 := by
      intro h8
      have hDeq : D = H.E := Subgroup.eq_of_le_of_card_ge hDE (by rw [H.card_E, h8])
      apply hxV
      refine h2 x hx2 (Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 fun e he => ?_, hxN⟩)
      have he' : e ∈ D := hDeq ▸ he
      exact Subgroup.mem_centralizer_singleton_iff.1 he'.2
    have hd : Nat.card D ∈ Nat.divisors 8 := Nat.mem_divisors.2 ⟨hdvd, by norm_num⟩
    have h8 : Nat.divisors 8 = {1, 2, 4, 8} := by decide
    rw [h8] at hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    omega
  have hmemD : ∀ y : {y : G // ∃ m ∈ Q, y = m * x * m⁻¹}, y.1 * x⁻¹ ∈ D := by
    rintro ⟨_, t, ht, rfl⟩
    obtain ⟨w, hwV, hy, hwx⟩ := hcomm t ht
    have e1 : t * x * t⁻¹ * x⁻¹ = w := by rw [hy]; group
    show t * x * t⁻¹ * x⁻¹ ∈ D
    rw [e1]
    exact ⟨hwV, Subgroup.mem_centralizer_singleton_iff.2 hwx.symm⟩
  have horb : Nat.card {y : G // ∃ m ∈ Q, y = m * x * m⁻¹} ≤ 4 := by
    refine le_trans (Nat.card_le_card_of_injective (fun y => (⟨y.1 * x⁻¹, hmemD y⟩ : D)) ?_) hD4
    intro a b hab
    exact Subtype.ext (mul_right_cancel (congrArg Subtype.val hab))
  have hcls := J1Std.card_eq_card_conjClass_mul Q x
  rw [hQcard] at hcls
  have hC : Nat.card (centralizer ({x} : Set G) ⊓ Q : Subgroup G) ≤ 16 :=
    (H.star_conj hc hQp.to_inf_right inf_le_left).1
  have := Nat.mul_le_mul horb hC
  omega

end CFSG.EvenSporadicStandard.ReeStd
