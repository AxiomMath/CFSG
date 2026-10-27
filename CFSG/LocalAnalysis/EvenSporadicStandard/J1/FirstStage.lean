module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J1.Count
public import CFSG.LocalAnalysis.EvenSporadicStandard.J1.DihedralPair
public import CFSG.LocalAnalysis.EvenSporadicStandard.J1.Step2
public import CFSG.LocalAnalysis.EvenSporadicStandard.J1.StageOne

public section

namespace CFSG.EvenSporadicStandard.J1Std

open Subgroup

section Centralizing

variable {A : Type*} [Group A] [Finite A]

theorem exists_card_eight_centralizing (hA : Nat.card A = 168)
    (hconj : ∀ α β : A, α ≠ 1 → β ≠ 1 → α * α = 1 → β * β = 1 → IsConj α β)
    {α : A} (hα : α ≠ 1) (hα2 : α * α = 1) :
    ∃ P : Subgroup A, Nat.card P = 8 ∧ α ∈ P ∧ P ≤ centralizer ({α} : Set A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, hP₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := A) 2 (n := 3)
    (by rw [hA]; norm_num)
  have hP₀p : IsPGroup 2 P₀ := IsPGroup.of_card hP₀
  have : Nontrivial P₀ := by
    rw [← Finite.one_lt_card_iff_nontrivial, hP₀]
    norm_num
  have := hP₀p.center_nontrivial
  have hZp : IsPGroup 2 (Subgroup.center P₀) := hP₀p.to_subgroup _
  obtain ⟨m, hm0, hm⟩ := hZp.nontrivial_iff_card.mp inferInstance
  have h2 : 2 ∣ Nat.card (Subgroup.center P₀) := by
    rw [hm]
    exact dvd_pow_self 2 hm0.ne'
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center P₀) 2 h2
  set c : A := ((x : P₀) : A) with hc
  have hc2 : orderOf c = 2 := by
    rw [hc, Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hx
  have hcc : c * c = 1 := by
    rw [← pow_two, ← hc2]
    exact pow_orderOf_eq_one c
  have hc1 : c ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hc2
    exact absurd hc2 (by norm_num)
  have hcP : c ∈ P₀ := (x : P₀).2
  have hcomm : ∀ p ∈ P₀, p * c = c * p := fun p hp => by
    have := Subgroup.mem_center_iff.1 x.2 ⟨p, hp⟩
    exact congrArg Subtype.val this
  obtain ⟨g, hg⟩ := isConj_iff.1 (hconj c α hc1 hα hcc hα2)
  refine ⟨P₀.map (MulAut.conj g).toMonoidHom, ?_, ⟨c, hcP, ?_⟩, ?_⟩
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hP₀]
    norm_num
  · simpa [MulAut.conj_apply] using hg
  · rintro _ ⟨p, hp, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← hg]
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply]
    calc g * p * g⁻¹ * (g * c * g⁻¹) = g * (p * c) * g⁻¹ := by group
      _ = g * (c * p) * g⁻¹ := by rw [hcomm p hp]
      _ = g * c * g⁻¹ * (g * p * g⁻¹) := by group

end Centralizing

variable {G : Type} [Group G] [Finite G]

theorem Setting.conj_mem_V_of_first_stage (H : Setting G) (hV : 2 ∣ H.V.index)
    (hcase : Nat.card (H.RC H.V) = Nat.card H.V) {x : G}
    (hxN : x ∈ normalizer (H.V : Set G)) (hc : IsConj H.z x) : x ∈ H.V := by
  by_contra hxV
  have h := H.exists_stage_one hV
  have hx2 : x * x = 1 := H.sq_of_isConj hc
  have hRC : H.RC H.V = H.V := (Subgroup.eq_of_le_of_card_ge h.S_le_RC hcase.le).symm
  have hNE : (normalizer (H.V : Set G) : Subgroup G) ≤ normalizer (H.E : Set G) := fun n hn =>
    mem_normalizer_iff.2 fun e => ⟨fun he => h.N_conj_E hn he, fun he => by
      have := h.N_conj_E (inv_mem hn) he
      simpa [mul_assoc] using this⟩
  set N : Subgroup G := normalizer (H.V : Set G) with hN
  let ρ : N →* MulAut H.E := H.E.normalizerMonoidHom.comp (Subgroup.inclusion hNE)
  have hρ : ∀ (n : N) (e : H.E), ((ρ n e : H.E) : G) = (n : G) * e * (n : G)⁻¹ :=
    fun n e => rfl
  have hker : ∀ n : N, ρ n = 1 ↔ (n : G) ∈ H.V := by
    intro n
    rw [← hRC]
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
  have hNcard : Nat.card N = 2688 := by
    have := h.card_N hV
    rw [H.card_E] at this
    simpa using this
  have hkercard : Nat.card ρ.ker = 16 := by
    have : Nat.card ρ.ker = Nat.card H.V := by
      refine Nat.card_congr ⟨fun n => ⟨(n.1 : G), (hker n.1).1 n.2⟩,
        fun v => ⟨⟨v, le_normalizer v.2⟩, (hker _).2 v.2⟩, ?_, ?_⟩
      · intro n
        rfl
      · intro v
        rfl
    rw [this, H.card_V]
  have hAut : Nat.card (MulAut H.E) = 168 :=
    card_mulAut_of_elemAbelian_eight H.card_E (fun a b => Subtype.ext (H.E_comm a.2 b.2))
      (fun a => Subtype.ext (H.sq_E a.1 a.2))
  have hrange : Nat.card ρ.range = 168 := by
    have := Subgroup.card_ker_mul_card_range ρ
    rw [hkercard, hNcard] at this
    omega
  have hsurj : Function.Surjective ρ := by
    have : ρ.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hrange, hAut])
    exact MonoidHom.range_eq_top.1 this
  set X : N := ⟨x, hxN⟩ with hX
  have hα1 : ρ X ≠ 1 := fun h1 => hxV ((hker X).1 h1)
  have hα2 : ρ X * ρ X = 1 := by
    rw [← map_mul]
    have e : X * X = 1 := Subtype.ext hx2
    rw [e, map_one]
  obtain ⟨P, hPcard, hαP, hPC⟩ := exists_card_eight_centralizing hAut
    (fun a b ha hb ha2 hb2 => isConj_of_involutions H.card_E
      (fun a b => Subtype.ext (H.E_comm a.2 b.2)) (fun a => Subtype.ext (H.sq_E a.1 a.2))
      ha hb ha2 hb2) hα1 hα2
  set Q' : Subgroup N := P.comap ρ with hQ'
  have hQ'card : Nat.card Q' = 128 := by
    have h1 := Subgroup.card_mul_index Q'
    have h2 : Q'.index = P.index := Subgroup.index_comap_of_surjective P hsurj
    have h3 := Subgroup.card_mul_index P
    rw [hPcard, hAut] at h3
    have h4 : P.index = 21 := by omega
    rw [h2, h4, hNcard] at h1
    omega
  set Q : Subgroup G := Q'.map N.subtype with hQ
  have hQcard : Nat.card Q = 128 := by
    rw [hQ, Subgroup.card_map_of_injective N.subtype_injective, hQ'card]
  have hQp : IsPGroup 2 Q := IsPGroup.of_card (n := 7) (by rw [hQcard]; norm_num)
  have hVQ : H.V ≤ Q := fun v hv => Subgroup.mem_map.2 ⟨⟨v, le_normalizer hv⟩, by
    show ρ ⟨v, le_normalizer hv⟩ ∈ P
    rw [(hker _).2 hv]
    exact one_mem P, rfl⟩
  have hxQ : x ∈ Q := Subgroup.mem_map.2 ⟨X, Subgroup.mem_comap.2 hαP, rfl⟩
  have hcomm : ∀ t ∈ Q, ∃ w ∈ H.V, t * x * t⁻¹ = w * x ∧ x * w = w * x := by
    rintro _ ⟨t', ht', rfl⟩
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
    have hwV : (u : G) ∈ H.V := (hker u).1 hu1
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
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
    have hdc : IsConj H.z d := h.conj d hdV hdE
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
      rw [← hRC]
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 fun e he => ?_, hxN⟩
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
  have hcls := card_eq_card_conjClass_mul Q x
  rw [hQcard] at hcls
  have hC : Nat.card (centralizer ({x} : Set G) ⊓ Q : Subgroup G) ≤ 16 :=
    (H.star_conj hc hQp.to_inf_right inf_le_left).1
  have := Nat.mul_le_mul horb hC
  omega

end CFSG.EvenSporadicStandard.J1Std
