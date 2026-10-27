module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SylowEndProj
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SylowEndRho

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd CFSG.GH74.GLS.Bg.Thompson

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa D : Subgroup G}
  {z b : G}

omit [Finite G] in
theorem inf_centralizer_mul_eq {D : Subgroup G} (hDc : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) {d₁ v : G}
    (hd₁ : d₁ ∈ D) : D ⊓ centralizer ({d₁ * v} : Set G) = D ⊓ centralizer ({v} : Set G) := by
  ext x
  constructor
  · rintro ⟨hx, hxc⟩
    refine ⟨hx, mem_centralizer_singleton_iff.2 ?_⟩
    have h1 : x * (d₁ * v) = d₁ * v * x := mem_centralizer_singleton_iff.1 hxc
    have h2 : x * d₁ = d₁ * x := hDc x hx d₁ hd₁
    have : d₁ * (x * v) = d₁ * (v * x) := by
      calc d₁ * (x * v) = (d₁ * x) * v := by group
        _ = (x * d₁) * v := by rw [h2]
        _ = x * (d₁ * v) := by group
        _ = d₁ * v * x := h1
        _ = d₁ * (v * x) := by group
    exact mul_left_cancel this
  · rintro ⟨hx, hxc⟩
    refine ⟨hx, mem_centralizer_singleton_iff.2 ?_⟩
    have h1 : x * v = v * x := mem_centralizer_singleton_iff.1 hxc
    have h2 : x * d₁ = d₁ * x := hDc x hx d₁ hd₁
    calc x * (d₁ * v) = (x * d₁) * v := by group
      _ = d₁ * (x * v) := by rw [h2]; group
      _ = d₁ * (v * x) := by rw [h1]
      _ = d₁ * v * x := by group

section

variable (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
  (hD : DHyp A Aa t D)

include H W W2 hD

omit W2 hD in
theorem ThCyc.two_mul_card_le_of_extremal {P : Subgroup G} (hP : IsPGroup 2 P)
    (hSP : S ⊔ zpowers t ≤ P) {g : G} (hext : IsExtremalIn 2 P (g⁻¹ * t * g)) :
    2 * Nat.card S ≤ Nat.card ↥(P ⊓ centralizer ({g⁻¹ * t * g} : Set G)) := by
  have hext' : IsSylowIn 2 (P ⊓ centralizer ({g⁻¹ * t * g} : Set G))
      (centralizer ({g⁻¹ * t * g} : Set G)) := hext
  have hSt : S ⊔ zpowers t ≤ centralizer ({t} : Set G) :=
    sup_le (fun x hx => mem_centralizer_singleton_iff.2 (H.comm_of_mem_L (W.S_le hx)).symm)
      (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))
  have hQ'c : (S ⊔ zpowers t).map (MulAut.conj g⁻¹).toMonoidHom ≤
      centralizer ({g⁻¹ * t * g} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxt : x * t = t * x := mem_centralizer_singleton_iff.1 (hSt hx)
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc g⁻¹ * x * g * (g⁻¹ * t * g) = g⁻¹ * (x * t) * g := by group
      _ = g⁻¹ * (t * x) * g := by rw [hxt]
      _ = g⁻¹ * t * g * (g⁻¹ * x * g) := by group
  have h := SylowEnd.card_le_of_isSylowIn hext' hQ'c ((hP.to_le hSP).map _)
  rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, H.card_sup_zpowers W] at h
  exact h

theorem ThCyc.ext_extremal_of_card
    (hAb : ∀ g : G, ∀ Y : Subgroup G, Y ≤ L.map (MulAut.conj g).toMonoidHom → IsPGroup 2 Y →
      (∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) → Nat.card Y ≤ 2 ^ 8)
    (hZ : ∀ s ∈ S, (∀ x ∈ S, s * x * s⁻¹ * x⁻¹ ∈ Aa) → s ∈ B)
    {P : Subgroup G} (hP : IsPGroup 2 P) (hSP : S ⊔ zpowers t ≤ P) (hBpP : Bp A t ≤ P)
    (hPN : P ≤ normalizer ((W5 A t : Subgroup G) : Set G)) {g : G}
    (hR : 2 * Nat.card S ≤ Nat.card ↥(P ⊓ centralizer ({g⁻¹ * t * g} : Set G)))
    (huP : g⁻¹ * t * g ∈ P) :
    g⁻¹ * t * g ∉ D ∧ Nat.card ↥(D ⊓ centralizer ({g⁻¹ * t * g} : Set G)) = 2 ^ 8 ∧
      P = (P ⊓ centralizer ({g⁻¹ * t * g} : Set G)) ⊔ D ∧
      (∀ x ∈ P, (g⁻¹ * t * g) * x * (g⁻¹ * t * g)⁻¹ * x⁻¹ ∈ D) ∧
      ∃ d₁ ∈ D, g⁻¹ * t * g = d₁ * t ∨ g⁻¹ * t * g = d₁ * b ∨ g⁻¹ * t * g = d₁ * (b * t) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSP' : S ≤ P := le_sup_left.trans hSP
  have hDP : D ≤ P := (H.D_le_Bp W W2 hD).trans hBpP
  have hND : normalizer ((W5 A t : Subgroup G) : Set G) ≤ normalizer (D : Set G) :=
    le_normalizer_of_conj_mem hD.norm
  have hPD : P ≤ normalizer (D : Set G) := hPN.trans hND
  have hPcard := H.card_P_mul W hP hSP' hBpP hPN
  have hSpos : 0 < Nat.card S := Nat.card_pos
  have hPpos : 0 < Nat.card P := Nat.card_pos
  set u := g⁻¹ * t * g with hu
  have huD : u ∉ D := by
    intro huD
    have hM : D ≤ centralizer ({u} : Set G) := fun x hx =>
      mem_centralizer_singleton_iff.2 (hD.comm x hx u huD)
    have h := H.card_le_of_abelian hAb (c := g) hM huD hD.comm (hP.to_le hDP)
    rw [hD.card] at h
    norm_num at h
  set K0 := D ⊓ centralizer ({u} : Set G) with hK0
  set R' := P ⊓ centralizer ({u} : Set G) with hR'
  have hK0c : ∀ x ∈ K0, x * u = u * x := fun x hx => mem_centralizer_singleton_iff.1 hx.2
  have hRcard : 2 * Nat.card S ≤ Nat.card R' := hR
  have hRD : R' ⊓ D = K0 := by
    ext x
    constructor
    · rintro ⟨⟨_, hc⟩, hd⟩
      exact ⟨hd, hc⟩
    · rintro ⟨hd, hc⟩
      exact ⟨⟨hDP hd, hc⟩, hd⟩
  have hRnorm : R' ≤ normalizer (D : Set G) := inf_le_left.trans hPD
  have hprod := SylowEnd.card_sup_mul_card_inf hRnorm
  rw [hRD, hD.card] at hprod
  have hRDP : R' ⊔ D ≤ P := sup_le inf_le_left hDP
  have hle : Nat.card ↥(R' ⊔ D) ≤ Nat.card P := Subgroup.card_le_of_le hRDP
  have hK0lb : 2 ^ 8 ≤ Nat.card K0 := SylowEnd.arith_lb hprod hle hPcard hRcard hPpos
  have hK0ub : Nat.card K0 ≤ 2 ^ 8 := by
    have hM : K0 ⊔ zpowers u ≤ centralizer ({u} : Set G) :=
      sup_le inf_le_right (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))
    have hvM : u ∈ K0 ⊔ zpowers u := mem_sup_right (mem_zpowers u)
    have hK0u : u ∉ K0 := fun h => huD h.1
    have hab : ∀ x ∈ K0 ⊔ zpowers u, ∀ y ∈ K0 ⊔ zpowers u, x * y = y * x :=
      SylowEnd.sup_zpowers_comm hK0c (fun x hx y hy => hD.comm x hx.1 y hy.1)
    have hcomm : zpowers u ≤ centralizer (K0 : Set G) :=
      zpowers_le.2 (mem_centralizer_iff.2 fun y hy => hK0c y hy)
    have h2 : IsPGroup 2 ↥(K0 ⊔ zpowers u) :=
      isPGroup_sup_of_commute (hP.to_le (inf_le_left.trans hDP))
        (H.isPGroup_zpowers_conj g) hcomm
    have h := H.card_le_of_abelian hAb (c := g) hM hvM hab h2
    rw [H.card_sup_conj hK0c hK0u] at h
    norm_num at h
    omega
  have hK0 : Nat.card K0 = 2 ^ 8 := le_antisymm hK0ub hK0lb
  have hRDeq : R' ⊔ D = P := by
    refine Subgroup.eq_of_le_of_card_ge hRDP ?_
    rw [hK0] at hprod
    norm_num at hprod hPcard
    omega
  have hcent : ∀ x ∈ P, u * x * u⁻¹ * x⁻¹ ∈ D := by
    intro x hx
    have hx' : x ∈ D ⊔ R' := by rw [sup_comm, hRDeq]; exact hx
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left D R' hRnorm] at hx'
    obtain ⟨d, hd, r, hr, rfl⟩ := hx'
    have hur : r * u = u * r := mem_centralizer_singleton_iff.1 hr.2
    have h1 : u * r * u⁻¹ = r := by rw [← hur]; group
    have hud : u * d * u⁻¹ ∈ D := (mem_normalizer_iff.1 (hPD huP) d).1 hd
    have e : u * (d * r) * u⁻¹ * (d * r)⁻¹ = (u * d * u⁻¹) * d⁻¹ := by
      calc u * (d * r) * u⁻¹ * (d * r)⁻¹ = (u * d * u⁻¹) * (u * r * u⁻¹) * r⁻¹ * d⁻¹ := by
            group
        _ = (u * d * u⁻¹) * d⁻¹ := by rw [h1]; group
    rw [e]
    exact D.mul_mem hud (D.inv_mem hd)
  refine ⟨huD, hK0, hRDeq.symm, hcent, ?_⟩
  obtain ⟨d', hd', s0, hs0, τ, hτ, hus⟩ :=
    H.exists_decomp_P W W2 hD hP hSP' hBpP hPN huP
  have hτx : ∀ x ∈ S, τ * x * τ⁻¹ = x := by
    intro x hx
    rcases hτ with h1 | h1
    · rw [h1]
      group
    · rw [h1]
      calc t * x * t⁻¹ = (x * t) * t⁻¹ := by rw [H.comm_of_mem_L (W.S_le hx)]
        _ = x := by group
  have hs0B : s0 ∈ B := by
    refine hZ s0 hs0 fun x hx => ?_
    have hxP : x ∈ P := hSP' hx
    have h1 := hcent x hxP
    have hcD : s0 * x * s0⁻¹ * x⁻¹ ∈ D := by
      have e1 : u * x * u⁻¹ * x⁻¹ = d' * (s0 * x * s0⁻¹ * x⁻¹) * (x * d'⁻¹ * x⁻¹) := by
        rw [hus]
        calc d' * s0 * τ * x * (d' * s0 * τ)⁻¹ * x⁻¹
            = d' * s0 * (τ * x * τ⁻¹) * s0⁻¹ * d'⁻¹ * x⁻¹ := by group
          _ = d' * s0 * x * s0⁻¹ * d'⁻¹ * x⁻¹ := by rw [hτx x hx]
          _ = _ := by group
      have e2 : s0 * x * s0⁻¹ * x⁻¹ = d'⁻¹ * (u * x * u⁻¹ * x⁻¹) * (x * d' * x⁻¹) := by
        rw [e1]
        group
      rw [e2]
      exact D.mul_mem (D.mul_mem (D.inv_mem hd') h1)
        ((mem_normalizer_iff.1 (hPD hxP) d').1 hd')
    have hcL : s0 * x * s0⁻¹ * x⁻¹ ∈ L :=
      L.mul_mem (L.mul_mem (L.mul_mem (W.S_le hs0) (W.S_le hx)) (L.inv_mem (W.S_le hs0)))
        (L.inv_mem (W.S_le hx))
    exact H.mem_Aa_of_mem_C_of_mem_L W W2 (hD.le_C hcD) hcL
  rcases W2.mem_Aa_or_mul_b W hs0B with h | h
  · refine ⟨d' * s0, D.mul_mem hd' (hD.Aa_le h), ?_⟩
    rcases hτ with h1 | h1
    · exfalso
      apply huD
      rw [hus, h1, mul_one]
      exact D.mul_mem hd' (hD.Aa_le h)
    · left
      rw [hus, h1]
  · refine ⟨d' * (s0 * b), D.mul_mem hd' (hD.Aa_le h), ?_⟩
    have e : d' * s0 = d' * (s0 * b) * b := by
      calc d' * s0 = d' * (s0 * b) * b⁻¹ := by group
        _ = d' * (s0 * b) * b := by rw [W2.b_inv_eq_self]
    rcases hτ with h1 | h1
    · right
      left
      rw [hus, h1, mul_one, e]
    · right
      right
      rw [hus, h1, e]
      group

theorem ThCyc.ext_extremal
    (hAb : ∀ g : G, ∀ Y : Subgroup G, Y ≤ L.map (MulAut.conj g).toMonoidHom → IsPGroup 2 Y →
      (∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) → Nat.card Y ≤ 2 ^ 8)
    (hZ : ∀ s ∈ S, (∀ x ∈ S, s * x * s⁻¹ * x⁻¹ ∈ Aa) → s ∈ B)
    {P : Subgroup G} (hP : IsPGroup 2 P) (hSP : S ⊔ zpowers t ≤ P) (hBpP : Bp A t ≤ P)
    (hPN : P ≤ normalizer ((W5 A t : Subgroup G) : Set G)) {g : G}
    (hext : IsExtremalIn 2 P (g⁻¹ * t * g)) (huP : g⁻¹ * t * g ∈ P) :
    g⁻¹ * t * g ∉ D ∧ Nat.card ↥(D ⊓ centralizer ({g⁻¹ * t * g} : Set G)) = 2 ^ 8 ∧
      P = (P ⊓ centralizer ({g⁻¹ * t * g} : Set G)) ⊔ D ∧
      (∀ x ∈ P, (g⁻¹ * t * g) * x * (g⁻¹ * t * g)⁻¹ * x⁻¹ ∈ D) ∧
      ∃ d₁ ∈ D, g⁻¹ * t * g = d₁ * t ∨ g⁻¹ * t * g = d₁ * b ∨ g⁻¹ * t * g = d₁ * (b * t) :=
  H.ext_extremal_of_card W W2 hD hAb hZ hP hSP hBpP hPN
    (H.two_mul_card_le_of_extremal W hP hSP hext) huP

omit W2 hD in
theorem ThCyc.isPGroup_S_sup_Bp : IsPGroup 2 ↥(S ⊔ Bp A t) :=
  W.pgroup.to_sup_of_normal_right' (H.isPGroup_Bp W)
    ((H.S_le_normalizer W).trans (H.normalizer_le_normalizer_Bp W))

omit W2 hD in
theorem ThCyc.S_sup_Bp_le_normalizer :
    S ⊔ Bp A t ≤ normalizer ((W5 A t : Subgroup G) : Set G) :=
  sup_le (H.S_le_normalizer W) inf_le_right

omit hD in
theorem ThCyc.t_mem_Bp : t ∈ Bp A t :=
  (inf_le_left : Csub A Aa t ≤ Bp A t) (H.t_mem_inf_centralizer_Aa W W2)

end

end CFSG.EvenSporadicStandard.ThStd
