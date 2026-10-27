module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Lemma12_9b

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec12b

open Subgroup CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12

section

variable {G : Type} [Group G] [Finite G] {x z : G} {S T P Q Rd F : Subgroup G} {a : G}
  {V P₁ F' : Subgroup G}

namespace Hyp129

variable (H : Hyp129 G x z S T P Q Rd F)
include H

theorem xinv_P (A : Ph0 G x z S T P a) {p : G} (hp : p ∈ P) (hp2 : p * p = 1) :
    ∃ g : G, g⁻¹ * x * g = x * p := by
  by_cases hp1 : p = 1
  · exact ⟨1, by rw [hp1]; simp⟩
  obtain ⟨c, hc, hcp⟩ := H.conj p hp hp2 hp1
  have hxc : x * c = c * x := Subgroup.mem_centralizer_iff.1 hc x (Set.mem_singleton x)
  refine ⟨a * c, ?_⟩
  have hcx : c⁻¹ * x * c = x := by
    calc c⁻¹ * x * c = c⁻¹ * (x * c) := by group
      _ = c⁻¹ * (c * x) := by rw [hxc]
      _ = x := by group
  calc (a * c)⁻¹ * x * (a * c) = c⁻¹ * (a⁻¹ * x * a) * c := by group
    _ = c⁻¹ * (x * z) * c := by rw [A.xa']
    _ = c⁻¹ * (x * (c * p * c⁻¹)) * c := by rw [hcp]
    _ = (c⁻¹ * x * c) * p := by group
    _ = x * p := by rw [hcx]

theorem zconj_P {p : G} (hp : p ∈ P) (hp2 : p * p = 1) (hp1 : p ≠ 1) :
    ∃ g : G, g⁻¹ * z * g = p := by
  obtain ⟨c, _, hcp⟩ := H.conj p hp hp2 hp1
  exact ⟨c, by rw [← hcp]; group⟩

end Hyp129

namespace Ph1

variable (H : Hyp129 G x z S T P Q Rd F) (A : Ph0 G x z S T P a)
  (B : Ph1 G x z T P Rd a V P₁ F')
include H A B

omit A in
theorem P1_le_T : P₁ ≤ T := B.le_Rd.trans H.base.Rd_le_T

theorem inv_cases {c : G} (hc : c ∈ P₁) (hc2 : c * c = 1) :
    c ∈ P ∨ ∃ p₁ ∈ P, ∃ u ∈ Hconj a V, u * u = 1 ∧ u ∉ P ⊔ Subgroup.zpowers x ∧
      c = p₁⁻¹ * u * p₁ := by
  rcases B.cases with e | ⟨u, huW, hu2, huR, e⟩
  · left; rw [e] at hc; exact hc
  · rw [e] at hc
    have huT : u ∈ T := Ph0.W_le_T H A B.V_le huW
    have huRd : u ∈ Rd := Ph0.W_le_Rd H A B.V_le B.V_four huW
    obtain ⟨a', ha', p, hp, hcd⟩ := mem_sup_zpowers_of_normalIn H.base.P_normal huT hc
    rcases zpowers_sq_cases hu2 ha' with h1 | h1
    · left; rw [hcd, h1, one_mul]; exact hp
    · right
      rw [h1] at hcd
      have ha₀ : u * p * u⁻¹ ∈ P := H.base.P_normal.2 u huT p hp
      have hcu : u * p * u⁻¹ * u = c := by rw [hcd]; group
      have hR : u ∉ P ⊔ Q := by rw [H.h127.Q_eq]; exact huR
      obtain ⟨p₁, hp₁, he⟩ := H.trans u huRd hR hu2 (u * p * u⁻¹) ha₀ 1 P.one_mem
        (by rw [hcu]; exact hc2) (by rw [one_mul]; exact hu2)
      refine ⟨p₁, hp₁, u, huW, hu2, huR, ?_⟩
      rw [hcu, one_mul] at he
      have : c = p₁⁻¹ * (p₁ * c * p₁⁻¹) * p₁ := by group
      rw [this, he]

theorem inv_zconj {c : G} (hc : c ∈ P₁) (hc2 : c * c = 1) (hc1 : c ≠ 1) :
    ∃ g : G, g⁻¹ * z * g = c := by
  rcases B.inv_cases H A hc hc2 with hcP | ⟨p₁, hp₁, u, huW, hu2, huR, hcu⟩
  · exact H.zconj_P hcP hc2 hc1
  · have hv'V : a * u * a⁻¹ ∈ V := huW
    have hv'P : a * u * a⁻¹ ∈ P := B.V_le hv'V
    have hv'2 : (a * u * a⁻¹) * (a * u * a⁻¹) = 1 := (B.V_four.1 _ hv'V).1
    have hv'1 : a * u * a⁻¹ ≠ 1 := by
      intro h1
      apply hc1
      have hu1 : u = 1 := by
        have h2 : u = a⁻¹ * (a * u * a⁻¹) * a := by group
        rw [h2, h1]; group
      rw [hcu, hu1]; group
    obtain ⟨g, hg⟩ := H.zconj_P hv'P hv'2 hv'1
    refine ⟨g * a * p₁, ?_⟩
    calc (g * a * p₁)⁻¹ * z * (g * a * p₁) = p₁⁻¹ * (a⁻¹ * (g⁻¹ * z * g) * a) * p₁ := by group
      _ = p₁⁻¹ * (a⁻¹ * (a * u * a⁻¹) * a) * p₁ := by rw [hg]
      _ = c := by rw [hcu]; group

theorem inv_xconj {c : G} (hc : c ∈ P₁) (hc2 : c * c = 1) :
    ∃ g : G, g⁻¹ * x * g = x * c := by
  rcases B.inv_cases H A hc hc2 with hcP | ⟨p₁, hp₁, u, huW, hu2, huR, hcu⟩
  · exact H.xinv_P A hcP hc2
  · have hv'V : a * u * a⁻¹ ∈ V := huW
    have hzP : z ∈ P := B.V_le B.z_V
    have hv'P : a * u * a⁻¹ ∈ P := B.V_le hv'V
    have hzv'V : z * (a * u * a⁻¹) ∈ V := V.mul_mem B.z_V hv'V
    have hzv'P : z * (a * u * a⁻¹) ∈ P := B.V_le hzv'V
    have hzv'2 : (z * (a * u * a⁻¹)) * (z * (a * u * a⁻¹)) = 1 := (B.V_four.1 _ hzv'V).1
    obtain ⟨g, hg⟩ := H.xinv_P A hzv'P hzv'2
    have hxp : x * p₁ = p₁ * x := H.base.x_central p₁ (H.base.P_le_T hp₁)
    have hx1 : p₁⁻¹ * x * p₁ = x := by
      calc p₁⁻¹ * x * p₁ = p₁⁻¹ * (x * p₁) := by group
        _ = p₁⁻¹ * (p₁ * x) := by rw [hxp]
        _ = x := by group
    have hza' : a⁻¹ * z * a = z := by
      have := A.za
      calc a⁻¹ * z * a = a⁻¹ * (a * z * a⁻¹) * a := by rw [this]
        _ = z := by group
    have key : a⁻¹ * (x * (z * (a * u * a⁻¹))) * a = x * u := by
      calc a⁻¹ * (x * (z * (a * u * a⁻¹))) * a = (a⁻¹ * x * a) * (a⁻¹ * z * a) * u := by group
        _ = (x * z) * z * u := by rw [A.xa', hza']
        _ = x * u := by rw [mul_assoc x z z, H.hz.z_sq, mul_one]
    refine ⟨g * a * p₁, ?_⟩
    calc (g * a * p₁)⁻¹ * x * (g * a * p₁) = p₁⁻¹ * (a⁻¹ * (g⁻¹ * x * g) * a) * p₁ := by group
      _ = p₁⁻¹ * (a⁻¹ * (x * (z * (a * u * a⁻¹))) * a) * p₁ := by rw [hg]
      _ = p₁⁻¹ * (x * u) * p₁ := by rw [key]
      _ = (p₁⁻¹ * x * p₁) * (p₁⁻¹ * u * p₁) := by group
      _ = x * c := by rw [hx1, hcu]

theorem zconj_T_iff {y : G} (hyT : y ∈ T) :
    (∃ g : G, g⁻¹ * z * g = y) ↔ (y ∈ P₁ ∧ y * y = 1 ∧ y ≠ 1) := by
  constructor
  · rintro ⟨g, hg⟩
    have hy2 : y * y = 1 := by
      rw [← hg]
      calc g⁻¹ * z * g * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
        _ = 1 := by rw [H.hz.z_sq]; group
    have hy1 : y ≠ 1 := by
      intro h1
      apply H.hz.z_ne_one
      have h2 : z = g * (g⁻¹ * z * g) * g⁻¹ := by group
      rw [h2, hg, h1]; group
    refine ⟨?_, hy2, hy1⟩
    have hyRd : y ∈ Rd := H.h127.omega1_le (Subgroup.subset_closure ⟨hyT, hy2⟩)
    rw [← B.sup_x] at hyRd
    obtain ⟨p, hp, c, hc, hyp⟩ := mem_sup_of_commute
      (comm_zpowers (fun u hu => H.base.x_central u (B.P1_le_T H hu))) hyRd
    rcases zpowers_sq_cases H.base.x_sq hc with h1 | h1
    · rw [hyp, h1, mul_one]; exact hp
    · exfalso
      rw [h1] at hyp
      have hpx : p * x = x * p := (H.base.x_central p (B.P1_le_T H hp)).symm
      have hp2 : p * p = 1 := by
        have : y * y = p * p := by
          calc y * y = (p * x) * (p * x) := by rw [hyp]
            _ = p * (x * p) * x := by group
            _ = p * (p * x) * x := by rw [← hpx]
            _ = p * p * (x * x) := by group
            _ = p * p := by rw [H.base.x_sq, mul_one]
        rw [← this]; exact hy2
      obtain ⟨g', hg'⟩ := B.inv_xconj H A hp hp2
      have hyx : y = g'⁻¹ * x * g' := by rw [hg', hyp, hpx]
      have hzc := (H.h127.z_not_conj A.card4 (g' * g⁻¹)).1
      apply hzc
      have : (g' * g⁻¹)⁻¹ * x * (g' * g⁻¹) = g * (g'⁻¹ * x * g') * g⁻¹ := by group
      rw [this, ← hyx, ← hg]; group
  · rintro ⟨hy, hy2, hy1⟩
    exact B.inv_zconj H A hy hy2 hy1

theorem P1_eq_closure :
    P₁ = Subgroup.closure {y : G | y ∈ T ∧ ∃ g : G, g⁻¹ * z * g = y} := by
  apply le_antisymm
  · obtain ⟨ρ, s, j, hD⟩ := dihData_of_dih H.base.T_pgroup (B.P1_le_T H) B.dih B.big
    intro d hd
    obtain ⟨c₁, hc₁, c₂, hc₂, h1, h2, rfl⟩ := hD.prod_inv d hd
    have key : ∀ c ∈ P₁, c * c = 1 →
        c ∈ Subgroup.closure {y : G | y ∈ T ∧ ∃ g : G, g⁻¹ * z * g = y} := by
      intro c hc hc2
      by_cases hc1 : c = 1
      · rw [hc1]; exact Subgroup.one_mem _
      · exact Subgroup.subset_closure ⟨B.P1_le_T H hc, B.inv_zconj H A hc hc2 hc1⟩
    exact Subgroup.mul_mem _ (key c₁ hc₁ h1) (key c₂ hc₂ h2)
  · rw [Subgroup.closure_le]
    rintro y ⟨hyT, hy⟩
    exact ((B.zconj_T_iff H A hyT).1 hy).1

theorem P1_normalS : ∀ s ∈ S, ∀ c ∈ P₁, s * c * s⁻¹ ∈ P₁ := by
  intro s hs c hc
  rw [B.P1_eq_closure H A] at hc ⊢
  have hle : Subgroup.closure {y : G | y ∈ T ∧ ∃ g : G, g⁻¹ * z * g = y} ≤
      Hconj s (Subgroup.closure {y : G | y ∈ T ∧ ∃ g : G, g⁻¹ * z * g = y}) := by
    rw [Subgroup.closure_le]
    rintro y ⟨hyT, g, hg⟩
    rw [SetLike.mem_coe, mem_Hconj]
    exact Subgroup.subset_closure ⟨H.T_normal_S s hs y hyT, g * s⁻¹, by rw [← hg]; group⟩
  exact hle hc

end Ph1

end

end CFSG.GH74.GLS.Stage1.Thm6.Sec12b
