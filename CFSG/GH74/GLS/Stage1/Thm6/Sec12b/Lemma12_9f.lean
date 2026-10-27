module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Lemma12_9e

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec12b

open Subgroup CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12

section

variable {G : Type} [Group G] [Finite G] {x z : G} {S T P Q Rd F : Subgroup G} {a : G}
  {V P₁ F' : Subgroup G}

theorem pow_four_eq {G : Type*} [Group G] (w : G) : w ^ 4 = (w * w) * (w * w) := by
  simp [pow_succ, mul_assoc]

namespace Hyp129

theorem card_P_four_or_ge8 (H : Hyp129 G x z S T P Q Rd F) :
    Nat.card P = 4 ∨ 8 ≤ Nat.card P := by
  obtain ⟨V, hVP, hV⟩ := H.P4
  have hP4' : 4 ≤ Nat.card P := by
    have := Subgroup.card_le_of_le hVP
    rwa [hV.2] at this
  have hpg : IsPGroup 2 ↥P := H.base.T_pgroup.to_le H.base.P_le_T
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hpg
  by_cases hn2 : n ≤ 2
  · left
    interval_cases n
    · rw [pow_zero] at hn; omega
    · rw [pow_one] at hn; omega
    · rw [hn]; norm_num
  · right
    have h8' : (8 : ℕ) ≤ 2 ^ n := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

theorem Z0_central (H : Hyp129 G x z S T P Q Rd F) {u : G}
    (hu : u ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers z) :
    u * u = 1 ∧ ∀ t ∈ T, u * t = t * u :=
  ⟨(H.base.xz_le_Z H.hz hu).2.1, fun t ht => (H.base.xz_le_Z H.hz hu).2.2 t ht⟩

theorem Z0_le_Rd (H : Hyp129 G x z S T P Q Rd F) {u : G}
    (hu : u ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers z) : u ∈ Rd := by
  have : Subgroup.zpowers x ⊔ Subgroup.zpowers z ≤ Rd :=
    sup_le ((Subgroup.zpowers_le).2 H.x_mem_Rd)
      ((Subgroup.zpowers_le).2 (H.P_le_Rd H.hz.z_mem_P))
  exact this hu

end Hyp129

namespace Ph1

theorem P1_conj_iff (H : Hyp129 G x z S T P Q Rd F) (A : Ph0 G x z S T P a)
    (B : Ph1 G x z T P Rd a V P₁ F') {g : G} (hg : g ∈ S) :
    ∀ d, d ∈ P₁ ↔ g * d * g⁻¹ ∈ P₁ := by
  intro d
  constructor
  · exact B.P1_normalS H A g hg d
  · intro h
    have := B.P1_normalS H A g⁻¹ (S.inv_mem hg) _ h
    have e : g⁻¹ * (g * d * g⁻¹) * g⁻¹⁻¹ = d := by group
    rwa [e] at this

theorem Rd_normalS (H : Hyp129 G x z S T P Q Rd F) (A : Ph0 G x z S T P a)
    (B : Ph1 G x z T P Rd a V P₁ F') : ∀ s ∈ S, ∀ r ∈ Rd, s * r * s⁻¹ ∈ Rd := by
  intro s hs r hr
  have hle : Rd ≤ Hconj s Rd := by
    rw [← B.sup_x]
    refine sup_le (fun c hc => ?_) ((Subgroup.zpowers_le).2 ?_)
    · rw [mem_Hconj]
      exact Subgroup.mem_sup_left (B.P1_normalS H A s hs c hc)
    · rw [mem_Hconj]
      by_cases hsT : s ∈ T
      · have : s * x * s⁻¹ = x := by
          have h1 := H.base.x_central s hsT
          calc s * x * s⁻¹ = (x * s) * s⁻¹ := by rw [h1]
            _ = x := by group
        rw [this]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
      · rw [Ph0.sx H A hs hsT]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
          (Subgroup.mem_sup_left (B.P_le H.hz.z_mem_P))
  exact hle hr

theorem F'_inv (H : Hyp129 G x z S T P Q Rd F) (B : Ph1 G x z T P Rd a V P₁ F') {y : G}
    (hy : y ∈ F') (hy2 : y * y = 1) : y = 1 ∨ y = x := by
  have hyT : y ∈ T := B.F_le hy
  have hyRd : y ∈ Rd := H.h127.omega1_le (Subgroup.subset_closure ⟨hyT, hy2⟩)
  have : y ∈ F' ⊓ Rd := ⟨hy, hyRd⟩
  rw [B.F_inf] at this
  exact zpowers_sq_cases H.base.x_sq this

theorem exists_w (H : Hyp129 G x z S T P Q Rd F) (B : Ph1 G x z T P Rd a V P₁ F')
    (hF : F' ≠ Subgroup.zpowers x) : ∃ w ∈ F', w * w = x := by
  classical
  have hnle : ¬ F' ≤ Subgroup.zpowers x := fun h => hF (le_antisymm h B.x_le)
  obtain ⟨f, hfF', hfx⟩ := IsConcreteLE.not_le_iff_exists.1 hnle
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.1 H.base.T_pgroup) ⟨f, B.F_le hfF'⟩
  have hm' : orderOf f = 2 ^ m := by rw [← hm]; exact (Subgroup.orderOf_mk f _).symm
  have hex : ∃ j : ℕ, f ^ (2 ^ j) ∈ Subgroup.zpowers x :=
    ⟨m, by rw [← hm', pow_orderOf_eq_one]; exact Subgroup.one_mem _⟩
  obtain ⟨j, hj, hjmin⟩ : ∃ j : ℕ, f ^ (2 ^ j) ∈ Subgroup.zpowers x ∧
      ∀ i < j, f ^ (2 ^ i) ∉ Subgroup.zpowers x :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i hi => Nat.find_min hex hi⟩
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hfx (by simpa using hj)
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hw : f ^ (2 ^ i) * f ^ (2 ^ i) = f ^ (2 ^ (i + 1)) := by
    rw [← pow_add, pow_succ, mul_two]
  have hwF : f ^ (2 ^ i) ∈ F' := Subgroup.pow_mem F' hfF' _
  refine ⟨f ^ (2 ^ i), hwF, ?_⟩
  rw [hw]
  rcases zpowers_sq_cases H.base.x_sq hj with h1 | h1
  · exfalso
    have h2 : f ^ (2 ^ i) * f ^ (2 ^ i) = 1 := by rw [hw, h1]
    rcases B.F'_inv H hwF h2 with h3 | h3
    · exact hjmin i (by omega) (by rw [h3]; exact Subgroup.one_mem _)
    · exact hjmin i (by omega) (by rw [h3]; exact Subgroup.mem_zpowers x)
  · exact h1

theorem w_pow4 (H : Hyp129 G x z S T P Q Rd F) {w : G} (hww : w * w = x) : w ^ 4 = 1 := by
  rw [pow_four_eq, hww, H.base.x_sq]

theorem comm_w_P1 (H : Hyp129 G x z S T P Q Rd F) (A : Ph0 G x z S T P a)
    (B : Ph1 G x z T P Rd a V P₁ F') {w : G} (hwF : w ∈ F') (hww : w * w = x) {p : G}
    (hp : p ∈ P₁) : w * p * w⁻¹ * p⁻¹ = 1 ∨ w * p * w⁻¹ * p⁻¹ = z := by
  have hmem : w * p * w⁻¹ * p⁻¹ ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers z :=
    (B.F_c1 w hwF (w_pow4 H hww)).2 p (B.le_Rd hp)
  have hP₁ : w * p * w⁻¹ * p⁻¹ ∈ P₁ :=
    P₁.mul_mem (B.P1_normalS H A w (H.base.T_le_S (B.F_le hwF)) p hp) (P₁.inv_mem hp)
  have hmem' : w * p * w⁻¹ * p⁻¹ ∈ omegaZ T := by
    rw [H.base.Z_eq H.hz A.card4]; exact hmem
  rcases H.base.Z_cases H.hz A.card4 _ hmem' with e | e | e | e
  · exact Or.inl e
  · exfalso; apply B.x_not_mem_P1 H; rw [← e]; exact hP₁
  · exact Or.inr e
  · exfalso
    apply B.x_not_mem_P1 H
    rw [e] at hP₁
    have : x = (x * z) * z⁻¹ := by group
    rw [this]
    exact P₁.mul_mem hP₁ (P₁.inv_mem (B.z_mem_P1 H))

theorem w_not_cent (H : Hyp129 G x z S T P Q Rd F) (A : Ph0 G x z S T P a)
    (B : Ph1 G x z T P Rd a V P₁ F') {w : G} (hwF : w ∈ F') (hww : w * w = x)
    (h8 : 8 ≤ Nat.card P) : ¬ ∀ p ∈ P₁, w * p = p * w := by
  intro hc
  have hwT : w ∈ T := B.F_le hwF
  have hw'T : a⁻¹ * w * a ∈ T := by
    rw [A.a_norm]
    have : a * (a⁻¹ * w * a) * a⁻¹ = w := by group
    rw [this]; exact hwT
  have hw'P : ∀ p ∈ P, (a⁻¹ * w * a) * p = p * (a⁻¹ * w * a) := by
    intro p hp
    have hap : a * p * a⁻¹ ∈ P₁ := B.P1_normalS H A a A.a_mem p (B.P_le hp)
    have h1 := hc _ hap
    calc (a⁻¹ * w * a) * p = a⁻¹ * (w * (a * p * a⁻¹)) * a := by group
      _ = a⁻¹ * ((a * p * a⁻¹) * w) * a := by rw [h1]
      _ = p * (a⁻¹ * w * a) := by group
  obtain ⟨u, hu, w₂, hw₂F, hw₂4, hw'⟩ := B.F_c4 h8 _ hw'T hw'P
  obtain ⟨hu2, huc⟩ := H.Z0_central hu
  have hw₂T : w₂ ∈ T := B.F_le hw₂F
  have hsq : (a⁻¹ * w * a) * (a⁻¹ * w * a) = w₂ * w₂ := by
    rw [hw']
    calc u * w₂ * (u * w₂) = u * (w₂ * u) * w₂ := by group
      _ = u * (u * w₂) * w₂ := by rw [huc w₂ hw₂T]
      _ = (u * u) * (w₂ * w₂) := by group
      _ = w₂ * w₂ := by rw [hu2, one_mul]
  have hsq2 : (a⁻¹ * w * a) * (a⁻¹ * w * a) = x * z := by
    calc (a⁻¹ * w * a) * (a⁻¹ * w * a) = a⁻¹ * (w * w) * a := by group
      _ = x * z := by rw [hww, A.xa']
  have hw₂w₂ : (w₂ * w₂) * (w₂ * w₂) = 1 := by
    rw [← pow_four_eq]; exact hw₂4
  rcases B.F'_inv H (Subgroup.mul_mem _ hw₂F hw₂F) hw₂w₂ with h1 | h1
  ·
    rw [hsq, h1] at hsq2
    have : x = z := by
      have h2 : x * z = 1 := hsq2.symm
      rw [mul_eq_one_iff_eq_inv] at h2
      rw [h2]; exact inv_eq_of_mul_eq_one_right H.hz.z_sq
    exact H.base.x_ne_z H.hz this
  · rw [hsq, h1] at hsq2
    have : z = 1 := by
      have h2 : x * 1 = x * z := by rw [mul_one]; exact hsq2
      exact (mul_left_cancel h2).symm
    exact H.hz.z_ne_one this

theorem cent_P1_le (H : Hyp129 G x z S T P Q Rd F) (A : Ph0 G x z S T P a)
    (B : Ph1 G x z T P Rd a V P₁ F') (hF : F' ≠ Subgroup.zpowers x) {t : G} (htT : t ∈ T)
    (htc : ∀ p ∈ P₁, t * p = p * t) : t ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers z := by
  have h8 : 8 ≤ Nat.card P := by
    rcases H.card_P_four_or_ge8 with h4 | h8
    · exact absurd (B.F_c3 h4) hF
    · exact h8
  obtain ⟨u, hu, w₂, hw₂F, hw₂4, hw'⟩ := B.F_c4 h8 t htT (fun p hp => htc p (B.P_le hp))
  obtain ⟨hu2, huc⟩ := H.Z0_central hu
  have hw₂T : w₂ ∈ T := B.F_le hw₂F
  have hw₂c : ∀ p ∈ P₁, w₂ * p = p * w₂ := by
    intro p hp
    have h1 := htc p hp
    rw [hw'] at h1
    have hpT : p ∈ T := B.P1_le_T H hp
    have h2 : u * (w₂ * p) = u * (p * w₂) := by
      calc u * (w₂ * p) = (u * w₂) * p := by group
        _ = p * (u * w₂) := h1
        _ = (p * u) * w₂ := by group
        _ = (u * p) * w₂ := by rw [(huc p hpT).symm]
        _ = u * (p * w₂) := by group
    exact mul_left_cancel h2
  have hw₂w₂ : (w₂ * w₂) * (w₂ * w₂) = 1 := by
    rw [← pow_four_eq]; exact hw₂4
  rcases B.F'_inv H (Subgroup.mul_mem _ hw₂F hw₂F) hw₂w₂ with h1 | h1
  ·
    have hw₂inv : w₂ = 1 ∨ w₂ = x := B.F'_inv H hw₂F h1
    rw [hw']
    rcases hw₂inv with e | e
    · rw [e, mul_one]; exact hu
    · rw [e]
      exact Subgroup.mul_mem _ hu (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))
  · exact absurd hw₂c (B.w_not_cent H A hw₂F h1 h8)

theorem cent_S_P1_le (H : Hyp129 G x z S T P Q Rd F) (A : Ph0 G x z S T P a)
    (B : Ph1 G x z T P Rd a V P₁ F') (hF : F' ≠ Subgroup.zpowers x) {s : G} (hsS : s ∈ S)
    (hsc : ∀ p ∈ P₁, s * p = p * s) : s ∈ Rd := by
  by_cases hsT : s ∈ T
  · exact H.Z0_le_Rd (B.cent_P1_le H A hF hsT hsc)
  · exfalso
    have hnorm : s ∈ Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G) := by
      apply mem_normalizer_of_forward
      intro e he
      have hle : V ⊔ Subgroup.zpowers x ≤ Hconj s (V ⊔ Subgroup.zpowers x) := by
        refine sup_le (fun v hv => ?_) ((Subgroup.zpowers_le).2 ?_)
        · rw [mem_Hconj]
          have h1 := hsc v (B.P_le (B.V_le hv))
          have : s * v * s⁻¹ = v := by rw [h1]; group
          rw [this]; exact Subgroup.mem_sup_left hv
        · rw [mem_Hconj, Ph0.sx H A hsS hsT]
          exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
            (Subgroup.mem_sup_left B.z_V)
      exact mem_Hconj.1 (hle he)
    exact A.K1 V B.V_le B.V_four s hsS hsT hnorm

theorem S_comm_Rd (H : Hyp129 G x z S T P Q Rd F) (A : Ph0 G x z S T P a)
    (B : Ph1 G x z T P Rd a V P₁ F') (hF : F' ≠ Subgroup.zpowers x) :
    ∀ g ∈ S, ∀ k ∈ S, g * k * g⁻¹ * k⁻¹ ∈ Rd := by
  intro g hg k hk
  obtain ⟨ρ, s, j, hD, _⟩ := B.dih_data H
  obtain ⟨d, hdP, hcomm⟩ := hD.comm_inner (B.P1_conj_iff H A hg) (B.P1_conj_iff H A hk)
  have hdS : d ∈ S := H.base.T_le_S (B.P1_le_T H hdP)
  have hκS : g * k * g⁻¹ * k⁻¹ ∈ S :=
    S.mul_mem (S.mul_mem (S.mul_mem hg hk) (S.inv_mem hg)) (S.inv_mem hk)
  have hcent : ∀ p ∈ P₁, (d⁻¹ * (g * k * g⁻¹ * k⁻¹)) * p = p * (d⁻¹ * (g * k * g⁻¹ * k⁻¹)) := by
    intro p hp
    have h1 := hcomm p hp
    calc d⁻¹ * (g * k * g⁻¹ * k⁻¹) * p
        = d⁻¹ * ((g * k * g⁻¹ * k⁻¹) * p * (g * k * g⁻¹ * k⁻¹)⁻¹) * (g * k * g⁻¹ * k⁻¹) := by group
      _ = d⁻¹ * (d * p * d⁻¹) * (g * k * g⁻¹ * k⁻¹) := by rw [h1]
      _ = p * (d⁻¹ * (g * k * g⁻¹ * k⁻¹)) := by group
  have hk' : d⁻¹ * (g * k * g⁻¹ * k⁻¹) ∈ Rd :=
    B.cent_S_P1_le H A hF (S.mul_mem (S.inv_mem hdS) hκS) hcent
  have e : g * k * g⁻¹ * k⁻¹ = d * (d⁻¹ * (g * k * g⁻¹ * k⁻¹)) := by group
  rw [e]
  exact Rd.mul_mem (B.le_Rd hdP) hk'

theorem noSq_Rd (H : Hyp129 G x z S T P Q Rd F) (A : Ph0 G x z S T P a)
    (B : Ph1 G x z T P Rd a V P₁ F') {y : G} (hyRd : y ∈ Rd) {g : G}
    (hg : g⁻¹ * x * g = y * y) : False := by
  rw [← B.sup_x] at hyRd
  obtain ⟨p, hp, c, hc, hyp⟩ := mem_sup_of_commute
    (comm_zpowers (fun u hu => H.base.x_central u (B.P1_le_T H hu))) hyRd
  rcases zpowers_sq_cases H.base.x_sq hc with h1 | h1
  · rw [h1, mul_one] at hyp
    exact B.x_conj_not_P1 H A (y := y * y) (by rw [hyp]; exact P₁.mul_mem hp hp) ⟨g, hg⟩
  · rw [h1] at hyp
    have hpx : x * p = p * x := H.base.x_central p (B.P1_le_T H hp)
    have e : y * y = p * p := by
      calc y * y = (p * x) * (p * x) := by rw [hyp]
        _ = p * (x * p) * x := by group
        _ = p * (p * x) * x := by rw [hpx]
        _ = p * p * (x * x) := by group
        _ = p * p := by rw [H.base.x_sq, mul_one]
    exact B.x_conj_not_P1 H A (y := y * y) (by rw [e]; exact P₁.mul_mem hp hp) ⟨g, hg⟩

theorem noSq_ST (H : Hyp129 G x z S T P Q Rd F) (A : Ph0 G x z S T P a)
    (B : Ph1 G x z T P Rd a V P₁ F') {y : G} (hyS : y ∈ S) (hyT : y ∉ T) {g : G}
    (hg : g⁻¹ * x * g = y * y) : False := by
  have hy2T : y * y ∈ T := by
    have := H.coset_eq (S.inv_mem hyS) hyS (fun h => hyT (by simpa using T.inv_mem h)) hyT
    simpa using this
  have hy2sq : (y * y) * (y * y) = 1 := by
    rw [← hg]
    calc g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
      _ = 1 := by rw [H.base.x_sq]; group
  have hy₂Rd : y * y ∈ Rd := H.h127.omega1_le (Subgroup.subset_closure ⟨hy2T, hy2sq⟩)
  rw [← B.sup_x] at hy₂Rd
  obtain ⟨p, hp, c, hc, hyp⟩ := mem_sup_of_commute
    (comm_zpowers (fun u hu => H.base.x_central u (B.P1_le_T H hu))) hy₂Rd
  rcases zpowers_sq_cases H.base.x_sq hc with h1 | h1
  · rw [h1, mul_one] at hyp
    exact B.x_conj_not_P1 H A (y := y * y) (by rw [hyp]; exact hp) ⟨g, hg⟩
  · rw [h1] at hyp
    have hpT : p ∈ T := B.P1_le_T H hp
    have hpx : x * p = p * x := H.base.x_central p hpT
    have hp2 : p * p = 1 := by
      have e : (y * y) * (y * y) = p * p := by
        calc (y * y) * (y * y) = (p * x) * (p * x) := by rw [hyp]
          _ = p * (x * p) * x := by group
          _ = p * (p * x) * x := by rw [hpx]
          _ = p * p * (x * x) := by group
          _ = p * p := by rw [H.base.x_sq, mul_one]
      rw [← e]; exact hy2sq
    have hcomm : y * (p * x) * y⁻¹ = p * x := by
      rw [← hyp]; group
    have hxy := Ph0.sx H A hyS hyT
    have hqT : y * p * y⁻¹ ∈ T := H.T_normal_S y hyS p hpT
    have hqz : y * p * y⁻¹ = p * z := by
      have h2 : (y * p * y⁻¹) * (x * z) = p * x := by
        rw [← hxy]
        calc y * p * y⁻¹ * (y * x * y⁻¹) = y * (p * x) * y⁻¹ := by group
          _ = p * x := hcomm
      have hxzc : x * z = z * x := (H.hz.z_central x H.base.x_mem_T).symm
      have h3 : (y * p * y⁻¹) * z * x = p * x := by
        calc (y * p * y⁻¹) * z * x = (y * p * y⁻¹) * (z * x) := by group
          _ = (y * p * y⁻¹) * (x * z) := by rw [hxzc]
          _ = p * x := h2
      have h4 : (y * p * y⁻¹) * z = p := mul_right_cancel h3
      calc y * p * y⁻¹ = (y * p * y⁻¹) * z * z := by
            rw [mul_assoc (y * p * y⁻¹) z z, H.hz.z_sq, mul_one]
        _ = p * z := by rw [h4]
    by_cases hp1 : p = 1
    · apply H.hz.z_ne_one
      rw [hp1] at hqz
      simpa using hqz.symm
    by_cases hpz : p = z
    · apply H.hz.z_ne_one
      rw [hpz, Ph0.sz H A y hyS] at hqz
      have : z = z * z := hqz
      rw [H.hz.z_sq] at this
      exact this
    exact (B.K1pp H A hp hp2 hp1 hpz y hyS hyT).2 hqz

end Ph1

end

end CFSG.GH74.GLS.Stage1.Thm6.Sec12b
