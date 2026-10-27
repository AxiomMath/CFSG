module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKGG

open Subgroup
open scoped Pointwise

theorem exists_sylow_two_fixed {K : Type*} [Group K] [Finite K] {S : Subgroup (MulAut K)}
    (hS : IsPGroup 2 ↥S) :
    ∃ P : Sylow 2 K, ∀ σ ∈ S, ∀ x : K, σ x ∈ (P : Subgroup K) ↔ x ∈ (P : Subgroup K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (Sylow 2 K) := inferInstance
  have h1 := hS.card_modEq_card_fixedPoints (α := Sylow 2 K)
  have h2 := card_sylow_modEq_one 2 K
  have h3 : Nat.card (MulAction.fixedPoints ↥S (Sylow 2 K)) ≡ 1 [MOD 2] := h1.symm.trans h2
  have hne : Nat.card (MulAction.fixedPoints ↥S (Sylow 2 K)) ≠ 0 := by
    intro h0
    rw [h0] at h3
    exact absurd (Nat.modEq_zero_iff_dvd.mp h3.symm) (by norm_num)
  have hpos : 0 < Nat.card (MulAction.fixedPoints ↥S (Sylow 2 K)) := Nat.pos_of_ne_zero hne
  obtain ⟨⟨P, hP⟩⟩ := Nat.card_pos_iff.mp hpos |>.1
  refine ⟨P, fun σ hσ x => ?_⟩
  have hfix : (⟨σ, hσ⟩ : ↥S) • P = P := hP ⟨σ, hσ⟩
  have hsub : (σ • (P : Subgroup K)) = (P : Subgroup K) := by
    have := congrArg (fun Q : Sylow 2 K => (Q : Subgroup K)) hfix
    simpa [Sylow.pointwise_smul_def] using this
  have hmem : σ x ∈ (P : Subgroup K) ↔ x ∈ (P : Subgroup K) := by
    conv_lhs => rw [← hsub]
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp
  exact hmem

theorem commute_of_inf_ker_eq_bot {A Q : Type*} [Group A] [Group Q] (hQ : ∀ x y : Q, x * y = y * x)
    (Θ : A →* Q) {S : Subgroup A} (hS : S ⊓ Θ.ker = ⊥) :
    (∀ s ∈ S, ∀ t ∈ S, s * t = t * s) ∧
      ∀ b ∈ Subgroup.normalizer (S : Set A), ∀ s ∈ S, b * s = s * b := by
  have hker : ∀ x y : A, x * y * x⁻¹ * y⁻¹ ∈ Θ.ker := fun x y => by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [hQ (Θ x) (Θ y)]
    group
  refine ⟨fun s hs t ht => ?_, fun b hb s hs => ?_⟩
  · have hmem : s * t * s⁻¹ * t⁻¹ ∈ S ⊓ Θ.ker :=
      ⟨S.mul_mem (S.mul_mem (S.mul_mem hs ht) (S.inv_mem hs)) (S.inv_mem ht), hker s t⟩
    rw [hS, Subgroup.mem_bot] at hmem
    calc s * t = s * t * s⁻¹ * t⁻¹ * (t * s) := by group
      _ = t * s := by rw [hmem, one_mul]
  · have hbs : b * s * b⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hb s).mp hs
    have hmem : b * s * b⁻¹ * s⁻¹ ∈ S ⊓ Θ.ker :=
      ⟨S.mul_mem hbs (S.inv_mem hs), by simpa [mul_assoc] using hker b s⟩
    rw [hS, Subgroup.mem_bot] at hmem
    calc b * s = b * s * b⁻¹ * s⁻¹ * (s * b) := by group
      _ = s * b := by rw [hmem, one_mul]

private theorem zmod_two_mult_cases (e : Multiplicative (ZMod 2)) :
    e = 1 ∨ e = Multiplicative.ofAdd (1 : ZMod 2) := by
  have h2 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases h2 (Multiplicative.toAdd e) with h | h
  · left
    apply Multiplicative.toAdd.injective
    simpa using h
  · right
    apply Multiplicative.toAdd.injective
    simpa using h

private theorem ofAdd_one_mul_self :
    (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd (1 : ZMod 2) = 1 := by
  rw [← ofAdd_add]
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rw [h11]
  exact ofAdd_zero

theorem exists_involutions_of_types {A C : Type*} [Group A] [Group C] [IsCyclic C]
    (Θ : A →* C × Multiplicative (ZMod 2)) {S : Subgroup A} (hS : IsPGroup 2 ↥S)
    (hnc : ¬ IsCyclic ↥S) (hinj : S ⊓ Θ.ker = ⊥) :
    ∃ a ∈ S, ∃ b ∈ S, a * a = 1 ∧ b * b = 1 ∧ (Θ a).1 ≠ 1 ∧ (Θ a).2 = 1 ∧
      Θ b = (1, Multiplicative.ofAdd (1 : ZMod 2)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : ∀ x ∈ S, Θ x = 1 → x = 1 := fun x hx h => by
    have : x ∈ S ⊓ Θ.ker := ⟨hx, h⟩
    rw [hinj] at this
    exact this
  have ht : ∃ t ∈ S, Θ t = (1, Multiplicative.ofAdd (1 : ZMod 2)) := by
    by_contra hno
    push Not at hno
    apply hnc
    refine isCyclic_of_injective
      ((MonoidHom.fst C (Multiplicative (ZMod 2))).comp (Θ.comp S.subtype)) ?_
    intro x y hxy
    have hz : (x⁻¹ * y : ↥S) ∈ (⊤ : Subgroup ↥S) := trivial
    have hzS : ((x⁻¹ * y : ↥S) : A) ∈ S := (x⁻¹ * y).2
    have hfst : (Θ ((x⁻¹ * y : ↥S) : A)).1 = 1 := by
      have : (Θ (x : A)).1 = (Θ (y : A)).1 := hxy
      simp [map_mul, map_inv, this]
    rcases zmod_two_mult_cases (Θ ((x⁻¹ * y : ↥S) : A)).2 with h2 | h2
    · have hΘ1 : Θ ((x⁻¹ * y : ↥S) : A) = 1 := by
        refine Prod.ext hfst ?_
        simpa using h2
      have := hker _ hzS hΘ1
      have hxy' : x⁻¹ * y = 1 := Subtype.ext this
      exact inv_mul_eq_one.mp hxy'
    · exact absurd (Prod.ext hfst h2) (fun h => hno _ hzS h)
  obtain ⟨t, htS, hΘt⟩ := ht
  have hs0 : ∃ s ∈ S, (Θ s).1 ≠ 1 := by
    by_contra hno
    push Not at hno
    apply hnc
    refine isCyclic_of_injective
      ((MonoidHom.snd C (Multiplicative (ZMod 2))).comp (Θ.comp S.subtype)) ?_
    intro x y hxy
    have hzS : ((x⁻¹ * y : ↥S) : A) ∈ S := (x⁻¹ * y).2
    have hsnd : (Θ ((x⁻¹ * y : ↥S) : A)).2 = 1 := by
      have : (Θ (x : A)).2 = (Θ (y : A)).2 := hxy
      simp [map_mul, map_inv, this]
    have hfst : (Θ ((x⁻¹ * y : ↥S) : A)).1 = 1 := hno _ hzS
    have := hker _ hzS (Prod.ext hfst hsnd)
    exact inv_mul_eq_one.mp (Subtype.ext this)
  obtain ⟨s₀, hs₀S, hs₀⟩ := hs0
  have hs1 : ∃ s ∈ S, (Θ s).1 ≠ 1 ∧ (Θ s).2 = 1 := by
    rcases zmod_two_mult_cases (Θ s₀).2 with h2 | h2
    · exact ⟨s₀, hs₀S, hs₀, h2⟩
    · refine ⟨s₀ * t, S.mul_mem hs₀S htS, ?_, ?_⟩
      · rw [map_mul, hΘt]
        simpa using hs₀
      · rw [map_mul, hΘt, Prod.snd_mul, h2]
        exact ofAdd_one_mul_self
  obtain ⟨s₁, hs₁S, hs₁1, hs₁2⟩ := hs1
  have hs₁ne : s₁ ≠ 1 := fun h => hs₁1 (by rw [h, map_one]; rfl)
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hS) ⟨s₁, hs₁S⟩
  have hm' : orderOf s₁ = 2 ^ m := by
    simpa [Subgroup.orderOf_mk] using hm
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · exfalso
      rw [h0, pow_zero, orderOf_eq_one_iff] at hm'
      exact hs₁ne hm'
    · exact h0
  set a := s₁ ^ (2 ^ (m - 1)) with ha
  have hord : orderOf a = 2 := by
    have hdvd : 2 ^ (m - 1) ∣ orderOf s₁ := by
      rw [hm']
      exact pow_dvd_pow 2 (by omega)
    rw [ha, orderOf_pow_of_dvd (by positivity) hdvd, hm']
    have : 2 ^ m = 2 * 2 ^ (m - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [this]
    exact Nat.mul_div_cancel _ (by positivity)
  have haS : a ∈ S := S.pow_mem hs₁S _
  have haa : a * a = 1 := by
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hord])
  have hΘa : Θ a = (Θ s₁) ^ (2 ^ (m - 1)) := by rw [ha, map_pow]
  have hΘa2 : (Θ a).2 = 1 := by rw [hΘa, Prod.pow_snd, hs₁2, one_pow]
  have hΘa1 : (Θ a).1 ≠ 1 := by
    intro h1
    have hΘ1 : Θ a = 1 := Prod.ext h1 hΘa2
    have := hker a haS hΘ1
    rw [this, orderOf_one] at hord
    omega
  refine ⟨a, haS, t, htS, haa, ?_, hΘa1, hΘa2, hΘt⟩
  have htt : Θ (t * t) = 1 := by
    rw [map_mul, hΘt]
    refine Prod.ext (by simp) ?_
    exact ofAdd_one_mul_self
  exact hker _ (S.mul_mem htS htS) htt

theorem cocycle_two_step {Γ : Type*} [Group Γ] (α : MulAut Γ) (hα : ∀ x, α (α x) = x)
    {H H' : Subgroup Γ} (hH' : H' ≤ H)
    (hbase : ∀ n ∈ H', n * α n = 1 → ∃ m ∈ H', n = m * (α m)⁻¹)
    (hquot : ∀ g ∈ H, g * α g = 1 → ∃ w ∈ H, w⁻¹ * g * α w ∈ H') :
    ∀ g ∈ H, g * α g = 1 → ∃ w ∈ H, g = w * (α w)⁻¹ := by
  intro g hg hcocycle
  obtain ⟨w₁, hw₁, hn⟩ := hquot g hg hcocycle
  set n := w₁⁻¹ * g * α w₁ with hndef
  have hn1 : n * α n = 1 := by
    have : α n = (α w₁)⁻¹ * α g * w₁ := by
      rw [hndef, map_mul, map_mul, map_inv, hα]
    rw [this, hndef]
    calc w₁⁻¹ * g * α w₁ * ((α w₁)⁻¹ * α g * w₁) = w₁⁻¹ * (g * α g) * w₁ := by group
      _ = 1 := by rw [hcocycle]; group
  obtain ⟨m, hm, hmn⟩ := hbase n hn hn1
  refine ⟨w₁ * m, H.mul_mem hw₁ (hH' hm), ?_⟩
  have hg' : g = w₁ * n * (α w₁)⁻¹ := by
    rw [hndef]
    group
  rw [hg', hmn, map_mul]
  group

theorem exists_conj_into_maximal_two {G : Type*} [Group G] [Finite G] {H T : Subgroup G}
    (hTH : T ≤ H) (hT : IsPGroup 2 ↥T)
    (hmax : ∀ P : Subgroup G, IsPGroup 2 ↥P → T ≤ P → P ≤ H → P ≤ T)
    {h : G} (hh : h ∈ H) {m : ℕ} (hhm : h ^ (2 ^ m) = 1) :
    ∃ x ∈ H, x⁻¹ * h * x ∈ T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT' : IsPGroup 2 ↥(T.subgroupOf H) := hT.comap_subtype
  let P₀ : Sylow 2 ↥H :=
    { toSubgroup := T.subgroupOf H
      isPGroup' := hT'
      is_maximal' := fun {Q} hQ hle => by
        have hQ' : IsPGroup 2 ↥(Q.map H.subtype) := hQ.map H.subtype
        have hTQ : T ≤ Q.map H.subtype := by
          intro x hx
          exact ⟨⟨x, hTH hx⟩, hle (by simpa [Subgroup.mem_subgroupOf] using hx), rfl⟩
        have hQH : Q.map H.subtype ≤ H := by
          rintro _ ⟨y, -, rfl⟩
          exact y.2
        have hQT := hmax _ hQ' hTQ hQH
        refine le_antisymm (fun y hy => ?_) hle
        have : (y : G) ∈ T := hQT ⟨y, hy, rfl⟩
        simpa [Subgroup.mem_subgroupOf] using this }
  let h' : ↥H := ⟨h, hh⟩
  have hh' : h' ^ (2 ^ m) = 1 := Subtype.ext hhm
  have hzp : IsPGroup 2 ↥(Subgroup.zpowers h') := by
    apply IsPGroup.of_card_dvd_pow (n := m)
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hh'
  obtain ⟨Q, hQ⟩ := hzp.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq ↥H P₀ Q
  have hmem : h' ∈ (Q : Subgroup ↥H) := hQ (Subgroup.mem_zpowers h')
  rw [← hx, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hmem
  refine ⟨x, x.2, ?_⟩
  have : (MulAut.conj x)⁻¹ • h' ∈ (P₀ : Subgroup ↥H) := hmem
  have h2 : (x⁻¹ * h' * x : ↥H) ∈ T.subgroupOf H := by
    simpa [MulAut.conj_apply, mul_assoc] using this
  simpa [Subgroup.mem_subgroupOf] using h2

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKGG

