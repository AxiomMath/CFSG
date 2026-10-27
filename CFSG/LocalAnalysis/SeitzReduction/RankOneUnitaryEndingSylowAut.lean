module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingSylowField
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingFactor

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup
open scoped commutatorElement

namespace U3RootCoords

variable {G : Type*} [Group G] {E : Type*} [Field E] {T₁ : Subgroup G} {σ : E →+* E}
  {u v : G → E}

theorem v_one_eq_zero (hc : U3RootCoords T₁ σ u v) : v 1 = 0 := by
  have h := hc.mul_v 1 (one_mem _) 1 (one_mem _)
  rw [mul_one, hc.u_one, zero_mul, sub_zero] at h
  linear_combination -h

theorem eq_one_of_u_eq_zero_of_v_eq_zero (hc : U3RootCoords T₁ σ u v) {y : G} (hy : y ∈ T₁)
    (hu : u y = 0) (hv : v y = 0) : y = 1 :=
  hc.inj y hy 1 (one_mem _) (by rw [hu, hc.u_one]) (by rw [hv, hc.v_one_eq_zero])

theorem sq_eq_one_of_u_eq_zero [CharP E 2] (hc : U3RootCoords T₁ σ u v) {y : G} (hy : y ∈ T₁)
    (hu : u y = 0) : y ^ 2 = 1 := by
  obtain ⟨h1, h2⟩ := hc.sq hy
  refine hc.eq_one_of_u_eq_zero_of_v_eq_zero (pow_mem hy 2) h1 ?_
  rw [h2, hu, zero_mul]

theorem comm_of_u_eq_zero (hc : U3RootCoords T₁ σ u v) {y : G} (hy : y ∈ T₁) (hu : u y = 0)
    {z : G} (hz : z ∈ T₁) : y * z = z * y := by
  rw [hc.commute_iff hy hz, hu, map_zero, zero_mul, mul_zero]

theorem u_eq_zero_of_comm (hc : U3RootCoords T₁ σ u v) (hσ : ∃ c : E, σ c ≠ c) {y : G}
    (hy : y ∈ T₁) (hcomm : ∀ z ∈ T₁, y * z = z * y) : u y = 0 := by
  by_contra ha
  obtain ⟨c, hcσ⟩ := hσ
  obtain ⟨z, hz, hzu⟩ := hc.u_surj (u y * c)
  have h := (hc.commute_iff hy hz).mp (hcomm z hz)
  rw [hzu, map_mul] at h
  have hσa : σ (u y) ≠ 0 := (map_ne_zero σ).mpr ha
  apply hcσ
  have h' : (u y * σ (u y)) * σ c = (u y * σ (u y)) * c := by linear_combination h
  exact mul_left_cancel₀ (mul_ne_zero ha hσa) h'

theorem of_partner (hc : U3RootCoords T₁ σ u v) {U Y Y' : Subgroup G} {t : G} (htt : t * t = 1)
    (hYU : Y ⊔ Y' = U) (hinf : Y ⊓ Y' = ⊥) (hcomm : ∀ a ∈ Y, ∀ b ∈ Y', a * b = b * a)
    (ht : ∀ a ∈ Y, t * a * t⁻¹ ∈ Y') (ht' : ∀ b ∈ Y', t * b * t⁻¹ ∈ Y)
    (hCt : ∀ x ∈ U, x * t = t * x → x ∈ T₁) (hT₁ : ∀ x ∈ T₁, x ∈ U ∧ x * t = t * x) :
    U3RootCoords Y σ (fun g => u (g * (t * g * t⁻¹))) (fun g => v (g * (t * g * t⁻¹))) := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hYle : Y ≤ U := hYU ▸ le_sup_left
  have hY'le : Y' ≤ U := hYU ▸ le_sup_right
  have hφT : ∀ x ∈ Y, x * (t * x * t⁻¹) ∈ T₁ := by
    intro x hx
    refine hCt _ (mul_mem (hYle hx) (hY'le (ht x hx))) ?_
    have hxx : x * (t * x * t⁻¹) = (t * x * t⁻¹) * x := hcomm x hx _ (ht x hx)
    calc x * (t * x * t⁻¹) * t = (t * x * t⁻¹) * x * t := by rw [hxx]
      _ = t * x * (t⁻¹ * x * t) := by group
      _ = t * x * (t * x * t⁻¹) := by rw [htinv]
      _ = t * (x * (t * x * t⁻¹)) := by group
  have hφmul : ∀ x ∈ Y, ∀ x' ∈ Y, x * x' * (t * (x * x') * t⁻¹) =
      x * (t * x * t⁻¹) * (x' * (t * x' * t⁻¹)) := by
    intro x hx x' hx'
    have h1 : x' * (t * x * t⁻¹) = (t * x * t⁻¹) * x' := hcomm x' hx' _ (ht x hx)
    calc x * x' * (t * (x * x') * t⁻¹) = x * (x' * (t * x * t⁻¹)) * (t * x' * t⁻¹) := by group
      _ = x * ((t * x * t⁻¹) * x') * (t * x' * t⁻¹) := by rw [h1]
      _ = x * (t * x * t⁻¹) * (x' * (t * x' * t⁻¹)) := by group
  have hφinj : ∀ x ∈ Y, ∀ x' ∈ Y, x * (t * x * t⁻¹) = x' * (t * x' * t⁻¹) → x = x' :=
    fun x hx x' hx' h =>
      (eq_and_eq_of_mul_eq_mul_of_inf_eq_bot hinf hx hx' (ht x hx) (ht x' hx') h).1
  have hφsurj : ∀ z ∈ T₁, ∃ y ∈ Y, y * (t * y * t⁻¹) = z := by
    intro z hz
    obtain ⟨hzU, hzt⟩ := hT₁ z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_eq_of_mem_sup_of_commute hcomm (hYU ▸ hzU)
    have e : (t * b * t⁻¹) * (t * a * t⁻¹) = a * b := by
      calc (t * b * t⁻¹) * (t * a * t⁻¹) = (t * a * t⁻¹) * (t * b * t⁻¹) :=
            hcomm _ (ht' b hb) _ (ht a ha)
        _ = t * (a * b) * t⁻¹ := by group
        _ = a * b := by rw [← hzt]; group
    obtain ⟨e1, e2⟩ := eq_and_eq_of_mul_eq_mul_of_inf_eq_bot hinf (ht' b hb) ha (ht a ha) hb e
    exact ⟨a, ha, by rw [← e2]⟩
  refine ⟨fun y hy => hc.rel _ (hφT y hy), fun y hy y' hy' => ?_, fun y hy y' hy' => ?_,
    fun y hy y' hy' h1 h2 => hφinj y hy y' hy' (hc.inj _ (hφT y hy) _ (hφT y' hy') h1 h2),
    fun a b hab => ?_, fun a => ?_⟩
  · rw [hφmul y hy y' hy', hc.mul_u _ (hφT y hy) _ (hφT y' hy')]
  · rw [hφmul y hy y' hy', hc.mul_v _ (hφT y hy) _ (hφT y' hy')]
  · obtain ⟨z, hz, hzu, hzv⟩ := hc.surj a b hab
    obtain ⟨y, hy, rfl⟩ := hφsurj z hz
    exact ⟨y, hy, hzu, hzv⟩
  · obtain ⟨z, hz, hzu⟩ := hc.u_surj a
    obtain ⟨y, hy, rfl⟩ := hφsurj z hz
    exact ⟨y, hy, hzu⟩

theorem apply_sq_eq [CharP E 2] [Finite E] (hc : U3RootCoords T₁ σ u v) {q : ℕ}
    (hσq : ∀ x, σ x = x ^ q) (hE : Nat.card E = q ^ 2) (hF : Nat.card {x : E // σ x = x} = q)
    (α : G → G) (hαT : ∀ y ∈ T₁, α y ∈ T₁)
    (hαmul : ∀ y ∈ T₁, ∀ y' ∈ T₁, α (y * y') = α y * α y')
    (hαα : ∀ y ∈ T₁, u (α (α y)) = u y) {y : G} (hy : y ∈ T₁) : α (y ^ 2) = y ^ 2 := by
  have hσ := NormInvolution.exists_sigma_ne σ hE hF
  have hαA : ∀ z ∈ T₁, u z = 0 → u (α z) = 0 := by
    intro z hz hzu
    refine hc.u_eq_zero_of_comm hσ (hαT z hz) fun w hw => ?_
    have hw2 : α (α w) ∈ T₁ := hαT _ (hαT w hw)
    have hk : (α (α w))⁻¹ * w ∈ T₁ := mul_mem (inv_mem hw2) hw
    have hku : u ((α (α w))⁻¹ * w) = 0 := by rw [hc.u_mul_inv hw2 hw, hαα w hw, sub_self]
    have h1 : α z * α (α w) = α (α w) * α z := by
      rw [← hαmul z hz _ (hαT w hw), ← hαmul _ (hαT w hw) z hz,
        hc.comm_of_u_eq_zero hz hzu (hαT w hw)]
    have h2 : α z * ((α (α w))⁻¹ * w) = ((α (α w))⁻¹ * w) * α z :=
      (hc.comm_of_u_eq_zero hk hku (hαT z hz)).symm
    calc α z * w = α z * α (α w) * ((α (α w))⁻¹ * w) := by group
      _ = α (α w) * α z * ((α (α w))⁻¹ * w) := by rw [h1]
      _ = α (α w) * (α z * ((α (α w))⁻¹ * w)) := by group
      _ = α (α w) * (((α (α w))⁻¹ * w) * α z) := by rw [h2]
      _ = w * α z := by group
  choose s hsT hsu using hc.u_surj
  have hφu : ∀ w ∈ T₁, u (α w) = u (α (s (u w))) := by
    intro w hw
    have hk : (s (u w))⁻¹ * w ∈ T₁ := mul_mem (inv_mem (hsT _)) hw
    have hku : u ((s (u w))⁻¹ * w) = 0 := by rw [hc.u_mul_inv (hsT _) hw, hsu, sub_self]
    have e : w = s (u w) * ((s (u w))⁻¹ * w) := by group
    conv_lhs => rw [e]
    rw [hαmul _ (hsT _) _ hk, hc.mul_u _ (hαT _ (hsT _)) _ (hαT _ hk), hαA _ hk hku, add_zero]
  have hφadd : ∀ a b, u (α (s (a + b))) = u (α (s a)) + u (α (s b)) := by
    intro a b
    have h1 := hφu _ (mul_mem (hsT a) (hsT b))
    rw [hc.mul_u _ (hsT a) _ (hsT b), hsu, hsu, hαmul _ (hsT a) _ (hsT b),
      hc.mul_u _ (hαT _ (hsT a)) _ (hαT _ (hsT b))] at h1
    exact h1.symm
  have hφφ : ∀ a, u (α (s (u (α (s a))))) = a := fun a =>
    (hφu _ (hαT _ (hsT a))).symm.trans ((hαα _ (hsT a)).trans (hsu a))
  have hz : ∀ b : E, ∃ z : G, σ b = b → (z ∈ T₁ ∧ u z = 0 ∧ v z = b) := by
    intro b
    by_cases hb : σ b = b
    · obtain ⟨z, hz, hzu, hzv⟩ := hc.surj 0 b (by
        rw [hb, map_zero, zero_mul, add_zero, CharTwo.add_self_eq_zero])
      exact ⟨z, fun _ => ⟨hz, hzu, hzv⟩⟩
    · exact ⟨1, fun h => absurd h hb⟩
  choose zz hzz using hz
  have hzzeq : ∀ w ∈ T₁, u w = 0 → w = zz (v w) := by
    intro w hw hwu
    obtain ⟨h1, h2, h3⟩ := hzz (v w) (hc.sigma_v_of_u_eq_zero hw hwu)
    exact hc.inj _ hw _ h1 (by rw [hwu, h2]) h3.symm
  have hχadd : ∀ a b, σ a = a → σ b = b →
      v (α (zz (a + b))) = v (α (zz a)) + v (α (zz b)) := by
    intro a b ha hb
    obtain ⟨ha1, ha2, ha3⟩ := hzz a ha
    obtain ⟨hb1, hb2, hb3⟩ := hzz b hb
    have hab : zz a * zz b ∈ T₁ := mul_mem ha1 hb1
    have habu : u (zz a * zz b) = 0 := by rw [hc.mul_u _ ha1 _ hb1, ha2, hb2, add_zero]
    have habv : v (zz a * zz b) = a + b := by rw [hc.v_mul_of_u_eq_zero ha1 hb1 ha2, ha3, hb3]
    have e : zz (a + b) = zz a * zz b := by
      have := hzzeq _ hab habu
      rw [habv] at this
      exact this.symm
    rw [e, hαmul _ ha1 _ hb1, hc.v_mul_of_u_eq_zero (hαT _ ha1) (hαT _ hb1) (hαA _ ha1 ha2)]
  have hχ : ∀ a, v (α (zz (a * σ a))) = u (α (s a)) * σ (u (α (s a))) := by
    intro a
    obtain ⟨h1, h2⟩ := hc.sq (hsT a)
    have e : zz (a * σ a) = s a ^ 2 := by
      have := hzzeq _ (pow_mem (hsT a) 2) h1
      rw [h2, hsu] at this
      exact this.symm
    rw [e, pow_two, hαmul _ (hsT a) _ (hsT a), ← pow_two]
    exact (hc.sq (hαT _ (hsT a))).2
  have hN := NormInvolution.norm_apply_eq_of_involutive σ hσq hE hF
    (fun a => u (α (s a))) (fun b => v (α (zz b))) hφadd hφφ hχadd hχ
  have hαy : α (y ^ 2) = α y ^ 2 := by rw [pow_two, hαmul _ hy _ hy, ← pow_two]
  obtain ⟨hy1, hy2⟩ := hc.sq hy
  obtain ⟨hα1, hα2⟩ := hc.sq (hαT _ hy)
  rw [hαy]
  refine hc.inj _ (pow_mem (hαT _ hy) 2) _ (pow_mem hy 2) (by rw [hα1, hy1]) ?_
  rw [hα2, hy2, hφu _ hy]
  exact hN (u y)

end U3RootCoords

section Factors

variable {G : Type*} [Group G]

theorem conj_sq_eq_of_mem_normalizer {E : Type*} [Field E] [CharP E 2] [Finite E]
    {σ : E →+* E} {q : ℕ} (hσq : ∀ x, σ x = x ^ q) (hE : Nat.card E = q ^ 2)
    (hF : Nat.card {x : E // σ x = x} = q) {U Y₁ Y₂ : Subgroup G} {u₁ v₁ u₂ v₂ : G → E}
    (hc₁ : U3RootCoords Y₁ σ u₁ v₁) (hc₂ : U3RootCoords Y₂ σ u₂ v₂) (hU : Y₁ ⊔ Y₂ = U)
    (hinf : Y₁ ⊓ Y₂ = ⊥) (hcomm : ∀ a ∈ Y₁, ∀ b ∈ Y₂, a * b = b * a) {x : G} (hxx : x * x = 1)
    (hx₁ : x ∈ normalizer ((U ⊓ centralizer (Y₂ : Set G) : Subgroup G) : Set G))
    (hx₂ : x ∈ normalizer ((U ⊓ centralizer (Y₁ : Set G) : Subgroup G) : Set G))
    {y : G} (hy : y ∈ Y₁) : x * y ^ 2 * x⁻¹ = y ^ 2 := by
  have hσ := NormInvolution.exists_sigma_ne σ hE hF
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hY₁U : Y₁ ≤ U := hU ▸ le_sup_left
  have hY₂U : Y₂ ≤ U := hU ▸ le_sup_right
  have hM₁ : ∀ g ∈ Y₁, g ∈ U ⊓ centralizer (Y₂ : Set G) := fun g hg =>
    mem_inf.mpr ⟨hY₁U hg, mem_centralizer_iff.mpr fun b hb => (hcomm g hg b hb).symm⟩
  have hxM₁ : ∀ g ∈ Y₁, x * g * x⁻¹ ∈ U ⊓ centralizer (Y₂ : Set G) := fun g hg =>
    (mem_normalizer_iff.mp hx₁ g).mp (hM₁ g hg)
  have hdec : ∀ g : G, ∃ a : G, g ∈ Y₁ → (a ∈ Y₁ ∧ a⁻¹ * (x * g * x⁻¹) ∈ Y₂) := by
    intro g
    by_cases hg : g ∈ Y₁
    · obtain ⟨a, ha, b, hb, hab⟩ :=
        exists_mul_eq_of_mem_sup_of_commute hcomm (hU ▸ (mem_inf.mp (hxM₁ g hg)).1)
      exact ⟨a, fun _ => ⟨ha, by rw [← hab, inv_mul_cancel_left]; exact hb⟩⟩
    · exact ⟨1, fun h => absurd h hg⟩
  choose α hα using hdec
  obtain ⟨β, hβdef⟩ : ∃ β : G → G, ∀ g, β g = (α g)⁻¹ * (x * g * x⁻¹) := ⟨_, fun _ => rfl⟩
  have hαY : ∀ g ∈ Y₁, α g ∈ Y₁ := fun g hg => (hα g hg).1
  have hβY : ∀ g ∈ Y₁, β g ∈ Y₂ := fun g hg => by rw [hβdef]; exact (hα g hg).2
  have hxg : ∀ g, x * g * x⁻¹ = α g * β g := fun g => by rw [hβdef]; group
  have hβC : ∀ g ∈ Y₁, ∀ b ∈ Y₂, β g * b = b * β g := by
    intro g hg b hb
    have hc1 : b * (x * g * x⁻¹) = (x * g * x⁻¹) * b :=
      mem_centralizer_iff.mp (mem_inf.mp (hxM₁ g hg)).2 b hb
    have hc2 : α g * b = b * α g := hcomm (α g) (hαY g hg) b hb
    have hc3 : (α g)⁻¹ * b = b * (α g)⁻¹ := by
      calc (α g)⁻¹ * b = (α g)⁻¹ * (b * α g) * (α g)⁻¹ := by group
        _ = (α g)⁻¹ * (α g * b) * (α g)⁻¹ := by rw [hc2]
        _ = b * (α g)⁻¹ := by group
    calc β g * b = (α g)⁻¹ * ((x * g * x⁻¹) * b) := by rw [hβdef]; group
      _ = (α g)⁻¹ * (b * (x * g * x⁻¹)) := by rw [hc1]
      _ = ((α g)⁻¹ * b) * (x * g * x⁻¹) := by group
      _ = (b * (α g)⁻¹) * (x * g * x⁻¹) := by rw [hc3]
      _ = b * β g := by rw [hβdef]; group
  have hβsq : ∀ g ∈ Y₁, β g ^ 2 = 1 := fun g hg =>
    hc₂.sq_eq_one_of_u_eq_zero (hβY g hg)
      (hc₂.u_eq_zero_of_comm hσ (hβY g hg) fun b hb => hβC g hg b hb)
  have hαmul : ∀ g ∈ Y₁, ∀ g' ∈ Y₁, α (g * g') = α g * α g' := by
    intro g hg g' hg'
    have hb : α g' * β g = β g * α g' := hcomm (α g') (hαY g' hg') _ (hβY g hg)
    have e : α (g * g') * β (g * g') = (α g * α g') * (β g * β g') := by
      calc α (g * g') * β (g * g') = x * (g * g') * x⁻¹ := (hxg _).symm
        _ = (x * g * x⁻¹) * (x * g' * x⁻¹) := by group
        _ = α g * (β g * α g') * β g' := by rw [hxg g, hxg g']; group
        _ = α g * (α g' * β g) * β g' := by rw [hb]
        _ = (α g * α g') * (β g * β g') := by group
    exact (eq_and_eq_of_mul_eq_mul_of_inf_eq_bot hinf (hαY _ (mul_mem hg hg'))
      (mul_mem (hαY g hg) (hαY g' hg')) (hβY _ (mul_mem hg hg'))
      (mul_mem (hβY g hg) (hβY g' hg')) e).1
  have hαα : ∀ g ∈ Y₁, u₁ (α (α g)) = u₁ g := by
    intro g hg
    have hβM : (β g)⁻¹ ∈ U ⊓ centralizer (Y₂ : Set G) ⊓ (U ⊓ centralizer (Y₁ : Set G)) := by
      refine inv_mem (mem_inf.mpr ⟨mem_inf.mpr ⟨hY₂U (hβY g hg), mem_centralizer_iff.mpr
        fun b hb => (hβC g hg b hb).symm⟩, mem_inf.mpr ⟨hY₂U (hβY g hg),
          mem_centralizer_iff.mpr fun a ha => hcomm a ha _ (hβY g hg)⟩⟩)
    have hc : x * (β g)⁻¹ * x⁻¹ ∈ U ⊓ centralizer (Y₁ : Set G) :=
      (mem_normalizer_iff.mp hx₂ _).mp (mem_inf.mp hβM).2
    obtain ⟨c₁, hc₁Y, c₂, hc₂', hc12⟩ :=
      exists_mul_eq_of_mem_sup_of_commute hcomm (hU ▸ (mem_inf.mp hc).1)
    have e1 : x * α g * x⁻¹ = g * (x * (β g)⁻¹ * x⁻¹) := by
      have hag : α g = x * g * x⁻¹ * (β g)⁻¹ := by rw [hxg g]; group
      rw [hag]
      calc x * (x * g * x⁻¹ * (β g)⁻¹) * x⁻¹ = (x * x) * g * x⁻¹ * (β g)⁻¹ * x⁻¹ := by group
        _ = g * (x * (β g)⁻¹ * x⁻¹) := by rw [hxx, hxinv]; group
    have e2 : α (α g) * β (α g) = (g * c₁) * c₂ := by
      rw [← hxg, e1, ← hc12]
      group
    have hgc : α (α g) = g * c₁ :=
      (eq_and_eq_of_mul_eq_mul_of_inf_eq_bot hinf (hαY _ (hαY g hg)) (mul_mem hg hc₁Y)
        (hβY _ (hαY g hg)) hc₂' e2).1
    have hc₁C : ∀ z ∈ Y₁, c₁ * z = z * c₁ := by
      intro z hz
      have h1 : z * (c₁ * c₂) = (c₁ * c₂) * z := by
        rw [hc12]; exact mem_centralizer_iff.mp (mem_inf.mp hc).2 z hz
      have h2 : z * c₂ = c₂ * z := hcomm z hz c₂ hc₂'
      have h3 : (c₁ * z) * c₂ = (z * c₁) * c₂ := by
        calc (c₁ * z) * c₂ = c₁ * (z * c₂) := by group
          _ = c₁ * (c₂ * z) := by rw [h2]
          _ = (c₁ * c₂) * z := by group
          _ = z * (c₁ * c₂) := h1.symm
          _ = (z * c₁) * c₂ := by group
      exact mul_right_cancel h3
    rw [hgc, hc₁.mul_u _ hg _ hc₁Y, hc₁.u_eq_zero_of_comm hσ hc₁Y hc₁C, add_zero]
  have hcore := hc₁.apply_sq_eq hσq hE hF α hαY hαmul hαα hy
  have hab : α y * β y = β y * α y := hcomm (α y) (hαY y hy) _ (hβY y hy)
  calc x * y ^ 2 * x⁻¹ = (x * y * x⁻¹) ^ 2 := by rw [pow_two, pow_two]; group
    _ = (α y * β y) ^ 2 := by rw [hxg y]
    _ = α y * (β y * α y) * β y := by rw [pow_two]; group
    _ = α y * (α y * β y) * β y := by rw [hab]
    _ = α y ^ 2 * β y ^ 2 := by rw [pow_two, pow_two]; group
    _ = α y ^ 2 := by rw [hβsq y hy, mul_one]
    _ = α (y ^ 2) := by rw [pow_two, pow_two, hαmul y hy y hy]
    _ = y ^ 2 := hcore

theorem conj_sq_eq_of_mem_sup {Y₁ Y₂ : Subgroup G} (hcomm : ∀ a ∈ Y₁, ∀ b ∈ Y₂, a * b = b * a)
    {x : G} (h₁ : ∀ a ∈ Y₁, x * a ^ 2 * x⁻¹ = a ^ 2) (h₂ : ∀ b ∈ Y₂, x * b ^ 2 * x⁻¹ = b ^ 2)
    {w : G} (hw : w ∈ Y₁ ⊔ Y₂) : x * w ^ 2 * x⁻¹ = w ^ 2 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_eq_of_mem_sup_of_commute hcomm hw
  have hab : a * b = b * a := hcomm a ha b hb
  have e : (a * b) ^ 2 = a ^ 2 * b ^ 2 := by
    calc (a * b) ^ 2 = a * (b * a) * b := by rw [pow_two]; group
      _ = a * (a * b) * b := by rw [hab]
      _ = a ^ 2 * b ^ 2 := by rw [pow_two, pow_two]; group
  rw [e]
  calc x * (a ^ 2 * b ^ 2) * x⁻¹ = (x * a ^ 2 * x⁻¹) * (x * b ^ 2 * x⁻¹) := by group
    _ = a ^ 2 * b ^ 2 := by rw [h₁ a ha, h₂ b hb]

theorem commutator_le_centralizer_of_sq {U : Subgroup G} {x : G}
    (hcen : ∀ w ∈ U, ∀ w' ∈ U, ∀ z ∈ U, ⁅w, w'⁆ * z = z * ⁅w, w'⁆)
    (hsq : ∀ w ∈ U, x * w ^ 2 * x⁻¹ = w ^ 2) : ⁅U, U⁆ ≤ centralizer ({x} : Set G) := by
  rw [Subgroup.commutator_le]
  intro w hw w' hw'
  rw [mem_centralizer_singleton_iff]
  have hk1 : w * w' = ⁅w, w'⁆ * (w' * w) := by rw [commutatorElement_def]; group
  have hkc : ⁅w, w'⁆ * w' = w' * ⁅w, w'⁆ := hcen w hw w' hw' w' hw'
  have key : (w' * w) ^ 2 = ⁅w, w'⁆ * (w' ^ 2 * w ^ 2) := by
    calc (w' * w) ^ 2 = w' * (w * w') * w := by rw [pow_two]; group
      _ = w' * (⁅w, w'⁆ * (w' * w)) * w := by rw [hk1]
      _ = (w' * ⁅w, w'⁆) * w' * w * w := by group
      _ = (⁅w, w'⁆ * w') * w' * w * w := by rw [hkc]
      _ = ⁅w, w'⁆ * (w' ^ 2 * w ^ 2) := by rw [pow_two, pow_two]; group
  have hk : ⁅w, w'⁆ = (w' * w) ^ 2 * (w' ^ 2 * w ^ 2)⁻¹ := by rw [key]; group
  have e : x * ((w' * w) ^ 2 * (w' ^ 2 * w ^ 2)⁻¹) * x⁻¹ =
      (x * (w' * w) ^ 2 * x⁻¹) * ((x * w' ^ 2 * x⁻¹) * (x * w ^ 2 * x⁻¹))⁻¹ := by group
  rw [hsq _ (mul_mem hw' hw), hsq _ hw', hsq _ hw, ← hk] at e
  calc ⁅w, w'⁆ * x = (x * ⁅w, w'⁆ * x⁻¹) * x := by rw [e]
    _ = x * ⁅w, w'⁆ := by group

end Factors

end CFSG.SeitzReduction.RankOne
