module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingNormalizerOdd
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingSylowAut

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace U3RootCoords

variable {G : Type*} [Group G] {E : Type*} [Field E] {T₁ : Subgroup G} {σ : E →+* E}
  {u v : G → E}

theorem exists_isometry [CharP E 2] [Finite E] (hc : U3RootCoords T₁ σ u v) {q : ℕ}
    (hσq : ∀ x, σ x = x ^ q) (hE : Nat.card E = q ^ 2) (hF : Nat.card {x : E // σ x = x} = q)
    (α : G → G) (hαT : ∀ y ∈ T₁, α y ∈ T₁)
    (hαmul : ∀ y ∈ T₁, ∀ y' ∈ T₁, α (y * y') = α y * α y')
    (hαα : ∀ y ∈ T₁, u (α (α y)) = u y) :
    ∃ φ : E → E, (∀ a b, φ (a + b) = φ a + φ b) ∧ (∀ a, φ (φ a) = a) ∧
      (∀ a, φ a * σ (φ a) = a * σ a) ∧ ∀ y ∈ T₁, u (α y) = φ (u y) := by
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
  exact ⟨fun a => u (α (s a)), hφadd, hφφ, hN, hφu⟩

end U3RootCoords

section Factors

variable {G : Type*} [Group G]

theorem exists_isometry_of_mem_normalizer {E : Type*} [Field E] [CharP E 2] [Finite E]
    {σ : E →+* E} {q : ℕ} (hσq : ∀ x, σ x = x ^ q) (hE : Nat.card E = q ^ 2)
    (hF : Nat.card {x : E // σ x = x} = q) {U Y₁ Y₂ : Subgroup G} {u₁ v₁ : G → E}
    (hc₁ : U3RootCoords Y₁ σ u₁ v₁) (hU : Y₁ ⊔ Y₂ = U) (hinf : Y₁ ⊓ Y₂ = ⊥)
    (hcomm : ∀ a ∈ Y₁, ∀ b ∈ Y₂, a * b = b * a) {y : G} (hyU : y ∈ normalizer (U : Set G))
    (hy₁ : y ∈ normalizer ((U ⊓ centralizer (Y₂ : Set G) : Subgroup G) : Set G))
    (hyy : ∀ w ∈ U, y * y * w * (y * y)⁻¹ * w⁻¹ ∈ U ⊓ centralizer (U : Set G)) :
    ∃ φ : E → E, (∀ a b, φ (a + b) = φ a + φ b) ∧ (∀ a, φ (φ a) = a) ∧
      (∀ a, φ a * σ (φ a) = a * σ a) ∧ ∀ a ∈ Y₁, ∀ a' ∈ Y₁,
        (y * a * y⁻¹ * a'⁻¹ ∈ U ⊓ centralizer (U : Set G) ↔ u₁ a' = φ (u₁ a)) := by
  have hσ := NormInvolution.exists_sigma_ne σ hE hF
  have hY₁U : Y₁ ≤ U := hU ▸ le_sup_left
  have hY₂U : Y₂ ≤ U := hU ▸ le_sup_right
  set Zs := U ⊓ centralizer (U : Set G) with hZs
  have hM₁ : ∀ g ∈ Y₁, g ∈ U ⊓ centralizer (Y₂ : Set G) := fun g hg =>
    mem_inf.mpr ⟨hY₁U hg, mem_centralizer_iff.mpr fun b hb => (hcomm g hg b hb).symm⟩
  have hyM₁ : ∀ g ∈ Y₁, y * g * y⁻¹ ∈ U ⊓ centralizer (Y₂ : Set G) := fun g hg =>
    (mem_normalizer_iff.mp hy₁ g).mp (hM₁ g hg)
  have hZ₂ : ∀ b ∈ Y₂, (∀ b' ∈ Y₂, b * b' = b' * b) → b ∈ Zs := by
    intro b hb hbc
    refine mem_inf.mpr ⟨hY₂U hb, mem_centralizer_iff.mpr fun z hz => ?_⟩
    exact (commute_of_mem_sup_of_commute_factors hcomm (fun a ha => (hcomm a ha b hb).symm) hbc
      (hU ▸ hz)).symm
  have hZ₁ : ∀ a ∈ Y₁, (∀ a' ∈ Y₁, a * a' = a' * a) → a ∈ Zs := by
    intro a ha hac
    refine mem_inf.mpr ⟨hY₁U ha, mem_centralizer_iff.mpr fun z hz => ?_⟩
    exact (commute_of_mem_sup_of_commute_factors hcomm hac (fun b hb => hcomm a ha b hb)
      (hU ▸ hz)).symm
  have hZu : ∀ a ∈ Y₁, a ∈ Zs → u₁ a = 0 := fun a ha hZ =>
    hc₁.u_eq_zero_of_comm hσ ha fun z hz =>
      (mem_centralizer_iff.mp (mem_inf.mp hZ).2 z (hY₁U hz)).symm
  have hconjZ : ∀ w ∈ U, ∀ z ∈ Zs, w * z * w⁻¹ ∈ Zs := by
    intro w hw z hz
    have h1 : w * z = z * w := mem_centralizer_iff.mp (mem_inf.mp hz).2 w hw
    rw [h1, mul_inv_cancel_right]
    exact hz
  have hyZ : ∀ z ∈ Zs, y * z * y⁻¹ ∈ Zs := by
    intro z hz
    obtain ⟨hzU, hzC⟩ := mem_inf.mp hz
    refine mem_inf.mpr ⟨(mem_normalizer_iff.mp hyU z).mp hzU, mem_centralizer_iff.mpr
      fun w hw => ?_⟩
    have hw' : y⁻¹ * w * y ∈ U := (mem_normalizer_iff''.mp hyU w).mp hw
    have h1 : (y⁻¹ * w * y) * z = z * (y⁻¹ * w * y) := mem_centralizer_iff.mp hzC _ hw'
    calc w * (y * z * y⁻¹) = y * ((y⁻¹ * w * y) * z) * y⁻¹ := by group
      _ = y * (z * (y⁻¹ * w * y)) * y⁻¹ := by rw [h1]
      _ = y * z * y⁻¹ * w := by group
  have hdec : ∀ g : G, ∃ a : G, g ∈ Y₁ → (a ∈ Y₁ ∧ a⁻¹ * (y * g * y⁻¹) ∈ Y₂) := by
    intro g
    by_cases hg : g ∈ Y₁
    · obtain ⟨a, ha, b, hb, hab⟩ :=
        exists_mul_eq_of_mem_sup_of_commute hcomm (hU ▸ (mem_inf.mp (hyM₁ g hg)).1)
      exact ⟨a, fun _ => ⟨ha, by rw [← hab, inv_mul_cancel_left]; exact hb⟩⟩
    · exact ⟨1, fun h => absurd h hg⟩
  choose α hα using hdec
  obtain ⟨β, hβdef⟩ : ∃ β : G → G, ∀ g, β g = (α g)⁻¹ * (y * g * y⁻¹) := ⟨_, fun _ => rfl⟩
  have hαY : ∀ g ∈ Y₁, α g ∈ Y₁ := fun g hg => (hα g hg).1
  have hβY : ∀ g ∈ Y₁, β g ∈ Y₂ := fun g hg => by rw [hβdef]; exact (hα g hg).2
  have hyg : ∀ g, y * g * y⁻¹ = α g * β g := fun g => by rw [hβdef]; group
  have hβC : ∀ g ∈ Y₁, ∀ b ∈ Y₂, β g * b = b * β g := by
    intro g hg b hb
    have hc1 : b * (y * g * y⁻¹) = (y * g * y⁻¹) * b :=
      mem_centralizer_iff.mp (mem_inf.mp (hyM₁ g hg)).2 b hb
    have hc2 : α g * b = b * α g := hcomm (α g) (hαY g hg) b hb
    have hc3 : (α g)⁻¹ * b = b * (α g)⁻¹ := by
      calc (α g)⁻¹ * b = (α g)⁻¹ * (b * α g) * (α g)⁻¹ := by group
        _ = (α g)⁻¹ * (α g * b) * (α g)⁻¹ := by rw [hc2]
        _ = b * (α g)⁻¹ := by group
    calc β g * b = (α g)⁻¹ * ((y * g * y⁻¹) * b) := by rw [hβdef]; group
      _ = (α g)⁻¹ * (b * (y * g * y⁻¹)) := by rw [hc1]
      _ = ((α g)⁻¹ * b) * (y * g * y⁻¹) := by group
      _ = (b * (α g)⁻¹) * (y * g * y⁻¹) := by rw [hc3]
      _ = b * β g := by rw [hβdef]; group
  have hβZ : ∀ g ∈ Y₁, β g ∈ Zs := fun g hg => hZ₂ _ (hβY g hg) fun b hb => hβC g hg b hb
  have hαmul : ∀ g ∈ Y₁, ∀ g' ∈ Y₁, α (g * g') = α g * α g' := by
    intro g hg g' hg'
    have hb : α g' * β g = β g * α g' := hcomm (α g') (hαY g' hg') _ (hβY g hg)
    have e : α (g * g') * β (g * g') = (α g * α g') * (β g * β g') := by
      calc α (g * g') * β (g * g') = y * (g * g') * y⁻¹ := (hyg _).symm
        _ = (y * g * y⁻¹) * (y * g' * y⁻¹) := by group
        _ = α g * (β g * α g') * β g' := by rw [hyg g, hyg g']; group
        _ = α g * (α g' * β g) * β g' := by rw [hb]
        _ = (α g * α g') * (β g * β g') := by group
    exact (eq_and_eq_of_mul_eq_mul_of_inf_eq_bot hinf (hαY _ (mul_mem hg hg'))
      (mul_mem (hαY g hg) (hαY g' hg')) (hβY _ (mul_mem hg hg'))
      (mul_mem (hβY g hg) (hβY g' hg')) e).1
  have hαα : ∀ g ∈ Y₁, u₁ (α (α g)) = u₁ g := by
    intro g hg
    have hag := hαY g hg
    have haag := hαY _ hag
    have e1 : y * y * g * (y * y)⁻¹ = α (α g) * β (α g) * (y * β g * y⁻¹) := by
      calc y * y * g * (y * y)⁻¹ = y * (y * g * y⁻¹) * y⁻¹ := by group
        _ = y * (α g * β g) * y⁻¹ := by rw [hyg g]
        _ = (y * α g * y⁻¹) * (y * β g * y⁻¹) := by group
        _ = α (α g) * β (α g) * (y * β g * y⁻¹) := by rw [hyg (α g)]
    have hc : g⁻¹ * α (α g) ∈ Zs := by
      have e2 : g⁻¹ * α (α g) = (g⁻¹ * (y * y * g * (y * y)⁻¹ * g⁻¹) * g) *
          (y * β g * y⁻¹)⁻¹ * (β (α g))⁻¹ := by
        rw [e1]
        group
      rw [e2]
      refine mul_mem (mul_mem ?_ (inv_mem (hyZ _ (hβZ g hg)))) (inv_mem (hβZ _ hag))
      have := hconjZ g⁻¹ (inv_mem (hY₁U hg)) _ (hyy g (hY₁U hg))
      rwa [inv_inv] at this
    have h0 := hZu _ (mul_mem (inv_mem hg) haag) hc
    rw [hc₁.u_mul_inv hg haag] at h0
    exact sub_eq_zero.mp h0
  obtain ⟨φ, hφadd, hφφ, hφN, hφu⟩ := hc₁.exists_isometry hσq hE hF α hαY hαmul hαα
  refine ⟨φ, hφadd, hφφ, hφN, fun a ha a' ha' => ?_⟩
  rw [← hφu a ha]
  constructor
  · intro h
    have e : α a * a'⁻¹ = (y * a * y⁻¹ * a'⁻¹) * (a' * (β a)⁻¹ * a'⁻¹) := by rw [hyg a]; group
    have hZ : α a * a'⁻¹ ∈ Zs := by
      rw [e]
      exact mul_mem h (hconjZ a' (hY₁U ha') _ (inv_mem (hβZ a ha)))
    have h0 := hZu _ (mul_mem (hαY a ha) (inv_mem ha')) hZ
    rw [hc₁.mul_u _ (hαY a ha) _ (inv_mem ha'), hc₁.u_inv ha'] at h0
    linear_combination -h0
  · intro h
    have hcu : u₁ (a'⁻¹ * α a) = 0 := by rw [hc₁.u_mul_inv ha' (hαY a ha), h, sub_self]
    have hcY : a'⁻¹ * α a ∈ Y₁ := mul_mem (inv_mem ha') (hαY a ha)
    have hcZ : a'⁻¹ * α a ∈ Zs := hZ₁ _ hcY fun z hz => hc₁.comm_of_u_eq_zero hcY hcu hz
    have e : y * a * y⁻¹ * a'⁻¹ = a' * (a'⁻¹ * α a) * a'⁻¹ * (a' * β a * a'⁻¹) := by
      rw [hyg a]
      group
    rw [e]
    exact mul_mem (hconjZ a' (hY₁U ha') _ hcZ) (hconjZ a' (hY₁U ha') _ (hβZ a ha))

end Factors

end CFSG.SeitzReduction.RankOne
