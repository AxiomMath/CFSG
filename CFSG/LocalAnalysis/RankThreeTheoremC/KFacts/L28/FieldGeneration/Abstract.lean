module

public import CFSG.RankThree.PartOne.CTP.SeitzField
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.RankThree.PartOne.CTP.StrongPClassification

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.L28.FieldGeneration

open CFSG.RankThree.PartOne.CTP

variable {K : Type} [Group K]

theorem eqLocus_eq_fixedSubgroup (α : MulAut K) :
    α.toMonoidHom.eqLocus (MonoidHom.id K) = fixedSubgroup α := by
  ext x
  exact Iff.rfl

theorem fixedSubgroup_conj_mul (α : MulAut K) (t : K) :
    fixedSubgroup (MulAut.conj t * α * MulAut.conj t⁻¹) =
      (fixedSubgroup α).map (MulAut.conj t).toMonoidHom := by
  ext x
  constructor
  · intro hx
    have hx' : t * α (t⁻¹ * x * t) * t⁻¹ = x := by
      have h : (MulAut.conj t * α * MulAut.conj t⁻¹) x = x := hx
      simp only [MulAut.mul_apply, MulAut.conj_apply, inv_inv] at h
      exact h
    refine ⟨t⁻¹ * x * t, ?_, ?_⟩
    · show α (t⁻¹ * x * t) = t⁻¹ * x * t
      calc α (t⁻¹ * x * t) = t⁻¹ * (t * α (t⁻¹ * x * t) * t⁻¹) * t := by group
        _ = t⁻¹ * x * t := by rw [hx']
    · show t * (t⁻¹ * x * t) * t⁻¹ = x
      group
  · rintro ⟨y, hy, rfl⟩
    have hy' : α y = y := hy
    show (MulAut.conj t * α * MulAut.conj t⁻¹) (t * y * t⁻¹) = t * y * t⁻¹
    simp only [MulAut.mul_apply, MulAut.conj_apply, inv_inv]
    rw [show t⁻¹ * (t * y * t⁻¹) * t = y by group, hy']

theorem exists_twist_of_cyclic_nine {T : Subgroup K} (hcyc : IsCyclic T) (h9 : Nat.card T = 9)
    {α : MulAut K} (hα3 : α ^ 3 = 1) (hαT : T.map α.toMonoidHom = T) (hne : ∃ s ∈ T, α s ≠ s) :
    ∃ t ∈ T, α t * t⁻¹ ≠ 1 ∧ α (α t * t⁻¹) = α t * t⁻¹ ∧ (α t * t⁻¹) ^ 3 = 1 := by
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hfin : Finite T := Nat.finite_of_card_ne_zero (by rw [h9]; norm_num)
  set t : K := (g : K) with htdef
  have htT : t ∈ T := g.2
  have hordg : orderOf g = 9 := by
    rw [← h9]
    exact orderOf_eq_card_of_forall_mem_zpowers hg
  have hord : orderOf t = 9 := by rw [htdef, Subgroup.orderOf_coe, hordg]
  have hpow : ∀ s ∈ T, ∃ n : ℕ, t ^ n = s := by
    intro s hs
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨s, hs⟩)
    have hk' : (t ^ k : K) = s := by
      rw [htdef, ← Subgroup.coe_zpow, hk]
    refine ⟨(k % 9).toNat, ?_⟩
    rw [← hk', ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num))]
    have h := zpow_mod_orderOf t k
    rw [hord] at h
    exact h
  have hαt : α t ∈ T := by
    rw [← hαT]
    exact ⟨t, htT, rfl⟩
  obtain ⟨k, hk9, htk⟩ : ∃ k : ℕ, k < 9 ∧ α t = t ^ k := by
    obtain ⟨n, hn⟩ := hpow _ hαt
    exact ⟨n % 9, Nat.mod_lt _ (by norm_num), by rw [← hn, ← hord, pow_mod_orderOf]⟩
  have hαpow : ∀ m : ℕ, α (t ^ m) = t ^ (k * m) := fun m => by
    rw [map_pow, htk, ← pow_mul]
  have h3 : t ^ (k * (k * k)) = t ^ 1 := by
    have h1 : (α ^ 3) t = t := by rw [hα3]; rfl
    rw [pow_succ, pow_succ, pow_one, MulAut.mul_apply, MulAut.mul_apply, htk, hαpow,
      hαpow] at h1
    rw [pow_one]
    exact h1
  have hmod : k * (k * k) % 9 = 1 % 9 := by
    have h := pow_eq_pow_iff_modEq.mp h3
    rw [hord] at h
    exact h
  have hk1 : k ≠ 1 := by
    rintro rfl
    obtain ⟨s, hs, hαs⟩ := hne
    obtain ⟨m, rfl⟩ := hpow s hs
    exact hαs (by rw [hαpow, one_mul])
  have hk47 : k = 4 ∨ k = 7 := by
    interval_cases k <;> omega
  have hdiv : ∀ m : ℕ, t ^ m = 1 ↔ 9 ∣ m := fun m => by
    rw [← hord]
    exact orderOf_dvd_iff_pow_eq_one.symm
  refine ⟨t, htT, ?_⟩
  rcases hk47 with rfl | rfl
  · have hw : α t * t⁻¹ = t ^ 3 := by
      rw [htk, pow_succ, mul_inv_cancel_right]
    rw [hw, hαpow, ← pow_mul, ne_eq, hdiv, hdiv, pow_eq_pow_iff_modEq, hord]
    exact ⟨by norm_num, by decide, by norm_num⟩
  · have hw : α t * t⁻¹ = t ^ 6 := by
      rw [htk, pow_succ, mul_inv_cancel_right]
    rw [hw, hαpow, ← pow_mul, ne_eq, hdiv, hdiv, pow_eq_pow_iff_modEq, hord]
    exact ⟨by norm_num, by decide, by norm_num⟩

theorem isOuterOfOrder_three [Finite K] (hsimple : IsSimpleGroup K)
    (hnab : ∃ a b : K, a * b ≠ b * a) {T : Subgroup K} (hT : CFSG.ABGLocalTools.IsSylowOf 3 T ⊤)
    (hcomm : IsMulCommutative T) {α : MulAut K} (hα : orderOf α = 3)
    (hαT : T.map α.toMonoidHom = T) (hne : ∃ s ∈ T, α s ≠ s) : IsOuterOfOrder 3 α := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨hα, fun g hg => ?_⟩
  have hcenter : Subgroup.center K = ⊥ := by
    rcases (Subgroup.center K).normal_of_characteristic.eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have hb : b ∈ Subgroup.center K := h ▸ Subgroup.mem_top b
      exact hab (Subgroup.mem_center_iff.mp hb a)
  have hg3 : g ^ 3 = 1 := by
    have h1 : MulAut.conj (g ^ 3) = 1 := by
      rw [map_pow, ← hg, ← hα, pow_orderOf_eq_one]
    have h2 : g ^ 3 ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro z
      have h3 := congrArg (fun φ : MulAut K => φ z) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h3
      calc z * g ^ 3 = g ^ 3 * z * (g ^ 3)⁻¹ * g ^ 3 := by rw [h3]
        _ = g ^ 3 * z := by group
    rw [hcenter] at h2
    exact Subgroup.mem_bot.mp h2
  have hgN : g ∈ Subgroup.normalizer (T : Set K) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [← hαT, hg]
      exact ⟨h, hh, by simp [MulAut.conj_apply]⟩
    · intro hh
      rw [← hαT, hg] at hh
      obtain ⟨h', hh', hEq⟩ := hh
      have : h' = h := by
        simpa [MulAut.conj_apply] using hEq
      rwa [← this]
  obtain ⟨-, hTp, hTi⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hT
  rw [Subgroup.relIndex_top_right] at hTi
  set P : Sylow 3 K := hTp.toSylow hTi with hPdef
  have hPT : (P : Subgroup K) = T := IsPGroup.toSylow_coe hTp hTi
  have hgp : IsPGroup 3 (Subgroup.zpowers g) := by
    have hd : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one hg3
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h3, pow_one])
  have hgT : g ∈ T := by
    have hPset : (P : Set K) = (T : Set K) := by rw [← hPT]; rfl
    have hgN' : g ∈ Subgroup.normalizer (P : Set K) := by rw [hPset]; exact hgN
    have h1 : g ∈ Subgroup.zpowers g ⊓ Subgroup.normalizer (P : Set K) :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_zpowers g, hgN'⟩
    have h2 : g ∈ Subgroup.zpowers g ⊓ (P : Subgroup K) := by
      rw [← hgp.inf_normalizer_sylow P]
      exact h1
    rw [← hPT]
    exact (Subgroup.mem_inf.mp h2).2
  obtain ⟨s, hs, hαs⟩ := hne
  apply hαs
  rw [hg, MulAut.conj_apply]
  have hcomm' : g * s = s * g := by
    have := hcomm.is_comm.comm ⟨g, hgT⟩ ⟨s, hs⟩
    exact congrArg Subtype.val this
  rw [hcomm', mul_inv_cancel_right]

theorem sup_fixedSubgroup_eq_top [Finite K] (hd : FieldAutData K 3) {T : Subgroup K}
    {α : MulAut K} (hα : IsOuterOfOrder 3 α) {t : K} (ht : t ∈ T) (hw1 : α t * t⁻¹ ≠ 1)
    (hwα : α (α t * t⁻¹) = α t * t⁻¹) (hw3 : (α t * t⁻¹) ^ 3 = 1) :
    T ⊔ fixedSubgroup α = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set w := α t * t⁻¹ with hwdef
  set τ := MulAut.conj t * α * MulAut.conj t⁻¹ with hτdef
  have hwC : w ∈ fixedSubgroup α := hwα
  have h3 : 3 ∣ Nat.card (fixedSubgroup α) := by
    have hord : orderOf w = 3 := orderOf_eq_prime hw3 hw1
    have h := orderOf_dvd_natCard (⟨w, hwC⟩ : fixedSubgroup α)
    rwa [Subgroup.orderOf_mk, hord] at h
  have hτout : IsOuterOfOrder 3 τ := by
    refine ⟨?_, fun g hg => hα.2 (t⁻¹ * g * t) ?_⟩
    · have hsc : SemiconjBy (MulAut.conj t) α τ := by
        rw [SemiconjBy, hτdef, map_inv]
        group
      rw [← hsc.orderOf_eq]
      exact hα.1
    · have h1 : α = MulAut.conj t⁻¹ * τ * MulAut.conj t := by
        rw [hτdef, map_inv]
        group
      rw [h1, hg, ← map_mul, ← map_mul]
  have hfixτ := fixedSubgroup_conj_mul α t
  have hne : fixedSubgroup α ≠ fixedSubgroup τ := by
    intro heq
    apply hw1
    refine hd.center α hα h3 w hwC fun y hy => ?_
    have hy' : y ∈ fixedSubgroup τ := heq ▸ hy
    rw [hfixτ] at hy'
    obtain ⟨y', hy'C, hyy'⟩ := hy'
    have hy'eq : y' = t⁻¹ * y * t := by
      rw [← hyy']
      change y' = t⁻¹ * (t * y' * t⁻¹) * t
      group
    have hfix : α (t⁻¹ * y * t) = t⁻¹ * y * t := by
      rw [← hy'eq]
      exact hy'C
    have hαy : α y = y := hy
    have hkey : (α t)⁻¹ * y * α t = t⁻¹ * y * t := by
      rw [← hfix, map_mul, map_mul, map_inv, hαy]
    calc w * y = α t * (t⁻¹ * y * t) * t⁻¹ := by rw [hwdef]; group
      _ = α t * ((α t)⁻¹ * y * α t) * t⁻¹ := by rw [hkey]
      _ = y * w := by rw [hwdef]; group
  rcases hd.gen α τ hα hτout hne with hg | hsmall
  · rw [eq_top_iff, ← hg, Subgroup.closure_le]
    rintro x (hx | hx)
    · exact Subgroup.mem_sup_right hx
    · rw [hfixτ] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      have htH : t ∈ T ⊔ fixedSubgroup α := Subgroup.mem_sup_left ht
      have hyH : y ∈ T ⊔ fixedSubgroup α := Subgroup.mem_sup_right hy
      change t * y * t⁻¹ ∈ T ⊔ fixedSubgroup α
      exact (T ⊔ fixedSubgroup α).mul_mem ((T ⊔ fixedSubgroup α).mul_mem htH hyH)
        ((T ⊔ fixedSubgroup α).inv_mem htH)
  · exact absurd h3 hsmall

end CFSG.LocalAnalysis.RankThreeTheoremC.L28.FieldGeneration
