module

public import Mathlib.GroupTheory.Sylow
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux2

public section

namespace CFSG.AGLEmbedding

variable {X : Type*} [Group X]

theorem exists_conj_eq_of_mem_sup {K : Subgroup X} {x : X}
    (hx : x ∈ K ⊔ Subgroup.centralizer (K : Set X)) :
    ∃ hxN : x ∈ Subgroup.normalizer (K : Set X), ∃ k : K,
      K.normalizerMonoidHom ⟨x, hxN⟩ = MulAut.conj k := by
  set S : Subgroup X := ((MulAut.conj : K →* MulAut K).range.comap
    K.normalizerMonoidHom).map (Subgroup.normalizer (K : Set X)).subtype with hS
  have hKS : K ≤ S := by
    intro k hk
    refine ⟨⟨k, Subgroup.le_normalizer hk⟩, ⟨⟨k, hk⟩, ?_⟩, rfl⟩
    ext y
    simp [MulAut.conj_apply]
  have hCS : Subgroup.centralizer (K : Set X) ≤ S := by
    intro c hc
    refine ⟨⟨c, Subgroup.centralizer_le_normalizer _ hc⟩, ⟨1, ?_⟩, rfl⟩
    ext y
    simp only [map_one, MulAut.one_apply]
    show y = c * y * c⁻¹
    rw [← Subgroup.mem_centralizer_iff.mp hc y y.2, mul_inv_cancel_right]
  obtain ⟨⟨y, hyN⟩, ⟨k, hk⟩, rfl⟩ := sup_le hKS hCS hx
  exact ⟨hyN, k, hk.symm⟩

theorem inv_mul_mem_centralizer_of_conj_eq {K : Subgroup X} {x : X}
    (hxN : x ∈ Subgroup.normalizer (K : Set X)) {k : K}
    (hk : K.normalizerMonoidHom ⟨x, hxN⟩ = MulAut.conj k) :
    (k : X)⁻¹ * x ∈ Subgroup.centralizer (K : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h1 : x * y * x⁻¹ = k * y * (k : X)⁻¹ := by
    have := congrArg (fun a : MulAut K => ((a ⟨y, hy⟩ : K) : X)) hk
    simpa [MulAut.conj_apply] using this
  calc y * ((k : X)⁻¹ * x) = (k : X)⁻¹ * (k * y * (k : X)⁻¹) * x := by group
    _ = (k : X)⁻¹ * (x * y * x⁻¹) * x := by rw [h1]
    _ = (k : X)⁻¹ * x * y := by group

theorem exists_proj {K W : Subgroup X} (hZ : Subgroup.center K = ⊥)
    (hWK : W ≤ K ⊔ Subgroup.centralizer (K : Set X)) :
    ∃ ρ : W →* K, ∀ w : W, ((ρ w : K) : X)⁻¹ * w ∈ Subgroup.centralizer (K : Set X) := by
  have hWN : W ≤ Subgroup.normalizer (K : Set X) := fun w hw =>
    (exists_conj_eq_of_mem_sup (hWK hw)).1
  set c : W →* MulAut K := K.normalizerMonoidHom.comp (Subgroup.inclusion hWN) with hc
  have hinj : Function.Injective (MulAut.conj : K →* MulAut K) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro k hk
    have hkZ : k ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro y
      have := congrArg (fun a : MulAut K => a y) (MonoidHom.mem_ker.mp hk)
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc y * k = k * y * k⁻¹ * k := by rw [this]
        _ = k * y := by group
    rw [hZ] at hkZ
    exact hkZ
  have hrange : ∀ w : W, c w ∈ (MulAut.conj : K →* MulAut K).range := by
    intro w
    obtain ⟨hxN, k, hk⟩ := exists_conj_eq_of_mem_sup (hWK w.2)
    exact ⟨k, hk.symm⟩
  set e := MonoidHom.ofInjective hinj with he
  set ρ : W →* K := e.symm.toMonoidHom.comp (c.codRestrict _ hrange) with hρ
  refine ⟨ρ, fun w => ?_⟩
  have hρw : MulAut.conj (ρ w) = c w := by
    have h1 : e (ρ w) = ⟨c w, hrange w⟩ := by
      simp [hρ]
    have h2 := congrArg Subtype.val h1
    rwa [MonoidHom.ofInjective_apply] at h2
  exact inv_mul_mem_centralizer_of_conj_eq (hWN w.2) (k := ρ w) (by rw [hρw]; rfl)

theorem eq_one_of_commute_of_isSimpleGroup {Λ : Type*} [Group Λ] [IsSimpleGroup Λ]
    (hΛab : ∃ a b : Λ, a * b ≠ b * a) {y : Λ} (hy : ∀ l : Λ, y * l = l * y) : y = 1 := by
  have hZ : Subgroup.center Λ = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Λ) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hΛab
      apply hab
      have hb : b ∈ Subgroup.center Λ := h ▸ Subgroup.mem_top b
      exact (Subgroup.mem_center_iff.mp hb a)
  have hyZ : y ∈ Subgroup.center Λ := Subgroup.mem_center_iff.mpr fun l => (hy l).symm
  rw [hZ] at hyZ
  exact hyZ

variable [Finite X]

theorem mem_centralizer_of_cyclic_sylow {p : ℕ} [hp : Fact p.Prime] {K : Subgroup X}
    (hZ : Subgroup.center K = ⊥) {TK : Sylow p K} (hTKc : IsCyclic (TK : Subgroup K))
    {x : X} (hxsup : x ∈ K ⊔ Subgroup.centralizer (K : Set X)) (hxp : x ^ p = 1)
    {W : Subgroup X} (hWx : ∀ w ∈ W, x * w = w * x)
    (hWK : W ≤ K ⊔ Subgroup.centralizer (K : Set X))
    {Λ : Type*} [Group Λ] [IsSimpleGroup Λ] (hΛab : ∃ a b : Λ, a * b ≠ b * a)
    (hΛp : p ∣ Nat.card Λ) (θ : W →* Λ) (hθs : Function.Surjective θ)
    (hkerC : ∀ w : W, (w : X) ∈ Subgroup.centralizer (K : Set X) → θ w = 1)
    (hkerp : ∀ w : W, θ w = 1 → p.Coprime (orderOf w)) :
    x ∈ Subgroup.centralizer (K : Set X) := by
  obtain ⟨hxN, k, hk⟩ := exists_conj_eq_of_mem_sup hxsup
  obtain ⟨c, hc, hxkc⟩ : ∃ c ∈ Subgroup.centralizer (K : Set X), x = k * c :=
    ⟨(k : X)⁻¹ * x, inv_mul_mem_centralizer_of_conj_eq hxN hk, by group⟩
  have hKC : ∀ y : K, (y : X) ∈ Subgroup.centralizer (K : Set X) → y = 1 := by
    intro y hy
    have hyZ : y ∈ Subgroup.center K := Subgroup.mem_center_iff.mpr fun l =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp hy l l.2)
    rw [hZ] at hyZ
    exact hyZ
  have hkc : ∀ y ∈ K, ∀ d ∈ Subgroup.centralizer (K : Set X), y * d = d * y := fun y hy d hd =>
    (Subgroup.mem_centralizer_iff.mp hd y hy)
  have hkp : k ^ p = 1 := by
    apply hKC
    have h1 : ((k : X)) ^ p * c ^ p = 1 := by
      rw [← (Commute.mul_pow (hkc k k.2 c hc) p), ← hxkc, hxp]
    have h2 : ((k ^ p : K) : X) = (c ^ p)⁻¹ := by
      rw [Subgroup.coe_pow]
      exact eq_inv_of_mul_eq_one_left h1
    rw [h2]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hc p)
  obtain ⟨ρ, hρ⟩ := exists_proj hZ hWK
  have hkA : ∀ w : W, k * ρ w = ρ w * k := by
    intro w
    obtain ⟨u, huC, hwu⟩ : ∃ u ∈ Subgroup.centralizer (K : Set X), (w : X) = ρ w * u :=
      ⟨_, hρ w, by group⟩
    have hxw := hWx w w.2
    rw [hxkc, hwu] at hxw
    have e1 : (k : X) * c * (ρ w * u) = k * ρ w * (c * u) := by
      calc (k : X) * c * (ρ w * u) = k * (c * ρ w) * u := by group
        _ = k * (ρ w * c) * u := by rw [hkc _ (ρ w).2 c hc]
        _ = k * ρ w * (c * u) := by group
    have e2 : (ρ w : X) * u * (k * c) = ρ w * k * (u * c) := by
      calc (ρ w : X) * u * (k * c) = ρ w * (u * k) * c := by group
        _ = ρ w * (k * u) * c := by rw [hkc _ k.2 u huC]
        _ = ρ w * k * (u * c) := by group
    rw [e1, e2] at hxw
    have hy : ((ρ w : X) * k)⁻¹ * ((k : X) * ρ w) = u * c * (c * u)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul]
      calc (k : X) * ρ w = k * ρ w * (c * u) * (c * u)⁻¹ := by group
        _ = ρ w * k * (u * c) * (c * u)⁻¹ := by rw [hxw]
        _ = ρ w * k * (u * c * (c * u)⁻¹) := by group
    have hyC : ((ρ w * k)⁻¹ * (k * ρ w) : K) = 1 := by
      apply hKC
      rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul, Subgroup.coe_mul, hy]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ huC hc)
        (Subgroup.inv_mem _ (Subgroup.mul_mem _ hc huC))
    exact (inv_mul_eq_one.mp hyC).symm
  obtain ⟨f, hf, hfs, -⟩ := exists_surjective_comp_eq ρ.rangeRestrict ρ.rangeRestrict_surjective
    θ hθs (by
      rw [MonoidHom.ker_rangeRestrict]
      intro w hw
      apply hkerC
      have := hρ w
      rwa [MonoidHom.mem_ker.mp hw, Subgroup.coe_one, inv_one, one_mul] at this)
  by_contra hxC
  have hk1 : k ≠ 1 := by
    rintro rfl
    apply hxC
    rw [hxkc, Subgroup.coe_one, one_mul]
    exact hc
  have hko : orderOf k = p := orderOf_eq_prime hkp hk1
  have hpA : p ∣ Nat.card ρ.range := hΛp.trans (Subgroup.card_dvd_of_surjective hfs)
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := ρ.range) p hpA
  have hsk : (s : K) * k = k * s := by
    obtain ⟨w, hw⟩ := s.2
    rw [← hw]
    exact (hkA w).symm
  have hYp : IsPGroup p (Subgroup.zpowers (s : K) ⊔ Subgroup.zpowers k : Subgroup K) := by
    have hk' : IsPGroup p (Subgroup.zpowers k) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hko, pow_one])
    have hs' : IsPGroup p (Subgroup.zpowers (s : K)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hs, pow_one])
    refine IsPGroup.to_sup_of_normal_right' hs' hk' ?_
    rw [Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy => by
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact ((Commute.zpow_right hsk j).eq).symm)
  obtain ⟨Q, hYQ⟩ := hYp.exists_le_sylow
  have hQc : IsCyclic (Q : Subgroup K) :=
    isCyclic_of_surjective (Sylow.equiv TK Q).toMonoidHom (Sylow.equiv TK Q).surjective
  have hsQ : (s : K) ∈ (Q : Subgroup K) := hYQ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
  have hkQ : k ∈ (Q : Subgroup K) := hYQ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  have heq : Subgroup.zpowers (⟨s, hsQ⟩ : (Q : Subgroup K)) =
      Subgroup.zpowers (⟨k, hkQ⟩ : (Q : Subgroup K)) := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers]
    have e1 : orderOf (⟨s, hsQ⟩ : (Q : Subgroup K)) = p := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hs]
    have e2 : orderOf (⟨k, hkQ⟩ : (Q : Subgroup K)) = p := by
      rw [Subgroup.orderOf_mk, hko]
    rw [e1, e2]
  have hks : (⟨k, hkQ⟩ : (Q : Subgroup K)) ∈ Subgroup.zpowers ⟨s, hsQ⟩ := by
    rw [heq]
    exact Subgroup.mem_zpowers _
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hks
  have hkA' : k ∈ ρ.range := by
    have h1 : k = (s : K) ^ j := by
      have := congrArg Subtype.val hj
      simpa using this.symm
    rw [h1]
    exact Subgroup.zpow_mem _ s.2 j
  have hfk : f ⟨k, hkA'⟩ = 1 := by
    apply eq_one_of_commute_of_isSimpleGroup hΛab
    intro l
    obtain ⟨⟨a, ha⟩, rfl⟩ := hfs l
    rw [← map_mul, ← map_mul]
    congr 1
    obtain ⟨w, rfl⟩ := ha
    apply Subtype.ext
    exact hkA w
  obtain ⟨w, hw⟩ := hkA'
  have hθw : θ w = 1 := by
    rw [← hf w]
    have : ρ.rangeRestrict w = ⟨k, ⟨w, hw⟩⟩ := Subtype.ext hw
    rw [this]
    exact hfk
  have hco := hkerp w hθw
  have hdvd : orderOf k ∣ orderOf w := by
    rw [← hw]
    exact orderOf_map_dvd ρ w
  rw [hko] at hdvd
  exact (Nat.Prime.coprime_iff_not_dvd hp.out).mp hco hdvd

end CFSG.AGLEmbedding
