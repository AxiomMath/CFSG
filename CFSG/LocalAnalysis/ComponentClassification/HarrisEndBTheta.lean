module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma48
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverKernelAction

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.EndB

open CFSG Subgroup CFSG.ABGLocalTools

section Theta

variable {G Q : Type} [Group G] [Group Q]

theorem exists_theta {E : Subgroup G} [E.Normal] [Group.IsPerfect E] (π : E →* Q)
    (hπ : Function.Surjective π) (hker : π.ker = center E) :
    ∃ θ : G →* MulAut Q,
      (∀ (g : G) (l l' : E), (l' : G) = g * l * g⁻¹ → θ g (π l) = π l') ∧
      ∀ g : G, θ g = 1 ↔ g ∈ centralizer (E : Set G) := by
  have hN : (⊤ : Subgroup G) ≤ normalizer (E : Set G) := by
    rw [Subgroup.normalizer_eq_top]
  obtain ⟨θ, h1, h2⟩ := M12Cover.CyclicKernel.exists_normalizer_action hN π hπ hker
  refine ⟨θ.comp (Subgroup.topEquiv (G := G)).symm.toMonoidHom, fun g l l' hl => ?_,
    fun g => ?_⟩
  · exact h1 ⟨g, mem_top g⟩ l l' hl
  · exact h2 ⟨g, mem_top g⟩

variable {E : Subgroup G} {π : E →* Q} {θ : G →* MulAut Q}

theorem theta_conj (hπ : Function.Surjective π)
    (hθ : ∀ (g : G) (l l' : E), (l' : G) = g * l * g⁻¹ → θ g (π l) = π l') (l : E) :
    θ l = MulAut.conj (π l) := by
  ext q
  obtain ⟨m, rfl⟩ := hπ q
  rw [hθ l m (l * m * l⁻¹) (by simp), MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem theta_mem_inner_iff (hπ : Function.Surjective π)
    (hθ : ∀ (g : G) (l l' : E), (l' : G) = g * l * g⁻¹ → θ g (π l) = π l')
    (hθ1 : ∀ g : G, θ g = 1 ↔ g ∈ centralizer (E : Set G)) (g : G) :
    θ g ∈ innAut Q ↔ g ∈ E ⊔ centralizer (E : Set G) := by
  have hc : ∀ k ∈ E, ∀ n ∈ centralizer (E : Set G), k * n = n * k :=
    fun k hk n hn => mem_centralizer_iff.mp hn k hk
  constructor
  · rintro ⟨m, hm⟩
    obtain ⟨l, rfl⟩ := hπ m
    have h1 : θ ((l : G)⁻¹ * g) = 1 := by
      rw [map_mul, map_inv, theta_conj hπ hθ, hm, inv_mul_cancel]
    rw [hθ1] at h1
    have h2 : g = l * ((l : G)⁻¹ * g) := by group
    rw [h2]
    exact mul_mem (mem_sup_left l.2) (mem_sup_right h1)
  · intro hg
    obtain ⟨k, hk, n, hn, rfl⟩ := M12Cover.CyclicKernel.exists_mul_of_mem_sup_of_commute hc hg
    have hn1 : θ n = 1 := (hθ1 n).mpr hn
    rw [map_mul, hn1, mul_one, show k = ((⟨k, hk⟩ : E) : G) from rfl, theta_conj hπ hθ]
    exact ⟨_, rfl⟩

theorem mem_sup_or_mul_mem_sup (hπ : Function.Surjective π)
    (hθ : ∀ (g : G) (l l' : E), (l' : G) = g * l * g⁻¹ → θ g (π l) = π l')
    (hθ1 : ∀ g : G, θ g = 1 ↔ g ∈ centralizer (E : Set G)) (hidx : (innAut Q).index = 2)
    {t : G} (ht : θ t ∉ innAut Q) (g : G) :
    g ∈ E ⊔ centralizer (E : Set G) ∨ g * t⁻¹ ∈ E ⊔ centralizer (E : Set G) := by
  by_cases hg : θ g ∈ innAut Q
  · exact Or.inl ((theta_mem_inner_iff hπ hθ hθ1 g).mp hg)
  · right
    rw [← theta_mem_inner_iff hπ hθ hθ1, map_mul, map_inv]
    have h := (Subgroup.mul_mem_iff_of_index_two hidx (a := θ g) (b := (θ t)⁻¹)).mpr
      ⟨fun h => absurd h hg, fun h => absurd (by simpa using h) ht⟩
    exact h

theorem odd_mem_sup (hπ : Function.Surjective π)
    (hθ : ∀ (g : G) (l l' : E), (l' : G) = g * l * g⁻¹ → θ g (π l) = π l')
    (hθ1 : ∀ g : G, θ g = 1 ↔ g ∈ centralizer (E : Set G)) (hidx : (innAut Q).index = 2)
    {g : G} (hg : Odd (orderOf g)) : g ∈ E ⊔ centralizer (E : Set G) := by
  rw [← theta_mem_inner_iff hπ hθ hθ1]
  obtain ⟨m, hm⟩ := hg
  have hsq : θ g = (θ g ^ (m + 1)) ^ 2 := by
    rw [← pow_mul, show (m + 1) * 2 = orderOf g + 1 by omega, pow_succ, ← map_pow,
      pow_orderOf_eq_one, map_one, one_mul]
  rw [hsq]
  have := (innAut Q).normal_of_index_eq_two hidx
  exact Subgroup.sq_mem_of_index_two hidx _

end Theta

theorem mem_of_odd_of_mem_sup {G : Type*} [Group G] [Finite G] {E N : Subgroup G}
    (hN : IsPGroup 2 N) (hc : ∀ k ∈ E, ∀ n ∈ N, k * n = n * k) {x : G} (hx : x ∈ E ⊔ N)
    (hodd : Odd (orderOf x)) : x ∈ E := by
  obtain ⟨e, he, n, hn, rfl⟩ := M12Cover.CyclicKernel.exists_mul_of_mem_sup_of_commute hc hx
  have hcomm : Commute e n := hc e he n hn
  set m := orderOf (e * n) with hm
  have hpow : (e * n) ^ m = 1 := pow_orderOf_eq_one _
  rw [hcomm.mul_pow] at hpow
  have hnm : n ^ m ∈ E := by
    have : n ^ m = (e ^ m)⁻¹ := eq_inv_of_mul_eq_one_right hpow
    rw [this]
    exact inv_mem (pow_mem he m)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hN) ⟨n, hn⟩
  have hk' : orderOf n = 2 ^ k := by rw [← Subgroup.orderOf_mk n hn]; exact hk
  have hcop : Nat.Coprime (orderOf n) m := by
    rw [hk']
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
  have hz : zpowers (n ^ m) = zpowers n := by
    refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr (pow_mem (mem_zpowers n) m)) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hcop.orderOf_pow]
  have hnz : n ∈ zpowers (n ^ m) := hz ▸ mem_zpowers n
  exact mul_mem he (zpowers_le.mpr hnm hnz)

theorem not_isPGroup_bar_of_odd_gen {C : Type*} [Group C] [Finite C] {A : Subgroup C}
    (hA : A ≤ closure {x : C | Odd (orderOf x)}) (hA2 : 2 ∣ Nat.card A) :
    ¬ IsPGroup 2 (C ⧸ pPrimeCore 2 C) := by
  intro hP
  have hle : closure {x : C | Odd (orderOf x)} ≤ pPrimeCore 2 C := by
    rw [closure_le]
    intro x hx
    have hx' : Odd (orderOf x) := hx
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP) (QuotientGroup.mk x)
    have hdvd : orderOf (QuotientGroup.mk x : C ⧸ pPrimeCore 2 C) ∣ orderOf x :=
      orderOf_map_dvd (QuotientGroup.mk' (pPrimeCore 2 C)) x
    rw [hk] at hdvd
    have hk0 : k = 0 := by
      by_contra h
      have h2 : 2 ∣ 2 ^ k := dvd_pow_self 2 h
      exact (Nat.not_even_iff_odd.mpr hx') (even_iff_two_dvd.mpr (h2.trans hdvd))
    rw [hk0, pow_zero, orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at hk
    exact hk
  have hdvd := Subgroup.card_dvd_of_le (hA.trans hle)
  have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 C)) := pPrimeCore_coprime_card
  exact Nat.not_coprime_of_dvd_of_dvd (by norm_num) (dvd_refl 2) (hA2.trans hdvd) hcop

theorem isSylowOf_top_of_normalizer_le {X : Type*} [Group X] [Finite X] {W M : Subgroup X}
    (hW : IsSylowOf 2 W M) (hN : normalizer (W : Set X) ≤ M) : IsSylowOf 2 W ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ, hWQ⟩ := exists_isSylowOf_ge hW.isPGroup (le_top : W ≤ ⊤)
  by_cases hWQ' : W = Q
  · exact hWQ' ▸ hQ
  · exfalso
    have hlt : W.subgroupOf Q < ⊤ := by
      refine lt_of_le_of_ne le_top fun h => hWQ' (le_antisymm hWQ fun x hx => ?_)
      have : (⟨x, hx⟩ : Q) ∈ W.subgroupOf Q := h ▸ mem_top _
      exact this
    have hnil : Group.IsNilpotent Q := hQ.isPGroup.isNilpotent
    have hnc := Group.normalizerCondition_of_isNilpotent (G := Q) _ hlt
    obtain ⟨y, hyN, hyW⟩ := IsConcreteLE.exists_of_lt hnc
    have hyN' : (y : X) ∈ normalizer (W : Set X) := by
      rw [mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        have hxQ : x ∈ Q := hWQ hx
        have := (mem_normalizer_iff.mp hyN ⟨x, hxQ⟩).mp (show (⟨x, hxQ⟩ : Q) ∈ W.subgroupOf Q
          from hx)
        exact this
      · intro hx
        have hxQ : x ∈ Q := by
          have h1 : (y : X)⁻¹ * (y * x * (y : X)⁻¹) * y ∈ Q :=
            mul_mem (mul_mem (inv_mem y.2) (hWQ hx)) y.2
          rwa [show (y : X)⁻¹ * (y * x * (y : X)⁻¹) * y = x by group] at h1
        exact (mem_normalizer_iff.mp hyN ⟨x, hxQ⟩).mpr hx
    have hyM : (y : X) ∈ M := hN hyN'
    have hsup : IsPGroup 2 ↥(W ⊔ zpowers (y : X)) :=
      hQ.isPGroup.to_le (sup_le hWQ (zpowers_le.mpr y.2))
    have heq := hW.eq_of_le (le_sup_left : W ≤ W ⊔ zpowers (y : X))
      (sup_le hW.le (zpowers_le.mpr hyM)) hsup
    exact hyW (show (y : X) ∈ W from heq ▸ mem_sup_right (mem_zpowers _))

end CFSG.ComponentClassification.HarrisLit.EndB
