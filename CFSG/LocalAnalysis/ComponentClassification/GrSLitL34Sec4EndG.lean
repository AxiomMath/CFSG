module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4EndT2

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem fourCube_of_conj {A B Z : Subgroup G} {a b₂ b₃ g₂ g₃ : G}
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hA64 : Nat.card A ≤ 64) (hB : IsElemTwo B)
    (haB : a ∈ B) (hb₂B : b₂ ∈ B) (hb₃B : b₃ ∈ B) (ha1 : a ≠ 1) (hb₂1 : b₂ ≠ 1)
    (hb₂a : b₂ ≠ a) (hb₃1 : b₃ ≠ 1) (hb₃a : b₃ ≠ a) (hb₃b : b₃ ≠ b₂) (hb₃ab : b₃ ≠ a * b₂)
    (hZc : IsCyclic ↥Z) (hZ4 : Nat.card Z = 4) (hZA : Z ≤ A) (haZ : a ∈ Z)
    (hg₂N : g₂ ∈ normalizer (A : Set G)) (hg₃N : g₃ ∈ normalizer (A : Set G))
    (hg₂ : g₂⁻¹ * a * g₂ = b₂) (hg₃ : g₃⁻¹ * a * g₃ = b₃) :
    Nonempty (↥A ≃* Multiplicative (Fin 3 → ZMod 4)) ∧ ∀ t ∈ A, t * t = 1 → t ∈ B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have haa : a * a = 1 := hB.2 a haB
  have hconjA : ∀ {g : G}, g ∈ normalizer (A : Set G) → ∀ z ∈ Z, g⁻¹ * z * g ∈ A := by
    intro g hg z hz
    simpa using (mem_normalizer_iff.mp (inv_mem hg) z).mp (hZA hz)
  let f : ↥Z × ↥Z × ↥Z → G := fun k =>
    (k.1 : G) * (g₂⁻¹ * (k.2.1 : G) * g₂) * (g₃⁻¹ * (k.2.2 : G) * g₃)
  have hfA : ∀ k, f k ∈ A := fun k => mul_mem (mul_mem (hZA k.1.2) (hconjA hg₂N _ k.2.1.2))
    (hconjA hg₃N _ k.2.2.2)
  have hfmul : ∀ k k', f (k * k') = f k * f k' := by
    intro k k'
    have e1 := hAab _ (hconjA hg₃N _ k.2.2.2) _ (hZA k'.1.2)
    have e2 := hAab _ (hconjA hg₂N _ k.2.1.2) _ (hZA k'.1.2)
    have e3 := hAab _ (hconjA hg₃N _ k.2.2.2) _ (hconjA hg₂N _ k'.2.1.2)
    rw [mul_six_regroup e1 e2 e3]
    simp only [f, Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
    group
  let μ : ↥Z × ↥Z × ↥Z →* ↥A :=
    { toFun := fun k => ⟨f k, hfA k⟩
      map_one' := Subtype.ext (by simp [f])
      map_mul' := fun k k' => Subtype.ext (hfmul k k') }
  have hμ : ∀ k, ((μ k : ↥A) : G) = f k := fun _ => rfl
  have hZinv : ∀ x : ↥Z, (x : G) * x = 1 → (x : G) = 1 ∨ (x : G) = a := by
    intro x hx
    by_cases hx1 : (x : G) = 1
    · exact Or.inl hx1
    · exact Or.inr (eq_of_mul_self_eq_one_of_isCyclic hZc x.2 haZ hx haa hx1 ha1)
  have hconj1 : ∀ {g c : G}, g⁻¹ * a * g = c → ∀ x : ↥Z, (x : G) * x = 1 →
      g⁻¹ * (x : G) * g = 1 ∨ g⁻¹ * (x : G) * g = c := by
    intro g c hgc x hx
    rcases hZinv x hx with h | h
    · left
      rw [h]
      group
    · right
      rw [h, hgc]
  have hμinj : Function.Injective μ := by
    rw [injective_iff_map_eq_one]
    intro k hk
    by_contra hk1
    have hpow : k ^ (2 ^ 2) = 1 := by
      have hx : ∀ x : ↥Z, x ^ (2 ^ 2) = 1 := fun x => by
        rw [show (2 : ℕ) ^ 2 = 4 from rfl, ← hZ4]
        exact pow_card_eq_one'
      exact Prod.ext (hx _) (Prod.ext (hx _) (hx _))
    obtain ⟨j, hj, hkj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hpow)
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hkj
      exact hk1 hkj
    set k' := k ^ (2 ^ (j - 1)) with hk'
    have hk'2 : k' * k' = 1 := by
      rw [hk', ← pow_add, ← two_mul, ← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hj0),
        ← hkj, pow_orderOf_eq_one]
    have hk'1 : k' ≠ 1 := pow_ne_one_of_lt_orderOf (by positivity) (by
      rw [hkj]
      exact Nat.pow_lt_pow_right (by norm_num) (Nat.sub_lt (Nat.pos_of_ne_zero hj0) one_pos))
    have hμk' : μ k' = 1 := by rw [hk', map_pow, hk, one_pow]
    have hc1 : (k'.1 : G) * k'.1 = 1 := congrArg (fun u => ((u.1 : ↥Z) : G)) hk'2
    have hc2 : (k'.2.1 : G) * k'.2.1 = 1 := congrArg (fun u => ((u.2.1 : ↥Z) : G)) hk'2
    have hc3 : (k'.2.2 : G) * k'.2.2 = 1 := congrArg (fun u => ((u.2.2 : ↥Z) : G)) hk'2
    have h0 := eq_one_of_mul_mul_eq_one hB haB hb₂B ha1 hb₂1 hb₂a hb₃1 hb₃a hb₃b hb₃ab
      (hZinv _ hc1) (hconj1 hg₂ _ hc2) (hconj1 hg₃ _ hc3) (congrArg Subtype.val hμk')
    apply hk'1
    refine Prod.ext (Subtype.ext h0.1) (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
    · have h2 := h0.2.1
      calc (k'.2.1 : G) = g₂ * (g₂⁻¹ * k'.2.1 * g₂) * g₂⁻¹ := by group
        _ = 1 := by rw [h2]; group
    · have h3 := h0.2.2
      calc (k'.2.2 : G) = g₃ * (g₃⁻¹ * k'.2.2 * g₃) * g₃⁻¹ := by group
        _ = 1 := by rw [h3]; group
  have hcard : Nat.card A = 64 := by
    have h := Nat.card_le_card_of_injective μ hμinj
    rw [Nat.card_prod, Nat.card_prod, hZ4] at h
    omega
  have hμbij : Function.Bijective μ := by
    rw [Nat.bijective_iff_injective_and_card]
    refine ⟨hμinj, ?_⟩
    rw [Nat.card_prod, Nat.card_prod, hZ4, hcard]
  let eμ : ↥Z × ↥Z × ↥Z ≃* ↥A := MulEquiv.ofBijective μ hμbij
  have hpre : ∀ t ∈ A, ∃ k, f k = t := fun t ht => by
    obtain ⟨k, hk⟩ := hμbij.2 ⟨t, ht⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  refine ⟨?_, ?_⟩
  · let eZ : Multiplicative (ZMod 4) ≃* ↥Z :=
      (ZMod.ringEquivCongr hZ4).toAddEquiv.toMultiplicative.symm.trans (zmodCyclicMulEquiv hZc)
    let e3 : Multiplicative (Fin 3 → ZMod 4) ≃*
        Multiplicative (ZMod 4) × Multiplicative (ZMod 4) × Multiplicative (ZMod 4) :=
      { toFun := fun v => (Multiplicative.ofAdd (Multiplicative.toAdd v 0),
          Multiplicative.ofAdd (Multiplicative.toAdd v 1),
          Multiplicative.ofAdd (Multiplicative.toAdd v 2))
        invFun := fun w => Multiplicative.ofAdd ![Multiplicative.toAdd w.1,
          Multiplicative.toAdd w.2.1, Multiplicative.toAdd w.2.2]
        left_inv := fun v => by
          funext i
          fin_cases i <;> rfl
        right_inv := fun w => rfl
        map_mul' := fun v w => rfl }
    exact ⟨(eμ.symm.trans (eZ.symm.prodCongr (eZ.symm.prodCongr eZ.symm))).trans e3.symm⟩
  · intro t ht htt
    obtain ⟨k, rfl⟩ := hpre t ht
    have hkk : k * k = 1 := by
      apply hμinj
      rw [map_mul, map_one]
      exact Subtype.ext (by rw [Subgroup.coe_mul, hμ, htt]; rfl)
    have hc1 : (k.1 : G) * k.1 = 1 := congrArg (fun u => ((u.1 : ↥Z) : G)) hkk
    have hc2 : (k.2.1 : G) * k.2.1 = 1 := congrArg (fun u => ((u.2.1 : ↥Z) : G)) hkk
    have hc3 : (k.2.2 : G) * k.2.2 = 1 := congrArg (fun u => ((u.2.2 : ↥Z) : G)) hkk
    have hmemB : ∀ {u c : G}, c ∈ B → (u = 1 ∨ u = c) → u ∈ B := by
      rintro u c hc (rfl | rfl)
      · exact one_mem B
      · exact hc
    exact mul_mem (mul_mem (hmemB haB (hZinv _ hc1)) (hmemB hb₂B (hconj1 hg₂ _ hc2)))
      (hmemB hb₃B (hconj1 hg₃ _ hc3))

theorem normalizer_le_of_inverts {T₁ T : Subgroup G} {c z : G}
    (hT : T = T₁ ⊔ zpowers c) (hcc : c * c = 1) (hinv : ∀ s ∈ T₁, c * s * c = s⁻¹)
    (hzT : z ∈ T₁) (hzz : z * z ≠ 1)
    (hsz : ∀ s ∈ T₁, s * s = 1 → (s * z) * (s * z) ≠ 1) :
    normalizer (T : Set G) ≤ normalizer (T₁ : Set G) := by
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
  have hcN : zpowers c ≤ normalizer (T₁ : Set G) := by
    rw [zpowers_le]
    refine mem_normalizer_of_map_le_self ?_
    rintro _ ⟨s, hs, rfl⟩
    show c * s * c⁻¹ ∈ T₁
    rw [hcinv, hinv s hs]
    exact inv_mem hs
  have hdec : ∀ t ∈ T, t ∈ T₁ ∨ ∃ s ∈ T₁, t = s * c := by
    intro t ht
    rw [hT] at ht
    have ht' : t ∈ ((T₁ : Set G) * (zpowers c : Set G)) := by
      rw [← coe_mul_of_right_le_normalizer_left T₁ (zpowers c) hcN]
      exact ht
    obtain ⟨s, hs, u, hu, rfl⟩ := ht'
    rcases eq_one_or_eq_of_mem_zpowers hcc hu with rfl | rfl
    · left
      simpa using hs
    · exact Or.inr ⟨s, hs, rfl⟩
  have hsc : ∀ s ∈ T₁, s * c * (s * c) = 1 := by
    intro s hs
    rw [show s * c * (s * c) = s * (c * s * c) by group, hinv s hs, mul_inv_cancel]
  have hT₁T : T₁ ≤ T := by rw [hT]; exact le_sup_left
  have hord : ∀ t ∈ T, t * t ≠ 1 → t ∈ T₁ := by
    intro t ht htt
    rcases hdec t ht with h | ⟨s, hs, rfl⟩
    · exact h
    · exact absurd (hsc s hs) htt
  intro n hn
  refine mem_normalizer_of_map_le_self ?_
  rintro _ ⟨s, hs, rfl⟩
  change n * s * n⁻¹ ∈ T₁
  have hconjT : ∀ u ∈ T₁, n * u * n⁻¹ ∈ T := fun u hu => (mem_normalizer_iff.mp hn u).mp (hT₁T hu)
  have hsq : ∀ u : G, n * u * n⁻¹ * (n * u * n⁻¹) = n * (u * u) * n⁻¹ := fun u => by group
  have hne : ∀ u ∈ T₁, u * u ≠ 1 → n * u * n⁻¹ ∈ T₁ := by
    intro u hu huu
    refine hord _ (hconjT u hu) ?_
    rw [hsq]
    intro h
    apply huu
    calc u * u = n⁻¹ * (n * (u * u) * n⁻¹) * n := by group
      _ = 1 := by rw [h]; group
  by_cases hss : s * s = 1
  · have h1 := hne _ (mul_mem hs hzT) (hsz s hs hss)
    have h2 := hne _ (inv_mem hzT) (by
      rw [← mul_inv_rev]
      intro h
      exact hzz (inv_eq_one.mp h))
    have := mul_mem h1 h2
    rwa [show n * (s * z) * n⁻¹ * (n * z⁻¹ * n⁻¹) = n * s * n⁻¹ by group] at this
  · exact hne s hs hss

end CFSG.ComponentClassification.GrSLit.GrS4
