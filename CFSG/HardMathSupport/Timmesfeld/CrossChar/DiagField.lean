module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Reduction

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance

section Chain

variable {M : Type*} [Group M]

theorem isSubnormal_subgroupOf_of_normalizes {A B C : Subgroup M} (hAB : A ≤ B) (_hBC : B ≤ C)
    (h1 : ∀ y ∈ B, ∀ a ∈ A, y * a * y⁻¹ ∈ A) (h2 : ∀ y ∈ C, ∀ b ∈ B, y * b * y⁻¹ ∈ B) :
    (A.subgroupOf C).IsSubnormal := by
  have hB : (B.subgroupOf C).IsSubnormal := by
    refine Subgroup.Normal.isSubnormal ⟨fun b hb g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hb ⊢
    simpa using h2 g.1 g.2 b.1 hb
  refine Subgroup.IsSubnormal.step _ _ (fun z hz => hAB hz) hB ⟨fun a ha g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at ha ⊢
  have ha' : (a : ↥C).1 ∈ A := ha
  simpa [Subgroup.mem_subgroupOf] using h1 g.1.1 g.2 (a : ↥C).1 ha'

end Chain

section Component

variable {K : Type*} [Group K] [Finite K] {p : ℕ}

omit [Finite K] in
theorem conj_mem_centralizer_iff_apply_eq (hinj : Function.Injective (MulAut.conj : K →* MulAut K))
    {x : MulAut K} {k : K} :
    MulAut.conj k ∈ Subgroup.centralizer ({x} : Set (MulAut K)) ↔ x k = k := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    apply hinj
    rw [← mul_conj_mul_inv, ← h, mul_inv_cancel_right]
  · intro h
    have := mul_conj_mul_inv x k
    rw [h, mul_inv_eq_iff_eq_mul] at this
    exact this.symm

theorem localDeltaIn_eq_bot_of_normal_quasisimple_fixSub (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : K →* MulAut K)) {H D : Subgroup (MulAut K)}
    (hH : innerAut K ≤ H) {x : MulAut K} (hx : x ∈ D) (hx1 : x ≠ 1) (T : Subgroup K)
    (hTx : ∀ t ∈ T, x t = t) (hTn : ∀ k : K, x k = k → ∀ t ∈ T, k * t * k⁻¹ ∈ T)
    (hTq : CFSG.IsQuasisimple T) (hTp : p ∣ Nat.card T)
    (hfaith : ∀ g : MulAut K, Nat.Coprime p (orderOf g) → (∀ t ∈ T, g t = t) → g = 1) :
    localDeltaIn p H D = ⊥ := by
  set Cx := Subgroup.centralizer ({x} : Set (MulAut K)) with hCx
  have hTC : T.map (MulAut.conj : K →* MulAut K) ≤ H ⊓ Cx := by
    rintro _ ⟨t, ht, rfl⟩
    exact Subgroup.mem_inf.2 ⟨hH ⟨t, rfl⟩, (conj_mem_centralizer_iff_apply_eq hinj).2 (hTx t ht)⟩
  refine localDeltaIn_eq_bot_of_faithful_component hp hinj hx hx1 T hTC ⟨?_, ?_⟩
    (fun h => (Nat.Prime.coprime_iff_not_dvd hp).1 h hTp) hfaith
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((T.equivMapOfInjective _ hinj).trans (Subgroup.subgroupOfEquivOfLe hTC).symm) hTq
  · refine isSubnormal_subgroupOf_of_normalizes (B := innerAut K ⊓ Cx) ?_ ?_ ?_ ?_
    · rintro _ ⟨t, ht, rfl⟩
      exact Subgroup.mem_inf.2 ⟨⟨t, rfl⟩, (conj_mem_centralizer_iff_apply_eq hinj).2 (hTx t ht)⟩
    · intro y hy
      exact Subgroup.mem_inf.2 ⟨hH (Subgroup.mem_inf.1 hy).1, (Subgroup.mem_inf.1 hy).2⟩
    · rintro y hy _ ⟨t, ht, rfl⟩
      obtain ⟨⟨k, rfl⟩, hk⟩ := Subgroup.mem_inf.1 hy
      refine ⟨k * t * k⁻¹, hTn k ((conj_mem_centralizer_iff_apply_eq hinj).1 hk) t ht, ?_⟩
      simp [map_mul, map_inv]
    · intro y hy b hb
      obtain ⟨⟨k, rfl⟩, hk⟩ := Subgroup.mem_inf.1 hb
      have hye := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hy).2
      have hke := Subgroup.mem_centralizer_singleton_iff.1 hk
      refine Subgroup.mem_inf.2 ⟨⟨y k, ?_⟩, ?_⟩
      · rw [← mul_conj_mul_inv]
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (((Commute.mul_left (show Commute y x from hye)
          (show Commute (MulAut.conj k) x from hke)).mul_left
          (show Commute y⁻¹ x from (show Commute y x from hye).inv_left)).eq)

theorem localDeltaIn_eq_bot_of_conj_normal_quasisimple_fixSub (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : K →* MulAut K)) {H D : Subgroup (MulAut K)}
    (hH : innerAut K ≤ H) {x : MulAut K} (hx : x ∈ D) (hx1 : x ≠ 1) (h y : MulAut K)
    (hxy : x = h * y * h⁻¹) (T : Subgroup K) (hTy : ∀ t ∈ T, y t = t)
    (hTn : ∀ k : K, y k = k → ∀ t ∈ T, k * t * k⁻¹ ∈ T)
    (hTq : CFSG.IsQuasisimple T) (hTp : p ∣ Nat.card T)
    (hfaith : ∀ g : MulAut K, Nat.Coprime p (orderOf g) → (∀ t ∈ T, g t = t) → g = 1) :
    localDeltaIn p H D = ⊥ := by
  have hyx : ∀ k : K, x k = k → y (h⁻¹ k) = h⁻¹ k := fun k hk => by
    have : x k = h (y (h⁻¹ k)) := by rw [hxy]; rfl
    rw [this] at hk
    exact h.injective (by rw [hk, MulAut.apply_inv_self])
  refine localDeltaIn_eq_bot_of_normal_quasisimple_fixSub hp hinj hH hx hx1
    (T.map (h : K →* K)) ?_ ?_ ?_ ?_ ?_
  · rintro _ ⟨t, ht, rfl⟩
    rw [hxy]
    change h (y (h⁻¹ (h t))) = h t
    rw [MulAut.inv_apply_self, hTy t ht]
  · rintro k hk _ ⟨t, ht, rfl⟩
    refine ⟨h⁻¹ k * t * (h⁻¹ k)⁻¹, hTn _ (hyx k hk) t ht, ?_⟩
    change h (h⁻¹ k * t * (h⁻¹ k)⁻¹) = k * h t * k⁻¹
    rw [map_mul, map_mul, map_inv, MulAut.apply_inv_self]
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (T.equivMapOfInjective (h : K →* K) h.injective) hTq
  · rwa [Subgroup.card_map_of_injective h.injective]
  · intro g hg hfix
    have hg' : Nat.Coprime p (orderOf (h⁻¹ * g * h)) := by
      have := MulEquiv.orderOf_eq (MulAut.conj h⁻¹) g
      rw [MulAut.conj_apply, inv_inv] at this
      rwa [this]
    have h1 : h⁻¹ * g * h = 1 := hfaith _ hg' fun t ht => by
      have h3 := hfix _ ⟨t, ht, rfl⟩
      change g (h t) = h t at h3
      change h⁻¹ (g (h t)) = t
      rw [h3, MulAut.inv_apply_self]
    calc g = h * (h⁻¹ * g * h) * h⁻¹ := by group
      _ = 1 := by rw [h1, mul_one, mul_inv_cancel]

end Component

end CFSG.HardMathSupport.Timmesfeld.CrossChar
