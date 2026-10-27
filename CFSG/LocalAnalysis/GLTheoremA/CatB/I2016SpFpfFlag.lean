module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I2016SpFpfNil
public import CFSG.Quasithin.Recognition.Kleidman.F204.O2Alg

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2016Sp

open Module Polynomial CFSG.Quasithin.Kleidman.F204.O2Alg

theorem sq_trivial_on_flag {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (U : Submodule (ZMod 2) V) (hU4 : finrank (ZMod 2) U ≤ 4)
    (hQ4 : finrank (ZMod 2) (V ⧸ U) ≤ 4) (γ T : Module.End (ZMod 2) V) (hγ : γ ^ 2 + γ + 1 = 0)
    (hTγ : Commute T γ) (hUγ : ∀ u ∈ U, γ u ∈ U) (hUT : ∀ u ∈ U, T u ∈ U) (a : ℕ)
    (hT : T ^ (2 ^ a) = 1) :
    (∀ u ∈ U, T (T u) = u) ∧ (∀ v, T (T v) - v ∈ U) := by
  have hirr : ∀ c : ZMod 2, c ^ 2 + c + 1 ≠ 0 := by decide
  set N : Module.End (ZMod 2) V := T - 1 with hNdef
  have hNapply : ∀ v, N v = T v - v := fun v => by simp [hNdef]
  have hNpow : N ^ (2 ^ a) = 0 := by
    have h := sub_pow_char_pow (R := (ZMod 2)[X]) (p := 2) (n := a) (X : (ZMod 2)[X]) 1
    have h2 := congrArg (aeval T) h
    simp only [map_pow, map_sub, aeval_X, map_one, one_pow, hT, sub_self] at h2
    exact h2
  have hNγ : Commute N γ := hTγ.sub_left (Commute.one_left γ)
  have hUN : ∀ u ∈ U, N u ∈ U := fun u hu => by
    rw [hNapply]
    exact U.sub_mem (hUT u hu) hu
  have hsqU : ∀ u ∈ U, N (N u) = 0 := by
    let γU : Module.End (ZMod 2) U := γ.restrict hUγ
    let NU : Module.End (ZMod 2) U := N.restrict hUN
    have h1 : γU ^ 2 + γU + 1 = 0 := by
      refine LinearMap.ext fun u => Subtype.ext ?_
      have := LinearMap.congr_fun hγ (u : V)
      simpa [pow_two, γU, Module.End.mul_apply] using this
    have h2 : IsNilpotent NU := by
      refine ⟨2 ^ a, ?_⟩
      rw [Module.End.pow_restrict]
      refine LinearMap.ext fun u => Subtype.ext ?_
      simp [hNpow]
    have h3 : Commute NU γU := by
      refine LinearMap.ext fun u => Subtype.ext ?_
      have := LinearMap.congr_fun hNγ.eq (u : V)
      simpa [NU, γU, Module.End.mul_apply] using this
    have h4 := sq_eq_zero_of_commute_nilpotent hirr γU h1 hU4 NU h3 h2
    intro u hu
    have := LinearMap.congr_fun h4 ⟨u, hu⟩
    simpa [pow_two, NU, Module.End.mul_apply] using congrArg Subtype.val this
  have hsqQ : ∀ v, N (N v) ∈ U := by
    have hγQ : U ≤ U.comap γ := fun u hu => hUγ u hu
    have hNQ : U ≤ U.comap N := fun u hu => hUN u hu
    let γQ : Module.End (ZMod 2) (V ⧸ U) := U.mapQ U γ hγQ
    let NQ : Module.End (ZMod 2) (V ⧸ U) := U.mapQ U N hNQ
    have h1 : γQ ^ 2 + γQ + 1 = 0 := by
      refine LinearMap.ext fun q => ?_
      obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective U q
      have := LinearMap.congr_fun hγ v
      simp only [LinearMap.add_apply, Module.End.one_apply, pow_two, Module.End.mul_apply,
        LinearMap.zero_apply] at this ⊢
      show Submodule.Quotient.mk (γ (γ v)) + Submodule.Quotient.mk (γ v) + Submodule.Quotient.mk v = 0
      rw [← Submodule.Quotient.mk_add, ← Submodule.Quotient.mk_add, this]
      rfl
    have h2 : IsNilpotent NQ := by
      refine ⟨2 ^ a, ?_⟩
      have h5 : U.mapQ U (N ^ (2 ^ a)) (U.le_comap_pow_of_le_comap hNQ (2 ^ a)) = NQ ^ (2 ^ a) :=
        Submodule.mapQ_pow (p := U) hNQ (2 ^ a)
      rw [← h5]
      refine LinearMap.ext fun q => ?_
      obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective U q
      simp [Submodule.mapQ_apply, hNpow]
    have h3 : Commute NQ γQ := by
      refine LinearMap.ext fun q => ?_
      obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective U q
      have := LinearMap.congr_fun hNγ.eq v
      simp only [Module.End.mul_apply] at this ⊢
      show Submodule.Quotient.mk (N (γ v)) = Submodule.Quotient.mk (γ (N v))
      rw [this]
    have h4 := sq_eq_zero_of_commute_nilpotent hirr γQ h1 hQ4 NQ h3 h2
    intro v
    have := LinearMap.congr_fun h4 (Submodule.Quotient.mk v)
    have h5 : (Submodule.Quotient.mk (N (N v)) : V ⧸ U) = 0 := by
      simpa [pow_two, NQ, Module.End.mul_apply] using this
    exact (Submodule.Quotient.mk_eq_zero U).mp h5
  have hNN : ∀ v, N (N v) = T (T v) + v := fun v => by
    have h1 := add_self_eq_zero (T v)
    rw [hNapply (N v), hNapply v, map_sub]
    have h2 : T (T v) - T v - (T v - v) = T (T v) + v - (T v + T v) := by abel
    rw [h2, h1, sub_zero]
  refine ⟨fun u hu => ?_, fun v => ?_⟩
  · have h := hsqU u hu
    rw [hNN u] at h
    exact eq_of_add_eq_zero2 h
  · rw [sub_eq_add', ← hNN v]
    exact hsqQ v

theorem exists_normal_exp_two {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : G →* Module.End (ZMod 2) V) (hρ : Function.Injective ρ) (U : Submodule (ZMod 2) V)
    (hU : ∀ g, ∀ u ∈ U, ρ g u ∈ U) :
    ∃ K : Subgroup G, K.Normal ∧ (∀ k ∈ K, k ^ 2 = 1) ∧
      ∀ g : G, (∀ u ∈ U, ρ g (ρ g u) = u) → (∀ v, ρ g (ρ g v) - v ∈ U) → g ^ 2 ∈ K := by
  have hinv : ∀ g w, ρ g (ρ g⁻¹ w) = w := fun g w => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  have hinv' : ∀ g w, ρ g⁻¹ (ρ g w) = w := fun g w => by
    simpa using hinv g⁻¹ w
  let K : Subgroup G :=
    { carrier := {k | (∀ u ∈ U, ρ k u = u) ∧ ∀ v, ρ k v - v ∈ U}
      one_mem' := by
        refine ⟨fun u _ => by simp, fun v => by simp⟩
      mul_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        refine ⟨fun u hu => ?_, fun v => ?_⟩
        · rw [map_mul, Module.End.mul_apply, hb1 u hu, ha1 u hu]
        · rw [map_mul, Module.End.mul_apply]
          have := U.add_mem (ha2 (ρ b v)) (hb2 v)
          simpa using this
      inv_mem' := by
        rintro k ⟨hk1, hk2⟩
        have hfix : ∀ u ∈ U, ρ k⁻¹ u = u := fun u hu => by
          have := hinv' k u
          rwa [hk1 u hu] at this
        refine ⟨hfix, fun v => ?_⟩
        have ht := hk2 v
        have h1 : ρ k⁻¹ (ρ k v - v) = ρ k v - v := hfix _ ht
        rw [map_sub, hinv'] at h1
        have h2 : ρ k⁻¹ v - v = -(ρ k v - v) := by
          rw [← h1]
          abel
        rw [h2]
        exact U.neg_mem ht }
  have hmem : ∀ k, k ∈ K ↔ (∀ u ∈ U, ρ k u = u) ∧ ∀ v, ρ k v - v ∈ U := fun k => Iff.rfl
  have hnormal : K.Normal := ⟨fun k hk g => by
    obtain ⟨hk1, hk2⟩ := (hmem k).1 hk
    refine (hmem _).2 ⟨fun u hu => ?_, fun v => ?_⟩
    · rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hk1 _ (hU g⁻¹ u hu),
        hinv]
    · rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
      have := hU g _ (hk2 (ρ g⁻¹ v))
      rwa [map_sub, hinv] at this⟩
  refine ⟨K, hnormal, fun k hk => ?_, fun g hg1 hg2 => ?_⟩
  · obtain ⟨hk1, hk2⟩ := (hmem k).1 hk
    apply hρ
    rw [pow_two, map_mul, map_one]
    refine LinearMap.ext fun v => ?_
    rw [Module.End.mul_apply]
    have ht := hk2 v
    have h1 := hk1 _ ht
    rw [map_sub] at h1
    have h2 : ρ k (ρ k v) = (ρ k v - v) + ρ k v := by
      rw [← h1]
      abel
    rw [h2, sub_eq_add']
    have h3 := add_self_eq_zero (ρ k v)
    calc ρ k v + v + ρ k v = v + (ρ k v + ρ k v) := by abel
      _ = v := by rw [h3, add_zero]
  · refine (hmem _).2 ⟨fun u hu => ?_, fun v => ?_⟩
    · rw [pow_two, map_mul, Module.End.mul_apply]
      exact hg1 u hu
    · rw [pow_two, map_mul, Module.End.mul_apply]
      exact hg2 v

end CFSG.LocalAnalysis.GLTheoremA.I2016Sp

end
