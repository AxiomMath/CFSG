module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.Goldschmidt.Steps.G3aGlue
public import CFSG.Goldschmidt75.OddCore
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup

variable {G : Type} [Group G]

theorem mem_of_fixedPointFree [Finite G] {R W : Subgroup G} {d : G}
    (hfree : ∀ r ∈ R, d⁻¹ * r * d = r → r = 1) (hWR : W ≤ R)
    (hdW : ∀ w ∈ W, d⁻¹ * w * d ∈ W) {r : G} (hr : r ∈ R)
    (hrW : r⁻¹ * (d⁻¹ * r * d) ∈ W) : r ∈ W := by
  have hinj : ∀ x ∈ R, ∀ y ∈ R, x⁻¹ * (d⁻¹ * x * d) = y⁻¹ * (d⁻¹ * y * d) → x = y := by
    intro x hx y hy h
    have h1 : d⁻¹ * (y * x⁻¹) * d = y * x⁻¹ := by
      calc d⁻¹ * (y * x⁻¹) * d = (d⁻¹ * y * d) * (d⁻¹ * x * d)⁻¹ := by group
        _ = y * (y⁻¹ * (d⁻¹ * y * d)) * (d⁻¹ * x * d)⁻¹ := by group
        _ = y * (x⁻¹ * (d⁻¹ * x * d)) * (d⁻¹ * x * d)⁻¹ := by rw [h]
        _ = y * x⁻¹ := by group
    have h2 := hfree _ (R.mul_mem hy (R.inv_mem hx)) h1
    rw [mul_inv_eq_one] at h2
    exact h2.symm
  let φ : W → W := fun w => ⟨(w : G)⁻¹ * (d⁻¹ * w * d), W.mul_mem (W.inv_mem w.2) (hdW w w.2)⟩
  have hφinj : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    exact hinj _ (hWR a.2) _ (hWR b.2) (congrArg Subtype.val hab)
  obtain ⟨w, hw⟩ := Finite.surjective_of_injective hφinj ⟨_, hrW⟩
  have h := hinj _ (hWR w.2) _ hr (congrArg Subtype.val hw)
  rw [← h]
  exact w.2

theorem exists_mul_of_fixedPointFree [Finite G] {R P V : Subgroup G} {d : G}
    (hPR : P ≤ centralizer (R : Set G)) (hdR : ∀ r ∈ R, d⁻¹ * r * d ∈ R)
    (hfree : ∀ r ∈ R, d⁻¹ * r * d = r → r = 1) (hdP : ∀ p ∈ P, d⁻¹ * p * d = p)
    (hVRP : V ≤ R ⊔ P) (hdV : ∀ v ∈ V, d⁻¹ * v * d ∈ V) {v : G} (hv : v ∈ V) :
    ∃ r ∈ V ⊓ R, ∃ p ∈ V ⊓ P, v = r * p := by
  have hPN : P ≤ normalizer (R : Set G) := hPR.trans (centralizer_le_normalizer _)
  have hv' : v ∈ ((P ⊔ R : Subgroup G) : Set G) := by rw [sup_comm]; exact hVRP hv
  rw [coe_mul_of_left_le_normalizer_right _ _ hPN] at hv'
  obtain ⟨p, hp, r, hr, rfl⟩ := hv'
  have hpr : p * r = r * p := (mem_centralizer_iff.mp (hPR hp) r hr).symm
  have hdp : d⁻¹ * p = p * d⁻¹ := by
    calc d⁻¹ * p = d⁻¹ * p * d * d⁻¹ := by group
      _ = p * d⁻¹ := by rw [hdP p hp]
  have e : r⁻¹ * (d⁻¹ * r * d) = (p * r)⁻¹ * (d⁻¹ * (p * r) * d) := by
    calc r⁻¹ * (d⁻¹ * r * d) = r⁻¹ * p⁻¹ * (p * d⁻¹) * r * d := by group
      _ = r⁻¹ * p⁻¹ * (d⁻¹ * p) * r * d := by rw [hdp]
      _ = (p * r)⁻¹ * (d⁻¹ * (p * r) * d) := by group
  have hW : r ∈ V ⊓ R := by
    refine mem_of_fixedPointFree hfree inf_le_right
      (fun w hw => mem_inf.mpr ⟨hdV w (mem_inf.mp hw).1, hdR w (mem_inf.mp hw).2⟩) hr ?_
    rw [e]
    refine mem_inf.mpr ⟨V.mul_mem (V.inv_mem hv) (hdV _ hv), ?_⟩
    rw [← e]
    exact R.mul_mem (R.inv_mem hr) (hdR r hr)
  have hpV : p ∈ V := by
    have := V.mul_mem hv (V.inv_mem (mem_inf.mp hW).1)
    simpa using this
  exact ⟨r, hW, p, mem_inf.mpr ⟨hpV, hp⟩, hpr⟩

theorem inf_sup_le_sup_inf {S K T : Subgroup G} [K.Normal] (hST : S ≤ T) :
    T ⊓ (S ⊔ K) ≤ S ⊔ (T ⊓ K) := by
  intro x hx
  have hx' : x ∈ ((S ⊔ K : Subgroup G) : Set G) := (mem_inf.mp hx).2
  rw [mul_normal] at hx'
  obtain ⟨s, hs, k, hk, rfl⟩ := hx'
  have hkT : k ∈ T := by
    have := mul_mem (inv_mem (hST hs)) (mem_inf.mp hx).1
    simpa using this
  exact mul_mem_sup hs (mem_inf.mpr ⟨hkT, hk⟩)

theorem inf_sup_le_of_disjoint [Finite G] (T : Sylow 2 G) {K C : Subgroup G} [K.Normal]
    (hKC : K ⊓ C = ⊥) (hCK : C ≤ centralizer (K : Set G)) :
    (T : Subgroup G) ⊓ (K ⊔ C) ≤ ((T : Subgroup G) ⊓ K) ⊔ ((T : Subgroup G) ⊓ C) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm : ∀ k ∈ K, ∀ c ∈ C, k * c = c * k := fun k hk c hc =>
    mem_centralizer_iff.mp (hCK hc) k hk
  have hTG : fusionIsSylowIn 2 (T : Subgroup G) ⊤ :=
    ⟨le_top, T.isPGroup', fun _ _ hP hTP => T.is_maximal' hP hTP⟩
  have hRK : fusionIsSylowIn 2 ((T : Subgroup G) ⊓ K) K :=
    G3a.fusionIsSylowIn_inf hTG le_top (Subgroup.normal_subgroupOf (N := K) (H := ⊤)).isSubnormal
  let Q : Subgroup G :=
    { carrier := {k | k ∈ K ∧ ∃ c ∈ C, k * c ∈ (T : Subgroup G)}
      mul_mem' := by
        rintro a b ⟨ha, c₁, hc₁, h₁⟩ ⟨hb, c₂, hc₂, h₂⟩
        refine ⟨K.mul_mem ha hb, c₁ * c₂, C.mul_mem hc₁ hc₂, ?_⟩
        have e : a * b * (c₁ * c₂) = a * c₁ * (b * c₂) := by
          rw [mul_assoc a b, ← mul_assoc b c₁, hcomm b hb c₁ hc₁]
          group
        rw [e]
        exact mul_mem h₁ h₂
      one_mem' := ⟨K.one_mem, 1, C.one_mem, by simp⟩
      inv_mem' := by
        rintro a ⟨ha, c, hc, h⟩
        refine ⟨K.inv_mem ha, c⁻¹, C.inv_mem hc, ?_⟩
        have e : a⁻¹ * c⁻¹ = (a * c)⁻¹ := by
          rw [mul_inv_rev, ← hcomm _ (K.inv_mem ha) _ (C.inv_mem hc)]
        rw [e]
        exact inv_mem h }
  have hQK : Q ≤ K := fun _ hx => hx.1
  have hQp : IsPGroup 2 Q := by
    rintro ⟨k, hk, c, hc, hkc⟩
    obtain ⟨n, hn⟩ := T.isPGroup' ⟨k * c, hkc⟩
    refine ⟨n, Subtype.ext ?_⟩
    have h1 : (k * c) ^ (2 ^ n) = 1 := congrArg Subtype.val hn
    have hkc' : Commute k c := hcomm k hk c hc
    rw [hkc'.mul_pow] at h1
    have h2 : k ^ (2 ^ n) ∈ K ⊓ C := by
      refine mem_inf.mpr ⟨K.pow_mem hk _, ?_⟩
      have : k ^ (2 ^ n) = (c ^ (2 ^ n))⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]
      exact C.inv_mem (C.pow_mem hc _)
    rw [hKC, mem_bot] at h2
    simpa using h2
  have hRQ : (T : Subgroup G) ⊓ K ≤ Q := fun x hx =>
    ⟨(mem_inf.mp hx).2, 1, C.one_mem, by rw [mul_one]; exact (mem_inf.mp hx).1⟩
  have hQeq : Q = (T : Subgroup G) ⊓ K := hRK.2.2 Q hQK hQp hRQ
  intro x hx
  have hx' : x ∈ ((K ⊔ C : Subgroup G) : Set G) := (mem_inf.mp hx).2
  rw [normal_mul] at hx'
  obtain ⟨k, hk, c, hc, rfl⟩ := hx'
  have hkQ : k ∈ Q := ⟨hk, c, hc, (mem_inf.mp hx).1⟩
  rw [hQeq] at hkQ
  have hcT : c ∈ (T : Subgroup G) := by
    have := mul_mem (inv_mem (mem_inf.mp hkQ).1) (mem_inf.mp hx).1
    simpa using this
  exact mul_mem_sup hkQ (mem_inf.mpr ⟨hcT, hc⟩)

theorem odd_index_of_le_comap_oddCore [Finite G] {N Q : Subgroup G} [N.Normal]
    (hQ : Q ≤ (goldschmidtOddCore (G ⧸ N)).comap (QuotientGroup.mk' N)) :
    Odd (N.subgroupOf Q).index := by
  let φ : Q →* G ⧸ N := (QuotientGroup.mk' N).comp Q.subtype
  have hker : φ.ker = N.subgroupOf Q := by
    ext x
    simp [φ, QuotientGroup.eq_one_iff, mem_subgroupOf]
  have hrange : φ.range ≤ goldschmidtOddCore (G ⧸ N) := by
    rintro _ ⟨x, rfl⟩
    exact hQ x.2
  rw [← hker, Subgroup.index_ker]
  exact Odd.of_dvd_nat odd_card_oddCore (Subgroup.card_dvd_of_le hrange)

end CFSG.Goldschmidt75
