module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.L5Three.Transvection
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.L5Three.Regular
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.L5Three

open Module Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem exists_dual_pair {v w : V} (h : w ∉ Submodule.span (ZMod 2) {v}) :
    ∃ f : V →ₗ[ZMod 2] ZMod 2, f v = 0 ∧ f w = 1 := by
  obtain ⟨f, hfw, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem h inferInstance
  refine ⟨f, ?_, ?_⟩
  · have : f v ∈ Submodule.map f (Submodule.span (ZMod 2) {v}) :=
      Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self v)
    rw [hmap] at this
    simpa using this
  · revert hfw
    generalize f w = a
    revert a
    decide

theorem tvec_mem_kernel [Finite V] {v : V} (hv : v ≠ 0) (Kr : Subgroup (V ≃ₗ[ZMod 2] V))
    (h1 : ∀ g ∈ Kr, ∀ u, g u - u ∈ Submodule.span (ZMod 2) {v})
    (h2 : ∀ g ∈ Kr, ∀ w ∈ Submodule.span (ZMod 2) {v}, g w = w)
    (hfull : Nat.card Kr = 2 ^ (finrank (ZMod 2) (Submodule.span (ZMod 2) {v}) *
      finrank (ZMod 2) (V ⧸ Submodule.span (ZMod 2) {v})))
    (f : V →ₗ[ZMod 2] ZMod 2) (hf : f v = 0) : tvec v f hf ∈ Kr := by
  set W := Submodule.span (ZMod 2) {v} with hW
  have hker : W ≤ LinearMap.ker (f.smulRight (⟨v, Submodule.mem_span_singleton_self v⟩ : W)) := by
    intro u hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hu
    simp [LinearMap.mem_ker, hf]
  obtain ⟨g, hg, hgu⟩ := kernel_surj W Kr h1 h2 hfull (W.liftQ _ hker)
  convert hg using 1
  apply LinearEquiv.ext
  intro u
  have := hgu u
  simp only [Submodule.liftQ_apply, LinearMap.smulRight_apply] at this
  rw [tvec_apply]
  have h' : g u = u + f u • v := by
    have := congrArg (fun w => w + u) this
    simp only [sub_add_cancel] at this
    rw [this, add_comm]
    rfl
  exact h'.symm

theorem fixed_of_order_five [Finite V] (hV : Nat.card V = 32) {z : V ≃ₗ[ZMod 2] V}
    (hz : orderOf z = 5) {v : V} (hv : v ≠ 0) (hzv : z v = v) :
    ∀ u, z u = u → u = 0 ∨ u = v := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have hrank : finrank (ZMod 2) V = 5 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
    rw [Nat.card_zmod, hV] at h
    have h32 : (32 : ℕ) = 2 ^ 5 := by norm_num
    rw [h32] at h
    exact (Nat.pow_right_injective (le_refl 2) h).symm
  set K : Submodule (ZMod 2) V := LinearMap.ker ((z : V →ₗ[ZMod 2] V) - LinearMap.id) with hK
  have hmemK : ∀ u, u ∈ K ↔ z u = u := by
    intro u
    simp [hK, LinearMap.mem_ker, sub_eq_zero]
  have hp : IsPGroup 5 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])
  have h := hp.card_modEq_card_fixedPoints V
  have hset : MulAction.fixedPoints (Subgroup.zpowers z) V = (K : Set V) := by
    ext u
    rw [mem_fixedPoints_zpowers]
    exact (hmemK u).symm
  have hcardK :
      Nat.card (MulAction.fixedPoints (Subgroup.zpowers z) V) = 2 ^ finrank (ZMod 2) K := by
    rw [hset]
    show Nat.card K = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [hcardK, hV] at h
  have hd : finrank (ZMod 2) K ≤ 5 := hrank ▸ Submodule.finrank_le K
  have hd1 : finrank (ZMod 2) K = 1 := by
    interval_cases hk : finrank (ZMod 2) K
    · exact absurd h (by decide)
    · rfl
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exfalso
      have : K = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [hk, hrank])
      have hall : ∀ u, z u = u := fun u => (hmemK u).1 (this ▸ Submodule.mem_top)
      have : z = 1 := LinearEquiv.ext hall
      rw [this, orderOf_one] at hz
      omega
  have hcard2 : Nat.card K = 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hd1]; norm_num
  intro u hu
  have hvK : v ∈ K := (hmemK v).2 hzv
  have huK : u ∈ K := (hmemK u).2 hu
  obtain ⟨a, b, hab, huniv⟩ := Nat.card_eq_two_iff.1 hcard2
  by_cases hu0 : u = 0
  · exact Or.inl hu0
  · right
    have h1 : (⟨v, hvK⟩ : K) ∈ ({a, b} : Set K) := by rw [huniv]; trivial
    have h2 : (⟨u, huK⟩ : K) ∈ ({a, b} : Set K) := by rw [huniv]; trivial
    have h0 : (⟨0, K.zero_mem⟩ : K) ∈ ({a, b} : Set K) := by rw [huniv]; trivial
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 h2 h0
    have hne1 : (⟨u, huK⟩ : K) ≠ ⟨0, K.zero_mem⟩ := fun h => hu0 (congrArg Subtype.val h)
    have hne2 : (⟨v, hvK⟩ : K) ≠ ⟨0, K.zero_mem⟩ := fun h => hv (congrArg Subtype.val h)
    have : (⟨u, huK⟩ : K) = ⟨v, hvK⟩ := by
      rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
        first | exact h2.trans h1.symm | (exfalso; apply hne1; exact h2.trans h0.symm) |
          (exfalso; apply hne2; exact h1.trans h0.symm)
    exact congrArg Subtype.val this

theorem eq_one_of_commute_five [Finite V] (hV : Nat.card V = 32) {z : V ≃ₗ[ZMod 2] V}
    (hz : orderOf z = 5) {v : V} (hv : v ≠ 0) (hzv : z v = v) {k : V ≃ₗ[ZMod 2] V}
    (hk1 : ∀ u, k u - u ∈ Submodule.span (ZMod 2) {v}) (hkv : k v = v) (hcomm : k * z = z * k) :
    k = 1 := by
  have hfix := fixed_of_order_five hV hz hv hzv
  have hspan : ∀ w ∈ Submodule.span (ZMod 2) {v}, z w = w := by
    intro w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
    simp [hzv]
  have hd : ∀ u, k (z u) - z u = k u - u := by
    intro u
    have h1 : k (z u) = z (k u) := by
      have := congrArg (fun g : V ≃ₗ[ZMod 2] V => g u) hcomm
      exact this
    rw [h1, ← map_sub, hspan _ (hk1 u)]
  have hpow : ∀ i : ℕ, ∀ u, k ((z ^ i) u) - (z ^ i) u = k u - u := by
    intro i
    induction i with
    | zero => intro u; rfl
    | succ i ih =>
      intro u
      have : (z ^ (i + 1)) u = z ((z ^ i) u) := by rw [pow_succ']; rfl
      rw [this, hd, ih]
  have hz5 : z ^ 5 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz] at this
  apply LinearEquiv.ext
  intro u
  set σ : V := (z ^ 0) u + (z ^ 1) u + (z ^ 2) u + (z ^ 3) u + (z ^ 4) u with hσ
  have e : ∀ i : ℕ, z ((z ^ i) u) = (z ^ (i + 1)) u := fun i => by
    show (z * z ^ i) u = (z ^ (i + 1)) u
    rw [pow_succ']
  have e5 : (z ^ 5) u = (z ^ 0) u := by rw [hz5, pow_zero]
  have hzσ : z σ = σ := by
    simp only [hσ, map_add]
    rw [e 0, e 1, e 2, e 3, e 4]
    simp only [zero_add, Nat.reduceAdd]
    rw [e5]
    abel
  have hσmem := hfix σ hzσ
  have hdσ : k σ - σ = 0 := by
    rcases hσmem with h | h
    · rw [h]; simp
    · rw [h, hkv, sub_self]
  have hsum' : k σ - σ = (k ((z ^ 0) u) - (z ^ 0) u) + (k ((z ^ 1) u) - (z ^ 1) u) +
      (k ((z ^ 2) u) - (z ^ 2) u) + (k ((z ^ 3) u) - (z ^ 3) u) + (k ((z ^ 4) u) - (z ^ 4) u) := by
    simp only [hσ, map_add]
    abel
  have hsum : k σ - σ = (k u - u) + (k u - u) + (k u - u) + (k u - u) + (k u - u) := by
    rw [hsum', hpow 0 u, hpow 1 u, hpow 2 u, hpow 3 u, hpow 4 u]
  rw [hdσ] at hsum
  have h2u := add_self_vec (k u - u)
  have : k u - u = 0 := by
    have e1 : (k u - u) + (k u - u) + (k u - u) + (k u - u) + (k u - u)
        = ((k u - u) + (k u - u)) + ((k u - u) + (k u - u)) + (k u - u) := by abel
    rw [e1, h2u] at hsum
    simpa using hsum.symm
  exact sub_eq_zero.1 this

end CFSG.AGLEmbeddingD2.McLaughlin.L5Three
