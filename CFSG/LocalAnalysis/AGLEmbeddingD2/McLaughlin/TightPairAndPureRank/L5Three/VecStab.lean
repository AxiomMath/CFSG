module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.L5Three.VecStab1
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.L5Three.Dim34
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.L5Three.FreeAction

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.L5Three

open Module Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem exists_stab_data {q : ℕ} [Fact q.Prime] (hVc : Nat.card V = q + 1)
    {Y : Subgroup (V ≃ₗ[ZMod 2] V)} {x : V ≃ₗ[ZMod 2] V} (hxY : x ∈ Y) (hx : orderOf x = q)
    {v : V} (hv : v ≠ 0) :
    ∃ Yv : Subgroup (V ≃ₗ[ZMod 2] V), Yv ≤ Y ∧ (∀ g ∈ Yv, g v = v) ∧
      Nat.card Y = q * Nat.card Yv := by
  let S := MulAction.stabilizer Y v
  have horb : MulAction.orbit Y v = {w : V | w ≠ 0} := by
    ext w
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨g, rfl⟩ h
      exact hv ((g : V ≃ₗ[ZMod 2] V).injective (by rw [map_zero]; exact h))
    · intro hw
      obtain ⟨k, -, hk⟩ := regular_action hVc hx hv hw
      exact ⟨⟨x ^ k, Subgroup.pow_mem Y hxY k⟩, hk⟩
  have hidx : S.index = q := by
    rw [MulAction.index_stabilizer, horb]
    have : ({w : V | w ≠ 0} : Set V) = (Set.univ : Set V) \ {0} := by ext; simp
    rw [this, Set.ncard_sdiff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ, hVc]
    omega
  refine ⟨S.map Y.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨s, -, rfl⟩; exact s.2
  · rintro _ ⟨s, hs, rfl⟩
    exact hs
  · rw [Subgroup.card_map_of_injective Subtype.coe_injective, ← Subgroup.index_mul_card S, hidx]

theorem le_stab_span {Yv : Subgroup (V ≃ₗ[ZMod 2] V)} {v : V} (h : ∀ g ∈ Yv, g v = v) :
    Yv ≤ stab (Submodule.span (ZMod 2) {v}) := by
  intro g hg w
  have hgv := h g hg
  have hgiv : g.symm v = v := by
    have := congrArg (fun u => g.symm u) hgv
    simpa using this.symm
  constructor
  · intro hw
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hw
    have : w = c • v := by
      calc w = g.symm (g w) := by simp
        _ = g.symm (c • v) := by rw [← hc]
        _ = c • v := by rw [map_smul, hgiv]
    exact Submodule.mem_span_singleton.2 ⟨c, this.symm⟩
  · intro hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
    rw [map_smul, hgv]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)

theorem sq_eq_one_of_kernel {v : V} {k : V ≃ₗ[ZMod 2] V}
    (hk1 : ∀ u, k u - u ∈ Submodule.span (ZMod 2) {v}) (hkv : k v = v) : k ^ 2 = 1 := by
  apply LinearEquiv.ext
  intro u
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hk1 u)
  have h1 : k u = u + c • v := by rw [hc]; abel
  change k (k u) = u
  rw [h1, map_add, map_smul, hkv, hc]
  calc k u + (k u - u) = (k u + k u) - u := by abel
    _ = 0 - u := by rw [add_self_vec]
    _ = u := by rw [zero_sub]; exact neg_eq_of_add_eq_zero_right (add_self_vec u)

theorem kill_4960_158720 (hV : finrank (ZMod 2) V = 5) {Y : Subgroup (V ≃ₗ[ZMod 2] V)}
    (h3 : ¬ 3 ∣ Nat.card Y) (hcard : Nat.card Y = 4960 ∨ Nat.card Y = 158720) : False := by
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have hVc : Nat.card V = 31 + 1 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hV]; norm_num
  have : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  have h31 : 31 ∣ Nat.card Y := by rcases hcard with h | h <;> rw [h] <;> norm_num
  obtain ⟨x₀, hx₀⟩ := exists_prime_orderOf_dvd_card' (G := Y) 31 h31
  set x : V ≃ₗ[ZMod 2] V := (x₀ : V ≃ₗ[ZMod 2] V) with hxdef
  have hx : orderOf x = 31 := (Subgroup.orderOf_coe x₀).trans hx₀
  obtain ⟨v, hv⟩ : ∃ v : V, v ≠ 0 := by
    have : 0 < finrank (ZMod 2) V := by omega
    exact Module.finrank_pos_iff_exists_ne_zero.1 this
  obtain ⟨Yv, hYvY, hYvfix, hYvcard⟩ := exists_stab_data hVc x₀.2 hx hv
  set W : Submodule (ZMod 2) V := Submodule.span (ZMod 2) {v} with hWdef
  have hWk : finrank (ZMod 2) W = 1 := finrank_span_singleton hv
  have hq : finrank (ZMod 2) (V ⧸ W) = 4 := by
    have := Submodule.finrank_quotient_add_finrank W
    omega
  have hYv3 : ¬ 3 ∣ Nat.card Yv := fun h => h3 (hYvcard ▸ Dvd.dvd.mul_left h 31)
  have : Finite W := inferInstance
  have : Finite (V ⧸ W) := Quotient.finite _
  obtain ⟨Kr, hKrY, h1, h2, hconj, hbound⟩ := card_stab_le W (le_stab_span hYvfix)
    (a := 1) (b := 64) (fun Z hZ => threeBound_one W hWk Z hZ) (fun Z hZ => threeBound_four (V ⧸ W) hq Z hZ) hYv3
  have hK16 := card_kernel_le W Kr h1 h2
  rw [hWk, hq] at hK16
  norm_num at hK16
  rcases hcard with hc | hc
  · have hYv : Nat.card Yv = 160 := by omega
    have hKr3 : 3 ≤ Nat.card Kr := by omega
    have hp2 : IsPGroup 2 Kr := fun k =>
      ⟨1, Subtype.ext (by simpa using sq_eq_one_of_kernel (h1 k.1 k.2) (h2 k.1 k.2 v
        (Submodule.mem_span_singleton_self v)))⟩
    obtain ⟨m, hm⟩ := hp2.exists_card_eq
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨z₀, hz₀⟩ := exists_prime_orderOf_dvd_card' (G := Yv) 5 (by rw [hYv]; norm_num)
    set z : V ≃ₗ[ZMod 2] V := (z₀ : V ≃ₗ[ZMod 2] V) with hzdef
    have hz : orderOf z = 5 := (Subgroup.orderOf_coe z₀).trans hz₀
    have hz5 : z ^ 5 = 1 := by
      have := pow_orderOf_eq_one z
      rwa [hz] at this
    have hzv : z v = v := hYvfix z z₀.2
    have hV32 : Nat.card V = 32 := by rw [hVc]
    have hKfree : ∀ k ∈ Kr, k ≠ 1 → z * k * z⁻¹ ≠ k := by
      intro k hk hk1 hzk
      apply hk1
      refine eq_one_of_commute_five hV32 hz hv hzv (h1 k hk) (h2 k hk v
        (Submodule.mem_span_singleton_self v)) ?_
      calc k * z = (z * k * z⁻¹) * z := by rw [hzk]
        _ = z * k := by group
    have hT : ∀ t ∈ ({k | k ∈ Kr ∧ k ≠ 1} : Set (V ≃ₗ[ZMod 2] V)), z * t * z⁻¹ ∈
        ({k | k ∈ Kr ∧ k ≠ 1} : Set (V ≃ₗ[ZMod 2] V)) := by
      rintro t ⟨htK, ht1⟩
      refine ⟨hconj z z₀.2 t htK, fun h => ht1 ?_⟩
      have : t = z⁻¹ * 1 * z := by rw [← h]; group
      simpa using this
    have hdvd := prime_dvd_ncard_of_free (p := 5) hz5 _ hT (fun t ⟨htK, ht1⟩ => hKfree t htK ht1)
    have hcardT : ({k | k ∈ Kr ∧ k ≠ 1} : Set (V ≃ₗ[ZMod 2] V)).ncard = Nat.card Kr - 1 := by
      have : ({k | k ∈ Kr ∧ k ≠ 1} : Set (V ≃ₗ[ZMod 2] V)) = (Kr : Set _) \ {1} := by
        ext t; simp
      rw [this, Set.ncard_sdiff_singleton_of_mem Kr.one_mem, ← Nat.card_coe_set_eq]
      rfl
    rw [hcardT] at hdvd
    have hKr16 : Nat.card Kr = 16 := by
      rw [hm] at hdvd hK16 hKr3 ⊢
      have hm4 : m ≤ 4 := by
        by_contra hm4
        push Not at hm4
        have : 2 ^ 5 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm4
        omega
      interval_cases m <;> omega
    have hfull : Nat.card Kr = 2 ^ (finrank (ZMod 2) W * finrank (ZMod 2) (V ⧸ W)) := by
      rw [hWk, hq, hKr16]; norm_num
    have htv : ∀ (f : V →ₗ[ZMod 2] ZMod 2) (hf : f v = 0), tvec v f hf ∈ Kr :=
      fun f hf => tvec_mem_kernel hv Kr h1 h2 hfull f hf
    set w : V := x v with hw
    have hwne : w ≠ v := fun h => hv (no_fixed_of_prime_order hVc hx h)
    have hw0 : w ≠ 0 := fun h => hv (x.injective (by rw [map_zero]; exact h))
    have hwspan : w ∉ W := by
      intro hmem
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
      have hc01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
      rcases hc01 c with rfl | rfl
      · apply hw0; rw [← hc]; simp
      · apply hwne; rw [← hc]; simp
    obtain ⟨f, hfv, hfw⟩ := exists_dual_pair hwspan
    have hxinv : x.symm v ≠ v := fun h => hwne (by
      have := congrArg (fun u => x u) h
      simpa using this.symm)
    have hxinv0 : x.symm v ≠ 0 := fun h => hv (x.symm.injective (by rw [map_zero]; exact h))
    have hxspan : x.symm v ∉ W := by
      intro hmem
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
      have hc01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
      rcases hc01 c with rfl | rfl
      · apply hxinv0; rw [← hc]; simp
      · apply hxinv; rw [← hc]; simp
    obtain ⟨f2, hf2v, hf2y⟩ := exists_dual_pair hxspan
    set g : V →ₗ[ZMod 2] ZMod 2 := f2.comp (x.symm : V ≃ₗ[ZMod 2] V).toLinearMap with hg
    have hgw : g w = 0 := by simp [hg, hw, hf2v]
    have hgv : g v = 1 := by simp [hg, hf2y]
    have ht1 := htv f hfv
    have ht2' := htv f2 hf2v
    have hxY : x ∈ Y := x₀.2
    have hKrYv : Kr ≤ Y := hKrY.trans hYvY
    have ht2Y : x * tvec v f2 hf2v * x⁻¹ ∈ Y :=
      Y.mul_mem (Y.mul_mem hxY (hKrYv ht2')) (Y.inv_mem hxY)
    have ht2 : x * tvec v f2 hf2v * x⁻¹ = tvec w g hgw := by
      apply LinearEquiv.ext
      intro u
      show x (tvec v f2 hf2v (x.symm u)) = tvec w g hgw u
      simp only [tvec_apply, map_add, map_smul, hg, LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [LinearEquiv.apply_symm_apply]
    have haY : tvec v f hfv * tvec w g hgw ∈ Y := by
      rw [← ht2]; exact Y.mul_mem (hKrYv ht1) ht2Y
    have hord := orderOf_tvec_mul v w f g hfv hgw hfw hgv
    have hdvd : orderOf (⟨tvec v f hfv * tvec w g hgw, haY⟩ : Y) ∣ Nat.card Y :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hord] at hdvd
    exact h3 hdvd
  · have hYv : Nat.card Yv = 5120 := by omega
    omega

end CFSG.AGLEmbeddingD2.McLaughlin.L5Three
