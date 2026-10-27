module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEnd413Simple

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.HarrisEnd

open CFSG Subgroup

theorem quaternion_facts :
    (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 2 ≠ 1 ∧
      (QuaternionGroup.xa 0 : QuaternionGroup 2) ^ 2 ≠ 1 ∧
      (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 ≠
        QuaternionGroup.xa 0 * QuaternionGroup.a 1 ∧
      ∀ g : QuaternionGroup 2, g ^ 2 = 1 → g ≠ 1 → g = QuaternionGroup.a 2 := by
  decide

theorem nonempty_quaternion_sylow_of_equiv {A B : Type*} [Group A] [Group B] [Finite A]
    [Finite B] (hA : ∀ P : Sylow 2 A, Nonempty (QuaternionGroup 2 ≃* ↥P)) (e : A ≃* B)
    (P : Sylow 2 B) : Nonempty (QuaternionGroup 2 ≃* ↥P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs : Function.Surjective (e.symm : B →* A) := e.symm.surjective
  obtain ⟨f⟩ := hA (P.mapSurjective hs)
  exact ⟨f.trans ((MulEquiv.subgroupCongr (Sylow.coe_mapSurjective _ _)).trans
    ((P : Subgroup B).equivMapOfInjective (e.symm : B →* A) e.symm.injective).symm)⟩

theorem conj_eq_of_quaternion {G : Type*} [Group G] {R N : Subgroup G}
    (hRN : R ≤ normalizer (N : Set G)) (e : QuaternionGroup 2 ≃* ↥(R ⊓ N)) {z : G}
    (hz : z ∈ R ⊓ N) (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) {r : G} (hr : r ∈ R) :
    r * z * r⁻¹ = z := by
  have hmem : r * z * r⁻¹ ∈ R ⊓ N :=
    mem_inf.mpr ⟨mul_mem (mul_mem hr (mem_inf.mp hz).1) (inv_mem hr),
      (mem_normalizer_iff.mp (hRN hr) z).mp (mem_inf.mp hz).2⟩
  have hinv : ∀ y : ↥(R ⊓ N), (y : G) ^ 2 = 1 → (y : G) ≠ 1 → e.symm y = QuaternionGroup.a 2 := by
    intro y hy2 hy1
    refine quaternion_facts.2.2.2 _ ?_ ?_
    · rw [← map_pow, show y ^ 2 = 1 from Subtype.ext (by rw [Subgroup.coe_pow, hy2]; rfl),
        map_one]
    · intro h
      apply hy1
      rw [show y = 1 from e.symm.injective (by rw [h, map_one])]
      rfl
  have h1 := hinv ⟨_, hmem⟩ (by
      show (r * z * r⁻¹) ^ 2 = 1
      rw [sq, show r * z * r⁻¹ * (r * z * r⁻¹) = r * (z * z) * r⁻¹ by group, ← sq, hz2,
        mul_one, mul_inv_cancel]) (by
      intro h
      change r * z * r⁻¹ = 1 at h
      apply hz1
      calc z = r⁻¹ * (r * z * r⁻¹) * r := by group
        _ = 1 := by rw [h]; group)
  have h2 := hinv ⟨z, hz⟩ hz2 hz1
  rw [← h2] at h1
  exact congrArg Subtype.val (e.symm.injective h1)

theorem four_le_index {G : Type*} [Group G] [Finite G] {I : Subgroup G} {a b c : G}
    (ha : a ∉ I) (hb : b ∉ I) (hc : c ∉ I) (hab : a⁻¹ * b ∉ I) (hac : a⁻¹ * c ∉ I)
    (hbc : b⁻¹ * c ∉ I) : 4 ≤ I.index := by
  let e : Fin 4 → G := ![1, a, b, c]
  have hne : ∀ k l : Fin 4, k < l → (e k)⁻¹ * e l ∉ I := by
    intro k l hkl
    fin_cases k <;> fin_cases l
    all_goals first | exact absurd hkl (by decide) | skip
    · show (1 : G)⁻¹ * a ∉ I
      rwa [inv_one, one_mul]
    · show (1 : G)⁻¹ * b ∉ I
      rwa [inv_one, one_mul]
    · show (1 : G)⁻¹ * c ∉ I
      rwa [inv_one, one_mul]
    · exact hab
    · exact hac
    · exact hbc
  let f : Fin 4 → G ⧸ I := fun k => (e k : G ⧸ I)
  have hf : Function.Injective f := by
    intro k l hkl
    by_contra hkl'
    rcases lt_or_gt_of_ne hkl' with h | h
    · exact hne k l h (QuotientGroup.eq.mp hkl)
    · exact hne l k h (QuotientGroup.eq.mp hkl.symm)
  have h4 : Nat.card (Fin 4) ≤ I.index := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_eq_fintype_card, Fintype.card_fin] at h4

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup ↥(layer G)]

theorem le_card_of_outer {K : Subgroup G} (hKE : K ≤ layer G) (hK : ∃ a b : K, a * b ≠ b * a)
    {R Q : Subgroup G} (hQR : Q ≤ R) (hQE : Q ≤ layer G) (hQ8 : Nat.card Q = 8)
    {b : G} (hbR : b ∈ R) (hbC : b ∈ centralizer (layer G : Set G)) (hb1 : b ≠ 1)
    {tb xb : G} (htR : tb ∈ R) (hxR : xb ∈ R) (ht2 : tb ^ 2 = 1) (hxt : xb * tb = tb * xb)
    (htout : conjOn (layer G) tb ∉ innAut ↥(layer G))
    (hxout : conjOn (layer G) xb ∉ innAut ↥(layer G))
    (hxtout : conjOn (layer G) (xb * tb) ∉ innAut ↥(layer G)) : 64 ≤ Nat.card R := by
  set φ : ↥R →* MulAut ↥(layer G) := (conjOn (layer G)).comp R.subtype with hφ
  have hker : 2 ≤ Nat.card φ.ker := by
    have hb : (⟨b, hbR⟩ : ↥R) ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      exact conjOn_eq_one_iff.mpr hbC
    have hne : φ.ker ≠ ⊥ := fun h => hb1 (by
      have := (mem_bot).mp (h ▸ hb)
      exact congrArg Subtype.val this)
    exact (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
  have hCE := centralizer_inf_layer_eq_bot hKE hK
  set I := φ.range ⊓ innAut ↥(layer G) with hI
  have hQinj : Function.Injective (φ.comp (inclusion hQR)) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro q hq
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hq
    have h1 : (q : G) ∈ centralizer (layer G : Set G) ⊓ layer G :=
      mem_inf.mpr ⟨conjOn_eq_one_iff.mp hq, hQE q.2⟩
    rw [hCE, mem_bot] at h1
    exact (mem_bot).mpr (Subtype.ext h1)
  have hI8 : 8 ≤ Nat.card I := by
    have hle : (φ.comp (inclusion hQR)).range ≤ I := by
      rintro _ ⟨q, rfl⟩
      refine mem_inf.mpr ⟨⟨inclusion hQR q, rfl⟩, ?_⟩
      rw [MonoidHom.comp_apply]
      change conjOn (layer G) (q : G) ∈ _
      exact ⟨⟨q, hQE q.2⟩, MulEquiv.ext fun n => Subtype.ext (by
        rw [conjOn_apply, MulAut.conj_apply]; rfl)⟩
    have := Subgroup.card_le_of_le hle
    rwa [← Nat.card_congr (MonoidHom.ofInjective hQinj).toEquiv, hQ8] at this
  set τ := φ ⟨tb, htR⟩ with hτ
  set σ := φ ⟨xb, hxR⟩ with hσ
  have hτv : (τ : MulAut ↥(layer G)) = conjOn (layer G) tb := rfl
  have hσv : (σ : MulAut ↥(layer G)) = conjOn (layer G) xb := rfl
  have hτ2 : τ⁻¹ = τ := by
    rw [hτv, ← map_inv, show tb⁻¹ = tb from inv_eq_of_mul_eq_one_right (by rw [← sq, ht2])]
  have hστ : σ * τ = τ * σ := by rw [hτv, hσv, ← map_mul, ← map_mul, hxt]
  have hτR : τ ∈ φ.range := ⟨⟨tb, htR⟩, rfl⟩
  have hσR : σ ∈ φ.range := ⟨⟨xb, hxR⟩, rfl⟩
  have hστR : σ * τ ∈ φ.range := mul_mem hσR hτR
  have hidx : 4 ≤ (I.subgroupOf φ.range).index := by
    refine four_le_index (a := ⟨τ, hτR⟩) (b := ⟨σ, hσR⟩) (c := ⟨σ * τ, hστR⟩) ?_ ?_ ?_ ?_ ?_ ?_
    · exact fun h => htout (mem_inf.mp h).2
    · exact fun h => hxout (mem_inf.mp h).2
    · exact fun h => hxtout (by rw [map_mul]; exact (mem_inf.mp h).2)
    · intro h
      apply hxtout
      have h1 := (mem_inf.mp h).2
      change τ⁻¹ * σ ∈ _ at h1
      rwa [hτ2, ← hστ, hσv, hτv, ← map_mul] at h1
    · intro h
      apply hxout
      have h1 := (mem_inf.mp h).2
      change τ⁻¹ * (σ * τ) ∈ _ at h1
      have hττ : τ * τ = 1 := by
        calc τ * τ = τ⁻¹ * τ := by rw [hτ2]
          _ = 1 := inv_mul_cancel τ
      rwa [hτ2, ← mul_assoc, ← hστ, mul_assoc, hττ, mul_one] at h1
    · intro h
      apply htout
      have h1 := (mem_inf.mp h).2
      change σ⁻¹ * (σ * τ) ∈ _ at h1
      rwa [inv_mul_cancel_left] at h1
  have hrange : 32 ≤ Nat.card φ.range := by
    have h := (I.subgroupOf φ.range).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv] at h
    calc 32 = 8 * 4 := by norm_num
      _ ≤ Nat.card I * (I.subgroupOf φ.range).index := Nat.mul_le_mul hI8 hidx
      _ = Nat.card φ.range := h
  have h := Subgroup.card_ker_mul_card_range φ
  calc 64 = 2 * 32 := by norm_num
    _ ≤ Nat.card φ.ker * Nat.card φ.range := Nat.mul_le_mul hker hrange
    _ = Nat.card R := h

end CFSG.ComponentClassification.HarrisLit.HarrisEnd
