module

public import CFSG.ClassicalInvolution.Q3.Q3MTG2Pair
public import CFSG.ClassicalInvolution.ModelFacts.G2D4TD4Struct
public import CFSG.ClassicalInvolution.ModelFacts.CF3A
public import CFSG.LieType.HighestRoot.CentTrialityFixed

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3MT

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.ClassicalInvolution.G2D4Models
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.ModelFacts
open scoped MatrixGroups


section Tuple

variable {K : Type} [Field K]

@[expose] def td4ShortTuple (w w₁ w₂ : Kˣ) : Fin d4.rank → Kˣ :=
  fun j => w ^ d4.cartan (nd 0) j * w₁ ^ d4.cartan (nd 1) j * w₂ ^ d4.cartan (nd 3) j

theorem td4ShortTuple_zero (w w₁ w₂ : Kˣ) : td4ShortTuple w w₁ w₂ (nd 0) = w ^ 2 := by
  have c1 : d4.cartan (nd 0) (nd 0) = 2 := by decide
  have c2 : d4.cartan (nd 1) (nd 0) = 0 := by decide
  have c3 : d4.cartan (nd 3) (nd 0) = 0 := by decide
  simp only [td4ShortTuple, c1, c2, c3]
  simp

theorem td4ShortTuple_one (w w₁ w₂ : Kˣ) : td4ShortTuple w w₁ w₂ (nd 1) = w₁ ^ 2 := by
  have c1 : d4.cartan (nd 0) (nd 1) = 0 := by decide
  have c2 : d4.cartan (nd 1) (nd 1) = 2 := by decide
  have c3 : d4.cartan (nd 3) (nd 1) = 0 := by decide
  simp only [td4ShortTuple, c1, c2, c3]
  simp

theorem td4ShortTuple_two (w w₁ w₂ : Kˣ) :
    td4ShortTuple w w₁ w₂ (nd 2) = (w * w₁ * w₂)⁻¹ := by
  have c1 : d4.cartan (nd 0) (nd 2) = -1 := by decide
  have c2 : d4.cartan (nd 1) (nd 2) = -1 := by decide
  have c3 : d4.cartan (nd 3) (nd 2) = -1 := by decide
  simp only [td4ShortTuple, c1, c2, c3]
  apply Units.ext
  simp [Units.val_mul]
  field_simp

theorem td4ShortTuple_three (w w₁ w₂ : Kˣ) : td4ShortTuple w w₁ w₂ (nd 3) = w₂ ^ 2 := by
  have c1 : d4.cartan (nd 0) (nd 3) = 0 := by decide
  have c2 : d4.cartan (nd 1) (nd 3) = 0 := by decide
  have c3 : d4.cartan (nd 3) (nd 3) = 2 := by decide
  simp only [td4ShortTuple, c1, c2, c3]
  simp

theorem weylTuple_td4Short_zero (w w₁ w₂ : Kˣ) :
    weylTuple tdNhat (td4ShortTuple w w₁ w₂) (nd 0) = w₁ * w₂ * w⁻¹ := by
  show rootChar (td4ShortTuple w w₁ w₂) (tdNhat⁻¹ • (Pi.single (nd 0) 1 : Fin d4.rank → ℤ)) = _
  rw [tdNhat_inv_smul_zero, rootChar_four, td4ShortTuple_zero, td4ShortTuple_one,
    td4ShortTuple_two, td4ShortTuple_three]
  have e0 : (vd4 (-1) 0 (-1) 0) (nd 0) = -1 := rfl
  have e1 : (vd4 (-1) 0 (-1) 0) (nd 1) = 0 := rfl
  have e2 : (vd4 (-1) 0 (-1) 0) (nd 2) = -1 := rfl
  have e3 : (vd4 (-1) 0 (-1) 0) (nd 3) = 0 := rfl
  rw [e0, e1, e2, e3]
  apply Units.ext
  simp
  field_simp

theorem weylTuple_td4Short_one (w w₁ w₂ : Kˣ) :
    weylTuple tdNhat (td4ShortTuple w w₁ w₂) (nd 1) = w * w₂ * w₁⁻¹ := by
  show rootChar (td4ShortTuple w w₁ w₂) (tdNhat⁻¹ • (Pi.single (nd 1) 1 : Fin d4.rank → ℤ)) = _
  rw [tdNhat_inv_smul_one, rootChar_four, td4ShortTuple_zero, td4ShortTuple_one,
    td4ShortTuple_two, td4ShortTuple_three]
  have e0 : (vd4 0 (-1) (-1) 0) (nd 0) = 0 := rfl
  have e1 : (vd4 0 (-1) (-1) 0) (nd 1) = -1 := rfl
  have e2 : (vd4 0 (-1) (-1) 0) (nd 2) = -1 := rfl
  have e3 : (vd4 0 (-1) (-1) 0) (nd 3) = 0 := rfl
  rw [e0, e1, e2, e3]
  apply Units.ext
  simp
  field_simp

theorem weylTuple_td4Short_two (w w₁ w₂ : Kˣ) :
    weylTuple tdNhat (td4ShortTuple w w₁ w₂) (nd 2) = 1 := by
  show rootChar (td4ShortTuple w w₁ w₂) (tdNhat⁻¹ • (Pi.single (nd 2) 1 : Fin d4.rank → ℤ)) = _
  rw [tdNhat_inv_smul_two, rootChar_four, td4ShortTuple_zero, td4ShortTuple_one,
    td4ShortTuple_two, td4ShortTuple_three]
  have e0 : (vd4 1 1 2 1) (nd 0) = 1 := rfl
  have e1 : (vd4 1 1 2 1) (nd 1) = 1 := rfl
  have e2 : (vd4 1 1 2 1) (nd 2) = 2 := rfl
  have e3 : (vd4 1 1 2 1) (nd 3) = 1 := rfl
  rw [e0, e1, e2, e3]
  apply Units.ext
  simp
  field_simp

theorem weylTuple_td4Short_three (w w₁ w₂ : Kˣ) :
    weylTuple tdNhat (td4ShortTuple w w₁ w₂) (nd 3) = w * w₁ * w₂⁻¹ := by
  show rootChar (td4ShortTuple w w₁ w₂) (tdNhat⁻¹ • (Pi.single (nd 3) 1 : Fin d4.rank → ℤ)) = _
  rw [tdNhat_inv_smul_three, rootChar_four, td4ShortTuple_zero, td4ShortTuple_one,
    td4ShortTuple_two, td4ShortTuple_three]
  have e0 : (vd4 0 0 (-1) (-1)) (nd 0) = 0 := rfl
  have e1 : (vd4 0 0 (-1) (-1)) (nd 1) = 0 := rfl
  have e2 : (vd4 0 0 (-1) (-1)) (nd 2) = -1 := rfl
  have e3 : (vd4 0 0 (-1) (-1)) (nd 3) = -1 := rfl
  rw [e0, e1, e2, e3]
  apply Units.ext
  simp
  field_simp

end Tuple

section Torus

variable {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem twistedIncl_slB_HSL (w : Kˣ) :
    twistedIncl σ (slB σ hσ (HSL w)) = rootDiagUnit d4
      (weylTuple tdNhat (td4ShortTuple w (Units.map σ.toMonoidHom w)
        (Units.map σ.toMonoidHom (Units.map σ.toMonoidHom w)))) := by
  rw [twistedIncl_slB, twistedIncl_slShort_HSL hσ w]
  exact canonicalRep_conj_rootDiagUnit tdNhat _

theorem zpow_eq_zpow_of_dvd_sub {G : Type*} [Group G] {x : G} {n : ℕ} (h : x ^ n = 1) {a b : ℤ}
    (hab : (n : ℤ) ∣ a - b) : x ^ a = x ^ b := by
  obtain ⟨k, hk⟩ := hab
  have : a = b + n * k := by omega
  rw [this, zpow_add, zpow_mul, zpow_natCast, h, one_zpow, mul_one]

include hσ in
theorem sq_eq_slB_HSL [Finite K] (hσ3 : ∀ c, σ c = c ^ 3) (hK : Nat.card K = 27)
    {t : twistedGroup σ} (ht : t ∈ TK σ) : ∃ w : Kˣ, t * t = slB σ hσ (HSL w) := by
  obtain ⟨b, hb⟩ := ht
  obtain ⟨c1, c3, -, c2⟩ := torus_compat hb
  set x : Kˣ := b (nd 0) with hx
  have hσu : ∀ y : Kˣ, Units.map σ.toMonoidHom y = y ^ 3 := fun y => Units.ext (by simp [hσ3])
  have h26 : x ^ 26 = 1 := by
    have h := pow_card_eq_one' (G := Kˣ) (x := x)
    rwa [Nat.card_units, hK] at h
  have hb1 : b (nd 1) = x ^ 3 := Units.ext (by rw [c1, hσ3]; simp [hx])
  have hb3 : b (nd 3) = x ^ 9 := Units.ext (by
    rw [c3, hσ3, c1, hσ3]
    simp [hx]
    ring)
  have hb2 : b (nd 2) * b (nd 2) = 1 := by
    apply Units.ext
    have h : ((b (nd 2) : Kˣ) : K) = (b (nd 2) : K) ^ 3 := by rw [← hσ3]; exact c2
    have hne : ((b (nd 2) : Kˣ) : K) ≠ 0 := (b (nd 2)).ne_zero
    have h0 : ((b (nd 2) : Kˣ) : K) * (((b (nd 2) : Kˣ) : K) * ((b (nd 2) : Kˣ) : K) - 1) = 0 := by
      linear_combination (-1 : K) * h
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd h1 hne
    · rw [Units.val_mul, Units.val_one]
      linear_combination h1
  refine ⟨x ^ 12, ?_⟩
  apply twistedIncl_injective σ
  rw [map_mul, hb, twistedIncl_slB_HSL hσ, ← rootDiagUnit_mul]
  congr 1
  funext j
  simp only [hσu]
  fin_cases j
  · show b (nd 0) * b (nd 0) = _
    rw [weylTuple_td4Short_zero]
    calc b (nd 0) * b (nd 0) = x ^ (2 : ℤ) := (zpow_two x).symm
      _ = x ^ (132 : ℤ) := zpow_eq_zpow_of_dvd_sub h26 (by norm_num)
      _ = _ := by group
  · show b (nd 1) * b (nd 1) = _
    rw [weylTuple_td4Short_one, hb1]
    calc x ^ 3 * x ^ 3 = x ^ (6 : ℤ) := by group
      _ = x ^ (84 : ℤ) := zpow_eq_zpow_of_dvd_sub h26 (by norm_num)
      _ = _ := by group
  · show b (nd 2) * b (nd 2) = _
    rw [weylTuple_td4Short_two, hb2]
  · show b (nd 3) * b (nd 3) = _
    rw [weylTuple_td4Short_three, hb3]
    calc x ^ 9 * x ^ 9 = x ^ (18 : ℤ) := by group
      _ = x ^ (-60 : ℤ) := zpow_eq_zpow_of_dvd_sub h26 (by norm_num)
      _ = _ := by group

end Torus

section Prod

variable {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

@[expose] noncomputable def td4ProdRange : Subgroup (twistedGroup σ) :=
  ((slLong σ hσ).noncommCoprod (slB σ hσ) (fun A B => slLong_comm_slB hσ A B)).range

theorem mem_td4ProdRange {x : twistedGroup σ} :
    x ∈ td4ProdRange hσ ↔ ∃ (A : SL(2, fixedField σ)) (B : SL(2, K)),
      slLong σ hσ A * slB σ hσ B = x :=
  ⟨fun ⟨⟨A, B⟩, h⟩ => ⟨A, B, h⟩, fun ⟨A, B, h⟩ => ⟨(A, B), h⟩⟩

theorem TK_conj_mem_td4ProdRange {t : twistedGroup σ} (ht : t ∈ TK σ) {s : twistedGroup σ}
    (hs : s ∈ td4ProdRange hσ) : t * s * t⁻¹ ∈ td4ProdRange hσ := by
  obtain ⟨A, B, rfl⟩ := (mem_td4ProdRange hσ).mp hs
  obtain ⟨A', hA'⟩ := TK_conj_slLong hσ ht A
  obtain ⟨B', hB'⟩ := TK_conj_slB hσ ht B
  refine (mem_td4ProdRange hσ).mpr ⟨A', B', ?_⟩
  rw [← hA', ← hB']
  group

include hσ in
theorem sq_mem_td4ProdRange [Finite K] (hσ3 : ∀ c, σ c = c ^ 3) (hK : Nat.card K = 27)
    (hK1 : (-1 : Kˣ) ≠ 1) (hC₀ : graphFixedRootGroup TwistTag.D4 K σ ≤ (twistedIncl σ).range)
    (hgF : ∀ g : twistedGroup σ, twistedIncl σ g ∈ graphFixedRootGroup TwistTag.D4 K σ)
    {x : twistedGroup σ} (hx : x * slLong σ hσ (-1) = slLong σ hσ (-1) * x) :
    x * x ∈ td4ProdRange hσ := by
  obtain ⟨t, ht, A, B, rfl⟩ := mem_SProd_of_centralizes hσ hK1 hC₀ hgF hx
  obtain ⟨w, hw⟩ := sq_eq_slB_HSL hσ hσ3 hK ht
  have hs : slLong σ hσ A * slB σ hσ B ∈ td4ProdRange hσ := (mem_td4ProdRange hσ).mpr ⟨A, B, rfl⟩
  have hconj : t⁻¹ * (slLong σ hσ A * slB σ hσ B) * t ∈ td4ProdRange hσ := by
    have := TK_conj_mem_td4ProdRange hσ (inv_mem ht) hs
    simpa using this
  have hsq : t * t ∈ td4ProdRange hσ :=
    (mem_td4ProdRange hσ).mpr ⟨1, HSL w, by rw [hw, map_one, one_mul]⟩
  have e : t * slLong σ hσ A * slB σ hσ B * (t * slLong σ hσ A * slB σ hσ B) =
      (t * t) * (t⁻¹ * (slLong σ hσ A * slB σ hσ B) * t) * (slLong σ hσ A * slB σ hσ B) := by
    group
  rw [e]
  exact mul_mem (mul_mem hsq hconj) hs

include hσ in
theorem chart_mem_td4ProdRange [Finite K] [CharP (fixedField σ) 3] (hσ3 : ∀ c, σ c = c ^ 3)
    (hK : Nat.card K = 27) (hK1 : (-1 : Kˣ) ≠ 1)
    (hC₀ : graphFixedRootGroup TwistTag.D4 K σ ≤ (twistedIncl σ).range)
    (hgF : ∀ g : twistedGroup σ, twistedIncl σ g ∈ graphFixedRootGroup TwistTag.D4 K σ)
    {Ψ : SL(2, fixedField σ) →* twistedGroup σ}
    (hc : ∀ A, Ψ A * slLong σ hσ (-1) = slLong σ hσ (-1) * Ψ A) (A : SL(2, fixedField σ)) :
    Ψ A ∈ td4ProdRange hσ := by
  obtain ⟨S₃, -, h3s, hcl⟩ := gen3_top_sl2 (F := fixedField σ)
  have hle : Subgroup.closure S₃ ≤ (td4ProdRange hσ).comap Ψ := by
    rw [Subgroup.closure_le]
    intro s hs
    have hy3 : Ψ s * Ψ s * Ψ s = 1 := by rw [← pow_three', ← map_pow, h3s s hs, map_one]
    have hsq := sq_mem_td4ProdRange hσ hσ3 hK hK1 hC₀ hgF (hc s)
    show Ψ s ∈ td4ProdRange hσ
    have e : Ψ s = (Ψ s * Ψ s) * (Ψ s * Ψ s) := by
      calc Ψ s = Ψ s * (Ψ s * Ψ s * Ψ s) := by rw [hy3, mul_one]
        _ = (Ψ s * Ψ s) * (Ψ s * Ψ s) := by group
    rw [e]
    exact mul_mem hsq hsq
  exact hle (hcl (Subgroup.mem_top A))

end Prod

section HS

variable {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem chart_neg_one_eq_td4 [Finite K] [CharP K 3] (hσ3 : ∀ c, σ c = c ^ 3)
    (hK : Nat.card K = 27) (hC₀ : graphFixedRootGroup TwistTag.D4 K σ ≤ (twistedIncl σ).range)
    (hgF : ∀ g : twistedGroup σ, twistedIncl σ g ∈ graphFixedRootGroup TwistTag.D4 K σ)
    {Ψ : SL(2, fixedField σ) →* twistedGroup σ} (hΨ : Function.Injective Ψ)
    (hc : ∀ A, Ψ A * slLong σ hσ (-1) = slLong σ hσ (-1) * Ψ A) :
    Ψ (-1) = slLong σ hσ (-1) := by
  have hchar : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; norm_num
  have hF3 : Nat.card (fixedField σ) = 3 :=
    CFSG.LieType.HighestRoot.card_fixedField_eq_three hchar hσ3
  have hK1 : (-1 : Kˣ) ≠ 1 := fun h =>
    Ring.neg_one_ne_one_of_char_ne_two hchar (by simpa using congrArg Units.val h)
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hchar
  have h2F : (2 : fixedField σ) ≠ 0 := fun h => h2 (congrArg Subtype.val h)
  obtain ⟨ε⟩ := nonempty_mulEquiv_sl2Three_of_natCard_eq_three hF3
  have hsymm : ε.symm (-1) = -1 := by
    have hsq : ε.symm (-1) * ε.symm (-1) = 1 := by
      rw [← map_mul, sl23_neg_one_mul_self, map_one]
    rcases sl2_sq_eq_one h2F hsq with h | h
    · exact absurd (ε.symm.injective (h.trans (map_one ε.symm).symm)) sl23_neg_one_ne_one
    · exact h
  have key := eq_central_of_le_mul3 h2 ((slLong σ hσ).comp ε.symm.toMonoidHom) (slB σ hσ)
    ((slLong_injective hσ).comp ε.symm.injective) (slB_injective hσ)
    (fun A B => slLong_comm_slB hσ _ B)
    (by
      show slLong σ hσ (ε.symm (-1)) = slB σ hσ (-1)
      rw [hsymm, slB_neg_one hσ])
    (Ψ.comp ε.symm.toMonoidHom) (hΨ.comp ε.symm.injective)
    (fun A => by
      obtain ⟨A', B', h⟩ := (mem_td4ProdRange hσ).mp
        (chart_mem_td4ProdRange hσ hσ3 hK hK1 hC₀ hgF hc (ε.symm A))
      exact ⟨ε A', B', by
        show Ψ (ε.symm A) = slLong σ hσ (ε.symm (ε A')) * slB σ hσ B'
        rw [MulEquiv.symm_apply_apply, h]⟩)
  have key' : Ψ (ε.symm (-1)) = slB σ hσ (-1) := key
  rw [hsymm, slB_neg_one hσ] at key'
  exact key'

end HS

end CFSG.ClassicalInvolution.Q3.Q3MT
