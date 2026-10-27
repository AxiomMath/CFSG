module

public import CFSG.CGT.Stroth77.DeviationGeneric

public section

namespace CFSG.CGT.Stroth77

open Matrix

namespace DeviationGeneric

open Stroth225Frame

local notation "𝓡[" S ", " D "]" =>
  S ⊓ Subgroup.normalizer (SetLike.coe D) ⊓ Subgroup.centralizer (SetLike.coe (mhoOne D))

variable {G : Type} [Group G] [Finite G] {S D : Subgroup G} {τ : StrothTypeIndex}
  {dD : StrothWeakTypeData D τ}

theorem exists_conj_mul_eq (dD : StrothWeakTypeData D τ) (hk : ∀ i, 2 ≤ τ.k i) {y : G}
    (hy : y ∈ 𝓡[S, D]) (hΩ₂ : ∀ w ∈ D, w ^ 4 = 1 → y * w * y⁻¹ = w) {e : G}
    (he : e ∈ mhoOne D) : ∃ d ∈ D, y⁻¹ * d * y * d = e := by
  have hω := omegaIn_one_le_mhoOne dD hk
  have hyN : y ∈ Subgroup.normalizer (D : Set G) := mem_normalizer_of_mem_R hy
  have hyiN : y⁻¹ ∈ Subgroup.normalizer (D : Set G) := inv_mem hyN
  have hconjD : ∀ d ∈ D, y⁻¹ * d * y ∈ D := fun d hd => by
    simpa using (Subgroup.mem_normalizer_iff.mp hyiN d).mp hd
  have hcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb => comm_of_mem dD ha hb
  let θ : D →* D :=
    { toFun := fun d => ⟨y⁻¹ * d * y * d, D.mul_mem (hconjD d d.2) d.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => by
        apply Subtype.ext
        have hab' : (a : G) * (b : G) = (b : G) * (a : G) := hcomm a a.2 b b.2
        have hc1 := hcomm (y⁻¹ * b * y * b) (D.mul_mem (hconjD b b.2) b.2) a a.2
        simp only [Subgroup.coe_mul]
        calc y⁻¹ * (a * b) * y * (a * b) = (y⁻¹ * a * y) * (y⁻¹ * b * y) * (a * b) := by group
          _ = (y⁻¹ * a * y) * (y⁻¹ * b * y) * (b * a) := by rw [hab']
          _ = y⁻¹ * a * y * ((y⁻¹ * b * y * b) * a) := by group
          _ = y⁻¹ * a * y * (a * (y⁻¹ * b * y * b)) := by rw [hc1]
          _ = y⁻¹ * a * y * a * (y⁻¹ * b * y * b) := by group }
  let sq : D →* D :=
    { toFun := fun d => d * d
      map_one' := by simp
      map_mul' := fun a b => by
        apply Subtype.ext
        have hab' : (a : G) * (b : G) = (b : G) * (a : G) := hcomm a a.2 b b.2
        simp only [Subgroup.coe_mul]
        calc (a : G) * b * (a * b) = a * (b * a) * b := by group
          _ = a * (a * b) * b := by rw [hab']
          _ = a * a * (b * b) := by group }
  have hker : θ.ker = sq.ker := by
    ext d
    simp only [MonoidHom.mem_ker]
    constructor
    · intro h0
      have h1 : y⁻¹ * (d : G) * y * d = 1 := congrArg Subtype.val h0
      have h3 : y⁻¹ * (d : G) * y = (d : G)⁻¹ := by
        calc y⁻¹ * (d : G) * y = (y⁻¹ * (d : G) * y * d) * (d : G)⁻¹ := by group
          _ = (d : G)⁻¹ := by rw [h1, one_mul]
      have h2 : y * (d : G) * y⁻¹ = (d : G)⁻¹ := by
        have e : y * (d : G)⁻¹ * y⁻¹ = d := by rw [← h3]; group
        calc y * (d : G) * y⁻¹ = (y * (d : G)⁻¹ * y⁻¹)⁻¹ := by group
          _ = (d : G)⁻¹ := by rw [e]
      have hmem := commutator_mem_omegaIn_one dD hy d.2
      rw [h2] at hmem
      have hd4 : (d : G) ^ 4 = 1 := by
        have h4 := ((mem_omegaIn_iff_of_comm hcomm).mp hmem).2
        have h5 : ((d : G)⁻¹ * (d : G)⁻¹) ^ 2 = ((d : G) ^ 4)⁻¹ := by group
        rw [pow_one, h5] at h4
        exact inv_eq_one.mp h4
      have h6 := hΩ₂ d d.2 hd4
      rw [h6] at h2
      apply Subtype.ext
      show (d : G) * d = 1
      calc (d : G) * d = (d : G) * (d : G)⁻¹ := by rw [← h2]
        _ = 1 := mul_inv_cancel _
    · intro h0
      have h1 : (d : G) * d = 1 := congrArg Subtype.val h0
      have hdΩ : (d : G) ∈ omegaIn 1 D := mem_omegaIn_one_of_mul_self d.2 h1
      have hyd : y⁻¹ * (d : G) * y = d := by
        have := Subgroup.mem_centralizer_iff.mp (mem_centralizer_of_mem_R hy) (d : G) (hω hdΩ)
        calc y⁻¹ * (d : G) * y = y⁻¹ * ((d : G) * y) := by group
          _ = y⁻¹ * (y * (d : G)) := by rw [this]
          _ = d := by group
      apply Subtype.ext
      show y⁻¹ * (d : G) * y * d = 1
      rw [hyd, h1]
  have hcard : Nat.card θ.range = Nat.card sq.range := by
    have h1 := Subgroup.card_ker_mul_card_range θ
    have h2 := Subgroup.card_ker_mul_card_range sq
    rw [hker] at h1
    have hpos : 0 < Nat.card sq.ker := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)
  have hle : θ.range ≤ sq.range := by
    rintro _ ⟨d, rfl⟩
    have hc : y⁻¹ * (d : G) * y * (d : G)⁻¹ ∈ omegaIn 1 D := by
      have := commutator_mem_omegaIn_one dD (inv_mem hy) d.2
      simpa using this
    obtain ⟨c, hcD, hc2⟩ := (mem_mhoOne_iff dD).mp (hω hc)
    refine ⟨⟨c, hcD⟩ * d, ?_⟩
    apply Subtype.ext
    have hcd : c * (d : G) = (d : G) * c := hcomm c hcD d d.2
    show (c * (d : G)) * (c * d) = y⁻¹ * (d : G) * y * d
    calc c * (d : G) * (c * d) = (c * c) * ((d : G) * d) := by
          rw [mul_assoc c, ← mul_assoc (d : G), ← hcd]; group
      _ = (y⁻¹ * (d : G) * y * (d : G)⁻¹) * ((d : G) * d) := by rw [hc2]
      _ = y⁻¹ * (d : G) * y * d := by group
  have heq : θ.range = sq.range := Subgroup.eq_of_le_of_card_ge hle hcard.ge
  obtain ⟨f, hfD, hf2⟩ := (mem_mhoOne_iff dD).mp he
  have hmem : (⟨e, hf2 ▸ D.mul_mem hfD hfD⟩ : D) ∈ θ.range := by
    rw [heq]
    exact ⟨⟨f, hfD⟩, Subtype.ext hf2⟩
  obtain ⟨d, hd⟩ := hmem
  exact ⟨d, d.2, congrArg Subtype.val hd⟩

omit [Finite G] in
theorem barD_of_pow_four (hk : ∀ i, 2 ≤ τ.k i) (hk3 : 3 ≤ τ.k 1) (hk3' : 3 ≤ τ.k 2) {w : D}
    (hw : w ^ 4 = 1) : barD dD hk w 1 = 0 ∧ barD dD hk w 2 = 0 :=
  ⟨barD_eq_zero_of_pow hk (j := 2) hw hk3, barD_eq_zero_of_pow hk (j := 2) hw hk3'⟩

theorem conj_eq_of_devMat_col (hk : ∀ i, 2 ≤ τ.k i) {y : G} (hy : y ∈ 𝓡[S, D])
    (hcol : ∀ i, devMat dD hk y hy i 0 = 0) {w : D} (hw1 : barD dD hk w 1 = 0)
    (hw2 : barD dD hk w 2 = 0) : y * w * y⁻¹ = w := by
  have h := devMat_val_eq (dD := dD) hk y hy w
  have hv : devMat dD hk y hy *ᵥ barD dD hk w = 0 := by
    funext i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hw1, hw2, hcol i]
  rw [hv, map_zero] at h
  have h2 := dD.e.injective (h.trans (map_zero dD.e).symm)
  have h3 := congrArg (fun a : Additive D => ((Additive.toMul a : D) : G)) h2
  simp only [toMul_ofMul, toMul_zero, Subgroup.coe_one] at h3
  calc y * (w : G) * y⁻¹ = (y * w * y⁻¹ * (w : G)⁻¹) * w := by group
    _ = w := by rw [h3, one_mul]

theorem mem_D_of_sq_mem_mhoOne (dD : StrothWeakTypeData D τ) (hk : ∀ i, 2 ≤ τ.k i)
    (hDS : D ≤ S) {A : Subgroup G} (hAD : A ≤ D) (hΩA : omegaIn 1 D ≤ A)
    (hA4 : ∀ a ∈ A, a ^ 4 = 1) {l₁ l₂ : G} (hl₁ : l₁ ∈ Subgroup.normalizer (D : Set G))
    (hl₂ : l₂ ∈ Subgroup.normalizer (D : Set G))
    (hinv : ∀ z ∈ S, z * z = 1 → z ∈ Subgroup.centralizer (A : Set G) →
      z⁻¹ * (l₁⁻¹ * z * l₁) ∈ A → z⁻¹ * (l₂⁻¹ * z * l₂) ∈ A → z ∈ A)
    {y : G} (hy : y ∈ 𝓡[S, D]) (hΩ₂ : ∀ w ∈ D, w ^ 4 = 1 → y * w * y⁻¹ = w)
    (hy₁ : y⁻¹ * (l₁⁻¹ * y * l₁) ∈ D) (hy₂ : y⁻¹ * (l₂⁻¹ * y * l₂) ∈ D)
    (hy2 : y * y ∈ mhoOne D) : y ∈ D := by
  have hcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb => comm_of_mem dD ha hb
  obtain ⟨d, hdD, hd⟩ := exists_conj_mul_eq dD hk hy hΩ₂ (inv_mem hy2)
  set z := y * d
  have hz2 : z * z = 1 := by
    calc z * z = (y * y) * (y⁻¹ * d * y * d) := by simp only [z]; group
      _ = 1 := by rw [hd, mul_inv_cancel]
  have hzS : z ∈ S := mul_mem (mem_S_of_mem_R hy) (hDS hdD)
  have hzconj : ∀ e ∈ D, z * e * z⁻¹ = y * e * y⁻¹ := fun e he => by
    have := hcomm d hdD e he
    calc z * e * z⁻¹ = y * (d * e) * d⁻¹ * y⁻¹ := by simp only [z]; group
      _ = y * (e * d) * d⁻¹ * y⁻¹ := by rw [this]
      _ = y * e * y⁻¹ := by group
  have hzA : z ∈ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have h1 := hΩ₂ a (hAD ha) (hA4 a ha)
    rw [← hzconj a (hAD ha)] at h1
    calc a * z = (z * a * z⁻¹) * z := by rw [h1]
      _ = z * a := by group
  have hmove : ∀ l : G, l ∈ Subgroup.normalizer (D : Set G) → y⁻¹ * (l⁻¹ * y * l) ∈ D →
      z⁻¹ * (l⁻¹ * z * l) ∈ A := by
    intro l hl hyl
    have hld : l⁻¹ * d * l ∈ D := (Subgroup.mem_normalizer_iff''.mp hl d).mp hdD
    set e := z⁻¹ * (l⁻¹ * z * l)
    have heD : e ∈ D := by
      have : e = d⁻¹ * (y⁻¹ * (l⁻¹ * y * l)) * (l⁻¹ * d * l) := by simp only [e, z]; group
      rw [this]
      exact D.mul_mem (D.mul_mem (D.inv_mem hdD) hyl) hld
    have hze : (z * e) * (z * e) = 1 := by
      have : z * e = l⁻¹ * z * l := by simp only [e]; group
      rw [this]
      calc l⁻¹ * z * l * (l⁻¹ * z * l) = l⁻¹ * (z * z) * l := by group
        _ = 1 := by rw [hz2]; group
    have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
    have hinvE : y * e * y⁻¹ = e⁻¹ := by
      rw [← hzconj e heD]
      calc z * e * z⁻¹ = z * e * z := by rw [hzinv]
        _ = ((z * e) * (z * e)) * e⁻¹ := by group
        _ = e⁻¹ := by rw [hze, one_mul]
    have hmem := commutator_mem_omegaIn_one dD hy heD
    rw [hinvE] at hmem
    have he4 : e ^ 4 = 1 := by
      have h4 := ((mem_omegaIn_iff_of_comm hcomm).mp hmem).2
      have h5 : (e⁻¹ * e⁻¹) ^ 2 = (e ^ 4)⁻¹ := by group
      rw [pow_one, h5] at h4
      exact inv_eq_one.mp h4
    have hye := hΩ₂ e heD he4
    rw [hye] at hinvE
    have he2 : e * e = 1 := by
      calc e * e = e * e⁻¹ := by rw [← hinvE]
        _ = 1 := mul_inv_cancel e
    exact hΩA (mem_omegaIn_one_of_mul_self heD he2)
  have hzA' : z ∈ A := hinv z hzS hz2 hzA (hmove l₁ hl₁ hy₁) (hmove l₂ hl₂ hy₂)
  have : y = z * d⁻¹ := by simp only [z]; group
  rw [this]
  exact mul_mem (hAD hzA') (inv_mem hdD)

end DeviationGeneric

end CFSG.CGT.Stroth77
