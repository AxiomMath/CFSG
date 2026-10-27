module

public import CFSG.LieType.SeitzGeneration.SubfieldPairSUEntry
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUBlock
public import CFSG.LieType.SeitzGeneration.UnitaryCenters

public section

namespace CFSG.LieType.SeitzGeneration.SUPair

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.RankThree.PartOne.CTP CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.Centers

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ} {k : Subfield K} {p : ℕ}

theorem tvMat_smul_left (ν : K) (b : Fin n → K) (c : K) :
    tvMat σ (ν • b) c = tvMat σ b (c * (σ ν * ν)) := by
  ext i j
  simp only [tvMat, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, Pi.smul_apply,
    smul_eq_mul, map_mul]
  ring

theorem coe_suConj_tv (hσ : ∀ c, σ (σ c) = c) (A : GL (Fin n) K)
    (hA : conjTr σ (A : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) = 1)
    {a : Fin n → K} (hia : herm σ a a = 0) {c : K} (hct : c + σ c = 0) :
    ((suConj hσ A hA (tv hσ hia hct) : SUid σ n) : GL (Fin n) K).val =
      tvMat σ ((A : Matrix (Fin n) (Fin n) K) *ᵥ a) c := by
  ext i j
  rw [entry_of_tv (suConj_smul_of_tv hσ A hA (tv_smul hσ hia hct)) i j]
  simp [tvMat, vecMulVec_apply, Matrix.one_apply, mul_assoc]

theorem coe_tv (hσ : ∀ c, σ (σ c) = c) {a : Fin n → K} (hia : herm σ a a = 0) {c : K}
    (hct : c + σ c = 0) : ((tv hσ hia hct : SUid σ n) : GL (Fin n) K).val = tvMat σ a c :=
  rfl

theorem map_u2 {F : Type} [Field F] (f : F →+* K) (s : F) :
    SpecialLinearGroup.map f (u2 s) = u2 (f s) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u2_coe]

theorem map_l2 {F : Type} [Field F] (f : F →+* K) (s : F) :
    SpecialLinearGroup.map f (l2 s) = l2 (f s) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [l2_coe]

section Main

variable [Finite K]

theorem isCenter_of_pair (hσ : ∀ c, σ (σ c) = c)
    (hk : ∀ x ∈ k, σ x ∈ k) (K₀ : Subfield K) (hK₀ : ∀ x, x ∈ K₀ ↔ σ x = x)
    (hp : p.Prime) (hp2 : p ≠ 2) (hKc : Nat.card K₀ = Nat.card (k.comap K₀.subtype) ^ p)
    (hk3 : 3 ≤ Nat.card (k.comap K₀.subtype)) {ε : K} (hεk : ε ∈ k) (hε0 : ε ≠ 0)
    (hσε : σ ε = -ε) (A : GL (Fin n) K)
    (hA : conjTr σ (A : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) = 1)
    {H : Subgroup (SUid σ n)} (hH₀ : ratSU σ k hk n ≤ H)
    (hH₁ : (ratSU σ k hk n).map (suConj hσ A hA) ≤ H) {a e : Fin n → K} (ha : IsRat k a)
    (hia : herm σ a a = 0) (he : IsRat k e) (hie : herm σ e e = 0)
    (hN : σ (herm σ e ((A : Matrix (Fin n) (Fin n) K) *ᵥ a)) *
      herm σ e ((A : Matrix (Fin n) (Fin n) K) *ᵥ a) ∉ k) : IsCenter H e := by
  set b : Fin n → K := (A : Matrix (Fin n) (Fin n) K) *ᵥ a with hb
  have hbb : herm σ b b = 0 := by rw [hb, herm_mulVec_unitary A hA, hia]
  set γ : K := herm σ e b with hγ
  have hγ0 : γ ≠ 0 := fun h => hN (by rw [h, map_zero, zero_mul]; exact k.zero_mem)
  have hσγ0 : σ γ ≠ 0 := (map_ne_zero σ).mpr hγ0
  have hσε0 : σ ε ≠ 0 := by rw [hσε]; exact neg_ne_zero.2 hε0
  set N : K := σ γ * γ with hNdef
  have hN0 : N ≠ 0 := mul_ne_zero hσγ0 hγ0
  set f : Fin n → K := (ε / γ) • b with hf
  have hef : herm σ e f = ε := by
    rw [hf, herm_smul_right, ← hγ]
    field_simp
  have hff : herm σ f f = 0 := by
    rw [hf, herm_smul_left, herm_smul_right, hbb]
    ring
  have hFE := pairRows_mul_pairCols hσ hε0 hσε hie hff hef
  let Φ : SpecialLinearGroup (Fin 2) K₀ →* GL (Fin n) K :=
    Matrix.SpecialLinearGroup.toGL.comp
      ((blockHom (pairCols e f) (pairRows σ e f ε) hFE).comp (SpecialLinearGroup.map K₀.subtype))
  have hΦu : ∀ s : K₀, (Φ (u2 s) : GL (Fin n) K).val = tvMat σ e ((s : K) / ε) := by
    intro s
    show ((blockHom (pairCols e f) (pairRows σ e f ε) hFE
      (SpecialLinearGroup.map K₀.subtype (u2 s)) : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = _
    rw [map_u2]
    exact blockHom_u2_pair hσ hε0 hσε hie hff hef _
  have hΦl : ∀ s : K₀, (Φ (l2 s) : GL (Fin n) K).val = tvMat σ f ((s : K) / σ ε) := by
    intro s
    show ((blockHom (pairCols e f) (pairRows σ e f ε) hFE
      (SpecialLinearGroup.map K₀.subtype (l2 s)) : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = _
    rw [map_l2]
    exact blockHom_l2_pair hσ hε0 hσε hie hff hef _
  set Hgl : Subgroup (GL (Fin n) K) := H.map (SUid σ n).subtype with hHgl
  set α : K₀ := ⟨ε ^ 2, (hK₀ _).2 (by rw [map_pow, hσε]; ring)⟩ with hα
  set β : K₀ := ⟨N, (hK₀ _).2 (by rw [hNdef, map_mul, hσ]; ring)⟩ with hβ
  have hu : ∀ t ∈ k.comap K₀.subtype, u2 (t * α) ∈ Hgl.comap Φ := by
    intro t ht
    have ht' : (t : K) ∈ k := ht
    have hct : ((t : K) * ε) + σ ((t : K) * ε) = 0 := by
      rw [map_mul, (hK₀ _).1 t.2, hσε]; ring
    refine ⟨tv hσ hie hct, hH₀ (tv_mem_ratSU hk hσ he hie (k.mul_mem ht' hεk) hct), ?_⟩
    apply Units.ext
    show ((tv hσ hie hct : SUid σ n) : GL (Fin n) K).val = (Φ (u2 (t * α))).val
    rw [coe_tv, hΦu]
    congr 1
    have h1 : (((t * α : K₀)) : K) = (t : K) * ε ^ 2 := rfl
    rw [h1]
    field_simp
  have hl : ∀ t ∈ k.comap K₀.subtype, l2 (t * β) ∈ Hgl.comap Φ := by
    intro t ht
    have ht' : (t : K) ∈ k := ht
    have hct : ((t : K) * ε) + σ ((t : K) * ε) = 0 := by
      rw [map_mul, (hK₀ _).1 t.2, hσε]; ring
    refine ⟨suConj hσ A hA (tv hσ hia hct),
      hH₁ ⟨tv hσ hia hct, tv_mem_ratSU hk hσ ha hia (k.mul_mem ht' hεk) hct, rfl⟩, ?_⟩
    apply Units.ext
    show ((suConj hσ A hA (tv hσ hia hct) : SUid σ n) : GL (Fin n) K).val = (Φ (l2 (t * β))).val
    rw [coe_suConj_tv, hΦl, hf, tvMat_smul_left]
    congr 1
    have h1 : (((t * β : K₀)) : K) = (t : K) * N := rfl
    rw [h1, hNdef, map_div₀]
    field_simp
  have hαβ : α * β ∉ k.comap K₀.subtype := by
    intro h
    apply hN
    have h' : ε ^ 2 * N ∈ k := h
    have : N = (ε ^ 2)⁻¹ * (ε ^ 2 * N) := by field_simp
    rw [this]
    exact k.mul_mem (k.inv_mem (k.pow_mem hεk 2)) h'
  have hM : Hgl.comap Φ = ⊤ := sl2_eq_top_of_root_pair hp hp2 hKc hk3 hαβ hu hl
  refine ⟨hie, fun c hc => ?_⟩
  have hσc : σ c = -c := by linear_combination hc
  have hfix : σ (c * ε) = c * ε := by rw [map_mul, hσc, hσε]; ring
  have hs : u2 (⟨c * ε, (hK₀ _).2 hfix⟩ : K₀) ∈ Hgl.comap Φ := hM ▸ Subgroup.mem_top _
  obtain ⟨g, hgH, hg⟩ := hs
  refine ⟨g, hgH, fun v => ?_⟩
  have hgm : ((g : GL (Fin n) K)).val = tvMat σ e c := by
    have := congrArg Units.val hg
    rw [hΦu] at this
    rw [show ((g : GL (Fin n) K)).val = ((SUid σ n).subtype g : GL (Fin n) K).val from rfl, this]
    congr 1
    field_simp
  rw [smul_def, hgm, tvMat_mulVec]

end Main

end CFSG.LieType.SeitzGeneration.SUPair
