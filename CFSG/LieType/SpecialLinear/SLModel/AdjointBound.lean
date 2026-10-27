module

public import CFSG.LieType.SpecialLinear.SLModel.Basic
public import CFSG.LieType.SpecialLinear.ExteriorModel.AdjointHeart
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.QuadraticDescent
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.AdjointHeartUnitary
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.EndFieldModel

public section

open Module Matrix CFSG.LieType.SpecialLinear.ExteriorModel CFSG.HardMathSupport.GuralnickMalle
  CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar CFSG.Quasithin.SmithCurtis

namespace CFSG.LieType.SpecialLinear.SLModel

variable {F : Type} [Field F] [Fintype F] [CharP F 2] {k : Type} [Field k] [CharP k 2]
  [Algebra F k] {m f : ℕ}

omit [Fintype F] in
theorem exists_equiv_adjointHeart (hm : 2 ≤ m) (ε : Fin f → Finset (Fin (m + 1))) (r₀ : Fin f)
    (hε' : ∀ r, r ≠ r₀ → ε r = ∅) (hε : ε r₀ = {⟨1, by omega⟩, ⟨m, by omega⟩}) :
    ∃ Φ : BModel k ε ≃ₗ[k] AdjointHeart (m + 1) k, ∀ g v,
      Φ (slModelRep (F := F) (k := k) ε g v) =
        adjointHeartRep (m + 1) k
          (GeneralLinearGroup.map (frobTwist F k f r₀) (SpecialLinearGroup.toGL g)) (Φ v) := by
  obtain ⟨Φ, hΦ⟩ := exists_bModel_equiv_adjointHeart (k := k) (n := m + 1) (τ := Fin f)
    (ε := ε) (r₀ := r₀) (by omega) hε hε'
  refine ⟨Φ, ?_⟩
  intro g v
  have hmap : SpecialLinearGroup.toGL
      (SpecialLinearGroup.map (frobTwist F k f r₀) g) =
      GeneralLinearGroup.map (frobTwist F k f r₀) (SpecialLinearGroup.toGL g) := by
    ext
    rfl
  rw [slModelRep, MonoidHom.comp_apply, hΦ, twistHom_apply, hmap]

theorem card_le_of_slModelRep_adjoint (hm : 2 ≤ m) (ε : Fin f → Finset (Fin (m + 1)))
    (r₀ : Fin f) (hε' : ∀ r, r ≠ r₀ → ε r = ∅)
    (hε : ε r₀ = {⟨1, by omega⟩, ⟨m, by omega⟩})
    {P : Subgroup (SpecialLinearGroup (Fin (m + 1)) F)} (hP : ∀ a ∈ P, a * a = 1)
    (hquad : ∀ a ∈ P, ∀ b ∈ P,
      (slModelRep (F := F) (k := k) ε a - 1) * (slModelRep (F := F) (k := k) ε b - 1) = 0) :
    Nat.card P ≤ Fintype.card F := by
  classical
  obtain ⟨Φ, hΦ⟩ := exists_equiv_adjointHeart (F := F) (k := k) hm ε r₀ hε' hε
  let φ := frobTwist F k f r₀
  let τ' : Representation k (SpecialLinearGroup (Fin (m + 1)) F) (AdjointHeart (m + 1) k) :=
    (adjointHeartRep (m + 1) k).comp
      ((GeneralLinearGroup.map φ).comp SpecialLinearGroup.toGL)
  have hβ : ∀ (g : SpecialLinearGroup (Fin (m + 1)) F) (v : BModel k ε),
      Φ (slModelRep (F := F) (k := k) ε g v) = τ' g (Φ v) := hΦ
  have hqk : ∀ a ∈ P, ∀ b ∈ P, (τ' a - 1) * (τ' b - 1) = 0 := by
    intro a ha b hb
    exact sub_one_mul_sub_one_of_equiv (β := Φ) hβ (hquad a ha b hb)
  have hqF : ∀ a ∈ P.map SpecialLinearGroup.toGL,
      ∀ b ∈ P.map SpecialLinearGroup.toGL,
      (adjointHeartRep (m + 1) F a - 1) * (adjointHeartRep (m + 1) F b - 1) = 0 := by
    intro a ha b hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    exact adjointHeartRep_sub_one_mul_sub_one_of_map (frobTwist F k f r₀)
      (SpecialLinearGroup.toGL a') (SpecialLinearGroup.toGL b')
      (by simpa [τ', φ] using hqk a' ha' b' hb')
  have hA : CFSG.Open.IsElemAbelian 2 (P.map SpecialLinearGroup.toGL) := by
    constructor
    · refine IsMulCommutative.of_comm (fun x y => ?_)
      apply Subtype.ext
      obtain ⟨a, ha, hxa⟩ := x.2
      obtain ⟨b, hb, hxb⟩ := y.2
      change (x : GL (Fin (m + 1)) F) * (y : GL (Fin (m + 1)) F) =
        (y : GL (Fin (m + 1)) F) * (x : GL (Fin (m + 1)) F)
      rw [← hxa, ← hxb]
      have hcomm : a * b = b * a := by
        have ha' : a⁻¹ = a := inv_eq_of_mul_self_eq_one (hP a ha)
        have hb' : b⁻¹ = b := inv_eq_of_mul_self_eq_one (hP b hb)
        have hab : (a * b)⁻¹ = a * b :=
          inv_eq_of_mul_self_eq_one (hP (a * b) (P.mul_mem ha hb))
        calc a * b = (a * b)⁻¹ := hab.symm
          _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
          _ = b * a := by rw [ha', hb']
      rw [← map_mul, ← map_mul, hcomm]
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := hx
      show SpecialLinearGroup.toGL a ^ 2 = 1
      rw [← map_pow, pow_two, hP a ha, map_one]
  have hcardmap : Nat.card (P.map SpecialLinearGroup.toGL) = Nat.card P :=
    Subgroup.card_map_of_injective (K := P) (f := SpecialLinearGroup.toGL)
      SpecialLinearGroup.toGL_injective
  have hcard := card_le_card_of_adjointHeart (K := F) (m := m + 1) hA hqF
  rw [hcardmap] at hcard
  simpa [Nat.card_eq_fintype_card] using hcard

omit [Fintype F] in
theorem two_mul_sub_two_le_finrank_range_slModelRep_adjoint (hm : 2 ≤ m)
    (ε : Fin f → Finset (Fin (m + 1))) (r₀ : Fin f) (hε' : ∀ r, r ≠ r₀ → ε r = ∅)
    (hε : ε r₀ = {⟨1, by omega⟩, ⟨m, by omega⟩})
    {u : SpecialLinearGroup (Fin (m + 1)) F} (hu : u * u = 1) (hu1 : u ≠ 1) :
    2 * m - 2 ≤ finrank k (LinearMap.range (slModelRep (F := F) (k := k) ε u - 1)) := by
  obtain ⟨Φ, hΦ⟩ := exists_equiv_adjointHeart (F := F) (k := k) hm ε r₀ hε' hε
  let φ := frobTwist F k f r₀
  let τ' : Representation k (SpecialLinearGroup (Fin (m + 1)) F) (AdjointHeart (m + 1) k) :=
    (adjointHeartRep (m + 1) k).comp
      ((GeneralLinearGroup.map φ).comp SpecialLinearGroup.toGL)
  have hβ : ∀ (g : SpecialLinearGroup (Fin (m + 1)) F) (v : BModel k ε),
      Φ (slModelRep (F := F) (k := k) ε g v) = τ' g (Φ v) := hΦ
  have hφ : Function.Injective φ := by
    change Function.Injective (frobTwist F k f r₀)
    rw [frobTwist]
    exact (FaithfulSMul.algebraMap_injective F k).comp (iterateFrobenius_inj F 2 (r₀ : ℕ))
  have hx2 : GeneralLinearGroup.map φ (SpecialLinearGroup.toGL u) *
      GeneralLinearGroup.map φ (SpecialLinearGroup.toGL u) = 1 := by
    have h1 : SpecialLinearGroup.toGL u * SpecialLinearGroup.toGL u = 1 := by
      rw [← map_mul, hu, map_one]
    rw [← map_mul, h1, map_one]
  have hx1 : GeneralLinearGroup.map φ (SpecialLinearGroup.toGL u) ≠ 1 := by
    intro h
    apply hu1
    apply SpecialLinearGroup.toGL_injective
    apply GeneralLinearGroup.map_injective hφ
    simpa using h
  have hmain := two_mul_sub_four_le_finrank_range_adjointHeartRep_sub_one
    (GeneralLinearGroup.map φ (SpecialLinearGroup.toGL u)) hx2 hx1
  have h2m : 2 * (m + 1) - 4 = 2 * m - 2 := by omega
  rw [h2m] at hmain
  rw [finrank_range_sub_one_eq_of_equiv (β := Φ) hβ u]
  simpa [τ'] using hmain

omit [Fintype F] in
theorem sixteen_lt_pow_finrank_range_slModelRep_adjoint (hm : 4 ≤ m)
    (ε : Fin f → Finset (Fin (m + 1))) (r₀ : Fin f) (hε' : ∀ r, r ≠ r₀ → ε r = ∅)
    (hε : ε r₀ = {⟨1, by omega⟩, ⟨m, by omega⟩}) {N : ℕ} (hN : 2 ≤ N)
    {u : SpecialLinearGroup (Fin (m + 1)) F} (hu : u * u = 1) (hu1 : u ≠ 1) :
    16 < N ^ finrank k (LinearMap.range (slModelRep (F := F) (k := k) ε u - 1)) := by
  have hrank := two_mul_sub_two_le_finrank_range_slModelRep_adjoint (k := k)
    (by omega : 2 ≤ m) ε r₀ hε' hε hu hu1
  have h6 : 6 ≤ 2 * m - 2 := by omega
  calc 16 < 2 ^ 6 := by norm_num
    _ ≤ 2 ^ finrank k (LinearMap.range (slModelRep (F := F) (k := k) ε u - 1)) :=
        Nat.pow_le_pow_right (by norm_num) (le_trans h6 hrank)
    _ ≤ N ^ finrank k (LinearMap.range (slModelRep (F := F) (k := k) ε u - 1)) :=
        Nat.pow_le_pow_left hN _

theorem two_mul_card_lt_pow_codim_slModelRep_adjoint (hm : 4 ≤ m)
    (hF : Fintype.card F = 2 ^ f) (ε : Fin f → Finset (Fin (m + 1))) (r₀ : Fin f)
    (hε' : ∀ r, r ≠ r₀ → ε r = ∅) (hε : ε r₀ = {⟨1, by omega⟩, ⟨m, by omega⟩})
    {N : ℕ} (hN : 2 ^ f ≤ N)
    {P : Subgroup (SpecialLinearGroup (Fin (m + 1)) F)} (hP1 : P ≠ ⊥)
    (hP : ∀ a ∈ P, a * a = 1)
    (hquad : ∀ a ∈ P, ∀ b ∈ P,
      (slModelRep (F := F) (k := k) ε a - 1) * (slModelRep (F := F) (k := k) ε b - 1) = 0) :
    2 * Nat.card P < N ^ (finrank k (BModel k ε) -
      finrank k (fixSub (slModelRep (F := F) (k := k) ε) P)) := by
  have hm2 : 2 ≤ m := by omega
  have hcard : Nat.card P ≤ 2 ^ f := by
    have h := card_le_of_slModelRep_adjoint (k := k) hm2 ε r₀ hε' hε hP hquad
    rwa [hF] at h
  have hfix : fixSub (slModelRep (F := F) (k := k) ε) P =
      fixSubGen (slModelRep (F := F) (k := k) ε) P := rfl
  rcases Subgroup.bot_or_exists_ne_one P with hbot | ⟨u, huP, hu1⟩
  · exact absurd hbot hP1
  have hrank := two_mul_sub_two_le_finrank_range_slModelRep_adjoint (k := k) hm2 ε r₀ hε' hε
    (hP u huP) hu1
  have hle := finrank_range_sub_one_le (τ := slModelRep (F := F) (k := k) ε) P huP
  have hcodim : 6 ≤ finrank k (BModel k ε) -
      finrank k (fixSub (slModelRep (F := F) (k := k) ε) P) := by
    rw [hfix]
    omega
  have hN2 : 2 ≤ N := by
    have h2f : 2 ≤ 2 ^ f := by
      have hf1 : 0 < f := r₀.pos
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf1
    omega
  have hNlt : 2 * N < N ^ 6 := by
    have hpos : 0 < N ^ 2 := pow_pos (by omega) 2
    have hN4 : 1 < N ^ 4 := by
      calc 1 < 2 ^ 4 := by norm_num
        _ ≤ N ^ 4 := Nat.pow_le_pow_left hN2 4
    have h1 : 2 * N ≤ N ^ 2 := by
      rw [pow_two]
      exact Nat.mul_le_mul_right N hN2
    have h2 : N ^ 2 < N ^ 6 := by
      calc N ^ 2 = N ^ 2 * 1 := (mul_one _).symm
        _ < N ^ 2 * N ^ 4 := Nat.mul_lt_mul_of_pos_left hN4 hpos
        _ = N ^ 6 := by ring
    omega
  have hpow : N ^ 6 ≤ N ^ (finrank k (BModel k ε) -
      finrank k (fixSub (slModelRep (F := F) (k := k) ε) P)) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  calc 2 * Nat.card P ≤ 2 * 2 ^ f := Nat.mul_le_mul_left 2 hcard
    _ ≤ 2 * N := Nat.mul_le_mul_left 2 hN
    _ < N ^ 6 := hNlt
    _ ≤ N ^ (finrank k (BModel k ε) -
        finrank k (fixSub (slModelRep (F := F) (k := k) ε) P)) := hpow

end CFSG.LieType.SpecialLinear.SLModel
