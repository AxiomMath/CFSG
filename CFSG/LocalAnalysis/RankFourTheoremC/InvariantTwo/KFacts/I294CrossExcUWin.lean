module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossExcUHerm
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossExcULevi

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

namespace CrossExcU

open CFSG.LocalAnalysis.ComponentInitial Subgroup

section Window

variable {ℓ f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K} {V : Type} [AddCommGroup V]
  [Module K V] [FiniteDimensional K V] {B : V →ₛₗ[h.bar] V →ₗ[K] K} {u : Module.End K V}
  {p s : ℕ}

theorem HermOddData.perp_invariant (hd : HermOddData B u p s) (hp : 0 < p) {W : Submodule K V}
    (hW : ∀ x ∈ W, u x ∈ W) : ∀ z ∈ hermPerp B W, u z ∈ hermPerp B W := by
  intro z hz w hw
  have h1 : u ((u ^ (p - 1)) w) = w := by
    rw [← Module.End.mul_apply, ← pow_succ' u (p - 1), Nat.sub_add_cancel hp, hd.pow_eq]
    rfl
  have h2 : (u ^ (p - 1)) w ∈ W := pow_apply_mem hW (p - 1) hw
  conv_lhs => rw [← h1]
  rw [hd.isom]
  exact hz _ h2

theorem HermOddData.exists_window (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hd : HermOddData B u p s) (hp : 0 < p) (hp0 : (p : K) ≠ 0) {e c : ℕ} (he : 0 < e)
    (hdeg : ∀ g : Polynomial K, Irreducible g → g ∣ Polynomial.X ^ p - 1 → g.natDegree ≤ e)
    (hc : c * e ≤ Module.finrank K V) :
    ∃ W : Submodule K V, (∀ x ∈ W, u x ∈ W) ∧ HermNondeg B W ∧ c * e ≤ Module.finrank K W ∧
      Module.finrank K W < (c + 1) * e := by
  let S : Set ℕ := {m | ∃ W : Submodule K V, (∀ x ∈ W, u x ∈ W) ∧ HermNondeg B W ∧
    Module.finrank K W = m ∧ m < (c + 1) * e}
  have hS0 : S.Nonempty :=
    ⟨0, ⊥, fun x hx => by simp [(Submodule.mem_bot K).1 hx], hermNondeg_bot, by simp,
      by positivity⟩
  have hSb : BddAbove S := ⟨(c + 1) * e, fun m ⟨_, _, _, _, hm⟩ => hm.le⟩
  obtain ⟨W, hW, hWnd, hWm, hWlt⟩ := Nat.sSup_mem hS0 hSb
  refine ⟨W, hW, hWnd, ?_, by omega⟩
  by_contra hlt
  rw [not_le] at hlt
  have hcompl := hermNondeg_isCompl hB hWnd
  have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
  have hperp0 : hermPerp B W ≠ ⊥ := by
    intro h0
    rw [h0, finrank_bot] at hsum
    omega
  obtain ⟨U, hU, hUperp, hU0, hUnd, hUe⟩ := hd.exists_small_nondeg hB hp hp0 hdeg
    (hd.perp_invariant hp hW) (hermNondeg_perp hB hBl hWnd) hperp0
  have hdisj : Disjoint W U := (hermNondeg_disjoint hB hWnd).mono_right hUperp
  have hfin : Module.finrank K ↥(W ⊔ U) = Module.finrank K W + Module.finrank K U := by
    have := Submodule.finrank_sup_add_finrank_inf_eq W U
    rw [disjoint_iff.1 hdisj, finrank_bot] at this
    omega
  have hU1 : 1 ≤ Module.finrank K U := Submodule.one_le_finrank_iff.2 hU0
  have hinv : ∀ x ∈ W ⊔ U, u x ∈ W ⊔ U := by
    intro x hx
    obtain ⟨w, hw, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add]
    exact (W ⊔ U).add_mem (Submodule.mem_sup_left (hW w hw)) (Submodule.mem_sup_right (hU z hz))
  have hce : (c + 1) * e = c * e + e := by ring
  have hmem : Module.finrank K ↥(W ⊔ U) ∈ S :=
    ⟨W ⊔ U, hinv, hermNondeg_sup hB hWnd hUnd hUperp, rfl, by omega⟩
  have hle := le_csSup hSb hmem
  omega

end Window

section Block

variable {ℓ f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K} {V : Type} [AddCommGroup V]
  [Module K V] {B : V →ₛₗ[h.bar] V →ₗ[K] K} {W C : Submodule K V}

@[expose] noncomputable def uProdMapOne (K W C : Type) [Field K] [AddCommGroup W] [Module K W]
    [AddCommGroup C] [Module K C] : Module.End K W →* Module.End K (W × C) where
  toFun g := g.prodMap (1 : Module.End K C)
  map_one' := LinearMap.prodMap_one
  map_mul' g g' := by rw [LinearMap.prodMap_mul, mul_one]

@[expose] noncomputable def uBlockEnd (hWC : IsCompl W C) : Module.End K W →* Module.End K V :=
  ((LinearEquiv.conjAlgEquiv K (Submodule.prodEquivOfIsCompl W C hWC)).toMulEquiv.toMonoidHom).comp
    (uProdMapOne K W C)

theorem uBlockEnd_apply_add (hWC : IsCompl W C) (g : Module.End K W) (w : W) (c : C) :
    uBlockEnd hWC g ((w : V) + (c : V)) = (g w : V) + (c : V) := by
  have hv : (w : V) + (c : V) = Submodule.prodEquivOfIsCompl W C hWC (w, c) := by
    rw [Submodule.coe_prodEquivOfIsCompl']
  rw [hv]
  simp [uBlockEnd, uProdMapOne, LinearEquiv.conjAlgEquiv_apply, Submodule.coe_prodEquivOfIsCompl']

theorem exists_add_of_isCompl (hWC : IsCompl W C) (v : V) :
    ∃ (w : W) (c : C), v = (w : V) + (c : V) := by
  have hv : v ∈ W ⊔ C := by rw [hWC.sup_eq_top]; trivial
  obtain ⟨w, hw, c, hc, rfl⟩ := Submodule.mem_sup.1 hv
  exact ⟨⟨w, hw⟩, ⟨c, hc⟩, rfl⟩

theorem uBlockEnd_injective (hWC : IsCompl W C) : Function.Injective (uBlockEnd (K := K) hWC) := by
  intro g g' hgg'
  ext w
  have h1 := uBlockEnd_apply_add hWC g w (0 : C)
  have h2 := uBlockEnd_apply_add hWC g' w (0 : C)
  rw [hgg'] at h1
  simp only [Submodule.coe_zero, add_zero] at h1 h2
  exact h1.symm.trans h2

theorem uBlockEnd_comm (hWC : IsCompl W C) {u : Module.End K V} (hW : ∀ x ∈ W, u x ∈ W)
    (hC : ∀ x ∈ C, u x ∈ C) (g : Module.End K W) (hg : g * u.restrict hW = u.restrict hW * g) :
    uBlockEnd hWC g * u = u * uBlockEnd hWC g := by
  ext v
  obtain ⟨w, c, rfl⟩ := exists_add_of_isCompl hWC v
  have hu : u ((w : V) + (c : V)) = ((u.restrict hW w : W) : V) + ((u.restrict hC c : C) : V) := by
    rw [map_add]
    rfl
  have hgw : g (u.restrict hW w) = u.restrict hW (g w) := by
    have := congrArg (fun F => F w) hg
    simpa using this
  have hcomm : ((g (u.restrict hW w) : W) : V) = u ((g w : W) : V) := by
    rw [hgw]
    rfl
  rw [Module.End.mul_apply, Module.End.mul_apply, hu, uBlockEnd_apply_add, uBlockEnd_apply_add,
    map_add, hcomm]
  rfl

theorem uBlockEnd_isometry (hB : B.IsSymm) (hWC : IsCompl W (hermPerp B W)) (g : Module.End K W)
    (hg : ∀ x y : W, B (g x : V) (g y : V) = B (x : V) (y : V)) (v v' : V) :
    B (uBlockEnd hWC g v) (uBlockEnd hWC g v') = B v v' := by
  obtain ⟨w, c, rfl⟩ := exists_add_of_isCompl hWC v
  obtain ⟨w', c', rfl⟩ := exists_add_of_isCompl hWC v'
  have hx1 : ∀ (a : W) (b : hermPerp B W), B (a : V) (b : V) = 0 := fun a b => b.2 a a.2
  have hx2 : ∀ (a : W) (b : hermPerp B W), B (b : V) (a : V) = 0 := fun a b =>
    (hermPerp_comm hB).1 b.2 a a.2
  rw [uBlockEnd_apply_add, uBlockEnd_apply_add]
  simp only [map_add, LinearMap.add_apply, hx1, hx2, hg, add_zero, zero_add]

theorem uBlockEnd_units_mem (hB : B.IsSymm) (hWC : IsCompl W (hermPerp B W))
    {g : (Module.End K W)ˣ} (hg : g ∈ sesqUnitaryGroup (B.domRestrict₁₂ W W)) :
    Units.map (uBlockEnd hWC) g ∈ sesqUnitaryGroup B :=
  mem_sesqUnitaryGroup.2 fun v v' =>
    uBlockEnd_isometry hB hWC (g : Module.End K W) (fun x y => mem_sesqUnitaryGroup.1 hg x y) v v'

end Block

section Index

variable {ℓ f : ℕ} {K : Type} [Field K] [Finite K]

theorem crossExcU_pow_add_ne_zero {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hodd : Odd (unitaryOrder ℓ f p)) (i : ℕ) :
    ((ℓ ^ f : ℕ) : ZMod p) ^ i + (-1) ^ i ≠ 0 := by
  intro h0
  have hs : ((-1 : ZMod p) ^ i) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  have hq : ((ℓ ^ f : ℕ) : ZMod p) ^ i = -(-1) ^ i := eq_neg_of_add_eq_zero_left h0
  have h1 : (-((ℓ ^ f : ℕ) : ZMod p)) ^ i = -1 := by
    calc (-((ℓ ^ f : ℕ) : ZMod p)) ^ i = (-1) ^ i * ((ℓ ^ f : ℕ) : ZMod p) ^ i := by
          rw [neg_eq_neg_one_mul, mul_pow]
      _ = (-1) ^ i * (-(-1) ^ i) := by rw [hq]
      _ = -(((-1 : ZMod p) ^ i) ^ 2) := by ring
      _ = -1 := by rw [hs]
  have h2 : (-((ℓ ^ f : ℕ) : ZMod p)) ^ (2 * i) = 1 := by
    rw [pow_mul', h1, neg_one_sq]
  have h3 : unitaryOrder ℓ f p ∣ 2 * i := (unitaryOrder_dvd_iff _).2 h2
  have h4 : unitaryOrder ℓ f p ∣ i := (Nat.coprime_two_right.2 hodd).dvd_mul_left.1 h3
  have h5 : (-((ℓ ^ f : ℕ) : ZMod p)) ^ i = 1 := (unitaryOrder_dvd_iff i).1 h4
  have h6 : (-1 : ZMod p) = 1 := h1.symm.trans h5
  have h7 : ((2 : ℕ) : ZMod p) = 0 := by
    have : (1 : ZMod p) + 1 = 0 := by
      calc (1 : ZMod p) + 1 = 1 + (-1) := by rw [h6]
        _ = 0 := add_neg_cancel 1
    exact_mod_cast (show ((1 + 1 : ℕ) : ZMod p) = 0 by exact_mod_cast this)
  have h8 := (ZMod.natCast_eq_zero_iff 2 p).1 h7
  have := Nat.le_of_dvd (by norm_num) h8
  omega

theorem crossExcU_prod_Icc_eq_range (g : ℕ → ℤ) (m : ℕ) :
    ∏ i ∈ Finset.Icc 1 m, g i = ∏ i ∈ Finset.range m, g (i + 1) := by
  induction m with
  | zero => simp
  | succ n ih => rw [Finset.prod_Icc_succ_top (by omega), Finset.prod_range_succ, ih]

theorem crossExcU_not_dvd_index_unitary (h : UnitaryFieldData ℓ f K) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpℓ : ¬ p ∣ ℓ) (hodd : Odd (unitaryOrder ℓ f p)) {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) : ¬ p ∣ (sesqUnitaryGroup B).index := by
  set m := Module.finrank K V with hm
  have hGL : Nat.card (Module.End K V)ˣ = Nat.card (GL (Fin m) K) :=
    Nat.card_congr (Units.mapEquiv (LinearMap.toMatrixAlgEquiv
      (Module.finBasis K V)).toMulEquiv).toEquiv
  have hGLcard := crossExcU_card_GL (K := K) m
  rcases Nat.eq_zero_or_pos m with hm0 | hm1
  · have h1 : Nat.card (Module.End K V)ˣ = 1 := by rw [hGL, hm0]; simpa using hGLcard
    intro hd
    have := Subgroup.index_dvd_card (sesqUnitaryGroup B)
    rw [h1] at this
    exact hp.one_lt.ne' (Nat.dvd_one.1 (hd.trans this))
  · have hord := (CFSG.LinearGroups.unitary_full_group_order h hB hBl
      (rfl : Module.finrank K V = m) hm1).1
    have hQ2 : 2 ≤ ℓ ^ f := by
      have h1 := Nat.one_lt_pow (n := f) (by have := h.one_le; omega) h.prime.one_lt
      omega
    have hq : Nat.card K = (ℓ ^ f) ^ 2 := h.card_eq_sq
    rw [hq] at hGLcard
    set a := m * (m - 1) / 2 with ha
    set U : ℤ := ∏ i ∈ Finset.range m, (((ℓ ^ f : ℕ) : ℤ) ^ (i + 1) - (-1) ^ (i + 1)) with hU
    set T : ℤ := ∏ i ∈ Finset.range m, (((ℓ ^ f : ℕ) : ℤ) ^ (i + 1) + (-1) ^ (i + 1)) with hT
    have hcardGU : (Nat.card (sesqUnitaryGroup B) : ℤ) = ((ℓ ^ f : ℕ) : ℤ) ^ a * U := by
      rw [hord, crossExcU_prod_Icc_eq_range (fun i => ((ℓ ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) m]
    have hpt : ∀ j : ℕ, (((ℓ ^ f : ℕ) : ℤ) ^ 2) ^ (j + 1) - 1 =
        (((ℓ ^ f : ℕ) : ℤ) ^ (j + 1) - (-1) ^ (j + 1)) *
          (((ℓ ^ f : ℕ) : ℤ) ^ (j + 1) + (-1) ^ (j + 1)) := by
      intro j
      have hs : ((-1 : ℤ) ^ (j + 1)) ^ 2 = 1 := by
        rw [← pow_mul, mul_comm, pow_mul]
        simp
      have he : (((ℓ ^ f : ℕ) : ℤ) ^ 2) ^ (j + 1) = (((ℓ ^ f : ℕ) : ℤ) ^ (j + 1)) ^ 2 := by
        rw [← pow_mul, ← pow_mul, mul_comm]
      rw [he]
      linear_combination hs
    have hcardG : (Nat.card (Module.End K V)ˣ : ℤ) = (((ℓ ^ f : ℕ) : ℤ) ^ a) ^ 2 * (U * T) := by
      rw [hGL, hGLcard, Nat.cast_mul, Nat.cast_pow, Nat.cast_prod, hU, hT,
        ← Finset.prod_mul_distrib]
      have hprod : ∏ j ∈ Finset.range m, (((((ℓ ^ f) ^ 2) ^ (j + 1) - 1 : ℕ)) : ℤ) =
          ∏ j ∈ Finset.range m, (((ℓ ^ f : ℕ) : ℤ) ^ (j + 1) - (-1) ^ (j + 1)) *
            (((ℓ ^ f : ℕ) : ℤ) ^ (j + 1) + (-1) ^ (j + 1)) := by
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [Nat.cast_sub (Nat.one_le_pow _ _ (by positivity)), ← hpt j]
        push_cast
        ring
      rw [hprod]
      push_cast
      ring
    have hidx := Subgroup.card_mul_index (sesqUnitaryGroup B)
    have hidxZ : (Nat.card (sesqUnitaryGroup B) : ℤ) * ((sesqUnitaryGroup B).index : ℤ) =
        Nat.card (Module.End K V)ˣ := by exact_mod_cast hidx
    rw [hcardGU, hcardG] at hidxZ
    have hU0 : U ≠ 0 := by
      refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
      intro h0
      have h1 : ((ℓ ^ f : ℕ) : ℤ) ^ (i + 1) = (-1) ^ (i + 1) := sub_eq_zero.1 h0
      have h2 : (2 : ℤ) ≤ ((ℓ ^ f : ℕ) : ℤ) ^ (i + 1) := by
        have : (2 : ℤ) ≤ ((ℓ ^ f : ℕ) : ℤ) := by exact_mod_cast hQ2
        calc (2 : ℤ) ≤ ((ℓ ^ f : ℕ) : ℤ) := this
          _ = ((ℓ ^ f : ℕ) : ℤ) ^ 1 := (pow_one _).symm
          _ ≤ ((ℓ ^ f : ℕ) : ℤ) ^ (i + 1) := pow_le_pow_right₀ (by linarith) (by omega)
      rw [h1] at h2
      rcases Nat.even_or_odd (i + 1) with he | ho
      · rw [he.neg_one_pow] at h2
        omega
      · rw [ho.neg_one_pow] at h2
        omega
    have hQ0 : ((ℓ ^ f : ℕ) : ℤ) ^ a ≠ 0 := pow_ne_zero _ (by positivity)
    have hidx' : ((sesqUnitaryGroup B).index : ℤ) = ((ℓ ^ f : ℕ) : ℤ) ^ a * T := by
      apply mul_left_cancel₀ (mul_ne_zero hQ0 hU0)
      linear_combination hidxZ
    intro hd
    have h0 : (((sesqUnitaryGroup B).index : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ p).2 hd
    have h1 : ((((ℓ ^ f : ℕ) : ℤ) ^ a * T : ℤ) : ZMod p) = 0 := by
      rw [← hidx']
      exact_mod_cast h0
    rw [hT] at h1
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_prod, Int.cast_add,
      Int.cast_neg, Int.cast_one] at h1
    have hQz : ((ℓ ^ f : ℕ) : ZMod p) ≠ 0 := fun h0 =>
      hpℓ (hp.dvd_of_dvd_pow ((ZMod.natCast_eq_zero_iff (ℓ ^ f) p).1 h0))
    haveI : Fact p.Prime := ⟨hp⟩
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact pow_ne_zero a hQz h2
    · obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.1 h2
      exact crossExcU_pow_add_ne_zero hp hp5 hodd (i + 1) hi

end Index

section OddData

variable {ℓ f : ℕ} {K : Type} [Field K] [Finite K]

theorem crossExcU_bar_eq (h : UnitaryFieldData ℓ f K) {e : ℕ} (hodd : Odd e) (a : K) :
    a ^ (ℓ ^ (f * e)) = h.bar a := by
  obtain ⟨k, rfl⟩ := hodd
  haveI := Fintype.ofFinite K
  have hcard : Fintype.card K = ℓ ^ (2 * f) := by rw [← Nat.card_eq_fintype_card, h.card]
  have h1 : ℓ ^ (f * (2 * k + 1)) = ℓ ^ f * (Fintype.card K) ^ k := by
    rw [hcard, ← pow_mul, ← pow_add]
    congr 1
    ring
  rw [h1, pow_mul, ← h.bar_apply]
  exact FiniteField.pow_card_pow k (h.bar a)

theorem crossExcU_dvd_pow_add_one {p : ℕ} (hodd : Odd (unitaryOrder ℓ f p)) :
    p ∣ ℓ ^ (f * unitaryOrder ℓ f p) + 1 := by
  have h1 : (-((ℓ ^ f : ℕ) : ZMod p)) ^ unitaryOrder ℓ f p = 1 := pow_orderOf_eq_one _
  have h2 : ((ℓ ^ f : ℕ) : ZMod p) ^ unitaryOrder ℓ f p = -1 :=
    neg_eq_iff_eq_neg.1 ((Odd.neg_pow hodd ((ℓ ^ f : ℕ) : ZMod p)).symm.trans h1)
  rw [← ZMod.natCast_eq_zero_iff, pow_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_one]
  calc ((ℓ ^ f : ℕ) : ZMod p) ^ unitaryOrder ℓ f p + 1 = -1 + 1 := by rw [h2]
    _ = 0 := neg_add_cancel 1

end OddData

section RankWindow

variable {ℓ f : ℕ} {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem crossExcU_rank_GU (h : UnitaryFieldData ℓ f K) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpℓ : ¬ p ∣ ℓ) (hodd : Odd (unitaryOrder ℓ f p)) {B : V →ₛₗ[h.bar] V →ₗ[K] K}
    (hB : B.IsSymm) (hBl : B.SeparatingLeft) (uV : (Module.End K V)ˣ)
    (huU : uV ∈ sesqUnitaryGroup B) (hup : uV ^ p = 1)
    (hdim : 4 * unitaryOrder ℓ f p ≤ Module.finrank K V) :
    4 ≤ CFSG.Open.pRank p (centralizer ({uV} : Set (Module.End K V)ˣ) ⊓ sesqUnitaryGroup B) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set e := unitaryOrder ℓ f p with he_def
  have he : 0 < e := unitaryOrder_pos hp hpℓ
  have hpK : ¬ p ∣ Nat.card K := by
    rw [h.card_eq_sq]
    exact fun hd => hpℓ (hp.dvd_of_dvd_pow (hp.dvd_of_dvd_pow hd))
  have hpe : ∀ j : ℕ, p ∣ Nat.card K ^ j - 1 ↔ e ∣ j := crossExcU_card_pow_iff_of_odd h hodd
  have hp0 : (p : K) ≠ 0 := natCast_ne_zero_of_not_dvd_card hp hpK
  let u : Module.End K V := (uV : Module.End K V)
  have hd : HermOddData B u p (f * e) :=
    ⟨by rw [← Units.val_pow_eq_pow_val, hup, Units.val_one],
      fun x y => mem_sesqUnitaryGroup.1 huU x y, crossExcU_dvd_pow_add_one hodd,
      crossExcU_bar_eq h hodd⟩
  have hdeg : ∀ g : Polynomial K, Irreducible g → g ∣ Polynomial.X ^ p - 1 →
      g.natDegree ≤ e := fun g hg hgP =>
    natDegree_le_of_dvd_X_pow_sub_one he ((hpe e).2 dvd_rfl) hg hgP
  obtain ⟨W, hW, hWnd, hW1, hW2⟩ := hd.exists_window hB hBl hp.pos hp0 he hdeg (c := 4) hdim
  have hWC := hermNondeg_isCompl hB hWnd
  have hC := hd.perp_invariant hp.pos hW
  have hB' : (B.domRestrict₁₂ W W).IsSymm := hB.domRestrict W
  have hBl' : (B.domRestrict₁₂ W W).SeparatingLeft := fun w hw =>
    Subtype.ext (hWnd w w.2 fun w' hw' => hw ⟨w', hw'⟩)
  have hidx := crossExcU_not_dvd_index_unitary h hp hp5 hpℓ hodd hB' hBl'
  have hyWp : (u.restrict hW) ^ p = 1 := by
    have h' : ∀ x ∈ W, (u ^ p) x ∈ W := fun x hx => by rw [hd.pow_eq]; simpa using hx
    rw [Module.End.pow_restrict p hW h']
    ext x
    simp [hd.pow_eq]
  let uW : (Module.End K W)ˣ := Units.ofPowEqOne (u.restrict hW) p hyWp hp.ne_zero
  have huW : uW ^ p = 1 := Units.ext (by simpa [uW] using hyWp)
  have huWmem : uW ∈ sesqUnitaryGroup (B.domRestrict₁₂ W W) :=
    mem_sesqUnitaryGroup.2 fun x y => hd.isom x y
  let GU := sesqUnitaryGroup (B.domRestrict₁₂ W W)
  let x₀ : GU := ⟨uW, huWmem⟩
  have hx₀ : x₀ ^ p = 1 := Subtype.ext huW
  have hzp : IsPGroup p (Subgroup.zpowers x₀) := by
    intro z
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 z.2
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, OneMemClass.coe_one, SubgroupClass.coe_pow]
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx₀, one_zpow]
  obtain ⟨P, hP⟩ := hzp.exists_le_sylow
  set S : Subgroup (Module.End K W)ˣ := (P : Subgroup GU).map GU.subtype with hS
  have hSp : IsPGroup p S := P.isPGroup'.map _
  have hne : Module.finrank K W / e < p := by
    rw [Nat.div_lt_iff_lt_mul he]
    nlinarith
  haveI hSab : IsMulCommutative S :=
    isMulCommutative_of_isPGroup_GL (hp.odd_of_ne_two (by omega)) hpK he hpe hne hSp
  have hSidx : ¬ p ∣ S.index := by
    rw [hS, Subgroup.index_map_subtype]
    exact Nat.Prime.not_dvd_mul hp P.not_dvd_index hidx
  let Ssyl : Sylow p (Module.End K W)ˣ := hSp.toSylow hSidx
  have hrank : 4 ≤ CFSG.Open.pRank p S := by
    have h1 := (CFSG.SectionRank.pRank_sylow Ssyl).1
    have h2 : (Ssyl : Subgroup (Module.End K W)ˣ) = S := IsPGroup.toSylow_coe hSp hSidx
    rw [h2] at h1
    rw [h1]
    exact le_pRank_GL hpK he hpe (r := 4) hW1
  have huS : (uW : (Module.End K W)ˣ) ∈ S := ⟨x₀, hP (Subgroup.mem_zpowers x₀), rfl⟩
  have hSle : S ≤ centralizer ({uW} : Set (Module.End K W)ˣ) ⊓ GU := by
    intro s hs
    refine ⟨Subgroup.mem_centralizer_singleton_iff.2 (setLike_mul_comm hs huS), ?_⟩
    obtain ⟨y, -, rfl⟩ := hs
    exact y.2
  have hX : 4 ≤ CFSG.Open.pRank p (centralizer ({uW} : Set (Module.End K W)ˣ) ⊓ GU) :=
    hrank.trans (CFSG.SectionRank.pRank_mono hp.one_lt hSle)
  let ι : (Module.End K W)ˣ →* (Module.End K V)ˣ := Units.map (uBlockEnd hWC)
  have hι : Function.Injective ι := Units.map_injective (uBlockEnd_injective hWC)
  refine hX.trans ((CFSG.SectionRank.pRank_le_map hp.one_lt ι hι _).trans
    (CFSG.SectionRank.pRank_mono hp.one_lt ?_))
  rintro _ ⟨g, ⟨hgc, hgGU⟩, rfl⟩
  have hg' : (g : Module.End K W) * u.restrict hW = u.restrict hW * (g : Module.End K W) := by
    have := Subgroup.mem_centralizer_singleton_iff.1 hgc
    exact congrArg Units.val this
  refine ⟨Subgroup.mem_centralizer_singleton_iff.2 (Units.ext ?_), uBlockEnd_units_mem hB hWC hgGU⟩
  rw [Units.val_mul, Units.val_mul]
  exact uBlockEnd_comm hWC hW hC (g : Module.End K W) hg'

end RankWindow

end CrossExcU

end CFSG.LocalAnalysis.RankFourTheoremC
