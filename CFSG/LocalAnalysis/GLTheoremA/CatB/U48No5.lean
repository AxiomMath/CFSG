module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48SL2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U48

open Matrix CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LieType.Universal.Unitary
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48
open CFSG.RankThree.PartTwo.KFacts.KS21.U58 (K hK card_K card_units_K)
open CFSG.ClassicalInvolution.Phan (Su)

noncomputable section

theorem card_su3 : Nat.card (Su K 2 3 3) = (2 ^ 3) ^ 3 * (((2 ^ 3) ^ 2 - 1) * ((2 ^ 3) ^ 3 + 1)) := by
  have h := CFSG.SectionRank.OddCover.card_statedSU_three (K := K) (p := 2) (f := 3) card_K
  rw [← Nat.card_congr (MulEquiv.subgroupCongr (SUid_eq_statedSU (F := K) (p := 2) (f := 3) card_K
    3)).toEquiv] at h
  rw [h]
  ring

theorem unitary_pow_five_eq_one {n : ℕ} (hn : n ≤ 3) (W : Matrix (Fin n) (Fin n) K)
    (hW : (W.map σ4)ᵀ * W = 1) (h5 : W ^ 5 = 1) : W = 1 := by
  have hdet9 : W.det ^ 9 = 1 := by
    have h1 := congrArg Matrix.det hW
    rw [det_mul, det_transpose, det_one] at h1
    have h2 : (W.map σ4).det = σ4 W.det := by
      have := RingHom.map_det (σ4 : K →+* K) W
      rw [RingHom.mapMatrix_apply] at this
      exact this.symm
    rw [h2, CFSG.LieType.BorelTits.unitaryInvolution_apply] at h1
    calc W.det ^ 9 = W.det ^ (2 ^ 3) * W.det := by ring
      _ = 1 := h1
  have hdet5 : W.det ^ 5 = 1 := by
    have := congrArg Matrix.det h5
    rwa [det_pow, det_one] at this
  have hdet : W.det = 1 := by
    have := pow_gcd_eq_one.2 ⟨hdet9, hdet5⟩
    simpa using this
  have hmul' : W * (W.map σ4)ᵀ = 1 := mul_eq_one_comm.1 hW
  let X : GL (Fin n) K := ⟨W, (W.map σ4)ᵀ, hmul', hW⟩
  have hX : X ∈ SUid σ4 n := by
    rw [mem_SUid]
    exact ⟨hdet, hW⟩
  let X' : Su K 2 3 n := ⟨X, hX⟩
  have hX5 : X' ^ 5 = 1 := by
    apply Subtype.ext
    apply Units.ext
    simpa [X', X] using h5
  have hX1 : X' = 1 := by
    have hord : orderOf X' ∣ 5 := orderOf_dvd_of_pow_eq_one hX5
    interval_cases n
    · exact Subsingleton.elim _ _
    · exact Subtype.ext (Units.ext (by
        ext i j
        rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]
        have := det_unique W
        simp only [Fin.default_eq_zero] at this
        simpa [X', X, this] using hdet))
    · have h2 := orderOf_dvd_natCard X'
      rw [card_su2] at h2
      have := Nat.eq_one_of_dvd_coprimes (by norm_num : Nat.Coprime 5 504) hord h2
      exact orderOf_eq_one_iff.1 this
    · have h2 := orderOf_dvd_natCard X'
      rw [card_su3] at h2
      have := Nat.eq_one_of_dvd_coprimes (by norm_num : Nat.Coprime 5 _) hord h2
      exact orderOf_eq_one_iff.1 this
  have := congrArg (fun Y : Su K 2 3 n => ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) hX1
  simpa [X', X] using this

section Blocks

variable {n : ℕ} {ι : Fin n → Fin 4}

theorem submatrix_mul_block (hι : Function.Injective ι) {x y : Matrix (Fin 4) (Fin 4) K}
    (hx : ∀ a l, l ∉ Set.range ι → x (ι a) l = 0) :
    (x * y).submatrix ι ι = x.submatrix ι ι * y.submatrix ι ι := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  exact (Fintype.sum_of_injective ι hι _ _ (fun l hl => by simp [hx a l hl]) (fun _ => rfl)).symm

theorem submatrix_pow_block (hι : Function.Injective ι) {x : Matrix (Fin 4) (Fin 4) K}
    (hx : ∀ a l, l ∉ Set.range ι → x (ι a) l = 0) (m : ℕ) :
    (x ^ m).submatrix ι ι = (x.submatrix ι ι) ^ m := by
  induction m with
  | zero => simp [Matrix.submatrix_one ι hι]
  | succ m ih => rw [pow_succ', pow_succ', submatrix_mul_block hι hx, ih]

end Blocks

theorem no_five_diag {g w : SU4}
    (hd : (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)).IsDiag) (hg3 : g ^ 3 = 1)
    (hg1 : g ≠ 1) (hw5 : w ^ 5 = 1) (hc : w * g = g * w) : w = 1 := by
  classical
  set M : Matrix (Fin 4) (Fin 4) K := ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hM
  set W : Matrix (Fin 4) (Fin 4) K := ((w : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hW
  set d : Fin 4 → K := fun i => M i i with hdd
  have hMd : diagonal d = M := hd.diagonal_diag
  have hM3 : M ^ 3 = 1 := by
    have h := congrArg (fun y : SU4 => ((y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) hg3
    simpa using h
  have hd3 : ∀ i, d i ^ 3 = 1 := by
    intro i
    rw [← hMd, diagonal_pow] at hM3
    have := congrFun (congrFun hM3 i) i
    rwa [diagonal_apply_eq, one_apply_eq] at this
  have hdet : ∏ i, d i = 1 := by
    have := (mem_SUid.mp g.2).1
    rw [← hM, ← hMd, det_diagonal] at this
    exact this
  have hnot : ∀ i, ∃ l, d l ≠ d i := by
    intro i
    by_contra hall
    push Not at hall
    apply hg1
    have h4 : d i ^ 4 = 1 := by
      have : ∏ l, d l = d i ^ 4 := by simp [hall]
      rwa [← this]
    have hv : d i = 1 := by
      have := pow_gcd_eq_one.2 ⟨h4, hd3 i⟩
      simpa using this
    apply Subtype.ext
    apply Units.ext
    rw [← hM, ← hMd]
    have : d = fun _ => 1 := funext fun l => (hall l).trans hv
    rw [this]
    simp
  have hcomm : ∀ i j, W i j * d j = d i * W i j := by
    intro i j
    have h := congrArg (fun y : SU4 => ((y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i j) hc
    simp only [Subgroup.coe_mul, Units.val_mul] at h
    rw [← hM, ← hMd, mul_diagonal, diagonal_mul] at h
    exact h
  have hz : ∀ i j, d i ≠ d j → W i j = 0 := by
    intro i j hij
    have h2 : W i j * (d j - d i) = 0 := by linear_combination hcomm i j
    rcases mul_eq_zero.1 h2 with h | h
    · exact h
    · exact absurd (sub_eq_zero.1 h).symm hij
  have hU : (W.map σ4)ᵀ * W = 1 := (mem_SUid.mp w.2).2
  have hW5 : W ^ 5 = 1 := by
    have h := congrArg (fun y : SU4 => ((y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) hw5
    simpa using h
  have hW1 : W = 1 := by
    ext i k
    set s : Finset (Fin 4) := Finset.univ.filter fun l => d l = d i with hs
    have hmem : ∀ l, l ∈ s ↔ d l = d i := by intro l; simp [hs]
    have hcard : s.card ≤ 3 := by
      by_contra hlt
      push Not at hlt
      have hle4 : s.card ≤ 4 := by simpa using Finset.card_le_univ s
      have hs4 : s = Finset.univ :=
        Finset.eq_univ_of_card s (by rw [Fintype.card_fin]; omega)
      obtain ⟨l, hl⟩ := hnot i
      exact hl ((hmem l).1 (hs4 ▸ Finset.mem_univ l))
    let ι : Fin s.card → Fin 4 := s.orderEmbOfFin rfl
    have hι : Function.Injective ι := (s.orderEmbOfFin rfl).injective
    have hrange : Set.range ι = (s : Set (Fin 4)) := Finset.range_orderEmbOfFin s rfl
    have hι_mem : ∀ a, d (ι a) = d i := fun a => (hmem _).1 (Finset.orderEmbOfFin_mem s rfl a)
    have hx0 : ∀ a l, l ∉ Set.range ι → W (ι a) l = 0 := by
      intro a l hl
      apply hz
      rw [hι_mem a]
      intro h
      apply hl
      rw [hrange]
      exact (hmem l).2 h.symm
    have hx1 : ∀ a l, l ∉ Set.range ι → ((W.map σ4)ᵀ) (ι a) l = 0 := by
      intro a l hl
      simp only [Matrix.transpose_apply, Matrix.map_apply]
      rw [hz l (ι a), map_zero]
      rw [hι_mem a]
      intro h
      apply hl
      rw [hrange]
      exact (hmem l).2 h
    have hUb : ((W.submatrix ι ι).map σ4)ᵀ * W.submatrix ι ι = 1 := by
      have h1 := submatrix_mul_block hι (y := W) hx1
      rw [hU, Matrix.submatrix_one ι hι] at h1
      have h2 : ((W.submatrix ι ι).map σ4)ᵀ = ((W.map σ4)ᵀ).submatrix ι ι := by
        ext a b
        simp
      rw [h2]
      exact h1.symm
    have hW5b : (W.submatrix ι ι) ^ 5 = 1 := by
      rw [← submatrix_pow_block hι hx0 5, hW5, Matrix.submatrix_one ι hι]
    have hb1 := unitary_pow_five_eq_one hcard (W.submatrix ι ι) hUb hW5b
    by_cases hik : d k = d i
    · have hia : i ∈ Set.range ι := by rw [hrange]; exact (hmem i).2 rfl
      have hka : k ∈ Set.range ι := by rw [hrange]; exact (hmem k).2 hik
      obtain ⟨a, ha⟩ := hia
      obtain ⟨b, hb⟩ := hka
      have key := congrFun (congrFun hb1 a) b
      rw [← ha, ← hb]
      simpa [Matrix.submatrix_apply, Matrix.one_apply, hι.eq_iff] using key
    · have hne : i ≠ k := fun h => hik (by rw [h])
      rw [hz i k (fun h => hik h.symm), Matrix.one_apply_ne hne]
  apply Subtype.ext
  apply Units.ext
  simpa [hW] using hW1

theorem no_five {g w : SU4} (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) (hw5 : w ^ 5 = 1)
    (hc : w * g = g * w) : w = 1 := by
  obtain ⟨a, ha⟩ := exists_conj_isDiag (P := Subgroup.zpowers g)
    (fun x hx y hy => by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      rw [← _root_.zpow_add, ← _root_.zpow_add, add_comm])
    (fun x hx => by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm i, _root_.zpow_mul, zpow_natCast, hg3, _root_.one_zpow])
  have hgd := ha g (Subgroup.mem_zpowers g)
  have h : a * w * a⁻¹ = 1 := no_five_diag (g := a * g * a⁻¹) (w := a * w * a⁻¹) hgd
    (by rw [conj_pow, hg3]; group)
    (fun h1 => hg1 (by
      have : g = a⁻¹ * (a * g * a⁻¹) * a := by group
      rw [this, h1]; group))
    (by rw [conj_pow, hw5]; group)
    (by
      calc a * w * a⁻¹ * (a * g * a⁻¹) = a * (w * g) * a⁻¹ := by group
        _ = a * (g * w) * a⁻¹ := by rw [hc]
        _ = a * g * a⁻¹ * (a * w * a⁻¹) := by group)
  have : w = a⁻¹ * (a * w * a⁻¹) * a := by group
  rw [this, h]
  group

end

end CFSG.LocalAnalysis.GLTheoremA.CatB.U48
