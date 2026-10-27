module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbSpFixed
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SpResidual.OddFixed
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SpResidual.TrivialTwo
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbSpSection

public noncomputable section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.AGLEmbedding.ParabPrime (perfectJoin perfectJoin_le perfectJoin_perfect le_perfectJoin)
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SpResidual
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (flagStabilizer)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (flag isoFlag)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {r : ℕ}

section Counting

theorem fixed_card_modEq {i : ℕ} (hi : i ≤ r) {v : StatedSp r (ZMod 2)} (hv3 : v ^ 3 = 1)
    (hF : ∀ x ∈ flag r (ZMod 2) i, spMat v *ᵥ x ∈ flag r (ZMod 2) i) :
    Nat.card {x : ↥(flag r (ZMod 2) i) // spMat v *ᵥ (x : Fin r ⊕ Fin r → ZMod 2) = x} ≡
      2 ^ i [MOD 3] := by
  classical
  set F := flag r (ZMod 2) i with hFdef
  let f : Function.End F := fun x => ⟨spMat v *ᵥ (x : Fin r ⊕ Fin r → ZMod 2), hF x x.2⟩
  have hv3' : spMat v ^ 3 = 1 := by rw [← spMat_pow, hv3]; rfl
  have hf3 : f ^ 3 = 1 := by
    funext x
    apply Subtype.ext
    have h3 : spMat v *ᵥ (spMat v *ᵥ (spMat v *ᵥ (x : Fin r ⊕ Fin r → ZMod 2))) = x := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        show spMat v * spMat v * spMat v = spMat v ^ 3 by simp [pow_succ, mul_assoc], hv3',
        Matrix.one_mulVec]
    exact h3
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let _ : Fintype F := Fintype.ofFinite F
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 3) (n := 1) (by simpa using hf3)
  have hcard : Fintype.card F = 2 ^ i := by
    have hfr : Module.finrank (ZMod 2) F = i :=
      SymplecticHigher.finrank_flag (r := r) (K := ZMod 2) (by omega)
    rw [Fintype.card_eq_nat_card, Module.natCard_eq_pow_finrank (K := ZMod 2), hfr]
    simp
  rw [hcard] at hmod
  have hfix : Nat.card {x : ↥F // spMat v *ᵥ (x : Fin r ⊕ Fin r → ZMod 2) = x} =
      Fintype.card f.fixedPoints := by
    rw [Fintype.card_eq_nat_card]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    constructor
    · intro h; exact Subtype.ext h
    · intro h; exact congrArg Subtype.val h
  rw [hfix]
  exact hmod.symm

end Counting

section Kill

variable {I : Set ℕ}

structure KillData (r : ℕ) (I : Set ℕ) (v : StatedSp r (ZMod 2)) : Prop where
  hI : ∀ i ∈ I, 1 ≤ i ∧ i ≤ r
  join : v ∈ perfectJoin (flagStabilizer r (ZMod 2) I)
  pow : v ^ 3 = 1
  ne_one : v ≠ 1
  free : PerfFree v

theorem mulVec_mem_flag {g : StatedSp r (ZMod 2)} (hg : g ∈ flagStabilizer r (ZMod 2) I) {i : ℕ}
    (hi : i ∈ I) {x : Fin r ⊕ Fin r → ZMod 2} (hx : x ∈ flag r (ZMod 2) i) :
    spMat g *ᵥ x ∈ flag r (ZMod 2) i :=
  spMat_mulVec_mem_of_mem_stabilizer (SymplecticHigher.mem_flagStabilizer.mp hg i hi) hx

theorem flag_isotropic {i : ℕ} (hir : i ≤ r) {x y : Fin r ⊕ Fin r → ZMod 2}
    (hx : x ∈ flag r (ZMod 2) i) (hy : y ∈ flag r (ZMod 2) i) :
    pairedSympForm (ZMod 2) r x y = 0 :=
  (SymplecticHigher.isCompleteIsotropicFlag_flag (r := r) (K := ZMod 2)).2.2 i hir x hx y hy

theorem mem_flag_mono {i j : ℕ} (hji : j ≤ i) (hir : i ≤ r) {x : Fin r ⊕ Fin r → ZMod 2}
    (hx : x ∈ flag r (ZMod 2) j) : x ∈ flag r (ZMod 2) i := by
  rw [SymplecticFlag.mem_flag_of_le (by omega)] at hx
  rw [SymplecticFlag.mem_flag_of_le hir, SymplecticFlag.mem_isoFlag] at *
  exact ⟨hx.1, fun k hk => hx.2 k (by omega)⟩

theorem KillData.no_fixed_even {v : StatedSp r (ZMod 2)} (h : KillData r I v) {i : ℕ} (hi : i ∈ I)
    (hev : Even i) : ∀ x ∈ flag r (ZMod 2) i, spMat v *ᵥ x = x → x = 0 := by
  intro a haF hva
  by_contra ha0
  have hir := (h.hI i hi).2
  have hr1 : 1 ≤ r := by have := (h.hI i hi).1; omega
  have hvJ : v ∈ flagStabilizer r (ZMod 2) I := perfectJoin_le _ h.join
  have hB : ∀ x ∈ flag r (ZMod 2) i, spMat v *ᵥ x = x → x = 0 ∨ x = a := fun x hx hvx =>
    fixed_isotropic_pair hr1 h.pow h.ne_one h.free hva ha0 hvx (flag_isotropic hir haF hx)
  have hmod := fixed_card_modEq hir h.pow (fun x hx => mulVec_mem_flag hvJ hi hx)
  have hcard : Nat.card {x : ↥(flag r (ZMod 2) i) // spMat v *ᵥ (x : Fin r ⊕ Fin r → ZMod 2) = x}
      = 2 := by
    rw [Nat.card_eq_two_iff]
    refine ⟨⟨⟨0, Submodule.zero_mem _⟩, by simp⟩, ⟨⟨a, haF⟩, hva⟩, ?_, ?_⟩
    · intro hxy
      exact ha0 (congrArg (fun z => (z.1 : Fin r ⊕ Fin r → ZMod 2)) hxy).symm
    · ext ⟨⟨z, hz⟩, hzv⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      rcases hB z hz hzv with h0 | h0
      · left; subst h0; rfl
      · right; subst h0; rfl
  rw [hcard] at hmod
  obtain ⟨k, rfl⟩ := hev
  have h1 : 2 ^ (k + k) % 3 = 1 := by
    rw [← two_mul, pow_mul, Nat.pow_mod]; norm_num
  unfold Nat.ModEq at hmod
  omega

theorem KillData.false_of_two_mem {v : StatedSp r (ZMod 2)} (h : KillData r I v) (h2 : 2 ∈ I) :
    False := by
  have hfix2 := TrivialTwo.fixes_flag_two_of_mem_perfectJoin h.hI h2 h.join
  have hr2 : 2 ≤ r := (h.hI 2 h2).2
  have he0 : (Pi.single (Sum.inl ⟨0, by omega⟩) 1 : Fin r ⊕ Fin r → ZMod 2) ∈
      flag r (ZMod 2) 2 := single_mem_flag hr2 0 (by omega) (by omega)
  have h0 := h.no_fixed_even h2 (by decide) _ he0 (hfix2 _ he0)
  have := congrFun h0 (Sum.inl ⟨0, by omega⟩)
  simp at this

theorem KillData.false_of_even_odd {v : StatedSp r (ZMod 2)} (h : KillData r I v) {i j : ℕ}
    (hi : i ∈ I) (hev : Even i) (hj : j ∈ I) (hodd : Odd j) (hji : j ≤ i) : False := by
  have hvJ : v ∈ flagStabilizer r (ZMod 2) I := perfectJoin_le _ h.join
  obtain ⟨a, haF, ha0, hva⟩ := OddFixed.exists_fixed_vector_of_odd h.hI hj hodd h.pow hvJ
  exact ha0 (h.no_fixed_even hi hev a (mem_flag_mono hji (h.hI i hi).2 haF) hva)

theorem card_section_le_four (A B : Submodule (ZMod 2) (Fin r ⊕ Fin r → ZMod 2)) (hAB : A ≤ B)
    (h : Module.finrank (ZMod 2) B ≤ Module.finrank (ZMod 2) A + 2) :
    Nat.card (↥B ⧸ A.comap B.subtype) ≤ 4 := by
  have h1 := Submodule.finrank_quotient_add_finrank (A.comap B.subtype)
  have h2 : Module.finrank (ZMod 2) (A.comap B.subtype) = Module.finrank (ZMod 2) A :=
    LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hAB)
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  calc 2 ^ Module.finrank (ZMod 2) (↥B ⧸ A.comap B.subtype) ≤ 2 ^ 2 :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 4 := by norm_num

theorem add_self_vec (x : Fin r ⊕ Fin r → ZMod 2) : x + x = 0 := by
  funext k
  simp only [Pi.add_apply, Pi.zero_apply]
  generalize x k = t
  revert t; decide

theorem neg_vec (x : Fin r ⊕ Fin r → ZMod 2) : -x = x := by
  rw [neg_eq_iff_add_eq_zero]; exact add_self_vec x

theorem orthogonal_isoFlag_eq {i : ℕ} (hir : i < r) :
    (pairedSympForm (ZMod 2) r).orthogonal (isoFlag r (ZMod 2) i) = flag r (ZMod 2) (2 * r - i) := by
  rw [flag, ite_eq_right (not_le.mpr (by omega))]
  congr 2
  omega

theorem KillData.false_of_pred_mem {v : StatedSp r (ZMod 2)} (h : KillData r I v) {i : ℕ}
    (hi : i ∈ I) (hodd : Odd i) (hir : i + 1 = r) : False := by
  have hir' := (h.hI i hi).2
  have hi1 := (h.hI i hi).1
  have hr1 : 1 ≤ r := by omega
  have hvJ : v ∈ flagStabilizer r (ZMod 2) I := perfectJoin_le _ h.join
  set A : Submodule (ZMod 2) (Fin r ⊕ Fin r → ZMod 2) := flag r (ZMod 2) i with hAdef
  set B : Submodule (ZMod 2) (Fin r ⊕ Fin r → ZMod 2) :=
    (pairedSympForm (ZMod 2) r).orthogonal (isoFlag r (ZMod 2) i) with hBdef
  have hAiso : A = isoFlag r (ZMod 2) i := by
    ext x; exact SymplecticFlag.mem_flag_of_le hir'
  have hBmem : ∀ x, x ∈ B ↔ ∀ y ∈ A, pairedSympForm (ZMod 2) r y x = 0 := by
    intro x
    rw [hBdef, LinearMap.BilinForm.mem_orthogonal_iff, hAiso]
  have hAB : A ≤ B := fun x hx => (hBmem x).2 fun y hy => flag_isotropic hir' hy hx
  have hAst : ∀ g ∈ flagStabilizer r (ZMod 2) I, ∀ x ∈ A, spMat g *ᵥ x ∈ A :=
    fun g hg x hx => mulVec_mem_flag hg hi hx
  have hBst : ∀ g ∈ flagStabilizer r (ZMod 2) I, ∀ x ∈ B, spMat g *ᵥ x ∈ B := by
    intro g hg x hx
    rw [hBmem] at hx ⊢
    intro y hy
    have hy' : spMat g⁻¹ *ᵥ y ∈ A := hAst _ (inv_mem hg) y hy
    have := pairedSympForm_spMat_mulVec g (spMat g⁻¹ *ᵥ y) x
    rw [Matrix.mulVec_mulVec, spMat_mul_inv, Matrix.one_mulVec] at this
    rw [this]
    exact hx _ hy'
  have hfrB : Module.finrank (ZMod 2) B = 2 * r - i := by
    have := SymplecticHigher.finrank_flag (r := r) (K := ZMod 2) (i := 2 * r - i) (by omega)
    rw [hBdef, orthogonal_isoFlag_eq (by omega)]
    exact this
  have hfrA : Module.finrank (ZMod 2) A = i :=
    SymplecticHigher.finrank_flag (r := r) (K := ZMod 2) (by omega)
  have hcard := card_section_le_four A B hAB (by omega)
  set w : Fin r ⊕ Fin r → ZMod 2 := Pi.single (Sum.inl ⟨i, by omega⟩) 1 with hw
  have hwB : w ∈ B := by
    show w ∈ (pairedSympForm (ZMod 2) r).orthogonal (isoFlag r (ZMod 2) i)
    rw [SymplecticFlag.mem_orthogonal_isoFlag]
    intro j _
    simp [hw]
  have hwA : w ∉ A := by
    rw [hAiso, SymplecticFlag.mem_isoFlag]
    intro hmem
    have := hmem.2 ⟨i, by omega⟩ le_rfl
    simp [hw] at this
  have hdA : spMat v *ᵥ w - w ∈ A := section_trivial A B _ hAst hBst hcard h.join w hwB
  set d := spMat v *ᵥ w - w with hd
  obtain ⟨a, haF, ha0, hva⟩ := OddFixed.exists_fixed_vector_of_odd h.hI hi hodd h.pow hvJ
  have hvdA : spMat v *ᵥ d ∈ A := hAst v hvJ d hdA
  have hv3' : spMat v ^ 3 = 1 := by rw [← spMat_pow, h.pow]; rfl
  have hvvv : ∀ x : Fin r ⊕ Fin r → ZMod 2, spMat v *ᵥ (spMat v *ᵥ (spMat v *ᵥ x)) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      show spMat v * spMat v * spMat v = spMat v ^ 3 by simp [pow_succ, mul_assoc], hv3',
      Matrix.one_mulVec]
  set c := w + spMat v *ᵥ w + spMat v *ᵥ (spMat v *ᵥ w) with hcdef
  have hcfix : spMat v *ᵥ c = c := by
    rw [hcdef, Matrix.mulVec_add, Matrix.mulVec_add, hvvv]
    abel
  have hc2 : c = w + spMat v *ᵥ d := by
    rw [hd, Matrix.mulVec_sub, sub_eq_add_neg, neg_vec, hcdef]
    abel
  have hcB : c ∈ B := by rw [hc2]; exact B.add_mem hwB (hAB hvdA)
  have hform : pairedSympForm (ZMod 2) r a c = 0 := (hBmem c).1 hcB a haF
  have hK := fixed_isotropic_pair hr1 h.pow h.ne_one h.free hva ha0 hcfix hform
  have hcA : c ∈ A := by
    rcases hK with h0 | h0
    · rw [h0]; exact A.zero_mem
    · rw [h0]; exact haF
  apply hwA
  have : w = c - spMat v *ᵥ d := by rw [hc2]; abel
  rw [this]
  exact A.sub_mem hcA hvdA

theorem flag_one_cases {y : Fin r ⊕ Fin r → ZMod 2} (hr : 1 ≤ r)
    (hy : y ∈ flag r (ZMod 2) 1) :
    y = 0 ∨ y = Pi.single (Sum.inl ⟨0, by omega⟩) 1 := by
  rw [SymplecticFlag.mem_flag_of_le hr, SymplecticFlag.mem_isoFlag] at hy
  have hc : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
  rcases hc (y (Sum.inl ⟨0, by omega⟩)) with h0 | h1
  · left
    funext k
    rcases k with k | k
    · by_cases hk : (k : ℕ) = 0
      · have : k = ⟨0, by omega⟩ := Fin.ext hk
        rw [this]; simpa using h0
      · simpa using hy.2 k (by omega)
    · simpa using hy.1 k
  · right
    funext k
    rcases k with k | k
    · by_cases hk : (k : ℕ) = 0
      · have : k = ⟨0, by omega⟩ := Fin.ext hk
        rw [this]; simpa using h1
      · rw [hy.2 k (by omega)]
        have hne : (Sum.inl k : Fin r ⊕ Fin r) ≠ Sum.inl ⟨0, by omega⟩ := by
          intro hh
          apply hk
          have := Sum.inl_injective hh
          simpa using congrArg Fin.val this
        rw [Pi.single_eq_of_ne hne]
    · simpa using hy.1 k

theorem KillData.false_of_one_three_mem {v : StatedSp r (ZMod 2)} (h : KillData r I v)
    (h1 : 1 ∈ I) (h3 : 3 ∈ I) : False := by
  have hr3 : 3 ≤ r := (h.hI 3 h3).2
  have hr1 : 1 ≤ r := by omega
  have hvJ : v ∈ flagStabilizer r (ZMod 2) I := perfectJoin_le _ h.join
  set A : Submodule (ZMod 2) (Fin r ⊕ Fin r → ZMod 2) := flag r (ZMod 2) 1 with hAdef
  set B : Submodule (ZMod 2) (Fin r ⊕ Fin r → ZMod 2) := flag r (ZMod 2) 3 with hBdef
  have hAB : A ≤ B := fun x hx => mem_flag_mono (by omega) hr3 hx
  have hfrB : Module.finrank (ZMod 2) B = 3 :=
    SymplecticHigher.finrank_flag (r := r) (K := ZMod 2) (by omega)
  have hfrA : Module.finrank (ZMod 2) A = 1 :=
    SymplecticHigher.finrank_flag (r := r) (K := ZMod 2) (by omega)
  have hcard := card_section_le_four A B hAB (by omega)
  have hAst : ∀ g ∈ flagStabilizer r (ZMod 2) I, ∀ x ∈ A, spMat g *ᵥ x ∈ A :=
    fun g hg x hx => mulVec_mem_flag hg h1 hx
  have hBst : ∀ g ∈ flagStabilizer r (ZMod 2) I, ∀ x ∈ B, spMat g *ᵥ x ∈ B :=
    fun g hg x hx => mulVec_mem_flag hg h3 hx
  have hsec := section_trivial A B _ hAst hBst hcard h.join
  obtain ⟨a, haF, ha0, hva⟩ := OddFixed.exists_fixed_vector_of_odd h.hI h1 (by decide) h.pow hvJ
  have hAfix : ∀ y ∈ A, spMat v *ᵥ y = y := by
    intro y hy
    rcases flag_one_cases hr1 hy with h0 | h0
    · rw [h0]; simp
    · rcases flag_one_cases hr1 haF with h0' | h0'
      · exact absurd h0' ha0
      · rw [h0, ← h0']; exact hva
  have hv3' : spMat v ^ 3 = 1 := by rw [← spMat_pow, h.pow]; rfl
  have hvvv : ∀ x : Fin r ⊕ Fin r → ZMod 2, spMat v *ᵥ (spMat v *ᵥ (spMat v *ᵥ x)) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      show spMat v * spMat v * spMat v = spMat v ^ 3 by simp [pow_succ, mul_assoc], hv3',
      Matrix.one_mulVec]
  have hBfix : ∀ x ∈ B, spMat v *ᵥ x = x := by
    intro x hx
    have hd : spMat v *ᵥ x - x ∈ A := hsec x hx
    have hfd := hAfix _ hd
    rw [Matrix.mulVec_sub] at hfd
    have hvvx : spMat v *ᵥ (spMat v *ᵥ x) = x := by
      have h1 : spMat v *ᵥ (spMat v *ᵥ x) = (spMat v *ᵥ x - x) + spMat v *ᵥ x := by
        rw [← hfd]; abel
      rw [h1, sub_eq_add_neg, neg_vec]
      calc (spMat v *ᵥ x + x) + spMat v *ᵥ x = (spMat v *ᵥ x + spMat v *ᵥ x) + x := by abel
        _ = x := by rw [add_self_vec, zero_add]
    have := hvvv x
    rw [hvvx] at this
    exact this
  have he0 : (Pi.single (Sum.inl ⟨0, by omega⟩) 1 : Fin r ⊕ Fin r → ZMod 2) ∈ B :=
    single_mem_flag hr3 0 (by omega) (by omega)
  have he1 : (Pi.single (Sum.inl ⟨1, by omega⟩) 1 : Fin r ⊕ Fin r → ZMod 2) ∈ B :=
    single_mem_flag hr3 1 (by omega) (by omega)
  have hne0 : (Pi.single (Sum.inl ⟨0, by omega⟩) 1 : Fin r ⊕ Fin r → ZMod 2) ≠ 0 := by
    intro h0
    have := congrFun h0 (Sum.inl ⟨0, by omega⟩)
    simp at this
  have hiso := flag_isotropic hr3 he0 he1
  rcases fixed_isotropic_pair hr1 h.pow h.ne_one h.free (hBfix _ he0) hne0 (hBfix _ he1) hiso
    with h0 | h0
  · have := congrFun h0 (Sum.inl ⟨1, by omega⟩)
    simp at this
  · have := congrFun h0 (Sum.inl ⟨1, by omega⟩)
    simp at this

end Kill

end CFSG.HardMathSupport.Curtis.UnitaryLevi
