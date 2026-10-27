module

public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.DoubledWord
public import CFSG.LieType.SpecialLinear.BorelTwist.Hecke
public import CFSG.LieType.SpecialLinear.TypeLabel.Basic
public import CFSG.LieType.SpecialLinear.TypeLabel.Period

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.Quasithin.SmithCurtis CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
  CFSG.LieType.Universal.Unitary
open scoped MatrixGroups

theorem testBit_add_mod_eq_of_dvd {f s a : ℕ} (ha : a < 2 ^ f)
    (hdvd : 2 ^ f - 1 ∣ a * (2 ^ s - 1)) {r : ℕ} (hr : r < f) :
    a.testBit ((r + s) % f) = a.testBit r := by
  have hf : 1 ≤ f := by omega
  let C : Finset ℕ := (Finset.range f).filter (fun j => a.testBit j)
  have hC : C ⊆ Finset.range f := Finset.filter_subset _ _
  have hsum : ∑ j ∈ C, 2 ^ j = a := by
    rw [← sum_testBit_fin_eq ha, Finset.sum_filter]
    exact (Fin.sum_univ_eq_sum_range (fun i => if a.testBit i then 2 ^ i else 0) f).symm
  have hmod : 2 ^ s * ∑ j ∈ C, 2 ^ j ≡ ∑ j ∈ C, 2 ^ j [MOD 2 ^ f - 1] := by
    have hle : a ≤ 2 ^ s * a := Nat.le_mul_of_pos_left a (Nat.two_pow_pos s)
    have hdiff : 2 ^ s * a - a = a * (2 ^ s - 1) := by
      rw [Nat.mul_sub_one, Nat.mul_comm a (2 ^ s)]
    rw [hsum]
    exact ((Nat.modEq_iff_dvd' hle).mpr (by rw [hdiff]; exact hdvd)).symm
  have hmem := CFSG.HardMathSupport.U4FF.digits_mem_shift_iff (m := f) (d := s) hf hC hmod hr
  exact Bool.eq_iff_iff.mpr (by
    simpa [C, hr, Nat.mod_lt _ (by omega : 0 < f)] using hmem)

private theorem testBit_bDigit {f n : ℕ} (ε : Fin f → Finset (Fin n)) (j : Fin n) {r : ℕ}
    (hr : r < f) : (bDigit ε j).testBit r = decide (j ∈ ε ⟨r, hr⟩) := by
  let S : Finset (Fin f) := Finset.univ.filter fun i => j ∈ ε i
  let S' : Finset ℕ := S.image (fun i : Fin f => (i : ℕ))
  have hS'sum : ∑ i ∈ S', 2 ^ i = bDigit ε j := by
    dsimp only [S', S]
    rw [Finset.sum_image (fun i _ q _ h => Fin.ext h), bDigit, ← Finset.sum_filter]
  have hbits : (bDigit ε j).bitIndices.toFinset = S' := by
    rw [← hS'sum]
    exact Finset.toFinset_bitIndices_sum_two_pow S'
  have hiff : ((bDigit ε j).testBit r : Prop) ↔ j ∈ ε ⟨r, hr⟩ := by
    have h1 : (bDigit ε j).testBit r = true ↔ r ∈ (bDigit ε j).bitIndices.toFinset := by
      rw [List.mem_toFinset, Nat.mem_bitIndices]
    rw [h1, hbits]
    simp only [S', S, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨q, hq, hqv⟩
      have hqr : q = ⟨r, hr⟩ := Fin.ext hqv
      simpa [hqr] using hq
    · intro hr'
      exact ⟨⟨r, hr⟩, hr', rfl⟩
  exact Bool.eq_iff_iff.mpr (by simpa [decide_eq_true_eq] using hiff)

theorem rotate_eq_of_dvd_bDigit {m f : ℕ} (ε : Fin f → Finset (Fin (m + 1)))
    (h0 : ∀ r, (0 : Fin (m + 1)) ∉ ε r) {s : ℕ}
    (hdvd : ∀ j : Fin m, 2 ^ f - 1 ∣ bDigit ε j.succ * (2 ^ s - 1)) (r : Fin f) :
    ε ⟨(r + s) % f, Nat.mod_lt _ r.pos⟩ = ε r := by
  ext j
  induction j using Fin.cases with
  | zero => simp [h0]
  | succ t =>
    have hb := testBit_add_mod_eq_of_dvd (f := f) (s := s) (a := bDigit ε t.succ)
      (bDigit_lt ε t.succ) (hdvd t) (r := (r : ℕ)) r.isLt
    rw [testBit_bDigit ε t.succ (r := ((r : ℕ) + s) % f) (hr := Nat.mod_lt _ r.pos),
      testBit_bDigit ε t.succ (r := (r : ℕ)) (hr := r.isLt)] at hb
    exact decide_eq_decide.mp hb

theorem dvd_card_ne_empty_of_rotate {f : ℕ} {ι : Type*} [DecidableEq ι] (ε : Fin f → Finset ι)
    {a : ℕ}
    (hrot : ∀ r : Fin f, ε ⟨(r + a) % f, Nat.mod_lt _ r.pos⟩ = ε r) :
    f / Nat.gcd a f ∣ (Finset.univ.filter fun r => ε r ≠ ∅).card := by
  classical
  cases f with
  | zero => simp
  | succ n =>
    let N := n + 1
    let w : ZMod N → Finset ι := fun x => ε x
    have hper : ∀ i : ZMod N, w (i + (a : ZMod N)) = w i := by
      intro i
      change ε (i + (a : ZMod N)) = ε i
      have hval : (i + (a : ZMod N)).val = (i.val + a) % N := by
        rw [ZMod.val_add, ZMod.val_natCast, Nat.add_mod_mod]
      have heq : i + (a : ZMod N) =
          (⟨(i.val + a) % N, Nat.mod_lt _ (by omega : 0 < N)⟩ : Fin N) := by
        apply Fin.ext
        exact hval
      rw [heq]
      exact hrot i
    let H : AddSubgroup (ZMod N) := AddSubgroup.zmultiples (a : ZMod N)
    have hHcard : Nat.card H = N / Nat.gcd a N := by
      dsimp only [H]
      rw [Nat.card_zmultiples, ZMod.addOrderOf_coe a (by omega : N ≠ 0), Nat.gcd_comm]
    let A := {i : ZMod N // w i ≠ ∅}
    let vaddH : H → A → A := fun x y =>
      ⟨(x : ZMod N) + y.1, by
        have h : w ((x : ZMod N) + y.1) = w y.1 := by
          rw [add_comm]
          exact CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.zsmul_period w hper
            (x : ZMod N) x.2 y.1
        intro h0
        exact y.2 (h.symm.trans h0)⟩
    let : AddAction H A :=
      { vadd := vaddH
        zero_vadd := by
          intro y
          apply Subtype.ext
          change (0 : ZMod N) + y.1 = y.1
          simp
        add_vadd := by
          intro x y z
          apply Subtype.ext
          change ((x : ZMod N) + (y : ZMod N)) + z.1 = (x : ZMod N) + ((y : ZMod N) + z.1)
          rw [add_assoc] }
    have hvadd : ∀ (x : H) (y : A), (x +ᵥ y).1 = (x : ZMod N) + y.1 := fun _ _ => rfl
    have hfree : ∀ b : A, AddAction.stabilizer H b = ⊥ := by
      intro b
      ext x
      constructor
      · intro hx
        rw [AddSubgroup.mem_bot]
        apply Subtype.ext
        have h := congrArg Subtype.val (AddAction.mem_stabilizer_iff.mp hx)
        rw [hvadd] at h
        have h' : (x : ZMod N) + b.1 = 0 + b.1 := by simpa using h
        exact add_right_cancel h'
      · intro hx
        rw [AddSubgroup.mem_bot] at hx
        subst hx
        simp
    have hcardA : Nat.card A =
        Nat.card (Quotient (AddAction.orbitRel H A)) * (N / Nat.gcd a N) := by
      have e := AddAction.selfEquivOrbitsQuotientProd (G := H) (X := A) hfree
      calc
        Nat.card A = Nat.card (Quotient (AddAction.orbitRel H A) × H) := Nat.card_congr e
        _ = Nat.card (Quotient (AddAction.orbitRel H A)) * Nat.card H := Nat.card_prod _ _
        _ = Nat.card (Quotient (AddAction.orbitRel H A)) * (N / Nat.gcd a N) := by rw [hHcard]
    have hdiv : N / Nat.gcd a N ∣ Nat.card A := by
      rw [hcardA]
      exact dvd_mul_left _ _
    have hfin : Nat.card A =
        (Finset.univ.filter fun r : Fin (n + 1) => ε r ≠ ∅).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      rfl
    rw [← hfin]
    exact hdiv

theorem rotate_half_of_card_eq_two {f : ℕ} {ι : Type*} [DecidableEq ι] (ε : Fin f → Finset ι)
    {s : ℕ} (hs : 0 < s) (hsf : s < f)
    (hrot : ∀ r : Fin f, ε ⟨(r + s) % f, Nat.mod_lt _ r.pos⟩ = ε r)
    (h2 : (Finset.univ.filter fun r => ε r ≠ ∅).card = 2) :
    ∃ e, f = 2 * e ∧ ∀ r : Fin f, ε ⟨(r + e) % f, Nat.mod_lt _ r.pos⟩ = ε r := by
  classical
  have hf : 0 < f := by omega
  let g := Nat.gcd s f
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left f hs
  have hgle : g ≤ s := Nat.gcd_le_left f hs
  have hgf : g ∣ f := Nat.gcd_dvd_right s f
  have hfdiv : f / g ∣ (Finset.univ.filter fun r => ε r ≠ ∅).card :=
    dvd_card_ne_empty_of_rotate ε (a := s) hrot
  rw [h2] at hfdiv
  have hle : f / g ≤ 2 := Nat.le_of_dvd (by norm_num) hfdiv
  have hne1 : f / g ≠ 1 := by
    intro h
    have hfg : f = g := by
      rw [← Nat.div_mul_cancel hgf, h, one_mul]
    omega
  have hne0 : f / g ≠ 0 := by
    have h := Nat.div_pos (Nat.le_of_dvd hf hgf) hgpos
    omega
  have hfg2 : f / g = 2 := by
    have h2' : 2 ≤ f / g := by
      by_contra hlt
      have h1 : 1 ≤ f / g := Nat.one_le_iff_ne_zero.mpr hne0
      have : f / g = 1 := by omega
      exact hne1 this
    exact le_antisymm hle h2'
  have hf2g : f = 2 * g := by
    rw [← Nat.div_mul_cancel hgf, hfg2]
  have hstep : ∀ x : ℕ, ε ⟨(x + s) % f, Nat.mod_lt _ hf⟩ = ε ⟨x % f, Nat.mod_lt _ hf⟩ := by
    intro x
    have h := hrot ⟨x % f, Nat.mod_lt _ hf⟩
    simpa [Nat.mod_add_mod] using h
  have hmul : ∀ k x : ℕ,
      ε ⟨(x + k * s) % f, Nat.mod_lt _ hf⟩ = ε ⟨x % f, Nat.mod_lt _ hf⟩ := by
    intro k
    induction k with
    | zero =>
        intro x
        simp
    | succ k ih =>
        intro x
        have h1 : x + (k + 1) * s = (x + k * s) + s := by ring
        rw [h1, hstep, ih]
  obtain ⟨m, _, hm⟩ := Nat.exists_mul_mod_eq_gcd (k := f) (n := s)
    (by have h := Nat.gcd_le_left f hs; omega)
  have hm' : s * m % f = g := hm
  refine ⟨g, hf2g, fun r => ?_⟩
  have h1 : (r.val + g) % f = (r.val + m * s) % f := by
    have h := Nat.add_mod_mod r.val (s * m) f
    rw [hm'] at h
    rwa [Nat.mul_comm m s]
  have h2' : ε (⟨(r.val + m * s) % f, Nat.mod_lt _ hf⟩ : Fin f) = ε r := by
    have h := hmul m r.val
    simpa [Nat.mod_eq_of_lt r.isLt] using h
  have hfin : (⟨(r.val + g) % f, Nat.mod_lt _ r.pos⟩ : Fin f) =
      ⟨(r.val + m * s) % f, Nat.mod_lt _ r.pos⟩ := by
    apply Fin.ext
    exact h1
  rw [hfin]
  exact h2'

variable {m f : ℕ} {F : Type} [Field F] [Fintype F] [CharP F 2] {k : Type} [Field k]
  [CharP k 2] [Algebra F k]

omit [Fintype F] [CharP F 2] [CharP k 2] [Algebra F k] in
private theorem slChiEps_slFieldAut (φ : F →+* k) (ε : Fin f → Finset (Fin (m + 1)))
    (τ : F ≃+* F) {e : ℕ} (hτ : ∀ x, τ x = x ^ 2 ^ e)
    (g : SpecialLinearGroup (Fin (m + 1)) F) :
    slChiEps m φ ε (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut
        (Fin (m + 1)) F τ g) = slChiEps m φ ε g ^ 2 ^ e := by
  unfold slChiEps
  rw [slFieldAut_matrix]
  simp only [Matrix.map_apply]
  have hprod : (∏ a, (τ.toRingHom ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a a)) ^
        bExp ε a) =
      (∏ a, (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a a ^ bExp ε a) ^ 2 ^ e := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [show τ.toRingHom ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a a) =
        (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a a ^ 2 ^ e from hτ _,
      ← pow_mul, ← pow_mul, mul_comm]
  rw [hprod, map_pow]

omit [CharP k 2] in
theorem rotate_eq_of_chi_pow (hF : Fintype.card F = 2 ^ f)
    (ε : Fin f → Finset (Fin (m + 1))) (h0 : ∀ r, (0 : Fin (m + 1)) ∉ ε r)
    {χ : SpecialLinearGroup (Fin (m + 1)) F → k}
    (hχ : ∀ g ∈ (curtisDatum m F 2).H, χ g = slChiEps m (algebraMap F k) ε g) {s : ℕ}
    (hpow : ∀ g ∈ (curtisDatum m F 2).H, χ g ^ 2 ^ s = χ g) (r : Fin f) :
    ε ⟨(r + s) % f, Nat.mod_lt _ r.pos⟩ = ε r := by
  refine rotate_eq_of_dvd_bDigit ε h0 (fun j => ?_) r
  let φ : F →+* k := algebraMap F k
  have hcard : Nat.card F = 2 ^ f := by rw [Nat.card_eq_fintype_card, hF]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf g = Nat.card F - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units]
  have hprim : IsPrimitiveRoot (φ (g : F)) (Nat.card F - 1) := by
    have h1 : IsPrimitiveRoot ((g : F)) (Nat.card F - 1) := by
      rw [← hord, ← orderOf_units]
      exact IsPrimitiveRoot.orderOf _
    exact h1.map_of_injective φ.injective
  let b := bDigit ε j.succ
  have hχdiag : χ (hdiag m F j g) = φ (g : F) ^ b := by
    rw [hχ (hdiag m F j g) (hdiag_mem_H m F j g), slChiEps_hdiag]
  have hpowdiag : (φ (g : F) ^ b) ^ 2 ^ s = φ (g : F) ^ b := by
    have h := hpow (hdiag m F j g) (hdiag_mem_H m F j g)
    rwa [hχdiag] at h
  have hφg : φ (g : F) ≠ 0 := by
    intro h
    exact g.ne_zero (φ.injective (h.trans (map_zero φ).symm))
  have hxne : φ (g : F) ^ b ≠ 0 := pow_ne_zero _ hφg
  have hx : (φ (g : F) ^ b) ^ (2 ^ s - 1) = 1 := by
    have h2 : (φ (g : F) ^ b) ^ (2 ^ s - 1) * (φ (g : F) ^ b) = φ (g : F) ^ b := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_two_pow (n := s))]
      exact hpowdiag
    refine mul_right_cancel₀ hxne ?_
    rw [one_mul]
    exact h2
  have hpowe : φ (g : F) ^ (b * (2 ^ s - 1)) = 1 := by
    rw [pow_mul]
    exact hx
  have hdvdN : Nat.card F - 1 ∣ b * (2 ^ s - 1) := hprim.dvd_of_pow_eq_one _ hpowe
  have hdvd' : 2 ^ f - 1 ∣ b * (2 ^ s - 1) := by
    rwa [hcard] at hdvdN
  simpa only [b] using hdvd'

omit [CharP k 2] in
theorem rotate_eq_of_chi_mem_range (hF : Fintype.card F = 2 ^ f)
    {E : Type} [Field E] [Fintype E] [Algebra E k] {s : ℕ} (hE : Fintype.card E = 2 ^ s)
    (ε : Fin f → Finset (Fin (m + 1))) (h0 : ∀ r, (0 : Fin (m + 1)) ∉ ε r)
    {χ : SpecialLinearGroup (Fin (m + 1)) F → k}
    (hχ : ∀ g ∈ (curtisDatum m F 2).H, χ g = slChiEps m (algebraMap F k) ε g)
    (hval : ∀ g ∈ (curtisDatum m F 2).H, ∃ c : E, χ g = algebraMap E k c) (r : Fin f) :
    ε ⟨(r + s) % f, Nat.mod_lt _ r.pos⟩ = ε r := by
  refine rotate_eq_of_chi_pow hF ε h0 hχ (fun g hg => ?_) r
  obtain ⟨c, hc⟩ := hval g hg
  rw [hc, ← map_pow]
  have h : c ^ Fintype.card E = c := FiniteField.pow_card c
  rw [hE] at h
  rw [h]

theorem rotate_eq_of_intertwine_stdAut (hF : Fintype.card F = 2 ^ f)
    (A : GL (Fin (m + 1)) F) (hA : IsUpperGL A) (τ : F ≃+* F) {a : ℕ}
    (hτ : ∀ x, τ x = x ^ 2 ^ a)
    {V : Type} [AddCommGroup V] [Module k V]
    {ρ : Representation k (SpecialLinearGroup (Fin (m + 1)) F) V} (hρ : IsSimpleRep ρ)
    {T : V ≃ₗ[k] V} (hT : ∀ g v, T (ρ g v) = ρ (borelStd (m + 1) F A τ 0 g) (T v))
    {y : V} {χ : SpecialLinearGroup (Fin (m + 1)) F → k} {J : Finset (Fin m)}
    (ht : IsCoverType (rankOne m F 2) ρ y χ J)
    (ε : Fin f → Finset (Fin (m + 1))) (h0 : ∀ r, (0 : Fin (m + 1)) ∉ ε r)
    (hχ : ∀ g ∈ (curtisDatum m F 2).H, χ g = slChiEps m (algebraMap F k) ε g) (r : Fin f) :
    ε ⟨(r + a) % f, Nat.mod_lt _ r.pos⟩ = ε r := by
  have htw := isCoverType_comp_borelStd (m := m) (F := F) A hA τ (ε := 0) (by norm_num) ht
  have hsymm : ∀ g v, T.symm
      ((ρ.comp (borelStd (m + 1) F A τ 0).toMonoidHom) g v) = ρ g (T.symm v) := by
    intro g v
    have h := congrArg T.symm (hT g (T.symm v))
    simpa [T.apply_symm_apply] using h.symm
  have htrans := IsCoverType.of_linearEquiv (e := T.symm) hsymm htw
  have htrans' : IsCoverType (rankOne m F 2) ρ (T.symm y)
      (χ ∘ CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut
        (Fin (m + 1)) F τ) J := by
    simpa [borelStdChar, borelStdSet] using htrans
  have hchi := (isCoverType_unique_sl (m := m) (F := F) (p := 2) hρ htrans' ht).1
  rw [Subgroup.comap_id] at hchi
  have hpow : ∀ g ∈ (curtisDatum m F 2).H, χ g ^ 2 ^ a = χ g := by
    intro g hg
    have hχg : χ g = slChiEps m (algebraMap F k) ε g := hχ g hg
    have hχaut : χ (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut
        (Fin (m + 1)) F τ g) =
        slChiEps m (algebraMap F k) ε
          (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut
            (Fin (m + 1)) F τ g) :=
      hχ _ (slFieldAut_mem_H (m := m) (F := F) τ hg)
    have hhelper := slChiEps_slFieldAut (m := m) (f := f) (φ := algebraMap F k) (ε := ε)
      (τ := τ) (e := a) hτ g
    have huniq : χ (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut
        (Fin (m + 1)) F τ g) = χ g := by
      have h := hchi g hg
      simpa [Function.comp] using h
    calc
      χ g ^ 2 ^ a = (slChiEps m (algebraMap F k) ε g) ^ 2 ^ a := by rw [hχg]
      _ = slChiEps m (algebraMap F k) ε
            (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut
              (Fin (m + 1)) F τ g) := hhelper.symm
      _ = χ (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut
            (Fin (m + 1)) F τ g) := hχaut.symm
      _ = χ g := huniq
  exact rotate_eq_of_chi_pow hF ε h0 hχ hpow r

end CFSG.LieType.SpecialLinear
