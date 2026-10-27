module

public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.Data.Nat.Choose.Dvd
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

section Ring

variable {A : Type*} [Ring A]

@[expose] def heisCofac (p : ℕ) (N : A) : A :=
  ∑ i ∈ Finset.range (p - 1), ((p.choose (i + 1) / p : ℕ) : A) * N ^ i

theorem heis_ring_binomial_identity {p : ℕ} (hp : p.Prime) (N : A) :
    (1 + N) ^ p = 1 + (p : A) * N * heisCofac p N + N ^ p := by
  have hp1 : 1 ≤ p := hp.one_lt.le
  have h := (Commute.one_right N).add_pow p
  rw [add_comm 1 N, h]
  simp only [one_pow, mul_one]
  rw [Finset.sum_range_succ, Nat.choose_self, Nat.cast_one, mul_one]
  have hsum : ∑ m ∈ Finset.range p, N ^ m * (p.choose m : A) =
      ∑ i ∈ Finset.range (p - 1), N ^ (i + 1) * (p.choose (i + 1) : A) + 1 := by
    obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    rw [hq, Finset.sum_range_succ']
    simp
  rw [hsum]
  have hterm : (p : A) * N * heisCofac p N =
      ∑ i ∈ Finset.range (p - 1), N ^ (i + 1) * (p.choose (i + 1) : A) := by
    unfold heisCofac
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i + 1 < p := by
      have := Finset.mem_range.1 hi
      omega
    have hdvd : p ∣ p.choose (i + 1) := Nat.Prime.dvd_choose_self hp (Nat.succ_ne_zero i) hi'
    have hc : p * (p.choose (i + 1) / p) = p.choose (i + 1) := Nat.mul_div_cancel' hdvd
    have hcen : Commute (((p.choose (i + 1) / p : ℕ)) : A) N := Nat.cast_commute _ _
    calc (p : A) * N * (((p.choose (i + 1) / p : ℕ) : A) * N ^ i)
        = (p : A) * (((p.choose (i + 1) / p : ℕ) : A) * (N * N ^ i)) := by
          rw [mul_assoc, ← mul_assoc N, ← hcen.eq, mul_assoc]
      _ = ((p * (p.choose (i + 1) / p) : ℕ) : A) * N ^ (i + 1) := by
          rw [← pow_succ', Nat.cast_mul, mul_assoc]
      _ = N ^ (i + 1) * (p.choose (i + 1) : A) := by
          rw [hc, (Nat.cast_commute _ _).eq]
  rw [hterm]
  abel

theorem heisCofac_eq {p : ℕ} (hp : p.Prime) (N : A) :
    ∃ w : A, Commute N w ∧ heisCofac p N = 1 + N * w := by
  have hp1 : 1 < p := hp.one_lt
  refine ⟨∑ i ∈ Finset.range (p - 2), ((p.choose (i + 2) / p : ℕ) : A) * N ^ i, ?_, ?_⟩
  · refine Commute.sum_right _ _ _ fun i _ => ?_
    exact ((Nat.cast_commute _ _).symm.mul_right ((Commute.refl N).pow_right i)).symm.symm
  · unfold heisCofac
    have : p - 1 = (p - 2) + 1 := by omega
    rw [this, Finset.sum_range_succ', Finset.mul_sum]
    have h0 : (p.choose 1 / p : ℕ) = 1 := by simp [Nat.choose_one_right, Nat.div_self hp.pos]
    simp only [pow_zero, mul_one, h0, Nat.cast_one]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have hcen : Commute (((p.choose (i + 2) / p : ℕ)) : A) N := Nat.cast_commute _ _
    rw [← mul_assoc, ← hcen.eq, mul_assoc, ← pow_succ']

end Ring

section Torsion

variable {S : Type*} [AddCommGroup S]

theorem heis_torsion_setup {p : ℕ} (hp : p.Prime)
    (hexp : ∃ n : ℕ, ∀ x : S, p ^ n • x = 0)
    (s : AddMonoid.End S) (hs : s ^ p = 1) :
    ∃ (N u : AddMonoid.End S), N = s - 1 ∧ Commute N u ∧ IsNilpotent N ∧ IsUnit u ∧
      (p : AddMonoid.End S) * N * u + N ^ p = 0 := by
  set N : AddMonoid.End S := s - 1 with hN
  have hbin : (1 + N) ^ p = 1 := by
    have : 1 + N = s := by rw [hN]; abel
    rw [this, hs]
  have hid : (p : AddMonoid.End S) * N * heisCofac p N + N ^ p = 0 := by
    have h := heis_ring_binomial_identity hp N
    rw [hbin] at h
    have h3 : 1 + ((p : AddMonoid.End S) * N * heisCofac p N + N ^ p) = 1 + 0 := by
      rw [add_zero, ← add_assoc]
      exact h.symm
    exact add_left_cancel h3
  obtain ⟨w, hw, hcf⟩ := heisCofac_eq hp N
  have hNu : Commute N (heisCofac p N) := by
    rw [hcf]
    exact (Commute.one_right N).add_right (Commute.refl N |>.mul_right hw)
  obtain ⟨n, hn⟩ := hexp
  have hnil : IsNilpotent N := by
    refine ⟨p * n, ?_⟩
    have h1 : N ^ p = (p : AddMonoid.End S) * (-(N * heisCofac p N)) := by
      have : N ^ p = -((p : AddMonoid.End S) * N * heisCofac p N) := by
        rw [eq_neg_iff_add_eq_zero, add_comm]; exact hid
      rw [this, mul_neg, mul_assoc]
    have h2 : ((p : AddMonoid.End S) ^ n) = 0 := by
      ext x
      rw [← Nat.cast_pow, AddMonoid.End.natCast_apply, hn x]
      rfl
    rw [pow_mul, h1, (Nat.cast_commute p (-(N * heisCofac p N))).mul_pow, h2, zero_mul]
  refine ⟨N, heisCofac p N, rfl, hNu, hnil, ?_, ?_⟩
  · rw [hcf]
    exact IsNilpotent.isUnit_one_add (hw.isNilpotent_mul_right hnil)
  · rw [mul_assoc]
    exact hid

theorem heis_nilpotent_pow_three_le {p : ℕ} (hp : p.Prime) [Finite S]
    (hrk : Nat.card {x : S // p • x = 0} ≤ p ^ 3)
    (N : AddMonoid.End S) (hnil : IsNilpotent N) :
    ∀ y : S, ∃ z : S, (N ^ 3) y = p • z := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  set P : AddMonoid.End S := (p : AddMonoid.End S) with hPdef
  have hP : ∀ x, P x = p • x := fun x => AddMonoid.End.natCast_apply p x
  let Pm : S →+ S := P
  have hPm : ∀ x, Pm x = p • x := hP
  set pS : AddSubgroup S := AddMonoidHom.range Pm with hpS
  have hmem : ∀ x : S, p • x ∈ pS := fun x => ⟨x, hP x⟩
  haveI : Module (ZMod p) (S ⧸ pS) := QuotientAddGroup.zmodModule hmem
  have hcard : Nat.card (S ⧸ pS) = Nat.card {x : S // p • x = 0} := by
    have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup pS
    have h2 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (AddMonoidHom.ker Pm)
    have h3 : Nat.card (S ⧸ AddMonoidHom.ker Pm) = Nat.card pS :=
      Nat.card_congr (QuotientAddGroup.quotientKerEquivRange Pm).toEquiv
    have h4 : Nat.card (AddMonoidHom.ker Pm) = Nat.card {x : S // p • x = 0} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun x => by
        rw [AddMonoidHom.mem_ker, hPm])
    have hpos : 0 < Nat.card pS := Nat.card_pos
    rw [h3, h4] at h2
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [← h1, h2, mul_comm]
  have hfin : Module.finrank (ZMod p) (S ⧸ pS) ≤ 3 := by
    haveI : Fintype (S ⧸ pS) := Fintype.ofFinite _
    have h := Module.card_eq_pow_finrank (K := ZMod p) (V := S ⧸ pS)
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hcard] at h
    have h' : p ^ Module.finrank (ZMod p) (S ⧸ pS) ≤ p ^ 3 := by
      rw [← h]; exact hrk
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h'
  have hmap : pS ≤ pS.comap (N : S →+ S) := by
    rintro _ ⟨y, rfl⟩
    refine ⟨N y, ?_⟩
    change P (N y) = N (P y)
    have : P * N = N * P := (Nat.cast_commute p N).eq
    exact congrArg (fun f : AddMonoid.End S => f y) this
  let N' : (S ⧸ pS) →+ (S ⧸ pS) := QuotientAddGroup.map pS pS (N : S →+ S) hmap
  let φ : Module.End (ZMod p) (S ⧸ pS) := AddMonoidHom.toZModLinearMap p N'
  have hφ : ∀ y : S, φ (QuotientAddGroup.mk y : S ⧸ pS) = (QuotientAddGroup.mk (N y) : S ⧸ pS) :=
    fun y => rfl
  have hφpow : ∀ (j : ℕ) (y : S), (φ ^ j) (QuotientAddGroup.mk y : S ⧸ pS) =
      (QuotientAddGroup.mk ((N ^ j) y) : S ⧸ pS) := by
    intro j
    induction j with
    | zero => intro y; simp
    | succ j ih =>
      intro y
      rw [pow_succ, Module.End.mul_apply, hφ, ih, pow_succ]
      rfl
  obtain ⟨k, hk⟩ := hnil
  have hφk : φ ^ k = 0 := by
    ext v
    induction v using QuotientAddGroup.induction_on with
    | H y => simp [hφpow, hk]
  haveI : Module.Finite (ZMod p) (S ⧸ pS) := Module.Finite.of_finite
  have hcp : φ.charpoly = Polynomial.X ^ Module.finrank (ZMod p) (S ⧸ pS) :=
    IsNilpotent.charpoly_eq_X_pow_finrank ⟨k, hφk⟩
  have hfr : φ ^ Module.finrank (ZMod p) (S ⧸ pS) = 0 := by
    have := LinearMap.aeval_self_charpoly φ
    rwa [hcp, map_pow, Polynomial.aeval_X] at this
  have hφ3 : φ ^ 3 = 0 := pow_eq_zero_of_le hfin hfr
  intro y
  have h1 : (QuotientAddGroup.mk ((N ^ 3) y) : S ⧸ pS) = 0 := by
    rw [← hφpow, hφ3]; rfl
  rw [QuotientAddGroup.eq_zero_iff] at h1
  obtain ⟨z, hz⟩ := h1
  exact ⟨z, by rw [← hz]; exact (hP z).symm⟩

theorem heis_end_mul_apply (f g : AddMonoid.End S) (x : S) : (f * g) x = f (g x) := rfl

theorem heis_fixes_torsion_of_pow_eq_one [Finite S] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hexp : ∃ n : ℕ, ∀ x : S, p ^ n • x = 0)
    (hrk : Nat.card {x : S // p • x = 0} ≤ p ^ 3)
    (hHP : ∀ x : S, p • x = 0 → ∃ y : S, p • y = x)
    (s : AddMonoid.End S) (hs : s ^ p = 1) (x : S) (hx : p • x = 0) : s x = x := by
  obtain ⟨N, u, hN, hNu, hnil, hu, hid⟩ := heis_torsion_setup hp hexp s hs
  have h3 := heis_nilpotent_pow_three_le hp hrk N hnil
  set P : AddMonoid.End S := (p : AddMonoid.End S) with hPdef
  have hP : ∀ y, P y = p • y := fun y => AddMonoid.End.natCast_apply p y
  have hPN : P * N = N * P := (Nat.cast_commute p N).eq
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have key : ∀ y : S, ∃ c' : S, (P * N) y = N ((P * N) c') := by
    intro y
    have hy : u (v y) = y := by
      have := congrArg (fun f : AddMonoid.End S => f y) hv
      simpa using this
    obtain ⟨z, hz⟩ := h3 (v y)
    have hPNy : (P * N) y = -((N ^ p) (v y)) := by
      have h1 : (P * N * u + N ^ p) (v y) = 0 := by rw [hid]; rfl
      have h2 : (P * N * u) (v y) = (P * N) y := by
        rw [heis_end_mul_apply, hy]
      have h4 : (P * N * u + N ^ p) (v y) = (P * N * u) (v y) + (N ^ p) (v y) := rfl
      rw [h4, h2] at h1
      exact eq_neg_of_add_eq_zero_left h1
    have hNP : Commute N P := (Nat.cast_commute p N).symm
    have hPcomm : ∀ (k : ℕ) (w : S), (N ^ k) (P w) = P ((N ^ k) w) := by
      intro k w
      have := (hNP.pow_left k).eq
      exact congrArg (fun f : AddMonoid.End S => f w) this
    have hNp : (N ^ p) (v y) = P (N (N ((N ^ (p - 5)) z))) := by
      have e1 : N ^ p = N ^ (p - 3) * N ^ 3 := by rw [← pow_add]; congr 1; omega
      have e2 : N ^ (p - 3) = N * N * N ^ (p - 5) := by
        rw [← pow_two, ← pow_add]; congr 1; omega
      have e3 : (N ^ (p - 3)) z = N (N ((N ^ (p - 5)) z)) := by rw [e2]; rfl
      rw [e1, heis_end_mul_apply, hz, ← hP, hPcomm, e3]
    have hNPc : ∀ w : S, N (P w) = P (N w) := fun w => by
      have := (Nat.cast_commute p N).eq
      exact (congrArg (fun f : AddMonoid.End S => f w) this).symm
    refine ⟨-((N ^ (p - 5)) z), ?_⟩
    rw [hPNy, hNp]
    change -(P (N (N ((N ^ (p - 5)) z)))) = N (P (N (-((N ^ (p - 5)) z))))
    rw [map_neg, map_neg, map_neg, hNPc]
  have iter : ∀ (k : ℕ) (y : S), ∃ c' : S, (P * N) y = (N ^ k) ((P * N) c') := by
    intro k
    induction k with
    | zero => intro y; exact ⟨y, rfl⟩
    | succ k ih =>
      intro y
      obtain ⟨c', hc'⟩ := ih y
      obtain ⟨c'', hc''⟩ := key c'
      refine ⟨c'', ?_⟩
      rw [hc', hc'', pow_succ]
      rfl
  obtain ⟨k, hk⟩ := hnil
  have hPN0 : ∀ y : S, (P * N) y = 0 := by
    intro y
    obtain ⟨c', hc'⟩ := iter k y
    rw [hc', hk]
    rfl
  obtain ⟨y, hy⟩ := hHP x hx
  have hNx : N x = 0 := by
    rw [← hy, ← hP]
    have : N (P y) = (P * N) y := by
      have := hPN
      exact (congrArg (fun f : AddMonoid.End S => f y) this).symm
    rw [this, hPN0]
  have : N x = s x - x := by rw [hN]; rfl
  rw [this] at hNx
  exact sub_eq_zero.1 hNx

end Torsion

section Mul

variable {G : Type*} [CommGroup G]

theorem heis_mul_fixes_torsion [Finite G] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hexp : ∃ n : ℕ, ∀ x : G, x ^ (p ^ n) = 1)
    (hrk : Nat.card {x : G // x ^ p = 1} ≤ p ^ 3)
    (hHP : ∀ x : G, x ^ p = 1 → ∃ y : G, y ^ p = x)
    (σ : G ≃* G) (hσ : σ ^ p = 1) (x : G) (hx : x ^ p = 1) : σ x = x := by
  let s : AddMonoid.End (Additive G) := (MulEquiv.toAdditive σ).toAddMonoidHom
  have hspow : ∀ (k : ℕ) (a : Additive G),
      (s ^ k) a = Additive.ofMul ((σ ^ k) (Additive.toMul a)) := by
    intro k
    induction k with
    | zero => intro a; rfl
    | succ k ih =>
      intro a
      rw [pow_succ, heis_end_mul_apply, ih]
      rfl
  have hs : s ^ p = 1 := by
    ext a
    rw [hspow, hσ]
    rfl
  have := heis_fixes_torsion_of_pow_eq_one (S := Additive G) hp hp5
    (by obtain ⟨n, hn⟩ := hexp; exact ⟨n, fun a => hn (Additive.toMul a)⟩)
    (by
      have : Nat.card {a : Additive G // p • a = 0} = Nat.card {x : G // x ^ p = 1} :=
        Nat.card_congr ⟨fun a => ⟨Additive.toMul a.1, a.2⟩, fun x => ⟨Additive.ofMul x.1, x.2⟩,
          fun _ => rfl, fun _ => rfl⟩
      rw [this]; exact hrk)
    (by
      intro a ha
      obtain ⟨y, hy⟩ := hHP (Additive.toMul a) ha
      exact ⟨Additive.ofMul y, hy⟩)
    s hs (Additive.ofMul x) hx
  exact this

end Mul

section Conj

variable {Q : Type*} [Group Q]

@[expose] def heisConjAut (S : Subgroup Q) (σ : Q) (hσ : ∀ s, s ∈ S ↔ σ * s * σ⁻¹ ∈ S) :
    S ≃* S where
  toFun s := ⟨σ * s * σ⁻¹, (hσ s).1 s.2⟩
  invFun s := ⟨σ⁻¹ * s * σ, by
    rw [hσ]
    simpa [mul_assoc] using s.2⟩
  left_inv s := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv s := by
    apply Subtype.ext
    simp [mul_assoc]
  map_mul' a b := by
    apply Subtype.ext
    simp [mul_assoc]

theorem heisConjAut_apply (S : Subgroup Q) (σ : Q) (hσ : ∀ s, s ∈ S ↔ σ * s * σ⁻¹ ∈ S) (s : S) :
    ((heisConjAut S σ hσ s : S) : Q) = σ * s * σ⁻¹ := rfl

end Conj

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
