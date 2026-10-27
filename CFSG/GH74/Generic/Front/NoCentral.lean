module

public import CFSG.GH74.Generic.Front.Defs
public import CFSG.GH74.L5U5.Models

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank CFSG.GH74.Filter.ClassicalOdd

namespace NoCentralAux

variable {F : Type*} [Field F]

theorem trace_eq_zero_of_anticomm {n : Type*} [Fintype n] [DecidableEq n] (h2 : (2 : F) ≠ 0)
    (X Y : Matrix n n F) (hY : Y * Y = -1) (hXY : X * Y = -(Y * X)) : Matrix.trace X = 0 := by
  have hYX : Y * X = -(X * Y) := by rw [hXY, neg_neg]
  have h1 : Matrix.trace (X * Y * Y) = Matrix.trace (Y * (X * Y)) := Matrix.trace_mul_comm _ _
  have h3 : Y * (X * Y) = -(X * Y * Y) := by
    calc Y * (X * Y) = (Y * X) * Y := (mul_assoc _ _ _).symm
      _ = -(X * Y) * Y := by rw [hYX]
      _ = -(X * Y * Y) := neg_mul _ _
  have h4 : X * Y * Y = -X := by
    rw [mul_assoc, hY]; simp
  rw [h3, Matrix.trace_neg] at h1
  have h5 : (2 : F) * Matrix.trace (X * Y * Y) = 0 := by linear_combination h1
  have h6 : Matrix.trace (X * Y * Y) = 0 := by
    rcases mul_eq_zero.1 h5 with h | h
    · exact absurd h h2
    · exact h
  rw [h4, Matrix.trace_neg] at h6
  simpa using h6

theorem cayley_hamilton_two (N : Matrix (Fin 2) (Fin 2) F) :
    N * N = Matrix.trace N • N - Matrix.det N • (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  rw [Matrix.det_fin_two, Matrix.trace_fin_two]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem det_eq_one_of_sq_neg_one {N : Matrix (Fin 2) (Fin 2) F} (h : N * N = -1)
    (ht : Matrix.trace N = 0) : Matrix.det N = 1 := by
  have := cayley_hamilton_two N
  rw [h, ht] at this
  have h00 := congrFun (congrFun this 0) 0
  simp at h00
  exact h00.symm

theorem mat2_impossible (h2 : (2 : F) ≠ 0) (A B C D : Matrix (Fin 2) (Fin 2) F)
    (hA : A * A = -1) (hB : B * B = -1) (hC : C * C = -1) (hD : D * D = -1)
    (hAB : A * B = -(B * A)) (hCD : C * D = -(D * C))
    (hAC : A * C = C * A) (hBC : B * C = C * B) :
    False := by
  have htA : Matrix.trace A = 0 := trace_eq_zero_of_anticomm h2 A B hB hAB
  have htC : Matrix.trace C = 0 := trace_eq_zero_of_anticomm h2 C D hD hCD
  have hdA : Matrix.det A = 1 := det_eq_one_of_sq_neg_one hA htA
  have hdC : Matrix.det C = 1 := det_eq_one_of_sq_neg_one hC htC
  have hAC' : (A * C) * B = -(B * (A * C)) := by
    calc (A * C) * B = A * (C * B) := by rw [mul_assoc]
      _ = A * (B * C) := by rw [hBC]
      _ = (A * B) * C := by rw [mul_assoc]
      _ = -(B * A) * C := by rw [hAB]
      _ = -(B * (A * C)) := by rw [neg_mul, mul_assoc]
  have htAC : Matrix.trace (A * C) = 0 := trace_eq_zero_of_anticomm h2 (A * C) B hB hAC'
  have hsq : (A * C) * (A * C) = -1 * -1 := by
    calc (A * C) * (A * C) = A * (C * A) * C := by simp only [mul_assoc]
      _ = A * (A * C) * C := by rw [hAC]
      _ = (A * A) * (C * C) := by simp only [mul_assoc]
      _ = -1 * -1 := by rw [hA, hC]
  have hsq' : (A * C) * (A * C) = 1 := by rw [hsq]; simp
  have hch := cayley_hamilton_two (A * C)
  rw [hsq', htAC, Matrix.det_mul, hdA, hdC] at hch
  have h00 := congrFun (congrFun hch 0) 0
  simp at h00
  apply h2
  linear_combination h00

theorem even_finrank_of_anticomm {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (h2 : (2 : F) ≠ 0) (a b : V →ₗ[F] V)
    (ha : ∀ x, a (a x) = -x) (hb : ∀ x, b (b x) = -x) (hab : ∀ x, a (b x) = -b (a x)) :
    Even (Module.finrank F V) := by
  set n := Module.finrank F V with hn
  have hneg : ∀ f : V →ₗ[F] V, LinearMap.det (-f) = (-1) ^ n * LinearMap.det f := by
    intro f
    have : -f = (-1 : F) • f := by simp
    rw [this, LinearMap.det_smul]
  have hA : a * a = -1 := LinearMap.ext fun x => by simp [ha]
  have hB : b * b = -1 := LinearMap.ext fun x => by simp [hb]
  have hAB : a * b = -(b * a) := LinearMap.ext fun x => by simp [hab]
  have h1 : (LinearMap.det a) * (LinearMap.det a) = (-1) ^ n := by
    have := congrArg LinearMap.det hA
    rw [map_mul, hneg, map_one, mul_one] at this
    exact this
  have h1' : (LinearMap.det b) * (LinearMap.det b) = (-1) ^ n := by
    have := congrArg LinearMap.det hB
    rw [map_mul, hneg, map_one, mul_one] at this
    exact this
  have hne : ((-1 : F)) ^ n ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
  have hda : LinearMap.det a ≠ 0 := by
    intro h; rw [h, zero_mul] at h1; exact hne h1.symm
  have hdb : LinearMap.det b ≠ 0 := by
    intro h; rw [h, zero_mul] at h1'; exact hne h1'.symm
  have h3 := congrArg LinearMap.det hAB
  rw [map_mul, hneg, map_mul] at h3
  have h4 : (-1 : F) ^ n = 1 := by
    have hab0 : LinearMap.det a * LinearMap.det b ≠ 0 := mul_ne_zero hda hdb
    have h5 : ((-1 : F) ^ n - 1) * (LinearMap.det a * LinearMap.det b) = 0 := by
      linear_combination (-1 : F) * h3
    rcases mul_eq_zero.1 h5 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hab0
  have hneq : (-1 : F) ≠ 1 := by
    intro h
    apply h2
    linear_combination (-1 : F) * h
  exact (neg_one_pow_eq_one_iff_even hneq).1 h4

theorem isCompl_ker_involution {V : Type*} [AddCommGroup V] [Module F V] (h2 : (2 : F) ≠ 0)
    (z : V →ₗ[F] V) (hz : ∀ x, z (z x) = x) :
    IsCompl (LinearMap.ker (z + 1)) (LinearMap.ker (z - 1)) := by
  have hp : ∀ x, (z + 1) x = z x + x := fun x => by simp
  have hm : ∀ x, (z - 1) x = z x - x := fun x => by simp
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx1 hx2
    rw [LinearMap.mem_ker, hp] at hx1
    rw [LinearMap.mem_ker, hm] at hx2
    have : (2 : F) • x = 0 := by
      rw [two_smul]
      calc x + x = (z x + x) - (z x - x) := by abel
        _ = 0 := by rw [hx1, hx2]; simp
    rcases smul_eq_zero.1 this with h | h
    · exact absurd h h2
    · exact h
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hx1 : (2 : F)⁻¹ • (x - z x) ∈ LinearMap.ker (z + 1) := by
      rw [LinearMap.mem_ker, hp, map_smul, map_sub, hz, ← smul_add]
      have : z x - x + (x - z x) = 0 := by abel
      rw [this, smul_zero]
    have hx2 : (2 : F)⁻¹ • (x + z x) ∈ LinearMap.ker (z - 1) := by
      rw [LinearMap.mem_ker, hm, map_smul, map_add, hz, ← smul_sub]
      have : z x + x - (x + z x) = 0 := by abel
      rw [this, smul_zero]
    have hsum : (2 : F)⁻¹ • (x - z x) + (2 : F)⁻¹ • (x + z x) = x := by
      rw [← smul_add]
      have : x - z x + (x + z x) = (2 : F) • x := by rw [two_smul]; abel
      rw [this, smul_smul, inv_mul_cancel₀ h2, one_smul]
    rw [← hsum]
    exact Submodule.add_mem_sup hx1 hx2

theorem exists_restrict {V : Type*} [AddCommGroup V] [Module F V] (S : Submodule F V)
    (f : V →ₗ[F] V) (hf : ∀ x ∈ S, f x ∈ S) : ∃ f' : S →ₗ[F] S, ∀ x : S, (f' x : V) = f x :=
  ⟨f.restrict hf, fun _ => rfl⟩

theorem even_finrank_of_stable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (h2 : (2 : F) ≠ 0) (a b : V →ₗ[F] V) (S : Submodule F V)
    (hSa : ∀ x ∈ S, a x ∈ S) (hSb : ∀ x ∈ S, b x ∈ S)
    (ha : ∀ x, a (a x) = -x) (hb : ∀ x, b (b x) = -x) (hab : ∀ x, a (b x) = -b (a x)) :
    Even (Module.finrank F S) := by
  obtain ⟨a', ha'⟩ := exists_restrict S a hSa
  obtain ⟨b', hb'⟩ := exists_restrict S b hSb
  refine even_finrank_of_anticomm h2 a' b' (fun x => ?_) (fun x => ?_) (fun x => ?_)
  · apply Subtype.ext
    rw [ha', ha', ha]
    rfl
  · apply Subtype.ext
    rw [hb', hb', hb]
    rfl
  · apply Subtype.ext
    rw [ha', hb', Submodule.coe_neg, hb', ha', hab]

theorem no_two_dim {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (hV : Module.finrank F V = 2) (h2 : (2 : F) ≠ 0) (a b c d : V →ₗ[F] V)
    (ha : ∀ x, a (a x) = -x) (hb : ∀ x, b (b x) = -x) (hc : ∀ x, c (c x) = -x)
    (hd : ∀ x, d (d x) = -x)
    (hab : ∀ x, a (b x) = -b (a x)) (hcd : ∀ x, c (d x) = -d (c x))
    (hac : ∀ x, a (c x) = c (a x)) (hbc : ∀ x, b (c x) = c (b x)) : False := by
  let bV : Module.Basis (Fin 2) F V := Module.finBasisOfFinrankEq F V hV
  let e := LinearMap.toMatrixAlgEquiv bV
  have hA : a * a = -1 := LinearMap.ext fun x => by simp [ha]
  have hB : b * b = -1 := LinearMap.ext fun x => by simp [hb]
  have hC : c * c = -1 := LinearMap.ext fun x => by simp [hc]
  have hD : d * d = -1 := LinearMap.ext fun x => by simp [hd]
  have hAB : a * b = -(b * a) := LinearMap.ext fun x => by simp [hab]
  have hCD : c * d = -(d * c) := LinearMap.ext fun x => by simp [hcd]
  have hAC : a * c = c * a := LinearMap.ext fun x => by simp [hac]
  have hBC : b * c = c * b := LinearMap.ext fun x => by simp [hbc]
  refine mat2_impossible h2 (e a) (e b) (e c) (e d) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← map_mul, hA, map_neg, map_one]
  · rw [← map_mul, hB, map_neg, map_one]
  · rw [← map_mul, hC, map_neg, map_one]
  · rw [← map_mul, hD, map_neg, map_one]
  · rw [← map_mul, hAB, map_neg, map_mul]
  · rw [← map_mul, hCD, map_neg, map_mul]
  · rw [← map_mul, hAC, map_mul]
  · rw [← map_mul, hBC, map_mul]

theorem involution_eq_one_or_neg_one {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (hV : Module.finrank F V = 4) (h2 : (2 : F) ≠ 0)
    (a b c d z : V →ₗ[F] V)
    (ha : ∀ x, a (a x) = -x) (hb : ∀ x, b (b x) = -x) (hab : ∀ x, a (b x) = -b (a x))
    (hc : ∀ x, c (c x) = z x) (hd : ∀ x, d (d x) = z x) (hdc : ∀ x, d (c x) = z (c (d x)))
    (hz : ∀ x, z (z x) = x)
    (hac : ∀ x, a (c x) = c (a x)) (hbc : ∀ x, b (c x) = c (b x))
    (hza : ∀ x, z (a x) = a (z x)) (hzb : ∀ x, z (b x) = b (z x))
    (hzc : ∀ x, z (c x) = c (z x)) (hzd : ∀ x, z (d x) = d (z x)) :
    z = 1 ∨ z = -1 := by
  have hcompl := isCompl_ker_involution h2 z hz
  have hmemW : ∀ x, x ∈ LinearMap.ker (z + 1) ↔ z x = -x := by
    intro x
    rw [LinearMap.mem_ker]
    simp only [LinearMap.add_apply, Module.End.one_apply]
    exact add_eq_zero_iff_eq_neg
  have hmemU : ∀ x, x ∈ LinearMap.ker (z - 1) ↔ z x = x := by
    intro x
    rw [LinearMap.mem_ker]
    simp only [LinearMap.sub_apply, Module.End.one_apply]
    exact sub_eq_zero
  have stabW : ∀ f : V →ₗ[F] V, (∀ x, z (f x) = f (z x)) →
      ∀ x ∈ LinearMap.ker (z + 1), f x ∈ LinearMap.ker (z + 1) := by
    intro f hf x hx
    rw [hmemW] at hx ⊢
    rw [hf, hx, map_neg]
  have stabU : ∀ f : V →ₗ[F] V, (∀ x, z (f x) = f (z x)) →
      ∀ x ∈ LinearMap.ker (z - 1), f x ∈ LinearMap.ker (z - 1) := by
    intro f hf x hx
    rw [hmemU] at hx ⊢
    rw [hf, hx]
  have hsum : Module.finrank F (LinearMap.ker (z + 1)) + Module.finrank F (LinearMap.ker (z - 1))
      = 4 := by
    rw [Submodule.finrank_add_eq_of_isCompl hcompl, hV]
  have hevW := even_finrank_of_stable h2 a b (LinearMap.ker (z + 1)) (stabW a hza) (stabW b hzb)
    ha hb hab
  have hevU := even_finrank_of_stable h2 a b (LinearMap.ker (z - 1)) (stabU a hza) (stabU b hzb)
    ha hb hab
  obtain ⟨k, hk⟩ := hevW
  obtain ⟨l, hl⟩ := hevU
  have hcases : Module.finrank F (LinearMap.ker (z + 1)) = 0 ∨
      Module.finrank F (LinearMap.ker (z + 1)) = 2 ∨
      Module.finrank F (LinearMap.ker (z + 1)) = 4 := by omega
  rcases hcases with h0 | h2' | h4
  · left
    have hWbot : LinearMap.ker (z + 1) = ⊥ := Submodule.finrank_eq_zero.1 h0
    have hUtop : LinearMap.ker (z - 1) = ⊤ := by
      have := hcompl.sup_eq_top
      rwa [hWbot, bot_sup_eq] at this
    ext x
    have hx : x ∈ LinearMap.ker (z - 1) := by rw [hUtop]; trivial
    rw [hmemU] at hx
    simpa using hx
  · exfalso
    obtain ⟨a', ha'⟩ := exists_restrict _ a (stabW a hza)
    obtain ⟨b', hb'⟩ := exists_restrict _ b (stabW b hzb)
    obtain ⟨c', hc'⟩ := exists_restrict _ c (stabW c hzc)
    obtain ⟨d', hd'⟩ := exists_restrict _ d (stabW d hzd)
    refine no_two_dim h2' h2 a' b' c' d' (fun x => ?_) (fun x => ?_) (fun x => ?_) (fun x => ?_)
      (fun x => ?_) (fun x => ?_) (fun x => ?_) (fun x => ?_)
    · apply Subtype.ext
      rw [ha', ha', ha]
      rfl
    · apply Subtype.ext
      rw [hb', hb', hb]
      rfl
    · apply Subtype.ext
      rw [hc', hc', hc]
      exact (hmemW _).1 x.2
    · apply Subtype.ext
      rw [hd', hd', hd]
      exact (hmemW _).1 x.2
    · apply Subtype.ext
      rw [ha', hb', Submodule.coe_neg, hb', ha', hab]
    · apply Subtype.ext
      rw [hc', hd', Submodule.coe_neg, hd', hc']
      have h1 := hdc x
      have hmem : c (d x) ∈ LinearMap.ker (z + 1) :=
        stabW c hzc _ (stabW d hzd _ x.2)
      rw [(hmemW _).1 hmem] at h1
      rw [h1, neg_neg]
    · apply Subtype.ext
      rw [ha', hc', hc', ha']
      exact hac _
    · apply Subtype.ext
      rw [hb', hc', hc', hb']
      exact hbc _
  · right
    have hUz : Module.finrank F (LinearMap.ker (z - 1)) = 0 := by omega
    have hUbot : LinearMap.ker (z - 1) = ⊥ := Submodule.finrank_eq_zero.1 hUz
    have hWtop : LinearMap.ker (z + 1) = ⊤ := by
      have := hcompl.sup_eq_top
      rwa [hUbot, sup_bot_eq] at this
    ext x
    have hx : x ∈ LinearMap.ker (z + 1) := by rw [hWtop]; trivial
    rw [hmemW] at hx
    simpa using hx

theorem scalar_sq_eq_one {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] (c : Fˣ)
    (h : Matrix.GeneralLinearGroup.scalar ι c * Matrix.GeneralLinearGroup.scalar ι c = 1) :
    c = 1 ∨ c = -1 := by
  have h1 := congrArg (fun u : GL ι F => (u : Matrix ι ι F)) h
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Units.val_one] at h1
  obtain ⟨i⟩ := ‹Nonempty ι›
  have h2 := congrFun (congrFun h1 i) i
  rw [← map_mul, Matrix.scalar_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h2
  rcases mul_self_eq_one_iff.1 h2 with h3 | h3
  · exact Or.inl (Units.ext h3)
  · exact Or.inr (Units.ext (by simpa using h3))

theorem scalar_neg_one {ι : Type} [Fintype ι] [DecidableEq ι] :
    (Matrix.GeneralLinearGroup.scalar ι (-1 : Fˣ) : GL ι F) = -1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_neg, Units.val_one, Units.val_neg,
    Units.val_one, map_neg, map_one]

end NoCentralAux

theorem q8q8_neg_one_of_neg_one {ι : Type} [Fintype ι] [DecidableEq ι] (hι : Fintype.card ι = 4)
    {F : Type} [Field F] (h2 : (2 : F) ≠ 0) (ψ : Q8 × Q8 →* GL ι F)
    (h : ψ (QuaternionGroup.a 2, 1) = -1) :
    ψ (1, QuaternionGroup.a 2) = -1 ∨ ψ (1, QuaternionGroup.a 2) = 1 := by
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : GL ι F →* Module.End F (ι → F),
      ∀ g : GL ι F, Φ g = Matrix.toLin' (g : Matrix ι ι F) :=
    ⟨{ toFun := fun g => Matrix.toLin' (g : Matrix ι ι F)
       map_one' := by simp; rfl
       map_mul' := fun g h => by simp [Matrix.toLin'_mul]; rfl }, fun _ => rfl⟩
  have hΦinj : Function.Injective Φ := by
    intro g h hgh
    rw [hΦ, hΦ] at hgh
    exact Units.ext (Matrix.toLin'.injective hgh)
  have hΦneg : ∀ g : GL ι F, Φ (-g) = -Φ g := by
    intro g
    rw [hΦ, hΦ]
    simp
  have hΦneg1 : Φ (-1) = -1 := by rw [hΦneg, map_one]
  have hmulx : ∀ (g h : GL ι F) (x : ι → F), Φ (g * h) x = Φ g (Φ h x) := by
    intro g h x
    rw [map_mul]
    rfl
  have hnegx : ∀ (g : GL ι F) (x : ι → F), Φ (-g) x = -Φ g x := by
    intro g x
    rw [hΦneg]
    rfl
  have hnegonex : ∀ x : ι → F, Φ (-1) x = -x := by
    intro x
    rw [hnegx, map_one]
    rfl
  have honex : ∀ x : ι → F, Φ 1 x = x := by
    intro x
    rw [map_one]
    rfl
  have p1 : ((QuaternionGroup.a 1, 1) : Q8 × Q8) * (QuaternionGroup.a 1, 1) =
      (QuaternionGroup.a 2, 1) := by decide
  have p2 : ((QuaternionGroup.xa 0, 1) : Q8 × Q8) * (QuaternionGroup.xa 0, 1) =
      (QuaternionGroup.a 2, 1) := by decide
  have p3 : ((QuaternionGroup.a 1, 1) : Q8 × Q8) * (QuaternionGroup.xa 0, 1) =
      (QuaternionGroup.a 2, 1) * ((QuaternionGroup.xa 0, 1) * (QuaternionGroup.a 1, 1)) := by
    decide
  have p4 : ((1, QuaternionGroup.a 1) : Q8 × Q8) * (1, QuaternionGroup.a 1) =
      (1, QuaternionGroup.a 2) := by decide
  have p5 : ((1, QuaternionGroup.xa 0) : Q8 × Q8) * (1, QuaternionGroup.xa 0) =
      (1, QuaternionGroup.a 2) := by decide
  have p6 : ((1, QuaternionGroup.xa 0) : Q8 × Q8) * (1, QuaternionGroup.a 1) =
      (1, QuaternionGroup.a 2) * ((1, QuaternionGroup.a 1) * (1, QuaternionGroup.xa 0)) := by
    decide
  have p7 : ((1, QuaternionGroup.a 2) : Q8 × Q8) * (1, QuaternionGroup.a 2) = 1 := by decide
  have p8 : ((QuaternionGroup.a 1, 1) : Q8 × Q8) * (1, QuaternionGroup.a 1) =
      (1, QuaternionGroup.a 1) * (QuaternionGroup.a 1, 1) := by decide
  have p9 : ((QuaternionGroup.xa 0, 1) : Q8 × Q8) * (1, QuaternionGroup.a 1) =
      (1, QuaternionGroup.a 1) * (QuaternionGroup.xa 0, 1) := by decide
  have p10 : ∀ g : Q8, ((1, QuaternionGroup.a 2) : Q8 × Q8) * (g, 1) =
      (g, 1) * (1, QuaternionGroup.a 2) := by decide
  have p11 : ∀ g : Q8, ((1, QuaternionGroup.a 2) : Q8 × Q8) * (1, g) =
      (1, g) * (1, QuaternionGroup.a 2) := by decide
  have r1 : ψ (QuaternionGroup.a 1, 1) * ψ (QuaternionGroup.a 1, 1) = -1 := by
    rw [← map_mul, p1]; exact h
  have r2 : ψ (QuaternionGroup.xa 0, 1) * ψ (QuaternionGroup.xa 0, 1) = -1 := by
    rw [← map_mul, p2]; exact h
  have r3 : ψ (QuaternionGroup.a 1, 1) * ψ (QuaternionGroup.xa 0, 1) =
      -(ψ (QuaternionGroup.xa 0, 1) * ψ (QuaternionGroup.a 1, 1)) := by
    rw [← map_mul, p3, map_mul, map_mul, h, neg_one_mul]
  have r4 : ψ (1, QuaternionGroup.a 1) * ψ (1, QuaternionGroup.a 1) =
      ψ (1, QuaternionGroup.a 2) := by rw [← map_mul, p4]
  have r5 : ψ (1, QuaternionGroup.xa 0) * ψ (1, QuaternionGroup.xa 0) =
      ψ (1, QuaternionGroup.a 2) := by rw [← map_mul, p5]
  have r6 : ψ (1, QuaternionGroup.xa 0) * ψ (1, QuaternionGroup.a 1) =
      ψ (1, QuaternionGroup.a 2) * (ψ (1, QuaternionGroup.a 1) * ψ (1, QuaternionGroup.xa 0)) := by
    rw [← map_mul, p6, map_mul, map_mul]
  have r7 : ψ (1, QuaternionGroup.a 2) * ψ (1, QuaternionGroup.a 2) = 1 := by
    rw [← map_mul, p7, map_one]
  have r8 : ψ (QuaternionGroup.a 1, 1) * ψ (1, QuaternionGroup.a 1) =
      ψ (1, QuaternionGroup.a 1) * ψ (QuaternionGroup.a 1, 1) := by
    rw [← map_mul, p8, map_mul]
  have r9 : ψ (QuaternionGroup.xa 0, 1) * ψ (1, QuaternionGroup.a 1) =
      ψ (1, QuaternionGroup.a 1) * ψ (QuaternionGroup.xa 0, 1) := by
    rw [← map_mul, p9, map_mul]
  have r10 : ∀ g : Q8, ψ (1, QuaternionGroup.a 2) * ψ (g, 1) =
      ψ (g, 1) * ψ (1, QuaternionGroup.a 2) := by
    intro g
    rw [← map_mul, p10, map_mul]
  have r11 : ∀ g : Q8, ψ (1, QuaternionGroup.a 2) * ψ (1, g) =
      ψ (1, g) * ψ (1, QuaternionGroup.a 2) := by
    intro g
    rw [← map_mul, p11, map_mul]
  have hV : Module.finrank F (ι → F) = 4 := by
    rw [Module.finrank_fintype_fun_eq_card, hι]
  have key := NoCentralAux.involution_eq_one_or_neg_one hV h2 (Φ (ψ (QuaternionGroup.a 1, 1)))
    (Φ (ψ (QuaternionGroup.xa 0, 1))) (Φ (ψ (1, QuaternionGroup.a 1)))
    (Φ (ψ (1, QuaternionGroup.xa 0))) (Φ (ψ (1, QuaternionGroup.a 2)))
    (fun x => by rw [← hmulx, r1, hnegonex])
    (fun x => by rw [← hmulx, r2, hnegonex])
    (fun x => by rw [← hmulx, r3, hnegx, hmulx])
    (fun x => by rw [← hmulx, r4])
    (fun x => by rw [← hmulx, r5])
    (fun x => by rw [← hmulx, r6, hmulx, hmulx])
    (fun x => by rw [← hmulx, r7, honex])
    (fun x => by rw [← hmulx, r8, hmulx])
    (fun x => by rw [← hmulx, r9, hmulx])
    (fun x => by rw [← hmulx, r10, hmulx])
    (fun x => by rw [← hmulx, r10, hmulx])
    (fun x => by rw [← hmulx, r11, hmulx])
    (fun x => by rw [← hmulx, r11, hmulx])
  rcases key with hk | hk
  · right
    exact hΦinj (by rw [hk, map_one])
  · left
    exact hΦinj (by rw [hk, hΦneg1])

theorem NoCentral.of_mulEquiv {K K' : Type} [Group K] [Group K'] (e : K ≃* K')
    (h : NoCentral K') : NoCentral K := by
  intro ψ hψ hcent
  exact h (e.toMonoidHom.comp ψ) (e.injective.comp hψ) ((mem_center_iff_of_mulEquiv e _).2 hcent)

theorem noCentral_of_center {ι : Type} [Fintype ι] [DecidableEq ι] (hι : Fintype.card ι = 4)
    {F : Type} [Field F] (h2 : (2 : F) ≠ 0) (K : Subgroup (GL ι F))
    (hc : ∀ g : ↥K, g ∈ Subgroup.center ↥K → g * g = 1 →
      (g : GL ι F) = 1 ∨ (g : GL ι F) = -1) :
    NoCentral ↥K := by
  intro ψ hψ hcent
  have hne1 : ((QuaternionGroup.a 2, 1) : Q8 × Q8) ≠ 1 := by decide
  have hne2 : ((1, QuaternionGroup.a 2) : Q8 × Q8) ≠ (QuaternionGroup.a 2, 1) := by decide
  have hne3 : ((1, QuaternionGroup.a 2) : Q8 × Q8) ≠ 1 := by decide
  have hsq : ψ (QuaternionGroup.a 2, 1) * ψ (QuaternionGroup.a 2, 1) = 1 := by
    have : ((QuaternionGroup.a 2, 1) : Q8 × Q8) * (QuaternionGroup.a 2, 1) = 1 := by decide
    rw [← map_mul, this, map_one]
  rcases hc _ hcent hsq with h1 | h1
  · exact hne1 (hψ (by rw [map_one]; exact Subtype.ext h1))
  · have h' : (K.subtype.comp ψ) (QuaternionGroup.a 2, 1) = -1 := h1
    rcases q8q8_neg_one_of_neg_one hι h2 (K.subtype.comp ψ) h' with h3 | h3
    · exact hne2 (hψ (Subtype.ext (h3.trans h1.symm)))
    · exact hne3 (hψ (by rw [map_one]; exact Subtype.ext h3))

theorem noCentral_statedSL4 {F : Type} [Field F] [Finite F] (hF : Nat.card F % 4 = 3) :
    NoCentral ↥(StatedSL 4 F) := by
  have hodd : Odd (Nat.card F) := Nat.odd_iff.2 (by omega)
  refine noCentral_of_center (ι := Fin 4) (Fintype.card_fin 4)
    (CFSG.GH74.L5U5.two_ne_zero_of_odd_card hodd) (StatedSL 4 F) ?_
  intro g hg _
  rcases (mem_center_statedSL_four_iff hF g).1 hg with h | h
  · exact Or.inl h
  · exact Or.inr (by rw [h, xGL_eq_neg_one])

theorem noCentral_statedSU4 {F : Type} [Field F] [Finite F] {q : ℕ} (hF : Nat.card F = q ^ 2)
    (hq : q % 4 = 1) : NoCentral ↥(StatedSU 4 q F) := by
  obtain ⟨p, f, hp, hchar, rfl⟩ := exists_prime_pow_of_card_eq_sq hF
  have hodd : Odd (Nat.card F) := by
    rw [hF]
    exact (Nat.odd_iff.2 (by omega : p ^ f % 2 = 1)).pow
  refine noCentral_of_center (ι := Fin 4) (Fintype.card_fin 4)
    (CFSG.GH74.L5U5.two_ne_zero_of_odd_card hodd) (StatedSU 4 (p ^ f) F) ?_
  intro g hg _
  rcases (mem_center_statedSU_four_iff hF hq g).1 hg with h | h
  · exact Or.inl h
  · exact Or.inr (by rw [h, xGL_eq_neg_one])

theorem noCentral_statedSp2 {F : Type} [Field F] [Finite F] (hF : Odd (Nat.card F)) :
    NoCentral ↥(StatedSp 2 F) := by
  refine noCentral_of_center (ι := Fin 2 ⊕ Fin 2) (by simp)
    (CFSG.GH74.L5U5.two_ne_zero_of_odd_card hF) (StatedSp 2 F) ?_
  intro g hg hgg
  rw [CFSG.LieType.Universal.Symplectic.center_eq, Subgroup.mem_subgroupOf, StatedScalars,
    MonoidHom.mem_range] at hg
  obtain ⟨c, hc⟩ := hg
  have hsq : Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c *
      Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c = 1 := by
    rw [hc]
    exact congrArg Subtype.val hgg
  rcases NoCentralAux.scalar_sq_eq_one c hsq with rfl | rfl
  · exact Or.inl (by rw [← hc, map_one])
  · exact Or.inr (by rw [← hc, NoCentralAux.scalar_neg_one])

end CFSG.GH74.Generic
