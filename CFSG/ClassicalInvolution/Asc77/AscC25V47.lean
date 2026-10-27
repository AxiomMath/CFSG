module

public import CFSG.ClassicalInvolution.Asc77.AscC25V41
public import CFSG.ClassicalInvolution.Asc77.AscC25V45
public import CFSG.ClassicalInvolution.Asc77.AscC25V46
import CFSG.ClassicalInvolution.Asc77.AscC25V39

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.GorensteinWalter
open scoped MatrixGroups commutatorElement

section Abstract

variable {G : Type} [Group G]

theorem exists_pow_conj_of_inverted {a z u : G} (hz2 : z * z = 1) (hza : z * a = a * z)
    (hzu : z * u = u * z) (hau : a * u * a⁻¹ = u⁻¹) {o : ℕ} (ho : Odd o)
    (hu : u ^ o = 1 ∨ u ^ o = z) :
    ∃ (w y : G) (j : ℕ), j ≤ 1 ∧ w = u * z ^ j ∧ (∃ k : ℕ, y = w ^ k) ∧ y * a * y⁻¹ = w * a := by
  obtain ⟨j, hj1, hw⟩ : ∃ j : ℕ, j ≤ 1 ∧ (u * z ^ j) ^ o = 1 := by
    rcases hu with h | h
    · exact ⟨0, by omega, by simpa using h⟩
    · refine ⟨1, le_rfl, ?_⟩
      have hcomm : Commute u (z ^ 1) := by
        rw [pow_one]
        exact hzu.symm
      rw [hcomm.mul_pow, h, pow_one, pow_eq_self_of_odd_of_mul_self_eq_one hz2 ho, hz2]
  set w : G := u * z ^ j with hwdef
  have hzj : z ^ j * a = a * z ^ j := by
    interval_cases j
    · simp
    · simpa using hza
  have hzji : (z ^ j)⁻¹ = z ^ j := by
    interval_cases j
    · simp
    · simpa using inv_eq_of_mul_eq_one_right hz2
  have haw : a * w * a⁻¹ = w⁻¹ := by
    have h1 : a * z ^ j * a⁻¹ = z ^ j := by
      calc a * z ^ j * a⁻¹ = (z ^ j * a) * a⁻¹ := by rw [hzj]
        _ = z ^ j := by group
    have hcz : z ^ j * u⁻¹ = u⁻¹ * z ^ j := by
      have h1 : Commute u z := hzu.symm
      have h2 : Commute u (z ^ j) := h1.pow_right j
      exact h2.inv_left.symm.eq
    calc a * w * a⁻¹ = (a * u * a⁻¹) * (a * z ^ j * a⁻¹) := by rw [hwdef]; group
      _ = u⁻¹ * z ^ j := by rw [hau, h1]
      _ = w⁻¹ := by rw [hwdef, mul_inv_rev, hzji, hcz]
  obtain ⟨k, hk⟩ := ho
  set y : G := w ^ (k + 1) with hydef
  have hy2 : y * y = w := by
    rw [hydef, ← pow_add]
    have h2 : w ^ (k + 1 + (k + 1)) = w ^ (2 * k + 1) * w := by
      rw [← pow_succ]
      congr 1
      ring
    rw [h2, ← hk, hw, one_mul]
  have hay : a * y * a⁻¹ = y⁻¹ := by
    calc a * y * a⁻¹ = (MulAut.conj a) y := by simp [MulAut.conj_apply]
      _ = ((MulAut.conj a) w) ^ (k + 1) := by rw [hydef, map_pow]
      _ = (w⁻¹) ^ (k + 1) := by simp [MulAut.conj_apply, haw]
      _ = y⁻¹ := by rw [hydef, inv_pow]
  refine ⟨w, y, j, hj1, hwdef, ⟨k + 1, hydef⟩, ?_⟩
  calc y * a * y⁻¹ = y * (a * y⁻¹ * a⁻¹) * a := by group
    _ = y * (a * y * a⁻¹)⁻¹ * a := by
        rw [show a * y⁻¹ * a⁻¹ = (a * y * a⁻¹)⁻¹ by group]
    _ = y * y * a := by rw [hay, inv_inv]
    _ = w * a := by rw [hy2]

theorem comm_or_comm_z_of_conj {a z g u w y : G} (hz2 : z * z = 1) (hza : z * a = a * z)
    (hzg : z * g = g * z) (hzy : z * y = y * z) (hu : u = g * a * g⁻¹ * a⁻¹) {j : ℕ}
    (hj : j ≤ 1) (hw : w = u * z ^ j) (hya : y * a * y⁻¹ = w * a) :
    (y⁻¹ * g) * a = a * (y⁻¹ * g) ∨ (y⁻¹ * g) * a = a * (y⁻¹ * g) * z := by
  have hua : u * a = g * a * g⁻¹ := by rw [hu]; group
  have hzyi : z * y⁻¹ = y⁻¹ * z := (Commute.inv_right (show Commute z y from hzy)).eq
  interval_cases j
  · left
    have hw' : w = u := by rw [hw]; simp
    have hmain : g * a * g⁻¹ = y * a * y⁻¹ := by rw [hya, hw', hua]
    calc y⁻¹ * g * a = y⁻¹ * (g * a * g⁻¹) * g := by group
      _ = y⁻¹ * (y * a * y⁻¹) * g := by rw [hmain]
      _ = a * (y⁻¹ * g) := by group
  · right
    have hw' : w = u * z := by rw [hw]; simp
    have hmain : y * a * y⁻¹ = g * a * g⁻¹ * z := by
      calc y * a * y⁻¹ = w * a := hya
        _ = u * (z * a) := by rw [hw', mul_assoc]
        _ = u * (a * z) := by rw [hza]
        _ = (u * a) * z := by rw [mul_assoc]
        _ = g * a * g⁻¹ * z := by rw [hua]
    have hmain' : g * a * g⁻¹ = y * a * y⁻¹ * z := by
      rw [hmain, mul_assoc (g * a * g⁻¹) z z, hz2, mul_one]
    have hzd : z * (y⁻¹ * g) = (y⁻¹ * g) * z := by
      calc z * (y⁻¹ * g) = (z * y⁻¹) * g := by group
        _ = (y⁻¹ * z) * g := by rw [hzyi]
        _ = y⁻¹ * (z * g) := by group
        _ = y⁻¹ * (g * z) := by rw [hzg]
        _ = (y⁻¹ * g) * z := by group
    calc y⁻¹ * g * a = y⁻¹ * (g * a * g⁻¹) * g := by group
      _ = y⁻¹ * (y * a * y⁻¹ * z) * g := by rw [hmain']
      _ = a * (y⁻¹ * z * g) := by group
      _ = a * (z * (y⁻¹ * g)) := by rw [← hzyi]; group
      _ = a * ((y⁻¹ * g) * z) := by rw [hzd]
      _ = a * (y⁻¹ * g) * z := by group

end Abstract

section Aux

theorem conj_comm_eq_one {H : Type*} [Group H] (C X Y : H) (hXY : X * Y = Y * X) :
    (C * X * C⁻¹) * (C * Y * C⁻¹) * (C * X * C⁻¹)⁻¹ * (C * Y * C⁻¹)⁻¹ = 1 := by
  have h1 : (C * X * C⁻¹) * (C * Y * C⁻¹) = (C * Y * C⁻¹) * (C * X * C⁻¹) := by
    calc (C * X * C⁻¹) * (C * Y * C⁻¹) = C * (X * Y) * C⁻¹ := by group
      _ = C * (Y * X) * C⁻¹ := by rw [hXY]
      _ = (C * Y * C⁻¹) * (C * X * C⁻¹) := by group
  rw [h1]
  group

theorem eq_of_odd_orderOf_of_pow_eq_one {Γ : Type*} [CommGroup Γ] {x y : Γ} {i : ℕ}
    (hx : x ^ 2 ^ i = 1) (hy : y ^ 2 ^ i = 1) (hodd : Odd (orderOf (x * y⁻¹))) : x = y := by
  have hpow : (x * y⁻¹) ^ 2 ^ i = 1 := by
    rw [mul_pow, inv_pow, hx, hy]
    simp
  have hdvd := orderOf_dvd_of_pow_eq_one hpow
  have hord : orderOf (x * y⁻¹) = 1 := by
    rcases (Nat.dvd_prime_pow Nat.prime_two).mp hdvd with ⟨j, -, hj⟩
    rw [hj] at hodd ⊢
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · rw [h0]
      rfl
    · exfalso
      have : Even (2 ^ j) := Nat.even_pow.mpr ⟨even_two, h0.ne'⟩
      exact (Nat.not_even_iff_odd.mpr hodd) this
  exact mul_inv_eq_one.mp (orderOf_eq_one_iff.mp hord)

end Aux

section Triv

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

@[expose] noncomputable def trivSub (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G}
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) {t' : G}
    (ht2 : t' * t' = 1) : Subgroup G where
  carrier := {x | ∃ (_ : x ∈ Subgroup.normalizer (K : Set G))
      (_ : t' * x * t' ∈ Subgroup.normalizer (K : Set G)),
      nuG hp hq e x = 1 ∧ nuG hp hq e (t' * x * t') = 1}
  mul_mem' := by
    rintro x y ⟨hx, hx', hνx, hνx'⟩ ⟨hy, hy', hνy, hνy'⟩
    have hxy : t' * (x * y) * t' = (t' * x * t') * (t' * y * t') := tconj_mul ht2 x y
    refine ⟨Subgroup.mul_mem _ hx hy, ?_, ?_, ?_⟩
    · rw [hxy]
      exact Subgroup.mul_mem _ hx' hy'
    · rw [nuG_mul hp hq e hx hy, hνx, hνy, one_mul]
    · rw [hxy, nuG_mul hp hq e hx' hy', hνx', hνy', one_mul]
  one_mem' := by
    have h1 : t' * 1 * t' = 1 := by rw [mul_one, ht2]
    refine ⟨Subgroup.one_mem _, ?_, nuG_one hp hq e, ?_⟩
    · rw [h1]
      exact Subgroup.one_mem _
    · rw [h1]
      exact nuG_one hp hq e
  inv_mem' := by
    rintro x ⟨hx, hx', hνx, hνx'⟩
    have hxi : t' * x⁻¹ * t' = (t' * x * t')⁻¹ := tconj_inv ht2 x
    refine ⟨Subgroup.inv_mem _ hx, ?_, ?_, ?_⟩
    · rw [hxi]
      exact Subgroup.inv_mem _ hx'
    · rw [nuG_inv hp hq e hx, hνx, inv_one]
    · rw [hxi, nuG_inv hp hq e hx', hνx', inv_one]

variable {K : Subgroup G} {t' : G}

theorem mem_trivSub_iff (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) (ht2 : t' * t' = 1)
    {x : G} :
    x ∈ trivSub hp hq e ht2 ↔ ∃ (_ : x ∈ Subgroup.normalizer (K : Set G))
      (_ : t' * x * t' ∈ Subgroup.normalizer (K : Set G)),
      nuG hp hq e x = 1 ∧ nuG hp hq e (t' * x * t') = 1 := Iff.rfl


theorem rightHom_conj_inr (γ : PGL2 (GaloisField p f)) (σ : GaloisField p f ≃+* GaloisField p f) :
    SemidirectProduct.rightHom (SemidirectProduct.inl γ * SemidirectProduct.inr σ *
      (SemidirectProduct.inl γ)⁻¹ : PGammaL2 (GaloisField p f)) = σ := by
  simp

end Triv

section Hyp

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}


theorem z_mem_trivSub (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t') (hp : p ≠ 2)
    (hq : 5 ≤ p ^ f) (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) :
    z ∈ trivSub hp hq e h.ht'2 := by
  have hzK : z ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer h.hz.mem
  have hνz : nuG hp hq e z = 1 := by
    rw [nuG_eq_one_iff hp hq e hzK]
    intro l hl
    have h1 : ⁅z, l⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (h.hz.commute_of_mem hl)
    rw [h1]
    exact Subgroup.one_mem _
  have htz : t' * z * t' = z := by
    calc t' * z * t' = (z * t') * t' := by rw [t'_comm_z h]
      _ = z := by rw [mul_assoc, h.ht'2, mul_one]
  refine ⟨hzK, ?_, hνz, ?_⟩
  · rw [htz]
    exact hzK
  · rw [htz]
    exact hνz

theorem exists_twist_rep (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t') (hp : p ≠ 2)
    (hq : 5 ≤ p ^ f) (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f))
    (γ : PGL2 (GaloisField p f)) {n : G} (hn : n ∈ Subgroup.normalizer (K : Set G))
    (hnz : n * z = z * n) (hn' : t' * n * t' ∈ Subgroup.normalizer (K : Set G))
    (hδ : diagChar hp hq e ⟨n, hn⟩ = 1) (hδ' : diagChar hp hq e ⟨t' * n * t', hn'⟩ = 1) :
    ∃ (g : G) (_ : g ∈ Subgroup.normalizer (K : Set G))
      (_ : t' * g * t' ∈ Subgroup.normalizer (K : Set G)), g * z = z * g ∧
      nuG hp hq e g = SemidirectProduct.inl γ *
        SemidirectProduct.inr (fieldChar hp hq e ⟨n, hn⟩) * (SemidirectProduct.inl γ)⁻¹ ∧
      nuG hp hq e (t' * g * t') = SemidirectProduct.inl γ *
        SemidirectProduct.inr (fieldChar hp hq e ⟨t' * n * t', hn'⟩) *
          (SemidirectProduct.inl γ)⁻¹ := by
  classical
  have ht2 := h.ht'2
  obtain ⟨κ₁, hκ₁K, hκ₁⟩ := exists_mem_K_nuG_eq_conj_inr hp hq e γ hn hδ
  obtain ⟨κ₂, hκ₂K, hκ₂⟩ := exists_mem_K_nuG_eq_conj_inr hp hq e γ hn' hδ'
  have hκ₁N : κ₁ ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hκ₁K
  have hκ₂N : κ₂ ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hκ₂K
  have hκ₁'K' : t' * κ₁ * t' ∈ K' := tconj_mem_K' h hκ₁K
  have hκ₂'K' : t' * κ₂ * t' ∈ K' := tconj_mem_K' h hκ₂K
  have hκ₁'N := K'_le_normalizer h hκ₁'K'
  have hκ₂'N := K'_le_normalizer h hκ₂'K'
  have hνA : nuG hp hq e (t' * κ₂ * t') = 1 := nuG_eq_one_of_mem_K' h hp hq e hκ₂'K'
  have hνB : nuG hp hq e (t' * κ₁ * t') = 1 := nuG_eq_one_of_mem_K' h hp hq e hκ₁'K'
  obtain ⟨g, hgdef⟩ : ∃ g : G, g = (t' * κ₂ * t')⁻¹ * (κ₁⁻¹ * n) := ⟨_, rfl⟩
  have hgN : g ∈ Subgroup.normalizer (K : Set G) := by
    rw [hgdef]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hκ₂'N)
      (Subgroup.mul_mem _ (Subgroup.inv_mem _ hκ₁N) hn)
  have hzg : Commute z g := by
    have c1 : Commute z (t' * κ₂ * t')⁻¹ :=
      Commute.inv_right (show Commute z (t' * κ₂ * t') from h.hz'.commute_of_mem hκ₂'K')
    have c2 : Commute z κ₁⁻¹ :=
      Commute.inv_right (show Commute z κ₁ from h.hz.commute_of_mem hκ₁K)
    have c3 : Commute z n := hnz.symm
    rw [hgdef]
    exact c1.mul_right (c2.mul_right c3)
  have hgz : g * z = z * g := hzg.eq.symm
  have e1 : t' * (t' * κ₂ * t')⁻¹ * t' = κ₂⁻¹ := by
    rw [tconj_inv ht2, tconj_tconj ht2]
  have e2 : t' * (κ₁⁻¹ * n) * t' = (t' * κ₁ * t')⁻¹ * (t' * n * t') := by
    rw [tconj_mul ht2, tconj_inv ht2]
  have hgt : t' * g * t' = κ₂⁻¹ * ((t' * κ₁ * t')⁻¹ * (t' * n * t')) := by
    rw [hgdef, tconj_mul ht2, e1, e2]
  have hgtN : t' * g * t' ∈ Subgroup.normalizer (K : Set G) := tconj_mem_normalizer h hgz hgN
  refine ⟨g, hgN, hgtN, hgz, ?_, ?_⟩
  · rw [hgdef, nuG_mul hp hq e (Subgroup.inv_mem _ hκ₂'N)
      (Subgroup.mul_mem _ (Subgroup.inv_mem _ hκ₁N) hn), nuG_inv hp hq e hκ₂'N, hνA, inv_one,
      one_mul]
    exact hκ₁
  · have hB : (t' * κ₁ * t')⁻¹ ∈ Subgroup.normalizer (K : Set G) := Subgroup.inv_mem _ hκ₁'N
    rw [hgt, nuG_mul hp hq e (Subgroup.inv_mem _ hκ₂N) (Subgroup.mul_mem _ hB hn'),
      nuG_mul hp hq e hB hn', nuG_inv hp hq e hκ₁'N, hνB, inv_one, one_mul,
      ← nuG_mul hp hq e (Subgroup.inv_mem _ hκ₂N) hn']
    exact hκ₂

theorem exists_corrected_rep (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t')
    (hC : (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) =
      Subgroup.zpowers z)
    (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f))
    {a : G} (ha2 : a * a = 1) (haz : a * z = z * a) (hat : a * t' = t' * a)
    (haN : a ∈ Subgroup.normalizer (K : Set G)) {γ : PGL2 (GaloisField p f)}
    {σ₀ σ τ : GaloisField p f ≃+* GaloisField p f}
    (hνa : nuG hp hq e a = SemidirectProduct.inl γ * SemidirectProduct.inr σ₀ *
      (SemidirectProduct.inl γ)⁻¹)
    {g : G} (hgN : g ∈ Subgroup.normalizer (K : Set G)) (hgz : g * z = z * g)
    (hgN' : t' * g * t' ∈ Subgroup.normalizer (K : Set G))
    (hνg : nuG hp hq e g = SemidirectProduct.inl γ * SemidirectProduct.inr σ *
      (SemidirectProduct.inl γ)⁻¹)
    (hνgt : nuG hp hq e (t' * g * t') = SemidirectProduct.inl γ * SemidirectProduct.inr τ *
      (SemidirectProduct.inl γ)⁻¹) :
    ∃ y ∈ trivSub hp hq e h.ht'2, y * z = z * y ∧
      ((y⁻¹ * g) * a = a * (y⁻¹ * g) ∨ (y⁻¹ * g) * a = a * (y⁻¹ * g) * z) := by
  classical
  let _ : CommGroup (GaloisField p f ≃+* GaloisField p f) := ringAutCommGroup _
  have ht2 := h.ht'2
  have hz2 : z * z = 1 := h.hz.sq
  have haz' : z * a = a * z := haz.symm
  have hgz' : z * g = g * z := hgz.symm
  have hXσ : (SemidirectProduct.inr σ : PGammaL2 (GaloisField p f)) * SemidirectProduct.inr σ₀ =
      SemidirectProduct.inr σ₀ * SemidirectProduct.inr σ := by
    rw [← map_mul, ← map_mul, mul_comm]
  have hXτ : (SemidirectProduct.inr τ : PGammaL2 (GaloisField p f)) * SemidirectProduct.inr σ₀ =
      SemidirectProduct.inr σ₀ * SemidirectProduct.inr τ := by
    rw [← map_mul, ← map_mul, mul_comm]
  obtain ⟨u, hudef⟩ : ∃ u : G, u = g * a * g⁻¹ * a⁻¹ := ⟨_, rfl⟩
  have hga : g * a ∈ Subgroup.normalizer (K : Set G) := Subgroup.mul_mem _ hgN haN
  have hgaN : g * a * g⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
    Subgroup.mul_mem _ hga (Subgroup.inv_mem _ hgN)
  have huN : u ∈ Subgroup.normalizer (K : Set G) := by
    rw [hudef]
    exact Subgroup.mul_mem _ hgaN (Subgroup.inv_mem _ haN)
  have huz : u * z = z * u := by
    have c1 : Commute z g := hgz'
    have c2 : Commute z a := haz'
    have hc : Commute z u := by
      rw [hudef]
      exact ((c1.mul_right c2).mul_right c1.inv_right).mul_right c2.inv_right
    exact hc.eq.symm
  have hutN : t' * u * t' ∈ Subgroup.normalizer (K : Set G) := tconj_mem_normalizer h huz huN
  have hνu : nuG hp hq e u = 1 := by
    rw [hudef, nuG_mul hp hq e hgaN (Subgroup.inv_mem _ haN),
      nuG_mul hp hq e hga (Subgroup.inv_mem _ hgN), nuG_mul hp hq e hgN haN,
      nuG_inv hp hq e hgN, nuG_inv hp hq e haN, hνg, hνa]
    exact conj_comm_eq_one _ _ _ hXσ
  have hat1 : t' * a * t' = a := by
    rw [← hat, mul_assoc, ht2, mul_one]
  have hut : t' * u * t' = (t' * g * t') * a * (t' * g * t')⁻¹ * a⁻¹ := by
    rw [hudef, tconj_mul ht2, tconj_mul ht2, tconj_mul ht2, tconj_inv ht2 g, tconj_inv ht2 a,
      hat1]
  have hgta : (t' * g * t') * a ∈ Subgroup.normalizer (K : Set G) :=
    Subgroup.mul_mem _ hgN' haN
  have hgtaN : (t' * g * t') * a * (t' * g * t')⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
    Subgroup.mul_mem _ hgta (Subgroup.inv_mem _ hgN')
  have hνut : nuG hp hq e (t' * u * t') = 1 := by
    rw [hut, nuG_mul hp hq e hgtaN (Subgroup.inv_mem _ haN),
      nuG_mul hp hq e hgta (Subgroup.inv_mem _ hgN'), nuG_mul hp hq e hgN' haN,
      nuG_inv hp hq e hgN', nuG_inv hp hq e haN, hνgt, hνa]
    exact conj_comm_eq_one _ _ _ hXτ
  have huT : u ∈ trivSub hp hq e ht2 := ⟨huN, hutN, hνu, hνut⟩
  have hord0 : orderOf u ≠ 0 := (orderOf_pos u).ne'
  obtain ⟨s, o, ho, hso⟩ := Nat.exists_eq_two_pow_mul_odd hord0
  have huo : u ^ o = 1 ∨ u ^ o = z := by
    have hord : orderOf (u ^ o) = 2 ^ s := by
      have h1 : o ∣ orderOf u := ⟨2 ^ s, by rw [hso, mul_comm]⟩
      rw [orderOf_pow_of_dvd ho.pos.ne' h1, hso, Nat.mul_div_cancel _ ho.pos]
    have hz' : u ^ o * z = z * u ^ o := (Commute.pow_left (show Commute u z from huz) o).eq
    exact eq_one_or_eq_z_of_nuG_eq_one h hC hp hq e hord hz' (Subgroup.pow_mem _ huN o)
      (by rw [tconj_pow ht2]; exact Subgroup.pow_mem _ hutN o)
      (by rw [nuG_pow hp hq e huN, hνu, one_pow])
      (by rw [tconj_pow ht2, nuG_pow hp hq e hutN, hνut, one_pow])
  have hau : a * u * a⁻¹ = u⁻¹ := by
    have ha1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    calc a * u * a⁻¹ = a * g * a * g⁻¹ * (a⁻¹ * a⁻¹) := by rw [hudef]; group
      _ = a * g * a * g⁻¹ := by rw [ha1, ha2, mul_one]
      _ = u⁻¹ := by
        rw [hudef]
        simp only [mul_inv_rev, inv_inv, ha1]
        group
  obtain ⟨w, y, j, hj1, hw, ⟨k, hk⟩, hya⟩ :=
    exists_pow_conj_of_inverted hz2 haz' huz.symm hau ho huo
  have hzT : z ∈ trivSub hp hq e ht2 := z_mem_trivSub h hp hq e
  have hwT : w ∈ trivSub hp hq e ht2 := by
    rw [hw]
    exact Subgroup.mul_mem _ huT (Subgroup.pow_mem _ hzT j)
  have hyT : y ∈ trivSub hp hq e ht2 := by
    rw [hk]
    exact Subgroup.pow_mem _ hwT k
  have hyz : y * z = z * y := by
    have hwz : Commute w z := by
      rw [hw]
      exact (show Commute u z from huz).mul_left ((Commute.refl z).pow_left j)
    rw [hk]
    exact (Commute.pow_left hwz k).eq
  exact ⟨y, hyT, hyz, comm_or_comm_z_of_conj hz2 haz' hgz' hyz.symm hudef hj1 hw hya⟩

theorem exists_comm_of_comm_or_z (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t') (hp : p ≠ 2)
    (hq : 5 ≤ p ^ f) (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) {a : G}
    (hFa : IsFAut R a) (ha2 : a * a = 1) {d₀ : G}
    (hd₀N : d₀ ∈ Subgroup.normalizer (K : Set G)) (hd₀z : d₀ * z = z * d₀)
    (hd₀N' : t' * d₀ * t' ∈ Subgroup.normalizer (K : Set G))
    (hc : d₀ * a = a * d₀ ∨ d₀ * a = a * d₀ * z) :
    ∃ (d : G) (hdN : d ∈ Subgroup.normalizer (K : Set G))
      (hdN' : t' * d * t' ∈ Subgroup.normalizer (K : Set G)), d * z = z * d ∧ d * a = a * d ∧
      fieldChar hp hq e ⟨d, hdN⟩ = fieldChar hp hq e ⟨d₀, hd₀N⟩ ∧
      fieldChar hp hq e ⟨t' * d * t', hdN'⟩ = fieldChar hp hq e ⟨t' * d₀ * t', hd₀N'⟩ := by
  classical
  have ht2 := h.ht'2
  have hzz : z * z = 1 := h.hz.sq
  rcases hc with hc | hc
  · exact ⟨d₀, hd₀N, hd₀N', hd₀z, hc, rfl, rfl⟩
  · obtain ⟨k, hkR, hk⟩ := exists_mem_comm_z_of_isFAut h.hqR h.hzR hFa ha2
    have hkK : k ∈ K := h.hRsyl.1 hkR
    have hkN : k ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hkK
    have hkz : k * z = z * k := comm_z_of_mem h.hzR hkR
    have hk' : t' * k * t' ∈ K' := tconj_mem_K' h hkK
    have hk'N : t' * k * t' ∈ Subgroup.normalizer (K : Set G) := K'_le_normalizer h hk'
    have hk'χ : fieldChar hp hq e ⟨t' * k * t', hk'N⟩ = 1 := by
      rw [fieldChar_eq_rightHom_nuG hp hq e hk'N, nuG_eq_one_of_mem_K' h hp hq e hk', map_one]
    have hdN : d₀ * k ∈ Subgroup.normalizer (K : Set G) := Subgroup.mul_mem _ hd₀N hkN
    have hdz : d₀ * k * z = z * (d₀ * k) := by
      calc d₀ * k * z = d₀ * (k * z) := by rw [mul_assoc]
        _ = d₀ * (z * k) := by rw [hkz]
        _ = (d₀ * z) * k := by rw [mul_assoc]
        _ = z * d₀ * k := by rw [hd₀z]
        _ = z * (d₀ * k) := by rw [mul_assoc]
    have hda : d₀ * k * a = a * (d₀ * k) := by
      have h1 : a * d₀ = d₀ * a * z := by
        calc a * d₀ = (a * d₀ * z) * z := by rw [mul_assoc, hzz, mul_one]
          _ = (d₀ * a) * z := by rw [← hc]
      have h2 : a * k = z * k * a := by
        calc a * k = (a * k * a⁻¹) * a := by group
          _ = z * k * a := by rw [hk]
      calc d₀ * k * a = d₀ * (k * a) := by rw [mul_assoc]
        _ = d₀ * (a * a * (k * a)) := by rw [ha2, one_mul]
        _ = d₀ * a * (a * k) * a := by group
        _ = d₀ * a * (z * k * a) * a := by rw [h2]
        _ = (d₀ * a * z) * k * (a * a) := by group
        _ = (a * d₀) * k := by rw [ha2, mul_one, ← h1]
        _ = a * (d₀ * k) := by rw [mul_assoc]
    have hdN' : t' * (d₀ * k) * t' ∈ Subgroup.normalizer (K : Set G) := by
      rw [tconj_mul ht2]
      exact Subgroup.mul_mem _ hd₀N' hk'N
    refine ⟨d₀ * k, hdN, hdN', hdz, hda, ?_, ?_⟩
    · have e1 : (⟨d₀ * k, hdN⟩ : Subgroup.normalizer (K : Set G)) = ⟨d₀, hd₀N⟩ * ⟨k, hkN⟩ := rfl
      rw [e1, map_mul, fieldChar_eq_one_of_mem hp hq e hkK hkN, mul_one]
    · have e2 : (⟨t' * (d₀ * k) * t', hdN'⟩ : Subgroup.normalizer (K : Set G)) =
          ⟨t' * d₀ * t', hd₀N'⟩ * ⟨t' * k * t', hk'N⟩ :=
        Subtype.ext (tconj_mul ht2 d₀ k)
      rw [e2, map_mul, hk'χ, mul_one]

theorem exists_comm_rep (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t')
    (hC : (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) =
      Subgroup.zpowers z)
    (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f))
    {a : G} (ha2 : a * a = 1) (haz : a * z = z * a) (hat : a * t' = t' * a) (hFa : IsFAut R a)
    (haN : a ∈ Subgroup.normalizer (K : Set G)) (hσ : fieldChar hp hq e ⟨a, haN⟩ ≠ 1) {n : G}
    (hn : n ∈ Subgroup.normalizer (K : Set G)) (hnz : n * z = z * n)
    (hn' : t' * n * t' ∈ Subgroup.normalizer (K : Set G))
    (hδ : diagChar hp hq e ⟨n, hn⟩ = 1) (hδ' : diagChar hp hq e ⟨t' * n * t', hn'⟩ = 1) :
    ∃ (d : G) (hdN : d ∈ Subgroup.normalizer (K : Set G))
      (hdN' : t' * d * t' ∈ Subgroup.normalizer (K : Set G)), d * z = z * d ∧ d * a = a * d ∧
      fieldChar hp hq e ⟨d, hdN⟩ = fieldChar hp hq e ⟨n, hn⟩ ∧
      fieldChar hp hq e ⟨t' * d * t', hdN'⟩ = fieldChar hp hq e ⟨t' * n * t', hn'⟩ := by
  classical
  have ht2 := h.ht'2
  have hα : nuG hp hq e a * nuG hp hq e a = 1 := by
    rw [← nuG_mul hp hq e haN haN, ha2, nuG_one]
  have hα' : (nuG hp hq e a).right ≠ 1 := by
    rw [nuG_of_mem hp hq e haN]
    exact hσ
  obtain ⟨γ, hγ⟩ := exists_pgl_conj_inr hp (gf_facts hp hq).1 hq (nuG hp hq e a) hα hα'
  have hνa := eq_inl_mul_inr_mul_inv (nuG hp hq e a) γ hγ
  obtain ⟨g, hgN, hgN', hgz, hνg, hνgt⟩ := exists_twist_rep h hp hq e γ hn hnz hn' hδ hδ'
  obtain ⟨y, hyT, hyz, hy⟩ := exists_corrected_rep h hC hp hq e ha2 haz hat haN hνa hgN hgz hgN'
    hνg hνgt
  have hyiT : y⁻¹ ∈ trivSub hp hq e ht2 := Subgroup.inv_mem _ hyT
  obtain ⟨hyiN, hyiN', hνyi, hνyi'⟩ := hyiT
  have hd₀N : y⁻¹ * g ∈ Subgroup.normalizer (K : Set G) := Subgroup.mul_mem _ hyiN hgN
  have hd₀z : (y⁻¹ * g) * z = z * (y⁻¹ * g) := by
    have c1 : Commute z y⁻¹ := (show Commute z y from hyz.symm).inv_right
    have c2 : Commute z g := hgz.symm
    exact (c1.mul_right c2).eq.symm
  have hd₀N' : t' * (y⁻¹ * g) * t' ∈ Subgroup.normalizer (K : Set G) :=
    tconj_mem_normalizer h hd₀z hd₀N
  have hχd₀ : fieldChar hp hq e ⟨y⁻¹ * g, hd₀N⟩ = fieldChar hp hq e ⟨n, hn⟩ := by
    rw [fieldChar_eq_rightHom_nuG hp hq e hd₀N, nuG_mul hp hq e hyiN hgN, hνyi, one_mul, hνg,
      rightHom_conj_inr]
  have hχd₀' : fieldChar hp hq e ⟨t' * (y⁻¹ * g) * t', hd₀N'⟩ =
      fieldChar hp hq e ⟨t' * n * t', hn'⟩ := by
    rw [fieldChar_eq_rightHom_nuG hp hq e hd₀N', tconj_mul ht2, nuG_mul hp hq e hyiN' hgN',
      hνyi', one_mul, hνgt, rightHom_conj_inr]
  obtain ⟨d, hdN, hdN', hdz, hda, hχd, hχd'⟩ :=
    exists_comm_of_comm_or_z h hp hq e hFa ha2 hd₀N hd₀z hd₀N' hy
  exact ⟨d, hdN, hdN', hdz, hda, hχd.trans hχd₀, hχd'.trans hχd₀'⟩

end Hyp

end CFSG.ClassicalInvolution.Asc77.C25V
