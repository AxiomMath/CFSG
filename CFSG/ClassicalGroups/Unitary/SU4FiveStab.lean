module

public import CFSG.ClassicalInvolution.Phan.Torus
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16Norm

public section

namespace CFSG.ClassicalGroups.Unitary

open CFSG.Open
open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg
  CFSG.ClassicalInvolution.Phan
open scoped Matrix

private theorem normOne_card_eq {K : Type*} [Field K] [Finite K]
    {σ : K ≃+* K} (hσ : IsUnitaryInvolution σ) (h2 : (2 : K) = 0)
    (hK : Nat.card K = 16) :
    Nat.card (normOne σ) = 5 := by
  let F : Subfield K := σ.toRingHom.eqLocusField (RingHom.id K)
  have hFmem : ∀ x : K, x ∈ F ↔ σ x = x := fun x => Iff.rfl
  obtain ⟨c, hc⟩ := hσ.exists_ne
  have htfix : σ (c + σ c) = c + σ c := by
    rw [map_add, hσ.invol, add_comm]
  have ht0 : c + σ c ≠ 0 := by
    intro h
    have hσc : σ c = -c := by
      rw [← add_eq_zero_iff_eq_neg]
      have h' : σ c + c = 0 := by rw [add_comm]; exact h
      exact h'
    have hneg : -c = c := by
      rw [neg_eq_iff_add_eq_zero, ← two_mul, h2, zero_mul]
    exact hc (hσc.trans hneg)
  let t : F := ⟨c + σ c, htfix⟩
  have ht0' : (t : K) ≠ 0 := ht0
  let f : F × F → K := fun p => (p.1 : K) + (p.2 : K) * c
  have hf_inj : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    simp only [f, Subtype.coe_mk] at h
    by_cases hbb : b = b'
    · have h' : (a : K) + (b : K) * c = (a' : K) + (b : K) * c := by
        rw [← hbb] at h
        exact h
      exact Prod.ext (Subtype.ext (add_right_cancel h')) hbb
    · exfalso
      have hden : (b' : K) - (b : K) ≠ 0 := by
        intro hzero
        apply hbb
        exact Subtype.ext (sub_eq_zero.mp hzero).symm
      have hprod : ((b' : K) - (b : K)) * c = (a : K) - (a' : K) := by
        linear_combination -h
      have hcF : c ∈ F := by
        have hcEq : c = ((a : K) - (a' : K)) / ((b' : K) - (b : K)) := by
          rw [eq_div_iff hden, mul_comm]
          exact hprod
        rw [hcEq]
        exact F.div_mem (F.sub_mem a.2 a'.2) (F.sub_mem b'.2 b.2)
      exact hc ((hFmem c).mp hcF)
  have hf_surj : Function.Surjective f := by
    intro x
    have hxfix : σ (x + σ x) = x + σ x := by
      rw [map_add, hσ.invol, add_comm]
    have ht2 : σ (t : K) = (t : K) := t.2
    let b : F := ⟨(x + σ x) / (t : K), by
      show σ ((x + σ x) / (t : K)) = (x + σ x) / (t : K)
      rw [map_div₀, hxfix, ht2]⟩
    have hbt : (b : K) * (t : K) = x + σ x := by
      show ((x + σ x) / (t : K)) * (t : K) = x + σ x
      field_simp
    have hfixa : σ (x + (b : K) * c) = x + (b : K) * c := by
      have hb2 : σ (b : K) = (b : K) := b.2
      have hsum : (x + (b : K) * c) + σ (x + (b : K) * c) = 0 := by
        rw [map_add, map_mul, hb2]
        calc
          x + (b : K) * c + (σ x + (b : K) * σ c)
              = (x + σ x) + (b : K) * (c + σ c) := by ring
          _ = (x + σ x) + (b : K) * (t : K) := by
                rw [show c + σ c = (t : K) from rfl]
          _ = (x + σ x) + (x + σ x) := by rw [hbt]
          _ = 0 := by rw [← two_mul, h2, zero_mul]
      have hsum' : σ (x + (b : K) * c) + (x + (b : K) * c) = 0 := by
        rw [add_comm]
        exact hsum
      have hσa : σ (x + (b : K) * c) = -(x + (b : K) * c) := by
        rw [← add_eq_zero_iff_eq_neg]
        exact hsum'
      have hneg : -(x + (b : K) * c) = x + (b : K) * c := by
        rw [neg_eq_iff_add_eq_zero, ← two_mul, h2, zero_mul]
      exact hσa.trans hneg
    let a : F := ⟨x + (b : K) * c, hfixa⟩
    refine ⟨⟨a, b⟩, ?_⟩
    show (a : K) + (b : K) * c = x
    show (x + (b : K) * c) + (b : K) * c = x
    rw [add_assoc, show (b : K) * c + (b : K) * c = 0 by
      rw [← two_mul, h2, zero_mul], add_zero]
  have hbij : Function.Bijective f := ⟨hf_inj, hf_surj⟩
  have hcard : Nat.card F * Nat.card F = 16 := by
    have h := Nat.card_congr (Equiv.ofBijective f hbij)
    rw [Nat.card_prod] at h
    rw [h, hK]
  have hFcard : Nat.card F = 4 := by
    rw [show (16 : ℕ) = 4 * 4 by norm_num] at hcard
    exact Nat.mul_self_inj.mp hcard
  let φ : K →* F :=
    { toFun := fun x => ⟨σ x * x, by
        show σ (σ x * x) = σ x * x
        rw [map_mul, hσ.invol, mul_comm]⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        show σ (x * y) * (x * y) = (σ x * x) * (σ y * y)
        rw [map_mul]
        ring }
  have hsurj : Function.Surjective (Units.map φ) := by
    intro v
    have hvfix : σ ((v : F) : K) = ((v : F) : K) := (v : F).2
    have hv0 : ((v : F) : K) ≠ 0 := by
      intro hzero
      exact v.ne_zero (Subtype.ext hzero)
    obtain ⟨x, hx⟩ := hσ.norm_surj ((v : F) : K) hvfix hv0
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [map_zero, zero_mul] at hx
      exact hv0 hx.symm
    refine ⟨Units.mk0 x hx0, ?_⟩
    apply Units.ext
    apply Subtype.ext
    show σ x * x = ((v : F) : K)
    exact hx
  have hker : (Units.map φ).ker = normOne σ := by
    ext u
    rw [MonoidHom.mem_ker, mem_normOne]
    constructor
    · intro h
      have hF : (Units.map φ u : Fˣ) = 1 := h
      have hK : ((φ (u : K) : F) : K) = ((1 : F) : K) :=
        congrArg (fun w : Fˣ => ((w : F) : K)) hF
      show σ (u : K) * (u : K) = 1
      simpa [φ] using hK
    · intro h
      apply Units.ext
      rw [Units.coe_map, Units.val_one]
      exact Subtype.ext (by simpa [φ] using h)
  have hcardKer : Nat.card (normOne σ) = 5 := by
    have h := Subgroup.card_ker_mul_card_of_surjective (f := Units.map φ) hsurj
    rw [hker] at h
    have hFunits : Nat.card Fˣ = 3 := by
      rw [Nat.card_units, hFcard]
    have hKunits : Nat.card Kˣ = 15 := by
      rw [Nat.card_units, hK]
    rw [hFunits, hKunits] at h
    omega
  exact hcardKer

private noncomputable def anisoTupleHom {K : Type*} [Field K] {σ : K ≃+* K} :
    normOne σ × normOne σ →* detKer σ 4 where
  toFun p := ⟨![p.1, p.2, p.1⁻¹ * p.2⁻¹, 1], by
    rw [mem_detKer, Fin.prod_univ_four]
    have h0 : (![p.1, p.2, p.1⁻¹ * p.2⁻¹, 1] : Fin 4 → normOne σ) 0 = p.1 := rfl
    have h1 : (![p.1, p.2, p.1⁻¹ * p.2⁻¹, 1] : Fin 4 → normOne σ) 1 = p.2 := rfl
    have h2 : (![p.1, p.2, p.1⁻¹ * p.2⁻¹, 1] : Fin 4 → normOne σ) 2 =
      p.1⁻¹ * p.2⁻¹ := rfl
    have h3 : (![p.1, p.2, p.1⁻¹ * p.2⁻¹, 1] : Fin 4 → normOne σ) 3 = 1 := rfl
    rw [h0, h1, h2, h3, mul_one]
    calc p.1 * p.2 * (p.1⁻¹ * p.2⁻¹)
        = (p.1 * p.1⁻¹) * (p.2 * p.2⁻¹) := by ac_rfl
      _ = 1 := by simp⟩
  map_one' := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp
  map_mul' p q := by
    apply Subtype.ext
    funext i
    fin_cases i
    · rfl
    · rfl
    · show (p.1 * q.1)⁻¹ * (p.2 * q.2)⁻¹ =
        (p.1⁻¹ * p.2⁻¹) * (q.1⁻¹ * q.2⁻¹)
      rw [_root_.mul_inv_rev, _root_.mul_inv_rev]
      ac_rfl
    · simp

private noncomputable def isoTupleHom {K : Type*} [Field K] {σ : K ≃+* K} :
    normOne σ × normOne σ →* detKer σ 4 where
  toFun p := ⟨![p.1, p.1, p.2, p.1⁻¹ * p.1⁻¹ * p.2⁻¹], by
    rw [mem_detKer, Fin.prod_univ_four]
    have h0 : (![p.1, p.1, p.2, p.1⁻¹ * p.1⁻¹ * p.2⁻¹] : Fin 4 → normOne σ) 0 = p.1 := rfl
    have h1 : (![p.1, p.1, p.2, p.1⁻¹ * p.1⁻¹ * p.2⁻¹] : Fin 4 → normOne σ) 1 = p.1 := rfl
    have h2 : (![p.1, p.1, p.2, p.1⁻¹ * p.1⁻¹ * p.2⁻¹] : Fin 4 → normOne σ) 2 = p.2 := rfl
    have h3 : (![p.1, p.1, p.2, p.1⁻¹ * p.1⁻¹ * p.2⁻¹] : Fin 4 → normOne σ) 3 =
      p.1⁻¹ * p.1⁻¹ * p.2⁻¹ := rfl
    rw [h0, h1, h2, h3]
    calc p.1 * p.1 * p.2 * (p.1⁻¹ * p.1⁻¹ * p.2⁻¹)
        = (p.1 * p.1⁻¹) * (p.1 * p.1⁻¹) * (p.2 * p.2⁻¹) := by ac_rfl
      _ = 1 := by simp⟩
  map_one' := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp
  map_mul' p q := by
    apply Subtype.ext
    funext i
    fin_cases i
    · rfl
    · rfl
    · rfl
    · show ((p.1 * q.1)⁻¹ * (p.1 * q.1)⁻¹) * (p.2 * q.2)⁻¹ =
        (p.1⁻¹ * p.1⁻¹ * p.2⁻¹) * (q.1⁻¹ * q.1⁻¹ * q.2⁻¹)
      simp only [_root_.mul_inv_rev]
      ac_rfl

private theorem anisoTupleHom_injective {K : Type*} [Field K] {σ : K ≃+* K} :
    Function.Injective (anisoTupleHom (σ := σ)) := by
  intro p q h
  have h0 := congrArg (fun d : detKer σ 4 => (d.1 0 : normOne σ)) h
  have h1 := congrArg (fun d : detKer σ 4 => (d.1 1 : normOne σ)) h
  have hp0 : (![p.1, p.2, p.1⁻¹ * p.2⁻¹, 1] : Fin 4 → normOne σ) 0 = p.1 := rfl
  have hq0 : (![q.1, q.2, q.1⁻¹ * q.2⁻¹, 1] : Fin 4 → normOne σ) 0 = q.1 := rfl
  have hp1 : (![p.1, p.2, p.1⁻¹ * p.2⁻¹, 1] : Fin 4 → normOne σ) 1 = p.2 := rfl
  have hq1 : (![q.1, q.2, q.1⁻¹ * q.2⁻¹, 1] : Fin 4 → normOne σ) 1 = q.2 := rfl
  simp only [anisoTupleHom, MonoidHom.coe_mk, OneHom.coe_mk, Subtype.coe_mk, hp0, hq0, hp1,
    hq1] at h0 h1
  exact Prod.ext h0 h1

private theorem isoTupleHom_injective {K : Type*} [Field K] {σ : K ≃+* K} :
    Function.Injective (isoTupleHom (σ := σ)) := by
  intro p q h
  have h0 := congrArg (fun d : detKer σ 4 => (d.1 0 : normOne σ)) h
  have h2 := congrArg (fun d : detKer σ 4 => (d.1 2 : normOne σ)) h
  have hp0 : (![p.1, p.1, p.2, p.1⁻¹ * p.1⁻¹ * p.2⁻¹] : Fin 4 → normOne σ) 0 = p.1 := rfl
  have hq0 : (![q.1, q.1, q.2, q.1⁻¹ * q.1⁻¹ * q.2⁻¹] : Fin 4 → normOne σ) 0 = q.1 := rfl
  have hp2 : (![p.1, p.1, p.2, p.1⁻¹ * p.1⁻¹ * p.2⁻¹] : Fin 4 → normOne σ) 2 = p.2 := rfl
  have hq2 : (![q.1, q.1, q.2, q.1⁻¹ * q.1⁻¹ * q.2⁻¹] : Fin 4 → normOne σ) 2 = q.2 := rfl
  simp only [isoTupleHom, MonoidHom.coe_mk, OneHom.coe_mk, Subtype.coe_mk, hp0, hq0, hp2,
    hq2] at h0 h2
  exact Prod.ext h0 h2

private def nval {K : Type*} [Field K] {σ : K ≃+* K} (u : normOne σ) : K :=
  ((u : Kˣ) : K)

private theorem exists_five_stab_of_move {K : Type*} [Field K] [Finite K]
    {σ : K ≃+* K} (hσ : IsUnitaryInvolution σ) (h2 : (2 : K) = 0)
    (hK : Nat.card K = 16)
    {x v0 : Fin 4 → K}
    (ψ : normOne σ × normOne σ →* detKer σ 4)
    (hψinj : Function.Injective ψ)
    (hscale : ∀ p : normOne σ × normOne σ,
      diagSU σ (ψ p).1 (ψ p).2 • v0 = nval p.1 • v0)
    (t : SUid σ 4) (a : K) (ha0 : a ≠ 0) (ht : t • v0 = a • x) :
    ∃ E : Subgroup (GL (Fin 4) K), E ≤ SUid σ 4 ∧ IsElemAbelian 5 E ∧
      Nat.card E = 25 ∧
      ∀ g ∈ E, ∃ c : K, (g : Matrix (Fin 4) (Fin 4) K) *ᵥ x = c • x := by
  have hNcard : Nat.card (normOne σ) = 5 := normOne_card_eq hσ h2 hK
  have hNpow : ∀ u : normOne σ, u ^ 5 = 1 := by
    intro u
    have h := pow_card_eq_one' (G := normOne σ) (x := u)
    rwa [hNcard] at h
  let g : normOne σ × normOne σ →* SUid σ 4 :=
    (MulAut.conj t).toMonoidHom.comp ((diagSUHom σ 4).comp ψ)
  let φ : normOne σ × normOne σ →* GL (Fin 4) K :=
    (SUid σ 4).subtype.comp g
  let E : Subgroup (GL (Fin 4) K) := φ.range
  have hφinj : Function.Injective φ := by
    intro p q hpq
    have h1 : g p = g q := Subtype.coe_injective hpq
    have h2 : (diagSUHom σ 4) (ψ p) = (diagSUHom σ 4) (ψ q) := by
      apply (MulAut.conj t).injective
      simpa [g] using h1
    exact hψinj (diagSUHom_injective 4 h2)
  have hEcard : Nat.card E = 25 := by
    have h := Nat.card_range_of_injective (f := φ) hφinj
    have hE : Nat.card E = Nat.card (Set.range φ) := rfl
    rw [hE, h, Nat.card_prod, hNcard]
  have hEsub : E ≤ SUid σ 4 := by
    intro y hy
    obtain ⟨p, rfl⟩ := hy
    exact (g p).2
  have hEea : IsElemAbelian 5 E := by
    refine ⟨?_, ?_⟩
    · refine IsMulCommutative.of_comm fun y z => ?_
      obtain ⟨p, hp⟩ := y.2
      obtain ⟨q, hq⟩ := z.2
      apply Subtype.ext
      change y.1 * z.1 = z.1 * y.1
      rw [← hp, ← hq, ← map_mul, ← map_mul, mul_comm p q]
    · intro y hy
      obtain ⟨p, hp⟩ := hy
      rw [← hp, ← map_pow]
      have hp5 : p ^ 5 = 1 := by
        ext <;> simp [hNpow]
      rw [hp5, map_one]
  refine ⟨E, hEsub, hEea, hEcard, ?_⟩
  intro y hy
  obtain ⟨p, hp⟩ := hy
  refine ⟨nval p.1, ?_⟩
  have hpre : t⁻¹ • x = a⁻¹ • v0 := by
    have h1 : t⁻¹ • (a • x) = v0 := by rw [← ht, inv_smul_smul]
    have h2 : a • (t⁻¹ • x) = v0 := by
      rw [smul_comm a t⁻¹ x, h1]
    calc t⁻¹ • x = a⁻¹ • (a • (t⁻¹ • x)) := by
          rw [smul_smul, inv_mul_cancel₀ ha0, one_smul]
      _ = a⁻¹ • v0 := by rw [h2]
  have hSu : (t * diagSU σ (ψ p).1 (ψ p).2 * t⁻¹) • x = nval p.1 • x := by
    calc (t * diagSU σ (ψ p).1 (ψ p).2 * t⁻¹) • x
        = t • (diagSU σ (ψ p).1 (ψ p).2 • (t⁻¹ • x)) := by
            rw [mul_smul, mul_smul]
      _ = t • (diagSU σ (ψ p).1 (ψ p).2 • (a⁻¹ • v0)) := by rw [hpre]
      _ = t • (a⁻¹ • (diagSU σ (ψ p).1 (ψ p).2 • v0)) := by
            rw [smul_comm a⁻¹ (diagSU σ (ψ p).1 (ψ p).2) v0]
      _ = t • (a⁻¹ • (nval p.1 • v0)) := by rw [hscale p]
      _ = t • ((a⁻¹ * nval p.1) • v0) := by rw [smul_smul]
      _ = (a⁻¹ * nval p.1) • (t • v0) := by
            rw [smul_comm (a⁻¹ * nval p.1) t v0]
      _ = (a⁻¹ * nval p.1) • (a • x) := by rw [ht]
      _ = ((a⁻¹ * nval p.1) * a) • x := by rw [smul_smul]
      _ = nval p.1 • x := by
            rw [show (a⁻¹ * nval p.1) * a = nval p.1 by
              field_simp]
  calc ((y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ x
      = (g p) • x := by
          rw [← hp]
          show ((↑(g p) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ x = (g p) • x
          rw [CFSG.ClassicalGroups.Unitary.smul_def]
    _ = (t * diagSU σ (ψ p).1 (ψ p).2 * t⁻¹) • x := by
          change ((MulAut.conj t) ((diagSUHom σ 4) (ψ p))) • x = _
          rw [MulAut.conj_apply, diagSUHom_apply]
    _ = nval p.1 • x := hSu

private def su4IsoVec (K : Type*) [Field K] : Fin 4 → K := ![1, 1, 0, 0]

private def su4AnisoVec (K : Type*) [Field K] : Fin 4 → K := Pi.single 0 1

private theorem su4IsoVec_ne_zero {K : Type*} [Field K] : su4IsoVec K ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [su4IsoVec] at this

private theorem herm_su4IsoVec {K : Type*} [Field K] {σ : K ≃+* K} (h2 : (2 : K) = 0) :
    herm σ (su4IsoVec K) (su4IsoVec K) = 0 := by
  have h11 : (1 : K) + 1 = 0 := by rw [← two_mul, h2, zero_mul]
  simp [herm, su4IsoVec, Fin.sum_univ_four, h11]

private theorem herm_su4AnisoVec {K : Type*} [Field K] {σ : K ≃+* K} :
    herm σ (su4AnisoVec K) (su4AnisoVec K) = 1 := by
  rw [su4AnisoVec, herm_single_right]
  simp

private theorem isoDiag_scale {K : Type*} [Field K] {σ : K ≃+* K}
    (p : normOne σ × normOne σ) :
    diagSU σ (isoTupleHom (σ := σ) p).1 (isoTupleHom (σ := σ) p).2 • su4IsoVec K =
      nval p.1 • su4IsoVec K := by
  rw [diagSU_smul]
  funext i
  fin_cases i <;> simp [su4IsoVec, isoTupleHom, nval]

private theorem anisoDiag_scale {K : Type*} [Field K] {σ : K ≃+* K}
    (p : normOne σ × normOne σ) :
    diagSU σ (anisoTupleHom (σ := σ) p).1 (anisoTupleHom (σ := σ) p).2 • su4AnisoVec K =
      nval p.1 • su4AnisoVec K := by
  rw [diagSU_smul]
  funext i
  fin_cases i <;> simp [su4AnisoVec, anisoTupleHom, nval]

theorem exists_elemAbelian_five_stab_line {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ 2) ^ 2) (x : Fin 4 → K) (hx : x ≠ 0) :
    ∃ E : Subgroup (GL (Fin 4) K), E ≤ StatedSU 4 (2 ^ 2) K ∧ IsElemAbelian 5 E ∧
      Nat.card E = 25 ∧ ∀ g ∈ E, ∃ c : K, (g : Matrix (Fin 4) (Fin 4) K) *ᵥ x = c • x := by
  obtain ⟨σ, hσ, h2, hS⟩ := CFSG.LocalAnalysis.RankThreeUC.statedSU_data (n := 2) hK
  have hK16 : Nat.card K = 16 := by rw [hK]; norm_num
  by_cases hxiso : herm σ x x = 0
  · obtain ⟨t, -, ht⟩ := exists_mem_T_smul_eq_of_iso hσ (n := 4) (by norm_num)
      (su4IsoVec_ne_zero (K := K)) (herm_su4IsoVec h2) hx hxiso
    obtain ⟨E, hEsub, hEea, hEcard, hEline⟩ :=
      exists_five_stab_of_move hσ h2 hK16 (isoTupleHom (σ := σ)) isoTupleHom_injective
        isoDiag_scale t 1 one_ne_zero (by simpa using ht)
    exact ⟨E, by rw [← hS]; exact hEsub, hEea, hEcard, hEline⟩
  · push Not at hxiso
    obtain ⟨a, ha⟩ := exists_smul_norm_one hσ hxiso
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [zero_smul, herm_zero_left] at ha
      exact zero_ne_one ha
    obtain ⟨t, -, ht⟩ := exists_mem_T_smul_eq_of_norm_one hσ (n := 4) (Or.inl (by norm_num))
      (herm_su4AnisoVec (σ := σ)) ha
    obtain ⟨E, hEsub, hEea, hEcard, hEline⟩ :=
      exists_five_stab_of_move hσ h2 hK16 (anisoTupleHom (σ := σ)) anisoTupleHom_injective
        anisoDiag_scale t a ha0 ht
    exact ⟨E, by rw [← hS]; exact hEsub, hEea, hEcard, hEline⟩

end CFSG.ClassicalGroups.Unitary
