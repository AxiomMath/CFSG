module

public import CFSG.RankThree.PartOne.KC.OrthogonalComponentFacts

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

open Polynomial Module QuadraticMap CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.Open

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ} {Bb : Subgroup ↥(orthDerived Q)}

@[expose] def quadKer (x : V ≃ₗ[F] V) (t : F) : Submodule F V :=
  LinearMap.ker (x.toLinearMap ∘ₗ x.toLinearMap + t • x.toLinearMap + LinearMap.id)

theorem mem_quadKer_iff {x : V ≃ₗ[F] V} {t : F} {v : V} :
    v ∈ quadKer x t ↔ x (x v) + t • x v + v = 0 := by
  simp [quadKer, LinearMap.mem_ker]

theorem apply_comm_of_isElemAbelian (hBb : IsElemAbelian p Bb) {b c : ↥(orthDerived Q)} (hb : b ∈ Bb)
    (hc : c ∈ Bb) (v : V) :
    (b : V ≃ₗ[F] V) ((c : V ≃ₗ[F] V) v) = (c : V ≃ₗ[F] V) ((b : V ≃ₗ[F] V) v) := by
  have hcomm : (⟨b, hb⟩ : ↥Bb) * ⟨c, hc⟩ = ⟨c, hc⟩ * ⟨b, hb⟩ := hBb.1.is_comm.comm _ _
  exact congrArg (fun z : ↥Bb => ((z : ↥(orthDerived Q)) : V ≃ₗ[F] V) v) hcomm

private theorem polar_eq_zero_of_eigen_aux1 {x : V ≃ₗ[F] V} {t : F}
    (ht : ∀ c : F, c * c + t * c + 1 ≠ 0) {w : V} (hw : w ∈ quadKer x t) (hxw : x w = w) :
    w = 0 := by
  have h0 := mem_quadKer_iff.1 hw
  rw [hxw, hxw] at h0
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact ht 1 (by simpa [one_add_one_eq_two] using h2)
  have h3 : w + w = 0 := by rw [← two_smul F w, h2, zero_smul]
  have h4 : t • w = (w + t • w + w) - (w + w) := by abel
  rw [h0, h3, sub_zero] at h4
  exact (smul_eq_zero.1 h4).resolve_left ht0

private theorem polar_eq_zero_of_eigen_aux2 (hBb : IsElemAbelian p Bb) {b g : ↥(orthDerived Q)}
    (hb : b ∈ Bb) (hg : g ∈ Bb) (n : ℕ) (x : V) :
    (b : V ≃ₗ[F] V) (((g : V ≃ₗ[F] V) ^ n) x) =
      ((g : V ≃ₗ[F] V) ^ n) ((b : V ≃ₗ[F] V) x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ', LinearEquiv.mul_apply,
      apply_comm_of_isElemAbelian hBb hb hg (((g : V ≃ₗ[F] V) ^ n) x), ih x]

private theorem polar_eq_zero_of_eigen_aux3 (e : V ≃ₗ[F] V) (n : ℕ) :
    ((e ^ n : V ≃ₗ[F] V) : V →ₗ[F] V) = (e : V →ₗ[F] V) ^ n :=
  map_pow (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := F) (M := V)) e n

private theorem polar_eq_zero_of_eigen_aux8 {g : ↥(orthDerived Q)} {t : F} {y : V}
    (hy : y ∈ quadKer (g : V ≃ₗ[F] V) t) {k : ℕ} :
    (∑ j ∈ Finset.range p, ((((g : V ≃ₗ[F] V) ^ k) ^ j : V ≃ₗ[F] V)) y) ∈
      quadKer (g : V ≃ₗ[F] V) t := by
  have hGstab : ∀ u ∈ quadKer (g : V ≃ₗ[F] V) t,
      (g : V ≃ₗ[F] V) u ∈ quadKer (g : V ≃ₗ[F] V) t := by
    intro u hu
    rw [mem_quadKer_iff] at hu ⊢
    have h := congrArg (g : V ≃ₗ[F] V) hu
    simpa only [map_add, map_smul, map_zero] using h
  have hGpow_mem : ∀ n : ℕ, ((g : V ≃ₗ[F] V) ^ n) y ∈ quadKer (g : V ≃ₗ[F] V) t := by
    intro n
    induction n with
    | zero => simpa using hy
    | succ n ih => rw [pow_succ', LinearEquiv.mul_apply]; exact hGstab _ ih
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [← pow_mul]
  exact hGpow_mem (k * j)

private theorem polar_eq_zero_of_eigen_aux9 (hp : p.Prime) {g : ↥(orthDerived Q)}
    (hGp : (g : V ≃ₗ[F] V) ^ p = 1) {y : V} {k : ℕ} (hpk : ¬ p ∣ k) :
    (g : V ≃ₗ[F] V) (∑ j ∈ Finset.range p, ((((g : V ≃ₗ[F] V) ^ k) ^ j : V ≃ₗ[F] V)) y) =
      ∑ j ∈ Finset.range p, ((((g : V ≃ₗ[F] V) ^ k) ^ j : V ≃ₗ[F] V)) y := by
  set rho : V ≃ₗ[F] V := (g : V ≃ₗ[F] V) ^ k with hrhodef
  have hρp : rho ^ p = 1 := by
    rw [hrhodef, ← pow_mul, mul_comm k p, pow_mul, hGp, one_pow]
  have hSfix : rho (∑ j ∈ Finset.range p, ((rho ^ j : V ≃ₗ[F] V)) y) =
      ∑ j ∈ Finset.range p, ((rho ^ j : V ≃ₗ[F] V)) y := by
    set S : V →ₗ[F] V := (∑ j ∈ Finset.range p, (rho : V →ₗ[F] V) ^ j) with hSdef
    have hSS : (rho : V →ₗ[F] V) * S = S := by
      have h : ((rho : V →ₗ[F] V) - 1) * S = 0 := by
        rw [hSdef, mul_geom_sum, ← polar_eq_zero_of_eigen_aux3 rho p, hρp,
          show ((1 : V ≃ₗ[F] V) : V →ₗ[F] V) = 1 by rfl, sub_self]
      rw [sub_mul, one_mul, sub_eq_zero] at h
      exact h
    have hSS' : (rho : V →ₗ[F] V) (S y) = S y := by
      have := congrArg (fun f : V →ₗ[F] V => f y) hSS
      rw [Module.End.mul_apply] at this
      exact this
    have hSy : S y = ∑ j ∈ Finset.range p, ((rho ^ j : V ≃ₗ[F] V)) y := by
      rw [hSdef, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← polar_eq_zero_of_eigen_aux3 rho j]
      rfl
    rw [← hSy]
    exact hSS'
  obtain ⟨k', hk'lt, hk'mod⟩ :=
    Nat.exists_mul_mod_eq_one_of_coprime (((hp.coprime_iff_not_dvd).2 hpk).symm) hp.one_lt
  have hG_eq : (g : V ≃ₗ[F] V) = rho ^ k' := by
    rw [hrhodef, ← pow_mul, pow_eq_pow_mod (k * k') hGp, hk'mod, pow_one]
  rw [hG_eq]
  have hfix : ∀ n : ℕ, ((rho ^ n : V ≃ₗ[F] V))
      (∑ j ∈ Finset.range p, ((rho ^ j : V ≃ₗ[F] V)) y) =
      ∑ j ∈ Finset.range p, ((rho ^ j : V ≃ₗ[F] V)) y := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ, LinearEquiv.mul_apply, hSfix, ih]
  exact hfix k'

private theorem exists_eigencomponents_aux1 {M : Type*} [AddCommMonoid M] (f : ℕ → M) {p : ℕ}
    (hp : 0 < p) (hf : f p = f 0) :
    ∑ k ∈ Finset.range p, f (k + 1) = ∑ k ∈ Finset.range p, f k := by
  rw [show p = (p - 1) + 1 by omega, Finset.sum_range_succ, Finset.sum_range_succ']
  rw [show (p - 1) + 1 = p by omega, hf]

private theorem exists_eigencomponents_aux2 {M : Type*} [AddCommMonoid M] (f : ℕ → M) {p : ℕ}
    (hp : 0 < p) (hf : f p = f 0) :
    ∑ m ∈ Finset.range p, f (p - m) = ∑ m ∈ Finset.range p, f m := by
  have h1 : ∑ m ∈ Finset.range p, f (p - m) = ∑ m ∈ Finset.range p, f ((p - 1 - m) + 1) := by
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_range] at hm
    congr 1
    omega
  rw [h1, Finset.sum_range_reflect (fun t => f (t + 1)) p]
  exact exists_eigencomponents_aux1 f hp hf

private theorem exists_eigencomponents_aux3 (hp : p.Prime) {g : ↥(orthDerived Q)}
    (hGp : (g : V ≃ₗ[F] V) ^ p = 1) {t : F} (ht : ∀ c : F, c * c + t * c + 1 ≠ 0) {y : V}
    (hy : y ∈ quadKer (g : V ≃ₗ[F] V) t) {k : ℕ} (hpk : ¬ p ∣ k) :
    (∑ m ∈ Finset.range p, (((g : V ≃ₗ[F] V) ^ k) ^ m) y) = 0 :=
  polar_eq_zero_of_eigen_aux1 ht (polar_eq_zero_of_eigen_aux8 (k := k) hy)
    (polar_eq_zero_of_eigen_aux9 (k := k) hp hGp hpk)

private theorem exists_eigencomponents_aux4 (hBb : IsElemAbelian p Bb) {g b : ↥(orthDerived Q)}
    (hg : g ∈ Bb) (hb : b ∈ Bb) (hGp : (g : V ≃ₗ[F] V) ^ p = 1)
    (hBp : (b : V ≃ₗ[F] V) ^ p = 1) (hp : 0 < p) {m : Fin p} {v : V} :
    (b : V ≃ₗ[F] V) ((p : F)⁻¹ • ∑ k ∈ Finset.range p,
        (((g : V ≃ₗ[F] V) ^ ((p - (m : ℕ)) * k)) (((b : V ≃ₗ[F] V) ^ k) v)))
      = ((g : V ≃ₗ[F] V) ^ (m : ℕ)) ((p : F)⁻¹ • ∑ k ∈ Finset.range p,
        (((g : V ≃ₗ[F] V) ^ ((p - (m : ℕ)) * k)) (((b : V ≃ₗ[F] V) ^ k) v))) := by
  set G : V ≃ₗ[F] V := (g : V ≃ₗ[F] V) with hGdef
  set B : V ≃ₗ[F] V := (b : V ≃ₗ[F] V) with hBdef
  have hGp' : G ^ p = 1 := by rw [hGdef]; exact hGp
  have hBp' : B ^ p = 1 := by rw [hBdef]; exact hBp
  have hterm (k : ℕ) : B ((G ^ ((p - (m : ℕ)) * k)) ((B ^ k) v))
      = (G ^ (m : ℕ)) ((G ^ ((p - (m : ℕ)) * (k + 1))) ((B ^ (k + 1)) v)) := by
    rw [polar_eq_zero_of_eigen_aux2 hBb hb hg ((p - (m : ℕ)) * k) ((B ^ k) v)]
    rw [show B ((B ^ k) v) = (B ^ (k + 1)) v by rw [pow_succ', LinearEquiv.mul_apply]]
    have hcoe : G ^ ((p - (m : ℕ)) * k) = G ^ (m : ℕ) * G ^ ((p - (m : ℕ)) * (k + 1)) := by
      rw [← pow_add]
      have harith : (m : ℕ) + (p - (m : ℕ)) * (k + 1) = p + (p - (m : ℕ)) * k := by
        rw [Nat.mul_succ]
        have hm : (m : ℕ) + (p - (m : ℕ)) = p := Nat.add_sub_cancel' (le_of_lt m.isLt)
        omega
      rw [harith, pow_add, hGp', one_mul]
    rw [hcoe, LinearEquiv.mul_apply]
  have hshift : ∑ k ∈ Finset.range p,
        (G ^ (m : ℕ)) ((G ^ ((p - (m : ℕ)) * (k + 1))) ((B ^ (k + 1)) v))
      = ∑ k ∈ Finset.range p, (G ^ (m : ℕ)) ((G ^ ((p - (m : ℕ)) * k)) ((B ^ k) v)) := by
    refine exists_eigencomponents_aux1
      (fun t => (G ^ (m : ℕ)) ((G ^ ((p - (m : ℕ)) * t)) ((B ^ t) v))) hp ?_
    have hL : (G ^ (m : ℕ)) ((G ^ ((p - (m : ℕ)) * p)) ((B ^ p) v)) = (G ^ (m : ℕ)) v := by
      congr 1
      rw [hBp', mul_comm (p - (m : ℕ)) p, pow_mul, hGp', one_pow]
      rfl
    have hR : (G ^ (m : ℕ)) ((G ^ ((p - (m : ℕ)) * 0)) ((B ^ 0) v)) = (G ^ (m : ℕ)) v := by
      rw [mul_zero, pow_zero, pow_zero]
      rfl
    rw [hL, hR]
  rw [map_smul B, map_sum B, map_smul (G ^ (m : ℕ)), map_sum (G ^ (m : ℕ))]
  congr 1
  rw [Finset.sum_congr rfl (fun k _ => hterm k), hshift]

private theorem exists_eigencomponents_aux5 (hBb : IsElemAbelian p Bb) {g b : ↥(orthDerived Q)}
    (hg : g ∈ Bb) (hb : b ∈ Bb) {t : F} {N : Submodule F V}
    (hN : ∀ b ∈ Bb, ∀ v ∈ N, (b : V ≃ₗ[F] V) v ∈ N) {v : V} (hvN : v ∈ N)
    (hvQ : v ∈ quadKer (g : V ≃ₗ[F] V) t) {m : Fin p} :
    (p : F)⁻¹ • ∑ k ∈ Finset.range p,
        (((g : V ≃ₗ[F] V) ^ ((p - (m : ℕ)) * k)) (((b : V ≃ₗ[F] V) ^ k) v)) ∈
      N ⊓ quadKer (g : V ≃ₗ[F] V) t := by
  have hBN : ∀ k, (((b : V ≃ₗ[F] V) ^ k) v) ∈ N := by
    intro k
    induction k with
    | zero => simpa using hvN
    | succ k ih => rw [pow_succ', LinearEquiv.mul_apply]; exact hN b hb _ ih
  have hGN : ∀ n, ∀ u ∈ N, (((g : V ≃ₗ[F] V) ^ n) u) ∈ N := by
    intro n
    induction n with
    | zero => intro u hu; simpa using hu
    | succ n ih => intro u hu; rw [pow_succ, LinearEquiv.mul_apply]; exact ih _ (hN g hg _ hu)
  have hGstab : ∀ u ∈ quadKer (g : V ≃ₗ[F] V) t,
      (g : V ≃ₗ[F] V) u ∈ quadKer (g : V ≃ₗ[F] V) t := by
    intro u hu
    rw [mem_quadKer_iff] at hu ⊢
    have h := congrArg (g : V ≃ₗ[F] V) hu
    simpa only [map_add, map_smul, map_zero] using h
  have hBstab : ∀ u ∈ quadKer (g : V ≃ₗ[F] V) t,
      (b : V ≃ₗ[F] V) u ∈ quadKer (g : V ≃ₗ[F] V) t := by
    intro u hu
    rw [mem_quadKer_iff] at hu ⊢
    have h := congrArg (b : V ≃ₗ[F] V) hu
    simp only [map_add, map_smul, map_zero] at h
    rw [apply_comm_of_isElemAbelian hBb hb hg ((g : V ≃ₗ[F] V) u),
      apply_comm_of_isElemAbelian hBb hb hg u] at h
    exact h
  have hGNQ : ∀ n, ∀ u ∈ quadKer (g : V ≃ₗ[F] V) t,
      (((g : V ≃ₗ[F] V) ^ n) u) ∈ quadKer (g : V ≃ₗ[F] V) t := by
    intro n
    induction n with
    | zero => intro u hu; simpa using hu
    | succ n ih => intro u hu; rw [pow_succ, LinearEquiv.mul_apply]; exact ih _ (hGstab _ hu)
  have hBNQ : ∀ k, (((b : V ≃ₗ[F] V) ^ k) v) ∈ quadKer (g : V ≃ₗ[F] V) t := by
    intro k
    induction k with
    | zero => simpa using hvQ
    | succ k ih => rw [pow_succ', LinearEquiv.mul_apply]; exact hBstab _ ih
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · exact N.smul_mem _ (Submodule.sum_mem _ fun k _ => hGN _ _ (hBN k))
  · exact (quadKer (g : V ≃ₗ[F] V) t).smul_mem _
      (Submodule.sum_mem _ fun k _ => hGNQ _ _ (hBNQ k))

private theorem exists_eigencomponents_aux6 (hBb : IsElemAbelian p Bb) {g b : ↥(orthDerived Q)}
    (hg : g ∈ Bb) (hb : b ∈ Bb) {c : ↥(orthDerived Q)} (hc : c ∈ Bb) {v : V}
    (hcv : (c : V ≃ₗ[F] V) v = v) {m : Fin p} :
    (c : V ≃ₗ[F] V) ((p : F)⁻¹ • ∑ k ∈ Finset.range p,
        (((g : V ≃ₗ[F] V) ^ ((p - (m : ℕ)) * k)) (((b : V ≃ₗ[F] V) ^ k) v)))
      = (p : F)⁻¹ • ∑ k ∈ Finset.range p,
        (((g : V ≃ₗ[F] V) ^ ((p - (m : ℕ)) * k)) (((b : V ≃ₗ[F] V) ^ k) v)) := by
  rw [map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [polar_eq_zero_of_eigen_aux2 hBb hc hg ((p - (m : ℕ)) * k) (((b : V ≃ₗ[F] V) ^ k) v),
    polar_eq_zero_of_eigen_aux2 hBb hc hb k v, hcv]

private theorem exists_eigencomponents_aux7 (hp : p.Prime) (hBb : IsElemAbelian p Bb)
    {g b : ↥(orthDerived Q)} (hg : g ∈ Bb) (hb : b ∈ Bb) (hGp : (g : V ≃ₗ[F] V) ^ p = 1)
    {t : F} (ht : ∀ c : F, c * c + t * c + 1 ≠ 0) {v : V}
    (hvQ : v ∈ quadKer (g : V ≃ₗ[F] V) t) {k : ℕ} (hk : k ∈ Finset.range p) (hk0 : k ≠ 0) :
    (∑ m ∈ Finset.range p,
        (((g : V ≃ₗ[F] V) ^ ((p - (m : ℕ)) * k)) (((b : V ≃ₗ[F] V) ^ k) v))) = 0 := by
  have hklt : k < p := Finset.mem_range.1 hk
  have hpk : ¬ p ∣ k := fun hdvd => hk0 (Nat.eq_zero_of_dvd_of_lt hdvd hklt)
  have hBstab : ∀ u ∈ quadKer (g : V ≃ₗ[F] V) t,
      (b : V ≃ₗ[F] V) u ∈ quadKer (g : V ≃ₗ[F] V) t := by
    intro u hu
    rw [mem_quadKer_iff] at hu ⊢
    have h := congrArg (b : V ≃ₗ[F] V) hu
    simp only [map_add, map_smul, map_zero] at h
    rw [apply_comm_of_isElemAbelian hBb hb hg ((g : V ≃ₗ[F] V) u),
      apply_comm_of_isElemAbelian hBb hb hg u] at h
    exact h
  have hBkQ_all : ∀ k : ℕ, (((b : V ≃ₗ[F] V) ^ k) v) ∈ quadKer (g : V ≃ₗ[F] V) t := by
    intro k
    induction k with
    | zero => simpa using hvQ
    | succ k ih => rw [pow_succ', LinearEquiv.mul_apply]; exact hBstab _ ih
  have hBkQ := hBkQ_all k
  have hGkp : (((g : V ≃ₗ[F] V) ^ k) : V ≃ₗ[F] V) ^ p = 1 := by
    rw [← pow_mul, mul_comm k p, pow_mul, hGp, one_pow]
  have hsub : ∑ m ∈ Finset.range p,
      (((g : V ≃ₗ[F] V) ^ ((p - (m : ℕ)) * k)) (((b : V ≃ₗ[F] V) ^ k) v))
      = ∑ m ∈ Finset.range p,
        ((((g : V ≃ₗ[F] V) ^ k) ^ (p - (m : ℕ))) (((b : V ≃ₗ[F] V) ^ k) v)) := by
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_comm (p - (m : ℕ)) k, ← pow_mul]
  rw [hsub]
  rw [exists_eigencomponents_aux2
    (fun t => (((g : V ≃ₗ[F] V) ^ k) ^ t) (((b : V ≃ₗ[F] V) ^ k) v)) hp.pos (by simp [hGkp])]
  exact exists_eigencomponents_aux3 hp hGp ht hBkQ hpk

private theorem exists_eigencomponents_aux8 (hp : p.Prime) (hBb : IsElemAbelian p Bb)
    {g b : ↥(orthDerived Q)} (hg : g ∈ Bb) (hb : b ∈ Bb) (hGp : (g : V ≃ₗ[F] V) ^ p = 1)
    {t : F} (ht : ∀ c : F, c * c + t * c + 1 ≠ 0) (hBp : (b : V ≃ₗ[F] V) ^ p = 1)
    (hpF : (p : F) ≠ 0) {v : V} (hvQ : v ∈ quadKer (g : V ≃ₗ[F] V) t) :
    (∑ m : Fin p, (p : F)⁻¹ • ∑ k ∈ Finset.range p,
        (((g : V ≃ₗ[F] V) ^ ((p - (m : ℕ)) * k)) (((b : V ≃ₗ[F] V) ^ k) v))) = v := by
  rw [← Finset.smul_sum]
  have hswap : ∑ m : Fin p, ∑ k ∈ Finset.range p,
      (((g : V ≃ₗ[F] V) ^ ((p - (m : ℕ)) * k)) (((b : V ≃ₗ[F] V) ^ k) v))
      = ∑ k ∈ Finset.range p, ∑ m : Fin p,
        (((g : V ≃ₗ[F] V) ^ ((p - (m : ℕ)) * k)) (((b : V ≃ₗ[F] V) ^ k) v)) := by
    rw [Finset.sum_comm]
  rw [hswap]
  have hsingle : (∑ k ∈ Finset.range p, ∑ m : Fin p,
      (((g : V ≃ₗ[F] V) ^ ((p - (m : ℕ)) * k)) (((b : V ≃ₗ[F] V) ^ k) v)))
      = (∑ m : Fin p,
      (((g : V ≃ₗ[F] V) ^ ((p - (m : ℕ)) * 0)) (((b : V ≃ₗ[F] V) ^ 0) v))) :=
    Finset.sum_eq_single 0
      (fun k hk hk0 => by
        rw [Fin.sum_univ_eq_sum_range
          (fun i : ℕ => (((g : V ≃ₗ[F] V) ^ ((p - i) * k)) (((b : V ≃ₗ[F] V) ^ k) v)))]
        exact exists_eigencomponents_aux7 hp hBb hg hb hGp ht hvQ hk hk0)
      (fun h0 => absurd (Finset.mem_range.2 hp.pos) h0)
  rw [hsingle]
  have hzero : ∀ m : Fin p,
      (((g : V ≃ₗ[F] V) ^ ((p - (m : ℕ)) * 0)) (((b : V ≃ₗ[F] V) ^ 0) v)) = v := by
    intro m
    rw [mul_zero, pow_zero, pow_zero]
    rfl
  rw [Finset.sum_congr rfl (fun m _ => hzero m), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, ← Nat.cast_smul_eq_nsmul F p v, smul_smul, inv_mul_cancel₀ hpF,
    one_smul]

theorem exists_eigencomponents (hp : p.Prime) (hp2 : p ≠ 2) (hBb : IsElemAbelian p Bb)
    {g : ↥(orthDerived Q)} (hg : g ∈ Bb) {t : F} (ht : ∀ c : F, c * c + t * c + 1 ≠ 0)
    {N : Submodule F V} (hN : ∀ b ∈ Bb, ∀ v ∈ N, (b : V ≃ₗ[F] V) v ∈ N)
    {b : ↥(orthDerived Q)} (hb : b ∈ Bb) {v : V} (hv : v ∈ N ⊓ quadKer (g : V ≃ₗ[F] V) t) :
    ∃ w : Fin p → V, (∀ m, w m ∈ N ⊓ quadKer (g : V ≃ₗ[F] V) t) ∧
      (∀ m : Fin p, (b : V ≃ₗ[F] V) (w m) = ((g : V ≃ₗ[F] V) ^ (m : ℕ)) (w m)) ∧ ∑ m, w m = v ∧
      ∀ c ∈ Bb, (c : V ≃ₗ[F] V) v = v → ∀ m, (c : V ≃ₗ[F] V) (w m) = w m := by
  have hBp : (b : V ≃ₗ[F] V) ^ p = 1 := by
    have := congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V)) (hBb.2 b hb)
    simpa using this
  have hGp : (g : V ≃ₗ[F] V) ^ p = 1 := by
    have := congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V)) (hBb.2 g hg)
    simpa using this
  have hpF : (p : F) ≠ 0 := by
    intro h
    have h2 : (2 : ℕ) ∣ p := (CharP.cast_eq_zero_iff F 2 p).mp h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2).symm
  refine ⟨fun m => (p : F)⁻¹ • ∑ k ∈ Finset.range p,
      (((g : V ≃ₗ[F] V) ^ ((p - (m : ℕ)) * k)) (((b : V ≃ₗ[F] V) ^ k) v)), ?_, ?_, ?_, ?_⟩
  · intro m
    exact exists_eigencomponents_aux5 hBb hg hb hN (Submodule.mem_inf.1 hv).1
      (Submodule.mem_inf.1 hv).2
  · intro m
    exact exists_eigencomponents_aux4 hBb hg hb hGp hBp hp.pos
  · exact exists_eigencomponents_aux8 hp hBb hg hb hGp ht hBp hpF (Submodule.mem_inf.1 hv).2
  · intro c hc hcv m
    exact exists_eigencomponents_aux6 hBb hg hb hc hcv

private theorem polar_eq_zero_of_eigen_aux4 {g : ↥(orthDerived Q)} {t : F}
    (ht : ∀ c : F, c * c + t * c + 1 ≠ 0) {x y : V}
    (hx : x ∈ quadKer (g : V ≃ₗ[F] V) t) (hp2eq : p = 2)
    (hGp : (g : V ≃ₗ[F] V) ^ p = 1) : QuadraticMap.polar Q x y = 0 := by
  subst hp2eq
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact ht 1 (by simpa [one_add_one_eq_two] using (CharTwo.two_eq_zero : (2 : F) = 0))
  have hGG : (g : V ≃ₗ[F] V) ((g : V ≃ₗ[F] V) x) = x := by
    rw [← LinearEquiv.mul_apply, ← pow_two, hGp]
    rfl
  have hxq := mem_quadKer_iff.1 hx
  rw [hGG] at hxq
  have hx2 : x + x = 0 := by rw [← two_smul F x, CharTwo.two_eq_zero, zero_smul]
  have htGx : t • ((g : V ≃ₗ[F] V) x) = 0 := by
    have h4 : t • ((g : V ≃ₗ[F] V) x) =
        (x + t • ((g : V ≃ₗ[F] V) x) + x) - (x + x) := by abel
    rw [hxq, hx2, sub_zero] at h4
    exact h4
  have hGx0 : (g : V ≃ₗ[F] V) x = 0 := (smul_eq_zero.1 htGx).resolve_left ht0
  have hx0 : x = 0 := by rw [← hGG, hGx0, map_zero]
  rw [hx0]
  simp

private theorem polar_eq_zero_of_eigen_aux5 (hp : p.Prime) {m m' : ℕ}
    (hmm' : ¬ m ≡ m' [MOD p]) : ¬ p ∣ m' + (p - 1) * m := by
  have h1 : ((p - 1 : ℕ) : ZMod p) = -1 := by
    rw [Nat.cast_sub hp.one_le, Nat.cast_one, ZMod.natCast_self, zero_sub]
  have hkz : ((m' + (p - 1) * m : ℕ) : ZMod p) = (m' : ZMod p) - (m : ZMod p) := by
    rw [Nat.cast_add, Nat.cast_mul, h1]
    ring
  have hne : (m : ZMod p) ≠ (m' : ZMod p) := fun h =>
    hmm' ((ZMod.natCast_eq_natCast_iff m m' p).mp h)
  intro hdvd
  have h0 : ((m' + (p - 1) * m : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff (m' + (p - 1) * m) p).2 hdvd
  rw [hkz] at h0
  exact hne (sub_eq_zero.mp h0).symm

private theorem polar_eq_zero_of_eigen_aux6 (hp : p.Prime) {g : ↥(orthDerived Q)}
    (hGp : (g : V ≃ₗ[F] V) ^ p = 1) {m m' : ℕ} :
    (g : V ≃ₗ[F] V) ^ m' =
      (g : V ≃ₗ[F] V) ^ m * (g : V ≃ₗ[F] V) ^ (m' + (p - 1) * m) := by
  have hmk : m + (m' + (p - 1) * m) = m' + p * m := by
    have hpm : (p - 1) * m + m = p * m := by
      nth_rewrite 2 [← one_mul m]
      rw [← Nat.add_mul, Nat.sub_add_cancel hp.one_le]
    omega
  calc (g : V ≃ₗ[F] V) ^ m'
      = (g : V ≃ₗ[F] V) ^ (m' + p * m) := by rw [pow_add, pow_mul, hGp, one_pow, mul_one]
    _ = (g : V ≃ₗ[F] V) ^ (m + (m' + (p - 1) * m)) := by rw [hmk]
    _ = (g : V ≃ₗ[F] V) ^ m * (g : V ≃ₗ[F] V) ^ (m' + (p - 1) * m) := by rw [pow_add]

private theorem polar_eq_zero_of_eigen_aux7 (hBb : IsElemAbelian p Bb) {g : ↥(orthDerived Q)}
    (hg : g ∈ Bb) {b : ↥(orthDerived Q)} (hb : b ∈ Bb)
    (hGO : (g : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hBO : (b : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {x y : V} {m m' : ℕ}
    (hGk : (g : V ≃ₗ[F] V) ^ m' =
      (g : V ≃ₗ[F] V) ^ m * (g : V ≃ₗ[F] V) ^ (m' + (p - 1) * m))
    (hbx : (b : V ≃ₗ[F] V) x = ((g : V ≃ₗ[F] V) ^ m) x)
    (hby : (b : V ≃ₗ[F] V) y = ((g : V ≃ₗ[F] V) ^ m') y) :
    ∀ j : ℕ, QuadraticMap.polar Q x ((((g : V ≃ₗ[F] V) ^ (m' + (p - 1) * m)) ^ j) y) =
      QuadraticMap.polar Q x y := by
  have hstep : ∀ z, (b : V ≃ₗ[F] V) z = ((g : V ≃ₗ[F] V) ^ m') z →
      QuadraticMap.polar Q x z =
        QuadraticMap.polar Q x (((g : V ≃ₗ[F] V) ^ (m' + (p - 1) * m)) z) := by
    intro z hz
    have h1 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hBO x z
    have h2 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup
      (Subgroup.pow_mem (TauCeti.QuadraticMap.orthogonalGroup Q) hGO m) x
      (((g : V ≃ₗ[F] V) ^ (m' + (p - 1) * m)) z)
    rw [hbx, hz, hGk, LinearEquiv.mul_apply] at h1
    exact h1.symm.trans h2
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have hz : (b : V ≃ₗ[F] V) ((((g : V ≃ₗ[F] V) ^ (m' + (p - 1) * m)) ^ j) y) =
        ((g : V ≃ₗ[F] V) ^ m') ((((g : V ≃ₗ[F] V) ^ (m' + (p - 1) * m)) ^ j) y) := by
      rw [← pow_mul, polar_eq_zero_of_eigen_aux2 hBb hb hg
        ((m' + (p - 1) * m) * j) y, hby,
        ← LinearEquiv.mul_apply, ← pow_add, ← LinearEquiv.mul_apply, ← pow_add,
        Nat.add_comm ((m' + (p - 1) * m) * j) m']
    have hs := hstep ((((g : V ≃ₗ[F] V) ^ (m' + (p - 1) * m)) ^ j) y) hz
    rw [pow_succ', LinearEquiv.mul_apply, ← hs, ih]

private theorem polar_eq_zero_of_eigen_aux10 (hp : p.Prime) (hp2ne : p ≠ 2)
    {rho : V ≃ₗ[F] V} {x y : V}
    (hW0 : (∑ j ∈ Finset.range p, ((rho ^ j : V ≃ₗ[F] V)) y) = 0)
    (hiter : ∀ j : ℕ, QuadraticMap.polar Q x (((rho ^ j : V ≃ₗ[F] V)) y) =
      QuadraticMap.polar Q x y) :
    QuadraticMap.polar Q x y = 0 := by
  have hw_sum : QuadraticMap.polar Q x (∑ j ∈ Finset.range p, ((rho ^ j : V ≃ₗ[F] V)) y) =
      ∑ j ∈ Finset.range p, QuadraticMap.polar Q x (((rho ^ j : V ≃ₗ[F] V)) y) := by
    rw [← QuadraticMap.polarBilin_apply_apply, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [QuadraticMap.polarBilin_apply_apply]
  have hpolar : (p : F) * QuadraticMap.polar Q x y = 0 := by
    have h4 : QuadraticMap.polar Q x (∑ j ∈ Finset.range p, ((rho ^ j : V ≃ₗ[F] V)) y) = 0 := by
      rw [hW0]; simp
    rw [hw_sum, Finset.sum_congr rfl (fun j _ => hiter j), Finset.sum_const,
      Finset.card_range, nsmul_eq_mul] at h4
    exact h4
  have hpF : (p : F) ≠ 0 := by
    intro h
    have h2 : (2 : ℕ) ∣ p := (CharP.cast_eq_zero_iff F 2 p).mp h
    exact hp2ne ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2).symm
  exact (mul_eq_zero.mp hpolar).resolve_left hpF

theorem polar_eq_zero_of_eigen (hp : p.Prime) (hBb : IsElemAbelian p Bb) {g : ↥(orthDerived Q)}
    (hg : g ∈ Bb) {t : F} (ht : ∀ c : F, c * c + t * c + 1 ≠ 0) {b : ↥(orthDerived Q)} (hb : b ∈ Bb)
    {x y : V} (hx : x ∈ quadKer (g : V ≃ₗ[F] V) t) (hy : y ∈ quadKer (g : V ≃ₗ[F] V) t)
    {m m' : ℕ} (hmm' : ¬ m ≡ m' [MOD p])
    (hbx : (b : V ≃ₗ[F] V) x = ((g : V ≃ₗ[F] V) ^ m) x)
    (hby : (b : V ≃ₗ[F] V) y = ((g : V ≃ₗ[F] V) ^ m') y) : QuadraticMap.polar Q x y = 0 := by
  haveI : Finite V := Module.finite_of_finite F
  have hGp : (g : V ≃ₗ[F] V) ^ p = 1 := by
    have := congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V)) (hBb.2 g hg)
    simpa using this
  rcases eq_or_ne p 2 with hp2eq | hp2ne
  · exact polar_eq_zero_of_eigen_aux4 ht hx hp2eq hGp
  have hGO : (g : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthDerived_le_orthogonalGroup g.2
  have hBO : (b : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthDerived_le_orthogonalGroup b.2
  have hGk := polar_eq_zero_of_eigen_aux6 hp hGp (m := m) (m' := m')
  have hiter := polar_eq_zero_of_eigen_aux7 hBb hg hb hGO hBO hGk hbx hby
  have hpk := polar_eq_zero_of_eigen_aux5 hp hmm'
  have hS0 : (∑ j ∈ Finset.range p,
      ((((g : V ≃ₗ[F] V) ^ (m' + (p - 1) * m)) ^ j : V ≃ₗ[F] V)) y) = 0 :=
    polar_eq_zero_of_eigen_aux1 ht
      (polar_eq_zero_of_eigen_aux8 (k := m' + (p - 1) * m) hy)
      (polar_eq_zero_of_eigen_aux9 (k := m' + (p - 1) * m) hp hGp hpk)
  exact polar_eq_zero_of_eigen_aux10 hp hp2ne hS0 hiter

private def exists_stab_max_vector_aux1 (Bb : Subgroup ↥(orthDerived Q)) (v : V) :
    Subgroup ↥(orthDerived Q) where
  carrier := {b | b ∈ Bb ∧ (b : V ≃ₗ[F] V) v = v}
  mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply, hb.2, ha.2]⟩
  one_mem' := ⟨one_mem _, rfl⟩
  inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by
    rw [Subgroup.coe_inv]
    exact (LinearEquiv.symm_apply_eq (a : V ≃ₗ[F] V)).2 ha.2.symm⟩

private lemma exists_stab_max_vector_aux2 {b : ↥(orthDerived Q)} {v : V} :
    b ∈ exists_stab_max_vector_aux1 Bb v ↔ b ∈ Bb ∧ (b : V ≃ₗ[F] V) v = v := Iff.rfl

private theorem exists_stab_max_vector_aux3 (hp : p.Prime) (hBb : IsElemAbelian p Bb)
    {g b : ↥(orthDerived Q)} (hg : g ∈ Bb) (hb : b ∈ Bb) {t : F}
    (ht : ∀ c : F, c * c + t * c + 1 ≠ 0) {N : Submodule F V}
    (hN : ∀ b ∈ Bb, ∀ v ∈ N, (b : V ≃ₗ[F] V) v ∈ N) {v : V} (hvQ : Q v ≠ 0)
    {w : Fin p → V} (hwmem : ∀ m, w m ∈ N ⊓ quadKer (g : V ≃ₗ[F] V) t)
    (hweig : ∀ m : Fin p, (b : V ≃ₗ[F] V) (w m) = ((g : V ≃ₗ[F] V) ^ (m : ℕ)) (w m))
    (hwsum : ∑ m, w m = v)
    (hwfix : ∀ c ∈ Bb, (c : V ≃ₗ[F] V) v = v → ∀ m, (c : V ≃ₗ[F] V) (w m) = w m)
    (hmax' : ∀ q, q ∈ N ⊓ quadKer (g : V ≃ₗ[F] V) t → Q q ≠ 0 →
      Nat.card (exists_stab_max_vector_aux1 Bb q) ≤
        Nat.card (exists_stab_max_vector_aux1 Bb v)) :
    ∃ m : Fin p, Q (w m) ≠ 0 ∧
      exists_stab_max_vector_aux1 Bb v = exists_stab_max_vector_aux1 Bb (w m) := by
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite ↥(orthDerived Q) :=
    Finite.of_injective (fun z : ↥(orthDerived Q) => ((z : V ≃ₗ[F] V) : V → V))
      fun a b h => Subtype.ext (LinearEquiv.ext (congrFun h))
  have horth : ∀ i j : Fin p, i ≠ j → QuadraticMap.polar Q (w i) (w j) = 0 := fun i j hij =>
    polar_eq_zero_of_eigen hp hBb hg ht hb (hwmem i).2 (hwmem j).2
      (by
        intro hmod
        exact hij (Fin.ext (by
          change (i : ℕ) % p = (j : ℕ) % p at hmod
          rwa [Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] at hmod)))
      (hweig i) (hweig j)
  have hQsum : Q v = ∑ m : Fin p, Q (w m) := by
    have hzero : ∑ ij ∈ (Finset.univ : Finset (Fin p)).sym2 with ¬ ij.IsDiag,
        QuadraticMap.polarSym2 Q (Sym2.map w ij) = 0 := by
      refine Finset.sum_eq_zero fun ij hij => ?_
      rw [Finset.mem_filter] at hij
      obtain ⟨-, hndiag⟩ := hij
      induction ij using Sym2.ind with
      | _ a b =>
        rw [Sym2.map_mk, QuadraticMap.polarSym2_sym2Mk]
        exact horth a b fun hab => hndiag (Sym2.mk_isDiag_iff.mpr hab)
    rw [← hwsum, QuadraticMap.map_sum, hzero, add_zero]
  obtain ⟨m, -, hmQ⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [← hQsum]; exact hvQ)
  refine ⟨m, hmQ, Subgroup.eq_of_le_of_card_ge ?_ (hmax' (w m) (hwmem m) hmQ)⟩
  intro c hc
  rw [exists_stab_max_vector_aux2] at hc ⊢
  exact ⟨hc.1, hwfix c hc.1 hc.2 m⟩

private theorem exists_stab_max_vector_aux4 (hBb : IsElemAbelian p Bb) {g b : ↥(orthDerived Q)}
    (hb : b ∈ Bb) (hg : g ∈ Bb) (hGp : (g : V ≃ₗ[F] V) ^ p = 1) {v : V} {m : Fin p}
    {w : Fin p → V}
    (hweig : (b : V ≃ₗ[F] V) (w m) = ((g : V ≃ₗ[F] V) ^ (m : ℕ)) (w m))
    (heq : exists_stab_max_vector_aux1 Bb v = exists_stab_max_vector_aux1 Bb (w m)) :
    (b : V ≃ₗ[F] V) v = ((g : V ≃ₗ[F] V) ^ (m : ℕ)) v := by
  let mm : ℕ := (m : ℕ)
  have hmm_lt : mm < p := m.isLt
  let c : ↥(orthDerived Q) := b * g ^ (p - mm)
  have hcB : c ∈ Bb := Bb.mul_mem hb (Bb.pow_mem hg _)
  have hcoe_c : (c : V ≃ₗ[F] V) =
      (b : V ≃ₗ[F] V) * ((g : V ≃ₗ[F] V) ^ (p - mm)) := by
    simp only [c, Subgroup.coe_mul, Subgroup.coe_pow]
  have hcfix_w : (c : V ≃ₗ[F] V) (w m) = w m := by
    rw [hcoe_c, LinearEquiv.mul_apply,
      polar_eq_zero_of_eigen_aux2 hBb hb hg (p - mm) (w m), hweig,
      ← LinearEquiv.mul_apply, ← pow_add, Nat.sub_add_cancel hmm_lt.le, hGp]
    rfl
  have hcstab : c ∈ exists_stab_max_vector_aux1 Bb (w m) := by
    rw [exists_stab_max_vector_aux2]; exact ⟨hcB, hcfix_w⟩
  have hcstabv : c ∈ exists_stab_max_vector_aux1 Bb v := heq.symm ▸ hcstab
  have hcv : (c : V ≃ₗ[F] V) v = v := (exists_stab_max_vector_aux2.mp hcstabv).2
  have hcv' : (b : V ≃ₗ[F] V) (((g : V ≃ₗ[F] V) ^ (p - mm)) v) = v := by
    rw [hcoe_c, LinearEquiv.mul_apply] at hcv
    exact hcv
  have hGy : ((g : V ≃ₗ[F] V) ^ mm) (((g : V ≃ₗ[F] V) ^ (p - mm)) v) = v := by
    rw [← LinearEquiv.mul_apply, ← pow_add, Nat.add_sub_cancel' hmm_lt.le, hGp]
    rfl
  have h1 : (b : V ≃ₗ[F] V) (((g : V ≃ₗ[F] V) ^ mm) (((g : V ≃ₗ[F] V) ^ (p - mm)) v)) =
      ((g : V ≃ₗ[F] V) ^ mm) ((b : V ≃ₗ[F] V) (((g : V ≃ₗ[F] V) ^ (p - mm)) v)) :=
    polar_eq_zero_of_eigen_aux2 hBb hb hg mm (((g : V ≃ₗ[F] V) ^ (p - mm)) v)
  rw [hcv', hGy] at h1
  exact h1

theorem exists_stab_max_vector (hp : p.Prime) (hp2 : p ≠ 2) (hBb : IsElemAbelian p Bb)
    {g : ↥(orthDerived Q)} (hg : g ∈ Bb) {t : F} (ht : ∀ c : F, c * c + t * c + 1 ≠ 0)
    {N : Submodule F V} (hN : ∀ b ∈ Bb, ∀ v ∈ N, (b : V ≃ₗ[F] V) v ∈ N)
    (hne : ∃ v ∈ N ⊓ quadKer (g : V ≃ₗ[F] V) t, Q v ≠ 0) :
    ∃ v ∈ N ⊓ quadKer (g : V ≃ₗ[F] V) t, Q v ≠ 0 ∧
      ∀ b ∈ Bb, ∃ m : ℕ, (b : V ≃ₗ[F] V) v = ((g : V ≃ₗ[F] V) ^ m) v := by
  classical
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite ↥(orthDerived Q) :=
    Finite.of_injective (fun z : ↥(orthDerived Q) => ((z : V ≃ₗ[F] V) : V → V))
      fun a b h => Subtype.ext (LinearEquiv.ext (congrFun h))
  have hGp : (g : V ≃ₗ[F] V) ^ p = 1 := by
    have := congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V)) (hBb.2 g hg)
    simpa using this
  let S : Set V := {v | v ∈ N ⊓ quadKer (g : V ≃ₗ[F] V) t ∧ Q v ≠ 0}
  obtain ⟨v₀, hv₀⟩ := hne
  have hSne : S.Nonempty := ⟨v₀, hv₀⟩
  obtain ⟨v, hmax⟩ := Set.Finite.exists_maximalFor
    (fun q => Nat.card (exists_stab_max_vector_aux1 Bb q)) S (Set.toFinite S) hSne
  have hvS : v ∈ S := hmax.1
  have hmax' : ∀ q ∈ S, Nat.card (exists_stab_max_vector_aux1 Bb q) ≤
      Nat.card (exists_stab_max_vector_aux1 Bb v) := fun q hq =>
    (le_total _ _).elim id fun h => hmax.2 hq h
  refine ⟨v, hvS.1, hvS.2, ?_⟩
  intro b hb
  obtain ⟨w, hwmem, hweig, hwsum, hwfix⟩ :=
    exists_eigencomponents hp hp2 hBb hg ht hN hb hvS.1
  obtain ⟨m, -, heq⟩ := exists_stab_max_vector_aux3 hp hBb hg hb ht hN hvS.2 hwmem hweig hwsum
    hwfix fun q hq hQ => hmax' q ⟨hq, hQ⟩
  exact ⟨(m : ℕ), exists_stab_max_vector_aux4 hBb hb hg hGp (hweig m) heq⟩

end CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

end
