module

public import CFSG.LocalAnalysis.AGLEmbedding.CoverCoreAux

public section

namespace CFSG.AGLEmbedding

open scoped commutatorElement

open CoverCore

section Span

variable {X : Type} [Group X] {p : ℕ} (D : ModuleSpec X p)

theorem ModuleSpec.card_span (hp : p.Prime) : Nat.card D.span = p ^ D.n := by
  have := Fact.mk hp
  let e : (Fin D.n → ZMod p) ≃ D.span := Equiv.ofBijective (fun c => ⟨D.elt c, D.elt_mem c⟩)
    ⟨fun c d h => D.elt_injective (congrArg Subtype.val h), fun u => by
      obtain ⟨c, hc⟩ := D.exists_elt u.2
      exact ⟨c, Subtype.ext hc⟩⟩
  rw [← Nat.card_congr e, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
    Fintype.card_fin]

end Span

variable {K X : Type} [Group K] [Group X] {p : ℕ} (D : ModuleSpec X p) (π : K →* X)

theorem ModuleSpec.card_comap [Finite K] (hp : p.Prime) (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.center K) :
    Nat.card (D.span.comap π) = Nat.card (Subgroup.center K) * p ^ D.n := by
  have : Finite X := Finite.of_surjective π hπ
  have h1 := Subgroup.card_mul_index (D.span.comap π)
  rw [Subgroup.index_comap_of_surjective _ hπ] at h1
  have h2 := Subgroup.card_mul_index D.span
  have h3 : Nat.card K = Nat.card X * Nat.card (Subgroup.center K) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv, hker]
  have hi : D.span.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rw [← D.card_span hp]
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hi)
  rw [h1, h3, ← h2]
  ring

theorem ModuleSpec.commutator_mem_center (hker : π.ker = Subgroup.center K) {x y : K}
    (hx : x ∈ D.span.comap π) (hy : y ∈ D.span.comap π) : ⁅x, y⁆ ∈ Subgroup.center K := by
  rw [← hker, MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact D.mul_comm_of_mem hx hy

theorem ModuleSpec.pow_mem_center (hker : π.ker = Subgroup.center K) {x : K}
    (hx : x ∈ D.span.comap π) : x ^ p ∈ Subgroup.center K := by
  rw [← hker, MonoidHom.mem_ker, map_pow]
  exact D.pow_eq_one_of_mem hx

theorem ModuleSpec.commutator_pow_eq_one (hker : π.ker = Subgroup.center K) {x y : K}
    (hx : x ∈ D.span.comap π) (hy : y ∈ D.span.comap π) : ⁅x, y⁆ ^ p = 1 := by
  have hc := D.commutator_mem_center π hker hx hy
  rw [(show Commute x ⁅x, y⁆ from Subgroup.mem_center_iff.mp hc x).commutatorElement_pow_left,
    commutatorElement_eq_one_iff_mul_comm]
  exact (Subgroup.mem_center_iff.mp (D.pow_mem_center π hker hx) y).symm

theorem ModuleSpec.surjInv_mem (hπ : Function.Surjective π) {u : X} (hu : u ∈ D.span) :
    Function.surjInv hπ u ∈ D.span.comap π := by
  rw [Subgroup.mem_comap, Function.surjInv_eq hπ]
  exact hu

theorem ModuleSpec.coverComm_mem_center (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.center K) {u v : X} (hu : u ∈ D.span) (hv : v ∈ D.span) :
    coverComm π hπ u v ∈ Subgroup.center K :=
  D.commutator_mem_center π hker (D.surjInv_mem π hπ hu) (D.surjInv_mem π hπ hv)

theorem ModuleSpec.coverComm_pow (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.center K) {u v : X} (hu : u ∈ D.span) (hv : v ∈ D.span) :
    coverComm π hπ u v ^ p = 1 :=
  D.commutator_pow_eq_one π hker (D.surjInv_mem π hπ hu) (D.surjInv_mem π hπ hv)

theorem ModuleSpec.coverComm_mul_left (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.center K) {u u' v : X} (hu' : u' ∈ D.span) (hv : v ∈ D.span) :
    coverComm π hπ (u * u') v = coverComm π hπ u v * coverComm π hπ u' v := by
  obtain ⟨x, rfl⟩ := hπ u
  obtain ⟨x', rfl⟩ := hπ u'
  obtain ⟨y, rfl⟩ := hπ v
  have hc := D.commutator_mem_center π hker hu' hv
  rw [← map_mul, ← commutatorElement_eq_coverComm π hπ hker,
    ← commutatorElement_eq_coverComm π hπ hker, ← commutatorElement_eq_coverComm π hπ hker,
    commutatorElement_mul_left_eq_conj_mul, Subgroup.mem_center_iff.mp hc x,
    mul_inv_cancel_right]
  exact (Subgroup.mem_center_iff.mp hc _).symm

theorem ModuleSpec.coverComm_mul_right (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.center K) {u v v' : X} (hu : u ∈ D.span) (hv : v ∈ D.span)
    (hv' : v' ∈ D.span) :
    coverComm π hπ u (v * v') = coverComm π hπ u v * coverComm π hπ u v' := by
  rw [coverComm_swap π hπ (v * v') u, D.coverComm_mul_left π hπ hker hv' hu, mul_inv_rev,
    ← coverComm_swap π hπ v' u, ← coverComm_swap π hπ v u]
  exact Subgroup.mem_center_iff.mp (D.coverComm_mem_center π hπ hker hu hv) _

theorem ModuleSpec.coverComm_conj (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.center K) (g : X) {u v : X} (hu : u ∈ D.span) (hv : v ∈ D.span) :
    coverComm π hπ (g * u * g⁻¹) (g * v * g⁻¹) = coverComm π hπ u v := by
  obtain ⟨k, rfl⟩ := hπ g
  obtain ⟨x, rfl⟩ := hπ u
  obtain ⟨y, rfl⟩ := hπ v
  have hc := D.commutator_mem_center π hker hu hv
  simp only [← map_inv, ← map_mul]
  rw [← commutatorElement_eq_coverComm π hπ hker, ← commutatorElement_eq_coverComm π hπ hker,
    ← conjugate_commutatorElement, Subgroup.mem_center_iff.mp hc k, mul_inv_cancel_right]

theorem ModuleSpec.exists_commForm (hp : p.Prime) (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.center K) (hZc : IsCyclic (Subgroup.center K)) :
    ∃ (f : K → ZMod p) (B : Matrix (Fin D.n) (Fin D.n) (ZMod p)),
      (∀ z, z ∈ Subgroup.center K → z ^ p = 1 → f z = 0 → z = 1) ∧ f 1 = 0 ∧
      B.transpose = -B ∧ (∀ j, (D.M j).transpose * B * D.M j = B) ∧
      ∀ x ∈ D.span.comap π, ∀ y ∈ D.span.comap π, ∀ c d, π x = D.elt c → π y = D.elt d →
        f ⁅x, y⁆ = ∑ i, c i * ∑ k, d k * B i k := by
  have := Fact.mk hp
  obtain ⟨f, hfmul, hfinj⟩ := exists_log_omega (K := K) hp hZc
  have hf1 : f 1 = 0 := by
    have h0 := hfmul 1 1 (one_mem _) (one_pow p) (one_mem _) (one_pow p)
    rwa [mul_one, left_eq_add] at h0
  have hfinv : ∀ {u v : X}, u ∈ D.span → v ∈ D.span →
      f (coverComm π hπ u v)⁻¹ = -f (coverComm π hπ u v) := by
    intro u v hu hv
    have h1 := D.coverComm_mem_center π hπ hker hu hv
    have h2 := D.coverComm_pow π hπ hker hu hv
    have h := hfmul _ _ (inv_mem h1) (by rw [inv_pow, h2, inv_one]) h1 h2
    rw [inv_mul_cancel, hf1] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  let b : (Fin D.n → ZMod p) → (Fin D.n → ZMod p) → ZMod p :=
    fun c d => f (coverComm π hπ (D.elt c) (D.elt d))
  have hb1 : ∀ c c' d, b (c + c') d = b c d + b c' d := fun c c' d => by
    simp only [b, D.elt_add, D.coverComm_mul_left π hπ hker (D.elt_mem c') (D.elt_mem d)]
    exact hfmul _ _ (D.coverComm_mem_center π hπ hker (D.elt_mem c) (D.elt_mem d))
      (D.coverComm_pow π hπ hker (D.elt_mem c) (D.elt_mem d))
      (D.coverComm_mem_center π hπ hker (D.elt_mem c') (D.elt_mem d))
      (D.coverComm_pow π hπ hker (D.elt_mem c') (D.elt_mem d))
  have hb2 : ∀ c d d', b c (d + d') = b c d + b c d' := fun c d d' => by
    simp only [b, D.elt_add, D.coverComm_mul_right π hπ hker (D.elt_mem c) (D.elt_mem d)
      (D.elt_mem d')]
    exact hfmul _ _ (D.coverComm_mem_center π hπ hker (D.elt_mem c) (D.elt_mem d))
      (D.coverComm_pow π hπ hker (D.elt_mem c) (D.elt_mem d))
      (D.coverComm_mem_center π hπ hker (D.elt_mem c) (D.elt_mem d'))
      (D.coverComm_pow π hπ hker (D.elt_mem c) (D.elt_mem d'))
  let B : Matrix (Fin D.n) (Fin D.n) (ZMod p) :=
    Matrix.of fun i k => b (Pi.single i 1) (Pi.single k 1)
  have hexp : ∀ c d, b c d = ∑ i, c i * ∑ k, d k * B i k := fun c d => by
    rw [eq_sum_of_map_add (F := fun c => b c d) (fun c c' => hb1 c c' d) c]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [eq_sum_of_map_add (F := b (Pi.single i 1)) (hb2 (Pi.single i 1)) d]
    rfl
  refine ⟨f, B, hfinj, hf1, ?_, fun j => ?_, ?_⟩
  · ext i k
    simp only [B, b, Matrix.transpose_apply, Matrix.neg_apply, Matrix.of_apply]
    rw [coverComm_swap π hπ, hfinv (D.elt_mem _) (D.elt_mem _)]
    rfl
  · ext i k
    have h1 : B i k = b (fun l => D.M j l i) (fun l => D.M j l k) := by
      simp only [B, b, Matrix.of_apply, D.elt_col, D.elt_single,
        D.coverComm_conj π hπ hker _ (D.a_mem_span i) (D.a_mem_span k)]
    rw [h1, hexp]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  · intro x _ y _ c d hxc hyd
    rw [commutatorElement_eq_coverComm π hπ hker, hxc, hyd]
    exact hexp c d

theorem ModuleSpec.commute_of_form_eq_zero (hp : p.Prime) (hker : π.ker = Subgroup.center K)
    {f : K → ZMod p} (hfinj : ∀ z, z ∈ Subgroup.center K → z ^ p = 1 → f z = 0 → z = 1)
    (hform : ∀ x ∈ D.span.comap π, ∀ y ∈ D.span.comap π, ∀ c d, π x = D.elt c →
      π y = D.elt d → f ⁅x, y⁆ = ∑ i, c i * ∑ k, d k * (0 : Matrix (Fin D.n) (Fin D.n)
        (ZMod p)) i k) :
    ∀ x ∈ D.span.comap π, ∀ y ∈ D.span.comap π, x * y = y * x := by
  have := Fact.mk hp
  intro x hx y hy
  obtain ⟨c, hc⟩ := D.exists_elt hx
  obtain ⟨d, hd⟩ := D.exists_elt hy
  rw [← commutatorElement_eq_one_iff_mul_comm]
  refine hfinj _ (D.commutator_mem_center π hker hx hy) (D.commutator_pow_eq_one π hker hx hy) ?_
  rw [hform x hx y hy c d hc.symm hd.symm]
  simp

theorem ModuleSpec.commute_of_noAlt (hp : p.Prime) (_hp2 : p ≠ 2) (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.center K) (_hZp : IsPGroup p (Subgroup.center K))
    (hZc : IsCyclic (Subgroup.center K)) (hD : D.NoAlt) :
    ∀ x ∈ D.span.comap π, ∀ y ∈ D.span.comap π, x * y = y * x := by
  obtain ⟨f, B, hfinj, -, hBt, hBM, hform⟩ := D.exists_commForm π hp hπ hker hZc
  obtain rfl : B = 0 := hD B hBt hBM
  exact D.commute_of_form_eq_zero π hp hker hfinj hform

theorem ModuleSpec.commute_or_mem_center_of_nondeg (hp : p.Prime) (_hp2 : p ≠ 2)
    (hπ : Function.Surjective π) (hker : π.ker = Subgroup.center K)
    (_hZp : IsPGroup p (Subgroup.center K)) (hZc : IsCyclic (Subgroup.center K))
    (hD : D.Nondeg) :
    (∀ x ∈ D.span.comap π, ∀ y ∈ D.span.comap π, x * y = y * x) ∨
      ∀ x ∈ D.span.comap π, (∀ y ∈ D.span.comap π, x * y = y * x) →
        x ∈ Subgroup.center K := by
  have := Fact.mk hp
  obtain ⟨f, B, hfinj, hf1, hBt, hBM, hform⟩ := D.exists_commForm π hp hπ hker hZc
  by_cases hB : B = 0
  · subst hB
    exact Or.inl (D.commute_of_form_eq_zero π hp hker hfinj hform)
  · right
    have hdet := hD B hBt hBM hB
    intro x hx hcomm
    obtain ⟨c, hc⟩ := D.exists_elt hx
    have hvec : Matrix.vecMul c B = 0 := by
      ext k
      have hy : Function.surjInv hπ (D.a k) ∈ D.span.comap π :=
        D.surjInv_mem π hπ (D.a_mem_span k)
      have h0 := hform x hx _ hy c (Pi.single k 1) hc.symm
        (by rw [Function.surjInv_eq hπ, D.elt_single])
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (hcomm _ hy), hf1] at h0
      simpa [Matrix.vecMul, dotProduct, Pi.single_apply] using h0.symm
    have hc0 : c = 0 := Matrix.eq_zero_of_vecMul_eq_zero hdet.ne_zero hvec
    rw [← hker, MonoidHom.mem_ker, ← hc, hc0, D.elt_zero]

theorem ModuleSpec.exists_pow_eq_pow_of_noFun (hp : p.Prime) (hp2 : p ≠ 2)
    (hπ : Function.Surjective π) (hker : π.ker = Subgroup.center K)
    (_hZp : IsPGroup p (Subgroup.center K)) (hZc : IsCyclic (Subgroup.center K))
    (hD : D.NoFun) : ∀ x ∈ D.span.comap π, ∃ z ∈ Subgroup.center K, x ^ p = z ^ p := by
  have := Fact.mk hp
  obtain ⟨h, hhmul, hhker⟩ := exists_log_center (K := K) hp hZc
  have hh1 : h 1 = 0 := by
    have h0 := hhmul 1 1 (one_mem _) (one_mem _)
    rwa [mul_one, left_eq_add] at h0
  have hhp : ∀ z ∈ Subgroup.center K, h (z ^ p) = 0 := by
    intro z hz
    have hm : ∀ m : ℕ, h (z ^ m) = m • h z := by
      intro m
      induction m with
      | zero => simp [hh1]
      | succ m ih => rw [pow_succ, hhmul _ _ (pow_mem hz m) hz, ih, succ_nsmul]
    rw [hm, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  have hwd : ∀ x ∈ D.span.comap π, ∀ x' : K, π x = π x' → h (x ^ p) = h (x' ^ p) := by
    intro x hx x' hxx'
    have hz : x⁻¹ * x' ∈ Subgroup.center K := hker ▸ π.eq_iff.mp hxx'.symm
    rw [← mul_inv_cancel_left x x',
      (show Commute x (x⁻¹ * x') from (Subgroup.mem_center_iff.mp hz x)).mul_pow,
      hhmul _ _ (D.pow_mem_center π hker hx) (pow_mem hz p), hhp _ hz, add_zero]
  let w : (Fin D.n → ZMod p) → ZMod p := fun c => h (Function.surjInv hπ (D.elt c) ^ p)
  have hs : ∀ c, Function.surjInv hπ (D.elt c) ∈ D.span.comap π :=
    fun c => D.surjInv_mem π hπ (D.elt_mem c)
  have hwx : ∀ x ∈ D.span.comap π, ∀ c, π x = D.elt c → h (x ^ p) = w c :=
    fun x hx c hxc => hwd x hx _ (by rw [Function.surjInv_eq hπ, hxc])
  have hwadd : ∀ c d, w (c + d) = w c + w d := by
    intro c d
    rw [← hwx _ (mul_mem (hs c) (hs d)) (c + d)
      (by rw [map_mul, Function.surjInv_eq hπ, Function.surjInv_eq hπ, D.elt_add]),
      mul_pow_prime_of_center hp hp2 (D.commutator_mem_center π hker (hs d) (hs c))
        (D.commutator_pow_eq_one π hker (hs d) (hs c)) (by rw [commutatorElement_def]; group)]
    exact hhmul _ _ (D.pow_mem_center π hker (hs c)) (D.pow_mem_center π hker (hs d))
  have hwcol : ∀ j i, w (fun k => D.M j k i) = w (Pi.single i 1) := by
    intro j i
    have hx : Function.surjInv hπ (D.a i) ∈ D.span.comap π :=
      D.surjInv_mem π hπ (D.a_mem_span i)
    have hmap : π (Function.surjInv hπ (D.g j) * Function.surjInv hπ (D.a i) *
        (Function.surjInv hπ (D.g j))⁻¹) = D.elt (fun k => D.M j k i) := by
      rw [map_mul, map_mul, map_inv, Function.surjInv_eq hπ, Function.surjInv_eq hπ, D.elt_col]
    have hconj : Function.surjInv hπ (D.g j) * Function.surjInv hπ (D.a i) *
        (Function.surjInv hπ (D.g j))⁻¹ ∈ D.span.comap π := by
      rw [Subgroup.mem_comap, hmap]
      exact D.elt_mem _
    rw [← hwx _ hconj _ hmap, conj_pow,
      Subgroup.mem_center_iff.mp (D.pow_mem_center π hker hx), mul_inv_cancel_right,
      hwx _ hx _ (by rw [Function.surjInv_eq hπ, D.elt_single])]
  let v : Fin D.n → ZMod p := fun k => w (Pi.single k 1)
  have hv : v = 0 := hD v fun j => by
    ext i
    simp only [Matrix.vecMul, dotProduct, v]
    rw [← hwcol j i, eq_sum_of_map_add hwadd (fun k => D.M j k i)]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  intro x hx
  obtain ⟨c, hc⟩ := D.exists_elt hx
  have h0 : h (x ^ p) = 0 := by
    rw [hwx x hx c hc.symm, eq_sum_of_map_add hwadd c]
    exact Finset.sum_eq_zero fun k _ => by
      rw [show w (Pi.single k 1) = 0 from congrFun hv k, mul_zero]
  exact hhker _ (D.pow_mem_center π hker hx) h0

end CFSG.AGLEmbedding
