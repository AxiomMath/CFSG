module

public import CFSG.LocalAnalysis.AGLEmbedding.CoverModule
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.AGLEmbedding.KFacts

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.AGLEmbedding CFSG.AGLEmbedding.CoverCore
open scoped IsMulCommutative commutatorElement

theorem i1021_exists_add_aux {A : Type*} [CommGroup A] {p : ℕ} [Fact p.Prime]
    [Module (ZMod p) (Additive A)] {a : A} (ha : a ≠ 1) :
    ∃ g : A → ZMod p, (∀ b c, g (b * c) = g b + g c) ∧ g a ≠ 0 := by
  have hv : (Additive.ofMul a) ≠ 0 := fun h => ha (by simpa using h)
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero (V := Additive A) (ZMod p) hv
  exact ⟨fun b => φ (Additive.ofMul b), fun b c => φ.map_add (Additive.ofMul b)
    (Additive.ofMul c), hφ⟩

theorem i1021_exists_add_of_exp {A : Type*} [CommGroup A] {p : ℕ} [Fact p.Prime]
    (hA : ∀ a : A, a ^ p = 1) {a : A} (ha : a ≠ 1) :
    ∃ g : A → ZMod p, (∀ b c, g (b * c) = g b + g c) ∧ g a ≠ 0 := by
  let inst : Module (ZMod p) (Additive A) := AddCommGroup.zmodModule (fun x => by
    have h := hA (Additive.toMul x)
    apply Additive.toMul.injective
    rw [toMul_nsmul]
    simpa using h)
  exact i1021_exists_add_aux ha

section Sep

variable {K : Type} [Group K] {p : ℕ} [Fact p.Prime]

theorem i1021_sep_omega {z : K} (hz : z ∈ Subgroup.center K) (hzp : z ^ p = 1) (hz1 : z ≠ 1) :
    ∃ f : K → ZMod p, (∀ z w, z ∈ Subgroup.center K → z ^ p = 1 → w ∈ Subgroup.center K →
      w ^ p = 1 → f (z * w) = f z + f w) ∧ f z ≠ 0 := by
  classical
  let Ω : Subgroup (Subgroup.center K) := (powMonoidHom p).ker
  have hΩ : ∀ c : Ω, c ^ p = 1 := fun c => Subtype.ext c.2
  have hzΩ : (⟨⟨z, hz⟩, Subtype.ext hzp⟩ : Ω) ≠ 1 := fun h => hz1 (by
    simpa using congrArg (fun c : Ω => ((c : Subgroup.center K) : K)) h)
  obtain ⟨g, hg, hgz⟩ := i1021_exists_add_of_exp hΩ hzΩ
  refine ⟨fun z => if h : z ∈ Subgroup.center K ∧ z ^ p = 1 then g ⟨⟨z, h.1⟩, Subtype.ext h.2⟩
    else 0, ?_, ?_⟩
  · intro z w hz hz' hw hw'
    have hzw : z * w ∈ Subgroup.center K ∧ (z * w) ^ p = 1 :=
      ⟨mul_mem hz hw, by
        rw [(show Commute z w from Subgroup.mem_center_iff.mp hz w |>.symm).mul_pow, hz', hw',
          one_mul]⟩
    simp only [dite_eq_left hzw, dite_eq_left (And.intro hz hz'),
      dite_eq_left (And.intro hw hw')]
    exact hg ⟨⟨z, hz⟩, Subtype.ext hz'⟩ ⟨⟨w, hw⟩, Subtype.ext hw'⟩
  · simpa [dite_eq_left (And.intro hz hzp)] using hgz

theorem i1021_sep_center {z : K} (hz : z ∈ Subgroup.center K)
    (hnp : ¬ ∃ w ∈ Subgroup.center K, z = w ^ p) :
    ∃ h : K → ZMod p, (∀ z w, z ∈ Subgroup.center K → w ∈ Subgroup.center K →
      h (z * w) = h z + h w) ∧ h z ≠ 0 := by
  classical
  let P : Subgroup (Subgroup.center K) := (powMonoidHom p).range
  have hQ : ∀ q : Subgroup.center K ⧸ P, q ^ p = 1 := fun q => by
    induction q using QuotientGroup.induction_on with
    | H z => exact (QuotientGroup.eq_one_iff _).mpr ⟨z, rfl⟩
  have hz1 : (QuotientGroup.mk (⟨z, hz⟩ : Subgroup.center K) : Subgroup.center K ⧸ P) ≠ 1 := by
    intro h
    obtain ⟨w, hw⟩ := (QuotientGroup.eq_one_iff _).1 h
    exact hnp ⟨w, w.2, by simpa using congrArg (fun c : Subgroup.center K => (c : K)) hw.symm⟩
  obtain ⟨g, hg, hgz⟩ := i1021_exists_add_of_exp hQ hz1
  refine ⟨fun z => if h : z ∈ Subgroup.center K then g (QuotientGroup.mk ⟨z, h⟩) else 0, ?_, ?_⟩
  · intro z w hz hw
    have hzw : z * w ∈ Subgroup.center K := mul_mem hz hw
    simp only [dite_eq_left hzw, dite_eq_left hz, dite_eq_left hw]
    exact hg (QuotientGroup.mk ⟨z, hz⟩) (QuotientGroup.mk ⟨w, hw⟩)
  · simpa [dite_eq_left hz] using hgz

end Sep

section Form

variable {K X : Type} [Group K] [Group X] {p : ℕ} (D : ModuleSpec X p) (π : K →* X)

theorem i1021_commForm_of (hp : p.Prime) (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.center K) (f : K → ZMod p)
    (hfmul : ∀ z w, z ∈ Subgroup.center K → z ^ p = 1 → w ∈ Subgroup.center K → w ^ p = 1 →
      f (z * w) = f z + f w) :
    ∃ B : Matrix (Fin D.n) (Fin D.n) (ZMod p), B.transpose = -B ∧
      (∀ j, (D.M j).transpose * B * D.M j = B) ∧
      ∀ x ∈ D.span.comap π, ∀ y ∈ D.span.comap π, ∀ c d, π x = D.elt c → π y = D.elt d →
        f ⁅x, y⁆ = ∑ i, c i * ∑ k, d k * B i k := by
  have := Fact.mk hp
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
  refine ⟨B, ?_, fun j => ?_, ?_⟩
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

theorem i1021_commute_of_noAlt (hp : p.Prime) (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.center K) (hD : D.NoAlt) :
    ∀ x ∈ D.span.comap π, ∀ y ∈ D.span.comap π, x * y = y * x := by
  have := Fact.mk hp
  intro x hx y hy
  by_contra hne
  have hc1 : ⁅x, y⁆ ≠ 1 := fun h => hne (commutatorElement_eq_one_iff_mul_comm.1 h)
  obtain ⟨f, hfmul, hfz⟩ := i1021_sep_omega (p := p) (D.commutator_mem_center π hker hx hy)
    (D.commutator_pow_eq_one π hker hx hy) hc1
  obtain ⟨B, hBt, hBM, hform⟩ := i1021_commForm_of D π hp hπ hker f hfmul
  obtain rfl : B = 0 := hD B hBt hBM
  obtain ⟨c, hc⟩ := D.exists_elt hx
  obtain ⟨d, hd⟩ := D.exists_elt hy
  have h0 := hform x hx y hy c d hc.symm hd.symm
  simp at h0
  exact hfz h0

theorem i1021_pow_zero_of_noFun (hp : p.Prime) (hp2 : p ≠ 2) (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.center K) (h : K → ZMod p)
    (hhmul : ∀ z w, z ∈ Subgroup.center K → w ∈ Subgroup.center K → h (z * w) = h z + h w)
    (hD : D.NoFun) : ∀ x ∈ D.span.comap π, h (x ^ p) = 0 := by
  have := Fact.mk hp
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
  rw [hwx x hx c hc.symm, eq_sum_of_map_add hwadd c]
  exact Finset.sum_eq_zero fun k _ => by
    rw [show w (Pi.single k 1) = 0 from congrFun hv k, mul_zero]

theorem i1021_pow_eq_pow_of_noFun (hp : p.Prime) (hp2 : p ≠ 2) (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.center K) (hD : D.NoFun) :
    ∀ x ∈ D.span.comap π, ∃ z ∈ Subgroup.center K, x ^ p = z ^ p := by
  have := Fact.mk hp
  intro x hx
  by_contra hno
  push Not at hno
  obtain ⟨h, hhmul, hhz⟩ := i1021_sep_center (p := p) (D.pow_mem_center π hker hx)
    (fun ⟨z, hz, hxz⟩ => hno z hz hxz)
  exact hhz (i1021_pow_zero_of_noFun D π hp hp2 hπ hker h hhmul hD x hx)

end Form

theorem i1021_le_pRank_of_datum {K X : Type} [Group K] [Finite K] [Group X] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (π : K →* X) (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.center K) (D : ModuleSpec X p) (hA : D.NoAlt) (hF : D.NoFun) :
    D.n ≤ CFSG.Open.pRank p (⊤ : Subgroup K) := by
  have := Fact.mk hp
  have hcomm := i1021_commute_of_noAlt D π hp hπ hker hA
  have hπZ : ∀ z ∈ Subgroup.center K, π z = 1 := fun z hz =>
    MonoidHom.mem_ker.mp (hker.symm ▸ hz)
  have hZÂ : ∀ z ∈ Subgroup.center K, z ∈ D.span.comap π := fun z hz => by
    rw [Subgroup.mem_comap, hπZ z hz]
    exact one_mem _
  set A := omegaOf (D.span.comap π) hcomm p
  have hmap : A.map π = D.span := by
    refine le_antisymm (Subgroup.map_le_iff_le_comap.mpr omegaOf_le) fun u hu => ?_
    obtain ⟨x, rfl⟩ := hπ u
    obtain ⟨z, hz, hxz⟩ := i1021_pow_eq_pow_of_noFun D π hp hp2 hπ hker hF x hu
    refine ⟨x * z⁻¹, ⟨mul_mem hu (hZÂ _ (inv_mem hz)), ?_⟩, ?_⟩
    · rw [(show Commute x z⁻¹ from Subgroup.mem_center_iff.mp (inv_mem hz) x).mul_pow, hxz,
        inv_pow, mul_inv_cancel]
    · rw [map_mul, hπZ _ (inv_mem hz), mul_one]
  have hdvd : Nat.card D.span ∣ Nat.card A := by
    have h1 : Nat.card (π.domRestrict A).range ∣ Nat.card A :=
      Subgroup.card_dvd_of_surjective (f := (π.domRestrict A).rangeRestrict)
        (MonoidHom.rangeRestrict_surjective _)
    rwa [MonoidHom.domRestrict_range, hmap] at h1
  have hAp : IsPGroup p A := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext g.2.2⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p)).1 hAp
  have hle : p ^ D.n ≤ p ^ k := by
    rw [← hk]
    exact Nat.le_of_dvd Nat.card_pos (D.card_span hp ▸ hdvd)
  have := (Nat.pow_le_pow_iff_right hp.one_lt).1 hle
  exact this.trans (CFSG.SectionRank.le_pRank hp.one_lt le_top isElemAbelian_omegaOf hk)

end CFSG.HardMathSupport.Solomon.Coordinator
