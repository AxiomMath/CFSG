module

public import CFSG.HardMathSupport.Curtis.Coordinator.SPLCellOrbit
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Std.Tactic.BVDecide.Normalize.Prop

public section

open Module Polynomial

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellOrth

open CFSG.HardMathSupport.Curtis.Coordinator.SPLCell

section Main

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [Module.Finite K V]
variable {G : Type*} [CommGroup G] [Fintype G]

theorem exists_five_pieces_kernels {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hr5 : 5 ≤ r)
    (hrp : ¬ r ∣ p - 1) (hpK : (p : K) ≠ 0) (hGp : ∀ g : G, g ^ p = 1)
    (hGK : ((Fintype.card G : ℕ) : K) ≠ 0)
    (ρ : G →* (V ≃ₗ[K] V)) (hρinj : Function.Injective ρ)
    (z : Module.End K V) (hz : ∀ g, Commute z ((ρ g : V ≃ₗ[K] V) : Module.End K V))
    (hzp : z ^ p = 1) (γ : MulAut G) (k : ℕ) (hγ : γ ^ r ^ k = 1) (g₀ : G) (hg₀ : γ g₀ ≠ g₀)
    (σ : K ≃+* K) (f : V →ₛₗ[(σ : K →+* K)] V) (hf : Function.Bijective f)
    (hfρ : ∀ g v, f (ρ g v) = ρ (γ g) (f v)) (hfz : ∀ v, f (z v) = z (f v))
    (hσ : ∀ h : K[X], h.Monic → Irreducible h → h ∣ X ^ p - 1 → h.map (σ : K →+* K) = h) :
    ∃ h : K[X], Irreducible h ∧ h.Monic ∧ h ∣ X ^ p - 1 ∧
      ∃ (M : Fin 5 → Submodule K V) (D : Fin 5 → Subgroup G), (∀ i, M i ≠ ⊥) ∧
        (∀ i, ∀ v ∈ M i, aeval z h v = 0) ∧ (∀ i, ∀ v ∈ M i, z v ∈ M i) ∧ iSupIndep M ∧
        (∀ i, (D i).index = p) ∧ (∀ i j, i ≠ j → D i ⊔ D j = ⊤) ∧
        (∀ i, ∀ w ∈ M i, ∀ d ∈ D i, ρ d w = w) ∧ (∀ i, ∀ w ∈ M i, ∑ g : G, ρ g w = 0) := by
  classical
  have : RingHomSurjective (σ : K →+* K) := ⟨σ.surjective⟩
  set a : G := γ g₀ * g₀⁻¹ with ha_def
  have ha1 : a ≠ 1 := fun h => hg₀ (mul_inv_eq_one.1 h)
  have hρa : ρ a ≠ 1 := fun h => ha1 (hρinj (by rw [h, map_one]))
  let Na : Module.End K V := ∑ i ∈ Finset.range p, ((ρ (a ^ i) : V ≃ₗ[K] V) : Module.End K V)
  let U : Submodule K V := LinearMap.ker Na
  have hNa_apply : ∀ v, Na v = ∑ i ∈ Finset.range p, ρ (a ^ i) v := fun v => by
    simp [Na, LinearMap.sum_apply]
  have hUi : InvSet (famSet ρ z) U := by
    intro F hF v hv
    rw [LinearMap.mem_ker, hNa_apply] at hv ⊢
    calc ∑ i ∈ Finset.range p, ρ (a ^ i) (F v) = ∑ i ∈ Finset.range p, F (ρ (a ^ i) v) :=
          Finset.sum_congr rfl fun i _ => fam_comm ρ z hz hF _ v
      _ = F (∑ i ∈ Finset.range p, ρ (a ^ i) v) := by rw [map_sum]
      _ = 0 := by rw [hv, map_zero]
  have hU0 : U ≠ ⊥ := by
    obtain ⟨w, hw⟩ : ∃ w, ρ a w ≠ w := by
      by_contra hcon
      push Not at hcon
      exact hρa (LinearEquiv.ext hcon)
    intro hbot
    have hmem : ρ a w - w ∈ U := by
      rw [LinearMap.mem_ker, hNa_apply]
      have : ∀ i : ℕ, ρ (a ^ i) (ρ a w - w) = ρ (a ^ (i + 1)) w - ρ (a ^ i) w := by
        intro i
        rw [map_sub, ← LinearEquiv.mul_apply, ← map_mul, ← pow_succ]
      simp only [this]
      rw [Finset.sum_range_sub (fun i => ρ (a ^ i) w) p, hGp a, pow_zero, map_one]
      simp
    rw [hbot, Submodule.mem_bot, sub_eq_zero] at hmem
    exact hw hmem
  have hUsum : ∀ v ∈ U, ∑ g : G, ρ g v = 0 := by
    intro v hv
    rw [LinearMap.mem_ker, hNa_apply] at hv
    have h1 : ∑ g : G, ρ g (∑ i ∈ Finset.range p, ρ (a ^ i) v) = (p : K) • ∑ g : G, ρ g v := by
      simp only [map_sum]
      rw [Finset.sum_comm]
      simp only [sum_absorb, Finset.sum_const, Finset.card_range, Nat.cast_smul_eq_nsmul]
    rw [hv] at h1
    simp only [map_zero, Finset.sum_const_zero] at h1
    exact (smul_eq_zero.1 h1.symm).resolve_left hpK
  obtain ⟨M, hMU, hM0, hMi, hcyc, h, hirr, hmon, hMh, hdvd⟩ :=
    exists_piece ρ z hz U hU0 hUi
  let D : Subgroup G := stabOn ρ M
  have haD : a ∉ D := by
    intro haD
    apply hM0
    rw [eq_bot_iff]
    intro v hv
    have h1 : Na v = (p : K) • v := by
      rw [hNa_apply]
      have : ∀ i : ℕ, ρ (a ^ i) v = v := fun i => (mem_stabOn.1 (D.pow_mem haD i)) v hv
      simp only [this, Finset.sum_const, Finset.card_range, Nat.cast_smul_eq_nsmul]
    have h2 : Na v = 0 := LinearMap.mem_ker.1 (hMU hv)
    rw [h1] at h2
    rw [Submodule.mem_bot]
    exact (smul_eq_zero.1 h2).resolve_left hpK
  have hDindex : D.index = p := card_quot_eq_of_cyclic hp hGp D hcyc a haD
  have hDγ : D.map (γ : G →* G) ≠ D := by
    intro hDγ
    exact haD (stable_acts_trivially hp hr hrp hGp γ hγ D hcyc hDγ a haD g₀)
  have hdvd' : h ∣ X ^ p - 1 := by
    apply hdvd
    simp [hzp]
  have hhσ : h.map (σ : K →+* K) = h := hσ h hmon hirr hdvd'
  have hh : h.map (σ.symm : K →+* K) = h := by
    have := congrArg (fun q : K[X] => q.map (σ.symm : K →+* K)) hhσ
    simp only [Polynomial.map_map] at this
    have h2 : (σ.symm : K →+* K).comp (σ : K →+* K) = RingHom.id K := by
      ext x; simp
    rw [h2, Polynomial.map_id] at this
    exact this.symm
  have hP0 : PieceProps ρ z h M D :=
    ⟨hM0, hMi, rfl, hMh, fun v hv => hUsum v (hMU hv)⟩
  let φ : Subgroup G → Subgroup G := fun H => H.map (γ : G →* G)
  let Pi : ℕ → Submodule K V := fun i => (Submodule.map f)^[i] M
  let Di : ℕ → Subgroup G := fun i => φ^[i] D
  have hPi : ∀ i, PieceProps ρ z h (Pi i) (Di i) := by
    intro i
    induction i with
    | zero => exact hP0
    | succ i ih =>
      have e1 : Pi (i + 1) = (Pi i).map f := by
        simp only [Pi]; rw [Function.iterate_succ_apply']
      have e2 : Di (i + 1) = φ (Di i) := by
        simp only [Di]; rw [Function.iterate_succ_apply']
      rw [e1, e2]
      exact PieceProps.map σ f hf.1 γ hfρ hfz hh ih
  have hDiIndex : ∀ i, (Di i).index = p := by
    intro i
    induction i with
    | zero => exact hDindex
    | succ i ih =>
      have e2 : Di (i + 1) = φ (Di i) := by
        simp only [Di]; rw [Function.iterate_succ_apply']
      rw [e2]
      change ((Di i).map (γ : G →* G)).index = p
      rw [Subgroup.index_map_equiv (Di i) γ]
      exact ih
  have hiter : ∀ (n : ℕ) (H : Subgroup G), φ^[n] H = H.map ((γ ^ n : MulAut G) : G →* G) := by
    intro n
    induction n with
    | zero =>
      intro H
      show H = H.map ((1 : MulAut G) : G →* G)
      exact (Subgroup.map_id H).symm
    | succ n ih =>
      intro H
      rw [Function.iterate_succ_apply', ih]
      change (H.map ((γ ^ n : MulAut G) : G →* G)).map (γ : G →* G) = _
      rw [Subgroup.map_map, pow_succ']
      rfl
  have hper : Function.IsPeriodicPt φ (r ^ k) D := by
    change φ^[r ^ k] D = D
    rw [hiter, hγ]
    exact Subgroup.map_id D
  have hdvdm : Function.minimalPeriod φ D ∣ r ^ k := hper.minimalPeriod_dvd
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hr).1 hdvdm
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hj
    exact hDγ (Function.minimalPeriod_eq_one_iff_isFixedPt.1 hj)
  have h5 : 5 ≤ Function.minimalPeriod φ D := by
    rw [hj]
    exact hr5.trans (Nat.le_self_pow hj0 r)
  have hdistinct : ∀ i j : Fin 5, i ≠ j → Di i ≠ Di j := by
    intro i j hij heq
    have hinj := Function.iterate_injOn_Iio_minimalPeriod (f := φ) (x := D)
    exact hij (Fin.ext (hinj (Set.mem_Iio.2 (lt_of_lt_of_le i.2 h5))
      (Set.mem_Iio.2 (lt_of_lt_of_le j.2 h5)) heq))
  have hsup : ∀ i j : Fin 5, i ≠ j → Di i ⊔ Di j = ⊤ := fun i j hij =>
    sup_eq_top_of_index_prime hp (hDiIndex i) (hDiIndex j) (hdistinct i j hij)
  have hfix : ∀ i : Fin 5, ∀ w ∈ Pi i, ∀ d ∈ Di i, ρ d w = w := by
    intro i w hw d hd
    have := (hPi i).stab
    rw [← this] at hd
    exact mem_stabOn.1 hd w hw
  have hsum : ∀ i : Fin 5, ∀ w ∈ Pi i, ∑ g : G, ρ g w = 0 := fun i w hw => (hPi i).sum_zero w hw
  have hcard : ∀ i : Fin 5, ((Nat.card (Di i) : ℕ) : K) ≠ 0 := by
    intro i hc
    have h1 := Subgroup.card_mul_index (Di i)
    rw [hDiIndex i] at h1
    apply hGK
    have : ((Fintype.card G : ℕ) : K) = ((Nat.card (Di i) * p : ℕ) : K) := by
      rw [h1, Nat.card_eq_fintype_card]
    rw [this]
    push_cast
    rw [hc, zero_mul]
  exact ⟨h, hirr, hmon, hdvd', fun i => Pi i, fun i => Di i, fun i => (hPi i).ne_bot,
    fun i => (hPi i).aeval_zero, fun i v hv => (hPi i).inv z (Or.inl rfl) v hv,
    iSupIndep_of_fixed ρ (fun i : Fin 5 => Pi i) (fun i : Fin 5 => Di i) hsup hfix hsum hcard hGK,
    fun i => hDiIndex i, hsup, hfix, hsum⟩

end Main

section Dim

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
variable {G : Type*} [CommGroup G] [Fintype G]

theorem polar_sumOver (B : LinearMap.BilinForm K V) (ρ : G →* (V ≃ₗ[K] V))
    (hρB : ∀ g u v, B (ρ g u) (ρ g v) = B u v) (D : Subgroup G) (u u' : V) :
    B (sumOver ρ D u) u' = B u (sumOver ρ D u') := by
  classical
  have key : ∀ g : G, B (ρ g u) u' = B u (ρ g⁻¹ u') := by
    intro g
    have h := hρB g⁻¹ (ρ g u) u'
    have e : ρ g⁻¹ (ρ g u) = u := by
      rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
    rw [e] at h
    exact h.symm
  simp only [sumOver_def, map_sum, LinearMap.sum_apply, apply_ite, map_zero]
  refine Fintype.sum_equiv (Equiv.inv G) _ _ (fun g => ?_)
  by_cases hg : g ∈ D
  · have : g⁻¹ ∈ D := D.inv_mem hg
    simp [hg, this, key]
  · have : g⁻¹ ∉ D := fun h => hg (by simpa using D.inv_mem h)
    simp [hg, this]

theorem sumOver_top (ρ : G →* (V ≃ₗ[K] V)) (u : V) : sumOver ρ ⊤ u = ∑ g : G, ρ g u := by
  classical
  simp [sumOver_def]

theorem sum_sumOver (ρ : G →* (V ≃ₗ[K] V)) (D : Subgroup G) (u : V) :
    ∑ g : G, ρ g (sumOver ρ D u) = (Nat.card D : K) • ∑ g : G, ρ g u := by
  classical
  have h1 : ∀ h : G, ∑ g : G, ρ g (if h ∈ D then ρ h u else 0) =
      if h ∈ D then ∑ g : G, ρ g u else 0 := by
    intro h
    by_cases hh : h ∈ D
    · simp only [hh, ite_true]
      exact sum_absorb ρ h u
    · simp [hh]
  rw [sumOver_def]
  simp only [map_sum]
  rw [Finset.sum_comm, Finset.sum_congr rfl (fun h _ => h1 h), Finset.sum_ite,
    Finset.sum_const_zero, add_zero, Finset.sum_const]
  have hc : (Finset.univ.filter (· ∈ D)).card = Nat.card D := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hc, Nat.cast_smul_eq_nsmul]

def fixKer (ρ : G →* (V ≃ₗ[K] V)) (D : Subgroup G) : Submodule K V where
  carrier := {v | (∀ d ∈ D, ρ d v = v) ∧ ∑ g : G, ρ g v = 0}
  add_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨fun d hd => ?_, ?_⟩
    · rw [map_add, ha1 d hd, hb1 d hd]
    · simp only [map_add, Finset.sum_add_distrib, ha2, hb2, add_zero]
  zero_mem' := by simp
  smul_mem' := by
    rintro c a ⟨ha1, ha2⟩
    refine ⟨fun d hd => ?_, ?_⟩
    · rw [map_smul, ha1 d hd]
    · simp only [map_smul, ← Finset.smul_sum, ha2, smul_zero]

noncomputable def projFixKer (ρ : G →* (V ≃ₗ[K] V)) (D : Subgroup G) (u : V) : V :=
  ((Nat.card D : ℕ) : K)⁻¹ • sumOver ρ D u - ((Fintype.card G : ℕ) : K)⁻¹ • sumOver ρ ⊤ u

theorem projFixKer_mem (ρ : G →* (V ≃ₗ[K] V)) (D : Subgroup G)
    (hD : ((Nat.card D : ℕ) : K) ≠ 0) (hG : ((Fintype.card G : ℕ) : K) ≠ 0) (u : V) :
    projFixKer ρ D u ∈ fixKer ρ D := by
  refine ⟨fun d hd => ?_, ?_⟩
  · rw [projFixKer, map_sub, map_smul, map_smul, ρ_sumOver ρ D hd, ρ_sumOver ρ ⊤ (Subgroup.mem_top d)]
  · have hcardtop : ((Nat.card (⊤ : Subgroup G) : ℕ) : K) = ((Fintype.card G : ℕ) : K) := by
      rw [Subgroup.card_top, Nat.card_eq_fintype_card]
    rw [projFixKer]
    simp only [map_sub, map_smul, Finset.sum_sub_distrib, ← Finset.smul_sum]
    rw [sum_sumOver, sum_sumOver, hcardtop, smul_smul, smul_smul, inv_mul_cancel₀ hD,
      inv_mul_cancel₀ hG, sub_self]

theorem projFixKer_of_mem (ρ : G →* (V ≃ₗ[K] V)) (D : Subgroup G)
    (hD : ((Nat.card D : ℕ) : K) ≠ 0) {v : V} (hv : v ∈ fixKer ρ D) : projFixKer ρ D v = v := by
  rw [projFixKer, sumOver_of_fixed ρ D hv.1, sumOver_top, hv.2, smul_zero, sub_zero, smul_smul,
    inv_mul_cancel₀ hD, one_smul]

theorem polar_projFixKer (B : LinearMap.BilinForm K V) (ρ : G →* (V ≃ₗ[K] V))
    (hρB : ∀ g u v, B (ρ g u) (ρ g v) = B u v) (D : Subgroup G) (u u' : V) :
    B (projFixKer ρ D u) u' = B u (projFixKer ρ D u') := by
  simp only [projFixKer, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    polar_sumOver B ρ hρB]

theorem finrank_ge_ten_of_pieces [FiniteDimensional K V] (B : LinearMap.BilinForm K V)
    (hB : ∀ v, B v v = 0) (hreg : ∀ v, (∀ w, B v w = 0) → v = 0)
    (ρ : G →* (V ≃ₗ[K] V)) (hρB : ∀ g u v, B (ρ g u) (ρ g v) = B u v)
    (hG : ((Fintype.card G : ℕ) : K) ≠ 0)
    (M : Fin 5 → Submodule K V) (D : Fin 5 → Subgroup G) (hM0 : ∀ i, M i ≠ ⊥)
    (hsup : ∀ i j, i ≠ j → D i ⊔ D j = ⊤)
    (hfix : ∀ i, ∀ w ∈ M i, ∀ d ∈ D i, ρ d w = w)
    (hker : ∀ i, ∀ w ∈ M i, ∑ g : G, ρ g w = 0)
    (hcard : ∀ i, ((Nat.card (D i) : ℕ) : K) ≠ 0) :
    10 ≤ Module.finrank K V := by
  classical
  let W : Fin 5 → Submodule K V := fun i => fixKer ρ (D i)
  have hind : iSupIndep W :=
    iSupIndep_of_fixed ρ W D hsup (fun i w hw => hw.1) (fun i w hw => hw.2) hcard hG
  have hW2 : ∀ i, 2 ≤ Module.finrank K (W i) := by
    intro i
    obtain ⟨v, hvM, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hM0 i)
    have hvW : v ∈ W i := ⟨hfix i v hvM, hker i v hvM⟩
    obtain ⟨w', hw'⟩ : ∃ w', B v w' ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hv0 (hreg v hcon)
    set w := projFixKer ρ (D i) w' with hw_def
    have hwW : w ∈ W i := projFixKer_mem ρ (D i) (hcard i) hG w'
    have hvw : B v w ≠ 0 := by
      rw [hw_def, ← polar_projFixKer B ρ hρB, projFixKer_of_mem ρ (D i) (hcard i) hvW]
      exact hw'
    have hli : LinearIndependent K ![v, w] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have h1 : t * B v w = 0 := by
        have := congrArg (B v) hst
        simpa [hB v] using this
      have ht : t = 0 := (mul_eq_zero.1 h1).resolve_right hvw
      refine ⟨?_, ht⟩
      rw [ht, zero_smul, add_zero] at hst
      exact (smul_eq_zero.1 hst).resolve_right hv0
    have hli' : LinearIndependent K ![(⟨v, hvW⟩ : W i), ⟨w, hwW⟩] := by
      refine LinearIndependent.of_comp (W i).subtype ?_
      convert hli using 1
      ext j
      fin_cases j <;> rfl
    have := hli'.fintype_card_le_finrank
    simpa using this
  have hinj := hind.dfinsupp_lsum_injective
  have h1 : Module.finrank K (DirectSum (Fin 5) fun i => W i) ≤ Module.finrank K V :=
    LinearMap.finrank_le_finrank_of_injective
      (f := (DFinsupp.lsum K fun i => (W i).subtype : (Π₀ i, W i) →ₗ[K] V)) hinj
  rw [Module.finrank_directSum] at h1
  calc 10 = ∑ _i : Fin 5, 2 := by simp
    _ ≤ ∑ i, Module.finrank K (W i) := Finset.sum_le_sum fun i _ => hW2 i
    _ ≤ _ := h1

theorem finrank_ge_ten_of_pieces_quadratic [FiniteDimensional K V] [CharP K 2]
    (Q : QuadraticForm K V)
    (hreg : ∀ v, (∀ w, QuadraticMap.polar Q v w = 0) → v = 0)
    (ρ : G →* (V ≃ₗ[K] V)) (hρQ : ∀ g v, Q (ρ g v) = Q v)
    (hG : ((Fintype.card G : ℕ) : K) ≠ 0)
    (M : Fin 5 → Submodule K V) (D : Fin 5 → Subgroup G) (hM0 : ∀ i, M i ≠ ⊥)
    (hsup : ∀ i j, i ≠ j → D i ⊔ D j = ⊤)
    (hfix : ∀ i, ∀ w ∈ M i, ∀ d ∈ D i, ρ d w = w)
    (hker : ∀ i, ∀ w ∈ M i, ∑ g : G, ρ g w = 0)
    (hcard : ∀ i, ((Nat.card (D i) : ℕ) : K) ≠ 0) :
    10 ≤ Module.finrank K V := by
  refine finrank_ge_ten_of_pieces (QuadraticMap.polarBilin Q) ?_ ?_ ρ ?_ hG M D hM0 hsup hfix hker
    hcard
  · intro v
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_nsmul,
      CharTwo.add_self_eq_zero]
  · intro v hv
    exact hreg v (fun w => by simpa using hv w)
  · intro g u v
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add, hρQ]

end Dim

section Glue

variable {K : Type*} [Field K] [Finite K] [CharP K 2]
  {V : Type*} [AddCommGroup V] [Module K V] [Module.Finite K V]
  {G : Type*} [CommGroup G] [Fintype G]

theorem five_pieces_dimension_ge_ten {f p r k : ℕ} (hK : Nat.card K = 2 ^ f) (hp : p.Prime)
    (hp2 : p ≠ 2) (hr : r.Prime) (hr5 : 5 ≤ r) (hrp : ¬ r ∣ p - 1)
    (hGp : ∀ g : G, g ^ p = 1) (hGK : ((Fintype.card G : ℕ) : K) ≠ 0)
    (ρ : G →* (V ≃ₗ[K] V)) (hρinj : Function.Injective ρ)
    (Q : QuadraticForm K V) (hreg : ∀ v, (∀ w, QuadraticMap.polar Q v w = 0) → v = 0)
    (hρQ : ∀ g v, Q (ρ g v) = Q v)
    (γ : MulAut G) (hγ : γ ^ r ^ k = 1) (g₀ : G) (hg₀ : γ g₀ ≠ g₀)
    (σ : K ≃+* K) (hσpow : σ ^ r ^ k = 1) (fM : V →ₛₗ[(σ : K →+* K)] V)
    (hfbij : Function.Bijective fM) (hfρ : ∀ (e : G) (v : V), fM (ρ e v) = ρ (γ e) (fM v)) :
    10 ≤ Module.finrank K V := by
  have hpK : (p : K) ≠ 0 := by
    intro h0
    rw [CharP.cast_eq_zero_iff K 2] at h0
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h0).symm
  have hσ : ∀ h : K[X], h.Monic → Irreducible h → h ∣ X ^ p - 1 →
      h.map (σ : K →+* K) = h := fun h hm hi hd =>
    map_eq_of_irreducible_dvd hp hp2 hr hrp hK σ hσpow hm hi hd
  obtain ⟨h, -, -, -, M, D, hM0, -, -, -, hDi, hsup, hfix, hker⟩ :=
    exists_five_pieces_kernels hp hr hr5 hrp hpK hGp hGK ρ hρinj 1
      (fun g => Commute.one_left _) (one_pow p) γ k hγ g₀ hg₀ σ fM hfbij hfρ
      (fun v => by simp) hσ
  have hcard : ∀ i, ((Nat.card (D i) : ℕ) : K) ≠ 0 := by
    intro i hc
    have h1 := Subgroup.card_mul_index (D i)
    rw [hDi i] at h1
    apply hGK
    have : ((Fintype.card G : ℕ) : K) = ((Nat.card (D i) * p : ℕ) : K) := by
      rw [h1, Nat.card_eq_fintype_card]
    rw [this]
    push_cast
    rw [hc, zero_mul]
  exact finrank_ge_ten_of_pieces_quadratic Q hreg ρ hρQ hGK M D hM0 hsup hfix hker hcard

end Glue

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellOrth
