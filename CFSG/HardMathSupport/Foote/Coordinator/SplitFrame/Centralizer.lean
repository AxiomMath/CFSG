module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Arith

public noncomputable section

open Polynomial
open scoped Matrix

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame

variable {K : Type*} [Field K] [Fintype K]

omit [Fintype K] in
theorem irreducible_X_sub_one : Irreducible (X - 1 : K[X]) := by
  simpa using irreducible_X_sub_C (1 : K)

theorem natDegree_of_irreducible_dvd {p n : ℕ} [hp : Fact p.Prime]
    (hord : orderOf ((Fintype.card K : ℕ) : ZMod p) = n)
    {f : K[X]} (hf : Irreducible f) (hdvd : f ∣ X ^ p - 1) (hnot : ¬ f ∣ X - 1) :
    n ∣ f.natDegree := by
  have : Fact (Irreducible f) := ⟨hf⟩
  have hq : 1 ≤ Fintype.card K := Fintype.one_lt_card.le
  have hf0 : f ≠ 0 := hf.ne_zero
  have hr : (AdjoinRoot.root f) ^ p = 1 := by
    have h0 : AdjoinRoot.mk f (X ^ p - 1) = 0 := AdjoinRoot.mk_eq_zero.2 hdvd
    rw [map_sub, map_pow, map_one, AdjoinRoot.mk_X] at h0
    exact sub_eq_zero.1 h0
  have hr1 : AdjoinRoot.root f ≠ 1 := by
    intro h
    apply hnot
    apply AdjoinRoot.mk_eq_zero.1
    rw [map_sub, map_one, AdjoinRoot.mk_X]
    exact sub_eq_zero.2 h
  have hordr : orderOf (AdjoinRoot.root f) = p := orderOf_eq_prime hr hr1
  have ne0 : AdjoinRoot.root f ≠ 0 := by
    intro h
    rw [h, zero_pow hp.out.ne_zero] at hr
    exact zero_ne_one hr
  have hmf : Module.Finite K (AdjoinRoot f) := (AdjoinRoot.powerBasis hf0).finite
  have hfin : Finite (AdjoinRoot f) := Module.finite_of_finite K
  let : Fintype (AdjoinRoot f) := Fintype.ofFinite _
  have hcard : Fintype.card (AdjoinRoot f) = Fintype.card K ^ f.natDegree := by
    rw [Module.card_eq_pow_finrank (K := K), (AdjoinRoot.powerBasis hf0).finrank,
      AdjoinRoot.powerBasis_dim hf0]
  have hpow : (AdjoinRoot.root f) ^ (Fintype.card (AdjoinRoot f) - 1) = 1 :=
    FiniteField.pow_card_sub_one_eq_one _ ne0
  have hdiv : p ∣ Fintype.card (AdjoinRoot f) - 1 := by
    rw [← hordr]
    exact orderOf_dvd_iff_pow_eq_one.2 hpow
  rw [hcard] at hdiv
  exact (dvd_pow_sub_one_iff hq hord).1 hdiv

theorem le_natDegree_or_sub_one_dvd {p n : ℕ} [hp : Fact p.Prime]
    (hord : orderOf ((Fintype.card K : ℕ) : ZMod p) = n)
    {f : K[X]} (hdvd : f ∣ X ^ p - 1) (hf0 : f ≠ 0) (hu : ¬ IsUnit f) :
    n ≤ f.natDegree ∨ X - 1 ∣ f := by
  obtain ⟨f0, hf0i, hf0d⟩ := WfDvdMonoid.exists_irreducible_factor hu hf0
  by_cases h1 : f0 ∣ X - 1
  · right
    have hass : Associated f0 (X - 1) := hf0i.associated_of_dvd irreducible_X_sub_one h1
    exact dvd_trans hass.symm.dvd hf0d
  · left
    have hdvd' : f0 ∣ X ^ p - 1 := dvd_trans hf0d hdvd
    have h2 := natDegree_of_irreducible_dvd hord hf0i hdvd' h1
    have hpos : 0 < f0.natDegree := hf0i.natDegree_pos
    have hle : f0.natDegree ≤ f.natDegree := natDegree_le_of_dvd hf0d hf0
    exact le_trans (Nat.le_of_dvd hpos h2) hle

theorem irreducible_of_squarefree_of_natDegree_le {p n : ℕ} [hp : Fact p.Prime]
    (hord : orderOf ((Fintype.card K : ℕ) : ZMod p) = n)
    {μ : K[X]} (hm : μ.Monic) (hμ1 : μ ≠ 1) (hsq : Squarefree μ)
    (hdvd : μ ∣ X ^ p - 1) (hdeg : μ.natDegree ≤ n) : Irreducible μ := by
  rw [hm.irreducible_iff_natDegree]
  refine ⟨hμ1, fun f g hf hg hfg => ?_⟩
  by_contra hcon
  have hcon' : f.natDegree ≠ 0 ∧ g.natDegree ≠ 0 := not_or.1 hcon
  have hsum : f.natDegree + g.natDegree = μ.natDegree := by
    rw [← hfg, Polynomial.natDegree_mul hf.ne_zero hg.ne_zero]
  have hfd : f ∣ μ := ⟨g, hfg.symm⟩
  have hgd : g ∣ μ := ⟨f, by rw [← hfg, mul_comm]⟩
  have hfu : ¬ IsUnit f := fun hu => hcon'.1 (natDegree_eq_zero_of_isUnit hu)
  have hgu : ¬ IsUnit g := fun hu => hcon'.2 (natDegree_eq_zero_of_isUnit hu)
  have hf' := le_natDegree_or_sub_one_dvd hord (dvd_trans hfd hdvd) hf.ne_zero hfu
  have hg' := le_natDegree_or_sub_one_dvd hord (dvd_trans hgd hdvd) hg.ne_zero hgu
  have hX1f : X - 1 ∣ f := by
    rcases hf' with h | h
    · omega
    · exact h
  have hX1g : X - 1 ∣ g := by
    rcases hg' with h | h
    · omega
    · exact h
  have hsq' : (X - 1) * (X - 1) ∣ μ := by
    rw [← hfg]
    exact mul_dvd_mul hX1f hX1g
  exact irreducible_X_sub_one.not_isUnit (hsq _ hsq')

theorem natCast_ne_zero_of_not_dvd {p : ℕ} [hp : Fact p.Prime]
    (hnd : ¬ p ∣ Fintype.card K) : (p : K) ≠ 0 := by
  intro h
  have h1 : ringChar K ∣ p := (CharP.cast_eq_zero_iff K (ringChar K) p).1 h
  have hq0 : ((Fintype.card K : ℕ) : K) = 0 := FiniteField.cast_card_eq_zero K
  rcases (Nat.dvd_prime hp.out).1 h1 with h2 | h2
  · exact CharP.ringChar_ne_one h2
  · apply hnd
    rw [← h2]
    exact (CharP.cast_eq_zero_iff K (ringChar K) _).1 hq0

theorem squarefree_of_dvd_X_pow_sub_one {p : ℕ} [hp : Fact p.Prime]
    (hnd : ¬ p ∣ Fintype.card K) {μ : K[X]} (hdvd : μ ∣ X ^ p - 1) : Squarefree μ :=
  ((X_pow_sub_one_separable_iff.2 (natCast_ne_zero_of_not_dvd hnd)).of_dvd hdvd).squarefree


theorem isCyclic_units_of_finite (L : Type*) [Field L] [Finite L] : IsCyclic Lˣ := by
  infer_instance

theorem minpoly_irreducible_natDegree_eq {p n : ℕ} [hp : Fact p.Prime] (hn : 2 ≤ n)
    (hord : orderOf ((Fintype.card K : ℕ) : ZMod p) = n)
    {M : Matrix (Fin n) (Fin n) K} (hM : M ^ p = 1) (hM1 : M ≠ 1) :
    Irreducible (minpoly K M) ∧ (minpoly K M).natDegree = n := by
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hnd : ¬ p ∣ Fintype.card K := not_dvd_of_orderOf (by omega) hord
  have hdvd : minpoly K M ∣ X ^ p - 1 := minpoly.dvd K M (by simp [hM])
  have hint : IsIntegral K M :=
    ⟨M.charpoly, Matrix.charpoly_monic M, by
      simpa [Polynomial.aeval_def] using Matrix.aeval_self_charpoly M⟩
  have hmonic : (minpoly K M).Monic := minpoly.monic hint
  have hμ1 : minpoly K M ≠ 1 := by
    intro h
    have h0 := minpoly.aeval K M
    rw [h, map_one] at h0
    exact one_ne_zero h0
  have hdeg : (minpoly K M).natDegree ≤ n := by
    have h2 := natDegree_le_of_dvd (Matrix.minpoly_dvd_charpoly M) (Matrix.charpoly_monic M).ne_zero
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at h2
    exact h2
  have hsq := squarefree_of_dvd_X_pow_sub_one hnd hdvd
  have hirr := irreducible_of_squarefree_of_natDegree_le hord hmonic hμ1 hsq hdvd hdeg
  have hdegeq : n ≤ (minpoly K M).natDegree := by
    rcases le_natDegree_or_sub_one_dvd hord hdvd hmonic.ne_zero hirr.not_isUnit with h | h
    · exact h
    · exfalso
      have hX1m : (X - 1 : K[X]).Monic := by simpa using monic_X_sub_C (1 : K)
      have hass : Associated (X - 1 : K[X]) (minpoly K M) :=
        irreducible_X_sub_one.associated_of_dvd hirr h
      have heq : (X - 1 : K[X]) = minpoly K M := eq_of_monic_of_associated hX1m hmonic hass
      apply hM1
      have h0 : aeval M (X - 1 : K[X]) = 0 := by
        rw [heq]
        exact minpoly.aeval K M
      simpa [sub_eq_zero] using h0
  exact ⟨hirr, le_antisymm hdeg hdegeq⟩


theorem mulVec_bijective_of_irreducible {n : ℕ} (hn : 1 ≤ n) {μ : K[X]}
    (hμ : Irreducible μ) (hdeg : μ.natDegree = n)
    {M : Matrix (Fin n) (Fin n) K}
    (ψ : AdjoinRoot μ →+* Matrix (Fin n) (Fin n) K)
    (_hψ : ∀ f : K[X], ψ (AdjoinRoot.mk μ f) = aeval M f) :
    Function.Bijective (fun a : AdjoinRoot μ => ψ a *ᵥ (Pi.single ⟨0, hn⟩ 1 : Fin n → K)) := by
  have : Fact (Irreducible μ) := ⟨hμ⟩
  have hμ0 : μ ≠ 0 := hμ.ne_zero
  have hmf : Module.Finite K (AdjoinRoot μ) := (AdjoinRoot.powerBasis hμ0).finite
  have hfin : Finite (AdjoinRoot μ) := Module.finite_of_finite K
  let : Fintype (AdjoinRoot μ) := Fintype.ofFinite _
  set v : Fin n → K := Pi.single ⟨0, hn⟩ 1 with hv
  have hinj : Function.Injective (fun a : AdjoinRoot μ => ψ a *ᵥ v) := by
    intro a b hab
    have hab' : ψ a *ᵥ v = ψ b *ᵥ v := hab
    by_contra hne
    have hc : a - b ≠ 0 := sub_ne_zero.2 hne
    have hcv : ψ (a - b) *ᵥ v = 0 := by
      rw [map_sub, Matrix.sub_mulVec, hab', sub_self]
    have hv0 : v = 0 := by
      calc v = ψ 1 *ᵥ v := by rw [map_one, Matrix.one_mulVec]
        _ = (ψ (a - b)⁻¹ * ψ (a - b)) *ᵥ v := by
          rw [← map_mul, inv_mul_cancel₀ hc]
        _ = ψ (a - b)⁻¹ *ᵥ (ψ (a - b) *ᵥ v) := by rw [Matrix.mulVec_mulVec]
        _ = 0 := by rw [hcv, Matrix.mulVec_zero]
    have h0 := congrFun hv0 ⟨0, hn⟩
    simp [v] at h0
  have hcardL : Fintype.card (AdjoinRoot μ) = Fintype.card K ^ n := by
    rw [Module.card_eq_pow_finrank (K := K), (AdjoinRoot.powerBasis hμ0).finrank,
      AdjoinRoot.powerBasis_dim hμ0, hdeg]
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨hinj, ?_⟩
  rw [hcardL]
  simp

theorem eq_image_of_commute {n : ℕ} (hn : 2 ≤ n) {μ : K[X]} (hμ : Irreducible μ)
    (hdeg : μ.natDegree = n) {M : Matrix (Fin n) (Fin n) K}
    (ψ : AdjoinRoot μ →+* Matrix (Fin n) (Fin n) K)
    (hψ : ∀ f : K[X], ψ (AdjoinRoot.mk μ f) = aeval M f)
    {h : Matrix (Fin n) (Fin n) K} (hMh : h * M = M * h) : ∃ a, ψ a = h := by
  have hn1 : 1 ≤ n := by omega
  have : Fact (Irreducible μ) := ⟨hμ⟩
  have hsurj := (mulVec_bijective_of_irreducible hn1 hμ hdeg ψ hψ).2
  have hadj : Algebra.adjoin K {M} ≤ Subalgebra.centralizer K {h} := by
    apply Algebra.adjoin_le
    intro x hx
    rw [Set.mem_singleton_iff.1 hx, SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.1 hg]
    exact hMh
  have hpsi : ∀ b, h * ψ b = ψ b * h := by
    intro b
    obtain ⟨f, rfl⟩ := (AdjoinRoot.mk_surjective : Function.Surjective (AdjoinRoot.mk μ)) b
    have hmem : ψ (AdjoinRoot.mk μ f) ∈ Algebra.adjoin K {M} := by
      rw [hψ]; exact Polynomial.aeval_mem_adjoin_singleton K M
    exact (Subalgebra.mem_centralizer_iff K).1 (hadj hmem) h (Set.mem_singleton h)
  obtain ⟨a0, ha0⟩ := hsurj (h *ᵥ (Pi.single ⟨0, hn1⟩ 1 : Fin n → K))
  have ha0' : ψ a0 *ᵥ (Pi.single ⟨0, hn1⟩ 1 : Fin n → K) = h *ᵥ (Pi.single ⟨0, hn1⟩ 1 : Fin n → K) :=
    ha0
  refine ⟨a0, Matrix.ext_of_mulVec_single fun j => ?_⟩
  obtain ⟨b, hb⟩ := hsurj (Pi.single j 1 : Fin n → K)
  have hb' : ψ b *ᵥ (Pi.single ⟨0, hn1⟩ 1 : Fin n → K) = Pi.single j 1 := hb
  rw [← hb']
  calc ψ a0 *ᵥ (ψ b *ᵥ (Pi.single ⟨0, hn1⟩ 1 : Fin n → K))
      = (ψ a0 * ψ b) *ᵥ (Pi.single ⟨0, hn1⟩ 1 : Fin n → K) := by rw [Matrix.mulVec_mulVec]
    _ = (ψ b * ψ a0) *ᵥ (Pi.single ⟨0, hn1⟩ 1 : Fin n → K) := by
          rw [← map_mul, ← map_mul, mul_comm a0 b]
    _ = ψ b *ᵥ (ψ a0 *ᵥ (Pi.single ⟨0, hn1⟩ 1 : Fin n → K)) := by rw [Matrix.mulVec_mulVec]
    _ = ψ b *ᵥ (h *ᵥ (Pi.single ⟨0, hn1⟩ 1 : Fin n → K)) := by rw [ha0']
    _ = (ψ b * h) *ᵥ (Pi.single ⟨0, hn1⟩ 1 : Fin n → K) := by rw [Matrix.mulVec_mulVec]
    _ = (h * ψ b) *ᵥ (Pi.single ⟨0, hn1⟩ 1 : Fin n → K) := by rw [(hpsi b).symm]
    _ = h *ᵥ (ψ b *ᵥ (Pi.single ⟨0, hn1⟩ 1 : Fin n → K)) := by rw [Matrix.mulVec_mulVec]

theorem isCyclic_centralizer_of_orderOf_eq (K : Type*) [Field K] [Fintype K] {n p : ℕ}
    (hp : p.Prime) (hn : 2 ≤ n) (hord : orderOf ((Fintype.card K : ℕ) : ZMod p) = n)
    {g : Matrix.SpecialLinearGroup (Fin n) K} (hg : orderOf g = p) :
    IsCyclic (Subgroup.centralizer ({g} : Set (Matrix.SpecialLinearGroup (Fin n) K))) := by
  have := Fact.mk hp
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  set M : Matrix (Fin n) (Fin n) K := (g : Matrix (Fin n) (Fin n) K) with hMdef
  have hMp : M ^ p = 1 := by
    have h1 : g ^ p = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
    have h2 := congrArg (fun x : Matrix.SpecialLinearGroup (Fin n) K =>
      (x : Matrix (Fin n) (Fin n) K)) h1
    simpa [hMdef, Matrix.SpecialLinearGroup.coe_pow] using h2
  have hM1 : M ≠ 1 := by
    intro h1
    have hg1 : g = 1 := Subtype.ext (Matrix.ext fun i j => congrFun (congrFun h1 i) j)
    have h2 : orderOf g = 1 := by rw [hg1, orderOf_one]
    rw [hg] at h2
    exact hp.one_lt.ne' h2
  obtain ⟨hirr, hdeg⟩ := minpoly_irreducible_natDegree_eq hn hord hMp hM1
  have hroot := minpoly.aeval K M
  generalize minpoly K M = μ at hirr hdeg hroot
  have : Fact (Irreducible μ) := ⟨hirr⟩
  have hμ0 : μ ≠ 0 := hirr.ne_zero
  have hmf : Module.Finite K (AdjoinRoot μ) := (AdjoinRoot.powerBasis hμ0).finite
  have hfin : Finite (AdjoinRoot μ) := Module.finite_of_finite K
  have H : ∀ a ∈ Ideal.span ({μ} : Set K[X]), (Polynomial.aeval M).toRingHom a = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 ha
    simp [hroot]
  let ψ : AdjoinRoot μ →+* Matrix (Fin n) (Fin n) K :=
    Ideal.Quotient.lift (Ideal.span ({μ} : Set K[X])) (Polynomial.aeval M).toRingHom H
  have hψ : ∀ f : K[X], ψ (AdjoinRoot.mk μ f) = aeval M f := fun f => rfl
  have hψinj : Function.Injective ψ := ψ.injective
  have hrange : ∀ c : Matrix.SpecialLinearGroup (Fin n) K, c ∈ Subgroup.centralizer {g} →
      ∃ a, ψ a = (c : Matrix (Fin n) (Fin n) K) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff] at hc
    have h2 := congrArg (fun x : Matrix.SpecialLinearGroup (Fin n) K =>
      (x : Matrix (Fin n) (Fin n) K)) (hc g (Set.mem_singleton g))
    simp only [Matrix.SpecialLinearGroup.coe_mul] at h2
    exact eq_image_of_commute hn hirr hdeg ψ hψ h2.symm
  have hdetne : ∀ c : Matrix.SpecialLinearGroup (Fin n) K, (c : Matrix (Fin n) (Fin n) K) ≠ 0 := by
    intro c h0
    have hd := Matrix.SpecialLinearGroup.det_coe c
    rw [h0, Matrix.det_zero] at hd
    exact zero_ne_one hd
  set H := Subgroup.centralizer ({g} : Set (Matrix.SpecialLinearGroup (Fin n) K)) with hH
  have hne : ∀ c : H, Function.invFun ψ (c : Matrix (Fin n) (Fin n) K) ≠ 0 := by
    intro c h0
    have e := Function.invFun_eq (hrange c.1 c.2)
    rw [h0, map_zero] at e
    exact hdetne c.1 e.symm
  let φ : H →* (AdjoinRoot μ)ˣ :=
    MonoidHom.mk' (fun c : H => Units.mk0 (Function.invFun ψ (c : Matrix (Fin n) (Fin n) K)) (hne c))
      (by
        intro c1 c2
        apply Units.ext
        simp only [Units.val_mul, Units.val_mk0]
        have key : ((((c1 * c2 : H) : Matrix.SpecialLinearGroup (Fin n) K)) :
            Matrix (Fin n) (Fin n) K) =
            ψ (Function.invFun ψ ((c1 : Matrix.SpecialLinearGroup (Fin n) K) :
              Matrix (Fin n) (Fin n) K) * Function.invFun ψ ((c2 : Matrix.SpecialLinearGroup (Fin n) K) :
              Matrix (Fin n) (Fin n) K)) := by
          rw [map_mul, Function.invFun_eq (hrange c1.1 c1.2), Function.invFun_eq (hrange c2.1 c2.2)]
          simp [Matrix.SpecialLinearGroup.coe_mul]
        rw [key]
        exact Function.leftInverse_invFun hψinj _)
  have hφinj : Function.Injective φ := by
    intro c1 c2 h12
    have h' : Function.invFun ψ (c1 : Matrix (Fin n) (Fin n) K) =
        Function.invFun ψ (c2 : Matrix (Fin n) (Fin n) K) := by
      have := congrArg Units.val h12
      simpa [φ] using this
    have e1 := Function.invFun_eq (hrange c1.1 c1.2)
    have e2 := Function.invFun_eq (hrange c2.1 c2.2)
    have hM' : (c1 : Matrix (Fin n) (Fin n) K) = (c2 : Matrix (Fin n) (Fin n) K) :=
      calc (c1 : Matrix (Fin n) (Fin n) K) = ψ (Function.invFun ψ (c1 : Matrix (Fin n) (Fin n) K)) :=
            e1.symm
        _ = ψ (Function.invFun ψ (c2 : Matrix (Fin n) (Fin n) K)) := by rw [h']
        _ = (c2 : Matrix (Fin n) (Fin n) K) := e2
    exact Subtype.ext (Subtype.ext (Matrix.ext fun i j => congrFun (congrFun hM' i) j))
  exact isCyclic_of_injective φ hφinj

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
