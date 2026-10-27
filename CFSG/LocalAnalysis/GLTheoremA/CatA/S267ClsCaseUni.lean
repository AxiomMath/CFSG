module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsCaseLin
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsAutFieldUni

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.H81Orth.Wt
open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData sesqUnitaryGroup)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open scoped IsMulCommutative

section Form

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem unitForm_separatingLeft (σ : K →+* K) :
    (unitForm σ : (ι → K) →ₗ[K] (ι → K) →ₛₗ[σ] K).SeparatingLeft := by
  intro x hx
  funext i
  have h := hx (Pi.single i 1)
  simpa [unitForm_apply, dotProduct, Pi.single_apply] using h

theorem unitForm_ne_zero [Nonempty ι] (σ : K →+* K) :
    (unitForm σ : (ι → K) →ₗ[K] (ι → K) →ₛₗ[σ] K) ≠ 0 := by
  intro h
  obtain ⟨i⟩ := ‹Nonempty ι›
  have h1 := congrArg
    (fun β : (ι → K) →ₗ[K] (ι → K) →ₛₗ[σ] K => β (Pi.single i 1) (Pi.single i 1)) h
  simp [unitForm_apply, dotProduct, Pi.single_apply] at h1

theorem mul_map_eq_one_of_scalar_mem [Nonempty ι] (σ : K →+* K) {c : Kˣ}
    (hc : Matrix.GeneralLinearGroup.scalar ι c ∈ isomGL (unitForm σ)) : (c : K) * σ c = 1 := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  have h := (mem_isomGL.mp hc) (Pi.single i 1) (Pi.single i 1)
  rw [← glEquiv_apply, glEquiv_scalar_apply] at h
  have h' : σ (c : K) * c = 1 := by simpa [unitForm_apply, dotProduct, Pi.single_apply] using h
  rw [mul_comm]
  exact h'

end Form

section Small

variable {K : Type} [Field K] {ℓ f : ℕ}

theorem pow_succ_eq_one_of_scalar_mem {n : ℕ} [NeZero n] (h : UnitaryFieldData ℓ f K) {c : Kˣ}
    (hc : Matrix.GeneralLinearGroup.scalar (Fin n) c ∈ isomGL (unitForm (ι := Fin n) h.bar)) :
    c ^ (ℓ ^ f + 1) = 1 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩
  have h1 := mul_map_eq_one_of_scalar_mem h.bar hc
  rw [UnitaryFieldData.bar_apply] at h1
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one, pow_succ', h1]

theorem not_dvd_card_U_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) {q : ℕ}
    (hq3 : ((q : ℕ) : ZMod p) = 3) : ¬ p ∣ q * ((q + 1) * (q ^ 2 - 1)) := by
  intro h
  have hq1 : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with h0 | h0
    · rw [h0, Nat.cast_zero] at hq3
      have : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast hq3.symm
      rw [ZMod.natCast_eq_zero_iff] at this
      exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 this) hp3
    · exact h0
  have h3 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
  have hdvd : p ∣ 2 ^ 5 * 3 := by
    have h' := (ZMod.natCast_eq_zero_iff _ p).2 h
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_sub h3, Nat.cast_pow, Nat.cast_one,
      hq3] at h'
    rw [← ZMod.natCast_eq_zero_iff,
      show ((2 ^ 5 * 3 : ℕ) : ZMod p) = 3 * ((3 + 1) * (3 ^ 2 - 1)) by push_cast; ring]
    exact h'
  rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h)

theorem dvd_card_U_two_of_plane {n : ℕ} (h : UnitaryFieldData ℓ f K) {p : ℕ} (hp : p.Prime)
    {M N : Submodule K (Fin n → K)} (hM : Module.finrank K M = 2)
    (hnd : ∀ m ∈ M, (∀ m' ∈ M, unitForm h.bar m m' = 0) → m = 0) {x : GL (Fin n) K}
    (hx : x ∈ blkSub (unitForm h.bar) M N) (hxp : x ^ p = 1)
    (hx1 : ∃ m ∈ M, glEquiv x m ≠ m) :
    p ∣ ℓ ^ f * ((ℓ ^ f + 1) * ((ℓ ^ f) ^ 2 - 1)) := by
  classical
  haveI : Finite K := h.finite
  set B := unitFormU (σ := h.bar) h.bar (fun _ => rfl) M with hB
  have hBs : B.IsSymm := unitFormU_isSymm h.bar (fun _ => rfl) h.bar_bar M
  have hBl : B.SeparatingLeft := (unitFormU_nondegenerate h.bar (fun _ => rfl) h.bar_bar hnd).1
  have hcard := (CFSG.LinearGroups.unitary_full_group_order h hBs hBl hM (by norm_num)).1
  set g := resU (unitForm h.bar) M N ⟨x, hx⟩ with hg
  have hgp : g ^ p = 1 := by
    have h1 : (⟨x, hx⟩ : blkSub (unitForm h.bar) M N) ^ p = 1 := Subtype.ext (by simpa using hxp)
    rw [hg, ← map_pow, h1, map_one]
  have hg1 : g ≠ 1 := by
    obtain ⟨m, hm, hxm⟩ := hx1
    intro h1
    apply hxm
    have h2 := congrArg (fun e : M ≃ₗ[K] M => ((e ⟨m, hm⟩ : M) : Fin n → K)) h1
    simpa [hg, coe_resU_apply] using h2
  set g' : LinearMap.GeneralLinearGroup K M :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K M).symm g with hg'
  have hg'm : ∀ m : M, (g' : M →ₗ[K] M) m = g m := fun m => by
    rw [hg']
    rfl
  have hmem : g' ∈ sesqUnitaryGroup B := by
    intro m m'
    rw [hg'm, hg'm, unitFormU_apply, unitFormU_apply, hg, coe_resU_apply, coe_resU_apply]
    have := (mem_isomGL.mp hx.1) (m' : Fin n → K) (m : Fin n → K)
    rwa [← glEquiv_apply, ← glEquiv_apply] at this
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf (⟨g', hmem⟩ : sesqUnitaryGroup B) = p := by
    refine orderOf_eq_prime ?_ fun h1 => hg1 ?_
    · apply Subtype.ext
      show (g' : LinearMap.GeneralLinearGroup K M) ^ p = 1
      rw [hg', ← map_pow, hgp, map_one]
    · have h2 := congrArg (fun y : sesqUnitaryGroup B =>
        LinearMap.GeneralLinearGroup.generalLinearEquiv K M (y : LinearMap.GeneralLinearGroup K M))
        h1
      simpa [hg'] using h2
  have hdvd := orderOf_dvd_natCard
    (⟨g', hmem⟩ : sesqUnitaryGroup B)
  rw [hord] at hdvd
  have hq1 : 1 ≤ (ℓ ^ f) ^ 2 := Nat.one_le_pow _ _ (Nat.one_le_pow _ _ h.prime.pos)
  have hcard' : Nat.card (sesqUnitaryGroup B) =
      ℓ ^ f * ((ℓ ^ f + 1) * ((ℓ ^ f) ^ 2 - 1)) := by
    have hI : Finset.Icc 1 2 = {1, 2} := by decide
    rw [hI, Finset.prod_pair (by norm_num), show 2 * (2 - 1) / 2 = 1 by norm_num, pow_one]
      at hcard
    have h3 : (((ℓ ^ f) ^ 2 - 1 : ℕ) : ℤ) = ((ℓ ^ f : ℕ) : ℤ) ^ 2 - 1 := by
      rw [Nat.cast_sub hq1]
      push_cast
      ring
    exact_mod_cast (by rw [hcard]; push_cast [Nat.cast_sub hq1]; ring :
      ((Nat.card (sesqUnitaryGroup B) : ℕ) : ℤ) =
        ((ℓ ^ f * ((ℓ ^ f + 1) * ((ℓ ^ f) ^ 2 - 1)) : ℕ) : ℤ))
  rwa [hcard'] at hdvd

end Small

section Unitary

variable {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

theorem concl_uni
    (hp : p.Prime) (hp2 : p ≠ 2) {ℓ f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) (hℓ2 : ℓ ≠ 2) (hℓp : ℓ ≠ p) [hSn : S.Normal]
    (hcore : GLAPPrimeCore p ↥S = ⊥) (hZ : Subgroup.center ↥S = ⊥) (hB : IsElemAbelian p B)
    (hrank : p ^ GLATwoLocalRank p Ω ≤ Nat.card B) (h4 : p ^ 4 ≤ Nat.card B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p) {n : ℕ} (hn : 3 ≤ n)
    (hdiag : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1)) (e : PSimple p S ≃* StatedProj (StatedSU n (ℓ ^ f) K))
    {Q : TauCeti.PrimePower} (hQℓ : Q.p = ℓ) (hQK : Q.card = ℓ ^ f)
    {hv : (TauCeti.LieTypeIndex.twistedA (n - 1) Q).Valid}
    (eL : Nonempty (PSimple p S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA (n - 1) Q, hv⟩).Group))
    (hHq : ∃ (K' : Type) (_ : Group K') (_ : Finite K'),
      Nonempty (PQuot p (⊤ : Subgroup K') ≃* ↥S) ∧ GLATwoLocalRank ℓ K' ≤ CFSG.Open.pRank p B) :
    S267ConcA p S B ∨ S267ConcBCDE p ℓ S B := by
  classical
  haveI : Finite K := h.finite
  haveI : NeZero n := ⟨by omega⟩
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  haveI : CharP K ℓ := h.charP
  have hℓ := h.prime
  have hcharne : ∀ m : ℕ, m.Prime → m ≠ ℓ → (m : K) ≠ 0 := by
    intro m hm hmℓ h0
    exact hmℓ ((Nat.prime_dvd_prime_iff_eq hℓ hm).1 ((CharP.cast_eq_zero_iff K ℓ m).1 h0)).symm
  have h2K : (2 : K) ≠ 0 := by exact_mod_cast hcharne 2 Nat.prime_two (Ne.symm hℓ2)
  have hpK : (p : K) ≠ 0 := hcharne p hp (Ne.symm hℓp)
  have hp3' : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨φ, hφS, hφk, hC, θ, hθ, hθel, hθk, hθ1, hsplit⟩ :=
    ModelGen.exists_clsData_uni h hp hp2 hcore hZ hn (fun h' => hℓ2 (by
      have := h'.2
      have h2 : ℓ ∣ 2 := this ▸ dvd_pow_self ℓ (by have := h.one_le; omega)
      exact (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 h2)) (Ne.symm hℓp) hdiag e hB
  obtain ⟨Dat, hform1⟩ : ∃ D : ClsInner p S B (StatedSU n (ℓ ^ f) K) (unitForm (ι := Fin n) h.bar),
      FieldElt p S B D.φ (unitForm (ι := Fin n) h.bar) D.θ D.b D.A D.σ →
        ∀ u v, unitForm h.bar (ModelGen.semiMap D.A D.σ u) (ModelGen.semiMap D.A D.σ v) =
          D.σ (unitForm h.bar u v) := by
    rcases hsplit with hBB | ⟨b, hb, hbN, hBb, hbinf, A, σ, hA, hact, hform, hfix⟩
    · exact ⟨⟨φ, hφS, hφk, hC, θ, hθ, hθel, hθk, hθ1, 1, 1, RingEquiv.refl K, Or.inl hBB⟩,
        fun hF => absurd (one_mem _) hF.2.1⟩
    · refine ⟨⟨φ, hφS, hφk, hC, θ, hθ, hθel, hθk, hθ1, b, A, σ,
        Or.inr ⟨hb, hbN, hBb, hbinf, hact, hform, hfix⟩⟩, fun _ u v => ?_⟩
      show unitForm h.bar (ModelGen.semiMap A σ u) (ModelGen.semiMap A σ v) =
        σ (unitForm h.bar u v)
      rw [ModelGen.semiMap_apply, ModelGen.semiMap_apply, ModelGen.unitForm_mulVec_of_mem h hA,
        ModelGen.unitForm_map, ModelGen.unitForm_mulVec_of_mem h (inv_mem hA)]
  have hnd0 : ∀ U : Submodule K (Fin n → K),
      (unitForm (ι := Fin n) h.bar = 0 ∨ ∀ u ∈ U, (∀ u' ∈ U, unitForm h.bar u u' = 0) → u = 0) →
      ∀ u ∈ U, (∀ u' ∈ U, unitForm h.bar u u' = 0) → u = 0 := fun U hU =>
    hU.resolve_left (unitForm_ne_zero h.bar)
  have hSU : CFSG.ClassicalGroups.UnitaryFlag.gramSU h (1 : Matrix (Fin n) (Fin n) K) =
      StatedSU n (ℓ ^ f) K := (CFSG.ClassicalGroups.UnitaryFlag.unitarySU_eq_gramSU h n).symm
  have hblk : ∀ U W : Submodule K (Fin n → K), IsCompl U W →
      (∀ u ∈ U, ∀ w ∈ W, unitForm (ι := Fin n) h.bar u w = 0 ∧ unitForm h.bar w u = 0) →
      (unitForm (ι := Fin n) h.bar = 0 ∨ ∀ u ∈ U, (∀ u' ∈ U, unitForm h.bar u u' = 0) → u = 0) →
      (3 ≤ Module.finrank K U ∨ (Module.finrank K U = 2 ∧ ℓ ^ f ≠ 3)) →
      blkI (unitForm (ι := Fin n) h.bar) U W ≤ StatedSU n (ℓ ^ f) K ∧
      CFSG.Open.IsQuasisimple ↥(blkI (unitForm (ι := Fin n) h.bar) U W) ∧
      (∀ x ∈ blkSub (unitForm (ι := Fin n) h.bar) U W, orderOf x = p →
        p ∣ Nat.card ↥(blkI (unitForm (ι := Fin n) h.bar) U W)) ∧
      (∀ y : GL (Fin n) K, (∀ u ∈ U, glEquiv y u ∈ U) →
        (∀ j ∈ blkI (unitForm (ι := Fin n) h.bar) U W, y * j = j * y) →
        ∃ c : K, ∀ u ∈ U, glEquiv y u = c • u) ∧
      (∀ (A : GL (Fin n) K) (σ : K ≃+* K), orderOf σ = p →
        (∀ u ∈ U, ModelGen.semiMap A σ u ∈ U) →
        ∀ y : GL (Fin n) K, (∀ u ∈ U, glEquiv y u ∈ U) → ∀ k : ℕ, 0 < k → k < p →
          ¬ ∀ j ∈ blkI (unitForm (ι := Fin n) h.bar) U W,
            y * (ModelGen.semiConj A σ ^ k) j * y⁻¹ = j) := by
    intro U W hUW horth hnd hdim
    have hnd' := hnd0 U hnd
    exact ⟨hSU ▸ blkI_le_gramSU h U W, isQuasisimple_blkI_unitForm h hℓ2 hUW horth hnd' hdim,
      fun x hx hxp => dvd_card_blkI_unitForm h hℓ2 hUW horth hnd' hdim hp hx hxp,
      fun y hyU hy => exists_smul_of_commute_blkI_unitForm h hℓ2 hUW horth hnd' hdim hyU hy,
      fun A σ hσ hU y hyU k hk0 hkp =>
        not_forall_semiConj_pow_unitForm h hℓ2 hUW horth hnd' hdim hp hp2 hσ hU hyU hk0 hkp⟩
  have hpf_of : ∀ σ : K ≃+* K, orderOf σ = p → p ∣ f := fun σ hσ =>
    (unitary_card_fixedSubfield (U := (⊤ : Submodule K (Fin n → K))) (A := (1 : GL (Fin n) K))
      h hp hp2 hσ fun _ _ => trivial).1
  have hpow_mod : ∀ σ : K ≃+* K, orderOf σ = p →
      ((ℓ ^ f : ℕ) : ZMod p) = ((ℓ ^ (f / p) : ℕ) : ZMod p) := by
    intro σ hσ
    have hpf := hpf_of σ hσ
    haveI := Fact.mk hp
    conv_lhs => rw [show f = f / p * p from (Nat.div_mul_cancel hpf).symm, pow_mul]
    rw [Nat.cast_pow, ZMod.pow_card]
  have hq3 : ℓ ^ f = 3 → ℓ = 3 := fun h3 =>
    (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 (h3 ▸ dvd_pow_self ℓ
      (by have := h.one_le; omega))
  have hQscal : (∃ c : Kˣ, c ≠ 1 ∧ c ^ p = 1 ∧ Matrix.GeneralLinearGroup.scalar (Fin n) c ∈
      isomGL (unitForm (ι := Fin n) h.bar)) →
      ℓ ^ f ≠ 3 ∧ (FieldElt p S B Dat.φ (unitForm (ι := Fin n) h.bar) Dat.θ Dat.b Dat.A Dat.σ →
        ℓ ^ (f / p) ≠ 3) := by
    rintro ⟨c, hc1, hcp, hcβ⟩
    haveI := Fact.mk hp
    have hd : p ∣ ℓ ^ f + 1 := by
      rw [← orderOf_eq_prime hcp hc1]
      exact orderOf_dvd_of_pow_eq_one (pow_succ_eq_one_of_scalar_mem h hcβ)
    have hd' : ((ℓ ^ f + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).2 hd
    have hne : ∀ m : ℕ, ((m : ℕ) : ZMod p) = 3 → ((m + 1 : ℕ) : ZMod p) ≠ 0 := by
      intro m hm h0
      rw [Nat.cast_add, hm, Nat.cast_one] at h0
      have : ((4 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
      rw [ZMod.natCast_eq_zero_iff] at this
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
        (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 from this)))
    refine ⟨fun h3 => hne _ (by rw [h3]; norm_num) hd', fun hF h3 => hne _ ?_ hd'⟩
    rw [hpow_mod Dat.σ hF.2.2.2.2.1.1, h3]
    norm_num
  have hQdim2 : ∀ (M N : Submodule K (Fin n → K)) (x : GL (Fin n) K), Module.finrank K M = 2 →
      (unitForm (ι := Fin n) h.bar = 0 ∨ ∀ m ∈ M, (∀ m' ∈ M, unitForm h.bar m m' = 0) → m = 0) →
      x ∈ blkSub (unitForm (ι := Fin n) h.bar) M N → x ^ p = 1 → (∃ m ∈ M, glEquiv x m ≠ m) →
      ℓ ^ f ≠ 3 ∧ (FieldElt p S B Dat.φ (unitForm (ι := Fin n) h.bar) Dat.θ Dat.b Dat.A Dat.σ →
        ℓ ^ (f / p) ≠ 3) := by
    intro M N x hM hndM hx hxp hx1
    have hd := dvd_card_U_two_of_plane h hp hM (hnd0 M hndM) hx hxp hx1
    refine ⟨fun h3 => ?_, fun hF h3 => ?_⟩
    · rw [h3] at hd
      exact not_dvd_card_U_two hp hp2 (fun hp3 => hℓp ((hq3 h3).trans hp3.symm)) (by norm_num) hd
    · refine not_dvd_card_U_two hp hp2 (fun hp3 => hℓp ?_) ?_ hd
      · have h3' : ℓ ∣ 3 := h3 ▸ dvd_pow_self ℓ (by
          have hpf := hpf_of _ hF.2.2.2.2.1.1
          have := Nat.div_pos (Nat.le_of_dvd (by have := h.one_le; omega) hpf) hp.pos
          omega)
        exact ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 h3').trans hp3.symm
      · rw [hpow_mod Dat.σ hF.2.2.2.2.1.1, h3]
        norm_num
  have hD1 : ∀ (Aε : Subgroup (GL (Fin n) K)) [IsMulCommutative Aε], (∀ a : ↥Aε, a ^ p = 1) →
      Aε ≤ isomGL (unitForm (ι := Fin n) h.bar) →
      IsMaxElem (unitForm (ι := Fin n) h.bar) (glRep Aε) p ∅ →
      (∃ c : Kˣ, c ≠ 1 ∧ c ^ p = 1 ∧ Matrix.GeneralLinearGroup.scalar (Fin n) c ∈
        isomGL (unitForm (ι := Fin n) h.bar)) →
      ∀ H' : Hyperplane ↥Aε p, weightSpace (glRep Aε) H'.1 ≠ ⊥ →
        Module.finrank K (weightSpace (glRep Aε) H'.1) = 1 := by
    intro Aε _ hA hAεβ hmax ⟨c, hc1, hcp, hcβ⟩ H' hH'
    haveI : Fintype K := Fintype.ofFinite K
    haveI := Fact.mk hp
    have hd : p ∣ ℓ ^ f + 1 := by
      rw [← orderOf_eq_prime hcp hc1]
      exact orderOf_dvd_of_pow_eq_one (pow_succ_eq_one_of_scalar_mem h hcβ)
    have hσp : ∀ c' : K, c' ^ p = 1 → c' * h.bar c' = 1 := by
      intro c' hc'
      rw [UnitaryFieldData.bar_apply, ← pow_succ']
      obtain ⟨k, hk⟩ := hd
      rw [hk, pow_mul, hc', one_pow]
    have hq : p ∣ Fintype.card K - 1 := by
      rw [← Nat.card_eq_fintype_card, h.card, pow_mul', sq]
      have h1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
      have : ℓ ^ f * ℓ ^ f - 1 = (ℓ ^ f + 1) * (ℓ ^ f - 1) := by
        zify [h1, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega) :
          ℓ ^ f * ℓ ^ f ≠ 0)]
        ring
      rw [this]
      exact Dvd.dvd.mul_right hd _
    exact finrank_weightSpace_eq_one_uni (unitForm (ι := Fin n) h.bar) (glRep Aε) hp hA hpK
      (isIsomRep_glRep hAεβ) (fun u v => (unitForm_swap h.bar_bar u v).symm) hσp h2K
      (unitForm_separatingLeft h.bar) hmax hq H' hH'
  rcases concl_lu (ι := Fin n) hp hB hrank hBC hcore hZ h4 h2K hpK Dat
      (ModelGen.statedSU_le_isomGL h) (Or.inr (unitForm_separatingLeft h.bar))
      (fun g hg hdet => (CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h).2
        ⟨hdet, ModelGen.map_bar_transpose_mul_of_mem_isomGL h hg⟩)
      (fun g hg hgp => ModelGen.exists_scalar_mul_mem_statedSU h hp hdiag hg hgp)
      (QbigF := fun σ => ℓ ^ (f / p) ≠ 3) hblk
      (fun U W hUW horth hnd A σ hσ hform hU hW x hx hxp hdim =>
        glaPLayer_inf_centGL_ne_bot_unitForm h hℓ2 hUW horth (hnd0 U hnd) hp hp2 hσ hU hW hform
          hdim hx hxp)
      hform1 hQscal hQdim2 hD1 with
    hA | ⟨hB4, hodd⟩ | ⟨hB4, hn4, hsc, hBdec, hBdisj⟩
  · exact Or.inl hA
  ·
    exfalso
    have hexp : Q.exponent = f := by
      have h1 : ℓ ^ Q.exponent = ℓ ^ f := by rw [← hQℓ, ← TauCeti.PrimePower.card_def, hQK, hQℓ]
      exact Nat.pow_right_injective hℓ.two_le h1
    have hd : HqRank.HqSixIdx ℓ (⟨.twistedA (n - 1) Q, hv⟩ : TauCeti.ValidLieTypeIndex).1 := by
      refine ⟨hQℓ, ?_⟩
      rcases hodd with h9 | ⟨h6, hF⟩
      · rw [Fintype.card_fin] at h9
        exact Or.inl (by omega)
      · rw [Fintype.card_fin] at h6
        refine Or.inr ⟨by omega, ?_⟩
        have hpf := hpf_of _ hF.2.2.2.2.1.1
        rw [hexp]
        exact hp3'.trans (Nat.le_of_dvd (by have := h.one_le; omega) hpf)
    have hrk : CFSG.Open.pRank p B ≤ 5 :=
      CFSG.SectionRank.pRank_le hp.one_lt fun _ hEB _ =>
        (Subgroup.card_le_of_le hEB).trans
          (hB4.le.trans (Nat.pow_le_pow_right hp.pos (by norm_num)))
    exact HqRank.not_hq_of_pQuot hℓ2 hd eL hrk hHq
  ·
    right
    obtain ⟨c, hc1, hcp, hcβ⟩ := hsc
    rw [Fintype.card_fin] at hn4
    have hn3 : n - 1 = 3 := by omega
    have hcat : pSimpleIsLie p S (.twistedA 3 Q) := by
      obtain ⟨eL⟩ := eL
      revert hv eL
      rw [hn3]
      intro hv eL
      exact ⟨TauCeti.CFSGIndex.lie ⟨.twistedA 3 Q, hv⟩, rfl, ⟨eL⟩⟩
    refine Or.inr (Or.inl ⟨hB4, hBdec, hBdisj, center_pQuot_eq_bot_of_core hcore hZ, Q, hQℓ,
      Or.inr ⟨hcat, ?_⟩⟩)
    haveI := Fact.mk hp
    rw [hQK, ← orderOf_eq_prime hcp hc1]
    exact orderOf_dvd_of_pow_eq_one (pow_succ_eq_one_of_scalar_mem h hcβ)

end Unitary

end CFSG.LocalAnalysis.GLTheoremA.S267.Cls
