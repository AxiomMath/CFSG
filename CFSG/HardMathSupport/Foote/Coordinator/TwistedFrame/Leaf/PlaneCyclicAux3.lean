module

public import CFSG.RankThree.Classical.SteinbergBYExchangedSL3
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Centralizer

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.PlaneCyclic

open Polynomial
open scoped MatrixGroups Matrix
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame

universe u

theorem exists_field_centralizer {F : Type u} [Field F] [Fintype F] {p : ℕ} (hp : p.Prime)
    (hord : orderOf ((Fintype.card F : ℕ) : ZMod p) = 3) {A : SL(3, F)} (hA : orderOf A = p) :
    ∃ (E : Type u) (_ : Field E) (_ : Finite E) (ψ : E →+* Matrix (Fin 3) (Fin 3) F),
      ∀ Z : Matrix (Fin 3) (Fin 3) F,
        Z * (A : Matrix (Fin 3) (Fin 3) F) = (A : Matrix (Fin 3) (Fin 3) F) * Z →
          ∃ e, ψ e = Z := by
  have := Fact.mk hp
  have : Nonempty (Fin 3) := ⟨0⟩
  set M : Matrix (Fin 3) (Fin 3) F := (A : Matrix (Fin 3) (Fin 3) F) with hMdef
  have hMp : M ^ p = 1 := by
    have h1 : A ^ p = 1 := by rw [← hA]; exact pow_orderOf_eq_one A
    have h2 := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 3) F =>
      (x : Matrix (Fin 3) (Fin 3) F)) h1
    simpa [hMdef, Matrix.SpecialLinearGroup.coe_pow] using h2
  have hM1 : M ≠ 1 := by
    intro h1
    have hg1 : A = 1 := Subtype.ext (Matrix.ext fun i j => congrFun (congrFun h1 i) j)
    have h2 : orderOf A = 1 := by rw [hg1, orderOf_one]
    rw [hA] at h2
    exact hp.one_lt.ne' h2
  obtain ⟨hirr, hdeg⟩ := minpoly_irreducible_natDegree_eq (by norm_num : 2 ≤ 3) hord hMp hM1
  have hroot := minpoly.aeval F M
  generalize minpoly F M = μ at hirr hdeg hroot
  have : Fact (Irreducible μ) := ⟨hirr⟩
  have hμ0 : μ ≠ 0 := hirr.ne_zero
  have hmf : Module.Finite F (AdjoinRoot μ) := (AdjoinRoot.powerBasis hμ0).finite
  have hfin : Finite (AdjoinRoot μ) := Module.finite_of_finite F
  have H : ∀ a ∈ Ideal.span ({μ} : Set F[X]), (Polynomial.aeval M).toRingHom a = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 ha
    simp [hroot]
  let ψ : AdjoinRoot μ →+* Matrix (Fin 3) (Fin 3) F :=
    Ideal.Quotient.lift (Ideal.span ({μ} : Set F[X])) (Polynomial.aeval M).toRingHom H
  have hψ : ∀ f : F[X], ψ (AdjoinRoot.mk μ f) = aeval M f := fun f => rfl
  exact ⟨AdjoinRoot μ, inferInstance, hfin, ψ, fun Z hZ =>
    eq_image_of_commute (by norm_num : 2 ≤ 3) hirr hdeg ψ hψ hZ⟩


section Setup

open Matrix CFSG.RankThree.Classical2 CFSG.RankThree.Classical.SteinbergBY

variable {Ω : Type} [Field Ω] {ℓ f : ℕ} {k : Type} [Field k] [Algebra k Ω]

local notation "M₃" => Matrix (Fin 3) (Fin 3) Ω

theorem exists_exchange_setup (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hk : Nat.card k = ℓ ^ f)
    [IsAlgClosure k Ω] (σ : Ω →+* Ω) (hσ : ∀ c, σ c = c ^ ℓ ^ f) (a b : SL(3, Ω)) :
    ∃ (F : Subfield Ω) (h₁ h₂ : SL(3, Ω)), (∀ c : Ω, c ∈ F ↔ c ^ (ℓ ^ f) ^ 2 = c) ∧
      Nat.card F = (ℓ ^ f) ^ 2 ∧ a * SpecialLinearGroup.map σ h₂ = h₁ ∧
      b * SpecialLinearGroup.map σ h₁ = h₂ := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact (pow_pos hℓ.pos f).ne')
  have : Fintype k := Fintype.ofFinite k
  have : CharP k ℓ := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hk])
  have : CharP Ω ℓ := charP_of_injective_algebraMap (algebraMap k Ω).injective ℓ
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  set q := ℓ ^ f with hq
  have hq1 : 1 ≤ q := Nat.one_le_pow _ _ hℓ.pos
  set F : Subfield Ω := (iterateFrobenius Ω ℓ (2 * f)).eqLocusField (RingHom.id Ω) with hFdef
  have hq2 : q ^ 2 = ℓ ^ (2 * f) := by rw [hq, ← pow_mul, mul_comm]
  have hF2 : ∀ c : Ω, c ∈ F ↔ c ^ ℓ ^ (2 * f) = c := fun c => by
    rw [hFdef, RingHom.mem_eqLocusField, iterateFrobenius_def, RingHom.id_apply]
  have hF : ∀ c : Ω, c ∈ F ↔ c ^ q ^ 2 = c := fun c => by
    rw [hq2]
    exact hF2 c
  have hFcard : Nat.card F = q ^ 2 := by
    rw [hq2, ← natCard_setOf_pow_eq_self (Ω := Ω) (ℓ := ℓ) (by omega : 2 * f ≠ 0)]
    exact Nat.card_congr (Equiv.subtypeEquivRight hF2)
  have : Finite F := Nat.finite_of_card_ne_zero (by
    rw [hFcard]
    exact (pow_pos (pow_pos hℓ.pos f) 2).ne')
  have hkq : ∀ c : k, c ^ q = c := fun c => by
    rw [← hk, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hσσ : ∀ c, σ (σ c) = c ^ q ^ 2 := fun c => by rw [hσ, hσ, ← pow_mul, sq]
  set σS : SL(3, Ω) →* SL(3, Ω) := SpecialLinearGroup.map σ with hσSdef
  have hσS : ∀ X : SL(3, Ω), (σS X : M₃) = (X : M₃).map σ := fun X => rfl
  set F' : IntermediateField k Ω := F.toIntermediateField (fun x => by
    rw [hF, ← map_pow, pow_two, pow_mul, hkq, hkq]) with hF'def
  have : IsAlgClosure F' Ω :=
    ⟨IsAlgClosure.isAlgClosed k, Algebra.IsAlgebraic.tower_top (K := k) (A := Ω) F'⟩
  have : CharP F' ℓ := (RingHom.charP_iff_charP (algebraMap F' Ω) ℓ).mpr inferInstance
  have hF'card : Nat.card F' = ℓ ^ (2 * f) := by
    rw [← hq2, ← hFcard]
    rfl
  obtain ⟨-, hlang⟩ := matrix_frobenius_lang (K := F') (f := 2 * f) hℓ (by omega)
    hF'card (n := 3) (by norm_num) (SpecialLinearGroup.toGL (a * σS b))
  obtain ⟨H, hHdet, hH⟩ := hlang (a * σS b).2
  set Hs : SL(3, Ω) := ⟨H, hHdet⟩ with hHsdef
  have hc₀ : a * σS b = Hs⁻¹ * σS (σS Hs) := by
    apply Subtype.ext
    have e1 : ((a * σS b : SL(3, Ω)) : M₃) = (SpecialLinearGroup.toGL (a * σS b) : M₃) := rfl
    have hinv : ((Hs⁻¹ : SL(3, Ω)) : M₃) = ((H⁻¹ : GL (Fin 3) Ω) : M₃) := by
      rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.coe_units_inv, Matrix.inv_def, hHdet,
        Ring.inverse_one, one_smul]
    rw [e1, hH, Matrix.SpecialLinearGroup.coe_mul, hσS, hσS, Matrix.map_map, hinv]
    congr 1
    ext i j
    rw [Matrix.map_apply, Matrix.map_apply, Function.comp_apply, hσσ, hq2]
  set h₁ : SL(3, Ω) := Hs⁻¹ with hh₁
  set h₂ : SL(3, Ω) := b * σS h₁ with hh₂
  have hah : a * σS h₂ = h₁ := by
    rw [hh₂, map_mul, ← mul_assoc, hc₀, mul_assoc, ← map_mul σS, ← map_mul σS, hh₁,
      mul_inv_cancel, map_one, map_one, mul_one]
  exact ⟨F, h₁, h₂, hF, hFcard, hah, rfl⟩

end Setup


section Cover

theorem isCyclic_of_cover {Γ Q W : Type*} [Group Γ] [Group Q] [Group W] (ν : Γ →* Q)
    (hν : Function.Surjective ν) (Cn : Subgroup Q) (f : Γ →* W) (T : Subgroup W) [IsCyclic T]
    (hT : ∀ h, ν h ∈ Cn → f h ∈ T) (hker : ∀ h, ν h ∈ Cn → f h = 1 → ν h = 1) :
    IsCyclic Cn := by
  let H : Subgroup Γ := Cn.comap ν
  let φ : H →* T := (f.comp H.subtype).codRestrict T (fun h => hT h h.2)
  let νH : H →* Cn := (ν.comp H.subtype).codRestrict Cn (fun h => h.2)
  have hle : φ.ker ≤ νH.ker := by
    intro h hh
    rw [MonoidHom.mem_ker] at hh ⊢
    have h1 : f (h : Γ) = 1 := congrArg Subtype.val hh
    exact Subtype.ext (hker (h : Γ) h.2 h1)
  have hsurj : Function.Surjective νH := by
    intro c
    obtain ⟨h, hh⟩ := hν (c : Q)
    exact ⟨⟨h, by rw [Subgroup.mem_comap, hh]; exact c.2⟩, Subtype.ext hh⟩
  have hcycQ : IsCyclic (H ⧸ φ.ker) :=
    isCyclic_of_injective (QuotientGroup.kerLift φ) (QuotientGroup.kerLift_injective φ)
  exact isCyclic_of_surjective (QuotientGroup.lift φ.ker νH hle) (by
    intro c
    obtain ⟨h, rfl⟩ := hsurj c
    exact ⟨QuotientGroup.mk h, rfl⟩)

end Cover

section Scalar

open Matrix CFSG.RankThree.Classical2 CFSG.RankThree.Classical.SteinbergBY

variable {Ω : Type} [Field Ω]

local notation "M₃" => Matrix (Fin 3) (Fin 3) Ω

theorem scalar_eq_one_of_conj {p : ℕ} (hp : Nat.Coprime 3 p) {A X : SL(3, Ω)} {c : Ω}
    (hc : c ^ 3 = 1) (hA : A ^ p = 1) (h : (X : M₃) * (A : M₃) = c • ((A : M₃) * (X : M₃))) :
    c = 1 := by
  have hk : ∀ k : ℕ, (X : M₃) * ((A ^ k : SL(3, Ω)) : M₃) =
      c ^ k • (((A ^ k : SL(3, Ω)) : M₃) * (X : M₃)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mul_assoc, h, Matrix.smul_mul,
        Matrix.mul_assoc, ih, Matrix.mul_smul, Matrix.mul_assoc, smul_smul, pow_succ']
  have h1 := hk p
  rw [hA, Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one, Matrix.one_mul] at h1
  have h2 : c ^ p = 1 := by
    apply smul_left_cancel_sl (X := X)
    rw [one_smul]
    exact h1.symm
  exact (pow_eq_one_iff_of_coprime hp).1 ⟨hc, h2⟩

end Scalar


section Main

open Matrix CFSG.RankThree.Classical2 CFSG.RankThree.Classical.SteinbergBY

variable {Ω : Type} [Field Ω]

local notation "M₃" => Matrix (Fin 3) (Fin 3) Ω

theorem sl_pow_three_of_scalar {X : SL(3, Ω)} {c : Ω} (hc : c ^ 3 = 1)
    (h : (X : M₃) = scalar (Fin 3) c) : X ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, h, ← map_pow, hc, map_one, Matrix.SpecialLinearGroup.coe_one]

theorem exchange_cyclic_aux [IsAlgClosed Ω] {q : ℕ} (hq3 : q % 3 = 1) (hq2 : 2 ≤ q) (σ : Ω →+* Ω)
    (hσ : ∀ c, σ c = c ^ q) (F : Subfield Ω) (hF : ∀ c : Ω, c ∈ F ↔ c ^ q ^ 2 = c)
    (hFcard : Nat.card F = q ^ 2) {Q : Type*} [Group Q] (ν : SL(3, Ω) × SL(3, Ω) →* Q)
    (hν : Function.Surjective ν)
    (hνker : ∀ X Y : SL(3, Ω), ν (X, Y) = 1 ↔ ∃ c : Ω, c ^ 3 = 1 ∧ (X : M₃) = scalar (Fin 3) c ∧
      (Y : M₃) = scalar (Fin 3) c)
    (θ : Q ≃* Q)
    (hθν : ∀ X Y : SL(3, Ω), θ (ν (X, Y)) =
      ν (SpecialLinearGroup.map σ Y, SpecialLinearGroup.map σ X))
    {p : ℕ} (hp : p.Prime) (hord : orderOf ((q ^ 2 : ℕ) : ZMod p) = 3) :
    ∀ y : ↥(fixSubgroup θ), orderOf y = p →
      IsCyclic ↥(Subgroup.centralizer ({y} : Set ↥(fixSubgroup θ))) := by
  classical
  intro y hy
  have hq1 : 1 ≤ q := by omega
  have hp3 : p ≠ 3 := by
    rintro rfl
    haveI : Fact (Nat.Prime 3) := ⟨hp⟩
    have h1 : ((q ^ 2 : ℕ) : ZMod 3) ^ 3 = 1 := by
      have := pow_orderOf_eq_one ((q ^ 2 : ℕ) : ZMod 3)
      rwa [hord] at this
    have h2 : ((q ^ 2 : ℕ) : ZMod 3) ^ 3 = ((q ^ 2 : ℕ) : ZMod 3) := ZMod.pow_card _
    rw [h2] at h1
    rw [h1, orderOf_one] at hord
    omega
  have hcop : Nat.Coprime 3 p := (Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3)
  haveI hFfin : Finite F := Nat.finite_of_card_ne_zero (by rw [hFcard]; positivity)
  haveI : Fintype F := Fintype.ofFinite F
  have hFc : Fintype.card F = q ^ 2 := by rw [← Nat.card_eq_fintype_card]; exact hFcard
  set σS : SL(3, Ω) →* SL(3, Ω) := SpecialLinearGroup.map σ with hσSdef
  have hσS : ∀ X : SL(3, Ω), (σS X : M₃) = (X : M₃).map σ := fun X => rfl
  have hσσ : ∀ c, σ (σ c) = c ^ q ^ 2 := fun c => by rw [hσ, hσ, ← pow_mul, sq]
  have hpow : ∀ c : Ω, c ^ 3 = 1 → c ^ q = c := fun c hc =>
    pow_eq_self_of_three_dvd hq1 (Nat.dvd_of_mod_eq_zero (by omega)) hc
  have hσc : ∀ c : Ω, c ^ 3 = 1 → σ c = c := fun c hc => by rw [hσ]; exact hpow c hc
  have hνeq : ∀ X Y X' Y' : SL(3, Ω), ν (X, Y) = ν (X', Y') ↔ ∃ c : Ω, c ^ 3 = 1 ∧
      (X' : M₃) = c • (X : M₃) ∧ (Y' : M₃) = c • (Y : M₃) := by
    intro X Y X' Y'
    rw [← inv_mul_eq_one, ← map_inv, ← map_mul, Prod.inv_mk, Prod.mk_mul_mk, hνker]
    constructor
    · rintro ⟨c, hc, h1, h2⟩
      exact ⟨c, hc, coe_eq_smul_of_inv_mul h1, coe_eq_smul_of_inv_mul h2⟩
    · rintro ⟨c, hc, h1, h2⟩
      exact ⟨c, hc, inv_mul_coe_eq_scalar h1, inv_mul_coe_eq_scalar h2⟩
  have hfixν : ∀ X Y : SL(3, Ω), θ (ν (X, Y)) = ν (X, Y) ↔ ∃ c : Ω, c ^ 3 = 1 ∧
      (σS Y : M₃) = c • (X : M₃) ∧ (σS X : M₃) = c • (Y : M₃) := by
    intro X Y
    rw [hθν, eq_comm, hνeq]
  have hσsmul : ∀ (c : Ω) (X Y : SL(3, Ω)), (Y : M₃) = c • (X : M₃) →
      (σS Y : M₃) = σ c • (σS X : M₃) := by
    intro c X Y h
    rw [hσS, hσS, h]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  set ι : SL(3, F) →* SL(3, Ω) := SpecialLinearGroup.map F.subtype with hιdef
  have hι : ∀ A : SL(3, F), (ι A : M₃) = (A : Matrix (Fin 3) (Fin 3) F).map F.subtype :=
    fun A => rfl
  have hιinj : Function.Injective ι := specialLinearGroup_map_injective F.subtype.injective
  have hσσfix : ∀ X : SL(3, Ω), σS (σS X) = X → ∃ A : SL(3, F), ι A = X := by
    intro X hX
    refine exists_map_eq_of_forall_mem_range F.subtype.injective X fun i j => ?_
    have h1 := congrArg (fun Z : SL(3, Ω) => (Z : M₃) i j) hX
    simp only [hσS, Matrix.map_apply, hσσ] at h1
    exact ⟨⟨_, (hF _).mpr h1⟩, rfl⟩
  set y' : Q := (y : Q) with hy'
  have hyθ : θ y' = y' := y.2
  have hyp : y' ^ p = 1 := by
    have h1 : y ^ p = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
    exact congrArg Subtype.val h1
  have hyord : orderOf y' = p := by rw [hy', Subgroup.orderOf_coe, hy]
  obtain ⟨⟨A₁, A₂⟩, hA, hAp⟩ : ∃ g : SL(3, Ω) × SL(3, Ω), ν g = y' ∧ g ^ p = 1 := by
    obtain ⟨g, hg⟩ := hν y'
    have hgp : ν (g ^ p) = 1 := by rw [map_pow, hg, hyp]
    obtain ⟨c, hc, h1, h2⟩ := (hνker (g.1 ^ p) (g.2 ^ p)).1 hgp
    have hg3 : (g ^ p) ^ 3 = 1 := by
      refine Prod.ext ?_ ?_
      · rw [Prod.fst_one, Prod.pow_fst, Prod.pow_fst]
        exact sl_pow_three_of_scalar hc h1
      · rw [Prod.snd_one, Prod.pow_snd, Prod.pow_snd]
        exact sl_pow_three_of_scalar hc h2
    obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
    refine ⟨g ^ (3 * m), ?_, ?_⟩
    · rw [map_pow, hg, ← pow_mod_orderOf, hyord, hm, pow_one]
    · rw [← pow_mul, show 3 * m * p = p * 3 * m by ring, pow_mul, pow_mul, hg3, one_pow]
  have hA1p : A₁ ^ p = 1 := by
    have := congrArg Prod.fst hAp
    rwa [Prod.pow_fst, Prod.fst_one] at this
  have hA2p : A₂ ^ p = 1 := by
    have := congrArg Prod.snd hAp
    rwa [Prod.pow_snd, Prod.snd_one] at this
  obtain ⟨c, hc3, hc1, hc2⟩ := (hfixν A₁ A₂).1 (by rw [hA]; exact hyθ)
  have hc : c = 1 := by
    have h3 : (σS (σS A₁) : M₃) = (c * c) • (A₁ : M₃) := by
      rw [hσsmul c A₂ (σS A₁) hc2, hσc c hc3, hc1, smul_smul]
    have h4 : (σS (σS A₁)) ^ p = 1 := by rw [← map_pow, ← map_pow, hA1p, map_one, map_one]
    have h5 : ((c * c) ^ p) • (1 : M₃) = 1 := by
      have := congrArg (fun X : SL(3, Ω) => (X : M₃)) h4
      simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one] at this
      rw [h3, _root_.smul_pow, ← Matrix.SpecialLinearGroup.coe_pow, hA1p,
        Matrix.SpecialLinearGroup.coe_one] at this
      exact this
    have h6 : (c * c) ^ p = 1 := by
      have := congrFun (congrFun h5 0) 0
      simpa using this
    have h7 : c * c = 1 := by
      refine (pow_eq_one_iff_of_coprime hcop).1 ⟨?_, h6⟩
      calc (c * c) ^ 3 = c ^ 3 * c ^ 3 := by ring
        _ = 1 := by rw [hc3, one_mul]
    exact (pow_eq_one_iff_of_coprime (by norm_num : Nat.Coprime 2 3)).1 ⟨by rw [sq]; exact h7, hc3⟩
  subst hc
  have hσA1 : σS A₁ = A₂ := Subtype.ext (by rw [hc2, one_smul])
  have hσA2 : σS A₂ = A₁ := Subtype.ext (by rw [hc1, one_smul])
  obtain ⟨A, hAι⟩ := hσσfix A₁ (by rw [hσA1, hσA2])
  have hAp' : A ^ p = 1 := by
    apply hιinj
    rw [map_pow, hAι, hA1p, map_one]
  have hA1 : A ≠ 1 := by
    intro h1
    rw [h1, map_one] at hAι
    have hA1' : A₁ = 1 := hAι.symm
    have hA2' : A₂ = 1 := by rw [← hσA1, hA1', map_one]
    have h2 : y' = 1 := by
      rw [← hA, hA1', hA2']
      exact map_one ν
    rw [h2, orderOf_one] at hyord
    exact hp.one_lt.ne' hyord.symm
  haveI : Fact p.Prime := ⟨hp⟩
  have hAord : orderOf A = p := orderOf_eq_prime hAp' hA1
  obtain ⟨E, hEF, hEfin, ψ, hψ⟩ := exists_field_centralizer hp (by rw [hFc]; exact hord) hAord
  let W := GL (Fin 3) Ω ⧸ Subgroup.center (GL (Fin 3) Ω)
  let f : SL(3, Ω) × SL(3, Ω) →* W :=
    (QuotientGroup.mk' (Subgroup.center (GL (Fin 3) Ω))).comp
      (Matrix.SpecialLinearGroup.toGL.comp (MonoidHom.fst _ _))
  let ψ' : E →+* M₃ := F.subtype.mapMatrix.comp ψ
  let lam : Eˣ →* W := (QuotientGroup.mk' (Subgroup.center (GL (Fin 3) Ω))).comp
    (Units.map ψ'.toMonoidHom)
  haveI : IsCyclic Eˣ := inferInstance
  let T : Subgroup W := lam.range
  haveI hTcyc : IsCyclic T :=
    isCyclic_of_surjective lam.rangeRestrict lam.rangeRestrict_surjective
  set Cn : Subgroup Q := (Subgroup.centralizer ({y} : Set ↥(fixSubgroup θ))).map
    (fixSubgroup θ).subtype with hCn
  have hCnmem : ∀ z : Q, z ∈ Cn → θ z = z ∧ y' * z = z * y' := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hz
    refine ⟨w.2, ?_⟩
    have := Subgroup.mem_centralizer_iff.1 hw y (Set.mem_singleton y)
    exact congrArg Subtype.val this
  suffices hcyc : IsCyclic Cn by
    haveI := hcyc
    exact isCyclic_of_surjective
      (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).symm.toMonoidHom
      (MulEquiv.surjective _)
  refine isCyclic_of_cover ν hν Cn f T ?_ ?_
  · rintro ⟨X, Y⟩ hh
    obtain ⟨hz, hcomm⟩ := hCnmem _ hh
    obtain ⟨d, hd3, hd1, hd2⟩ := (hfixν X Y).1 hz
    have hc1 : ν (A₁ * X, A₂ * Y) = ν (X * A₁, Y * A₂) := by
      have h1 : ν (A₁, A₂) * ν (X, Y) = ν (X, Y) * ν (A₁, A₂) := by rw [hA]; exact hcomm
      rw [← map_mul, ← map_mul] at h1
      exact h1
    obtain ⟨c, hc3', hcX, hcY⟩ := (hνeq _ _ _ _).1 hc1
    simp only [Matrix.SpecialLinearGroup.coe_mul] at hcX hcY
    have hc' : c = 1 := scalar_eq_one_of_conj hcop hc3' hA1p hcX
    rw [hc', one_smul] at hcX
    have hσX2 : (σS (σS X) : M₃) = (d * d) • (X : M₃) := by
      rw [hσsmul d Y (σS X) hd2, hσc d hd3, hd1, smul_smul]
    have hd0 : d ≠ 0 := by
      rintro rfl
      norm_num at hd3
    have hq4 : 4 ≤ q ^ 2 := by nlinarith
    obtain ⟨κ, hκ⟩ := IsAlgClosed.exists_pow_nat_eq ((d * d)⁻¹) (by omega : 0 < q ^ 2 - 1)
    have hκ0 : κ ≠ 0 := by
      rintro rfl
      rw [zero_pow (by omega)] at hκ
      exact inv_ne_zero (mul_ne_zero hd0 hd0) hκ.symm
    have hκq : κ ^ q ^ 2 = κ * (d * d)⁻¹ := by
      rw [← hκ, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ q ^ 2)]
    have hZF : ∀ i j, κ * (X : M₃) i j ∈ F := by
      intro i j
      rw [hF, ← hσσ, map_mul, map_mul, hσσ κ]
      have h1 := congrFun (congrFun hσX2 i) j
      simp only [hσS, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at h1
      rw [h1, hκq]
      field_simp
    let Z : Matrix (Fin 3) (Fin 3) F := Matrix.of fun i j => ⟨κ * (X : M₃) i j, hZF i j⟩
    have hZmap : Z.map F.subtype = κ • (X : M₃) := by
      ext i j
      simp [Z]
    have hAmap : (A : Matrix (Fin 3) (Fin 3) F).map F.subtype = (A₁ : M₃) := by
      rw [← hι, hAι]
    have hZcomm : Z * (A : Matrix (Fin 3) (Fin 3) F) = (A : Matrix (Fin 3) (Fin 3) F) * Z := by
      apply Matrix.map_injective F.subtype.injective
      show (Z * (A : Matrix (Fin 3) (Fin 3) F)).map F.subtype =
        ((A : Matrix (Fin 3) (Fin 3) F) * Z).map F.subtype
      rw [Matrix.map_mul, Matrix.map_mul, hZmap, hAmap, Matrix.smul_mul, Matrix.mul_smul, hcX]
    obtain ⟨e, he⟩ := hψ Z hZcomm
    have hψe : ψ' e = κ • (X : M₃) := by
      show (ψ e).map F.subtype = _
      rw [he, hZmap]
    have he0 : e ≠ 0 := by
      rintro rfl
      rw [map_zero] at hψe
      have h1 : κ • (X : M₃) = 0 := hψe.symm
      rcases smul_eq_zero.1 h1 with h | h
      · exact hκ0 h
      · exact sl_coe_ne_zero X h
    have h1 : ψ' (e⁻¹) * (X : M₃) = κ⁻¹ • (1 : M₃) := by
      have h2 : ψ' (e⁻¹) * ψ' e = 1 := by rw [← map_mul, inv_mul_cancel₀ he0, map_one]
      rw [hψe, Matrix.mul_smul] at h2
      calc ψ' (e⁻¹) * (X : M₃) = κ⁻¹ • (κ • (ψ' (e⁻¹) * (X : M₃))) := by
            rw [smul_smul, inv_mul_cancel₀ hκ0, one_smul]
        _ = κ⁻¹ • (1 : M₃) := by rw [h2]
    refine ⟨Units.mk0 e he0, ?_⟩
    show (QuotientGroup.mk (Units.map ψ'.toMonoidHom (Units.mk0 e he0)) : W) =
      QuotientGroup.mk (Matrix.SpecialLinearGroup.toGL X)
    rw [QuotientGroup.eq, Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
    refine ⟨κ⁻¹, ?_⟩
    have hu : ((Units.map ψ'.toMonoidHom (Units.mk0 e he0))⁻¹ : GL (Fin 3) Ω) =
        Units.map ψ'.toMonoidHom (Units.mk0 e he0)⁻¹ := (map_inv _ _).symm
    rw [Units.val_mul, hu]
    show scalar (Fin 3) κ⁻¹ = ψ' (((Units.mk0 e he0)⁻¹ : Eˣ) : E) * (X : M₃)
    rw [Units.val_inv_eq_inv_val, Units.val_mk0, h1, scalar_three_eq_smul]
  · rintro ⟨X, Y⟩ hh hf1
    obtain ⟨hz, -⟩ := hCnmem _ hh
    obtain ⟨d, hd3, hd1, hd2⟩ := (hfixν X Y).1 hz
    have hmem : Matrix.SpecialLinearGroup.toGL X ∈ Subgroup.center (GL (Fin 3) Ω) :=
      (QuotientGroup.eq_one_iff _).1 hf1
    obtain ⟨t, ht⟩ := (Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar).1 hmem
    have hXs : (X : M₃) = scalar (Fin 3) t := ht.symm
    have ht3 : t ^ 3 = 1 := by
      have h1 := X.2
      rw [hXs, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin] at h1
      exact h1
    have hd0 : d ≠ 0 := by
      rintro rfl
      norm_num at hd3
    have ht0 : t ≠ 0 := by
      rintro rfl
      norm_num at ht3
    have hσt : σ t = t := hσc t ht3
    have hYs : (Y : M₃) = scalar (Fin 3) (d⁻¹ * t) := by
      have h1 : (σS X : M₃) = scalar (Fin 3) t := by rw [hσS, hXs, scalar_map, hσt]
      rw [h1] at hd2
      calc (Y : M₃) = d⁻¹ • (d • (Y : M₃)) := by rw [smul_smul, inv_mul_cancel₀ hd0, one_smul]
        _ = d⁻¹ • scalar (Fin 3) t := by rw [← hd2]
        _ = scalar (Fin 3) (d⁻¹ * t) := by
          rw [scalar_three_eq_smul, scalar_three_eq_smul, smul_smul]
    have h2 : d⁻¹ * t = d * t := by
      have h3 : (σS Y : M₃) = scalar (Fin 3) (d⁻¹ * t) := by
        rw [hσS, hYs, scalar_map, map_mul, map_inv₀, hσc d hd3, hσt]
      have e1 := congrFun (congrFun h3 0) 0
      have e2 := congrFun (congrFun hd1 0) 0
      have e3 := e1.symm.trans e2
      simpa [hXs] using e3
    have hdd : d * d = 1 := by
      have h4 : d⁻¹ = d := mul_right_cancel₀ ht0 h2
      have h5 := inv_mul_cancel₀ hd0
      rwa [h4] at h5
    have hd : d = 1 :=
      (pow_eq_one_iff_of_coprime (by norm_num : Nat.Coprime 2 3)).1 ⟨by rw [sq]; exact hdd, hd3⟩
    refine (hνker X Y).2 ⟨t, ht3, hXs, ?_⟩
    rw [hYs, hd, inv_one, one_mul]

end Main


section General

open Matrix CFSG.RankThree.Classical2 CFSG.RankThree.Classical.SteinbergBY

theorem isCyclic_centralizer_of_injective_hom_gen {G H : Type*} [Group G] [Group H] (Λ : G →* H)
    (hΛ : Function.Injective Λ) {p : ℕ}
    (hH : ∀ x : H, orderOf x = p → IsCyclic ↥(Subgroup.centralizer ({x} : Set H))) {g : G}
    (hg : orderOf g = p) : IsCyclic ↥(Subgroup.centralizer ({g} : Set G)) := by
  have hc := hH (Λ g) (by rw [orderOf_injective Λ hΛ g, hg])
  let φ : ↥(Subgroup.centralizer ({g} : Set G)) →*
      ↥(Subgroup.centralizer ({Λ g} : Set H)) :=
    (Λ.comp (Subgroup.centralizer ({g} : Set G)).subtype).codRestrict _ (by
      rintro ⟨x, hx⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
      rw [← map_mul, ← map_mul, hx])
  refine isCyclic_of_injective φ ?_
  rintro ⟨x, hx⟩ ⟨y, hy⟩ h
  apply Subtype.ext
  exact hΛ (congrArg Subtype.val h)

theorem isCyclic_centralizer_of_injective_hom_sl {G : Type*} [Group G] {F : Type*} [Field F]
    [Fintype F] {ν p : ℕ} (hp : p.Prime) (hν : 2 ≤ ν)
    (hord : orderOf ((Fintype.card F : ℕ) : ZMod p) = ν)
    (Λ : G →* SL(ν, F)) (hΛ : Function.Injective Λ) {g : G} (hg : orderOf g = p) :
    IsCyclic ↥(Subgroup.centralizer ({g} : Set G)) := by
  have h1 : orderOf (Λ g) = p := by rw [orderOf_injective Λ hΛ g, hg]
  have hc := isCyclic_centralizer_of_orderOf_eq F hp hν hord h1
  let φ : ↥(Subgroup.centralizer ({g} : Set G)) →*
      ↥(Subgroup.centralizer ({Λ g} : Set SL(ν, F))) :=
    (Λ.comp (Subgroup.centralizer ({g} : Set G)).subtype).codRestrict _ (by
      rintro ⟨x, hx⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
      rw [← map_mul, ← map_mul, hx])
  refine isCyclic_of_injective φ ?_
  rintro ⟨x, hx⟩ ⟨y, hy⟩ h
  apply Subtype.ext
  exact hΛ (congrArg Subtype.val h)

variable {Ω : Type} [Field Ω] {ℓ f : ℕ} {k : Type} [Field k] [Algebra k Ω]

local notation "M₃" => Matrix (Fin 3) (Fin 3) Ω

theorem exchange_cyclic {Q : Type*} [Group Q] (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hk : Nat.card k = ℓ ^ f) [IsAlgClosure k Ω] (σ : Ω →+* Ω) (hσ : ∀ c, σ c = c ^ ℓ ^ f)
    (μ : SL(3, Ω) × SL(3, Ω) →* Q) (hμ : Function.Surjective μ)
    (hμker : ∀ x : SL(3, Ω) × SL(3, Ω), μ x = 1 ↔ ∃ c : Ω, c ^ 3 = 1 ∧
      (x.1 : M₃) = scalar (Fin 3) c ∧ (x.2 : M₃) = scalar (Fin 3) c)
    (θ : Q ≃* Q) (a b : SL(3, Ω))
    (hθ : ∀ A B : SL(3, Ω), θ (μ (A, B)) =
      μ (a * SpecialLinearGroup.map σ B * a⁻¹, b * SpecialLinearGroup.map σ A * b⁻¹))
    {p : ℕ} (hp : p.Prime) (hord : orderOf (((ℓ ^ f) ^ 2 : ℕ) : ZMod p) = 3) :
    ∀ y : ↥(fixSubgroup θ), orderOf y = p →
      IsCyclic ↥(Subgroup.centralizer ({y} : Set ↥(fixSubgroup θ))) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact (pow_pos hℓ.pos f).ne')
  have : Fintype k := Fintype.ofFinite k
  have : CharP k ℓ := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hk])
  have : CharP Ω ℓ := charP_of_injective_algebraMap (algebraMap k Ω).injective ℓ
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  by_cases h3 : (ℓ ^ f) % 3 = 1
  ·
    have hq2 : 2 ≤ ℓ ^ f :=
      le_trans hℓ.two_le (Nat.le_self_pow (by omega) ℓ)
    obtain ⟨F, h₁, h₂, hF, hFcard, hah, hh₂⟩ := exists_exchange_setup hℓ hf hk σ hσ a b
    set σS : SL(3, Ω) →* SL(3, Ω) := SpecialLinearGroup.map σ with hσSdef
    set ν : SL(3, Ω) × SL(3, Ω) →* Q :=
      μ.comp ((MulAut.conj h₁).toMonoidHom.prodMap (MulAut.conj h₂).toMonoidHom) with hνdef
    have hν : ∀ X Y, ν (X, Y) = μ (h₁ * X * h₁⁻¹, h₂ * Y * h₂⁻¹) := fun X Y => rfl
    have hνsurj : Function.Surjective ν := by
      intro x
      obtain ⟨⟨X, Y⟩, hXY⟩ := hμ x
      refine ⟨(h₁⁻¹ * X * h₁, h₂⁻¹ * Y * h₂), ?_⟩
      rw [hν, ← hXY]
      congr 1
      ext <;> simp only [] <;> group
    have hνker : ∀ X Y : SL(3, Ω), ν (X, Y) = 1 ↔ ∃ c : Ω, c ^ 3 = 1 ∧ (X : M₃) = scalar (Fin 3) c ∧
        (Y : M₃) = scalar (Fin 3) c := by
      intro X Y
      rw [hν, hμker]
      simp only [conj_coe_eq_scalar_iff]
    have hθν : ∀ X Y : SL(3, Ω), θ (ν (X, Y)) = ν (σS Y, σS X) := by
      intro X Y
      have e1 : a * σS (h₂ * Y * h₂⁻¹) * a⁻¹ = (a * σS h₂) * σS Y * (a * σS h₂)⁻¹ := by
        simp only [map_mul, map_inv]
        group
      have e2 : b * σS (h₁ * X * h₁⁻¹) * b⁻¹ = (b * σS h₁) * σS X * (b * σS h₁)⁻¹ := by
        simp only [map_mul, map_inv]
        group
      rw [hν, hθ, hν, e1, e2, hah, hh₂]
    exact exchange_cyclic_aux h3 hq2 σ hσ F hF hFcard ν hνsurj hνker θ hθν hp hord
  ·
    obtain ⟨k₂, hk₂, h₁, h₂, ρ, -, hρfix, -, -, -, hρcard, -, -, -, hindex, -⟩ :=
      exchanged_sl3_central_product_frobenius_full_fixed_layer hℓ hf hk σ hσ μ hμ hμker θ a b hθ
    have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
    have hgcd : Nat.gcd 3 (ℓ ^ f - 1) = 1 := by
      have h3' : ¬ 3 ∣ ℓ ^ f - 1 := by omega
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3'
    have hρinj : Function.Injective ρ := by
      rw [← MonoidHom.ker_eq_bot_iff]
      exact Subgroup.card_eq_one.1 (by rw [hρcard, hgcd])
    have hidx : (ρ.range.subgroupOf (fixSubgroup θ)).index = 1 :=
      Nat.dvd_one.1 (by rw [← hgcd]; exact hindex)
    have htop : ρ.range.subgroupOf (fixSubgroup θ) = ⊤ := Subgroup.index_eq_one.1 hidx
    have hle : fixSubgroup θ ≤ ρ.range := fun x hx => by
      have : (⟨x, hx⟩ : ↥(fixSubgroup θ)) ∈ ρ.range.subgroupOf (fixSubgroup θ) := by
        rw [htop]; exact Subgroup.mem_top _
      exact this
    let Λ : ↥(fixSubgroup θ) →* SL(3, ↥k₂) :=
      (MonoidHom.ofInjective hρinj).symm.toMonoidHom.comp (Subgroup.inclusion hle)
    have hΛ : Function.Injective Λ := fun x y h =>
      Subgroup.inclusion_injective hle ((MonoidHom.ofInjective hρinj).symm.injective h)
    have hk₂card : Nat.card k₂ = (ℓ ^ f) ^ 2 := by
      have hq2 : (ℓ ^ f) ^ 2 = ℓ ^ (2 * f) := by rw [← pow_mul, mul_comm]
      have hF2 : ∀ c : Ω, c ∈ k₂ ↔ c ^ ℓ ^ (2 * f) = c := fun c => by rw [hk₂, hq2]
      rw [hq2, ← natCard_setOf_pow_eq_self (Ω := Ω) (ℓ := ℓ) (by omega : 2 * f ≠ 0)]
      exact Nat.card_congr (Equiv.subtypeEquivRight hF2)
    haveI : Finite k₂ := Nat.finite_of_card_ne_zero (by
      rw [hk₂card]; exact (pow_pos (pow_pos hℓ.pos f) 2).ne')
    haveI : Fintype k₂ := Fintype.ofFinite k₂
    have hFc : Fintype.card k₂ = (ℓ ^ f) ^ 2 := by rw [← Nat.card_eq_fintype_card]; exact hk₂card
    intro y hy
    exact isCyclic_centralizer_of_injective_hom_sl hp (by norm_num : 2 ≤ 3)
      (by rw [hFc]; exact hord) Λ hΛ hy

end General

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.PlaneCyclic
