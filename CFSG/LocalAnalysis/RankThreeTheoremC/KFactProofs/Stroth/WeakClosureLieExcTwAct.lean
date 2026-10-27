module

public import CFSG.RankThree.PartOne.KE.CTTorusFixed
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcLangNFix

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross CFSG.RankThree.PartOne.KE
open scoped commutatorElement Matrix

section Acts

variable {τ : Tag} {L : Type} [Field L]

@[expose] def TwActsAs (y : ModGL τ L) (u : WeylGroup τ) : Prop :=
  ∀ b : Fin τ.rank → Lˣ, y * rootDiagUnit τ b * y⁻¹ = rootDiagUnit τ (weylTuple u b)

theorem TwActsAs.one : TwActsAs (1 : ModGL τ L) (1 : WeylGroup τ) := fun b => by
  rw [weylTuple_one]; group

theorem TwActsAs.mul {y₁ y₂ : ModGL τ L} {u₁ u₂ : WeylGroup τ} (h₁ : TwActsAs y₁ u₁)
    (h₂ : TwActsAs y₂ u₂) : TwActsAs (y₁ * y₂) (u₁ * u₂) := fun b => by
  have e : y₁ * y₂ * rootDiagUnit τ b * (y₁ * y₂)⁻¹ =
      y₁ * (y₂ * rootDiagUnit τ b * y₂⁻¹) * y₁⁻¹ := by group
  rw [e, h₂ b, h₁, weylTuple_weylTuple]

theorem TwActsAs.inv {y : ModGL τ L} {u : WeylGroup τ} (h : TwActsAs y u) :
    TwActsAs y⁻¹ u⁻¹ := fun b => by
  have h1 := h (weylTuple u⁻¹ b)
  rw [weylTuple_weylTuple, mul_inv_cancel, weylTuple_one] at h1
  have e : y⁻¹ * rootDiagUnit τ b * y⁻¹⁻¹ =
      y⁻¹ * (y * rootDiagUnit τ (weylTuple u⁻¹ b) * y⁻¹) * y⁻¹⁻¹ := by
    rw [h1]
  rw [e]
  group

theorem TwActsAs.commutator {y₁ y₂ : ModGL τ L} {u₁ u₂ : WeylGroup τ} (h₁ : TwActsAs y₁ u₁)
    (h₂ : TwActsAs y₂ u₂) : TwActsAs ⁅y₁, y₂⁆ ⁅u₁, u₂⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  exact ((h₁.mul h₂).mul h₁.inv).mul h₂.inv

theorem twActsAs_canonicalRep (u : WeylGroup τ) :
    TwActsAs (canonicalRep (coxeterSystem τ) L u) u := fun b =>
  canonicalRep_conj_rootDiagUnit u b

theorem TwActsAs.torus_mul [IsAlgClosed L] {y t : ModGL τ L} {u : WeylGroup τ} (h : TwActsAs y u)
    (ht : t ∈ torusGroup τ L) : TwActsAs (t * y) u := fun b => by
  have e : t * y * rootDiagUnit τ b * (t * y)⁻¹ = t * (y * rootDiagUnit τ b * y⁻¹) * t⁻¹ := by
    group
  rw [e, h b, torusGroup_mul_comm ht (rootDiagUnit_mem_torusGroup _), mul_assoc, mul_inv_cancel,
    mul_one]

theorem eq_one_of_rootChar_cert {p : ℕ} [hp : Fact p.Prime] {b : Fin τ.rank → Lˣ}
    (hbp : ∀ i, b i ^ p = 1) {A₁ A₂ Y₁ Y₂ : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} {c : ℤ}
    (hcert : A₁ * Y₁ + A₂ * Y₂ = c • (1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ))
    (hc : ¬ (p : ℤ) ∣ c) (h₁ : ∀ x, rootChar b (A₁ *ᵥ x) = 1)
    (h₂ : ∀ x, rootChar b (A₂ *ᵥ x) = 1) : b = 1 := by
  refine CTTorus.eq_one_of_rootChar_eq_one fun x => ?_
  have hx : c • x = A₁ *ᵥ (Y₁ *ᵥ x) + A₂ *ᵥ (Y₂ *ᵥ x) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, hcert, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  have h1 : rootChar b x ^ c = 1 := by
    rw [← rootChar_zsmul, hx, rootChar_add, h₁, h₂, mul_one]
  have h2 : rootChar b x ^ p = 1 := CTTorus.rootChar_pow_eq_one hbp x
  have h3 : orderOf (rootChar b x) ∣ p := orderOf_dvd_of_pow_eq_one h2
  rcases (Nat.dvd_prime hp.out).1 h3 with h | h
  · exact orderOf_eq_one_iff.1 h
  · exfalso
    apply hc
    have h4 := (orderOf_dvd_iff_zpow_eq_one (G := Lˣ)).2 h1
    rw [h] at h4
    exact h4

end Acts

section Scalar

variable {τ : Tag} {L : Type} [Field L]
  {M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} {Fr : L →+* L} {q : ℕ}

theorem weylTuple_eq_zpow_of_scalar (hFr : ∀ c, Fr c = c ^ q) {u : WeylGroup τ} {s : ℤ} {k : ℕ}
    (hu : ∀ x : Fin τ.rank → ℤ, u⁻¹ • x = s • ((M ^ k) *ᵥ x)) {b : Fin τ.rank → Lˣ}
    (hb : b ∈ fixedCharTuples M Fr) (i : Fin τ.rank) :
    weylTuple u b i = b i ^ (s * (q : ℤ) ^ k) := by
  have h1 : weylTuple u b i = rootChar b (u⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ)) := rfl
  rw [h1, hu, rootChar_zsmul, rootChar_pow_mulVec_of_mem_fixedCharTuples hFr hb,
    CTTorus.rootChar_single, ← zpow_natCast, ← zpow_mul]
  congr 1
  push_cast
  ring

theorem twFixedPointFree_of_scalar (hFr : ∀ c, Fr c = c ^ q) {u : WeylGroup τ} {s : ℤ} {k : ℕ}
    (hu : ∀ x : Fin τ.rank → ℤ, u⁻¹ • x = s • ((M ^ k) *ᵥ x)) {p : ℕ} [hp : Fact p.Prime]
    (hnd : ¬ (p : ℤ) ∣ s * (q : ℤ) ^ k - 1) {b : Fin τ.rank → Lˣ}
    (hb : b ∈ fixedCharTuples M Fr) (hbp : ∀ i, b i ^ p = 1) (hfix : weylTuple u b = b) :
    b = 1 := by
  funext i
  have h1 : b i ^ (s * (q : ℤ) ^ k) = b i := by
    rw [← weylTuple_eq_zpow_of_scalar hFr hu hb i, hfix]
  have h2 : b i ^ (s * (q : ℤ) ^ k - 1) = 1 := by
    rw [zpow_sub_one, h1, mul_inv_cancel]
  have h3 : orderOf (b i) ∣ p := orderOf_dvd_of_pow_eq_one (hbp i)
  rcases (Nat.dvd_prime hp.out).1 h3 with h | h
  · exact orderOf_eq_one_iff.1 h
  · exfalso
    apply hnd
    have h4 := (orderOf_dvd_iff_zpow_eq_one (G := Lˣ)).2 h2
    rw [h] at h4
    exact h4

theorem rootChar_pow_eq_of_dvd {p : ℕ} {b : Fin τ.rank → Lˣ} (hbp : ∀ i, b i ^ p = 1) {q : ℕ}
    {e' : ℤ} (hq : (p : ℤ) ∣ (q : ℤ) - e') (x : Fin τ.rank → ℤ) :
    rootChar b x ^ q = rootChar b x ^ e' := by
  obtain ⟨m, hm⟩ := hq
  have hq' : (q : ℤ) = e' + p * m := by linarith
  have h2 : rootChar b x ^ p = 1 := CTTorus.rootChar_pow_eq_one hbp x
  rw [← zpow_natCast, hq', zpow_add, zpow_mul, zpow_natCast, h2, one_zpow, mul_one]

theorem twFixedPointFree_of_cert (hFr : ∀ c, Fr c = c ^ q) {u : WeylGroup τ}
    {N : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} (hN : ∀ x : Fin τ.rank → ℤ, u⁻¹ • x = N *ᵥ x)
    {p : ℕ} [hp : Fact p.Prime] {e' : ℤ} (hq : (p : ℤ) ∣ (q : ℤ) - e')
    {Y₁ Y₂ : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} {c : ℤ}
    (hcert : (M - e' • (1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ)) * Y₁ + (N - 1) * Y₂ =
      c • (1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ))
    (hc : ¬ (p : ℤ) ∣ c) {b : Fin τ.rank → Lˣ} (hb : b ∈ fixedCharTuples M Fr)
    (hbp : ∀ i, b i ^ p = 1) (hfix : weylTuple u b = b) : b = 1 := by
  refine eq_one_of_rootChar_cert hbp hcert hc (fun x => ?_) (fun x => ?_)
  · rw [Matrix.sub_mulVec, rootChar_sub, mem_fixedCharTuples_iff.1 hb, CTTorus.map_units_eq_pow hFr,
      rootChar_pow_eq_of_dvd hbp hq, Matrix.smul_mulVec, Matrix.one_mulVec, rootChar_zsmul]
    exact mul_inv_cancel _
  · rw [Matrix.sub_mulVec, rootChar_sub, Matrix.one_mulVec, ← hN, ← rootChar_weylTuple, hfix]
    exact mul_inv_cancel _

end Scalar

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross
