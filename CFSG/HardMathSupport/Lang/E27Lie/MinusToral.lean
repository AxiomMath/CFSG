module

public import CFSG.HardMathSupport.Lang.E27Lie.MinusToralCore
public import CFSG.HardMathSupport.Lang.E27Lie.TrialityOdd
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnSubB
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnH90
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnWeyl
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnFixedLine
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4FixedLine
public import CFSG.LocalAnalysis.OddStandard.GH71.S55D4Ord3Fr
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcLeviToral
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4TorusFrame
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTrialityOddEllMain
public import CFSG.RankThree.PartOne.CTP.SeitzThree
public import CFSG.RankThree.PartOne.CTP.StrongPFinal
public import CFSG.RankThree.PartOne.S12.InputsBase
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Lang.E27Lie

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.GH74.GLS.Stage2.OddAut
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Chevalley.TrialityFold
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped Matrix

section Kappa

variable {L : Type} [Field L]

theorem kappa_form {M : ModGL TwistTag.D4.tag L} (hM : M ∈ monomialSubgroup TwistTag.D4.tag L)
    {w : WeylGroup TwistTag.D4.tag} (hMw : MapsRootLines M w) (hw : w ∈ relWeylTwist TwistTag.D4)
    (hw1 : w ≠ 1) (hw3 : w ^ 3 = 1) (b : Lˣ) (hb : b ^ 3 = 1) :
    ∃ x : Lˣ, (x = b ∨ x = b⁻¹) ∧
      M⁻¹ * rootDiagUnit TwistTag.D4.tag ![1, 1, b, 1] * M *
        (rootDiagUnit TwistTag.D4.tag ![1, 1, b, 1])⁻¹ =
      rootDiagUnit TwistTag.D4.tag ![x, x, 1, x] := by
  have hconj := CFSG.OddStandard.GH71.S55.monomial_conj_rootDiagUnit (inv_mem hM) hMw.inv
    (![1, 1, b, 1] : Fin TwistTag.D4.tag.rank → Lˣ)
  rw [inv_inv] at hconj
  obtain ⟨M₀, hM₀, hsmul⟩ := d4_relWeylTwist_order_three_smul hw hw3
  have hcol : ∀ i : Fin TwistTag.D4.tag.rank,
      w • (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ) = M₀.mulVec (Pi.single i 1) :=
    fun i => hsmul _
  have hd : (rootDiagUnit TwistTag.D4.tag (![1, 1, b, 1] : Fin TwistTag.D4.tag.rank → Lˣ))⁻¹ =
      rootDiagUnit TwistTag.D4.tag (![1, 1, b, 1] : Fin TwistTag.D4.tag.rank → Lˣ)⁻¹ :=
    rootDiagUnit_inv _
  have key : ∀ i : Fin TwistTag.D4.tag.rank,
      weylTuple w⁻¹ (![1, 1, b, 1] : Fin TwistTag.D4.tag.rank → Lˣ) i =
        b ^ (M₀.mulVec (Pi.single i 1) (2 : Fin 4)) := by
    intro i
    simp only [weylTuple, inv_inv, hcol]
    refine (rootChar_d4_apply _ _).trans ?_
    simp
  have hb2 : b ^ (-2 : ℤ) * b⁻¹ = 1 := by
    calc b ^ (-2 : ℤ) * b⁻¹ = b ^ (-3 : ℤ) := by
          rw [← zpow_neg_one, ← zpow_add]; norm_num
      _ = 1 := by
          rw [zpow_neg, show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hb, inv_one]
  have hb2' : (b ^ 2)⁻¹ * b⁻¹ = 1 := by
    rw [← mul_inv_rev, show b * b ^ 2 = b ^ 3 by group, hb, inv_one]
  have hA : ∀ i : Fin TwistTag.D4.tag.rank,
      (d4MatThreeA.mulVec (Pi.single i 1)) (2 : Fin 4) = ![-1, -1, 1, -1] i := by
    intro i
    fin_cases i <;> decide +kernel
  have hB : ∀ i : Fin TwistTag.D4.tag.rank,
      (d4MatThreeB.mulVec (Pi.single i 1)) (2 : Fin 4) = ![1, 1, -2, 1] i := by
    intro i
    fin_cases i <;> decide +kernel
  rw [hconj, hd, ← rootDiagUnit_mul]
  rcases hM₀ with rfl | rfl | rfl
  · exact absurd (ext_single fun j => by rw [hcol j, one_smul]; exact Matrix.one_mulVec _) hw1
  · refine ⟨b⁻¹, Or.inr rfl, ?_⟩
    congr 1
    funext i
    rw [Pi.mul_apply, key, hA]
    have hfin : ∀ j : Fin 4, b ^ (![-1, -1, 1, -1] : Fin 4 → ℤ) j *
        ((![1, 1, b, 1] : Fin 4 → Lˣ)⁻¹) j = (![b⁻¹, b⁻¹, 1, b⁻¹] : Fin 4 → Lˣ) j := by
      intro j
      fin_cases j <;> simp [Pi.inv_apply]
    exact hfin i
  · refine ⟨b, Or.inl rfl, ?_⟩
    congr 1
    funext i
    rw [Pi.mul_apply, key, hB]
    have hfin : ∀ j : Fin 4, b ^ (![1, 1, -2, 1] : Fin 4 → ℤ) j *
        ((![1, 1, b, 1] : Fin 4 → Lˣ)⁻¹) j = (![b, b, 1, b] : Fin 4 → Lˣ) j := by
      intro j
      fin_cases j <;> simp [Pi.inv_apply, hb2']
    exact hfin i

end Kappa


section Arith

variable {L : Type} [Field L]

theorem unit_pow_of_mod_three {x : Lˣ} (hx : x ^ 3 = 1) {Q : ℕ} (hQ : Q % 3 = 2) :
    x ^ Q = x⁻¹ := by
  have h : Q = 2 + 3 * (Q / 3) := by omega
  rw [h, pow_add, pow_mul, hx, one_pow, mul_one]
  rw [eq_inv_iff_mul_eq_one, ← pow_succ]
  exact hx

theorem h90_equations {Q : ℕ} (hQ : Q % 3 = 2) {x : Lˣ} (hx : x ^ 3 = 1) {a : Lˣ}
    (ha : a ^ (Q + 1) = x) :
    a ^ (Q ^ 3 + 1) = 1 ∧
    d4Tuple x x 1 x * (fun i => d4QTuple Q 1 a (TwistTag.D4.perm i)) = d4QTuple Q 1 a := by
  have hxQ : x ^ Q = x⁻¹ := unit_pow_of_mod_three hx hQ
  have hx2 : x * x = x⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_three']
    exact hx
  have hxx : x⁻¹ * x⁻¹ = x := by rw [← mul_inv_rev, hx2, inv_inv]
  have haQ : a ^ Q = x * a⁻¹ := by
    rw [pow_succ] at ha
    rw [← ha]
    group
  have haQQ : a ^ (Q * Q) = x * a := by
    rw [pow_mul, haQ, mul_pow, inv_pow, haQ, hxQ, mul_inv_rev, inv_inv, mul_comm a x⁻¹,
      ← mul_assoc, hxx]
  refine ⟨?_, ?_⟩
  · rw [show Q ^ 3 = Q * Q * Q by ring, pow_succ, pow_mul, haQQ, mul_pow, hxQ, haQ]
    group
  · funext j
    rcases fin_cases j with rfl | rfl | rfl | rfl
    · rw [Pi.mul_apply, perm_i0]
      change x * (a ^ Q)⁻¹ = a
      rw [haQ, mul_inv_rev, inv_inv, mul_comm a x⁻¹, ← mul_assoc, mul_inv_cancel, one_mul]
    · rw [Pi.mul_apply, perm_i1]
      change x * a ^ (Q * Q) = (a ^ Q)⁻¹
      rw [haQQ, haQ, mul_inv_rev, inv_inv, ← mul_assoc, hx2, mul_comm]
    · rw [Pi.mul_apply, perm_i2]
      change (1 : Lˣ) * 1 = 1
      exact mul_one 1
    · rw [Pi.mul_apply, perm_i3]
      change x * a = a ^ (Q * Q)
      rw [haQQ]

end Arith

section Frame

variable {L : Type} [Field L]

theorem rootDiagUnit_tuple_pow_three {x : Lˣ} (hx : x ^ 3 = 1) :
    rootDiagUnit TwistTag.D4.tag (d4Tuple x x 1 x) ^ 3 = 1 := by
  have h : (rootDiagUnitHom TwistTag.D4.tag L) (d4Tuple x x 1 x) ^ 3 = 1 := by
    rw [← map_pow]
    have : d4Tuple x x 1 x ^ 3 = (1 : Fin TwistTag.D4.tag.rank → Lˣ) := by
      funext j
      rcases fin_cases j with rfl | rfl | rfl | rfl
      · exact hx
      · exact hx
      · exact one_pow 3
      · exact hx
    rw [this, map_one]
  exact h

end Frame

variable {p f : ℕ} [Fact p.Prime]

theorem minusToral_frame (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hf : 1 ≤ f)
    (hq : (p ^ f) % 3 = 2) (K : Type) [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) (L : Type) [Field L] [Algebra K L]
    [IsAlgClosure K L] [CharP L p] {g₀ : ModGL TwistTag.D4.tag L} (hg₀ : D4MinusFrame p f L g₀)
    (b : Lˣ) (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1)
    (s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hsψ : d4MinusPsi σ L g₀ s = rootDiagUnit TwistTag.D4.tag (![1, 1, b, 1] :
      Fin TwistTag.D4.tag.rank → Lˣ)) :
    27 ∣ Nat.card (fixedSubgroup (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ)) := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  obtain ⟨hg₀C, hg₀P, hg₀F⟩ := id hg₀
  set Fr : L →+* L := iterateFrobenius L p f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (p ^ f) := fun c => iterateFrobenius_def p f c
  have hcomm : (algebraMap K L).comp σ.toRingHom = Fr.comp (algebraMap K L) :=
    RingHom.ext fun c => by simp [hσ, hFr, map_pow]
  set ψ := d4MinusPsi σ L g₀ with hψ
  have hinj : Function.Injective ψ := d4MinusPsi_injective g₀
  set δ := fieldActor (t := TwistTag.D4) σ σ with hδ
  set P := diagramMap TwistTag.D4 L with hP
  have hψδ : ∀ y, ψ (δ y) = P⁻¹ * ψ y * P := fun y => d4MinusPsi_fieldActor Fr hcomm hg₀P y
  have hrange : ∀ x ∈ twistedTorusOf (trialityOpposition L) (twistHom TwistTag.D4 L Fr),
      ∃ y, ψ y = x := fun x hx =>
    (d4MinusPsi_mem_range_iff hp hf hK hσ Fr hFr hg₀C hg₀F x).2
      ⟨twistedTorusOf_le_adjointGroup _ _ hx, (mem_twistedTorusOf.1 hx).2⟩
  obtain ⟨T', m', hT', hm'T, hm'3, hm'n, hm'δ, -, -, -, hm'mono, hm'tor⟩ :=
    d4Minus_exists_N' hf hq hK hσ hg₀
  set M := ψ m' with hMdef
  have hMP : P⁻¹ * M * P = M := by rw [← hψδ, hm'δ]
  have hbQ : b ^ (p ^ f + 1) = 1 := by
    have : p ^ f + 1 = 3 * ((p ^ f + 1) / 3) := by omega
    rw [this, pow_mul, hb3, one_pow]
  have hdT := d4Minus_s0_mem Fr hFr hbQ
  set d := rootDiagUnit TwistTag.D4.tag (![1, 1, b, 1] : Fin TwistTag.D4.tag.rank → Lˣ) with hd
  have hsT : s ∈ T' := (hT' s).2 (by rw [hsψ]; exact hdT)
  have hcomm_t : ∀ a a' : Fin TwistTag.D4.tag.rank → Lˣ,
      rootDiagUnit TwistTag.D4.tag a * rootDiagUnit TwistTag.D4.tag a' =
        rootDiagUnit TwistTag.D4.tag a' * rootDiagUnit TwistTag.D4.tag a := fun a a' => by
    rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
  obtain ⟨w, k, hk, hMk⟩ := monomialSubgroup_le_torusWeylCosets hm'mono
  have hMw : MapsRootLines M w := hMk ▸ mapsRootLines_mul_canonicalRep hk w
  have hMF : trialityOpposition L * twistHom TwistTag.D4 L Fr M * (trialityOpposition L)⁻¹ = M :=
    ((d4MinusPsi_mem_range_iff hp hf hK hσ Fr hFr hg₀C hg₀F M).1 ⟨m', rfl⟩).2
  have hw : w ∈ relWeylTwist TwistTag.D4 :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.d4MnFL_relWeylTwist_of_fixed Fr hk hMk hMF
  have hw1 : w ≠ 1 := fun h => hm'tor (mem_torusGroup_of_mapsRootLines_one hm'mono (h ▸ hMw))
  have hM3 : M ^ 3 ∈ torusGroup TwistTag.D4.tag L := by
    have h3 := (hT' _).1 hm'3
    rw [map_pow] at h3
    exact (mem_twistedTorusOf.1 h3).1
  have hw3 : w ^ 3 = 1 :=
    (d4Minus_mapsRootLines_pow hMw 3).unique (mapsRootLines_of_mem_torusGroup hM3)
  obtain ⟨x, hx, hκ⟩ := kappa_form hm'mono hMw hw hw1 hw3 b hb3
  have hx3 : x ^ 3 = 1 := by
    rcases hx with rfl | rfl
    · exact hb3
    · rw [inv_pow, hb3, inv_one]
  have hx1 : x ≠ 1 := by
    rcases hx with rfl | rfl
    · exact hb1
    · exact inv_ne_one.2 hb1
  have hκ1 : M⁻¹ * d * M * d⁻¹ = rootDiagUnit TwistTag.D4.tag (d4Tuple x x 1 x) := hκ
  set Dκ := rootDiagUnit TwistTag.D4.tag (d4Tuple x x 1 x) with hDκ
  obtain ⟨a₀, ha₀⟩ : ∃ a : Lˣ, a ^ (p ^ f + 1) = x := by
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (x : L) (Nat.succ_pos (p ^ f))
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [zero_pow (Nat.succ_ne_zero _)] at hr
      exact x.ne_zero hr.symm
    exact ⟨Units.mk0 r hr0, Units.ext (by simpa using hr)⟩
  obtain ⟨hQ3, hQeq⟩ := h90_equations hq hx3 ha₀
  have hDt : rootDiagUnit TwistTag.D4.tag (d4QTuple (p ^ f) 1 a₀) ∈
      twistedTorusOf (trialityOpposition L) (twistHom TwistTag.D4 L Fr) := by
    rw [d4Q_twistedTorus Fr]
    exact ⟨d4QTuple (p ^ f) 1 a₀, d4QTuple_mem hFr (one_pow _) hQ3, rfl⟩
  obtain ⟨y₁, hy₁⟩ := hrange _ hDt
  have hy₁T : y₁ ∈ T' := (hT' y₁).2 (by rw [hy₁]; exact hDt)
  set φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := MulAut.conj s * δ with hφdef
  have hψφ : ∀ y, ψ (φ y) = d * (P⁻¹ * ψ y * P) * d⁻¹ := by
    intro y
    have : φ y = s * δ y * s⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv, hψδ, hsψ]
  have hPconj : ∀ a : Fin TwistTag.D4.tag.rank → Lˣ,
      P⁻¹ * rootDiagUnit TwistTag.D4.tag a * P =
        rootDiagUnit TwistTag.D4.tag (fun i => a (TwistTag.D4.perm i)) := fun a =>
    d4Minus_h90_conj a
  have hmφ : φ (m' * y₁) = m' * y₁ := by
    apply hinj
    rw [hψφ, map_mul, hy₁]
    have e1 : P⁻¹ * (M * rootDiagUnit TwistTag.D4.tag (d4QTuple (p ^ f) 1 a₀)) * P =
        M * rootDiagUnit TwistTag.D4.tag (fun i => d4QTuple (p ^ f) 1 a₀ (TwistTag.D4.perm i)) := by
      rw [show P⁻¹ * (M * rootDiagUnit TwistTag.D4.tag (d4QTuple (p ^ f) 1 a₀)) * P =
        (P⁻¹ * M * P) * (P⁻¹ * rootDiagUnit TwistTag.D4.tag (d4QTuple (p ^ f) 1 a₀) * P) by
        group, hMP, hPconj]
    rw [e1]
    set D' := rootDiagUnit TwistTag.D4.tag
      (fun i => d4QTuple (p ^ f) 1 a₀ (TwistTag.D4.perm i)) with hD'
    have h2 : d * M = M * (Dκ * d) := by
      calc d * M = M * (M⁻¹ * d * M) := by group
        _ = M * (Dκ * d) := by rw [← hκ1]; group
    have h3 : Dκ * D' = rootDiagUnit TwistTag.D4.tag (d4QTuple (p ^ f) 1 a₀) := by
      rw [hDκ, hD', ← rootDiagUnit_mul, hQeq]
    have hcdD : d * D' = D' * d := hcomm_t _ _
    calc d * (M * D') * d⁻¹ = (d * M) * D' * d⁻¹ := by group
      _ = M * (Dκ * d) * D' * d⁻¹ := by rw [h2]
      _ = M * Dκ * (d * D') * d⁻¹ := by group
      _ = M * Dκ * (D' * d) * d⁻¹ := by rw [hcdD]
      _ = M * (Dκ * D') := by group
      _ = M * rootDiagUnit TwistTag.D4.tag (d4QTuple (p ^ f) 1 a₀) := by rw [h3]
  set u₁ := m'⁻¹ * s * m' * s⁻¹ with hu₁def
  have hu₁ψ : ψ u₁ = Dκ := by
    rw [hu₁def, map_mul, map_mul, map_mul, map_inv, map_inv, hsψ]
    exact hκ1
  have hu₁T : u₁ ∈ T' :=
    T'.mul_mem (mnWeyl_inv_mul_mul_mem hm'3 hm'n hsT) (T'.inv_mem hsT)
  have hκperm : (fun i => d4Tuple x x 1 x (TwistTag.D4.perm i)) = d4Tuple x x 1 x := by
    funext j
    rcases fin_cases j with rfl | rfl | rfl | rfl
    · rw [perm_i0]; rfl
    · rw [perm_i1]; rfl
    · rw [perm_i2]
    · rw [perm_i3]; rfl
  have hu₁φ : φ u₁ = u₁ := by
    apply hinj
    rw [hψφ, hu₁ψ, hDκ, hPconj, hκperm, ← hDκ]
    have hc : d * Dκ = Dκ * d := hcomm_t _ _
    rw [hc]
    group
  have hsφ : φ s = s := by
    apply hinj
    have hcd : P⁻¹ * d * P = d := d4Minus_s0_comm b
    rw [hψφ, hsψ, hcd]
    group
  have hcu : u₁ * s = s * u₁ := by
    apply hinj
    rw [map_mul ψ u₁ s, map_mul ψ s u₁, hu₁ψ, hsψ]
    exact hcomm_t _ _
  have hu₁3 : u₁ ^ 3 = 1 := by
    apply hinj
    rw [map_pow, hu₁ψ, map_one]
    exact rootDiagUnit_tuple_pow_three hx3
  have hu₁1 : u₁ ≠ 1 := by
    intro h
    have h1 := congrArg ψ h
    rw [hu₁ψ, map_one, hDκ, ← rootDiagUnit_one (τ := TwistTag.D4.tag) (K := L)] at h1
    have h2 := congrFun (rootDiagUnit_injective h1) i0
    exact hx1 h2
  have hs3 : s ^ 3 = 1 := by
    apply hinj
    rw [map_pow, hsψ, map_one]
    exact d4Minus_s0_pow3 hb3
  have hsn : s ∉ Subgroup.zpowers u₁ := by
    rintro ⟨k, hk⟩
    have h1 := congrArg ψ hk
    rw [map_zpow, hu₁ψ, hsψ, hDκ] at h1
    have h2 : rootDiagUnit TwistTag.D4.tag (d4Tuple x x 1 x ^ k) =
        rootDiagUnit TwistTag.D4.tag (![1, 1, b, 1] : Fin TwistTag.D4.tag.rank → Lˣ) := by
      exact (map_zpow (rootDiagUnitHom TwistTag.D4.tag L) (d4Tuple x x 1 x) k).trans h1
    have h3 := congrFun (rootDiagUnit_injective h2) i2
    rw [Pi.pow_apply] at h3
    have h4 : (1 : Lˣ) ^ k = b := h3
    exact hb1 (by simpa using h4.symm)
  have hm : ∀ t ∈ T', (m' * y₁) * t * (m' * y₁)⁻¹ ∈ T' := by
    intro t ht
    have e : (m' * y₁) * t * (m' * y₁)⁻¹ = m' * (y₁ * t * y₁⁻¹) * m'⁻¹ := by group
    rw [e]
    exact hm'n _ (T'.mul_mem (T'.mul_mem hy₁T ht) (T'.inv_mem hy₁T))
  have hm3 : (m' * y₁) ^ 3 ∈ T' := by
    have hc1 := mnWeyl_inv_mul_mul_mem hm'3 hm'n hy₁T
    have hc2 := mnWeyl_inv_mul_mul_mem hm'3 hm'n hc1
    have e : (m' * y₁) ^ 3 = m' ^ 3 * (m'⁻¹ * (m'⁻¹ * y₁ * m') * m') * (m'⁻¹ * y₁ * m') * y₁ := by
      rw [pow_three' (m' * y₁)]
      group
    rw [e]
    exact T'.mul_mem (T'.mul_mem (T'.mul_mem hm'3 hc2) hc1) hy₁T
  have hmT : m' * y₁ ∉ T' := by
    intro h
    apply hm'T
    have := T'.mul_mem h (T'.inv_mem hy₁T)
    rwa [mul_inv_cancel_right] at this
  exact dvd_card_of_torus_lift (φ := φ) (C := fixedSubgroup φ) (fun x => Iff.rfl) hm hm3 hmT hmφ
    hu₁T hsT hu₁φ hsφ hcu hu₁3 hu₁1 hs3 hsn

theorem minusToralLower_holds : MinusToralLower := by
  intro p f hp hp2 hp3 hf hq K _ _ hK σ hσ s hs _
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨L, _, _, _, _, g₀, b, hframe, hb3, hb1, hsL⟩ := hs
  refine minusToral_frame hp hp2 hp3 hf hq K hK σ hσ L hframe b hb3 hb1 s ?_
  rw [d4MinusPsi_apply, hsL]
  group

end CFSG.HardMathSupport.Lang.E27Lie
