module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015NLSymplectic
import CFSG.SignalizerFunctorTheorem.NonLocal.SpTwoTwo
import CFSG.SignalizerFunctorTheorem.NonLocal.Cross
import CFSG.SignalizerFunctorTheorem.NonLocal.SpData

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2015

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA.MI
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.PartOne.KCSpComm CFSG.RankThree.Classical
  CFSG.ComponentClassification.PresentationLocal
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.ComponentClassification.UnbalancedCatalog (descentField)
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (subfieldSpHom)
open scoped commutatorElement Matrix

section Irreducible

variable {r : ℕ} {K : Type} [Field K]

private theorem sympCommAct {u v : Fin r ⊕ Fin r → K} (huv : spForm r K u v = 1)
    (y : Fin r ⊕ Fin r → K) :
    spEnd ⁅spTransvection u 1, spTransvection v 1⁆ y =
      y + spForm r K y u • u - (spForm r K y u + spForm r K y v) • v := by
  have h1 : spForm r K u u = 0 := spForm_isAlt.self_eq_zero u
  have h2 : spForm r K v v = 0 := spForm_isAlt.self_eq_zero v
  have h3 : spForm r K v u = -1 := by rw [← spForm_isAlt.neg_eq u v, huv]
  rw [commutatorElement_def, spEnd_mul, spEnd_mul, spEnd_mul, spTransvection_inv,
    spTransvection_inv]
  simp only [Module.End.mul_apply, spEnd_spTransvection, map_add, map_smul, map_sub, map_neg,
    LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.neg_apply,
    huv, h1, h2, h3, smul_eq_mul]
  module

private theorem sympInvN (k : Subfield K) (W : Submodule K (Fin r ⊕ Fin r → K))
    (hW : ∀ g ∈ commutator (StatedSp r k), ∀ w ∈ W, spEnd (subfieldSpHom r k g) w ∈ W)
    (u₀ v₀ : Fin r ⊕ Fin r → k) (huv : spForm r k u₀ v₀ = 1) {w : Fin r ⊕ Fin r → K}
    (hw : w ∈ W) :
    spForm r K w (fun a => (u₀ a : K)) • (fun a => (u₀ a : K)) -
      (spForm r K w (fun a => (u₀ a : K)) + spForm r K w (fun a => (v₀ a : K))) •
        (fun a => (v₀ a : K)) ∈ W := by
  set u : Fin r ⊕ Fin r → K := fun a => (u₀ a : K) with hu
  set v : Fin r ⊕ Fin r → K := fun a => (v₀ a : K) with hv
  have huvK : spForm r K u v = 1 := by
    have h := spForm_map k.subtype u₀ v₀
    rw [huv, map_one] at h
    exact h
  have hc : ⁅spTransvection u₀ (1 : k), spTransvection v₀ (1 : k)⁆ ∈ commutator (StatedSp r k) :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hj : subfieldSpHom r k ⁅spTransvection u₀ (1 : k), spTransvection v₀ (1 : k)⁆ =
      ⁅spTransvection u (1 : K), spTransvection v (1 : K)⁆ := by
    rw [map_commutatorElement, subfieldSpHom_spTransvection, subfieldSpHom_spTransvection]
    rfl
  have h1 := hW _ hc w hw
  rw [hj, sympCommAct huvK] at h1
  have h2 := W.sub_mem h1 hw
  have h3 : w + spForm r K w u • u - (spForm r K w u + spForm r K w v) • v - w =
      spForm r K w u • u - (spForm r K w u + spForm r K w v) • v := by abel
  rwa [h3] at h2

private theorem sympForm_sub (k : Subfield K) (a b : Fin r ⊕ Fin r → k) :
    spForm r K (fun i => (a i : K)) (fun i => (b i : K)) = ((spForm r k a b : k) : K) :=
  spForm_map (k.subtype : k →+* K) a b

private theorem sympInvPi (k : Subfield K) (W : Submodule K (Fin r ⊕ Fin r → K))
    (hW : ∀ g ∈ commutator (StatedSp r k), ∀ w ∈ W, spEnd (subfieldSpHom r k g) w ∈ W)
    (u₀ v₀ : Fin r ⊕ Fin r → k) (h12 : spForm r k u₀ v₀ = 1) (h21 : spForm r k v₀ u₀ = 1)
    {w : Fin r ⊕ Fin r → K} (hw : w ∈ W) :
    spForm r K w (fun a => (v₀ a : K)) • (fun a => (u₀ a : K)) +
      spForm r K w (fun a => (u₀ a : K)) • (fun a => (v₀ a : K)) ∈ W := by
  have h1 := sympInvN k W hW u₀ v₀ h12 hw
  have h2 := sympInvN k W hW v₀ u₀ h21 hw
  have h3 := W.neg_mem (W.add_mem h1 h2)
  convert h3 using 1
  module

private theorem sympInvE (k : Subfield K) (W : Submodule K (Fin r ⊕ Fin r → K))
    (hW : ∀ g ∈ commutator (StatedSp r k), ∀ w ∈ W, spEnd (subfieldSpHom r k g) w ∈ W)
    (x y x' y' : Fin r ⊕ Fin r → k)
    (hxy : spForm r k x y = 1) (hyx : spForm r k y x = 1)
    (hxy' : spForm r k x' y' = 1) (hyx' : spForm r k y' x' = 1)
    (h1 : spForm r k x' x = 0) (h2 : spForm r k x' y = 0) (h3 : spForm r k y' x = 0)
    (h4 : spForm r k y' y = 1) {w : Fin r ⊕ Fin r → K} (hw : w ∈ W) :
    spForm r K w (fun a => (x' a : K)) • (fun a => (x a : K)) ∈ W := by
  have hw' := sympInvPi k W hW x' y' hxy' hyx' hw
  have hw'' := sympInvPi k W hW x y hxy hyx hw'
  convert hw'' using 1
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    sympForm_sub, h1, h2, h3, h4]
  simp

private theorem sympE_data : ∀ x x' : Fin 2 ⊕ Fin 2, x' ≠ x → x' ≠ Sum.swap x →
    spForm 2 (ZMod 2) (Pi.single x 1) (Pi.single (Sum.swap x) 1) = 1 ∧
    spForm 2 (ZMod 2) (Pi.single (Sum.swap x) 1) (Pi.single x 1) = 1 ∧
    spForm 2 (ZMod 2) (Pi.single x' 1) (Pi.single (Sum.swap x') 1 + Pi.single x 1) = 1 ∧
    spForm 2 (ZMod 2) (Pi.single (Sum.swap x') 1 + Pi.single x 1) (Pi.single x' 1) = 1 ∧
    spForm 2 (ZMod 2) (Pi.single x' 1) (Pi.single x 1) = 0 ∧
    spForm 2 (ZMod 2) (Pi.single x' 1) (Pi.single (Sum.swap x) 1) = 0 ∧
    spForm 2 (ZMod 2) (Pi.single (Sum.swap x') 1 + Pi.single x 1) (Pi.single x 1) = 0 ∧
    spForm 2 (ZMod 2) (Pi.single (Sum.swap x') 1 + Pi.single x 1)
      (Pi.single (Sum.swap x) 1) = 1 := by
  decide

private theorem sympCharP_two {k : Type} [Field k] (hk : Nat.card k = 2) : CharP k 2 := by
  have : Finite k := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype k := Fintype.ofFinite k
  have hk' : Fintype.card k = 2 := by rw [← Nat.card_eq_fintype_card]; exact hk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime hk'

private theorem sympCoeSingle (k : Subfield K) (ι : ZMod 2 →+* k) (b : Fin r ⊕ Fin r) :
    (fun a => ((ι ∘ (Pi.single b (1 : ZMod 2) : Fin r ⊕ Fin r → ZMod 2)) a : K)) =
      (Pi.single b 1 : Fin r ⊕ Fin r → K) := by
  ext a
  by_cases h : a = b <;> simp [h]

private theorem sympInvE2 (k : Subfield K) (hk : Nat.card k = 2)
    (W : Submodule K (Fin 2 ⊕ Fin 2 → K))
    (hW : ∀ g ∈ commutator (StatedSp 2 k), ∀ w ∈ W, spEnd (subfieldSpHom 2 k g) w ∈ W)
    (x x' : Fin 2 ⊕ Fin 2) (h1 : x' ≠ x) (h2 : x' ≠ Sum.swap x) {w : Fin 2 ⊕ Fin 2 → K}
    (hw : w ∈ W) :
    spForm 2 K w (Pi.single x' 1) • (Pi.single x 1 : Fin 2 ⊕ Fin 2 → K) ∈ W := by
  have := sympCharP_two hk
  let ι : ZMod 2 →+* k := ZMod.castHom (dvd_refl 2) k
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩ := sympE_data x x' h1 h2
  have key := sympInvE k W hW (ι ∘ Pi.single x 1) (ι ∘ Pi.single (Sum.swap x) 1)
    (ι ∘ Pi.single x' 1) (ι ∘ (Pi.single (Sum.swap x') 1 + Pi.single x 1))
    (by rw [spForm_map ι, d1, map_one]) (by rw [spForm_map ι, d2, map_one])
    (by rw [spForm_map ι, d3, map_one]) (by rw [spForm_map ι, d4, map_one])
    (by rw [spForm_map ι, d5, map_zero]) (by rw [spForm_map ι, d6, map_zero])
    (by rw [spForm_map ι, d7, map_zero]) (by rw [spForm_map ι, d8, map_one]) hw
  rwa [sympCoeSingle, sympCoeSingle] at key

open CFSG.SignalizerFunctorTheorem.NonLocal in
theorem sympIrreducibleCommutator (k : Subfield K) (hk : Nat.card k = 2)
    (W : Submodule K (Fin 2 ⊕ Fin 2 → K))
    (hW : ∀ g ∈ commutator (StatedSp 2 k), ∀ w ∈ W, spEnd (subfieldSpHom 2 k g) w ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  classical
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  have hE := sympInvE2 k hk W hW
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨z, hz⟩ : ∃ z : Fin 2 ⊕ Fin 2, spForm 2 K w (Pi.single z 1) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hw0
    refine spForm_nondegenerate.1 w (fun n => ?_)
    have hn : n = ∑ c, n c • (Pi.single c (1 : K) : Fin 2 ⊕ Fin 2 → K) := by
      ext x
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hn, map_sum]
    simp [hcon]
  have h1 : ∀ x : Fin 2 ⊕ Fin 2, z ≠ x → z ≠ Sum.swap x →
      (Pi.single x 1 : Fin 2 ⊕ Fin 2 → K) ∈ W := by
    intro x hx1 hx2
    have h := W.smul_mem (spForm 2 K w (Pi.single z 1))⁻¹ (hE x z hx1 hx2 hwW)
    rwa [smul_smul, inv_mul_cancel₀ hz, one_smul] at h
  have hex : ∀ z : Fin 2 ⊕ Fin 2, ∃ x₀ : Fin 2 ⊕ Fin 2, z ≠ x₀ ∧ z ≠ Sum.swap x₀ := by decide
  obtain ⟨x₀, hx₀1, hx₀2⟩ := hex z
  have hex₀ := h1 x₀ hx₀1 hx₀2
  obtain ⟨ε, hε, hεb⟩ := exists_spForm_single (K := K) x₀
  have hne : spForm 2 K (Pi.single x₀ 1) (Pi.single (Sum.swap x₀) 1) ≠ 0 := by
    rw [hεb]
    simp [hε]
  have h2 : ∀ x : Fin 2 ⊕ Fin 2, Sum.swap x₀ ≠ x → Sum.swap x₀ ≠ Sum.swap x →
      (Pi.single x 1 : Fin 2 ⊕ Fin 2 → K) ∈ W := by
    intro x hx1 hx2
    have h := W.smul_mem (spForm 2 K (Pi.single x₀ 1) (Pi.single (Sum.swap x₀) 1))⁻¹
      (hE x (Sum.swap x₀) hx1 hx2 hex₀)
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at h
  have hcomb : ∀ z x₀ c : Fin 2 ⊕ Fin 2, z ≠ x₀ → z ≠ Sum.swap x₀ →
      (z ≠ c ∧ z ≠ Sum.swap c) ∨ (Sum.swap x₀ ≠ c ∧ Sum.swap x₀ ≠ Sum.swap c) := by decide
  have hall : ∀ c : Fin 2 ⊕ Fin 2, (Pi.single c 1 : Fin 2 ⊕ Fin 2 → K) ∈ W := by
    intro c
    rcases hcomb z x₀ c hx₀1 hx₀2 with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact h1 c ha hb
    · exact h2 c ha hb
  rw [eq_top_iff]
  intro v _
  have hv : v = ∑ c, v c • (Pi.single c (1 : K) : Fin 2 ⊕ Fin 2 → K) := by
    ext x
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hv]
  exact W.sum_mem (fun c _ => W.smul_mem _ (hall c))

open CFSG.SignalizerFunctorTheorem.NonLocal CFSG.SignalizerFunctorTheorem.CatalogBridge in
theorem sympNonLocalizedCommutator [Finite K] (k : Subfield K) (hk : Nat.card k = 2) :
    NonLocalized ((proj 2 K).comp
      ((subfieldSpHom 2 k).comp (commutator (StatedSp 2 k)).subtype)).range := by
  classical
  haveI : CharP K 2 := (RingHom.charP_iff k.subtype k.subtype.injective 2).mp (sympCharP_two hk)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nonempty (Fin 2 ⊕ Fin 2) := ⟨Sum.inl 0⟩
  let P := spProjData 2 K
  let φH : ↥(commutator (StatedSp 2 k)) →* StatedSp 2 K :=
    (subfieldSpHom 2 k).comp (commutator (StatedSp 2 k)).subtype
  have hirr : ∀ W : Submodule K (Fin 2 ⊕ Fin 2 → K),
      (∀ g : ↥(commutator (StatedSp 2 k)), ∀ n ∈ W,
        (P.ρ (φH g) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ n ∈ W) → W = ⊥ ∨ W = ⊤ :=
    fun W hW => sympIrreducibleCommutator k hk W (fun g hg w hw => hW ⟨g, hg⟩ w hw)
  have hrange : (P.π.comp (φH.comp (⊤ : Subgroup ↥(commutator (StatedSp 2 k))).subtype)).range =
      (P.π.comp φH).range := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g.1, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨⟨g, Subgroup.mem_top g⟩, rfl⟩
  refine P.nonLocalized_of_closing_gen φH
    (fun E hE hnorm => P.eq_bot_of_isPGroup φH hirr E hE hnorm) ⊤
    (by rw [hrange]; exact isSimpleGroup_range_commutator_sp_two_two k hk)
    (fun x hx => centralizer_commutator_sp_two_two k hk x fun n => hx ⟨n, Subgroup.mem_top n⟩) ?_
  intro s hs hsr V hV0 hVcomm hVexp hVnorm hfaith hup
  have : Finite (StatedProj (StatedSp 2 K)) :=
    Finite.of_surjective (proj 2 K) (proj_surjective (r := 2) (K := K))
  have : IsMulCommutative V := ⟨⟨fun a b => Subtype.ext (hVcomm _ a.2 _ b.2)⟩⟩
  have : Fact s.Prime := ⟨hs⟩
  have hVp : IsPGroup s V := by
    refine IsPGroup.iff_orderOf.mpr (fun g => ?_)
    have h1 : orderOf g ∣ s := orderOf_dvd_of_pow_eq_one (Subtype.ext (hVexp g g.2))
    rcases (Nat.dvd_prime hs).mp h1 with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hVp
  have hs3 : 3 ≤ s := by
    have := hs.two_le
    have : s ≠ 2 := hsr
    omega
  have hcard4 : Fintype.card (Fin 2 ⊕ Fin 2) = 4 := by
    rw [Fintype.card_sum, Fintype.card_fin]
  have hm3 : m ≤ 3 := by
    rcases hup with h | ⟨e, he, hdvd, hle⟩
    · rw [hm, hcard4] at h
      exact (Nat.pow_le_pow_iff_right hs.one_lt).mp h
    · rw [hm] at hdvd hle
      obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hs).mp hdvd
      rw [hcard4] at he
      have hj1 : j ≤ 1 := by
        by_contra hj
        have : s ^ 2 ≤ s ^ j := Nat.pow_le_pow_right (by omega) (by omega)
        have : 3 ^ 2 ≤ s ^ 2 := Nat.pow_le_pow_left hs3 2
        omega
      have hmj : m ≤ 2 * j := by
        rw [← pow_mul, mul_comm] at hle
        exact (Nat.pow_le_pow_iff_right hs.one_lt).mp hle
      omega
  exact sp_two_two_closing k hk hs hsr V hVexp hm hV0 (fun g hg v hv => hVnorm ⟨g, hg⟩ v hv)
    (fun g hg h => hfaith ⟨g, hg⟩ (Subgroup.mem_top _) h) hm3

end Irreducible

section Witness

variable {K : Type} [Field K] [Finite K]

private theorem sympAlt6_noncomm : ∃ a b : alternatingGroup (Fin 6), a * b ≠ b * a := by
  let p : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 1 2
  let q : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 1 3
  have hp : p ∈ alternatingGroup (Fin 6) :=
    Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)
  have hq : q ∈ alternatingGroup (Fin 6) :=
    Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)
  have hpq : p * q ≠ q * p := by decide +kernel
  exact ⟨⟨p, hp⟩, ⟨q, hq⟩, fun h => hpq (congrArg Subtype.val h)⟩

open CFSG.SignalizerFunctorTheorem.NonLocal in
theorem sympNLWitnessTwo (σ : K ≃+* K) (hk : Nat.card (descentField σ) = 2) :
    NLWitness (fieldAut 2 K σ : MulAut (LargeEvenProj (LargeEvenSpGroup K 2))) := by
  have hs := isSimpleGroup_range_commutator_sp_two_two (descentField σ) hk
  have hna : ∃ x y : ↥((proj 2 K).comp ((subfieldSpHom 2 (descentField σ)).comp
      (commutator (StatedSp 2 (descentField σ))).subtype)).range, x * y ≠ y * x := by
    obtain ⟨a, b, hab⟩ := sympAlt6_noncomm
    let e := rangeCommutatorEquiv (descentField σ) hk
    exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by rw [map_mul, map_mul]; exact h))⟩
  refine nlWitness_of_nonLocalized (MulEquiv.refl (StatedProj (StatedSp 2 K))) hs hna
    (sympNonLocalizedCommutator (descentField σ) hk) ?_
  rintro _ ⟨y, ⟨⟨g, hg⟩, rfl⟩, rfl⟩
  exact KCSpComm.fieldAut_subfieldProj σ g

theorem sympNLWitnessRes {p n : ℕ} (hn : 1 ≤ n) (hnp : n = p) (hK : Nat.card K = 2 ^ n)
    {f : MulAut (LargeEvenProj (LargeEvenSpGroup K 2))}
    (hf : f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSpGroup K 2)))
    (hord : orderOf f = p) : NLWitness f := by
  obtain ⟨σ, rfl, -, hcard⟩ := sympFieldAut_data (by norm_num) hn hK hf hord
  refine sympNLWitnessTwo σ ?_
  rw [hcard, ← hnp, Nat.div_self hn, pow_one]

end Witness

section Family

set_option linter.unusedSectionVars false


theorem i2015NLResSp4_holds : I2015NLResSp4 := by
  intro lab hlab ht
  refine atLabelWhen_of_witness hlab ?_ (fun p _ h => by
    rcases ht with ht | ht <;> rw [ht] at h <;> exact absurd h.1 (by decide))
  intro p _ _ _ _ hC Q hQ
  obtain ⟨t, r, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  obtain ⟨hr2, hnp⟩ : r = 2 ∧ n = p := hC
  subst hr2
  rcases ht with rfl | rfl <;>
  · dsimp only [CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
    refine NbrGraphSymplectic.recipeSymplectic_all (fun K _ _ hK => ?_) hQ
    intro _ _ _ f hf hord _ _
    exact sympNLWitnessRes hn hnp hK hf hord

end Family

end CFSG.LocalAnalysis.GLTheoremA.I2015

end
