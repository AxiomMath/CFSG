module

public import CFSG.ClassicalInvolution.Asc77.AscL62Aut
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1916

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped MatrixGroups commutatorElement

section SL23

@[expose] def elem3 : SL(2, ZMod 3) := ⟨!![1, 1; 0, 1], by decide⟩

theorem elem3_pow : elem3 ^ 3 = 1 := by decide +kernel

theorem sl23_eq_elem3 : ∀ g : SL(2, ZMod 3), g ^ 3 = 1 →
    (∀ p : SL(2, ZMod 3), p ^ 4 = 1 → g * p * g⁻¹ = elem3 * p * elem3⁻¹) → g = elem3 := by
  decide +kernel

theorem sl23_decomp : ∀ s : SL(2, ZMod 3), ∃ p : SL(2, ZMod 3), p ^ 4 = 1 ∧
    (s = p ∨ s = p * elem3 ∨ s = p * elem3 * elem3) := by
  decide +kernel

theorem sl23_card : Nat.card SL(2, ZMod 3) = 24 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem sl23_card_four :
    (Finset.univ.filter (fun p : SL(2, ZMod 3) => p ^ 4 = 1)).card = 8 := by
  decide +kernel

theorem sl23_pow24 : ∀ s : SL(2, ZMod 3), s ^ 24 = 1 := by decide +kernel

theorem sl23_pow_four_of_pow_eight : ∀ s : SL(2, ZMod 3), s ^ 8 = 1 → s ^ 4 = 1 := by
  decide +kernel

theorem sl23_pow_four_of_two_pow {s : SL(2, ZMod 3)} {k : ℕ} (h : s ^ 2 ^ k = 1) : s ^ 4 = 1 := by
  refine sl23_pow_four_of_pow_eight s ?_
  have h1 : orderOf s ∣ 24 := orderOf_dvd_of_pow_eq_one (sl23_pow24 s)
  have h2 : orderOf s ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  have h3 : a ≤ 3 := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ 4 ∣ orderOf s := by rw [ha]; exact pow_dvd_pow 2 hlt
    have := this.trans h1
    omega
  exact orderOf_dvd_iff_pow_eq_one.mp (by rw [ha]; exact (pow_dvd_pow 2 h3 : 2 ^ a ∣ 2 ^ 3))

theorem mem_sylow_sl23 (P : Sylow 2 SL(2, ZMod 3)) {s : SL(2, ZMod 3)} (hs : s ^ 4 = 1) :
    s ∈ P := by
  classical
  have hcard : Nat.card P = 8 := by
    rw [Sylow.card_eq_multiplicity, sl23_card]
    have : (24 : ℕ).factorization 2 = 3 := by
      rw [show (24 : ℕ) = 2 ^ 3 * 3 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
        Nat.Prime.factorization_pow Nat.prime_two]
      simp [Nat.factorization_eq_zero_of_not_dvd]
    rw [this]
    norm_num
  set T : Finset SL(2, ZMod 3) := Finset.univ.filter (fun p => p ∈ P) with hT
  set F : Finset SL(2, ZMod 3) := Finset.univ.filter (fun p : SL(2, ZMod 3) => p ^ 4 = 1)
    with hF
  have hTF : T ⊆ F := by
    intro x hx
    rw [hT, Finset.mem_filter] at hx
    rw [hF, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hx.2⟩
    exact sl23_pow_four_of_two_pow (congrArg Subtype.val hk)
  have hTcard : T.card = 8 := by
    rw [← hcard, Nat.card_eq_fintype_card, hT, ← Fintype.card_subtype]
    rfl
  have hTeq : T = F := Finset.eq_of_subset_of_card_le hTF (by rw [hTcard, hF, sl23_card_four])
  have hsF : s ∈ F := by rw [hF, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hs⟩
  rw [← hTeq, hT, Finset.mem_filter] at hsF
  exact hsF.2

theorem sl23_hom_eq_of_fixes (α : SL(2, ZMod 3) →* SL(2, ZMod 3))
    (hα : ∀ p : SL(2, ZMod 3), p ^ 4 = 1 → α p = p) (s : SL(2, ZMod 3)) : α s = s := by
  have hc : α elem3 = elem3 := by
    refine sl23_eq_elem3 _ (by rw [← map_pow, elem3_pow, map_one]) fun p hp => ?_
    have h1 : (elem3 * p * elem3⁻¹) ^ 4 = 1 := by rw [conj_pow, hp]; group
    calc α elem3 * p * (α elem3)⁻¹ = α (elem3 * p * elem3⁻¹) := by
          rw [map_mul, map_mul, map_inv, hα p hp]
      _ = elem3 * p * elem3⁻¹ := hα _ h1
  obtain ⟨p, hp, h | h | h⟩ := sl23_decomp s
  · rw [h, hα p hp]
  · rw [h, map_mul, hα p hp, hc]
  · rw [h, map_mul, map_mul, hα p hp, hc]

end SL23

section M3

@[expose] noncomputable def slEquiv {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) :
    SL(2, R) ≃* SL(2, S) :=
  MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map e.toRingHom)
    (Matrix.SpecialLinearGroup.map e.symm.toRingHom)
    (MonoidHom.ext fun A => Matrix.SpecialLinearGroup.ext _ _ fun i j => by simp)
    (MonoidHom.ext fun A => Matrix.SpecialLinearGroup.ext _ _ fun i j => by simp)

theorem mulAut_eq_one_of_fixes_sylow_three (P : Sylow 2 SL(2, GaloisField 3 1))
    (β : MulAut SL(2, GaloisField 3 1)) (hfix : ∀ x ∈ P, β x = x) : β = 1 := by
  set ψ : SL(2, GaloisField 3 1) ≃* SL(2, ZMod 3) :=
    slEquiv (GaloisField.equivZmodP 3).toRingEquiv with hψ
  let α : SL(2, ZMod 3) →* SL(2, ZMod 3) :=
    (ψ.toMonoidHom.comp (β : SL(2, GaloisField 3 1) →* SL(2, GaloisField 3 1))).comp
      ψ.symm.toMonoidHom
  let P' : Sylow 2 SL(2, ZMod 3) := Sylow.mapSurjective (f := ψ.toMonoidHom) ψ.surjective P
  have hα : ∀ p : SL(2, ZMod 3), p ^ 4 = 1 → α p = p := by
    intro p hp
    have hpP : p ∈ P' := mem_sylow_sl23 P' hp
    have hpP' : p ∈ (P : Subgroup SL(2, GaloisField 3 1)).map ψ.toMonoidHom := by
      rw [← Sylow.coe_mapSurjective (f := ψ.toMonoidHom) ψ.surjective P]
      exact hpP
    obtain ⟨x, hx, rfl⟩ := hpP'
    change ψ (β (ψ.symm (ψ x))) = ψ x
    rw [MulEquiv.symm_apply_apply, hfix x hx]
  ext x : 1
  have h1 := sl23_hom_eq_of_fixes α hα (ψ x)
  change ψ (β (ψ.symm (ψ x))) = ψ x at h1
  rw [MulEquiv.symm_apply_apply] at h1
  exact ψ.injective h1

variable {p e : ℕ} [Fact p.Prime]

theorem mulAut_eq_one_of_fixes_sylow (hp : p ≠ 2) (he : 0 < e)
    (P : Sylow 2 SL(2, GaloisField p e)) (n : ℕ) (β : MulAut SL(2, GaloisField p e))
    (hβ : β ^ 2 ^ n = 1) (hfix : ∀ x ∈ P, β x = x) : β = 1 := by
  by_cases h5 : 5 ≤ p ^ e
  · exact AscL62.mulAut_eq_one_of_pow_two_pow_eq_one hp h5 P n β hβ hfix
  · have hp3 : 3 ≤ p := by
      have h2 := (Fact.out : p.Prime).two_le
      have hodd : p ≠ 2 := hp
      omega
    have he1 : e = 1 := by
      by_contra hne
      have h2 : 2 ≤ e := by omega
      have : p ^ 2 ≤ p ^ e := Nat.pow_le_pow_right (by omega) h2
      nlinarith
    subst he1
    have hp3' : p = 3 := by
      rw [pow_one] at h5
      by_contra hne
      have h4 : p ≠ 4 := by
        intro h4
        have hpr : p.Prime := Fact.out
        rw [h4] at hpr
        exact absurd hpr (by norm_num)
      omega
    subst hp3'
    exact mulAut_eq_one_of_fixes_sylow_three P β hfix

theorem mulAut_trivial_quotient_of_fixes {L : Type} [Group L] (hp : p ≠ 2) (he : 0 < e)
    (N : Subgroup L) [N.Normal] (eL : L ⧸ N ≃* SL(2, GaloisField p e))
    (α : MulAut L) (hαN : N.map (α : L →* L) = N) (n : ℕ) (hα : α ^ 2 ^ n = 1)
    (P : Sylow 2 SL(2, GaloisField p e))
    (hfix : ∀ x ∈ P, ∃ r : L, eL (QuotientGroup.mk r) = x ∧ eL (QuotientGroup.mk (α r)) = x) :
    ∀ k : L, (QuotientGroup.mk (α k) : L ⧸ N) = QuotientGroup.mk k := by
  set ᾱ : MulAut (L ⧸ N) := QuotientGroup.congr N N (α : L ≃* L) hαN with hᾱ
  have hᾱmk : ∀ x : L, ᾱ (QuotientGroup.mk x) = QuotientGroup.mk (α x) := fun x => rfl
  have hpow : ∀ (m : ℕ) (x : L), (ᾱ ^ m) (QuotientGroup.mk x) =
      QuotientGroup.mk ((α ^ m) x) := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      rw [pow_succ, MulAut.mul_apply, hᾱmk, ih, pow_succ, MulAut.mul_apply]
  have hᾱn : ᾱ ^ 2 ^ n = 1 := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H y => rw [hpow, hα]; rfl
  have hβn : (MulAut.congr eL) ᾱ ^ 2 ^ n = 1 := by
    rw [← map_pow, hᾱn, map_one]
  have hβfix : ∀ x ∈ P, (MulAut.congr eL) ᾱ x = x := by
    intro x hx
    obtain ⟨r, hr1, hr2⟩ := hfix x hx
    rw [MulAut.congr_apply]
    simp only [MulEquiv.trans_apply]
    have : eL.symm x = QuotientGroup.mk r := by rw [← hr1]; simp
    rw [this, hᾱmk]
    exact hr2
  have h1 := mulAut_eq_one_of_fixes_sylow hp he P n _ hβn hβfix
  intro k
  have h2 : (MulAut.congr eL) ᾱ (eL (QuotientGroup.mk k)) = eL (QuotientGroup.mk k) := by
    rw [h1]; rfl
  rw [MulAut.congr_apply] at h2
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h2
  exact eL.injective h2

theorem commutator_mem_oddCoreOf_of_equiv {G : Type} [Group G] [Finite G] (hp : p ≠ 2)
    (he : 0 < e) {L R V : Subgroup G}
    (eL : ↥L ⧸ classicalInvolutionOddCore ↥L ≃* SL(2, GaloisField p e)) (hR : IsSylow2In R L)
    (hV2 : IsPGroup 2 ↥V) (hVL : ∀ y ∈ V, conjSub y L = L)
    (hcomm : ∀ r ∈ R, ∀ v ∈ V, r * v = v * r) :
    ∀ k ∈ L, ∀ v ∈ V, ⁅v, k⁆ ∈ oddCoreOf L := by
  intro k hk v hv
  have hvN : v ∈ Subgroup.normalizer (L : Set G) := mem_normalizer_iff_conjSub_eq.mpr (hVL v hv)
  set α : MulAut ↥L := L.normalizerMonoidHom ⟨v, hvN⟩ with hα
  have hαN : (classicalInvolutionOddCore ↥L).map (α : ↥L →* ↥L) =
      classicalInvolutionOddCore ↥L :=
    CFSG.ComponentClassification.OddCore.equiv_invariant (α : ↥L ≃* ↥L)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, orderOf v = 2 ^ n := AscL62.orderOf_eq_two_pow_of_isPGroup hV2 hv
  have hαn : α ^ 2 ^ n = 1 := by
    rw [hα, ← map_pow]
    have : (⟨v, hvN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 2 ^ n = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_pow, OneMemClass.coe_one]
      rw [← hn, pow_orderOf_eq_one]
    rw [this, map_one]
  let φ : ↥L →* SL(2, GaloisField p e) :=
    (eL : ↥L ⧸ classicalInvolutionOddCore ↥L →* SL(2, GaloisField p e)).comp
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥L))
  have hφs : Function.Surjective φ := eL.surjective.comp (QuotientGroup.mk'_surjective _)
  let P : Sylow 2 SL(2, GaloisField p e) :=
    Sylow.mapSurjective (f := φ) hφs (AscL62.sylowOfIsSylow2In'' hR)
  have hfix : ∀ x ∈ P, ∃ r : ↥L, eL (QuotientGroup.mk r) = x ∧
      eL (QuotientGroup.mk (α r)) = x := by
    intro x hx
    have hx' : x ∈ ((AscL62.sylowOfIsSylow2In'' hR : Subgroup ↥L)).map φ := by
      have := Sylow.coe_mapSurjective (f := φ) hφs (AscL62.sylowOfIsSylow2In'' hR)
      rw [← this]
      exact hx
    obtain ⟨r, hr, rfl⟩ := hx'
    have hrR : (r : G) ∈ R := hr
    have hvr : v * (r : G) * v⁻¹ = r := by
      rw [← hcomm r hrR v hv]
      group
    have hαr : α r = r := by
      apply Subtype.ext
      rw [hα]
      simpa using hvr
    exact ⟨r, rfl, by rw [hαr]; rfl⟩
  have h1 := mulAut_trivial_quotient_of_fixes hp he _ eL α hαN n hαn P hfix ⟨k, hk⟩
  have h2 : (α ⟨k, hk⟩ : ↥L) * (⟨k, hk⟩ : ↥L)⁻¹ ∈ classicalInvolutionOddCore ↥L := by
    rw [← div_eq_mul_inv, ← QuotientGroup.eq_iff_div_mem]
    exact h1
  have h3 : ((α ⟨k, hk⟩ : ↥L) : G) = v * k * v⁻¹ := by
    rw [hα]
    simp
  have hmem : ⁅v, k⁆ ∈ L := by
    rw [commutatorElement_def]
    have := (α ⟨k, hk⟩).2
    rw [h3] at this
    exact L.mul_mem this (L.inv_mem hk)
  refine mem_oddCoreOf_iff.mpr ⟨hmem, ?_⟩
  convert h2 using 1
  apply Subtype.ext
  simp [h3, commutatorElement_def]

end M3

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1916
