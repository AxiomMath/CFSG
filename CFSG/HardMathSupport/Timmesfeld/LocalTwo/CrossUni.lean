module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossUniPlane
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossUniOuter

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar

variable {ℓ f n p : ℕ} {K : Type} [Field K]

theorem isLocallyBalancedAbs_two_primeFormP (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n)
    (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) (hp : p.Prime) (hp5 : 5 < p) (hpℓ : p ≠ ℓ)
    (hHeis : p ∣ ℓ ^ f + 1 → p ∣ n → UniHeisPlane h n p) :
    IsLocallyBalancedAbs p 2 (primeFormP h (idGram K n)) := by
  classical
  have hfin := h.finite
  have : Finite (primeFormP h (idGram K n)) := finite_primeFormP
  have hinj := CFSG.RankThree.PartOne.KCUnitaryRegular.conj_injective_primeFormP h
    (isPrimeFormGram_idGram (K := K) (n := n)) hn hne
  intro D hD hcard H hH hDH
  by_cases hDl : D ≤ primeFormD h (idGram K n)
  · exact localDeltaIn_eq_bot_of_le_primeFormD_plane hn hne hp hp5 hpℓ hHeis hD hcard hDl hH hDH
  · obtain ⟨x, hxD, hxl, hfc⟩ := exists_fieldCore_unitary_outer h hn hne hp hp5 hpℓ hD hcard hDl
    have hx1 : x ≠ 1 := fun h1 => hxl (h1 ▸ one_mem _)
    exact localDeltaIn_eq_bot_of_fieldCore hp hinj hH hxD hx1 hfc

theorem crossCharTwoFamAt_twistedA_of_planes (R : TauCeti.ValidLieTypeIndex → ℕ → Prop)
    (hR : ∀ (idx : TauCeti.ValidLieTypeIndex) (p : ℕ) (r : ℕ) (q : TauCeti.PrimePower),
      idx.1 = .twistedA r q → R idx p →
      (∀ idx' : TauCeti.ValidLieTypeIndex, IsLpEpsIndex p idx'.1 →
        IsEmpty (CatT idx ≃* CatT idx')) →
      ∀ (K : Type) [Field K] (h : UnitaryFieldData q.p q.exponent K), p.Prime → 5 < p →
        p ≠ q.p → p ∣ q.p ^ q.exponent + 1 → p ∣ r + 1 → UniHeisPlane h (r + 1) p) :
    CrossCharTwoFamAt .twistedA R := by
  rintro ⟨d, hv⟩ hk p hp hp5 hc hRp hnexc
  obtain ⟨r, q, hd⟩ := hk
  change d = _ at hd
  subst hd
  have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv
    (MulEquiv.refl (CatT ⟨.twistedA r q, hv⟩))
  obtain ⟨⟨hℓ, hf, hn, hq⟩, K, _, _, hK, ⟨eT⟩⟩ := hm
  have h : UnitaryFieldData q.p q.exponent K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq' : ¬(r + 1 = 3 ∧ q.p ^ q.exponent = 2) := fun ⟨h1, h2⟩ => hq (by rw [h1, h2])
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_idGram (n := r + 1) (K := K))
  let e : CatT ⟨.twistedA r q, hv⟩ ≃* primeFormP h (idGram K (r + 1)) :=
    (eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm
  have hpq : p ≠ q.p := fun h => hc (by simp [h])
  exact IsLocallyBalancedAbs.of_mulEquiv e
    (isLocallyBalancedAbs_two_primeFormP h (by omega) hq' hp hp5 hpq
      (fun h1 h2 => hR ⟨.twistedA r q, hv⟩ p r q rfl hRp hnexc K h hp hp5 hpq h1 h2))

theorem crossCharTwoFamCat_twistedA_of_heisenberg (hH : UniHeisenbergPlaneBalance) :
    CrossCharTwoFamCat .twistedA := by
  refine crossCharTwoFamAt_twistedA_of_planes (fun _ _ => True) ?_ |> fun hAt =>
    fun idx hk p hp hp5 hc hnexc => hAt idx hk p hp hp5 hc trivial hnexc
  rintro idx p r q hd - hnexc K _ h hp hp5 hpq h1 h2
  have hrp : r + 1 ≠ p := by
    intro hrp
    have hr : r = p - 1 := by omega
    obtain ⟨d, hv⟩ := idx
    change d = _ at hd
    subst hd
    have hLp : IsLpEpsIndex p (TauCeti.LieTypeIndex.twistedA r q) :=
      Or.inr ⟨q, by rw [hr], Nat.mod_eq_zero_of_dvd (by rw [TauCeti.PrimePower.card_def]; exact h1)⟩
    exact (hnexc ⟨.twistedA r q, hv⟩ hLp).false (MulEquiv.refl _)
  have hne : ¬(r + 1 = 3 ∧ q.p ^ q.exponent = 2) := by
    rintro ⟨h3, h4⟩
    have : p ≤ r + 1 := Nat.le_of_dvd (by omega) h2
    omega
  exact hH q.p q.exponent (r + 1) K h (by
    have : p ≤ r + 1 := Nat.le_of_dvd (by omega) h2
    omega) hne p hp hp5 hpq h1 h2 hrp

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
