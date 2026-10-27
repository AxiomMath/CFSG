module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19_10Red
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalTwoFrontier
public import CFSG.RankThree.Native.SuzFiveCentralizers
public import CFSG.Sporadic.SuzOddCore.SmallAut

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.RankThree.Native CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SmallOddCore

private theorem suz_autModel :
    AutModel suzM suzT where
  le := suzM_le_suzT
  conj_mem := fun _ hx _ hp => suzT_conj_mem_suzM hx hp
  surj := fun α => by
    obtain ⟨t, rfl⟩ := suzConjT_bijective.2 α
    exact ⟨(t : Equiv.Perm (Fin 1782)), t.2, fun p => suzConjT_apply t p⟩
  inj := fun x _ hc => by
    have hxc : x ∈ Subgroup.centralizer (suzM : Set (Equiv.Perm (Fin 1782))) :=
      Subgroup.mem_centralizer_iff.2 fun p hp => (hc p hp).symm
    rw [suzM_centralizer, Subgroup.mem_bot] at hxc
    exact hxc

private theorem suz_card_mulAut :
    Nat.card (MulAut suzM) = 2 * Nat.card suzM := by
  have h1 : Nat.card suzT = Nat.card (MulAut suzM) :=
    Nat.card_congr (Equiv.ofBijective _ suzConjT_bijective)
  rw [← h1, suzT_card, suzM_card]

private theorem suz_witness :
    ∀ E : Subgroup suzM, IsElemAbelian 5 E → Nat.card E = 5 ^ 2 →
      ∃ d ∈ E, d ≠ 1 ∧
        GLAPPrimeCoreOf 5 (Subgroup.centralizer ({(d : Equiv.Perm (Fin 1782))} :
          Set (Equiv.Perm (Fin 1782))) ⊓ suzT) = ⊥ := by
  intro E _ hEc
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨⟨hQP, -, -, -, -⟩, ⟨hlines, -⟩, hrec, hgood, -⟩ :=
    R3E_Suz_full_five_centralizer_structures
  obtain ⟨hCeq, hDs, hDnab, -⟩ := hrec 0
  obtain ⟨-, hDcard, hcentEq, hcard5⟩ := hgood 0 (Or.inl rfl)
  have hx0mem : Subgroup.zpowers (suzFiveLine 0) ≤ suzFiveQ ∧
      Nat.card (Subgroup.zpowers (suzFiveLine 0)) = 5 :=
    (Set.ext_iff.1 hlines (Subgroup.zpowers (suzFiveLine 0))).2 ⟨0, rfl⟩
  have hx0Q : suzFiveLine 0 ∈ suzFiveQ := hx0mem.1 (Subgroup.mem_zpowers _)
  have hx0M : suzFiveLine 0 ∈ suzM := hQP hx0Q
  have hx0o : orderOf (suzFiveLine 0) = 5 := by
    rw [← Nat.card_zpowers]
    exact hx0mem.2
  have hx0ne : suzFiveLine 0 ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx0o
    norm_num at hx0o
  have hD : ⁅suzFiveC 0, suzFiveC 0⁆ = suzFiveD 0 := rfl
  have hcore : GLAPPrimeCoreOf 5
      (Subgroup.centralizer ({suzFiveLine 0} : Set (Equiv.Perm (Fin 1782))) ⊓ suzT) = ⊥ := by
    rw [← hCeq]
    exact gLAPPrimeCoreOf_eq_bot_of_record_derived Nat.prime_five hDs hDnab
      (by rw [hD, hDcard]; norm_num)
      (IsPGroup.of_card (n := 1) (by rw [pow_one, hD, hcentEq]; exact hcard5))
  have hf5 : (Nat.card suzM).factorization 5 = 2 := by
    rw [suzM_card, show (448345497600 : ℕ) = 5 ^ 2 * 17933819904 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_five, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hEMle : E.map suzM.subtype ≤ suzM := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hEMcard : Nat.card (E.map suzM.subtype) = 5 ^ (Nat.card suzM).factorization 5 := by
    rw [hf5, Subgroup.card_map_of_injective suzM.subtype_injective, hEc]
  obtain ⟨g, hgM, hgE⟩ := Co3T.exists_conj_mem_of_full hEMle hEMcard hx0M hx0o
  obtain ⟨d, hdE, hd⟩ := Subgroup.mem_map.1 hgE
  have hdv : (d : Equiv.Perm (Fin 1782)) = g⁻¹ * suzFiveLine 0 * g := hd
  refine ⟨d, hdE, ?_, ?_⟩
  · intro hd1
    apply hx0ne
    have h1 : (d : Equiv.Perm (Fin 1782)) = 1 := by rw [hd1]; rfl
    rw [hdv] at h1
    calc suzFiveLine 0 = g * (g⁻¹ * suzFiveLine 0 * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  ·
    have hk : g⁻¹ ∈ suzT := suzT.inv_mem (suzM_le_suzT hgM)
    have hk1 : ∀ q ∈ suzT, g⁻¹ * q * g⁻¹⁻¹ ∈ suzT := fun q hq =>
      suzT.mul_mem (suzT.mul_mem hk hq) (suzT.inv_mem hk)
    have hk2 : ∀ q ∈ suzT, g⁻¹⁻¹ * q * g⁻¹ ∈ suzT := fun q hq =>
      suzT.mul_mem (suzT.mul_mem (suzT.inv_mem hk) hq) hk
    have hmap := map_conj_centralizer_inf (P := suzT) hk1 hk2 (suzFiveLine 0)
    have hψinj : Function.Injective (MulAut.conj g⁻¹).toMonoidHom := (MulAut.conj g⁻¹).injective
    have hcon : GLAPPrimeCoreOf 5
        ((Subgroup.centralizer ({suzFiveLine 0} : Set (Equiv.Perm (Fin 1782))) ⊓ suzT).map
          (MulAut.conj g⁻¹).toMonoidHom) = ⊥ := by
      rw [← map_glaPPrimeCoreOf_of_injective 5 _ hψinj, hcore, Subgroup.map_bot]
    rw [hmap, inv_inv] at hcon
    rw [hdv]
    exact hcon

theorem sporadicTwoBalanceFive_Suz :
    SporadicTwoBalanceFive .Suz := by
  rintro S _ _ hsimple hnab ⟨e⟩
  obtain ⟨e'⟩ := CFSG.Sporadic.Bridge.Suz.nonempty_mulEquiv
  let θ : S ≃* suzM := (e.trans e'.symm).trans suzEquivM
  have hcen : Subgroup.center S = ⊥ := center_eq_bot_of_isSimpleGroup hnab
  have hcard : Nat.card (MulAut S) = 2 * Nat.card S := by
    rw [Nat.card_congr (MulAut.congr θ).toEquiv, suz_card_mulAut, Nat.card_congr θ.toEquiv]
  have hout : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S) ≤ 2 :=
    (card_out_eq_two Nat.card_pos hcen hcard).le
  exact isLocallyBalancedAbs_two_of_autModel Nat.prime_five (by norm_num) suz_autModel θ hcen
    hout suz_witness

end CFSG.HardMathSupport.Dickson.LocalTwoBalance
