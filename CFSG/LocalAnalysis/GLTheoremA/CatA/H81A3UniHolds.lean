module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Facts
import CFSG.LocalAnalysis.GLTheoremA.CatA.H81ChoiceTransport
import CFSG.LocalAnalysis.GLTheoremA.CatA.H81A3UniAut
import CFSG.LocalAnalysis.GLTheoremA.CatA.H81A3UniType
import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CTrans
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.RankThree.PartOne.KF.UnitaryDiag

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H81

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel LinA3 UniA3

private theorem map_map_symm {A B : Type*} [Group A] [Group B] (e : A ≃* B) (P : Subgroup A) :
    (P.map e.toMonoidHom).map e.symm.toMonoidHom = P := by
  ext x
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

private theorem h81Choice_torusU {ℓ f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}
    [Finite K] [Fact ℓ.Prime] [CharP K ℓ] {p : ℕ} {μ : K} (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (hq : 5 ≤ ℓ ^ f) (hℓ2 : ℓ ≠ 2) (hp : p.Prime) (hp2 : p ≠ 2) (hμ : IsPrimitiveRoot μ p)
    (hpq : p ∣ ℓ ^ f + 1) {JType : Subgroup (PS h) → Prop} (hJT : JType (JU h))
    {P : Subgroup (PS h)}
    (hP : ∀ (d : Fin 4 → K) (hn : ∀ i, h.bar (d i) * d i = 1) (hd : ∏ i, d i = 1),
      (∀ i, d i ^ p = 1) → projU h (diagU h d hn hd) ∈ P) :
    H81Choice p P JType :=
  ⟨projU h (yU h hp hp2 hμ hpq), hP _ _ _ (yd_pow hp hp2 hμ), projU_yU_ne_one hp hp2 hμ hpq,
    JU h, glaPComponent_centralizer_projU_yU hp hp2 hμ hpq hK hq,
    fun L hL => eq_of_glaPComponent_centralizer_projU_yU hp hp2 hμ hpq hK hq hL, hJT,
    ⟨projU h (zU h hp hp2 hμ hpq), hP _ _ _ (zd_pow hp hp2 hμ),
      projU_zU_not_mem_zpowers hp hp2 hμ hpq, glaPLayer_JU_inf_centralizer_ne_bot hp hp2 hμ hpq hK hq⟩,
    fun α hα hc => aut_eq_conj_yU_zpow hK hq hℓ2 hp hp2 hμ hpq α hα hc⟩

theorem h81FactTwA3_holds : H81FactTwA3 := by
  intro p Q hp hp2 hQ2 hdiv H _ _ hcat P hPel hPcard
  classical
  haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨i, hi, ⟨e₀⟩⟩ := hcat
  rcases i with _ | _ | ⟨⟨d, hv⟩⟩ | _
  · exact absurd hi id
  · exact absurd hi id
  swap
  · exact absurd hi id
  change d = .twistedA 3 Q at hi
  subst hi
  obtain ⟨-, K, _, _, hK, ⟨e₁⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 Q hv e₀
  have h : UnitaryFieldData Q.p Q.exponent K :=
    ⟨Q.prime_p, Q.exponent_pos, by rw [hK, ← pow_mul, mul_comm]⟩
  haveI : CharP K Q.p := h.charP
  obtain ⟨e₂⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_idGram (K := K) (n := 4))
  let e : H ≃* PS h := e₁.trans ((unitaryPSUEquiv h (by norm_num : 1 ≤ 4)).symm.trans e₂.symm)
  have hpq : p ∣ Q.p ^ Q.exponent + 1 := by
    rw [TauCeti.PrimePower.card_def] at hdiv
    exact hdiv
  have hq5 : 5 ≤ Q.p ^ Q.exponent := by
    have hodd : Odd (Q.p ^ Q.exponent) := (Q.prime_p.odd_of_ne_two hQ2).pow
    have h2 : 2 ∣ Q.p ^ Q.exponent + 1 := by
      obtain ⟨m, hm⟩ := hodd
      exact ⟨m + 1, by omega⟩
    have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
    have h2p : 2 * p ∣ Q.p ^ Q.exponent + 1 := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h2 hpq
    have hle := Nat.le_of_dvd (by omega) h2p
    have h3 : 3 ≤ p := by
      have := hp.two_le
      omega
    omega
  obtain ⟨μ, hμ⟩ := CFSG.RankThree.PartOne.KFU.exists_isPrimitiveRoot h hp hpq
  have hP'el : IsElemAbelian p (P.map e.toMonoidHom) :=
    (CFSG.LocalAnalysis.GLTheoremA.T123C.isElemAbelian_map_iff e.injective p P).2 hPel
  have hP'card : Nat.card (P.map e.toMonoidHom) = p ^ 3 := by
    rw [Subgroup.card_map_of_injective e.injective, hPcard]
  obtain ⟨A, hA⟩ := exists_conj_diagU_mem hp hp2 hpq hP'el hP'card
  set c := primeFormConjHom h (idGram K 4) A with hc
  have hch := h81Choice_torusU hK hq5 hQ2 hp hp2 hμ hpq
    (isSL3Type_JU hK hq5 hp hp2 hμ hpq) (P := (P.map e.toMonoidHom).map c.toMonoidHom) hA
  have h1 := h81Choice_map_mulEquiv hp c.symm (fun J hJ => isSL3Type_map_mulEquiv c.symm hJ) hch
  rw [map_map_symm] at h1
  have h2 := h81Choice_map_mulEquiv hp e.symm (fun J hJ => isSL3Type_map_mulEquiv e.symm hJ) h1
  rwa [map_map_symm] at h2

end CFSG.LocalAnalysis.GLTheoremA.H81
