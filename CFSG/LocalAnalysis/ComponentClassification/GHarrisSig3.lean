module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisMb2
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisSig1

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG CFSG.Open Subgroup CFSG.SignalizerFunctorTheorem

theorem isCharacteristicP_two_congr {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : IsCharacteristicP 2 A) : IsCharacteristicP 2 B := by
  unfold IsCharacteristicP at h ⊢
  intro b hb
  rw [← pCore_map_iso 2 e] at hb ⊢
  refine ⟨e.symm b, h ?_, by simp⟩
  rw [mem_centralizer_iff] at hb ⊢
  intro a ha
  have h1 := hb (e a) ⟨a, ha, rfl⟩
  apply e.injective
  simpa using h1

theorem isCharacteristicP_of_normal_le {Y : Type*} [Group Y] {Q : Subgroup Y} (hQn : Q.Normal)
    (hQ : IsPGroup 2 Q) (hC : centralizer (Q : Set Y) ≤ Q) : IsCharacteristicP 2 Y := by
  unfold IsCharacteristicP
  have hQP : Q ≤ pCore 2 Y := le_sSup ⟨hQn, hQ⟩
  exact (centralizer_le hQP).trans (hC.trans hQP)

variable {G : Type} [Group G]

theorem charTwoCent_map (φ : G ≃* G) {S : Subgroup G} (h : CharTwoCent S) :
    CharTwoCent (S.map φ.toMonoidHom) := by
  have hC := centralizer_map_equiv φ S
  let e : centralizer (S : Set G) ≃* centralizer ((S.map φ.toMonoidHom : Subgroup G) : Set G) :=
    (φ.subgroupMap _).trans (MulEquiv.subgroupCongr hC.symm)
  have he := pPrimeCore_map_iso 2 e
  exact isCharacteristicP_two_congr (QuotientGroup.congr _ _ e (by rw [← he]; rfl)) h

theorem charTwo_of_eq {H₁ H₂ : Subgroup G} (h : H₁ = H₂)
    (h1 : IsCharacteristicP 2 (H₁ ⧸ pPrimeCore 2 H₁)) :
    IsCharacteristicP 2 (H₂ ⧸ pPrimeCore 2 H₂) := by
  subst h
  exact h1

theorem charTwoCent_zpowers_of_conj {z u g : G} (hg : g⁻¹ * z * g = u)
    (hz : IsCharacteristicP 2 (centralizer ({z} : Set G) ⧸
      pPrimeCore 2 (centralizer ({z} : Set G)))) :
    CharTwoCent (zpowers u) := by
  have hz' : CharTwoCent (zpowers z) :=
    charTwo_of_eq (by rw [zpowers_eq_closure, centralizer_closure]) hz
  have key : zpowers u = (zpowers z).map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, hg]
  rw [key]
  exact charTwoCent_map _ hz'

theorem charTwoAt_of_conj [Finite G] {z : G}
    (hz : IsCharacteristicP 2 (centralizer ({z} : Set G) ⧸
      pPrimeCore 2 (centralizer ({z} : Set G))))
    {A : Subgroup G} (hA : ∀ a ∈ A, a ≠ 1 → ∃ g : G, g⁻¹ * z * g = a) : CharTwoAt A := by
  intro S hS
  have hS2 : Nat.card S = 2 := by rw [hS.2, pow_one]
  obtain ⟨a, haS, ha1⟩ : ∃ a ∈ S, a ≠ 1 := by
    by_contra! h
    have hbot : S = ⊥ := (eq_bot_iff_forall S).mpr h
    rw [hbot, card_bot] at hS2
    exact absurd hS2 (by decide)
  have ha2 : orderOf a = 2 := by
    have hdvd : orderOf a ∣ 2 := hS2 ▸ orderOf_dvd_natCard S haS
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) ha1
    · exact h
  have hSa : zpowers a = S :=
    eq_of_le_of_card_ge (zpowers_le.mpr haS) (by rw [hS2, Nat.card_zpowers, ha2])
  obtain ⟨g, hg⟩ := hA a (hS.1 haS) ha1
  rw [← hSa]
  exact charTwoCent_zpowers_of_conj hg hz

section Ybar

variable {Y : Type} [Group Y] [Finite Y]

namespace GHSylow

variable (D : GHSylow Y)

theorem isCharacteristicP_Y (hC : GorensteinHaradaThmCInput) (hO : pPrimeCore 2 Y = ⊥)
    (hz : ∀ y : Y, y * D.z = D.z * y) : IsCharacteristicP 2 Y := by
  have hSp : IsPGroup 2 (D.S : Subgroup Y) := D.S.isPGroup'
  by_cases hB : pCore 2 D.Xt = ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt)
  · obtain ⟨-, -, -, hCT⟩ := D.prop38B_of hC hO hz hB
    have hTn : ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt).Normal := by
      rw [← hB]
      exact pCore_normal
    exact isCharacteristicP_of_normal_le (D.S1_normal_of hO hz hTn)
      (hSp.to_le inf_le_left) (D.centralizer_S1_le_of hO hz hCT)
  · obtain ⟨-, hCE, -, -⟩ := D.prop38A_of hC hO hz hB
    exact isCharacteristicP_of_normal_le (D.E_normal_Y hC hO hz) (hSp.to_le D.E_le_S)
      (D.centralizer_E_le_of hCE)

end GHSylow

end Ybar

variable [Finite G]

namespace GHSylow

variable (D : GHSylow G)

theorem isCharacteristicP_Mb (hC : GorensteinHaradaThmCInput) :
    IsCharacteristicP 2 (centralizer ({D.z} : Set G) ⧸
      pPrimeCore 2 (centralizer ({D.z} : Set G))) :=
  D.toMb.isCharacteristicP_Y hC D.pPrimeCore_Mb D.z_comm_Mb

end GHSylow

end CFSG.ComponentClassification.GHarris
