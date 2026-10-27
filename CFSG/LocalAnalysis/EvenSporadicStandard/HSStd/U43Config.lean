module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43ConfigInst
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43ConfigGlue
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7Lam
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Tables
public import CFSG.LieType.Multipliers.U43
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.Contra
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.Stages

public section

namespace CFSG.EvenSporadicStandard.HSStd.U43

open Subgroup CFSG.EvenSporadicStandard.M24Std.CU43 CFSG.EvenSporadicStandard.HSStd
  CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

section Model


theorem model_j8
    {X' : Subgroup (Equiv.Perm (Fin 820))} (hP : P ≤ X') (hR : X' ≤ R) (hT : rP 8 ∈ X')
    (hC : Nat.card ↥(X' ⊓ centralizer ({rP 8} : Set (Equiv.Perm (Fin 820)))) = 2880)
    (hZ : ∀ z ∈ X' ⊓ centralizer ({rP 8} : Set (Equiv.Perm (Fin 820))),
      (∀ x ∈ X' ⊓ centralizer ({rP 8} : Set (Equiv.Perm (Fin 820))), z * x = x * z) →
        z = 1 ∨ z = rP 8) {y c k : Equiv.Perm (Fin 820)} (hs : SigRel (rP 8) y c k) (hy : y ∈ X')
    (hc : c ∈ X') (hk : k ∈ X') :
    Nat.card ↥(X' ⊓ centralizer ({y} : Set (Equiv.Perm (Fin 820)))) = 1944 ∧
      Nat.card ↥(X' ⊓ centralizer ({y, c, rP 8 * c * (rP 8)⁻¹, k, rP 8 * k * (rP 8)⁻¹} :
        Set (Equiv.Perm (Fin 820)))) = 3 := by
  have hT2 : rP 8 * rP 8 = 1 := rP_mul_self (by norm_num)
  have hTrep := rep_tabOf_rP (j := 8) (by norm_num)
  have hcard : (cosSet X').card = 4 := by
    have h := card_inf_centralizer_rP8 hP hR
    omega
  have h0 : 0 ∈ cosSet X' := mem_cosSet.2 ⟨by norm_num, by rw [tP_zero]; exact X'.one_mem⟩
  have h2 : 2 ∈ cosSet X' := by
    obtain ⟨g, hg, hrg, -⟩ := rP_mem_InvCoset (j := 8) (by norm_num)
    have hk2 : repCoset[8]! = 2 := by decide
    rw [hk2] at hrg
    refine mem_cosSet.2 ⟨by norm_num, ?_⟩
    have : tP 2 = g⁻¹ * rP 8 := by rw [hrg]; group
    rw [this]
    exact X'.mul_mem (X'.inv_mem (hP hg)) hT
  rcases cosSet_cases (cosSet X') (fun k hk => (mem_cosSet.1 hk).1) h0 h2
    (fun a ha b hb => cosSet_closed ha hb) hcard with hK | hK | hK
  · exfalso
    obtain ⟨z, hzX, hz1, hzT, hzc, hzcomm⟩ := va_central hP hR hK hC
    rcases hZ z (mem_inf.2 ⟨hzX, mem_centralizer_singleton_iff.2 hzc⟩) hzcomm with h | h
    · exact hz1 h
    · exact hzT h
  · exact caseZ4_spec hP hR hK hTrep hT2 hs hy hc hk
  · exact caseVb_spec hP hR hK hTrep hT2 hs hy hc hk

end Model

theorem u43Config_proved :
    U43Config := by
  intro X _ _ N _ hL hC t ht he y c k hs
  obtain ⟨e⟩ := he
  obtain ⟨eX⟩ := CFSG.LieType.Multipliers.U43.nonempty_mulEquiv_X₀ hL
  let θ : ↥N ≃* P := eX.trans psiEquiv
  have h8 : N.index ∣ 8 := card_quotient_dvd_eight N θ hC
  have hinj : Function.Injective (emb N θ) := emb_injective N θ hC
  have hsM := (sigRel_of_sigmaConfig hs).map (emb N θ) hinj
  have htt : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht, sq] at this
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    omega
  have hT2 : emb N θ t * emb N θ t = 1 := by rw [← map_mul, htt, map_one]
  have hT1 : emb N θ t ≠ 1 := fun h => ht1 (hinj (by rw [h, map_one]))
  obtain ⟨j, hj, hjcls, -⟩ := involution_data (emb_mem N θ t) hT2 hT1
  obtain ⟨g₀, hg₀, hTeq⟩ := hjcls
  have hCt : Nat.card ↥(centralizer ({t} : Set X)) = 2880 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod,
      CFSG.QuasithinUnique.Setup.X3Aut.card_mulAut_alt6]
    simp
  have hcentN : Nat.card ↥(N ⊓ centralizer ({t} : Set X)) = repCent[j]! := by
    rw [card_inf_centralizer_emb N θ hC t, hTeq, card_inf_centralizer_conj hg₀,
      card_inf_centralizer_rP hj]
  have hrel := relIndex_mul_card N (centralizer ({t} : Set X))
  rw [hCt, hcentN] at hrel
  have hr : N.relIndex (centralizer ({t} : Set X)) ∣ 8 :=
    (relIndex_dvd_index_of_normal _ _).trans h8
  have hj458 : j = 4 ∨ j = 5 ∨ j = 8 := by
    generalize N.relIndex (centralizer ({t} : Set X)) = r at hrel hr
    have hr' : r ∈ Nat.divisors 8 := Nat.mem_divisors.2 ⟨hr, by norm_num⟩
    rw [show Nat.divisors 8 = {1, 2, 4, 8} by decide] at hr'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr'
    rcases hr' with rfl | rfl | rfl | rfl <;> interval_cases j <;> simp [repCent] at hrel ⊢
  set a : Equiv.Perm (Fin 820) := g₀⁻¹ with ha
  have haP : a ∈ P := P.inv_mem hg₀
  have hTa : a * emb N θ t * a⁻¹ = rP j := by rw [hTeq, ha]; group
  have hsM' := hsM.conj a
  rw [hTa] at hsM'
  have hyR : a * emb N θ y * a⁻¹ ∈ R :=
    R.mul_mem (R.mul_mem (P_le_R haP) (emb_mem N θ y)) (R.inv_mem (P_le_R haP))
  have hcR : a * emb N θ c * a⁻¹ ∈ R :=
    R.mul_mem (R.mul_mem (P_le_R haP) (emb_mem N θ c)) (R.inv_mem (P_le_R haP))
  have hkR : a * emb N θ k * a⁻¹ ∈ R :=
    R.mul_mem (R.mul_mem (P_le_R haP) (emb_mem N θ k)) (R.inv_mem (P_le_R haP))
  rcases hj458 with rfl | rfl | rfl
  · exact (caseI4_vacuous (rep_tabOf_rP (by norm_num)) (rP_mul_self (by norm_num)) hsM' hyR hcR
      hkR).elim
  · exact (caseI5_vacuous (rep_tabOf_rP (by norm_num)) (rP_mul_self (by norm_num)) hsM' hyR hcR
      hkR).elim
  ·
    set X' : Subgroup (Equiv.Perm (Fin 820)) := (emb N θ).range with hX'
    have hPX : P ≤ X' := fun p hp => by
      obtain ⟨c', -, hc'⟩ := exists_emb_eq N θ hp
      exact MonoidHom.mem_range.2 ⟨c', hc'⟩
    have hXR : X' ≤ R := by
      rintro _ ⟨x, rfl⟩
      exact emb_mem N θ x
    have haX : a ∈ X' := hPX haP
    have hmem : ∀ x : X, a * emb N θ x * a⁻¹ ∈ X' := fun x =>
      X'.mul_mem (X'.mul_mem haX ⟨x, rfl⟩) (X'.inv_mem haX)
    have hTX : rP 8 ∈ X' := hTa ▸ hmem t
    have hCX : Nat.card ↥(X' ⊓ centralizer ({rP 8} : Set (Equiv.Perm (Fin 820)))) = 2880 := by
      have h1 := card_centralizer_map (emb N θ) hinj ({t} : Set X)
      rw [Set.image_singleton, hCt] at h1
      have h2 := card_inf_centralizer_conj_set X' haX ({emb N θ t} : Set (Equiv.Perm (Fin 820)))
      rw [Set.image_singleton, hTa] at h2
      rw [h2, ← h1]
    have hZX : ∀ g ∈ centralizer ({t} : Set X),
        (∀ l ∈ centralizerDerived t, g * l = l * g) → g ∈ zpowers t :=
      fun g hg hc => mem_zpowers_of_commute_derived ht e hg hc
    have hZ := centre_transport (emb N θ) hinj hT2 hZX haX
    rw [hTa] at hZ
    obtain ⟨h1, h2⟩ := model_j8 hPX hXR hTX hCX hZ hsM' (hmem y) (hmem c) (hmem k)
    constructor
    · have := card_centralizer_map (emb N θ) hinj ({y} : Set X)
      rw [Set.image_singleton] at this
      rw [this, ← card_inf_centralizer_conj_set X' haX ({emb N θ y} : Set (Equiv.Perm (Fin 820))),
        Set.image_singleton]
      exact h1
    · have := card_centralizer_map (emb N θ) hinj
        ({y, c, t * c * t⁻¹, k, t * k * t⁻¹} : Set X)
      simp only [Set.image_insert_eq, Set.image_singleton, map_mul, map_inv] at this
      rw [this, ← card_five_conj X' haX (emb N θ t) (emb N θ y) (emb N θ c) (emb N θ k), hTa]
      exact h2

end CFSG.EvenSporadicStandard.HSStd.U43
