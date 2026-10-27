module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisVQ
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisSig3
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisKlein
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisFusSound
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisSig2

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG CFSG.Open Subgroup SCert CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

namespace GHSylow

variable (D : GHSylow G)

omit [Finite G] in
theorem conj_z_of_mem_V (h10 : D.FusN 1 0) (h20 : D.FusN 2 0) {v : G} (hv : v ∈ D.V)
    (hv1 : v ≠ 1) : ∃ g : G, g⁻¹ * D.z * g = v := by
  have e0 : SE.invRep (Fin.ofNat 9 0) = SE.gen 0 := by decide
  obtain ⟨g₁, hg₁⟩ := h10
  obtain ⟨g₂, hg₂⟩ := h20
  rw [e0, show Fin.ofNat 9 1 = 1 by decide] at hg₁
  rw [e0, show Fin.ofNat 9 2 = 2 by decide] at hg₂
  obtain ⟨c, -, hc⟩ := D.exists_conj_rep_of_mem_V hv hv1
  have key : ∀ (w : G) (g : G), g⁻¹ * w * g = D.z → c⁻¹ * v * c = w →
      ∃ g' : G, g'⁻¹ * D.z * g' = v := fun w g hg hcw =>
    ⟨g⁻¹ * c⁻¹, by rw [← hg, ← hcw]; group⟩
  rcases hc with h | h | h
  · exact key D.z 1 (by group) h
  · exact key D.t g₁ hg₁ h
  · exact key D.a1l g₂ hg₂ h


theorem charTwoAt_V (hC : GorensteinHaradaThmCInput) (h10 : D.FusN 1 0) (h20 : D.FusN 2 0) :
    CharTwoAt D.V :=
  charTwoAt_of_conj (D.isCharacteristicP_Mb hC) fun _ ha ha1 => D.conj_z_of_mem_V h10 h20 ha ha1

omit [Finite G]
  in
theorem eight_le_card_V : 8 ≤ Nat.card D.V := D.card_V.ge

theorem sigW_V_spec (hC : GorensteinHaradaThmCInput) (h10 : D.FusN 1 0) (h20 : D.FusN 2 0) :
    (Nat.Coprime 2 (Nat.card (sigW D.V)) ∧ D.V ≤ normalizer (sigW D.V : Set G)) ∧
      ∀ S ∈ signalizerFunctorEk 2 1 D.V, sigW D.V ⊓ centralizer (S : Set G) = oddCent S :=
  sigW_spec D.isElemAbelian_V D.eight_le_card_V (D.charTwoAt_V hC h10 h20)

theorem sigW_V_eq (hC : GorensteinHaradaThmCInput) (h10 : D.FusN 1 0) (h20 : D.FusN 2 0)
    {B : Subgroup G} (hB : B ≤ D.V) (h4 : 4 ≤ Nat.card B) : sigW D.V = sigW4 B :=
  sigW_eq_sigW4 D.isElemAbelian_V D.eight_le_card_V (D.charTwoAt_V hC h10 h20) hB h4

theorem normalizer_le_H (hC : GorensteinHaradaThmCInput) (h10 : D.FusN 1 0)
    (h20 : D.FusN 2 0) {B : Subgroup G} (hB : B ≤ D.V) (h4 : 4 ≤ Nat.card B) :
    normalizer (B : Set G) ≤ normalizer (sigW D.V : Set G) := by
  rw [D.sigW_V_eq hC h10 h20 hB h4]
  exact normalizer_le_sigW4 B

theorem normalizer_V_le_H (hC : GorensteinHaradaThmCInput) (h10 : D.FusN 1 0)
    (h20 : D.FusN 2 0) : normalizer (D.V : Set G) ≤ normalizer (sigW D.V : Set G) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq, ← MulEquiv.toMonoidHom_eq_coe] at hg ⊢
  set B : Subgroup G := klein D.z D.t D.t_mul_t D.z_comm_t
  have hBV : B ≤ D.V := klein_le D.z_mem_V D.t_mem_V
  have hB4 : 4 ≤ Nat.card B := (card_klein D.z_mul_z D.z_ne_one D.t_ne_one D.z_ne_t.symm).ge
  have hBg : B.map (MulAut.conj g).toMonoidHom ≤ D.V := by
    rw [← hg]
    exact map_mono hBV
  have hBg4 : 4 ≤ Nat.card (B.map (MulAut.conj g).toMonoidHom) := by
    rw [card_map_of_injective (MulAut.conj g).injective]
    exact hB4
  rw [D.sigW_V_eq hC h10 h20 hBV hB4, ← sigW4_map, ← D.sigW_V_eq hC h10 h20 hBg hBg4,
    D.sigW_V_eq hC h10 h20 hBV hB4]

omit [Finite G]
  in
theorem oddCent_zpowers_z : oddCent (zpowers D.z) = D.OM := by
  have h : centralizer ((zpowers D.z : Subgroup G) : Set G) = D.M := by
    rw [zpowers_eq_closure, centralizer_closure]
  have key : ∀ K : Subgroup G, K = D.M → (pPrimeCore 2 ↥K).map K.subtype = D.OM := by
    rintro K rfl
    rfl
  exact key _ h

omit [Finite G]
  in
theorem OM_le_W : D.OM ≤ sigW D.V := by
  rw [← D.oddCent_zpowers_z]
  refine oddCent_le_sigW ⟨zpowers_le.mpr D.z_mem_V, ?_⟩
  rw [Nat.card_zpowers, pow_one]
  exact orderOf_eq_prime (by rw [pow_two, D.z_mul_z]) D.z_ne_one

theorem exists_conj_OM {u v : ↥D.M} (hu : u * u = 1) (hv : v * v = 1)
    (h : D.piM u = D.piM v) : ∃ o ∈ pPrimeCore 2 ↥D.M, o⁻¹ * u * o = v := by
  set o' := v⁻¹ * u with ho'
  have ho'O : o' ∈ pPrimeCore 2 ↥D.M := (QuotientGroup.eq).mp h.symm
  have hodd : Odd (orderOf o') := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥D.M)) := pPrimeCore_coprime_card
    have hdvd : orderOf o' ∣ Nat.card (pPrimeCore 2 ↥D.M) := by
      rw [← Subgroup.orderOf_mk o' ho'O]
      exact orderOf_dvd_natCard _
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h2 =>
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hcop (h2.trans hdvd))
  have hvo : v * o' = u := by rw [ho', mul_inv_cancel_left]
  obtain ⟨k, hk⟩ := exists_conj_of_inv_mul_inv hv (by rw [hvo]; exact hu) hodd
  rw [hvo] at hk
  refine ⟨(o' ^ k)⁻¹, inv_mem (pow_mem ho'O k), ?_⟩
  rw [inv_inv, ← hk]
  group

theorem M_le_H_of (hC : GorensteinHaradaThmCInput) (h10 : D.FusN 1 0) (h20 : D.FusN 2 0)
    (hconj : ∀ m ∈ D.M, ∃ o ∈ D.OM, ∃ (e : G) (he : e * e = 1) (hze : D.z * e = e * D.z),
      o * e * o⁻¹ = m * D.t * m⁻¹ ∧ sigW4 (klein D.z e he hze) = sigW D.V) :
    D.M ≤ normalizer (sigW D.V : Set G) := by
  intro m hm
  obtain ⟨o, ho, e, he, hze, hoe, hW⟩ := hconj m hm
  rw [mem_normalizer_iff_map_conj_eq, ← MulEquiv.toMonoidHom_eq_coe]
  have hBV : klein D.z D.t D.t_mul_t D.z_comm_t ≤ D.V := klein_le D.z_mem_V D.t_mem_V
  have hB4 : 4 ≤ Nat.card (klein D.z D.t D.t_mul_t D.z_comm_t) :=
    (card_klein D.z_mul_z D.z_ne_one D.t_ne_one D.z_ne_t.symm).ge
  have hz : ∀ g ∈ D.M, (MulAut.conj g) D.z = D.z := fun g hg => by
    rw [MulAut.conj_apply]
    have := D.z_comm_of_mem_M (inv_mem hg)
    rwa [inv_inv] at this
  have hoW : (sigW D.V).map (MulAut.conj o).toMonoidHom = sigW D.V := by
    rw [MulEquiv.toMonoidHom_eq_coe, ← mem_normalizer_iff_map_conj_eq]
    exact le_normalizer (D.OM_le_W ho)
  calc (sigW D.V).map (MulAut.conj m).toMonoidHom
      = (sigW4 (klein D.z D.t D.t_mul_t D.z_comm_t)).map (MulAut.conj m).toMonoidHom := by
        rw [D.sigW_V_eq hC h10 h20 hBV hB4]
    _ = sigW4 ((klein D.z D.t D.t_mul_t D.z_comm_t).map (MulAut.conj m).toMonoidHom) :=
        (sigW4_map _ _).symm
    _ = sigW4 ((klein D.z e he hze).map (MulAut.conj o).toMonoidHom) := by
        rw [klein_map, klein_map]
        congr 1
        refine klein_congr ((hz m hm).trans (hz o (D.OM_le_M ho)).symm) ?_
        rw [MulAut.conj_apply, MulAut.conj_apply, hoe]
    _ = (sigW4 (klein D.z e he hze)).map (MulAut.conj o).toMonoidHom := sigW4_map _ _
    _ = sigW D.V := by rw [hW, hoW]

end GHSylow

end CFSG.ComponentClassification.GHarris
