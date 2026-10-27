module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAUInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAUCons
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAUBasic
public import Certificates.Certificate26820
public import Certificates.Certificate26821
public import Certificates.Certificate26822

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup Matrix CFSG.Blueprint CFSG.Blueprint.NativeSporadic

section Core

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f s y n : G} {S₀ : Subgroup G}
  {C : ECoord G}

theorem sect8InputU_core (H : Sect7Hyps G L f s y S₀ n) (h : Sect8Hyp C f n S₀) (hQ : Q0Facts)
    (hUQ : UFactsQ) {sl : List M4} (hUS : UFactsOf sl)
    (hS : ∀ m ∈ normalizer (C.E : Set G), C.mat m ∈ sl) {T K : Subgroup G}
    (hT : Lemma61Out C hQ f S₀ T K)
    (hFy : ∀ w : G, w * f ^ 2 = f ^ 2 * w → w ∉ L ⊔ zpowers y → w ∉ L ⊔ zpowers f →
      ∀ g : G, w ≠ g⁻¹ * f ^ 2 * g)
    (hK : ∃ w ∈ T, w ∉ C.E ∧ (∀ a ∈ C.E, a * a = 1 → w * a = a * w) ∧
      ∃ g : G, w = g⁻¹ * f ^ 2 * g)
    (hO : ∀ w ∈ T, w ∉ C.E → (∀ a ∈ C.E, a * a = 1 → w * a = a * w) → w ∈ L ⊔ zpowers y →
      (∃ g : G, w = g⁻¹ * f ^ 2 * g) → Cl16 C f w) :
    ∃ U : Subgroup G, U ≤ T ∧ U.relIndex T = 2 ∧ f ∉ U ∧ C.E1sub hQ ≤ U ∧
      (∀ w ∈ T, w * f ^ 2 = f ^ 2 * w → w ∈ L ⊔ zpowers y → w ∈ U) ∧
      ∀ x ∈ T, x ∉ U → x * x = 1 →
        ∃ z ∈ T, x * (z⁻¹ * f ^ 2 * z) = (z⁻¹ * f ^ 2 * z) * x := by
  have hf2E : f ^ 2 ∈ C.E := pow_mem h.f_mem 2
  have hf2f2 : f ^ 2 * f ^ 2 = 1 := by rw [← pow_add]; exact H.four.pow_four
  have hSD := hT.sylow
  have hTN : ∀ z ∈ T, z ∈ normalizer (C.E : Set G) := fun z hz => hSD.mem_normalizer_E hz
  have hTE : C.E ≤ T := hSD.E_le
  have hF8 : ((C.Fsub hQ : Subgroup G) : Set G).ncard = 8 := by
    rw [C.ncard_Fsub hQ hUQ.fcard.2]
    exact hUQ.fcard.1
  have htrans := hSD.tF_trans hf2f2 hf2E hF8
  have good : ∀ w ∈ T, w ∉ C.E → (∀ a ∈ C.E, a * a = 1 → w * a = a * w) →
      (∃ g : G, w = g⁻¹ * f ^ 2 * g) →
      w * f ^ 2 = f ^ 2 * w ∧ C.mat w = -1 ∧ w ∈ L ⊔ zpowers y := by
    intro w hwT hwE hwc hwconj
    have hwn := hTN w hwT
    have hmat := h.mat_neg_of_comm hUS hwn (hS w hwn) hwE hwc
    have hwf2 : w * f ^ 2 = f ^ 2 * w := hwc _ hf2E hf2f2
    refine ⟨hwf2, hmat, ?_⟩
    by_contra hwy
    have hwLF : w ∉ L ⊔ zpowers f := by
      intro hw
      obtain ⟨l, hl, i, hw'⟩ := exists_mul_zpow_of_mem_sup (SAU.hcom H) hw
      have hcw : w * f = f * w := by
        rw [hw']
        exact ((show Commute l f from SAU.hcom H l hl).mul_left
          (Commute.zpow_left (Commute.refl f) i)).eq
      have h1 := h.inv_of_mat_neg hwn hmat h.f_mem
      rw [hcw] at h1
      have h2 : f = f⁻¹ := by
        calc f = f * w * w⁻¹ := by group
          _ = f⁻¹ := h1
      have h3 : f ^ 2 = 1 := by
        calc f ^ 2 = f * f := sq f
          _ = f * f⁻¹ := by rw [← h2]
          _ = 1 := by group
      have := orderOf_dvd_of_pow_eq_one h3
      rw [H.four.order] at this
      omega
    obtain ⟨g, hg⟩ := hwconj
    exact hFy w hwf2 hwy hwLF g hg
  obtain ⟨y', hy'T, hy'E, hy'c, hy'conj⟩ := hK
  obtain ⟨hy'f2, hy'm, hy'H⟩ := good y' hy'T hy'E hy'c hy'conj
  have hy'n := hTN y' hy'T
  have hy'cl : Cl16 C f y' := hO y' hy'T hy'E hy'c hy'H hy'conj
  have hc : SAU.ConsHyp T C.E (C.E1sub hQ) y' f :=
    { E_le := hTE
      E₁_le := fun e he => he.1
      T_norm_E := fun z hz e he => hSD.conj_mem_E hz he
      T_norm_E₁ := fun z hz e he =>
        h.conj_mem_E1sub hQ hUS (hTN z hz) (hS z (hTN z hz)) he
      E_comm := fun a ha b hb => C.comm ha hb
      y_mem := hy'T
      y_inv := fun e he => h.inv_of_mat_neg hy'n hy'm he
      cls := by
        intro z hz
        have hw''T : z * y' * z⁻¹ ∈ T := T.mul_mem (T.mul_mem hz hy'T) (T.inv_mem hz)
        have hw''E : z * y' * z⁻¹ ∉ C.E := by
          intro hE
          apply hy'E
          have := hSD.conj_mem_E (T.inv_mem hz) hE
          have e1 : z⁻¹ * (z * y' * z⁻¹) * z⁻¹⁻¹ = y' := by group
          rwa [e1] at this
        have hw''c : ∀ a ∈ C.E, a * a = 1 → (z * y' * z⁻¹) * a = a * (z * y' * z⁻¹) := by
          intro a ha haa
          have ha' : z⁻¹ * a * z ∈ C.E := by
            have := hSD.conj_mem_E (T.inv_mem hz) ha
            simpa using this
          have haa' : (z⁻¹ * a * z) * (z⁻¹ * a * z) = 1 := by
            calc (z⁻¹ * a * z) * (z⁻¹ * a * z) = z⁻¹ * (a * a) * z := by group
              _ = 1 := by rw [haa]; group
          have h1 := hy'c _ ha' haa'
          calc z * y' * z⁻¹ * a = z * (y' * (z⁻¹ * a * z)) * z⁻¹ := by group
            _ = z * ((z⁻¹ * a * z) * y') * z⁻¹ := by rw [h1]
            _ = a * (z * y' * z⁻¹) := by group
        obtain ⟨g₀, hg₀⟩ := hy'conj
        have hw''conj : ∃ g : G, z * y' * z⁻¹ = g⁻¹ * f ^ 2 * g := by
          refine ⟨g₀ * z⁻¹, ?_⟩
          rw [hg₀]
          group
        obtain ⟨-, hw''m, hw''H⟩ := good _ hw''T hw''E hw''c hw''conj
        have hw''n := hTN _ hw''T
        have hw''cl := hO _ hw''T hw''E hw''c hw''H hw''conj
        exact h.uniq_Cl16 H hQ hUQ hy'n hy'm hy'H hy'cl hw''n hw''m hw''H hw''cl
      sqrt := fun ε hε hεε => h.exists_sqrt hQ hε hεε
      inv_mem_E₁ := fun e he hee => h.inv_mem_E1sub hQ he hee
      f_mem := h.f_mem
      f_not := by
        intro hf
        have hv := ((C.mem_E1sub_iff_vec hQ).1 hf).2
        rw [h.vec_f, hQ.two_f] at hv
        exact hUQ.tnot hv
      f_sq := h.inv_mem_E1sub hQ (C.E.mul_mem h.f_mem h.f_mem) (by simpa [sq] using hf2f2)
      cases := fun e he => h.E_cases hQ he }
  refine ⟨hc.Usub, hc.Usub_le, hc.relIndex_Usub, hc.f_not_mem_Usub, hc.E₁_le_Usub, ?_, ?_⟩
  · intro w hwT hwc hwH
    obtain ⟨e, heE, c, hcT, hcy, hwe⟩ := hc.decomp hwT
    have hcn := hTN c hcT
    have hcc : c * f ^ 2 = f ^ 2 * c := by
      have hce : c = e⁻¹ * w := by rw [hwe]; group
      rw [hce]
      have he : e⁻¹ * f ^ 2 = f ^ 2 * e⁻¹ := C.comm (C.E.inv_mem heE) hf2E
      calc e⁻¹ * w * f ^ 2 = e⁻¹ * (w * f ^ 2) := by rw [mul_assoc]
        _ = e⁻¹ * (f ^ 2 * w) := by rw [hwc]
        _ = (e⁻¹ * f ^ 2) * w := by rw [mul_assoc]
        _ = f ^ 2 * (e⁻¹ * w) := by rw [he, mul_assoc]
    have hcH : c ∈ L ⊔ zpowers y :=
      h.cent_le_H1 H hQ hUQ hy'n hy'm hy'H hy'cl hcc hcn hcy
    have heH : e ∈ L ⊔ zpowers y := by
      have : e = w * c⁻¹ := by rw [hwe]; group
      rw [this]
      exact mul_mem hwH (inv_mem hcH)
    have heE1 := h.mem_E1sub_of_mem_H1 hQ H hUQ heE heH
    rw [hwe]
    exact (hc.mem_Usub_iff heE hcT hcy).2 heE1
  · intro x hxT hxU hxx
    have hxn := hTN x hxT
    have hB := hS x hxn
    have hBB : C.mat x * C.mat x = 1 := by rw [← C.mat_mul hxn hxn, hxx, C.mat_one]
    rcases hUS.fx _ hB hBB with ⟨v, hv, hfix⟩ | hFX
    · have hvF : C.elt v ∈ C.Fsub hQ := ⟨C.elt_mem v, by rw [C.vec_elt]; exact hv⟩
      obtain ⟨z', hz'T, hz'⟩ := htrans _ hvF
      refine ⟨z'⁻¹, T.inv_mem hz'T, ?_⟩
      have e1 : z'⁻¹⁻¹ * f ^ 2 * z'⁻¹ = C.elt (tVec + v) := by
        rw [inv_inv, hz', h.f2_eq hQ, ← C.elt_add]
      rw [e1]
      have := C.conj_elt hxn (tVec + v)
      rw [hfix] at this
      calc x * C.elt (tVec + v) = (x * C.elt (tVec + v) * x⁻¹) * x := by group
        _ = C.elt (tVec + v) * x := by rw [this]
    · exfalso
      apply hxU
      obtain ⟨e, heE, c, hcT, hcy, hxe⟩ := hc.decomp hxT
      have hcn := hTN c hcT
      have hmatx : C.mat x = C.mat c := by
        rw [hxe, C.mat_mul (le_normalizer heE) hcn,
          (C.mat_eq_one_iff (le_normalizer heE)).2 (fun a ha => C.comm heE ha), one_mul]
      have hcc1 : C.mat (c * c) = 1 := by rw [C.mat_mul hcn hcn, ← hmatx, hBB]
      have hccE : c * c ∈ C.E := h.mem_E_of_mat_eq_one (mul_mem hcn hcn) hcc1
      have hccy : Commute (c * c) y' :=
        (show Commute c y' from hcy).mul_left (show Commute c y' from hcy)
      have hccinv : (c * c) * (c * c) = 1 :=
        h.mul_self_of_comm hy'n hy'm hccE hccy.eq.symm
      have ha : e * (c * e * c⁻¹) = (c * c)⁻¹ := by
        have h0 : e * c * (e * c) = 1 := by rw [← hxe]; exact hxx
        calc e * (c * e * c⁻¹) = (e * c * (e * c)) * (c * c)⁻¹ := by group
          _ = (c * c)⁻¹ := by rw [h0, one_mul]
      have hceE : c * e * c⁻¹ ∈ C.E := hSD.conj_mem_E hcT heE
      have haE : e * (c * e * c⁻¹) ∈ C.E := C.E.mul_mem heE hceE
      have hvec : C.vec (e * (c * e * c⁻¹)) = C.vec e + C.mat x *ᵥ C.vec e := by
        rw [C.vec_mul heE hceE, C.vec_conj hcn heE, hmatx]
      have h2 : (C.vec e + C.mat x *ᵥ C.vec e) + (C.vec e + C.mat x *ᵥ C.vec e) = 0 := by
        rw [← hvec, ← C.vec_mul haE haE]
        have h3 : e * (c * e * c⁻¹) * (e * (c * e * c⁻¹)) = 1 := by
          rw [ha]
          calc (c * c)⁻¹ * (c * c)⁻¹ = ((c * c) * (c * c))⁻¹ := by group
            _ = 1 := by rw [hccinv]; group
        rw [h3, C.vec_one]
      have hvE := hFX _ h2
      have heE1 : e ∈ C.E1sub hQ := (C.mem_E1sub_iff_vec hQ).2 ⟨heE, hvE⟩
      rw [hxe]
      exact (hc.mem_Usub_iff heE hcT hcy).2 heE1

end Core

section Holds


theorem sect8InputU_of_inputs (hFy : Sect8InputFy) (hK : ∀ hQ : Q0Facts, Sect8InputK hQ)
    (hO : ∀ hQ : Q0Facts, Sect8InputO hQ) : ∀ hQ : Q0Facts, Sect8InputU hQ := by
  intro hQ G _ _ L f s y S₀ n H C h T K hT
  have hNC : NormComplete := Certificates.certificate26421
  have hCF : CandFacts := Certificates.certificate26422
  have hUQ : UFactsQ := Certificates.certificate26820
  have hs2 : s ^ 2 ≠ f ^ 2 := by
    intro h2
    obtain ⟨u, hu1, -, hu3⟩ := H.u
    obtain ⟨τ, hτ, hτ'⟩ := H.four.exists_center_gen
    apply hu3
    have : u = τ := Subtype.ext (hu1.trans (h2.trans hτ'.symm))
    rw [this]
    exact hτ
  obtain ⟨n₀, hn0, hα₀, hn0t, hs2z⟩ := h.exists_n0 hQ hNC hCF H.n_t hs2
  have hfus := fun m hm => h.exists_fus hQ H.four.order H.not_conj hs2z (m := m) hm
  have hS : ∀ m ∈ normalizer (C.E : Set G), C.mat m ∈ sList (C.mat n₀) :=
    fun m hm => h.mat_mem_sList hQ hn0 hn0t hs2z hfus hm
  have hUS : UFactsOf (sList (C.mat n₀)) := by
    simp only [alphaReps, List.mem_cons, List.not_mem_nil, or_false] at hα₀
    rcases hα₀ with h1 | h1
    · rw [h1]; exact Certificates.certificate26821
    · rw [h1]; exact Certificates.certificate26822
  exact sect8InputU_core H h hQ hUQ hUS hS hT (hFy G L f s y S₀ n H)
    (hK hQ G L f s y S₀ n H C h T K hT) (hO hQ G L f s y S₀ n H C h T K hT)

end Holds

end CFSG.EvenSporadicStandard.TwoHS
