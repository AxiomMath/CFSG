module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3KFacts
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Unitary
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryAutPCard
import CFSG.RankThree.Automorphisms.CoprimeCyclicTools
public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding Subgroup

theorem u3_index {K : Type} [Group K] (h : IsRankThreeU3 K) :
    ∃ d : TauCeti.ValidLieTypeIndex, IsUnitaryIndex 3 d ∧ d.1.fieldExponent = 1 ∧
      Nonempty (K ≃* CatGroup d) := by
  obtain ⟨q, hqp, hq1, hv, ⟨e⟩⟩ := h
  have hd : IsUnitaryIndex 3 ⟨.twistedA 2 q, hv⟩ := ⟨q, hqp, rfl⟩
  obtain ⟨q', -, hd', hfe, -⟩ := hd.exists_eq
  injection hd' with _ hqq
  subst hqq
  exact ⟨⟨.twistedA 2 q, hv⟩, hd, by rw [hfe, hq1], ⟨e⟩⟩

theorem u3SylowData_proved : U3SylowData := by
  intro K _ _ hK T
  obtain ⟨d, hd, hfe, he⟩ := u3_index hK
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hcard, hcomm, hexp, E, hET, hE, hEc⟩ :=
    kFactUnitarySylowStructure K 3 d (by norm_num) hd he T
  rw [hfe] at hcard hEc
  have hcard' : Nat.card (T : Subgroup K) = 3 ^ 3 := by simpa using hcard
  have hnc : ¬ IsMulCommutative (T : Subgroup K) := by
    intro hc
    have h1 : (T : Subgroup K) ≤ centralizer ((T : Subgroup K) : Set K) :=
      Subgroup.le_centralizer_iff_isMulCommutative.mpr hc
    have h2 : ⁅(T : Subgroup K), (T : Subgroup K)⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h1
    rw [h2, inf_eq_left.mpr h1] at hcomm
    have h3 : Nat.card (T : Subgroup K) = 1 := by rw [← hcomm]; simp
    omega
  refine ⟨hcard', hexp, hnc, ⟨E, hET, hE, by simpa using hEc⟩, ?_, ?_⟩
  ·
    obtain ⟨-, hf, hq, K', _, _, J, hJ, hK', hfix, ⟨e⟩⟩ :=
      UnitaryModel.exists_equiv_psu (UnitaryModel.statedClassicalModel hd he)
    obtain ⟨S, hS⟩ := UnitaryModel.exists_sylow_eq_rootGroup J hJ hK' hfix hf
    obtain ⟨e', he'⟩ := UnitaryModel.exists_equiv_map_eq e T S
    have hU : (T : Subgroup K).map e'.toMonoidHom = UnitaryThreeRecognition.Model.rootGroup J hJ :=
      he'.trans hS
    intro c hc
    have hcR : e' c ∈ UnitaryThreeRecognition.Model.rootGroup J hJ := by
      refine UnitaryModel.mem_rootGroup_of_forall_comm J hJ hK' hfix hq fun r hr => ?_
      have hr' : e'.symm r ∈ (T : Subgroup K) := by
        have : r ∈ (T : Subgroup K).map e'.toMonoidHom := hU ▸ hr
        exact Subgroup.mem_map_equiv.1 this
      have h1 := mem_centralizer_iff.mp hc (e'.symm r) hr'
      have h2 := congrArg e' h1
      simpa [map_mul] using h2
    have h3 : e' c ∈ (T : Subgroup K).map e'.toMonoidHom := hU ▸ hcR
    have h4 := Subgroup.mem_map_equiv.1 h3
    rwa [MulEquiv.symm_apply_apply] at h4
  · intro Y hY
    have hco := kFactUnitaryBorelMaximal K 3 d hd he T
    rcases eq_or_lt_of_le hY with h | h
    · exact Or.inl h.symm
    · exact Or.inr (hco.2 _ h)

theorem u3BorelCore_proved : U3BorelCore := by
  intro X _ _ K hKn hC hKU T hTK hTsyl
  have : K.Normal := hKn
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨d, hd, -, he⟩ := u3_index hKU
  have hTp : IsPGroup 3 ↥T := (isSylowOf_iff.mp hTsyl).2.1
  obtain ⟨Q, hQ⟩ := hTsyl
  set N : Subgroup X := normalizer (T : Set X) with hN
  set R : Subgroup X := rankThreePrimeCore 3 N with hR
  have hRN : R ≤ N := CFSG.AGLEmbedding.glbPrimeCore_le 3 N
  have hRcop : Nat.Coprime 3 (Nat.card R) := CFSG.AGLEmbedding.glbPrimeCore_coprime 3 N
  have hNR : N ≤ normalizer (R : Set X) := CFSG.AGLEmbedding.le_normalizer_glbPrimeCore 3 N
  have hTN : T ≤ N := Subgroup.le_normalizer
  have hTR : T ⊓ R = ⊥ :=
    CFSG.RankThree.Automorphisms.inf_eq_bot_of_isPGroup_of_coprime hTp hRcop.symm
  refine eq_bot_iff.mpr fun r hr => ?_
  have hrN : r ∈ N := hRN hr
  have hcomm : ∀ t ∈ T, r * t = t * r := by
    intro t ht
    have h1 : r * t * r⁻¹ * t⁻¹ ∈ T :=
      T.mul_mem ((mem_normalizer_iff.mp hrN t).mp ht) (T.inv_mem ht)
    have h2 : r * t * r⁻¹ * t⁻¹ ∈ R := by
      have h3 : t * r⁻¹ * t⁻¹ ∈ R := by
        have := (mem_normalizer_iff.mp (hNR (hTN ht)) r⁻¹).mp (R.inv_mem hr)
        simpa [mul_assoc] using this
      have := R.mul_mem hr h3
      simpa [mul_assoc] using this
    have h4 : r * t * r⁻¹ * t⁻¹ ∈ T ⊓ R := ⟨h1, h2⟩
    rw [hTR, Subgroup.mem_bot] at h4
    calc r * t = (r * t * r⁻¹ * t⁻¹) * (t * r) := by group
      _ = t * r := by rw [h4, one_mul]
  have hfix : ∀ u ∈ (Q : Subgroup K), (MulAut.conjNormal r : MulAut K) u = u := by
    intro u hu
    have huT : (u : X) ∈ T := hQ ▸ ⟨u, hu, rfl⟩
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    calc r * (u : X) * r⁻¹ = ((u : X) * r) * r⁻¹ := by rw [hcomm _ huT]
      _ = u := by group
  obtain ⟨u, huQ, hu⟩ := kFactUnitaryUnipotentCentralizer K 3 d hd he Q _ hfix
  have huT : (u : X) ∈ T := hQ ▸ ⟨u, huQ, rfl⟩
  have hcK : (u : X)⁻¹ * r ∈ centralizer (K : Set X) := by
    rw [mem_centralizer_iff]
    intro k hk
    have h1 := congrArg (fun φ : MulAut K => ((φ ⟨k, hk⟩ : K) : X)) hu
    simp only [MulAut.conjNormal_apply, MulAut.conj_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at h1
    calc k * ((u : X)⁻¹ * r) = (u : X)⁻¹ * ((u : X) * k * (u : X)⁻¹) * r := by group
      _ = (u : X)⁻¹ * (r * k * r⁻¹) * r := by rw [h1]
      _ = ((u : X)⁻¹ * r) * k := by group
  rw [hC, Subgroup.mem_bot] at hcK
  have hru : r = u := by
    have : (u : X)⁻¹ * r = 1 := hcK
    calc r = (u : X) * ((u : X)⁻¹ * r) := by group
      _ = u := by rw [this, mul_one]
  have : r ∈ T ⊓ R := ⟨hru ▸ huT, hr⟩
  rwa [hTR, Subgroup.mem_bot] at this

theorem u3AutData_proved : U3AutData := by
  intro K _ _ hK S hS
  obtain ⟨d, hd, hfe, he⟩ := u3_index hK
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := kFactUnitaryAutPCard K 3 d (by norm_num) hd he S hS
  rwa [hfe, mul_one, mul_one] at h

end CFSG.LocalAnalysis.RankThreeTheoremC
