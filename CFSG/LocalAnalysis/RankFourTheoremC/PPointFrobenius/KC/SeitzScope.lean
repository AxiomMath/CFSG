module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.KC.Statement
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.KC.Alt
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.KC.LieChar
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.KC.Sporadic
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentOffCharBase
import CFSG.LieType.SeitzGeneration.ClassicalAssembly
public import CFSG.LieType.SeitzGeneration.ExcParabolic
public import CFSG.LieType.SeitzGeneration.ExcPlaneAssembly
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LieType.SeitzGeneration.Lift

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

open CFSG.Open CFSG.AGLEmbeddingD2 CFSG.LieType.SeitzGeneration

@[expose] def SeitzInnerExFive : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (p : ℕ), p.Prime → 5 ≤ p → p ≠ d.1.characteristic →
    ¬ IsD2SeitzException p d.1 → ¬ RankLE2 p (Cat d) →
    (∃ E : Subgroup (MulAut (Cat d)), IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      InnerPlane d p E) →
    ∃ E : Subgroup (MulAut (Cat d)), IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      InnerPlane d p E ∧ PlaneGen E

@[expose] def ExcParabolicPlaneFive : Prop :=
  ExcParabolicPlaneOn fun d p => ¬ IsClassicalIndex d ∧ 5 ≤ p

section Reduction

theorem kc_innerEx_classical_five : ∀ (d : TauCeti.ValidLieTypeIndex) (p : ℕ), p.Prime → 5 ≤ p →
    p ≠ d.1.characteristic → ¬ IsD2SeitzException p d.1 → ¬ RankLE2 p (Cat d) →
    IsClassicalIndex d.1 →
    (∃ E : Subgroup (MulAut (Cat d)), IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      InnerPlane d p E) →
    ∃ E : Subgroup (MulAut (Cat d)), IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      InnerPlane d p E ∧ PlaneGen E := by
  intro d p hp hp5 hpd hex hrk hc hE
  have hp2 : p ≠ 2 := by omega
  have hrange : d.1.InStandardRange := ((TauCeti.LieTypeIndex.valid_iff _).1 d.2).1
  rcases (isClassicalIndex_iff hrange).1 hc with h | h | h | h
  · exact innerEx_linear d h p hp hp2 hpd hex hE
  · obtain ⟨d, hv⟩ := d
    obtain ⟨m, q, rfl⟩ := h
    obtain ⟨E, hEa, hcE, hinner⟩ := hE
    by_cases hlift : CentralPrimeFree p (.twistedA m q)
    · exact ⟨E, hEa, hcE, hinner, seitzInnerUnitary_of_nontoral unitarySUNontoral
        ⟨.twistedA m q, hv⟩ p hp hp2 hpd hex E hEa hcE ⟨hinner, hp5, ⟨m, q, rfl⟩, hlift⟩⟩
    · have hl : p ∣ q.card + 1 ∧ p ∣ m + 1 := by simpa [CentralPrimeFree] using hlift
      have hm : 4 ≤ m := by
        have := Nat.le_of_dvd (by omega) hl.2
        omega
      have hq2 : q.card ≠ 2 := by
        have := Nat.le_of_dvd (by omega) hl.1
        omega
      exact innerEx_unitary_diag hv hp hl.1 hq2 hm ⟨E, hEa, hcE, hinner⟩
  · exact innerEx_symplectic d h p hp hp2 hpd hex hE
  · exact seitzInnerEx_orth_high d h p hp hp2 hpd hrk hE

end Reduction

private theorem kcScope_isElemAbelian_comap_inj {G H : Type*} [Group G] [Group H] {p : ℕ}
    (f : G →* H) (hf : Function.Injective f) {E : Subgroup H} (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.comap f) := by
  obtain ⟨⟨hc⟩, hx⟩ := hE
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx' => ?_⟩
  · apply Subtype.ext
    apply hf
    have := hc.comm ⟨f (a : G), a.2⟩ ⟨f (b : G), b.2⟩
    have h := congrArg Subtype.val this
    change f ((a : G) * b) = f ((b : G) * a)
    rw [map_mul, map_mul]
    exact h
  · apply hf
    rw [map_pow, map_one]
    exact hx _ hx'

theorem kc_glbCore_eq_top_of_innerGen {K : Type} [Group K] [Finite K] (hs : IsSimpleGroup K)
    (hnab : ∃ a b : K, a * b ≠ b * a) {d : TauCeti.ValidLieTypeIndex} (e : K ≃* Cat d) {p : ℕ}
    (hp : p.Prime) (T : Sylow p K)
    (hgen : ∃ E' : Subgroup (MulAut (Cat d)), IsElemAbelian p E' ∧ Nat.card E' = p ^ 2 ∧
      InnerPlane d p E' ∧ PlaneGen E') :
    GLBCore p 1 (T : Subgroup K) = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨E', hE'el, -, hE'inner, hE'gen⟩ := hgen
  have hinj := CFSG.AGLEmbedding.conj_injective_of_simple hs hnab
  let ψ : K →* MulAut (Cat d) := (MulAut.congr e).toMonoidHom.comp MulAut.conj
  have hψ : Function.Injective ψ := (MulAut.congr e).injective.comp hinj
  have hrange : E' ≤ ψ.range := by
    intro ε hε
    obtain ⟨c, hc⟩ := hE'inner hε
    refine ⟨e.symm c, ?_⟩
    rw [← hc]
    change (MulAut.congr e).toMonoidHom (MulAut.conj (e.symm c)) = MulAut.conj c
    rw [CFSG.LieType.SeitzGeneration.mulAut_congr_conj e, MulEquiv.apply_symm_apply]
  set E₁ : Subgroup K := E'.comap ψ with hE₁
  have hmap : E₁.map ψ = E' := Subgroup.map_comap_eq_self hrange
  have hE₁el : IsElemAbelian p E₁ := kcScope_isElemAbelian_comap_inj ψ hψ hE'el
  have hclos : Subgroup.closure {c : Cat d | ∃ ε ∈ E₁.map ψ, ε ≠ 1 ∧ ε c = c} = ⊤ := by
    rw [hmap]
    exact hE'gen
  have hle : (⊤ : Subgroup (Cat d)) ≤ (GLBCore p 1 E₁).map e.toMonoidHom := by
    rw [← hclos, Subgroup.closure_le]
    rintro c ⟨ε, hε, hε1, hεc⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hε
    have hx1 : x ≠ 1 := by
      rintro rfl
      exact hε1 (map_one ψ)
    refine ⟨e.symm c, CFSG.AGLEmbedding.mem_glbCore_of_commute hp hE₁el hx hx1 ?_, by simp⟩
    have h1 : ψ x c = e (x * e.symm c * x⁻¹) := by
      simp [ψ, MulAut.congr_apply]
    rw [h1] at hεc
    have h2 : x * e.symm c * x⁻¹ = e.symm c := by
      apply e.injective
      rw [hεc]
      simp
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2.symm
  have hcore : GLBCore p 1 E₁ = ⊤ := by
    rw [eq_top_iff]
    intro k _
    obtain ⟨k', hk', hk'e⟩ := Subgroup.mem_map.mp (hle (Subgroup.mem_top (e k)))
    exact e.injective hk'e ▸ hk'
  exact CFSG.AGLEmbedding.glbCore_eq_top_of_mulEquiv hp (MulEquiv.refl K)
    (CFSG.Open.IsElemAbelian.isPGroup hE₁el) hcore T

theorem kc_glbCore_eq_top_of_innerExFive (hS : SeitzInnerExFive) {K : Type} [Group K] [Finite K]
    {p n : ℕ} [Fact p.Prime] {S : Sylow p K} {L : Subgroup K} (h : KCData K p n S L)
    (hs : IsSimpleGroup K) (hnab : ∃ a b : K, a * b ≠ b * a) (d : TauCeti.ValidLieTypeIndex)
    (e : K ≃* Cat d) (hpd : p ≠ d.1.characteristic) (hex : ¬ IsD2SeitzException p d.1) :
    GLBCore p 1 (S : Subgroup K) = ⊤ := by
  have hp : p.Prime := h.prime
  have hp5 : 5 ≤ p := h.p5
  have hp2 : p ≠ 2 := by omega
  have : Fact (IsPGroup p (S : Subgroup K)) := ⟨S.isPGroup'⟩
  obtain ⟨E, -, hEcard, hEel⟩ := CFSG.lemma_4_5_a hp2 h.noncyc_S
  set E₀ : Subgroup K := E.map (S : Subgroup K).subtype with hE₀
  have hEel' : IsElemAbelian p E :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p E).mp hEel
  have hE₀el : IsElemAbelian p E₀ :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hEel' _
  have hE₀card : Nat.card E₀ = p ^ 2 := by
    rw [hE₀, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hEcard]
  have hinj := CFSG.AGLEmbedding.conj_injective_of_simple hs hnab
  let ψ : K →* MulAut (Cat d) := (MulAut.congr e).toMonoidHom.comp MulAut.conj
  have hψ : Function.Injective ψ := (MulAut.congr e).injective.comp hinj
  have hψel : IsElemAbelian p (E₀.map ψ) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE₀el ψ
  have hrank : ¬ RankLE2 p (Cat d) := by
    intro hr
    have hSel : IsElemAbelian p (S : Subgroup K) := h.elem_S
    have hmap := hr ((S : Subgroup K).map e.toMonoidHom)
      (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hSel _)
    rw [Subgroup.card_map_of_injective e.injective, h.card_S] at hmap
    have h3 : p ^ 3 ≤ p ^ n := Nat.pow_le_pow_right hp.pos h.n3
    have h2 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  have hgen := hS d p hp hp5 hpd hex hrank
    ⟨E₀.map ψ, hψel, by rw [Subgroup.card_map_of_injective hψ, hE₀card],
      InnerPlane.map_congr_conj e E₀ p⟩
  exact kc_glbCore_eq_top_of_innerGen hs hnab e hp S hgen

theorem kc_lieOff_five (hS : SeitzInnerExFive) (hF : KCFiveParts) {K : Type} [Group K] [Finite K]
    {p n : ℕ} [Fact p.Prime] {S : Sylow p K} {L : Subgroup K} (h : KCData K p n S L)
    (hs : IsSimpleGroup K) (hnab : ∃ a b : K, a * b ≠ b * a) (d : TauCeti.ValidLieTypeIndex)
    (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) (hpd : p ≠ d.1.characteristic)
    (hΓ : GLBCore p 1 (S : Subgroup K) ≠ ⊤) : False := by
  have hp5 : 5 ≤ p := h.p5
  have hex : ¬ IsD2SeitzException p d.1 := by
    rintro (⟨h3, -⟩ | ⟨h5, hd⟩)
    · omega
    · have hdvd : 5 ^ 3 ∣ Nat.card K := by
        have hK := h.dvd
        rw [h5] at hK
        exact (pow_dvd_pow (5 : ℕ) h.n3).trans hK
      exact hF d hd (by rwa [Nat.card_congr e.toEquiv] at hdvd)
  exact hΓ (kc_glbCore_eq_top_of_innerExFive hS h hs hnab d e hpd hex)

theorem stronglyEmbeddedPSL2KFact_of_inputs_five (hS : SeitzInnerExFive)
    (hC : CFSG.AGLEmbedding.CharPGen) (hF : KCFiveParts) (hO : KCSporadicOrders)
    (hT : KCThFive) : StronglyEmbeddedPSL2KFact := by
  intro K _ _ hs hnab hcat p n _ hp5 hn S L hSL ⟨e⟩ hΓ
  have h := kcData_of_sylow_le hp5 hn S L hSL e
  obtain ⟨i, ⟨e'⟩⟩ := hcat
  cases i with
  | cyclic q hq => exact (CFSG.AGLEmbedding.not_nonempty_mulEquiv_zmod hnab ⟨e'⟩).elim
  | alternating m hm => exact (kc_alt h m e' hΓ).elim
  | lie d =>
    by_cases hc : p = d.1.characteristic
    · exact kc_lieChar hC h hs hnab d e' hc hΓ
    · exact (kc_lieOff_five hS hF h hs hnab d e' hc hΓ).elim
  | sporadic s => exact (kc_sporadic hO hT h s e').elim

section Exceptional

theorem seitzInnerExFive_of_excParabolicFive (hP : ExcParabolicPlaneFive) : SeitzInnerExFive := by
  intro d p hp hp5 hpd hex hrk hE
  have hp2 : p ≠ 2 := by omega
  by_cases hc : IsClassicalIndex d.1
  · exact kc_innerEx_classical_five d p hp hp5 hpd hex hrk hc hE
  · obtain ⟨E₁, hE₁el, hE₁c, hE₁i, hN⟩ := hP d p hp hp2 hpd hex ⟨hc, hp5⟩ hrk
    exact ⟨E₁, hE₁el, hE₁c, hE₁i,
      seitzExcParabolic d p hp hp2 hpd hex E₁ hE₁el hE₁c ⟨hE₁i, hc, hN⟩⟩

structure ExcFiveResiduals : Prop where
  trialityOddFive : ExcPlaneTrialityOddFive
  f4 : ExcParabolicPlaneOn fun d p => IsF4Index d ∧ 5 ≤ p
  e6 : ExcParabolicPlaneOn fun d p => IsE6Index d ∧ 5 ≤ p
  twistedE6 : ExcParabolicPlaneOn fun d p => IsTwistedE6Index d ∧ 5 ≤ p
  e7 : ExcParabolicPlaneOn fun d p => IsE7Index d ∧ 5 ≤ p
  e8 : ExcParabolicPlaneOn fun d p => IsE8Index d ∧ 5 ≤ p

theorem excParabolicPlaneFive_of_residuals (hR : ExcFiveResiduals) : ExcParabolicPlaneFive := by
  intro d p hp hp2 hpd hex ⟨hnc, hp5⟩ hr
  have hF := excParabolicPlaneFree
  rcases (not_isClassicalIndex_iff d.1).mp hnc with
    ((hd | hd | hd | hd | hd) | (hd | hd)) | (hd | hd | hd | hd)
  · exact hF.g2Five d p hp hp2 hpd hex ⟨hd, hp5⟩ hr
  · exact hR.f4 d p hp hp2 hpd hex ⟨hd, hp5⟩ hr
  · exact hR.e6 d p hp hp2 hpd hex ⟨hd, hp5⟩ hr
  · exact hR.e7 d p hp hp2 hpd hex ⟨hd, hp5⟩ hr
  · exact hR.e8 d p hp hp2 hpd hex ⟨hd, hp5⟩ hr
  · by_cases hc : d.1.characteristic = 2
    · exact hF.trialityEvenFive d p hp hp2 hpd hex ⟨hd, hp5, hc⟩ hr
    · exact hR.trialityOddFive d p hp hp2 hpd hex ⟨hd, hp5, hc⟩ hr
  · exact hR.twistedE6 d p hp hp2 hpd hex ⟨hd, hp5⟩ hr
  · exact hF.suzuki d p hp hp2 hpd hex hd hr
  · exact hF.reeG2 d p hp hp2 hpd hex hd hr
  · exact hF.reeF4Five d p hp hp2 hpd hex ⟨hd, hp5⟩ hr
  · exact hF.tits d p hp hp2 hpd hex hd hr

theorem excParabolicPlaneFive_of_excParabolicPlane (h : ExcParabolicPlane) :
    ExcParabolicPlaneFive :=
  ExcParabolicPlaneOn.mono (fun _ _ hd => hd.1) h

end Exceptional

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
