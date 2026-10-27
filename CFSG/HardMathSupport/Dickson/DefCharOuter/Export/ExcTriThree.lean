module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcTriClassB
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcInterface
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExceptionalBase

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.Export

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3
  CFSG.HardMathSupport.Lang.Triality
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.HardMathSupport.Dickson.Sec6.I923
  CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4Aux

theorem exc_fixSubgroup_inv {S : Type*} [Group S] (β : MulAut S) :
    fixSubgroup β⁻¹ = fixSubgroup β := by
  ext x
  show β⁻¹ x = x ↔ β x = x
  constructor
  · intro h
    calc β x = β (β⁻¹ x) := by rw [h]
      _ = x := MulAut.apply_inv_self _ β x
  · intro h
    calc β⁻¹ x = β⁻¹ (β x) := by rw [h]
      _ = x := MulAut.inv_apply_self _ β x

theorem OuterCentData.of_inv {p : ℕ} {S : Type} [Group S] {β : MulAut S}
    (h : OuterCentData p β⁻¹) : OuterCentData p β where
  unique I J hI hJ := h.unique I J (by rwa [exc_fixSubgroup_inv]) (by rwa [exc_fixSubgroup_inv])
  chev I hI := h.chev I (by rwa [exc_fixSubgroup_inv])
  core hexc := by
    have := h.core hexc
    rwa [exc_fixSubgroup_inv] at this
  cent hexc w hw hwβ hfixw :=
    h.cent hexc w hw (((Commute.inv_right (show Commute w β from hwβ)).eq))
      (by rwa [exc_fixSubgroup_inv])
  noHatSix hp3 I hI := h.noHatSix hp3 I (by rwa [exc_fixSubgroup_inv])
  l227 hp3 I hI hL β' hβ3 hββ' hmap :=
    h.l227 hp3 I (by rwa [exc_fixSubgroup_inv]) hL β' hβ3
      (((Commute.inv_right (show Commute β' β from hββ')).eq)) hmap

section Reduction

variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 3]
  (hK : Nat.card K = (3 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (3 ^ f))
include hf hK hσ

theorem exc_form_of_order_three
    (α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hα3 : α ^ 3 = 1)
    (hαin : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    ∃ g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (α = MulAut.conj g * fieldActor (t := TwistTag.D4) σ σ ∨
        α⁻¹ = MulAut.conj g * fieldActor (t := TwistTag.D4) σ σ) ∧
        (MulAut.conj g * fieldActor (t := TwistTag.D4) σ σ) ^ 3 = 1 := by
  classical
  obtain ⟨-, hex, ⟨Θ, hΘ, -, hker, -⟩, hcyc, hcard, -, -, -⟩ :=
    odd_triality_exact_automorphism_normal_form Nat.prime_three (by norm_num) hf K hK σ hσ
  have hσ3 : σ ^ 3 = 1 := by
    ext c
    exact ringEquiv_cube_apply_eq hK hσ c
  have hσ1 : σ ≠ 1 := by
    intro h
    have hc := CFSG.RankThree.PartOne.KGD.card_fixSubfield_cube Nat.prime_three hf hK σ hσ
    have htop : fixSubfield σ = ⊤ := by
      ext c
      simp [h]
    rw [htop] at hc
    have hc' : Nat.card K = 3 ^ f := by
      rw [← hc]
      exact (Nat.card_congr Subfield.topEquiv.toEquiv).symm
    have hp1 : 1 < 3 ^ f := Nat.one_lt_pow (by omega) (by norm_num)
    rw [hK] at hc'
    nlinarith [hp1, pow_pos (lt_trans Nat.zero_lt_one hp1) 2]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hσord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  obtain ⟨⟨g, δ'⟩, hgδ, -⟩ := hex α
  have hα : α = MulAut.conj g * fieldActor (t := TwistTag.D4) σ δ' := hgδ
  have hΘα : Θ α = δ' := hΘ α g δ' hα
  have hδ'3 : δ' ^ 3 = 1 := by rw [← hΘα, ← map_pow, hα3, map_one]
  have hδ'1 : δ' ≠ 1 := fun h => hαin (by
    have hmem : α ∈ Θ.ker := by rw [MonoidHom.mem_ker, hΘα, h]
    rwa [hker] at hmem)
  have hδ'ord : orderOf δ' = 3 := orderOf_eq_prime hδ'3 hδ'1
  have hδσ : δ' = σ ∨ δ' = σ⁻¹ := by
    have hfin : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
    have : Fintype (K ≃+* K) := Fintype.ofFinite _
    have h3dvd : 3 ∣ Fintype.card (K ≃+* K) := by
      rw [← Nat.card_eq_fintype_card, hcard]
      exact Dvd.intro _ rfl
    have hcnt := IsCyclic.card_orderOf_eq_totient (α := K ≃+* K) h3dvd
    have hφ : Nat.totient 3 = 2 := by decide
    set S : Finset (K ≃+* K) := Finset.univ.filter fun a => orderOf a = 3 with hS
    have hσinv : σ ≠ σ⁻¹ := by
      intro h
      have h2 : σ ^ 2 = 1 := by
        calc σ ^ 2 = σ * σ := sq σ
          _ = σ * σ⁻¹ := by rw [← h]
          _ = 1 := mul_inv_cancel σ
      apply hσ1
      calc σ = σ ^ 3 * (σ ^ 2)⁻¹ := by group
        _ = 1 := by rw [hσ3, h2]; simp
    have hsub : ({σ, σ⁻¹} : Finset (K ≃+* K)) ⊆ S := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases ha with rfl | rfl
      · exact hσord
      · rw [orderOf_inv]
        exact hσord
    have hSeq : ({σ, σ⁻¹} : Finset (K ≃+* K)) = S :=
      Finset.eq_of_subset_of_card_le hsub (by
        rw [Finset.card_pair hσinv]
        have : S.card = 2 := by rw [hS, hcnt, hφ]
        omega)
    have hδS : δ' ∈ S := by
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hδ'ord
    rw [← hSeq] at hδS
    simpa using hδS
  rcases hδσ with h | h
  · rw [h] at hα
    exact ⟨g, Or.inl hα, by rw [← hα]; exact hα3⟩
  · rw [h] at hα
    have hEinv : (fieldActor (t := TwistTag.D4) σ σ⁻¹)⁻¹ = fieldActor (t := TwistTag.D4) σ σ := by
      have h1 := fieldActor_mul (t := TwistTag.D4) σ σ⁻¹ σ
      rw [inv_mul_cancel, fieldActor_one] at h1
      exact inv_eq_of_mul_eq_one_right h1.symm
    have hα' : α⁻¹ = MulAut.conj (fieldActor (t := TwistTag.D4) σ σ g⁻¹) *
        fieldActor (t := TwistTag.D4) σ σ := by
      rw [hα, mul_inv_rev, hEinv,
        ← map_inv (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →* _) g]
      refine MulEquiv.ext fun x => ?_
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul]
      simp only [map_inv]
    refine ⟨fieldActor (t := TwistTag.D4) σ σ g⁻¹, Or.inr hα', ?_⟩
    rw [← hα', inv_pow, hα3, inv_one]

theorem exc_reduction_unipotent_gen
    (P : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) → Prop)
    (hconj : ∀ ε β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      P (ε * β * ε⁻¹) → P β)
    (hinv : ∀ β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), P β⁻¹ → P β)
    (β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hβ3 : β ^ 3 = 1)
    (hout : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    ∃ u : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (u : ModGL TwistTag.D4.tag K) ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ∧
      (MulAut.conj u * fieldActor (t := TwistTag.D4) σ σ) ^ 3 = 1 ∧
      (P (MulAut.conj u * fieldActor (t := TwistTag.D4) σ σ) → P β) := by
  classical
  haveI := finite_graphFixedRootGroup_D4 σ
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hform, hg3⟩ := exc_form_of_order_three hf hK σ hσ β hβ3 hout
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  obtain ⟨Sy, hPU⟩ := (exceptional_fixed_Sylow_opposition TwistTag.D4 K 3 σ w₀ hw₀).1
  have hZ : Function.Injective (MulAut.conj : (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
    conj_injective_of_center_eq_bot (center_graphFixedRootGroup_eq_bot σ.surjective)
  have hσ3 : σ ^ 3 = 1 := by
    ext c
    exact ringEquiv_cube_apply_eq hK hσ c
  have hδ3 : fieldActor (t := TwistTag.D4) σ σ ^ 3 = 1 := by
    have h1 : fieldActor (t := TwistTag.D4) σ (σ ^ 3) = fieldActor σ σ ^ 3 :=
      map_pow (fieldActorHom (t := TwistTag.D4) σ) σ 3
    rw [← h1, hσ3, fieldActor_one]
  have hF : fieldActor (t := TwistTag.D4) σ σ ∈
      graphFixedUnipotentStabilizer TwistTag.D4 K σ.toRingHom := by
    have := normalActor_mem (t := TwistTag.D4) σ 1 σ
    rwa [normalActor_one_left] at this
  have hδU : ∀ u ∈ (Sy : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
      fieldActor (t := TwistTag.D4) σ σ u ∈
        (Sy : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
    intro u hu
    rw [hPU] at hu ⊢
    have := Subgroup.mem_map_of_mem (fieldActor (t := TwistTag.D4) σ σ).toMonoidHom hu
    rwa [hF.1] at this
  obtain ⟨-, -, ⟨Θ, hΘ, -, hker, -⟩, -, -, -, -, -⟩ :=
    odd_triality_exact_automorphism_normal_form Nat.prime_three (by norm_num) hf K hK σ hσ
  have hσ1 : σ ≠ 1 := by
    intro h
    have hc := CFSG.RankThree.PartOne.KGD.card_fixSubfield_cube Nat.prime_three hf hK σ hσ
    have htop : fixSubfield σ = ⊤ := by
      ext c
      simp [h]
    rw [htop] at hc
    have hc' : Nat.card K = 3 ^ f := by
      rw [← hc]
      exact (Nat.card_congr Subfield.topEquiv.toEquiv).symm
    have hp1 : 1 < 3 ^ f := Nat.one_lt_pow (by omega) (by norm_num)
    rw [hK] at hc'
    nlinarith [hp1, pow_pos (lt_trans Nat.zero_lt_one hp1) 2]
  have hδI : fieldActor (t := TwistTag.D4) σ σ ∉
      (MulAut.conj : (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range := by
    intro hmem
    have hmem' : fieldActor (t := TwistTag.D4) σ σ ∈ Θ.ker := by rw [hker]; exact hmem
    have hΘδ : Θ (fieldActor (t := TwistTag.D4) σ σ) = σ :=
      hΘ (fieldActor (t := TwistTag.D4) σ σ) 1 σ (by rw [map_one, one_mul])
    exact hσ1 (hΘδ.symm.trans hmem')
  obtain ⟨ε, u, hu, hcase⟩ := exists_conj_mem_innExt Sy hZ hδ3 hδU hδI g hg3
  have huU : (u : ModGL TwistTag.D4.tag K) ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom := by
    have : u ∈ (Sy : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := hu
    rw [hPU, Subgroup.mem_subgroupOf] at this
    exact this
  refine ⟨u, huU, ?_, ?_⟩
  · rcases hcase with h | h
    · rw [← h, conj_pow, hg3, mul_one, mul_inv_cancel]
    · rw [← h, conj_pow, inv_pow, hg3, inv_one, mul_one, mul_inv_cancel]
  · intro hu'
    have hg : P (MulAut.conj g * fieldActor (t := TwistTag.D4) σ σ) := by
      rcases hcase with h | h
      · refine hconj ε _ ?_
        rw [h]
        exact hu'
      · refine hinv _ (hconj ε _ ?_)
        rw [h]
        exact hu'
    rcases hform with h | h
    · rw [h]
      exact hg
    · exact hinv _ (by rw [h]; exact hg)

theorem three_of_classes_gen
    (P : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) → Prop)
    (hconj : ∀ ε β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      P (ε * β * ε⁻¹) → P β)
    (hinv : ∀ β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), P β⁻¹ → P β)
    (hA : P (fieldActor (t := TwistTag.D4) σ σ))
    (hB : ∀ {c : K} (hc : σ c = c), c ≠ 0 →
      P (MulAut.conj (longElt hf hK σ hσ (Or.inr (Or.inr rfl)) c hc) *
        fieldActor (t := TwistTag.D4) σ σ))
    (β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hβ3 : β ^ 3 = 1)
    (hout : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) : P β := by
  classical
  haveI := finite_graphFixedRootGroup_D4 σ
  obtain ⟨u, hu, hu3, hred⟩ := exc_reduction_unipotent_gen hf hK σ hσ P hconj hinv β hβ3 hout
  refine hred ?_
  obtain ⟨w, s, r, r', hs, hr, hr', hw⟩ := exists_twistedConj_longForm hf hK σ hσ hu hu3
  refine hconj (MulAut.conj w⁻¹) _ ?_
  rw [conj_mul_twisted hf hK σ hσ (fieldActor (t := TwistTag.D4) σ σ) u w, hw]
  by_cases hne : s = 0 ∧ r = 0 ∧ r' = 0
  · obtain ⟨rfl, rfl, rfl⟩ := hne
    rw [longElt_zero hf hK σ hσ, longElt_zero hf hK σ hσ, longElt_zero hf hK σ hσ]
    simp only [mul_one, map_one, one_mul]
    exact hA
  · obtain ⟨ε, c, hc, hc0, hε⟩ := exists_conj_to_top_of_longForm hf hK σ hσ hs hr hr' hne
    refine hconj ε _ ?_
    rw [hε]
    exact hB hc hc0

theorem outerCentData_three_of_classes
    (hA : OuterCentData 3 (fieldActor (t := TwistTag.D4) σ σ))
    (β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hβ3 : β ^ 3 = 1)
    (hout : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) : OuterCentData 3 β := by
  classical
  haveI := finite_graphFixedRootGroup_D4 σ
  exact three_of_classes_gen hf hK σ hσ (fun γ => OuterCentData 3 γ)
    (fun ε γ h => OuterCentData.of_conj_aut Nat.prime_three ε h)
    (fun γ h => OuterCentData.of_inv h) hA
    (fun hc hc0 => outerCentData_three_classB hf hK σ hσ hc hc0) β hβ3 hout

end Reduction

theorem exc_charP_three_of_card (K : Type) [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = (3 ^ f) ^ 3) : CharP K 3 := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨s, hs, m, hsp, hm⟩ := FiniteField.card' K
  rw [← Nat.card_eq_fintype_card, hK] at hm
  have h1 : s ∣ (3 ^ f) ^ 3 := by
    rw [hm]
    exact dvd_pow_self s m.ne_zero
  have h2 : s = 3 :=
    (Nat.prime_dvd_prime_iff_eq hsp Nat.prime_three).1
      (hsp.dvd_of_dvd_pow (hsp.dvd_of_dvd_pow h1))
  rw [h2] at hs
  exact hs

theorem exc_exists_graphFixed_of_tauCeti (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) {S : Type} [Group S]
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩) (hq3 : q.p = 3) :
    ∃ (f : ℕ) (_ : 1 ≤ f) (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K),
      Nat.card K = (3 ^ f) ^ 3 ∧ (∀ c, σ c = c ^ (3 ^ f)) ∧
        Nonempty (S ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  obtain ⟨f, hfq⟩ : ∃ f, q.exponent = f := ⟨_, rfl⟩
  have hf : 1 ≤ f := by
    rw [← hfq]
    exact q.exponent_pos
  have hqcard : q.card = 3 ^ f := by
    rw [TauCeti.PrimePower.card_def, hq3, hfq]
  have hp2 : q.p ≠ 2 := by
    rw [hq3]
    norm_num
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK₀ : Nat.card (GaloisField 3 (3 * f)) = (3 ^ f) ^ 3 := by
    rw [GaloisField.card 3 (3 * f) (by omega), ← pow_mul, mul_comm]
  have hσ₀ : ∀ c : GaloisField 3 (3 * f),
      iterateFrobenius (GaloisField 3 (3 * f)) 3 f c = c ^ 3 ^ f := fun c => by
    rw [iterateFrobenius_def]
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Twisted.twistedBridge_trialityD4 q hv hp2
    (GaloisField 3 (3 * f)) (by rw [hK₀, hqcard]; rfl)
    (iterateFrobenius (GaloisField 3 (3 * f)) 3 f)
    (fun c => by rw [hqcard]; exact hσ₀ c)
  have hmodel : TwistedChevalleyModel S TwistTag.D4 (3 ^ f) := by
    unfold TwistedChevalleyModel
    exact ⟨GaloisField 3 (3 * f), inferInstance, inferInstance, hK₀,
      iterateFrobenius (GaloisField 3 (3 * f)) 3 f, hσ₀, ⟨e.trans b.symm⟩⟩
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e₁⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card TwistTag.D4 Nat.prime_three hf hmodel
  exact ⟨f, hf, K, inferInstance, inferInstance, σ, hK, hσ, ⟨e₁⟩⟩

theorem outerCentData_trialityD4_three_of
    (hA : ∀ (f : ℕ), 1 ≤ f → ∀ (K : Type) [Field K] [Finite K] [CharP K 3],
      Nat.card K = (3 ^ f) ^ 3 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (3 ^ f)) →
        OuterCentData 3 (fieldActor (t := TwistTag.D4) σ σ))
    (S : Type) [Group S] [Finite S]
    (idx : TauCeti.ValidLieTypeIndex) (htag : IsExcTrialityD4 idx.1)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group))
    (hpc : 3 = idx.1.characteristic)
    (β : MulAut S) (hβ : orderOf β = 3) (hout : β ∉ innerAut S) : OuterCentData 3 β := by
  classical
  obtain ⟨e⟩ := he
  obtain ⟨d, hv⟩ := idx
  cases d with
  | trialityD4 q =>
    have hq3 : q.p = 3 := by simpa using hpc.symm
    obtain ⟨f, hf, K, _, _, σ, hK, hσ, ⟨e₁⟩⟩ := exc_exists_graphFixed_of_tauCeti q hv e hq3
    haveI : CharP K 3 := exc_charP_three_of_card K hK
    haveI : Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
      Finite.of_equiv S e₁.toEquiv
    refine OuterCentData.of_congr Nat.prime_three e₁ ?_
    have hαp : MulAut.congr e₁ β ^ 3 = 1 := by
      rw [← map_pow, ← hβ, pow_orderOf_eq_one, map_one]
    have hαin : MulAut.congr e₁ β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
      rintro ⟨g, hg⟩
      apply hout
      refine ⟨e₁.symm g, ?_⟩
      apply (MulAut.congr e₁).injective
      rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, e₁.apply_symm_apply]
      exact hg
    exact outerCentData_three_of_classes hf hK σ hσ (hA f hf K hK σ hσ) _ hαp hαin
  | _ => simp [IsExcTrialityD4] at htag

end CFSG.HardMathSupport.Dickson.DefCharOuter.Export
