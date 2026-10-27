module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.TrialityThreeAssembly
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TrialityThree

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 TauCeti
open CFSG.HardMathSupport.Seitz.TrialityOdd (exists_trialityD4_model_odd)
open CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator
  (seitzExcAnisotropicForAt_trialityOdd_proved)
open CFSG.LieType.Chevalley (graphFixedRootGroup odd_triality_exact_automorphism_normal_form)
open CFSG.RankThree.PartOne.CTP (eq_conj_of_congr_eq_conj)
open CFSG.RankThree.PartOne.SEITZ2
  (exists_conj_mem_of_plane_of_cyclic_outer isCyclic_outer_of_hom)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

@[expose] def OutRankOne (p : ℕ) (K : Type) [Group K] : Prop :=
  ∀ F : Subgroup (MulAut K), IsElemAbelian p F → Nat.card F = p ^ 2 →
    ∃ g : K, g ≠ 1 ∧ MulAut.conj g ∈ F

theorem OutRankOne.of_mulEquiv {K P : Type} [Group K] [Group P] (e : K ≃* P) {p : ℕ}
    (h : OutRankOne p P) : OutRankOne p K := by
  intro F hF hFc
  have hF' : IsElemAbelian p (F.map (MulAut.congr e).toMonoidHom) := hF.map _
  have hc' : Nat.card (F.map (MulAut.congr e).toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective (MulAut.congr e).injective, hFc]
  obtain ⟨g, hg1, hgF⟩ := h _ hF' hc'
  obtain ⟨φ, hφF, hφ⟩ := hgF
  refine ⟨e.symm g, fun h1 => hg1 (by simpa using congrArg e h1), ?_⟩
  have := eq_conj_of_congr_eq_conj e (σ := φ) hφ
  rw [← this]
  exact hφF

theorem outRankOne_of_isCyclic_outer {P : Type} [Group P] [Finite P] {p : ℕ} (hp : p.Prime)
    (hcyc : IsCyclic (Outer P)) :
    OutRankOne p P := by
  intro F hF hFc
  have := hF.isElementaryAbelian
  exact exists_conj_mem_of_plane_of_cyclic_outer hp hcyc F hFc

section OutRank

variable {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y} [K.Normal] {p : ℕ} [Fact p.Prime]

theorem card_inf_eq_of_outRank (hC : Subgroup.centralizer (K : Set Y) = ⊥)
    (hnoK : ¬ ∃ E : Subgroup Y, E ≤ K ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3)
    (hout : OutRankOne p K) {E : Subgroup Y} (hE : IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 3) : Nat.card (E ⊓ K : Subgroup Y) = p ^ 2 := by
  have hp : p.Prime := Fact.out
  have hEKa : IsElemAbelian p (E ⊓ K : Subgroup Y) := hE.mono inf_le_left
  have hdvd : Nat.card (E ⊓ K : Subgroup Y) ∣ p ^ 3 := by
    rw [← hEc]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  rcases (show k ≤ 1 ∨ k = 2 ∨ k = 3 by omega) with hk1 | rfl | rfl
  · exfalso
    obtain ⟨F, hFE, -, hdisj, hsup⟩ := CFSG.SignalizerFunctorTheorem.exists_complement_containing
      hp hE inf_le_left bot_le (inf_bot_eq _)
    have hcF : Nat.card (E ⊓ K : Subgroup Y) * Nat.card F = p ^ 3 := by
      rw [← hEc]
      exact CFSG.SignalizerFunctorTheorem.card_mul_card_complement hE inf_le_left hFE hdisj hsup
    have hFa : IsElemAbelian p F := hE.mono hFE
    have hFK : F ⊓ K = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      have : y ∈ (E ⊓ K) ⊓ F := ⟨⟨hFE hy.1, hy.2⟩, hy.1⟩
      rwa [hdisj] at this
    have hF2 : p ^ 2 ∣ Nat.card F := by
      have hFdvd : Nat.card F ∣ p ^ 3 := ⟨Nat.card (E ⊓ K : Subgroup Y), by rw [← hcF, mul_comm]⟩
      obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow hp).1 hFdvd
      rw [hk', hj', ← pow_add] at hcF
      have hkj := Nat.pow_right_injective hp.two_le hcF
      rw [hj']
      exact pow_dvd_pow p (by omega)
    obtain ⟨F₀, hF₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := F) p hF2
    let F₁ : Subgroup Y := F₀.map F.subtype
    have hF₁F : F₁ ≤ F := Subgroup.map_subtype_le F₀
    have hF₁c : Nat.card F₁ = p ^ 2 := by
      rw [Subgroup.card_map_of_injective F.subtype_injective, hF₀]
    have hF₁a : IsElemAbelian p F₁ := hFa.mono hF₁F
    have hinj := conjNormal_injective (K := K) hC
    have hE' : IsElemAbelian p (F₁.map (MulAut.conjNormal : Y →* MulAut K)) := hF₁a.map _
    have hc' : Nat.card (F₁.map (MulAut.conjNormal : Y →* MulAut K)) = p ^ 2 := by
      rw [Subgroup.card_map_of_injective hinj, hF₁c]
    obtain ⟨g, hg1, hgE⟩ := hout _ hE' hc'
    obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.1 hgE
    rw [← MulAut.conjNormal_val] at hyg
    have hyK : y = (g : Y) := hinj hyg
    have hy1 : y ∈ F ⊓ K := ⟨hF₁F hy, hyK ▸ g.2⟩
    rw [hFK, Subgroup.mem_bot] at hy1
    exact hg1 (Subtype.ext (hyK ▸ hy1))
  · exact hk'
  · exact absurd ⟨E ⊓ K, inf_le_right, hEKa, hk'⟩ hnoK

end OutRank

theorem rankLE2_of_no_cube {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    (h : ¬ ∃ E : Subgroup G, IsElemAbelian p E ∧ Nat.card E = p ^ 3) : RankLE2 p G := by
  by_contra hr
  exact h (exists_isElemAbelian_card_of_not_rankLE2 hp hr).2

theorem conj_injective_subgroup_of_centralizer_eq_bot {Y : Type*} [Group Y] {K : Subgroup Y}
    (hC : Subgroup.centralizer (K : Set Y) = ⊥) :
    Function.Injective (MulAut.conj : K →* MulAut K) := by
  rw [injective_iff_map_eq_one]
  intro k hk
  have hkC : (k : Y) ∈ Subgroup.centralizer (K : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := congrArg Subtype.val (DFunLike.congr_fun hk ⟨y, hy⟩)
    change (k : Y) * y * (k : Y)⁻¹ = y at h1
    calc y * (k : Y) = (k : Y) * y * (k : Y)⁻¹ * (k : Y) := by rw [h1]
      _ = (k : Y) * y := by group
  rw [hC, Subgroup.mem_bot] at hkC
  exact Subtype.ext hkC

section OutRankTriality


theorem outRankOne_trialityOdd {q : PrimePower} (hv : (LieTypeIndex.trialityD4 q).Valid)
    (hq2 : q.p ≠ 2) {K : Type} [Group K] [Finite K] (e : K ≃* Cat ⟨.trialityD4 q, hv⟩) :
    OutRankOne 3 K := by
  obtain ⟨X, _, _, σ, hX, hσ, ⟨e'⟩⟩ := exists_trialityD4_model_odd hq2 (K := K) ⟨hv, ⟨e⟩⟩
  obtain ⟨-, -, ⟨Θ, -, hsurj, hker, -⟩, hcyc, -⟩ :=
    odd_triality_exact_automorphism_normal_form q.prime_p hq2 q.exponent_pos X hX σ hσ
  have hcycOut := isCyclic_outer_of_hom Θ hsurj hker
  have : Finite (graphFixedRootGroup CFSG.Blueprint.Chevalley.TwistTag.D4 X σ.toRingHom) :=
    Finite.of_equiv K e'.toEquiv
  exact (outRankOne_of_isCyclic_outer Nat.prime_three hcycOut).of_mulEquiv e'

theorem card_inf_eq_nine_trialityOdd {q : PrimePower} (hv : (LieTypeIndex.trialityD4 q).Valid)
    (hq2 : q.p ≠ 2) {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y} [K.Normal]
    (hC : Subgroup.centralizer (K : Set Y) = ⊥)
    (he : Nonempty (K ≃* Cat ⟨.trialityD4 q, hv⟩))
    (hno : ¬ ∃ E₀ : Subgroup Y, E₀ ≤ K ∧ IsElemAbelian 3 E₀ ∧ Nat.card E₀ = 3 ^ 3)
    {E : Subgroup Y} (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 3) :
    Nat.card (E ⊓ K : Subgroup Y) = 3 ^ 2 := by
  obtain ⟨e⟩ := he
  have : Finite K := inferInstance
  exact card_inf_eq_of_outRank hC hno (outRankOne_trialityOdd hv hq2 e) hE hEc

end OutRankTriality

section InnerPlane


theorem planeGen_inner_trialityOdd_three {q : PrimePower}
    (hv : (LieTypeIndex.trialityD4 q).Valid) (hq2 : q.p ≠ 2) (hq3 : q.p ≠ 3)
    (hr : RankLE2 3 (Cat ⟨.trialityD4 q, hv⟩))
    {E : Subgroup (MulAut (Cat ⟨.trialityD4 q, hv⟩))} (hE : IsElemAbelian 3 E)
    (hEc : Nat.card E = 3 ^ 2) (hin : InnerPlane ⟨.trialityD4 q, hv⟩ 3 E) : PlaneGen E := by
  have hex : ¬ IsD2SeitzException 3 (LieTypeIndex.trialityD4 q) :=
    not_isD2SeitzException_of_chevalleyExc (isChevalleyExcIndex_trialityD4 q)
  have hchar : 3 ≠ (LieTypeIndex.trialityD4 q).characteristic := by
    rw [LieTypeIndex.characteristic_trialityD4]
    exact fun h => hq3 h.symm
  by_cases hN : NormalizesRSubgroup ⟨.trialityD4 q, hv⟩ E
  · exact seitzExcParabolicTw ⟨.trialityD4 q, hv⟩ 3 Nat.prime_three (by norm_num) hchar hex E hE
      hEc ⟨hin, Or.inl ⟨q, rfl⟩, hN⟩
  · exact seitzExcAnisotropicForAt_trialityOdd_proved ⟨.trialityD4 q, hv⟩ 3 Nat.prime_three
      (by norm_num) hchar hex E hE hEc ⟨hin, ⟨q, rfl⟩, ⟨q, rfl, hq2⟩, hr, hN⟩

theorem closure_centralizers_trialityOdd_three {q : PrimePower}
    (hv : (LieTypeIndex.trialityD4 q).Valid) (hq2 : q.p ≠ 2) (hq3 : q.p ≠ 3)
    (hinj : Function.Injective
      (MulAut.conj : Cat ⟨.trialityD4 q, hv⟩ →* MulAut (Cat ⟨.trialityD4 q, hv⟩)))
    (hr : RankLE2 3 (Cat ⟨.trialityD4 q, hv⟩)) {B : Subgroup (Cat ⟨.trialityD4 q, hv⟩)}
    (hB : IsElemAbelian 3 B) (hBc : Nat.card B = 3 ^ 2) :
    Subgroup.closure {k : Cat ⟨.trialityD4 q, hv⟩ | ∃ x ∈ B, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  have hE : IsElemAbelian 3 (B.map (MulAut.conj : Cat ⟨.trialityD4 q, hv⟩ →*
      MulAut (Cat ⟨.trialityD4 q, hv⟩))) := hB.map _
  have hEc : Nat.card (B.map (MulAut.conj : Cat ⟨.trialityD4 q, hv⟩ →*
      MulAut (Cat ⟨.trialityD4 q, hv⟩))) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective hinj, hBc]
  have hin : InnerPlane ⟨.trialityD4 q, hv⟩ 3 (B.map (MulAut.conj : Cat ⟨.trialityD4 q, hv⟩ →*
      MulAut (Cat ⟨.trialityD4 q, hv⟩))) := fun _ ⟨x, _, hx⟩ => ⟨x, hx⟩
  exact closure_comm_of_planeGen_conj (planeGen_inner_trialityOdd_three hv hq2 hq3 hr hE hEc hin)

end InnerPlane

@[expose] def TrialityOddLocalGen : Prop :=
  ∀ (q : PrimePower) (hv : (LieTypeIndex.trialityD4 q).Valid), q.p ≠ 2 → q.p ≠ 3 →
    ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y), K.Normal →
      Subgroup.centralizer (K : Set Y) = ⊥ → Nonempty (K ≃* Cat ⟨.trialityD4 q, hv⟩) →
      (¬ ∃ E₀ : Subgroup Y, E₀ ≤ K ∧ IsElemAbelian 3 E₀ ∧ Nat.card E₀ = 3 ^ 3) →
      ∀ E : Subgroup Y, IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
      ∀ a ∈ E ⊓ K, a ≠ 1 → ∀ k ∈ K, k * a = a * k →
        k ∈ Subgroup.closure {x : Y | x ∈ K ∧ x * a = a * x ∧
          ∃ e ∈ E, e ∉ Subgroup.zpowers a ∧ x * e = e * x}

section Reduction


theorem trialityOuterCubesThreeOdd_of_localGen (h : TrialityOddLocalGen) :
    TrialityOuterCubesThreeOdd := by
  intro q hv hq2 _ Y _ _ K hKn hC he hchar _ hno E hE hEc
  have hq3 : q.p ≠ 3 := by
    intro h3
    apply hchar
    show 3 = (LieTypeIndex.trialityD4 q).characteristic
    rw [LieTypeIndex.characteristic_trialityD4, h3]
  have : K.Normal := hKn
  have hA : Nat.card (E ⊓ K : Subgroup Y) = 3 ^ 2 :=
    card_inf_eq_nine_trialityOdd hv hq2 hC he hno hE hEc
  obtain ⟨e⟩ := he
  have hAK : E ⊓ K ≤ K := inf_le_right
  have hAa : IsElemAbelian 3 (E ⊓ K) := hE.mono inf_le_left
  have hBa : IsElemAbelian 3 (((E ⊓ K).subgroupOf K).map e.toMonoidHom) :=
    (hAa.subgroupOf K).map _
  have hBc : Nat.card (((E ⊓ K).subgroupOf K).map e.toMonoidHom) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv, hA]
  have hinj : Function.Injective (MulAut.conj : Cat ⟨.trialityD4 q, hv⟩ →*
      MulAut (Cat ⟨.trialityD4 q, hv⟩)) :=
    CFSG.LieType.SeitzGeneration.conj_injective_of_mulEquiv e.symm
      (conj_injective_subgroup_of_centralizer_eq_bot hC)
  have hnoC : ¬ ∃ F : Subgroup (Cat ⟨.trialityD4 q, hv⟩), IsElemAbelian 3 F ∧
      Nat.card F = 3 ^ 3 := by
    rintro ⟨F, hF, hFc⟩
    refine hno ⟨(F.map e.symm.toMonoidHom).map K.subtype, Subgroup.map_subtype_le _,
      (hF.map _).map _, ?_⟩
    rw [Subgroup.card_map_of_injective K.subtype_injective,
      Subgroup.card_map_of_injective e.symm.injective, hFc]
  have hgen := closure_centralizers_trialityOdd_three hv hq2 hq3 hinj
    (rankLE2_of_no_cube Nat.prime_three hnoC) hBa hBc
  have hKle := le_closure_centralizers_of_equiv hAK e hgen
  refine hKle.trans ((Subgroup.closure_le _).2 ?_)
  rintro x ⟨hxK, b, hbA, hb1, hxb⟩
  have hL : K ⊓ Subgroup.centralizer {b} ≤ hyperClosure 3 K E := by
    refine le_hyperClosure_of_plane Nat.prime_three hE hEc hbA.1 hb1 inf_le_left ?_ ?_
    · intro l hl
      exact (Subgroup.mem_centralizer_singleton_iff.1 hl.2).symm
    · intro l hl
      refine Subgroup.closure_mono ?_ (h q hv hq2 hq3 Y K hKn hC ⟨e⟩ hno E hE hEc b hbA hb1 l hl.1
        (Subgroup.mem_centralizer_singleton_iff.1 hl.2))
      rintro y ⟨hyK, hyb, f, hfE, hfb, hyf⟩
      exact ⟨⟨hyK, Subgroup.mem_centralizer_singleton_iff.2 hyb⟩, f, hfE, hfb, hyf.symm⟩
  exact hL ⟨hxK, Subgroup.mem_centralizer_singleton_iff.2 hxb⟩

end Reduction

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc
