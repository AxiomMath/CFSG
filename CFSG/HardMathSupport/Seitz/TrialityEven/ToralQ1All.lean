module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4Q1Main
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityThreeCharFree

set_option linter.unusedSectionVars false

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.GH74.GLS.Stage2.OddAut
  CFSG.LocalAnalysis.ComponentInitial CFSG
open scoped Matrix

namespace CFSG.HardMathSupport.Seitz.TrialityEven

open CFSG.GH74.GLS.Stage2.Bender.Thm1

local notation "𝒞[" K ", " σ "]" => graphFixedRootGroup TwistTag.D4 K (RingEquiv.toRingHom σ)


theorem d4_exists_aut_mono_plane_all {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (hq : (p ^ f) % 3 = 1) (E : Subgroup 𝒞[K, σ])
    (hEcard : Nat.card E = 3 ^ 2) :
    ∃ β : MulAut 𝒞[K, σ], ∀ e ∈ E,
      ((β⁻¹ e : 𝒞[K, σ]) : ModGL TwistTag.D4.tag K) ∈
        graphFixedMonomial TwistTag.D4 K σ.toRingHom := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcen : Subgroup.center 𝒞[K, σ] = ⊥ := center_graphFixedRootGroup_eq_bot σ.surjective
  have hinj : Function.Injective (MulAut.conj : 𝒞[K, σ] →* MulAut 𝒞[K, σ]) :=
    mulAut_conj_injective_of_center_bot hcen
  set V : Subgroup (MulAut 𝒞[K, σ]) := E.map (MulAut.conj : 𝒞[K, σ] →* MulAut 𝒞[K, σ]) with hV
  have hVp : IsPGroup 3 V := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [hV, Subgroup.card_map_of_injective hinj]
    exact hEcard
  obtain ⟨Θ, hΘ, hΘker⟩ :=
    (CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_fieldHom_D4 hp hf hK σ hσ).1
  obtain ⟨β, hβ⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.d4_exists_conj_le_B0_all hp hf K hK σ hσ hq V hVp
  refine ⟨β, fun e he => ?_⟩
  obtain ⟨g, δ, hgN, hgδ⟩ := hβ (MulAut.conj e) ⟨e, he, rfl⟩
  have hconj : β⁻¹ * MulAut.conj e * β = MulAut.conj (β⁻¹ e) := by
    refine MulEquiv.ext fun y => ?_
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.inv_apply_self]
  have hΘ1 : Θ (MulAut.conj (β⁻¹ e)) = 1 := by
    have : MulAut.conj (β⁻¹ e) ∈ Θ.ker := by
      rw [hΘker]
      exact ⟨β⁻¹ e, rfl⟩
    exact this
  rw [hconj] at hgδ
  have hΘδ : Θ (MulAut.conj (β⁻¹ e)) = δ := hΘ _ g δ hgδ
  have hδ1 : δ = 1 := hΘδ.symm.trans hΘ1
  rw [hδ1, fieldActor_one, mul_one] at hgδ
  have : β⁻¹ e = g := hinj hgδ
  rw [this]
  exact hgN

theorem d4_aniso_plane_q1_all {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (hq : (p ^ f) % 3 = 1) (E : Subgroup 𝒞[K, σ])
    (hEcard : Nat.card E = 3 ^ 2)
    (hanis : ∀ R : Subgroup 𝒞[K, σ], IsPGroup p R → R ≠ ⊥ →
      ¬ E ≤ Subgroup.normalizer (R : Set 𝒞[K, σ])) :
    ∃ β : MulAut 𝒞[K, σ], ∃ v ∈ E.map (β⁻¹).toMonoidHom, ∃ n ∈ E.map (β⁻¹).toMonoidHom,
      v ≠ 1 ∧ (v : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom ∧
      (n : ModGL TwistTag.D4.tag K) ∈ graphFixedMonomial TwistTag.D4 K σ.toRingHom ∧
      (n : ModGL TwistTag.D4.tag K) ∉ graphFixedTorus TwistTag.D4 K σ.toRingHom := by
  classical
  obtain ⟨β, hβ⟩ := d4_exists_aut_mono_plane_all hp hf K hK σ hσ hq E hEcard
  refine ⟨β, ?_⟩
  have hcard' : Nat.card (E.map (β⁻¹).toMonoidHom) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective (β⁻¹).injective]
    exact hEcard
  have hmono : ∀ x ∈ E.map (β⁻¹).toMonoidHom, (x : ModGL TwistTag.D4.tag K) ∈
      graphFixedMonomial TwistTag.D4 K σ.toRingHom := by
    rintro _ ⟨e, he, rfl⟩
    exact hβ e he
  rcases d4_plane_mono_cases K σ _ hcard' hmono with hT | h
  · exfalso
    obtain ⟨R, hRp, hR1, hER⟩ := d4_torus_plane_not_aniso hp hf K hK σ hσ _ hT
    have hmem : ∀ x : 𝒞[K, σ], x ∈ R.map β.toMonoidHom ↔ β⁻¹ x ∈ R := fun x => by
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨r, hr, rfl⟩
        show β⁻¹ (β r) ∈ R
        rw [MulAut.inv_apply_self]
        exact hr
      · intro h
        refine ⟨β⁻¹ x, h, ?_⟩
        show β (β⁻¹ x) = x
        rw [MulAut.apply_inv_self]
    refine hanis (R.map β.toMonoidHom) (hRp.map _) ?_ ?_
    · intro hbot
      exact hR1 ((Subgroup.map_eq_bot_iff_of_injective R β.injective).1 hbot)
    · intro e he
      have h1 := Subgroup.mem_normalizer_iff.1 (hER ⟨e, he, rfl⟩)
      rw [Subgroup.mem_normalizer_iff]
      intro x
      rw [hmem, hmem]
      have h2 : β⁻¹ x ∈ R ↔ β⁻¹ e * β⁻¹ x * (β⁻¹ e)⁻¹ ∈ R := h1 (β⁻¹ x)
      rw [map_mul, map_mul, map_inv]
      exact h2
  · exact h

theorem q1_line_data_all {p f : ℕ} (hq : (p ^ f) % 3 = 1) (K : Type) [Field K] [Finite K]
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (v n : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hv : (v : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom)
    (hv1 : v ≠ 1) (hv3 : v ^ 3 = 1) (hn3 : n ^ 3 = 1) (hnv : n * v = v * n)
    (hnmono : (n : ModGL TwistTag.D4.tag K) ∈ graphFixedMonomial TwistTag.D4 K σ.toRingHom)
    (hnT : (n : ModGL TwistTag.D4.tag K) ∉ graphFixedTorus TwistTag.D4 K σ.toRingHom) :
    ∃ ω : Kˣ, Units.map σ.toRingHom.toMonoidHom ω = ω ∧ ω ^ 3 = 1 ∧ ω ≠ 1 ∧
      (v : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag ![ω, ω, 1, ω] := by
  have hn3' : (n : ModGL TwistTag.D4.tag K) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hn3]
    rfl
  have hW3 : (graphFixedRootWeylHom TwistTag.D4 K σ.toRingHom
      ⟨(n : ModGL TwistTag.D4.tag K), Subgroup.mem_inf.2 ⟨hnmono, n.2⟩⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨(n : ModGL TwistTag.D4.tag K), Subgroup.mem_inf.2 ⟨hnmono, n.2⟩⟩ :
        graphFixedRootMonomial TwistTag.D4 K σ.toRingHom) ^ 3 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hn3')
    rw [this, map_one]
  have hfa := fieldActor_self_eq_of_cube hq K σ hσ v hv hv3
  refine CFSG.HardMathSupport.Timmesfeld.CrossChar.d4_fixed_line_all hq K σ hσ v n σ hv hv1 hv3
    hnmono hnT hW3 (Or.inl rfl) ?_
  rw [MulAut.mul_apply, hfa, MulAut.conj_apply, hnv]
  group

theorem q1_toral_data_all {p f : ℕ} [Fact p.Prime] (hf : 1 ≤ f)
    (hq : (p ^ f) % 3 = 1) (K : Type) [Field K] [Finite K] [CharP K p]
    (hK : Nat.card K = (p ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (v n : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hgen : ∀ S : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), v ∈ S → n ∈ S →
      E ≤ S)
    (hv : (v : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom)
    (hv1 : v ≠ 1) (hv3 : v ^ 3 = 1) (hn3 : n ^ 3 = 1) (hnv : n * v = v * n)
    (hnmono : (n : ModGL TwistTag.D4.tag K) ∈ graphFixedMonomial TwistTag.D4 K σ.toRingHom)
    (hnT : (n : ModGL TwistTag.D4.tag K) ∉ graphFixedTorus TwistTag.D4 K σ.toRingHom) :
    ∃ (y z : ModGL TwistTag.D4.tag (AlgebraicClosure K)),
      y ∈ adjointGroup TwistTag.D4.tag (AlgebraicClosure K) ∧
      ∃ hz : z ∈ monomialSubgroup TwistTag.D4.tag (AlgebraicClosure K),
        twistHom TwistTag.D4 (AlgebraicClosure K) (iterateFrobenius (AlgebraicClosure K) p f) y =
          z * y ∧
        (∀ e ∈ E, y * triEmb K σ (AlgebraicClosure K) e * y⁻¹ ∈
          torusGroup TwistTag.D4.tag (AlgebraicClosure K)) ∧
        (z ∈ torusGroup TwistTag.D4.tag (AlgebraicClosure K) ∨
          ∃ u : WeylGroup TwistTag.D4.tag, ∀ x,
            (u * weylQuotientHom TwistTag.D4.tag (AlgebraicClosure K) ⟨z⁻¹, inv_mem hz⟩ *
              (weylTwist TwistTag.D4 u)⁻¹) • x =
            d4T36M 1 *ᵥ permLattice TwistTag.D4.perm.symm x) := by
  classical
  have hp : p.Prime := Fact.out
  set L := AlgebraicClosure K with hL
  set Fr : L →+* L := iterateFrobenius L p f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (p ^ f) := fun c => iterateFrobenius_def p f c
  have hcomm : (algebraMap K L).comp σ.toRingHom = Fr.comp (algebraMap K L) :=
    RingHom.ext fun c => by simp [hσ, hFr, map_pow]
  obtain ⟨ω, -, hω3, hω1, hvω⟩ := q1_line_data_all hq K σ hσ v n hv hv1 hv3 hn3 hnv
    hnmono hnT
  set A : Lˣ := Units.map (algebraMap K L).toMonoidHom ω with hAdef
  have hA3 : A ^ 3 = 1 := by rw [hAdef, ← map_pow, hω3, map_one]
  have hA1 : A ≠ 1 := by
    intro h
    apply hω1
    apply Units.map_injective (f := (algebraMap K L).toMonoidHom) (algebraMap K L).injective
    rw [map_one]
    exact h
  set d : ModGL TwistTag.D4.tag L :=
    rootDiagUnit TwistTag.D4.tag (![A, A, 1, A] : Fin TwistTag.D4.tag.rank → Lˣ) with hd
  have hιv : triEmb K σ L v = d := by
    rw [triEmb_rootDiagUnit hvω, hd]
    congr 1
    funext i
    fin_cases i
    · rfl
    · rfl
    · exact map_one _
    · rfl
  have hνM := triEmb_mem_monomial (L := L) hnmono
  have hνC := triEmb_mem_adjointGroup (K := K) (σ := σ) (L := L) n
  have hν3 : (triEmb K σ L n) ^ 3 = 1 := by rw [← map_pow, hn3, map_one]
  have hνT := triEmb_not_mem_torus (L := L) hnT
  have hcommν : triEmb K σ L n * d = d * triEmb K σ L n := by
    rw [← hιv, ← map_mul, ← map_mul, hnv]
  obtain ⟨Y, hY, a, hYa, hreg⟩ := d4_toral_conj_A2 hA3 hA1 hνM hνC hν3 hνT hcommν
  set y : ModGL TwistTag.D4.tag L := Y⁻¹ with hydef
  have hy : y ∈ rootSpan TwistTag.D4.tag L d4LongA2 := inv_mem hY
  have hya : y * triEmb K σ L n * y⁻¹ = rootDiagUnit TwistTag.D4.tag a := by
    rw [hydef, inv_inv]
    exact hYa
  have hFν : twistHom TwistTag.D4 L Fr (triEmb K σ L n) = triEmb K σ L n :=
    triEmb_fixed Fr hcomm n
  obtain ⟨b, hzmem, hzb, hsame⟩ := q1_F_data hq hy hya (fun α hα => (hreg α hα).2) hFν
  obtain ⟨hzM, hcls, hztor⟩ := d4_A2_conj_monomial _ hzmem a b hreg hsame hzb
  have hyG : y ∈ adjointGroup TwistTag.D4.tag L := rootSpan_le_adjointGroup L d4LongA2 hy
  have hcent : y * d = d * y := by
    have h := rootSpan_le_centralizer (τ := TwistTag.D4.tag) (K := L)
      (![A, A, 1, A] : Fin TwistTag.D4.tag.rank → Lˣ) (S := d4LongA2)
      (fun α hα => (d4Minus_rootCharKernel hA3 hA1 α).2 hα) hy
    exact Subgroup.mem_centralizer_singleton_iff.1 h
  have hconjd : y * d * y⁻¹ = d := by
    rw [hcent]
    group
  set S : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    (torusGroup TwistTag.D4.tag L).comap ((MulAut.conj y).toMonoidHom.comp (triEmb K σ L))
    with hS
  have hvS : v ∈ S := by
    change y * triEmb K σ L v * y⁻¹ ∈ torusGroup TwistTag.D4.tag L
    rw [hιv, hconjd]
    exact rootDiagUnit_mem_torusGroup _
  have hnS : n ∈ S := by
    change y * triEmb K σ L n * y⁻¹ ∈ torusGroup TwistTag.D4.tag L
    rw [hya]
    exact rootDiagUnit_mem_torusGroup _
  have hyE : ∀ e ∈ E, y * triEmb K σ L e * y⁻¹ ∈ torusGroup TwistTag.D4.tag L :=
    fun e he => hgen S hvS hnS he
  refine ⟨y, twistHom TwistTag.D4 L Fr y * y⁻¹, hyG, hzM, (inv_mul_cancel_right _ _).symm, hyE, ?_⟩
  have hinv : weylQuotientHom TwistTag.D4.tag L
      ⟨(twistHom TwistTag.D4 L Fr y * y⁻¹)⁻¹, inv_mem hzM⟩ =
      (weylQuotientHom TwistTag.D4.tag L ⟨twistHom TwistTag.D4 L Fr y * y⁻¹, hzM⟩)⁻¹ :=
    map_inv (weylQuotientHom TwistTag.D4.tag L) ⟨twistHom TwistTag.D4 L Fr y * y⁻¹, hzM⟩
  rcases hcls with h1 | hA | hB
  · exact Or.inl (hztor.2 h1)
  · obtain ⟨u, hu⟩ := q1_class_witness (Or.inl hA)
    exact Or.inr ⟨u, fun x => by rw [hinv]; exact hu x⟩
  · obtain ⟨u, hu⟩ := q1_class_witness (Or.inr hB)
    exact Or.inr ⟨u, fun x => by rw [hinv]; exact hu x⟩

theorem d4_toral_q1_all {p f : ℕ} [Fact p.Prime] (hf : 1 ≤ f) (hq : (p ^ f) % 3 = 1)
    (K : Type) [Field K] [Finite K] [CharP K p] (hK : Nat.card K = (p ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hE : IsElementaryAbelian 3 E)
    (hEcard : Nat.card E = 3 ^ 2)
    (hanis : ∀ R : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), IsPGroup p R →
      R ≠ ⊥ → ¬ E ≤ Subgroup.normalizer (R : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) :
    ∃ β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      (∃ F : D4PhiFrame K σ (p ^ f) 1, F.Contains (E.map (β⁻¹).toMonoidHom)) ∧
      ∃ F : D4SteinbergFrame K σ (p ^ f) 1, F.Contains (E.map (β⁻¹).toMonoidHom) := by
  classical
  have hp : p.Prime := Fact.out
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨β, v, hv, n, hn, hv1, hvT, hnM, hnT⟩ :=
    d4_aniso_plane_q1_all hp hf K hK σ hσ hq E hEcard hanis
  refine ⟨β, ?_⟩
  set E' := E.map (β⁻¹).toMonoidHom with hE'
  have hE'ea : IsElementaryAbelian 3 E' := IsElementaryAbelian.map (β⁻¹).toMonoidHom
  have hcard' : Nat.card E' = 3 ^ 2 := by
    rw [hE', Subgroup.card_map_of_injective (β⁻¹).injective]
    exact hEcard
  have hE'3 : ∀ e ∈ E', e ^ 3 = 1 := fun e he => elemPow_eq_one_of_isElementaryAbelian e he
  have hnv : n * v = v * n :=
    congrArg Subtype.val ((inferInstance : IsMulCommutative E').is_comm.comm ⟨n, hn⟩ ⟨v, hv⟩)
  have hnz : n ∉ Subgroup.zpowers v := by
    intro h
    apply hnT
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 h
    rw [Subgroup.coe_zpow]
    exact zpow_mem hvT k
  have hgen := plane_le_of_pair E' hcard' hE'3 hv hn hv1 hnz
  obtain ⟨y, z, hy, hz, hFy, hyE, hcase⟩ := q1_toral_data_all hf hq K hK σ hσ E' v n hgen hvT hv1
    (hE'3 v hv) (hE'3 n hn) hnv hnM hnT
  rcases hcase with hzT | ⟨u, hu⟩
  · exfalso
    obtain ⟨R, hRp, hR1, hER⟩ := d4_toral_split_normalizes hf K hK σ hσ E' hy hzT hFy hyE
    obtain ⟨R', hR'p, hR'1, hER'⟩ := normalizes_of_map (β⁻¹) E R hRp hR1 hER
    exact hanis R' hR'p hR'1 hER'
  · exact ⟨d4PhiFrame_of_toral hf K hK σ hσ E' hy hz hFy hyE u hu,
      d4SteinbergFrame_of_toral K σ hσ (Or.inl rfl) E' hE'3 hy hz hFy hyE u hu⟩

end CFSG.HardMathSupport.Seitz.TrialityEven
