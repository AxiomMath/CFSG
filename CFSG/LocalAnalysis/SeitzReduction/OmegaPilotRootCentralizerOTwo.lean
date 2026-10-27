module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotRootCentralizerPerfect
import CFSG.Quasithin.Background.A3ComponentsQuotient

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (plusIndexEquiv coordinateQuadPlus regular_coordinateQuadPlus)

section Fix

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem exists_fixed_ne_zero_of_isPGroup [CharP K 2] [Finite V]
    (N : Subgroup (V ≃ₗ[K] V)) (hN : IsPGroup 2 N) {e e' : V} (he : e ≠ 0)
    (hP : ∀ g ∈ N, ∀ v ∈ Submodule.span K {e, e'}, g v ∈ Submodule.span K {e, e'}) :
    ∃ u ∈ Submodule.span K {e, e'}, u ≠ 0 ∧ ∀ g ∈ N, g u = u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := Submodule.span K {e, e'} with hPdef
  let act : MulAction N P :=
    { smul := fun g p => ⟨(g : V ≃ₗ[K] V) p, hP g g.2 p p.2⟩
      one_smul := fun p => Subtype.ext rfl
      mul_smul := fun g h p => Subtype.ext rfl }
  have heP : e ∈ P := Submodule.subset_span (Set.mem_insert e _)
  have h2 : 2 ∣ Nat.card P := by
    have hord : addOrderOf (⟨e, heP⟩ : P) = 2 := by
      apply addOrderOf_eq_prime
      · apply Subtype.ext
        change (2 : ℕ) • e = 0
        rw [two_nsmul, ← two_smul K e, CharTwo.two_eq_zero, zero_smul]
      · intro h0
        exact he (congrArg Subtype.val h0)
    rw [← hord]
    exact addOrderOf_dvd_natCard _
  have h0 : (0 : P) ∈ MulAction.fixedPoints N P := fun g => Subtype.ext (map_zero _)
  obtain ⟨u, hu, hu0⟩ := hN.exists_fixed_point_of_prime_dvd_card_of_fixed_point P h2 h0
  refine ⟨u, u.2, fun h => hu0 (Subtype.ext h.symm), fun g hg => ?_⟩
  exact congrArg Subtype.val (hu ⟨g, hg⟩)

end Fix

section OTwo

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
  {a a' b b' : Fin d}

theorem rootLeviBar_normal_isPGroup_eq_bot_of (hi : IsHypCoord Q a a') (hj : IsHypCoord Q b b')
    (hd : PairDisjoint a a' b b') (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hQS : CFSG.IsQuasisimple (stabPairsBar Q a a' b b') ∧
      center (stabPairsBar Q a a' b b') = ⊥)
    (N : Subgroup (rootLeviBar Q hi.hypPair hj.hypPair))
    (hNn : N.Normal) (hN2 : IsPGroup 2 N) : N = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h₁₂ := hi.orth hj hd
  have hρ := projHom_injective (Q := Q) hi.exists_ne_zero
  set N' : Subgroup (matrixProjectiveDerived (Q)) := N.map (Subgroup.subtype _)
    with hN'
  have hN'le : N' ≤ rootLeviBar (Q) hi.hypPair hj.hypPair := map_subtype_le N
  have hN'2 : IsPGroup 2 N' := hN2.map _
  have hN'norm : ∀ m ∈ rootLeviBar (Q) hi.hypPair hj.hypPair, ∀ x ∈ N',
      m * x * m⁻¹ ∈ N' := by
    rintro m hm _ ⟨⟨x', hx'M⟩, hx'N, rfl⟩
    exact ⟨⟨m, hm⟩ * ⟨x', hx'M⟩ * ⟨m, hm⟩⁻¹, hNn.conj_mem _ hx'N _, rfl⟩
  set Nl := N'.comap (projHom (Q)) with hNl
  have hNl2 : IsPGroup 2 Nl := hN'2.comap_of_injective _ hρ
  have hNlM : ∀ X ∈ Nl, ((X : orthDerived _) : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈
      rootLevi _ hi.hypPair hj.hypPair := by
    intro X hX
    obtain ⟨Y, hY, hYX⟩ := hN'le hX
    rw [hρ hYX] at hY
    exact mem_subgroupOf.mp hY
  have hNlconj : ∀ m : orthDerived (Q),
      (m : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈ rootLevi _ hi.hypPair hj.hypPair →
      ∀ X ∈ Nl, m⁻¹ * X * m ∈ Nl := by
    intro m hm X hX
    have hmM : projHom _ m ∈ rootLeviBar (Q) hi.hypPair hj.hypPair :=
      ⟨m, mem_subgroupOf.mpr hm, rfl⟩
    change projHom _ (m⁻¹ * X * m) ∈ N'
    have h := hN'norm _ (inv_mem hmM) _ hX
    rwa [inv_inv, ← map_inv, ← map_mul, ← map_mul] at h
  set Nlin := Nl.map (orthDerived (Q)).subtype with hNlin
  have hNlin2 : IsPGroup 2 Nlin := hNl2.map _
  have hP : ∀ g ∈ Nlin, ∀ v ∈ Submodule.span K {hi.hypPair.e, hj.hypPair.e},
      g v ∈ Submodule.span K {hi.hypPair.e, hj.hypPair.e} := by
    rintro _ ⟨X, hX, rfl⟩ v hv
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hv
    obtain ⟨h1, h2⟩ := apply_e_of_commute h₁₂ (mem_centralizer_singleton_iff.mp (hNlM X hX).1.2)
    set g := ((X : orthDerived (Q)) : (Fin d → K) ≃ₗ[K] (Fin d → K))
      with hgdef
    refine Submodule.mem_span_pair.mpr
      ⟨a * polar (Q) (g hj.hypPair.f) hj.hypPair.e -
        b * polar (Q) (g hi.hypPair.f) hj.hypPair.e,
      b * polar (Q) (g hi.hypPair.f) hi.hypPair.e -
        a * polar (Q) (g hj.hypPair.f) hi.hypPair.e, ?_⟩
    simp only [Subgroup.coe_subtype, map_add, map_smul]
    rw [h1, h2]
    module
  obtain ⟨u, huP, hu0, hu⟩ := exists_fixed_ne_zero_of_isPGroup Nlin hNlin2 hi.hypPair.e_ne_zero hP
  have hinv : ∀ m : orthDerived (Q),
      (m : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈ rootLevi _ hi.hypPair hj.hypPair →
      ∀ v, (∀ g ∈ Nlin, g v = v) → ∀ g ∈ Nlin,
        g ((m : (Fin d → K) ≃ₗ[K] (Fin d → K)) v) =
          (m : (Fin d → K) ≃ₗ[K] (Fin d → K)) v := by
    rintro m hm v hv _ ⟨X, hX, rfl⟩
    have h := hv _ ⟨m⁻¹ * X * m, hNlconj m hm X hX, rfl⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv,
      LinearEquiv.mul_apply] at h ⊢
    calc (X : (Fin d → K) ≃ₗ[K] (Fin d → K))
          ((m : (Fin d → K) ≃ₗ[K] (Fin d → K)) v) =
        (m : (Fin d → K) ≃ₗ[K] (Fin d → K))
          (((m : (Fin d → K) ≃ₗ[K] (Fin d → K)))⁻¹
            ((X : (Fin d → K) ≃ₗ[K] (Fin d → K))
              ((m : (Fin d → K) ≃ₗ[K] (Fin d → K)) v))) := by
          rw [LinearEquiv.apply_inv_apply']
      _ = _ := by rw [h]
  have hsub : ∀ v w, (∀ g ∈ Nlin, g v = v) → (∀ g ∈ Nlin, g w = w) →
      ∀ g ∈ Nlin, g (v - w) = v - w := fun v w hv hw g hg => by rw [map_sub, hv g hg, hw g hg]
  have hsmul : ∀ (c : K) v, c ≠ 0 → (∀ g ∈ Nlin, g (c • v) = c • v) → ∀ g ∈ Nlin, g v = v :=
    fun c v hc hv g hg => by
      have h := hv g hg
      rw [map_smul] at h
      exact smul_right_injective _ hc h
  have hx1 : eichler (Q) hi.hypPair.e ((1 : K) • hj.hypPair.f) ∈
      orthDerived (Q) := eichler_mem_orthDerived hQ hT _ _
  have hy1 : eichler (Q) hj.hypPair.e ((1 : K) • hi.hypPair.f) ∈
      orthDerived (Q) := eichler_mem_orthDerived hQ hT _ _
  have hxM := eichler_smul_f_mem_rootLevi h₁₂ (1 : K)
  have hyM := eichler_smul_f_mem_rootLevi' h₁₂ (1 : K)
  have hFx := hinv ⟨_, hx1⟩ hxM
  have hFy := hinv ⟨_, hy1⟩ hyM
  have hx_e : ∀ c d : K, eichler (Q) hi.hypPair.e ((1 : K) • hj.hypPair.f)
      (c • hi.hypPair.e + d • hj.hypPair.e) - (c • hi.hypPair.e + d • hj.hypPair.e) =
        (-d) • hi.hypPair.e := by
    intro c d
    rw [map_add, map_smul, map_smul, eichler_smul_f_apply_e, eichler_smul_f_apply_e' h₁₂]
    module
  have hy_e : ∀ c d : K, eichler (Q) hj.hypPair.e ((1 : K) • hi.hypPair.f)
      (c • hi.hypPair.e + d • hj.hypPair.e) - (c • hi.hypPair.e + d • hj.hypPair.e) =
        (-c) • hj.hypPair.e := by
    intro c d
    rw [map_add, map_smul, map_smul, eichler_smul_f_apply_e, eichler_smul_f_apply_e' h₁₂.symm]
    module
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp huP
  have hFe : (∀ g ∈ Nlin, g hi.hypPair.e = hi.hypPair.e) ∧
      ∀ g ∈ Nlin, g hj.hypPair.e = hj.hypPair.e := by
    have he₁ : (∀ g ∈ Nlin, g hi.hypPair.e = hi.hypPair.e) →
        ∀ g ∈ Nlin, g hj.hypPair.e = hj.hypPair.e := by
      intro h1
      have h := hsub _ _ (hFy _ h1) h1
      have e : eichler (Q) hj.hypPair.e ((1 : K) • hi.hypPair.f)
          hi.hypPair.e - hi.hypPair.e = (-1 : K) • hj.hypPair.e := by
        have := hy_e 1 0
        simpa using this
      exact hsmul (-1) _ (neg_ne_zero.mpr one_ne_zero) (by rw [← e]; exact h)
    have he₂ : (∀ g ∈ Nlin, g hj.hypPair.e = hj.hypPair.e) →
        ∀ g ∈ Nlin, g hi.hypPair.e = hi.hypPair.e := by
      intro h2
      have h := hsub _ _ (hFx _ h2) h2
      have e : eichler (Q) hi.hypPair.e ((1 : K) • hj.hypPair.f)
          hj.hypPair.e - hj.hypPair.e = (-1 : K) • hi.hypPair.e := by
        have := hx_e 0 1
        simpa using this
      exact hsmul (-1) _ (neg_ne_zero.mpr one_ne_zero) (by rw [← e]; exact h)
    by_cases hβ : β = 0
    · have hα : α ≠ 0 := by
        rintro rfl
        apply hu0
        rw [hβ]
        simp
      have h := hsub _ _ (hFy _ hu) hu
      rw [hy_e] at h
      have h2 := hsmul (-α) _ (neg_ne_zero.mpr hα) h
      exact ⟨he₂ h2, h2⟩
    · have h := hsub _ _ (hFx _ hu) hu
      rw [hx_e] at h
      have h1 := hsmul (-β) _ (neg_ne_zero.mpr hβ) h
      exact ⟨h1, he₁ h1⟩
  have hN'S : N' ≤ stabPairsBar Q a a' b b' := by
    intro x hx
    obtain ⟨X, rfl⟩ := projHom_surjective _ x
    have hXNl : X ∈ Nl := hx
    have hXM := hNlM X hXNl
    have hg : ((X : orthDerived _) : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈ Nlin :=
      ⟨X, hXNl, rfl⟩
    have h1 := hFe.1 _ hg
    have h2 := hFe.2 _ hg
    obtain ⟨hf1, hf2⟩ := apply_e_of_commute (orth_flipPair_flipPair h₁₂)
      (mem_centralizer_singleton_iff.mp hXM.2)
    simp only [flipPair_e, flipPair_f, h1, h2, hi.hypPair.polar_ef, hj.hypPair.polar_ef,
      one_smul] at hf1 hf2
    rw [polar_comm _ hj.hypPair.e hi.hypPair.f, h₁₂.fe, zero_smul, sub_zero] at hf1
    rw [h₁₂.ef, zero_smul, sub_zero] at hf2
    exact ⟨X, mem_subgroupOf.mpr ⟨⟨h1, hf1⟩, h2, hf2⟩, rfl⟩
  set N'' := N'.subgroupOf (stabPairsBar Q a a' b b') with hN''
  have hN''n : N''.Normal := ⟨fun x hx s => mem_subgroupOf.mpr (by
    have := hN'norm (s : matrixProjectiveDerived (Q))
      (stabPairsBar_le_rootLeviBar hi hj s.2) x (mem_subgroupOf.mp hx)
    simpa using this)⟩
  rcases CFSG.Quasithin.A3.eq_top_or_le_center_of_subnormal hQS.1 hN''n.isSubnormal with htop | hcen
  · exfalso
    have h2S : IsPGroup 2 (stabPairsBar Q a a' b b') := fun s => by
      have hs : s ∈ N'' := htop ▸ mem_top s
      obtain ⟨k, hk⟩ := hN'2 ⟨s, mem_subgroupOf.mp hs⟩
      refine ⟨k, Subtype.ext ?_⟩
      have := congrArg Subtype.val hk
      simpa using this
    have hnt : Nontrivial (stabPairsBar Q a a' b b') := by
      obtain ⟨-, -, a, b, hab⟩ := hQS.1
      by_contra h
      rw [not_nontrivial_iff_subsingleton] at h
      exact hab (Subsingleton.elim _ _)
    have hc := h2S.center_nontrivial
    rw [hQS.2] at hc
    exact (Subgroup.nontrivial_iff_ne_bot _).mp hc rfl
  · have hN''bot : N'' = ⊥ := le_bot_iff.mp (hQS.2 ▸ hcen)
    have hN'bot : N' = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hx' : (⟨x, hN'S hx⟩ : stabPairsBar Q a a' b b') ∈ N'' := mem_subgroupOf.mpr hx
      rw [hN''bot, mem_bot] at hx'
      rw [mem_bot]
      exact congrArg Subtype.val hx'
    exact (Subgroup.map_eq_bot_iff_of_injective N (Subgroup.subtype_injective _)).mp hN'bot

theorem rootLeviBar_normal_isPGroup_eq_bot {n : ℕ} (hn : 5 ≤ n) {i j : Fin n} (hij : i ≠ j)
    (N : Subgroup (rootLeviBar (coordinateQuadPlus n K)
      (isHypCoord_coordinateQuadPlus (K := K) i).hypPair
      (isHypCoord_coordinateQuadPlus (K := K) j).hypPair))
    (hNn : N.Normal) (hN2 : IsPGroup 2 N) : N = ⊥ :=
  rootLeviBar_normal_isPGroup_eq_bot_of _ _ (pairDisjoint_plus hij)
    (regular_coordinateQuadPlus n K (by omega)).1 (regular_coordinateQuadPlus n K (by omega)).2
    (isQuasisimple_stabTwoBar hn hij) N hNn hN2

end OTwo

section Main

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem exists_pair_ne_fin (hn : 3 ≤ n) (k : Fin n) : ∃ i j : Fin n, i ≠ j ∧ i ≠ k ∧ j ≠ k := by
  by_cases h0 : k.val = 0
  · refine ⟨⟨1, by omega⟩, ⟨2, by omega⟩, ?_, ?_, ?_⟩ <;> simp [Fin.ext_iff, h0]
  · by_cases h1 : k.val = 1
    · refine ⟨⟨0, by omega⟩, ⟨2, by omega⟩, ?_, ?_, ?_⟩ <;> simp [Fin.ext_iff, h1]
    · refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ?_, ?_, ?_⟩ <;> simp [Fin.ext_iff] <;> omega

theorem centralizer_longRoot_decomp (hq : 4 ≤ Nat.card K) (hn : 5 ≤ n) (k : Fin n) :
    ∃ (z : matrixProjectiveDerived (coordinateQuadPlus n K))
      (Qz Mz : Subgroup (matrixProjectiveDerived (coordinateQuadPlus n K))),
      z ∈ pairPerp k ∧ IsLongRoot _ z ∧
        CFSG.Quasithin.perfectCore (centralizer ({z} : Set _)) = centralizer {z} ∧
        centralizer {z} = Qz ⊔ Mz ∧ IsPGroup 2 Qz ∧
        Mz ≤ normalizer (Qz : Set (matrixProjectiveDerived (coordinateQuadPlus n K))) ∧
        Disjoint Qz Mz ∧ (∀ N : Subgroup Mz, N.Normal → IsPGroup 2 N → N = ⊥) ∧
        pairTorus k ≤ Mz := by
  obtain ⟨i, j, hij, hik, hjk⟩ := exists_pair_ne_fin (by omega : 3 ≤ n) k
  have hQ := (regular_coordinateQuadPlus n K (by omega)).1
  have hi := isHypCoord_coordinateQuadPlus (K := K) i
  have hj := isHypCoord_coordinateQuadPlus (K := K) j
  have hk := isHypCoord_coordinateQuadPlus (K := K) k
  have h₁₂ := hi.orth hj (pairDisjoint_plus hij)
  have h₁₃ := hi.orth hk (pairDisjoint_plus hik)
  have h₂₃ := hj.orth hk (pairDisjoint_plus hjk)
  refine ⟨plusRootElt K (by omega) hij hik hjk, rootRadicalBar _ hi.hypPair hj.hypPair,
    rootLeviBar _ hi.hypPair hj.hypPair, ?_, isLongRoot_rootPairElt hQ h₁₂ h₁₃ h₂₃,
    CFSG.Quasithin.perfectCore_eq_self_of_perfect
      (commutator_centralizer_rootPairElt hn hq hij hik hjk),
    centralizer_rootPairElt hQ h₁₂ h₁₃ h₂₃, isPGroup_rootRadicalBar _ _,
    rootLeviBar_le_normalizer h₁₂, disjoint_rootRadicalBar_rootLeviBar h₁₂,
    fun N hN h2 => rootLeviBar_normal_isPGroup_eq_bot hn hij N hN h2, ?_⟩
  · exact rootPairElt_mem_pairPerpOf hQ h₁₂ h₁₃ h₂₃ hk
      ⟨single_plus_apply_eq_zero hik _ _ (.inl rfl) (.inl rfl),
        single_plus_apply_eq_zero hik _ _ (.inl rfl) (.inr rfl)⟩
      ⟨single_plus_apply_eq_zero hjk _ _ (.inl rfl) (.inl rfl),
        single_plus_apply_eq_zero hjk _ _ (.inl rfl) (.inr rfl)⟩
  · exact pairTorusOf_le_rootLeviBar hk
      ⟨single_plus_apply_eq_zero hik _ _ (.inl rfl) (.inl rfl),
        single_plus_apply_eq_zero hik _ _ (.inl rfl) (.inr rfl)⟩
      ⟨single_plus_apply_eq_zero hik _ _ (.inr rfl) (.inl rfl),
        single_plus_apply_eq_zero hik _ _ (.inr rfl) (.inr rfl)⟩
      ⟨single_plus_apply_eq_zero hjk _ _ (.inl rfl) (.inl rfl),
        single_plus_apply_eq_zero hjk _ _ (.inl rfl) (.inr rfl)⟩
      ⟨single_plus_apply_eq_zero hjk _ _ (.inr rfl) (.inl rfl),
        single_plus_apply_eq_zero hjk _ _ (.inr rfl) (.inr rfl)⟩

end Main

end CFSG.SeitzReduction.OmegaPilot
