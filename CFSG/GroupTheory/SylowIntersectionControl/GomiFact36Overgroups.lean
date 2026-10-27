module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFact36Inputs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ParabolicTransfer
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3318C
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListLinear
public import CFSG.Quasithin.MS93.MSPBT
public import CFSG.Quasithin.Vol2.GoldschmidtLem1227EqA6
public import CFSG.Adapters.LinearCatalogStated
public import CFSG.Adapters.StatedPSLTwoSeven
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2Carrier
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin

section TwoOver

variable {Q : Type*} [Group Q]

@[expose] def IsGomiTwoOver (S : Subgroup Q) : Prop :=
  ∃ X₁ X₂ : Subgroup Q, ∀ P : Subgroup Q,
    Subgroup.normalizer (S : Set Q) < P → P < ⊤ → P = X₁ ∨ P = X₂

@[expose] def GomiTwoOvergroups (Q : Type*) [Group Q] : Prop :=
  ∀ S : Sylow 2 Q, IsGomiTwoOver (S : Subgroup Q)

theorem IsGomiTwoOver.map {Y : Type*} [Group Y] {π : Q →* Y} (hπ : Function.Surjective π)
    {S : Subgroup Q} (hN : Subgroup.normalizer ((S.map π : Subgroup Y) : Set Y) =
      (Subgroup.normalizer (S : Set Q)).map π) (h : IsGomiTwoOver S) :
    IsGomiTwoOver (S.map π) := by
  obtain ⟨X₁, X₂, hX⟩ := h
  refine ⟨X₁.map π, X₂.map π, fun P hNP hPt => ?_⟩
  have hc : Subgroup.normalizer (S : Set Q) < P.comap π := by
    refine lt_of_le_of_ne (fun x hx => hNP.le ?_) fun heq => hNP.ne ?_
    · rw [hN]
      exact Subgroup.mem_map_of_mem π hx
    · rw [hN, heq, Subgroup.map_comap_eq_self_of_surjective hπ]
  have ht : P.comap π < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun heq => hPt.ne ?_
    rw [← Subgroup.map_comap_eq_self_of_surjective hπ P, heq, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr hπ]
  rcases hX _ hc ht with h | h
  · exact Or.inl (by rw [← h, Subgroup.map_comap_eq_self_of_surjective hπ])
  · exact Or.inr (by rw [← h, Subgroup.map_comap_eq_self_of_surjective hπ])

theorem IsGomiTwoOver.of_map {Y : Type*} [Group Y] {π : Q →* Y} {S : Subgroup Q}
    (hker : π.ker ≤ Subgroup.normalizer (S : Set Q))
    (hN : Subgroup.normalizer ((S.map π : Subgroup Y) : Set Y) =
      (Subgroup.normalizer (S : Set Q)).map π) (h : IsGomiTwoOver (S.map π)) :
    IsGomiTwoOver S := by
  obtain ⟨X₁, X₂, hX⟩ := h
  refine ⟨X₁.comap π, X₂.comap π, fun P hNP hPt => ?_⟩
  have hPeq : (P.map π).comap π = P := by
    rw [Subgroup.comap_map_eq, sup_eq_left.mpr (hker.trans hNP.le)]
  have hc : Subgroup.normalizer ((S.map π : Subgroup Y) : Set Y) < P.map π := by
    rw [hN]
    refine lt_of_le_of_ne (Subgroup.map_mono hNP.le) fun heq => hNP.ne ?_
    have := congrArg (Subgroup.comap π) heq
    rwa [hPeq, Subgroup.comap_map_eq, sup_eq_left.mpr hker] at this
  have ht : P.map π < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun heq => hPt.ne ?_
    rw [← hPeq, heq, Subgroup.comap_top]
  rcases hX _ hc ht with h | h
  · exact Or.inl (by rw [← hPeq, h])
  · exact Or.inr (by rw [← hPeq, h])

theorem GomiTwoOvergroups.of_surjective {X : Type} [Group X] [Finite X] {Y : Type} [Group Y]
    {π : X →* Y} (hπ : Function.Surjective π) (h : GomiTwoOvergroups X) :
    GomiTwoOvergroups Y := by
  intro S'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, rfl⟩ := Sylow.mapSurjective_surjective hπ 2 S'
  rw [Sylow.coe_mapSurjective]
  exact (h S).map hπ
    (CFSG.LocalAnalysis.UniquenessCase.UC22.normalizer_map_sylow_eq π hπ S)

theorem GomiTwoOvergroups.of_quotient {X : Type} [Group X] [Finite X] {Y : Type} [Group Y]
    {π : X →* Y} (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center X)
    (h : GomiTwoOvergroups Y) : GomiTwoOvergroups X := by
  intro S
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h' := h (S.mapSurjective hπ)
  rw [Sylow.coe_mapSurjective] at h'
  refine h'.of_map (fun z hz => ?_)
    (CFSG.LocalAnalysis.UniquenessCase.UC22.normalizer_map_sylow_eq π hπ S)
  have hz' := Subgroup.mem_center_iff.mp (hker hz)
  refine Subgroup.mem_normalizer_iff.mpr fun g => ?_
  rw [← hz' g, mul_inv_cancel_right]

theorem GomiTwoOvergroups.of_sylow [Finite Q] (S₀ : Sylow 2 Q)
    (h : IsGomiTwoOver (S₀ : Subgroup Q)) : GomiTwoOvergroups Q := by
  intro S
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq Q S₀ S
  have hg : ((g • S₀ : Sylow 2 Q) : Subgroup Q) =
      (S₀ : Subgroup Q).map (MulAut.conj g).toMonoidHom := by
    ext x
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
    rfl
  rw [hg]
  exact h.map (MulAut.conj g).surjective
    (Subgroup.map_equiv_normalizer_eq (S₀ : Subgroup Q) (MulAut.conj g)).symm

end TwoOver

section Models

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem gomiTwoOvergroups_sl3 (K : Type) [Field K] [Finite K] [CharP K 2] :
    GomiTwoOvergroups (Matrix.SpecialLinearGroup (Fin 3) K) := by
  obtain ⟨U, hU⟩ := exists_sylow_unitriangular (K := K) 2 (n := 3) (by norm_num)
  refine GomiTwoOvergroups.of_sylow U ⟨flagStabilizer 3 K {1}, flagStabilizer 3 K {2},
    fun P hNP hPt => ?_⟩
  rw [hU, normalizer_unitriangular] at hNP
  have hB : upperTriangular 3 K = flagStabilizer 3 K {1, 2} := by
    rw [CFSG.QuasithinUnique.Vol2Native.A312L.upperTriangular_eq_flagStabilizer_full]
    congr 1
    ext i
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  rcases CFSG.Quasithin.H13.L3318.overgroups_three hNP.le with h | h | h | h
  · exact absurd h hPt.ne
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd (h.trans hB.symm) hNP.ne'

open CFSG.Quasithin.MS93.MSP in
theorem gomiTwoOvergroups_sp4 (F : Type) [Field F] [Finite F] [CharP F 2] :
    GomiTwoOvergroups (Sp4 F) := by
  obtain ⟨S, hS⟩ := exists_sylow_sylS (F := F)
  refine GomiTwoOvergroups.of_sylow S ⟨P₁ F, P₂ F, fun P hNP hPt => ?_⟩
  rw [hS, normalizer_sylS] at hNP
  rcases overgroups_borel hNP.le with h | h | h | h
  · exact absurd h hNP.ne'
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h hPt.ne

open CFSG.Quasithin.H13.Lem1227Eq CFSG.Quasithin.H13.A6 in
theorem gomiTwoOvergroups_alt6 : GomiTwoOvergroups Alt6 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hS2, hSi⟩ := isSylowTwoOf_S6
  have hSi' : ¬ 2 ∣ S6.index := by
    rwa [show (S6.subgroupOf ⊤).index = S6.index from Subgroup.relIndex_top_right S6] at hSi
  refine GomiTwoOvergroups.of_sylow (hS2.toSylow hSi') ⟨Q1, Q2, fun P hNP hPt => ?_⟩
  rw [IsPGroup.toSylow_coe, normalizer_S6] at hNP
  set Y : Subgroup (Equiv.Perm (Fin 6)) := P.map (alternatingGroup (Fin 6)).subtype with hY
  have hmemD : ∀ σ ∈ QA6list, σ ∈ Y := fun σ hσ =>
    ⟨⟨σ, Dsub_le_alternating (mem_Dsub.2 hσ)⟩,
      hNP.le (Subgroup.mem_subgroupOf.2 (mem_Dsub.2 hσ)), rfl⟩
  have hcard : Nat.card P = 24 := by
    rcases lattice_S6 P hNP.le with h8 | h24 | htop
    · exact absurd (Subgroup.eq_of_le_of_card_ge hNP.le (by rw [h8, card_S6])) hNP.ne
    · exact h24
    · exact absurd htop hPt.ne
  rcases overgroup_A6 Y (Subgroup.map_subtype_le P) (hmemD _ (by decide +kernel))
      (hmemD _ (by decide +kernel)) (hmemD _ (by decide +kernel)) with h | h | h
  · refine Or.inl (Subgroup.eq_of_le_of_card_ge (fun σ hσ => ?_) (by rw [hcard, card_Q1]))
    rw [Q1, Subgroup.mem_subgroupOf, mem_P1sub]
    exact h _ ⟨σ, hσ, rfl⟩
  · refine Or.inr (Subgroup.eq_of_le_of_card_ge (fun σ hσ => ?_) (by rw [hcard, card_Q2]))
    rw [Q2, Subgroup.mem_subgroupOf, mem_P2sub]
    exact h _ ⟨σ, hσ, rfl⟩
  · refine absurd (eq_top_iff.mpr fun σ _ => ?_) hPt.ne
    have hσ : (σ : Equiv.Perm (Fin 6)) ∈ Y := by rw [h]; exact σ.2
    obtain ⟨p, hp, hpσ⟩ := hσ
    rwa [← Subtype.ext hpσ]

end Models

section Catalog

open TauCeti

theorem nonempty_sl3_two_of_typeA1 {Y : Type} [Group Y] (q : PrimePower) (hq7 : q.card = 7)
    (hv : (LieTypeIndex.A 1 q).Valid) (e : Y ≃* ValidLieTypeIndex.Group ⟨.A 1 q, hv⟩) :
    Nonempty (Y ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  have h := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
  have hq7' : q.p ^ q.exponent = 7 := (PrimePower.card_def q).symm.trans hq7
  have hp7 : q.p = 7 := (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_seven).1
    (hq7' ▸ dvd_pow_self q.p q.exponent_pos.ne')
  rw [hp7] at hq7' h
  have hex : q.exponent = 1 :=
    Nat.pow_right_injective (by norm_num : 2 ≤ 7) (hq7'.trans (pow_one 7).symm)
  rw [hex] at h
  exact CFSG.Open.StatedAPI.nonempty_mulEquiv_sl_three_two_of_psl_two_seven h

theorem exists_sp4_of_typeB2 {Y : Type} [Group Y] (q : PrimePower) (hq2 : q.p = 2)
    (hv : (LieTypeIndex.B 2 q).Valid) (e : Y ≃* ValidLieTypeIndex.Group ⟨.B 2 q, hv⟩) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
      Nonempty (Y ≃* CFSG.Quasithin.MS93.MSP.Sp4 K) := by
  obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
  rw [hq2] at hK
  have hchar : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      q.exponent_pos hK
  exact ⟨K, inferInstance, inferInstance, hchar, ⟨e'.trans
    ((QuotientGroup.quotientMulEquivOfEq
      CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot).trans
      QuotientGroup.quotientBot)⟩⟩

theorem gomiTwoOvergroups_psl3 (K : Type) [Field K] [Finite K] [CharP K 2] :
    GomiTwoOvergroups (Matrix.ProjectiveSpecialLinearGroup (Fin 3) K) :=
  (gomiTwoOvergroups_sl3 K).of_surjective (QuotientGroup.mk'_surjective _)

theorem gomiTwoOvergroups_of_isGomiL3_or_isGomiSp4 {Y : Type} [Group Y]
    (h : IsGomiL3 Y ∨ IsGomiSp4 Y) : GomiTwoOvergroups Y := by
  rcases h with hL3 | hSp4
  · obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := hL3
    rcases hd with ⟨q, hq2, hd⟩ | ⟨q, hq7, hd⟩
    · simp only at hd
      subst hd
      have : Fact q.p.Prime := ⟨q.prime_p⟩
      have : CharP (GaloisField q.p q.exponent) 2 := CharP.congr q.p hq2
      let e' := e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv)
      exact (gomiTwoOvergroups_psl3 _).of_surjective (π := e'.symm.toMonoidHom) e'.symm.surjective
    · simp only at hd
      subst hd
      obtain ⟨e'⟩ := nonempty_sl3_two_of_typeA1 q hq7 hv e
      exact (gomiTwoOvergroups_sl3 (ZMod 2)).of_surjective (π := e'.symm.toMonoidHom)
        e'.symm.surjective
  · rcases hSp4 with hA6 | ⟨⟨d, hv⟩, ⟨q, hq2, hd⟩, ⟨e⟩⟩
    · obtain ⟨e⟩ := hA6
      exact gomiTwoOvergroups_alt6.of_surjective (π := e.symm.toMonoidHom) e.symm.surjective
    · simp only at hd
      subst hd
      obtain ⟨K, _, _, _, ⟨e'⟩⟩ := exists_sp4_of_typeB2 q hq2 hv e
      exact (gomiTwoOvergroups_sp4 K).of_surjective (π := e'.symm.toMonoidHom) e'.symm.surjective

end Catalog

theorem subgroupOf_eq_of_isGomiTwoOver {G : Type} [Group G] {T L P : Subgroup G} (hTL : T ≤ L)
    {X₁ X₂ : Subgroup ↥L} (hX : ∀ P' : Subgroup ↥L,
      Subgroup.normalizer ((T.subgroupOf L : Subgroup ↥L) : Set ↥L) < P' → P' < ⊤ →
        P' = X₁ ∨ P' = X₂)
    (hP : L ⊓ Subgroup.normalizer (T : Set G) < P ∧ P < L) :
    P.subgroupOf L = X₁ ∨ P.subgroupOf L = X₂ := by
  refine hX _ ?_ (lt_top_iff_ne_top.mpr fun htop => hP.2.ne ?_)
  · rw [← Subgroup.subgroupOf_normalizer_eq hTL]
    refine lt_of_le_of_ne (fun x hx => ?_) fun heq => hP.1.not_ge fun y hy => ?_
    · rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact hP.1.le ⟨x.2, hx⟩
    · have hyL : y ∈ L := hP.2.le hy
      have hy' : (⟨y, hyL⟩ : ↥L) ∈ (Subgroup.normalizer (T : Set G)).subgroupOf L := by
        rw [heq, Subgroup.mem_subgroupOf]
        exact hy
      exact ⟨hyL, hy'⟩
  · exact le_antisymm hP.2.le (Subgroup.subgroupOf_eq_top.mp htop)

theorem gomiFact36Overgroups_holds : GomiFact36Overgroups := by
  intro G _ _ T L hT _ hQ P₁ P₂ P₃ hP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL : GomiTwoOvergroups ↥L :=
    (gomiTwoOvergroups_of_isGomiL3_or_isGomiSp4 hQ).of_quotient
      (QuotientGroup.mk'_surjective (Subgroup.center ↥L)) (by rw [QuotientGroup.ker_mk'])
  obtain ⟨hTL, hT2, hTi⟩ := hT
  have hTi' : ¬ 2 ∣ (T.subgroupOf L).index := hTi
  have hT2' : IsPGroup 2 ↥(T.subgroupOf L) := hT2.comap_of_injective L.subtype L.subtype_injective
  obtain ⟨X₁, X₂, hX⟩ := hL (hT2'.toSylow hTi')
  rw [IsPGroup.toSylow_coe] at hX
  have key : ∀ P ∈ [P₁, P₂, P₃], P.subgroupOf L = X₁ ∨ P.subgroupOf L = X₂ :=
    fun P hPm => subgroupOf_eq_of_isGomiTwoOver hTL hX (hP P hPm)
  have hinj : ∀ {A B : Subgroup G}, A ∈ [P₁, P₂, P₃] → B ∈ [P₁, P₂, P₃] →
      A.subgroupOf L = B.subgroupOf L → A = B := fun hA hB h => by
    rwa [Subgroup.subgroupOf_inj, inf_of_le_left (hP _ hA).2.le,
      inf_of_le_left (hP _ hB).2.le] at h
  have m1 : P₁ ∈ [P₁, P₂, P₃] := by simp
  have m2 : P₂ ∈ [P₁, P₂, P₃] := by simp
  have m3 : P₃ ∈ [P₁, P₂, P₃] := by simp
  rcases key _ m1 with h1 | h1 <;> rcases key _ m2 with h2 | h2 <;>
    rcases key _ m3 with h3 | h3
  all_goals first
    | exact Or.inl (hinj m1 m2 (h1.trans h2.symm))
    | exact Or.inr (Or.inl (hinj m1 m3 (h1.trans h3.symm)))
    | exact Or.inr (Or.inr (hinj m2 m3 (h2.trans h3.symm)))

end CFSG.GroupTheory

end
