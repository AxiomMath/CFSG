module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface2
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

variable {G : Type} [Group G] [Finite G]

theorem exists_isMaxBInvariantTwo (B U : Subgroup G) (hU : IsPGroup 2 U)
    (hBU : B ≤ Subgroup.normalizer (U : Set G)) :
    ∃ T : Subgroup G, IsMaxBInvariantTwo B T ∧ U ≤ T := by
  classical
  let S : Set (Subgroup G) := {T | IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧ U ≤ T}
  have hne : S.Nonempty := ⟨U, hU, hBU, le_rfl⟩
  obtain ⟨T, hTS, hTmax⟩ := (Set.toFinite S).exists_maximalFor id S hne
  refine ⟨T, ⟨hTS.1, hTS.2.1, fun T' h2 hB hle => ?_⟩, hTS.2.2⟩
  exact le_antisymm (hTmax ⟨h2, hB, hTS.2.2.trans hle⟩ hle) hle

omit [Finite G] in
theorem mem_centerOf_iff' {P : Subgroup G} {z : G} :
    z ∈ centerOf P ↔ z ∈ P ∧ ∀ y ∈ P, z * y = y * z := by
  constructor
  · rintro ⟨z', hz', rfl⟩
    refine ⟨z'.2, fun y hy => ?_⟩
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.1 hz') ⟨y, hy⟩).symm
  · rintro ⟨hz, hc⟩
    refine ⟨⟨z, hz⟩, Subgroup.mem_center_iff.2 fun g => ?_, rfl⟩
    exact Subtype.ext (hc g g.2).symm

theorem jOf_le (T : Subgroup G) : jOf T ≤ T := iSup₂_le fun _ hE => hE.1

theorem jOneOf_le (T : Subgroup G) : jOneOf T ≤ T := iSup₂_le fun _ hE => hE.1

omit [Finite G] in
theorem omegaOneZ_le (X : Subgroup G) : omegaOneZ X ≤ X :=
  (Subgroup.closure_le X).2 fun _ hx => (mem_centerOf_iff'.1 hx.1).1

theorem omegaOneZ_jOneOf_le (T : Subgroup G) : omegaOneZ (jOneOf T) ≤ T :=
  (omegaOneZ_le _).trans (jOneOf_le T)

theorem tripleOf_zero (T : Subgroup G) : tripleOf T 0 = jOf T := rfl

theorem tripleOf_one (T : Subgroup G) : tripleOf T 1 = omegaOneZ (jOneOf T) := rfl

theorem tripleOf_two (T : Subgroup G) : tripleOf T 2 = omegaOneZ T := rfl

theorem fin_three_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  revert i; decide

theorem tripleOf_le (T : Subgroup G) (i : Fin 3) : tripleOf T i ≤ T := by
  rcases fin_three_cases i with rfl | rfl | rfl
  · rw [tripleOf_zero]; exact jOf_le T
  · rw [tripleOf_one]; exact omegaOneZ_jOneOf_le T
  · rw [tripleOf_two]; exact omegaOneZ_le T

theorem tripleOf_isPGroup {T : Subgroup G} (hT : IsPGroup 2 T) (i : Fin 3) :
    IsPGroup 2 (tripleOf T i) :=
  hT.to_le (tripleOf_le T i)

theorem exists_orderOf_eq_two_mem {T : Subgroup G} (hT : IsPGroup 2 T) (hne : T ≠ ⊥) :
    ∃ x ∈ T, orderOf x = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hT.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hne (Subgroup.card_eq_one.1 (by simpa using hn))
  have hdvd : 2 ∣ Nat.card T := by
    rw [hn]; exact dvd_pow_self 2 hn0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := T) 2 hdvd
  refine ⟨x, x.2, ?_⟩
  rw [← hx]
  exact Subgroup.orderOf_coe x

omit [Finite G] in
theorem isElemAbelian_zpowers_of_orderOf_eq_two {x : G} (hx : orderOf x = 2) :
    IsElemAbelian 2 (Subgroup.zpowers x) := by
  refine ⟨inferInstance, fun y hy => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hx, pow_orderOf_eq_one,
    one_zpow]

theorem exists_elemAbelian_ne_bot {T : Subgroup G} (hT : IsPGroup 2 T) (hne : T ≠ ⊥) :
    ∃ E : Subgroup G, E ≤ T ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ CFSG.Open.pRank 2 T ∧ E ≠ ⊥ := by
  obtain ⟨x, hxT, hx2⟩ := exists_orderOf_eq_two_mem hT hne
  have h1 : 1 ≤ CFSG.Open.pRank 2 T := by
    refine CFSG.SectionRank.le_pRank Nat.one_lt_two (E := Subgroup.zpowers x)
      ((Subgroup.zpowers_le).2 hxT) (isElemAbelian_zpowers_of_orderOf_eq_two hx2) (k := 1) ?_
    rw [Nat.card_zpowers, hx2]; rfl
  obtain ⟨E, hET, hE, hcard⟩ := CFSG.SectionRank.exists_pRank Nat.one_lt_two T
  refine ⟨E, hET, hE, hcard, fun hbot => ?_⟩
  rw [hbot, Subgroup.card_bot] at hcard
  have : 2 ^ 1 ≤ 2 ^ CFSG.Open.pRank 2 T := Nat.pow_le_pow_right (by norm_num) h1
  omega

theorem jOf_ne_bot {T : Subgroup G} (hT : IsPGroup 2 T) (hne : T ≠ ⊥) : jOf T ≠ ⊥ := by
  obtain ⟨E, hET, hE, hcard, hEne⟩ := exists_elemAbelian_ne_bot hT hne
  intro hbot
  exact hEne (le_bot_iff.1 (hbot ▸ le_iSup₂_of_le E ⟨hET, hE, hcard⟩ le_rfl))

theorem jOneOf_ne_bot {T : Subgroup G} (hT : IsPGroup 2 T) (hne : T ≠ ⊥) :
    jOneOf T ≠ ⊥ := by
  obtain ⟨E, hET, hE, hcard, hEne⟩ := exists_elemAbelian_ne_bot hT hne
  intro hbot
  refine hEne (le_bot_iff.1 (hbot ▸ le_iSup₂_of_le E ⟨hET, hE, ?_⟩ le_rfl))
  rw [hcard]
  exact Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)

theorem omegaOneZ_ne_bot {X : Subgroup G} (hX : IsPGroup 2 X) (hne : X ≠ ⊥) :
    omegaOneZ X ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial ↥X := (Subgroup.nontrivial_iff_ne_bot X).2 hne
  have := hX.center_nontrivial
  have hZ2 : IsPGroup 2 ↥(Subgroup.center ↥X) := hX.to_subgroup _
  have hZne : Subgroup.center ↥X ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot _).1 inferInstance
  obtain ⟨z, hzZ, hz2⟩ := exists_orderOf_eq_two_mem hZ2 hZne
  intro hbot
  have hzc : (z : G) ∈ centerOf X := ⟨z, hzZ, rfl⟩
  have hz2' : (z : G) ^ 2 = 1 := by
    have : z ^ 2 = 1 := by rw [← hz2]; exact pow_orderOf_eq_one z
    simpa using congrArg Subtype.val this
  have hz1 : (z : G) ≠ 1 := by
    intro h1
    have : z = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hz2
    omega
  have hmem : (z : G) ∈ omegaOneZ X := Subgroup.subset_closure ⟨hzc, hz2'⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hz1 hmem

theorem tripleOf_ne_bot {T : Subgroup G} (hT : IsPGroup 2 T) (hne : T ≠ ⊥) (i : Fin 3) :
    tripleOf T i ≠ ⊥ := by
  rcases fin_three_cases i with rfl | rfl | rfl
  · rw [tripleOf_zero]; exact jOf_ne_bot hT hne
  · rw [tripleOf_one]; exact omegaOneZ_ne_bot (hT.to_le (jOneOf_le T)) (jOneOf_ne_bot hT hne)
  · rw [tripleOf_two]; exact omegaOneZ_ne_bot hT hne

omit [Finite G] in
theorem mem_normalizer_of_conj_mem {Y : Subgroup G} {g : G} (h1 : ∀ x ∈ Y, g * x * g⁻¹ ∈ Y)
    (h2 : ∀ x ∈ Y, g⁻¹ * x * g ∈ Y) : g ∈ Subgroup.normalizer (Y : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h1 x, fun hx => ?_⟩
  have := h2 _ hx
  simpa [mul_assoc] using this

theorem conj_mem_jOf {T : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (T : Set G)) {x : G}
    (hx : x ∈ jOf T) : g * x * g⁻¹ ∈ jOf T := by
  have h : (jOf T).map (MulAut.conj g).toMonoidHom ≤ jOf T := by
    rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun E hE => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    refine le_iSup₂_of_le (E.map (MulAut.conj g).toMonoidHom) ⟨?_, ?_, ?_⟩ le_rfl
    · rintro _ ⟨e, he, rfl⟩
      simpa [MulAut.conj_apply] using (Subgroup.mem_normalizer_iff.1 hg e).1 (hE.1 he)
    · exact CFSG.SectionRank.isElemAbelian_map hE.2.1 _
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]; exact hE.2.2
  simpa [MulAut.conj_apply] using h ⟨x, hx, rfl⟩

theorem conj_mem_jOneOf {T : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (T : Set G)) {x : G}
    (hx : x ∈ jOneOf T) : g * x * g⁻¹ ∈ jOneOf T := by
  have h : (jOneOf T).map (MulAut.conj g).toMonoidHom ≤ jOneOf T := by
    rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun E hE => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    refine le_iSup₂_of_le (E.map (MulAut.conj g).toMonoidHom) ⟨?_, ?_, ?_⟩ le_rfl
    · rintro _ ⟨e, he, rfl⟩
      simpa [MulAut.conj_apply] using (Subgroup.mem_normalizer_iff.1 hg e).1 (hE.1 he)
    · exact CFSG.SectionRank.isElemAbelian_map hE.2.1 _
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]; exact hE.2.2
  simpa [MulAut.conj_apply] using h ⟨x, hx, rfl⟩

omit [Finite G] in
theorem conj_mem_omegaOneZ {X : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (X : Set G))
    {x : G} (hx : x ∈ omegaOneZ X) : g * x * g⁻¹ ∈ omegaOneZ X := by
  have hg' : g⁻¹ ∈ Subgroup.normalizer (X : Set G) := inv_mem hg
  refine Subgroup.closure_induction (p := fun x _ => g * x * g⁻¹ ∈ omegaOneZ X) ?_ ?_ ?_ ?_ hx
  · rintro s ⟨hs, hs2⟩
    refine Subgroup.subset_closure ⟨?_, ?_⟩
    · obtain ⟨hsX, hsc⟩ := mem_centerOf_iff'.1 hs
      refine mem_centerOf_iff'.2 ⟨(Subgroup.mem_normalizer_iff.1 hg s).1 hsX, fun y hy => ?_⟩
      have hy' : g⁻¹ * y * g ∈ X := by
        simpa [mul_assoc] using (Subgroup.mem_normalizer_iff.1 hg' y).1 hy
      have := hsc _ hy'
      calc g * s * g⁻¹ * y = g * (s * (g⁻¹ * y * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * y * g) * s) * g⁻¹ := by rw [this]
        _ = y * (g * s * g⁻¹) := by group
    · rw [conj_pow, hs2]; group
  · simp [omegaOneZ]
  · intro a b _ _ ha hb
    have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [this]; exact mul_mem ha hb
  · intro a _ ha
    have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [this]; exact inv_mem ha

theorem normalizer_le_normalizer_tripleOf (T : Subgroup G) (i : Fin 3) :
    Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (tripleOf T i : Set G) := by
  intro g hg
  have hg' : g⁻¹ ∈ Subgroup.normalizer (T : Set G) := inv_mem hg
  rcases fin_three_cases i with rfl | rfl | rfl
  · rw [tripleOf_zero]
    exact mem_normalizer_of_conj_mem (fun x hx => conj_mem_jOf hg hx)
      (fun x hx => by simpa using conj_mem_jOf hg' hx)
  · rw [tripleOf_one]
    have hJ : ∀ {g : G}, g ∈ Subgroup.normalizer (T : Set G) →
        g ∈ Subgroup.normalizer (jOneOf T : Set G) := fun {g} hg =>
      mem_normalizer_of_conj_mem (fun x hx => conj_mem_jOneOf hg hx)
        (fun x hx => by simpa using conj_mem_jOneOf (inv_mem hg) hx)
    exact mem_normalizer_of_conj_mem (fun x hx => conj_mem_omegaOneZ (hJ hg) hx)
      (fun x hx => by simpa using conj_mem_omegaOneZ (hJ hg') hx)
  · rw [tripleOf_two]
    exact mem_normalizer_of_conj_mem (fun x hx => conj_mem_omegaOneZ hg hx)
      (fun x hx => by simpa using conj_mem_omegaOneZ hg' hx)

theorem le_normalizer_tripleOf {B T : Subgroup G} (hBT : B ≤ Subgroup.normalizer (T : Set G))
    (i : Fin 3) : B ≤ Subgroup.normalizer (tripleOf T i : Set G) :=
  hBT.trans (normalizer_le_normalizer_tripleOf T i)

theorem exists_mem_inter_of_card (s₁ s₂ : Finset (Fin 3)) (h₁ : 2 ≤ s₁.card) (h₂ : 2 ≤ s₂.card) :
    ∃ i, i ∈ s₁ ∧ i ∈ s₂ := by
  by_contra hno
  push Not at hno
  have hd : Disjoint s₁ s₂ := Finset.disjoint_left.2 fun i h1 h2 => hno i h1 h2
  have := Finset.card_union_of_disjoint hd
  have h3 : (s₁ ∪ s₂).card ≤ 3 := by
    simpa using Finset.card_le_univ (s₁ ∪ s₂)
  omega

theorem exists_common_cover (hS : GLStanding G 4 3) {B : Subgroup G}
    (hB : IsBOneMax 3 B) (h710 : Lemma710Stmt B) {K₁ K₂ : Subgroup G} (hK₁ : IsHSet B K₁)
    (hK₂ : IsHSet B K₂) :
    ∃ N : Subgroup G, N ≠ ⊤ ∧ B ≤ N ∧ Covers3 N K₁ ∧ Covers3 N K₂ := by
  have := hS.simple
  obtain ⟨U, hU0, hU2, hBU⟩ := hB.1.2.2
  obtain ⟨T, hT, hUT⟩ := exists_isMaxBInvariantTwo B U hU2 hBU
  have hTne : T ≠ ⊥ := fun h => hU0 (le_bot_iff.1 (h ▸ hUT))
  obtain ⟨s₁, hs₁, hc₁⟩ := h710 T hT K₁ hK₁
  obtain ⟨s₂, hs₂, hc₂⟩ := h710 T hT K₂ hK₂
  obtain ⟨i, hi₁, hi₂⟩ := exists_mem_inter_of_card s₁ s₂ hs₁ hs₂
  refine ⟨Subgroup.normalizer (tripleOf T i : Set G), ?_, le_normalizer_tripleOf hT.2.1 i,
    hc₁ i hi₁, hc₂ i hi₂⟩
  exact normalizer_ne_top_of_isPGroup_two hS.nonabelian (tripleOf_ne_bot hT.1 hTne i)
    (tripleOf_isPGroup hT.1 i)

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7
