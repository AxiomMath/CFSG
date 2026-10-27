module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotCTFieldInputs
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotEnd

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.EvenSmallLie
open CFSG.LieType.CurtisTits (IsCompatible)
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.LieType.Chevalley.E6GraphLevi (realize unitarySL unitaryTwist)
open CFSG.SeitzReduction.E6Pilot (adjDatumE6 scFamily leviIsogeny)

local instance twistedE6PilotCTFieldNeZero : NeZero TwistTag.E6.tag.rank := ⟨by decide⟩

local instance twistedE6PilotCTFieldNeZeroE6 : NeZero Tag.E6.rank := ⟨by decide⟩

local instance twistedE6PilotCTFieldNeZeroF4 : NeZero Tag.F4.rank := ⟨by decide⟩

section CT


variable {K : Type} [Field K] [Finite K] {G : Type} [Group G]

theorem exists_surjective_iSup_range_of_isCompatible_adj
    (φ : ∀ J, (adjDatumE6 K).leviAmalgam J →* G)
    (hφ : IsCompatible (adjDatumE6 K).leviAmalgam φ) (hnt : ∃ J, ∃ x, φ J x ≠ 1)
    {G₀ : Subgroup G} (hG₀ : ⨆ J, (φ J).range = G₀) :
    ∃ ψ : e6Data_valid.minGroup K →* G₀,
      Function.Surjective ψ ∧ ψ.ker ≤ center (e6Data_valid.minGroup K) ∧
      CFSG.IsQuasisimple G₀ ∧ center G₀ = (center (e6Data_valid.minGroup K)).map ψ ∧
      ∀ J (y : (e6Datum K).leviAmalgam J), ((ψ y : G₀) : G) = φ J (leviIsogeny J.1 y) := by
  subst hG₀
  have hle : ∀ J y, scFamily φ J y ∈ (⨆ J, (φ J).range : Subgroup G) := fun J y =>
    le_iSup (fun J => (φ J).range) J ⟨_, rfl⟩
  let φ' : ∀ J, (e6Datum K).leviAmalgam J →* (⨆ J, (φ J).range : Subgroup G) :=
    fun J => (scFamily φ J).codRestrict _ (hle J)
  have hφsc := E6Pilot.isCompatible_scFamily hφ
  have hφ' : IsCompatible (e6Datum K).leviAmalgam φ' := fun i j hij x y hxy =>
    Subtype.ext (hφsc i j hij x y hxy)
  have hgen' : ⨆ J, (φ' J).range = ⊤ := by
    apply Subgroup.map_injective (⨆ J, (φ J).range : Subgroup G).subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    refine iSup_congr fun J => ?_
    rw [← MonoidHom.range_comp]
    exact E6Pilot.range_scFamily φ J
  have hnt' : ∃ J, ∃ x, φ' J x ≠ 1 := by
    obtain ⟨J, x, hx⟩ := hnt
    obtain ⟨y, rfl⟩ := E6Pilot.leviIsogeny_surjective (K := K) J.1 x
    exact ⟨J, y, fun h => hx (congrArg Subtype.val h)⟩
  obtain ⟨ψ, hψ, hsurj, hker, hq, hZ⟩ :=
    E6Pilot.exists_surjective_of_isCompatible_e6 K φ' hφ' hgen' hnt'
  exact ⟨ψ, hsurj, hker, hq, hZ, fun J y => congrArg Subtype.val (hψ J y)⟩

end CT

theorem mem_normalizer_sup_2E6 {M : Type*} [Group M] {A B : Subgroup M} {t : M}
    (hA : t ∈ normalizer (A : Set M)) (hB : t ∈ normalizer (B : Set M)) :
    t ∈ normalizer ((A ⊔ B : Subgroup M) : Set M) := by
  have h := F4Pilot.mem_normalizer_iSup (H := fun b : Bool => cond b A B) (t := t)
    (fun b => by cases b <;> assumption)
  rwa [iSup_bool_eq] at h

section Adjacent

variable
  {K : Type} [Field K] [CharP K 2] {G : Type} [Group G]

abbrev e6Path (t : Fin 5) : Fin Tag.E6.rank := E6GraphLevi.pathIdx t

theorem one_ne_e6Path : ∀ t : Fin 5, (1 : Fin Tag.E6.rank) ≠ e6Path t := by
  intro t
  fin_cases t <;> decide

theorem exists_fieldFamily2E6_adjacent (h2 : (2 : K) = 0)
    (Φ : Matrix.SpecialLinearGroup (Fin 6) K →* G) (ΦY : subsystemGroup TwistTag.E6.tag K setD →* G)
    (hc : ∀ (m : Fin Tag.E6.rank) (hm : m ∈ ({0, 2, 4, 5} : Finset (Fin Tag.E6.rank))) (a b),
      Commute (yFam ΦY {1} one_mem_setD a) (xFam h2 Φ {m} (not_one_mem_singleton hm) (by simp) b))
    {B : Matrix.SpecialLinearGroup (Fin 6) K} (hB : B ∈ E6GraphLevi.adjacentSet K) :
    ∃ (J : {J : Finset (Fin (adjDatumE6 K).rank) // J.card ≤ 2})
      (x : (adjDatumE6 K).leviAmalgam J),
      fieldFamily2E6 h2 Φ ΦY hc J x = Φ B ∧
        (((x : adjointGroup .E6 K) : ModGL .E6 K) : ModGL TwistTag.E6.tag K) = realize h2 B := by
  obtain ⟨t, c, rfl | rfl⟩ := hB
  · have h1 : (1 : Fin Tag.E6.rank) ∉ ({e6Path t} : Finset (Fin Tag.E6.rank)) :=
      fun h => one_ne_e6Path t (Finset.mem_singleton.1 h)
    refine ⟨⟨{e6Path t}, by simp⟩, ⟨_, E6Pilot.xElement_mem_levi_adjDatumE6 (e6Path t) c⟩,
      ?_, (E6GraphLevi.realize_x h2 t c).symm⟩
    rw [fieldFamily2E6_of_not_mem h1]
    exact congrArg Φ (xSection_singleton_xUnit h2 t h1 (by simp) c _)
  · have h1 : (1 : Fin Tag.E6.rank) ∉ ({e6Path t} : Finset (Fin Tag.E6.rank)) :=
      fun h => one_ne_e6Path t (Finset.mem_singleton.1 h)
    refine ⟨⟨{e6Path t}, by simp⟩, ⟨_, E6Pilot.yElement_mem_levi_adjDatumE6 (e6Path t) c⟩,
      ?_, (E6GraphLevi.realize_y h2 t c).symm⟩
    rw [fieldFamily2E6_of_not_mem h1]
    exact congrArg Φ (xSection_singleton_yUnit h2 t h1 (by simp) c _)

end Adjacent

section Model


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {k K : Type} [Field k]
  [Field K] [Algebra k K]

theorem exists_fieldRowModel_2E6 (hf2 : 2 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {e : L ≃* graphFixedRootGroup TwistTag.E6 K σ} {t : G} (htL : t ∈ centralizer (L : Set G))
    (hX : FieldCoverParamX σ (E6GraphLevi.two_eq_zero_of_card_sq (by omega) hK) e t
      (modelToG e (neighbourTorus K (Units.map (algebraMap k K).toMonoidHom).range .X)))
    (hY : FieldNeighbourIso2E6 e t
      (modelToG e (neighbourTorus K (Units.map (algebraMap k K).toMonoidHom).range .Y))
      (subsystemGroup TwistTag.E6.tag K setD) (d4LeviTwist (apply_apply_eq hK hσ))
      (omegaMinusLevi σ)) :
    ∃ G₀ : Subgroup G, FieldRowModel2E6 e t (Units.map (algebraMap k K).toMonoidHom).range G₀ := by
  have hf : 1 ≤ f := by omega
  have : Finite k := F4Pilot.finite_of_natCard_eq_two_pow hk
  have := finite_of_card hK
  have : CharP K 2 := charP_two_of_card hf hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  obtain ⟨hA3, hAo, hAσ, hkσ⟩ := unitsRange_facts hf2 hk hσ
  obtain ⟨c₀, hc₀A, hc₀⟩ := F4Pilot.exists_mem_orderOf_eq_natCard hA3
  have ht₀ : c₀ ^ 2 ≠ 1 := (F4Pilot.ne_one_and_sq_ne_one_of_three_le_orderOf (hc₀ ▸ hA3)).2
  obtain ⟨hY', hc, htw⟩ := exists_fieldFamily_inputs_2E6 hf2 hk hK hσ htL hX hY
  let h2 : (2 : K) = 0 := E6GraphLevi.two_eq_zero_of_card_sq hf hK
  let ΦY : subsystemGroup TwistTag.E6.tag K setD →* G :=
    (centralizerPerfectCore _).subtype.comp hY'.Φ.toMonoidHom
  let φ := fieldFamily2E6 h2 hX.Φ ΦY hc
  have hcompat : IsCompatible (adjDatumE6 K).leviAmalgam φ := isCompatible_fieldFamily2E6 ht₀ htw
  have hnt : ∃ J, ∃ x, φ J x ≠ 1 := by
    have hB₀ : Matrix.SpecialLinearGroup.transvection (E6GraphLevi.castSucc_ne_succ 0) (1 : K) ∈
        E6GraphLevi.adjacentSet K := ⟨0, 1, Or.inl rfl⟩
    have h01 : ((Matrix.SpecialLinearGroup.transvection (E6GraphLevi.castSucc_ne_succ 0) (1 : K) :
        Matrix.SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) 0 1 = 1 := by
      simp only [Matrix.SpecialLinearGroup.transvection_coe]
      have e1 : (Fin.castSucc (0 : Fin 5) : Fin 6) = 0 := rfl
      have e2 : (Fin.succ (0 : Fin 5) : Fin 6) = 1 := rfl
      rw [e1, e2, Matrix.add_apply, Matrix.single_apply_same, Matrix.one_apply_ne (by decide),
        zero_add]
    obtain ⟨J, x, hJx, -⟩ := exists_fieldFamily2E6_adjacent h2 hX.Φ ΦY hc hB₀
    refine ⟨J, x, fun h => ?_⟩
    rw [hJx] at h
    have hBc := hX.ker_le (MonoidHom.mem_ker.2 h)
    obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hBc
    have h3 := congrArg (fun A : Matrix (Fin 6) (Fin 6) K => A 0 1) hr
    change (Matrix.scalar (Fin 6) r) 0 1 = _ at h3
    rw [h01, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ (by decide)] at h3
    exact zero_ne_one h3
  let G₀ : Subgroup G := ⨆ J, (φ J).range
  obtain ⟨ψ, hsurj, hker, hqs, hZ, hψφ⟩ :=
    exists_surjective_iSup_range_of_isCompatible_adj φ hcompat hnt (G₀ := G₀) rfl
  have hφG₀ : ∀ J x, φ J x ∈ G₀ := fun J x => le_iSup (fun J => (φ J).range) J ⟨x, rfl⟩
  have hXG₀ : ∀ B, hX.Φ B ∈ G₀ := by
    have hle : (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 6) K)) ≤ G₀.comap hX.Φ := by
      rw [← E6GraphLevi.closure_adjacentSet, Subgroup.closure_le]
      intro B hB
      obtain ⟨J, x, hJx, -⟩ := exists_fieldFamily2E6_adjacent h2 hX.Φ ΦY hc hB
      change hX.Φ B ∈ G₀
      rw [← hJx]
      exact hφG₀ J x
    exact fun B => hle (mem_top B)
  have hEX : neighbourCore e (Units.map (algebraMap k K).toMonoidHom).range .X ≤ G₀ := by
    rw [neighbourCore_def, ← hX.range_eq]
    rintro _ ⟨B, rfl⟩
    exact hXG₀ B
  have hYpiece : ∀ {I : Finset (Fin Tag.F4.rank)}, I.card ≤ 2 → I ⊆ {0, 1, 2} →
      pieceCore e (Units.map (algebraMap k K).toMonoidHom).range I =
        (((relLevi K I).subgroupOf (subsystemGroup TwistTag.E6.tag K setD)).map
          hY'.Φ.toMonoidHom).map (centralizerPerfectCore _).subtype := by
    intro I hI hIY
    exact hY'.pieceCore_eq_map_relLevi_Y' hf hK hσ htL hA3 hAσ hAo
      (fun c hc => by
        have h1 := pow_card_eq_one'
          (x := (⟨c, hc⟩ : (Units.map (algebraMap k K).toMonoidHom).range))
        exact congrArg Subtype.val h1) hI hIY
      (modelToG_mono e (neighbourTorus_le_relLeviTorus _ .Y (hIY.trans (by decide))))
  have hYG₀ : ∀ y : subsystemGroup TwistTag.E6.tag K setD, ΦY y ∈ G₀ := by
    have hle : subsystemGroup TwistTag.E6.tag K setD ≤
        (G₀.comap ΦY).map (subsystemGroup TwistTag.E6.tag K setD).subtype := by
      refine (Subgroup.closure_le _).2 ?_
      rintro g ⟨i, hi, c, hg⟩
      have hgS : g ∈ subsystemGroup TwistTag.E6.tag K setD :=
        Subgroup.subset_closure ⟨i, hi, c, hg⟩
      refine ⟨⟨g, hgS⟩, ?_, rfl⟩
      change ΦY ⟨g, hgS⟩ ∈ G₀
      have hi' : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := hi
      rcases hi' with rfl | hi'
      ·
        have h1 : (1 : Fin Tag.E6.rank) ∈ ({1} : Finset (Fin Tag.E6.rank)) :=
          Finset.mem_singleton_self _
        have hn : ¬∃ m ∈ ({1} : Finset (Fin Tag.E6.rank)), m ≠ 1 ∧ m ≠ 3 :=
          fun ⟨m, hm, hm1, _⟩ => hm1 (Finset.mem_singleton.1 hm)
        have hgA : g ∈ adjointGroup .E6 K := by
          rcases hg with rfl | rfl
          exacts [xUnit_mem_adjointGroup _ c, yUnit_mem_adjointGroup _ c]
        have hgL : (⟨g, hgA⟩ : adjointGroup .E6 K) ∈
            CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {1} := by
          rcases hg with rfl | rfl
          exacts [E6Pilot.xElement_mem_levi_adjDatumE6 1 c,
            E6Pilot.yElement_mem_levi_adjDatumE6 1 c]
        have e1 := fieldFamily2E6_of_Y (h2 := h2) (Φ := hX.Φ) (ΦY := ΦY) (hc := hc)
          (J := ⟨{1}, by simp⟩) h1 hn ⟨_, hgL⟩
        have e2 : yFam ΦY {1} (mem_setD_of_not_exists hn) ⟨_, hgL⟩ = ΦY ⟨g, hgS⟩ := rfl
        rw [← e2, ← e1]
        exact hφG₀ _ _
      ·
        have hr : e6IndexToF4 i = 1 ∨ e6IndexToF4 i = 2 := by
          have key : ∀ i : Fin Tag.E6.rank, (i = 2 ∨ i = 3 ∨ i = 4) →
              e6IndexToF4 i = 1 ∨ e6IndexToF4 i = 2 := by decide
          exact key i hi'
        have hgrel : g ∈ relLevi K {e6IndexToF4 i} := by
          rw [relLevi, ← F4Pilot.closure_xUnit_yUnit_eq_rootSpan]
          exact Subgroup.subset_closure ⟨i, mem_relNodeSet.2 (Finset.mem_singleton_self _), c, hg⟩
        have hI : ({e6IndexToF4 i} : Finset (Fin Tag.F4.rank)) ⊆ {0, 1, 2} := by
          rcases hr with h | h <;> rw [h] <;> decide
        have hIX : ({e6IndexToF4 i} : Finset (Fin Tag.F4.rank)) ⊆
            F4Pilot.AmalgamNeighbour.X.nodes := by
          rcases hr with h | h <;> rw [h] <;> decide
        have hmem : ΦY ⟨g, hgS⟩ ∈ pieceCore e (Units.map (algebraMap k K).toMonoidHom).range
            {e6IndexToF4 i} := by
          rw [hYpiece (by simp) hI]
          exact ⟨_, ⟨_, mem_subgroupOf.2 hgrel, rfl⟩, rfl⟩
        exact hEX (pieceCore_le_neighbourCore e _ .X hIX hmem)
    intro y
    obtain ⟨y', hy', hyy'⟩ := hle y.2
    have : y' = y := Subtype.ext hyy'
    rw [← this]
    exact hy'
  have hEY : neighbourCore e (Units.map (algebraMap k K).toMonoidHom).range .Y ≤ G₀ := by
    intro z hz
    obtain ⟨y, hy⟩ := hY'.Φ.surjective ⟨z, hz⟩
    have h := hYG₀ y
    change ((hY'.Φ y : centralizerPerfectCore _) : G) ∈ G₀ at h
    rw [hy] at h
    exact h
  have hΦX : ∀ B, hX.Φ B ∈ neighbourCore e (Units.map (algebraMap k K).toMonoidHom).range .X :=
    fun B => by
      rw [neighbourCore_def, ← hX.range_eq]
      exact ⟨B, rfl⟩
  have hΦY : ∀ y, ΦY y ∈ neighbourCore e (Units.map (algebraMap k K).toMonoidHom).range .Y :=
    fun y => (hY'.Φ y).2
  have hG₀le : G₀ ≤ neighbourCore e (Units.map (algebraMap k K).toMonoidHom).range .X ⊔
      neighbourCore e (Units.map (algebraMap k K).toMonoidHom).range .Y := by
    refine iSup_le fun J => ?_
    rintro _ ⟨x, rfl⟩
    by_cases h1 : (1 : Fin Tag.E6.rank) ∈ J.1
    · by_cases hm : ∃ m ∈ J.1, m ≠ 1 ∧ m ≠ 3
      · change fieldFamily2E6 h2 hX.Φ ΦY hc J x ∈ _
        rw [fieldFamily2E6_of_pair h1 hm]
        have hmem : pairFam h2 hX.Φ ΦY (mem_of_exists_other hm) (hc _ (mem_of_exists_other hm))
            ⟨x, levi_le_pair_of_exists J.2 h1 hm x.2⟩ ∈
              (pairFam h2 hX.Φ ΦY (mem_of_exists_other hm) (hc _ (mem_of_exists_other hm))).range :=
          ⟨_, rfl⟩
        rw [pairFam, F4Pilot.range_supLift] at hmem
        have hs : (yFam ΦY {1} one_mem_setD).range ⊔
            (xFam h2 hX.Φ {hm.choose} (not_one_mem_singleton (mem_of_exists_other hm))
              (by simp)).range ≤
            neighbourCore e (Units.map (algebraMap k K).toMonoidHom).range .X ⊔
              neighbourCore e (Units.map (algebraMap k K).toMonoidHom).range .Y := by
          refine sup_le ?_ ?_
          · rintro _ ⟨a, rfl⟩
            exact mem_sup_right (hΦY _)
          · rintro _ ⟨b, rfl⟩
            exact mem_sup_left (hΦX _)
        exact hs hmem
      · change fieldFamily2E6 h2 hX.Φ ΦY hc J x ∈ _
        rw [fieldFamily2E6_of_Y h1 hm]
        exact mem_sup_right (hΦY _)
    · change fieldFamily2E6 h2 hX.Φ ΦY hc J x ∈ _
      rw [fieldFamily2E6_of_not_mem h1]
      exact mem_sup_left (hΦX _)
  have hG₀eq : G₀ = neighbourCore e (Units.map (algebraMap k K).toMonoidHom).range .X ⊔
      neighbourCore e (Units.map (algebraMap k K).toMonoidHom).range .Y :=
    le_antisymm hG₀le (sup_le hEX hEY)
  have htN : t ∈ normalizer (G₀ : Set G) := by
    rw [hG₀eq]
    exact mem_normalizer_sup_2E6 (le_normalizer_neighbourCore e _ htL .X)
      (le_normalizer_neighbourCore e _ htL .Y)
  let Ψ : adjointGroup .E6 K ≃* G₀ ⧸ center G₀ :=
    (E6Pilot.centerQuotientIsogenyEquiv (K := K)).symm.trans
      (E6Pilot.centerQuotientMulEquiv ψ hsurj hker hZ)
  have hΨθ : ∀ s, Ψ (e6Isogeny K s) = QuotientGroup.mk (ψ s) := by
    intro s
    change (E6Pilot.centerQuotientMulEquiv ψ hsurj hker hZ)
      ((E6Pilot.centerQuotientIsogenyEquiv (K := K)).symm (e6Isogeny K s)) = _
    rw [← E6Pilot.centerQuotientIsogenyEquiv_mk, MulEquiv.symm_apply_apply,
      E6Pilot.centerQuotientMulEquiv_mk]
  have hΨφ : ∀ J (x : (adjDatumE6 K).leviAmalgam J),
      Ψ x = QuotientGroup.mk ⟨φ J x, hφG₀ J x⟩ := by
    intro J x
    obtain ⟨y, rfl⟩ := E6Pilot.leviIsogeny_surjective (K := K) J.1 x
    rw [E6Pilot.coe_leviIsogeny, hΨθ]
    congr 1
    exact Subtype.ext (hψφ J y)
  have hrealA : ∀ B, realize h2 B ∈ adjointGroup .E6 K := fun B =>
    subsystemGroup_le_adjointGroup_E6 _ (by rw [← E6GraphLevi.range_realize h2]; exact ⟨B, rfl⟩)
  have hKL : ∀ B, Ψ ⟨realize h2 B, hrealA B⟩ = QuotientGroup.mk ⟨hX.Φ B, hXG₀ B⟩ := by
    let f₁ : Matrix.SpecialLinearGroup (Fin 6) K →* G₀ ⧸ center G₀ :=
      Ψ.toMonoidHom.comp ((realize h2).codRestrict _ hrealA)
    let f₂ : Matrix.SpecialLinearGroup (Fin 6) K →* G₀ ⧸ center G₀ :=
      (QuotientGroup.mk' (center G₀)).comp (hX.Φ.codRestrict _ hXG₀)
    have hf : f₁ = f₂ := by
      refine MonoidHom.eq_of_eqOn_dense (E6GraphLevi.closure_adjacentSet (E := K)) fun B hB => ?_
      obtain ⟨J, x, hJx, hxB⟩ := exists_fieldFamily2E6_adjacent h2 hX.Φ ΦY hc hB
      have hx : ((realize h2).codRestrict _ hrealA) B = (x : adjointGroup .E6 K) :=
        Subtype.ext hxB.symm
      change Ψ (((realize h2).codRestrict _ hrealA) B) = QuotientGroup.mk _
      rw [hx, hΨφ J x]
      congr 1
      exact Subtype.ext hJx
    intro B
    exact DFunLike.congr_fun hf B
  have hσsurj : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  have hRX : ∀ r : Fin Tag.F4.rank, r ≠ 0 → relRankOne σ r ≤ su6Levi σ := by
    intro r hr
    refine le_inf ((relRankOne_le_relLevi σ r).trans (relLevi_le_subsystemGroup fun j hj => ?_))
      (relRankOne_le_C0 σ r)
    have hj' := mem_relNodeSet.1 hj
    rw [Finset.mem_singleton] at hj'
    intro h1
    rw [h1] at hj'
    exact hr (hj'.symm.trans (by decide))
  have hRY : relRankOne σ 0 ≤ omegaMinusLevi σ := by
    refine le_inf ((relRankOne_le_relLevi σ 0).trans (relLevi_le_subsystemGroup fun j hj => ?_))
      (relRankOne_le_C0 σ 0)
    have hj' := mem_relNodeSet.1 hj
    have key : ∀ j : Fin Tag.E6.rank, e6IndexToF4 j ∈ ({0} : Finset (Fin Tag.F4.rank)) →
        (j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) := by decide
    exact key j hj'
  have hsu : ∀ {y : ModGL TwistTag.E6.tag K}, y ∈ su6Levi σ →
      ∃ B ∈ unitarySL σ, realize h2 B = y := fun {y} hy => by
    have hy' : y ∈ subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA ⊓
        graphFixedRootGroup TwistTag.E6 K σ := hy
    rw [(E6GraphLevi.subsystemGroup_inf_eq_map_realize hK hσ h2).1] at hy'
    exact hy'
  have hC0 : ∀ y : graphFixedRootGroup TwistTag.E6 K σ, ((e.symm y : L) : G) ∈ G₀ := by
    have hle : graphFixedRootGroup TwistTag.E6 K σ ≤
        (G₀.comap (L.subtype.comp e.symm.toMonoidHom)).map
          (graphFixedRootGroup TwistTag.E6 K σ).subtype := by
      refine (iSup_relRankOne hσsurj).symm.le.trans (iSup_le fun r => ?_)
      intro z hz
      have hzC : z ∈ graphFixedRootGroup TwistTag.E6 K σ := relRankOne_le_C0 σ r hz
      refine ⟨⟨z, hzC⟩, ?_, rfl⟩
      change ((e.symm ⟨z, hzC⟩ : L) : G) ∈ G₀
      by_cases hr : r = 0
      · subst hr
        have hzD := hRY hz
        rw [← hY'.fix ⟨z, hzC⟩ hzD (mem_inf.1 hzD).1]
        exact hYG₀ _
      · obtain ⟨B, hB, hBz⟩ := hsu (hRX r hr hz)
        have hN1 := hX.N1 B hB (hBz ▸ hzC)
        have hze : (⟨z, hzC⟩ : graphFixedRootGroup TwistTag.E6 K σ) = ⟨realize h2 B, hBz ▸ hzC⟩ :=
          Subtype.ext hBz.symm
        rw [hze, ← hN1]
        exact hXG₀ B
    intro y
    obtain ⟨y', hy', hyy'⟩ := hle y.2
    have : y' = y := Subtype.ext hyy'
    rw [← this]
    exact hy'
  have hLG₀ : L ≤ G₀ := by
    intro g hg
    have h := hC0 (e ⟨g, hg⟩)
    rwa [MulEquiv.symm_apply_apply] at h
  have hCA : graphFixedRootGroup TwistTag.E6 K σ ≤ adjointGroup .E6 K :=
    graphFixedRootGroup_le_adjointGroup' σ
  have hQ1 : ∀ y : graphFixedRootGroup TwistTag.E6 K σ,
      Ψ ⟨(y : ModGL TwistTag.E6.tag K), hCA y.2⟩ = QuotientGroup.mk ⟨_, hC0 y⟩ := by
    let f₁ : graphFixedRootGroup TwistTag.E6 K σ →* G₀ ⧸ center G₀ :=
      Ψ.toMonoidHom.comp (Subgroup.inclusion hCA)
    let f₂ : graphFixedRootGroup TwistTag.E6 K σ →* G₀ ⧸ center G₀ :=
      (QuotientGroup.mk' (center G₀)).comp
        ((L.subtype.comp e.symm.toMonoidHom).codRestrict _ hC0)
    have hle : graphFixedRootGroup TwistTag.E6 K σ ≤
        (MonoidHom.eqLocus f₁ f₂).map (graphFixedRootGroup TwistTag.E6 K σ).subtype := by
      refine (iSup_relRankOne hσsurj).symm.le.trans (iSup_le fun r => ?_)
      intro z hz
      have hzC : z ∈ graphFixedRootGroup TwistTag.E6 K σ := relRankOne_le_C0 σ r hz
      refine ⟨⟨z, hzC⟩, ?_, rfl⟩
      change Ψ ⟨z, hCA hzC⟩ = QuotientGroup.mk ⟨((e.symm ⟨z, hzC⟩ : L) : G), hC0 _⟩
      by_cases hr : r = 0
      · subst hr
        have hzD := hRY hz
        have hzrel : z ∈ relLevi K {0} := relRankOne_le_relLevi σ 0 hz
        have hzL : (⟨z, hCA hzC⟩ : adjointGroup .E6 K) ∈
            CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {1} := by
          rw [E6Pilot.levi_adjDatumE6_eq, mem_subgroupOf]
          have h1 := (relLevi_one_eq_rootSpan (K := K)).2 ▸ hzrel
          exact h1
        have h1 : (1 : Fin Tag.E6.rank) ∈ ({1} : Finset (Fin Tag.E6.rank)) :=
          Finset.mem_singleton_self _
        have hn : ¬∃ m ∈ ({1} : Finset (Fin Tag.E6.rank)), m ≠ 1 ∧ m ≠ 3 :=
          fun ⟨m, hm, hm1, _⟩ => hm1 (Finset.mem_singleton.1 hm)
        have e1 := hΨφ ⟨{1}, by simp⟩ ⟨_, hzL⟩
        rw [show (⟨z, hCA hzC⟩ : adjointGroup .E6 K) =
          ((⟨_, hzL⟩ : (adjDatumE6 K).leviAmalgam ⟨{1}, by simp⟩) : adjointGroup .E6 K)
            from rfl, e1]
        congr 1
        apply Subtype.ext
        change fieldFamily2E6 h2 hX.Φ ΦY hc ⟨{1}, by simp⟩ ⟨_, hzL⟩ = _
        rw [fieldFamily2E6_of_Y h1 hn]
        exact hY'.fix ⟨z, hzC⟩ hzD (mem_inf.1 hzD).1
      · obtain ⟨B, hB, hBz⟩ := hsu (hRX r hr hz)
        have hN1 := hX.N1 B hB (hBz ▸ hzC)
        have hze : (⟨z, hzC⟩ : graphFixedRootGroup TwistTag.E6 K σ) =
            ⟨realize h2 B, hBz ▸ hzC⟩ := Subtype.ext hBz.symm
        have hza : (⟨z, hCA hzC⟩ : adjointGroup .E6 K) = ⟨realize h2 B, hrealA B⟩ :=
          Subtype.ext hBz.symm
        rw [hza, hKL B]
        congr 1
        apply Subtype.ext
        change hX.Φ B = ((e.symm ⟨z, hzC⟩ : L) : G)
        rw [hze]
        exact hN1
    intro y
    obtain ⟨y', hy', hyy'⟩ := hle y.2
    have : y' = y := Subtype.ext hyy'
    rw [← this]
    exact hy'
  obtain ⟨σE, hσE⟩ := exists_ringEquiv_toRingHom_eq σ
  let F' : MulAut (adjointGroup Tag.E6 K) := exactNormalAut Tag.E6 K 1 σE 1
  have hF'coe : ∀ y : adjointGroup Tag.E6 K,
      ((F' y : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) = twistHom TwistTag.E6 K σ y.1 := by
    intro y
    change ((exactNormalAut Tag.E6 K 1 σE 1 y : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) = _
    rw [coe_exactNormalAut, rootDiagUnit_one, one_mul, inv_one, mul_one, hσE]
    simp only [exactQ, pow_one]
    rfl
  let α : MulAut (adjointGroup Tag.E6 K) := EPilot.normalizerQuotMulAut Ψ.symm ⟨t, htN⟩
  have hprin : ∀ (y : adjointGroup Tag.E6 K) (g : G) (hg : g ∈ G₀) (hg' : t * g * t⁻¹ ∈ G₀),
      Ψ y = QuotientGroup.mk ⟨g, hg⟩ → Ψ (F' y) = QuotientGroup.mk ⟨t * g * t⁻¹, hg'⟩ →
        α y = F' y := by
    intro y g hg hg' h1 h2'
    have h3 := EPilot.normalizerQuotMulAut_apply Ψ.symm ⟨t, htN⟩ ⟨g, hg⟩
    have hy : Ψ.symm (QuotientGroup.mk' (center G₀) ⟨g, hg⟩) = y := by
      rw [MulEquiv.symm_apply_eq]
      exact h1.symm
    have hn : G₀.normalizerMonoidHom ⟨t, htN⟩ ⟨g, hg⟩ = ⟨t * g * t⁻¹, hg'⟩ :=
      Subtype.ext (Subgroup.normalizerMonoidHom_apply_apply_coe G₀ ⟨t, htN⟩ ⟨g, hg⟩)
    rw [hy, hn] at h3
    change α y = _ at h3
    rw [h3, MulEquiv.symm_apply_eq]
    exact h2'.symm
  have h1 : (1 : Fin Tag.E6.rank) ∈ ({1} : Finset (Fin Tag.E6.rank)) := Finset.mem_singleton_self _
  have hn : ¬∃ m ∈ ({1} : Finset (Fin Tag.E6.rank)), m ≠ 1 ∧ m ≠ 3 :=
    fun ⟨m, hm, hm1, _⟩ => hm1 (Finset.mem_singleton.1 hm)
  have hΨY : ∀ (z : adjointGroup .E6 K)
      (hz : z ∈ CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {1})
      (hzD : ((z : ModGL .E6 K) : ModGL TwistTag.E6.tag K) ∈
        subsystemGroup TwistTag.E6.tag K setD),
      Ψ z = QuotientGroup.mk ⟨ΦY ⟨_, hzD⟩, hYG₀ _⟩ := by
    intro z hz hzD
    have e1 := hΨφ ⟨{1}, by simp⟩ ⟨z, hz⟩
    refine e1.trans ?_
    congr 1
  have hperm1 : TwistTag.E6.perm 1 = 1 := by decide
  have hD1 : ∀ c : K, xUnit TwistTag.E6.tag K 1 c ∈ subsystemGroup TwistTag.E6.tag K setD ∧
      yUnit TwistTag.E6.tag K 1 c ∈ subsystemGroup TwistTag.E6.tag K setD := fun c =>
    ⟨Subgroup.subset_closure ⟨1, Or.inl rfl, c, Or.inl rfl⟩,
      Subgroup.subset_closure ⟨1, Or.inl rfl, c, Or.inr rfl⟩⟩
  have hαx : ∀ (i : Fin Tag.E6.rank) (c : K), α (xElement i c) = F' (xElement i c) := by
    intro i c
    by_cases hi : i = 1
    · subst hi
      have hz := E6Pilot.xElement_mem_levi_adjDatumE6 (k := K) 1 c
      have hz' := E6Pilot.xElement_mem_levi_adjDatumE6 (k := K) 1 (σ c)
      have hF : F' (xElement 1 c) = xElement 1 (σ c) := Subtype.ext (by
        rw [hF'coe]
        change twistHom TwistTag.E6 K σ (xUnit TwistTag.E6.tag K 1 c) =
          xUnit TwistTag.E6.tag K 1 (σ c)
        rw [twistHom_xUnit, hperm1])
      have htw1 : t * ΦY ⟨_, (hD1 c).1⟩ * t⁻¹ = ΦY ⟨_, (hD1 (σ c)).1⟩ := by
        have h4 := hY'.twist ⟨_, (hD1 c).1⟩
        change t * ((hY'.Φ ⟨_, (hD1 c).1⟩ : centralizerPerfectCore _) : G) * t⁻¹ =
          ((hY'.Φ ⟨_, (hD1 (σ c)).1⟩ : centralizerPerfectCore _) : G)
        rw [← h4]
        congr 2
        apply Subtype.ext
        change twistHom TwistTag.E6 K σ (xUnit TwistTag.E6.tag K 1 c) =
          xUnit TwistTag.E6.tag K 1 (σ c)
        rw [twistHom_xUnit, hperm1]
      refine hprin _ _ (hYG₀ _) (htw1 ▸ hYG₀ _) (hΨY _ hz (hD1 c).1) ?_
      rw [hF, hΨY _ hz' (hD1 (σ c)).1]
      congr 1
      exact Subtype.ext htw1.symm
    · obtain ⟨t', htl, -, -⟩ := pathIdx_lo_hi_check i hi
      have hxτ : xElement i c = ⟨realize h2 (Matrix.SpecialLinearGroup.transvection
          (E6GraphLevi.castSucc_ne_succ t') c), hrealA _⟩ := Subtype.ext (by
        change xUnit Tag.E6 K i c = realize h2 _
        rw [E6GraphLevi.realize_x]
        exact congrArg (fun j => xUnit Tag.E6 K j c) htl.symm)
      have hFτ : F' (xElement i c) = ⟨realize h2 (unitaryTwist σ
          (Matrix.SpecialLinearGroup.transvection (E6GraphLevi.castSucc_ne_succ t') c)),
          hrealA _⟩ := Subtype.ext (by
        rw [hF'coe, hxτ]
        exact E6GraphLevi.twistHom_realize σ h2 _)
      have hN3 := hX.N3 (Matrix.SpecialLinearGroup.transvection (E6GraphLevi.castSucc_ne_succ t') c)
      refine hprin _ _ (hXG₀ _) (hN3 ▸ hXG₀ _) (by rw [hxτ]; exact hKL _) ?_
      rw [hFτ, hKL]
      congr 1
      exact Subtype.ext hN3.symm
  have hαy : ∀ (i : Fin Tag.E6.rank) (c : K), α (yElement i c) = F' (yElement i c) := by
    intro i c
    by_cases hi : i = 1
    · subst hi
      have hz := E6Pilot.yElement_mem_levi_adjDatumE6 (k := K) 1 c
      have hz' := E6Pilot.yElement_mem_levi_adjDatumE6 (k := K) 1 (σ c)
      have hF : F' (yElement 1 c) = yElement 1 (σ c) := Subtype.ext (by
        rw [hF'coe]
        change twistHom TwistTag.E6 K σ (yUnit TwistTag.E6.tag K 1 c) =
          yUnit TwistTag.E6.tag K 1 (σ c)
        rw [twistHom_yUnit, hperm1])
      have htw1 : t * ΦY ⟨_, (hD1 c).2⟩ * t⁻¹ = ΦY ⟨_, (hD1 (σ c)).2⟩ := by
        have h4 := hY'.twist ⟨_, (hD1 c).2⟩
        change t * ((hY'.Φ ⟨_, (hD1 c).2⟩ : centralizerPerfectCore _) : G) * t⁻¹ =
          ((hY'.Φ ⟨_, (hD1 (σ c)).2⟩ : centralizerPerfectCore _) : G)
        rw [← h4]
        congr 2
        apply Subtype.ext
        change twistHom TwistTag.E6 K σ (yUnit TwistTag.E6.tag K 1 c) =
          yUnit TwistTag.E6.tag K 1 (σ c)
        rw [twistHom_yUnit, hperm1]
      refine hprin _ _ (hYG₀ _) (htw1 ▸ hYG₀ _) (hΨY _ hz (hD1 c).2) ?_
      rw [hF, hΨY _ hz' (hD1 (σ c)).2]
      congr 1
      exact Subtype.ext htw1.symm
    · obtain ⟨t', htl, -, -⟩ := pathIdx_lo_hi_check i hi
      have hyτ : yElement i c = ⟨realize h2 (Matrix.SpecialLinearGroup.transvection
          (E6GraphLevi.castSucc_ne_succ t').symm c), hrealA _⟩ := Subtype.ext (by
        change yUnit Tag.E6 K i c = realize h2 _
        rw [E6GraphLevi.realize_y]
        exact congrArg (fun j => yUnit Tag.E6 K j c) htl.symm)
      have hFτ : F' (yElement i c) = ⟨realize h2 (unitaryTwist σ
          (Matrix.SpecialLinearGroup.transvection (E6GraphLevi.castSucc_ne_succ t').symm c)),
          hrealA _⟩ := Subtype.ext (by
        rw [hF'coe, hyτ]
        exact E6GraphLevi.twistHom_realize σ h2 _)
      have hN3 := hX.N3 (Matrix.SpecialLinearGroup.transvection
        (E6GraphLevi.castSucc_ne_succ t').symm c)
      refine hprin _ _ (hXG₀ _) (hN3 ▸ hXG₀ _) (by rw [hyτ]; exact hKL _) ?_
      rw [hFτ, hKL]
      congr 1
      exact Subtype.ext hN3.symm
  have hαF : α = F' := MulEquiv.toMonoidHom_injective
    (CFSG.LieType.Ree.adjointGroup_hom_ext (f := α.toMonoidHom) (g := F'.toMonoidHom) hαx hαy)
  refine ⟨G₀, ⟨Subgroup.isPerfect_iff.1 hqs.1, ?_, hLG₀, hEX, hEY, htN, Ψ.symm, ?_, ?_⟩⟩
  · rw [hZ]
    exact Odd.of_dvd_nat E6Pilot.odd_card_center_minGroup_e6 (Subgroup.card_map_dvd _ _)
  · intro x hx
    have h := hQ1 (e x)
    have h' : Ψ.symm (QuotientGroup.mk ⟨(x : G), hx⟩) =
        ⟨((e x : graphFixedRootGroup TwistTag.E6 K σ) : ModGL TwistTag.E6.tag K), hCA (e x).2⟩ := by
      rw [MulEquiv.symm_apply_eq, h]
      congr 1
      apply Subtype.ext
      change (x : G) = ((e.symm (e x) : L) : G)
      rw [MulEquiv.symm_apply_apply]
    rw [h']
  · intro y
    change ((α y : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) = _
    rw [hαF]
    exact hF'coe y


theorem ctFieldFamilyInput2E6_holds : CTFieldFamilyInput2E6 := by
  intro G _ _ L f k K _ _ _ _ hf2 hk hK σ hσ e t htL _ hX hY
  exact exists_fieldRowModel_2E6 hf2 hk hK hσ htL hX hY

end Model

end CFSG.SeitzReduction.TwistedE6Pilot
