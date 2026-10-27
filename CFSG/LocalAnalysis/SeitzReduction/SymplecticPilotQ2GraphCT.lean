module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphAlign
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RootSL2
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2FieldCT

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear)
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.LieType.Universal.SpecialLinear (fundamentalRootSubgroup rootSubgroup)
open scoped MatrixGroups

variable {K : Type} [Field K] {N ε : ℕ}

@[expose] noncomputable def q2CastSL {m : ℕ} (h : m + 1 = 2 * N + ε) :
    SpecialLinearGroup (Fin (m + 1)) K ≃* SpecialLinearGroup (Fin (2 * N + ε)) K :=
  LinearPilot.reindexSpecialLinear (finCongr h)

theorem q2CastSL_transvection {m : ℕ} (h : m + 1 = 2 * N + ε) {i j : Fin (m + 1)} (hij : i ≠ j)
    (c : K) :
    q2CastSL h (SpecialLinearGroup.transvection hij c) =
      SpecialLinearGroup.transvection (fun h' => hij ((finCongr h).injective h')) c := by
  apply Subtype.ext
  change reindex (finCongr h) (finCongr h) (Matrix.transvection i j c) =
    Matrix.transvection (finCongr h i) (finCongr h j) c
  ext a b
  simp only [reindex_apply, submatrix_apply, Matrix.transvection, Matrix.add_apply,
    Matrix.one_apply, single_apply]
  congr 1
  · simp
  · by_cases ha : a = Fin.cast h i <;> by_cases hb : b = Fin.cast h j <;>
      simp_all [Fin.ext_iff]

theorem exists_plane_notMem_of_card_le_two {m : ℕ} (h : m + 1 = 2 * N + ε) (hN : 5 ≤ N)
    (J : Finset (Fin m)) (hJ : J.card ≤ 2) :
    ∃ k : Fin N, ∀ j ∈ J, finCongr h j.castSucc ∉ planeCoordsQ2 ε {k} ∧
      finCongr h j.succ ∉ planeCoordsQ2 ε {k} := by
  classical
  set T : Finset ℕ := J.biUnion fun j => {j.castSucc.val / 2, j.succ.val / 2} with hT
  have hTc : T.card ≤ 4 := by
    calc T.card ≤ ∑ j ∈ J, ({j.castSucc.val / 2, j.succ.val / 2} : Finset ℕ).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ J, 2 := Finset.sum_le_sum fun j _ => Finset.card_le_two
      _ = 2 * J.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ 4 := by omega
  obtain ⟨k, hk⟩ : ∃ k : Fin N, k.val ∉ T := by
    by_contra hc
    push Not at hc
    have hsub : (Finset.univ.image fun k : Fin N => k.val) ⊆ T := by
      intro x hx
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hx
      exact hc k
    have := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ Fin.val_injective, Finset.card_univ,
      Fintype.card_fin] at this
    omega
  refine ⟨k, fun j hj => ⟨fun h1 => hk ?_, fun h1 => hk ?_⟩⟩
  · obtain ⟨hlt, h2⟩ := mem_planeCoordsQ2_iff.1 h1
    rw [Finset.mem_singleton] at h2
    have h3 := congrArg Fin.val h2
    simp only [finCongr_apply, Fin.val_cast] at h3
    rw [← h3]
    exact Finset.mem_biUnion.2 ⟨j, hj, by simp⟩
  · obtain ⟨hlt, h2⟩ := mem_planeCoordsQ2_iff.1 h1
    rw [Finset.mem_singleton] at h2
    have h3 := congrArg Fin.val h2
    simp only [finCongr_apply, Fin.val_cast] at h3
    rw [← h3]
    exact Finset.mem_biUnion.2 ⟨j, hj, by simp⟩

theorem map_levi_le_q2Block {m : ℕ} (h : m + 1 = 2 * N + ε) {J : Finset (Fin m)} {k : Fin N}
    (hk : ∀ j ∈ J, finCongr h j.castSucc ∉ planeCoordsQ2 ε {k} ∧
      finCongr h j.succ ∉ planeCoordsQ2 ε {k}) :
    (CFSG.LieType.Universal.SpecialLinear.levi m K J).map (q2CastSL h).toMonoidHom ≤
      q2Block ε K {k} := by
  rw [CFSG.LieType.Universal.SpecialLinear.levi, Subgroup.map_iSup]
  refine iSup_le fun j => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hj => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun s => ?_
  rintro _ ⟨x, hx, rfl⟩
  have hk' := hk j hj
  cases s
  · obtain ⟨c, rfl⟩ := (CFSG.LieType.Universal.SpecialLinear.mem_rootSubgroup _ x).1 hx
    rw [MulEquiv.coe_toMonoidHom, q2CastSL_transvection]
    exact LinearPilot.transvection_mem_blockSpecialLinear _ (Finset.mem_compl.2 hk'.2)
      (Finset.mem_compl.2 hk'.1) c
  · obtain ⟨c, rfl⟩ := (CFSG.LieType.Universal.SpecialLinear.mem_rootSubgroup _ x).1 hx
    rw [MulEquiv.coe_toMonoidHom, q2CastSL_transvection]
    exact LinearPilot.transvection_mem_blockSpecialLinear _ (Finset.mem_compl.2 hk'.1)
      (Finset.mem_compl.2 hk'.2) c

theorem blockSpecialLinear_plane_le_map_levi {m : ℕ} (h : m + 1 = 2 * N + ε) (p : Fin N)
    (j : Fin m) (hj : j.val = 2 * p.val) :
    blockSpecialLinear ({q2Coord N ε (Sum.inl (Sum.inl p)), q2Coord N ε (Sum.inl (Sum.inr p))} :
        Finset (Fin (2 * N + ε))) ≤
      (CFSG.LieType.Universal.SpecialLinear.levi m K {j}).map (q2CastSL h).toMonoidHom := by
  have ha : finCongr h j.castSucc = q2Coord N ε (Sum.inl (Sum.inl p)) :=
    Fin.ext (by simp [hj])
  have hb : finCongr h j.succ = q2Coord N ε (Sum.inl (Sum.inr p)) :=
    Fin.ext (by simp [hj])
  rw [LinearPilot.blockSpecialLinear_eq_closure, Subgroup.closure_le]
  rintro _ ⟨i, i', hii, c, hi, hi', rfl⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hi'
  have hlevi : ∀ s : Bool, fundamentalRootSubgroup m K j s ≤
      CFSG.LieType.Universal.SpecialLinear.levi m K {j} := fun s =>
    le_iSup_of_le j (le_iSup_of_le (Finset.mem_singleton_self j)
      (le_iSup (fun s => fundamentalRootSubgroup m K j s) s))
  rcases hi with rfl | rfl <;> rcases hi' with rfl | rfl
  · exact absurd rfl hii
  · refine ⟨SpecialLinearGroup.transvection
      (show j.castSucc < j.succ from Fin.castSucc_lt_succ).ne c,
      hlevi true (CFSG.LieType.Universal.SpecialLinear.transvection_mem_rootSubgroup _ c), ?_⟩
    rw [MulEquiv.coe_toMonoidHom, q2CastSL_transvection]
    congr 1
  · refine ⟨SpecialLinearGroup.transvection
      (show j.castSucc < j.succ from Fin.castSucc_lt_succ).ne' c,
      hlevi false (CFSG.LieType.Universal.SpecialLinear.transvection_mem_rootSubgroup _ c), ?_⟩
    rw [MulEquiv.coe_toMonoidHom, q2CastSL_transvection]
    congr 1
  · exact absurd rfl hii

section Recognition

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {hK : Nat.card K = 2}
  {e : L ≃* StatedSp N K}

theorem exists_injective_nsLinRow_of_agree [CharP K 2] (hε : ε ≤ 1) (hN : 5 ≤ N)
    (P : ∀ k : Fin N, NsLinParam hK ε e k) (hagree : NsLinParamAgree P) :
    ∃ ψ : SpecialLinearGroup (Fin (2 * N + ε)) K →* G, Function.Injective ψ ∧
      ψ.range = nsGlobal e ∧ LieModel (nsGlobal e) .PSL (2 * N + ε) 2 1 := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; omega)
  obtain ⟨m, hm⟩ : ∃ m, m + 1 = 2 * N + ε := ⟨2 * N + ε - 1, by omega⟩
  choose kJ hkJ using fun J : {J : Finset (Fin m) // J.card ≤ 2} =>
    exists_plane_notMem_of_card_le_two hm hN J.1 J.2
  have hKle : ∀ (J : {J : Finset (Fin m) // J.card ≤ 2})
      (x : (CFSG.LieType.Universal.SpecialLinear.rootDatum m K).leviAmalgam J),
      q2CastSL hm (x : SpecialLinearGroup (Fin (m + 1)) K) ∈ q2Block ε K {kJ J} := by
    intro J x
    have hx : (x : SpecialLinearGroup (Fin (m + 1)) K) ∈
        CFSG.LieType.Universal.SpecialLinear.levi m K J.1 := by
      rw [← CFSG.LieType.Universal.SpecialLinear.levi_rootGroup]
      exact x.2
    exact map_levi_le_q2Block hm (hkJ J) ⟨x, hx, rfl⟩
  set φ : ∀ J, (CFSG.LieType.Universal.SpecialLinear.rootDatum m K).leviAmalgam J →* G :=
    fun J => (P (kJ J)).Φ.comp
      (((q2CastSL hm).toMonoidHom.comp (Subgroup.subtype _)).codRestrict _ (hKle J)) with hφ
  have hφapp : ∀ J x, φ J x = (P (kJ J)).Φ ⟨q2CastSL hm (x : SpecialLinearGroup (Fin (m + 1)) K),
      hKle J x⟩ := fun _ _ => rfl
  have hcomp : CFSG.LieType.CurtisTits.IsCompatible
      (CFSG.LieType.Universal.SpecialLinear.rootDatum m K).leviAmalgam φ := by
    intro I J _ x y hxy
    rw [hφapp, hφapp]
    have hy' : q2CastSL hm (x : SpecialLinearGroup (Fin (m + 1)) K) ∈ q2Block ε K {kJ J} := by
      rw [hxy]; exact hKle J y
    rw [hagree (kJ I) (kJ J) _ (hKle I x) hy']
    congr 2
    rw [hxy]
  set G₀ : Subgroup G := ⨆ J, (φ J).range with hG₀
  have hle : ∀ J x, φ J x ∈ G₀ := fun J x => le_iSup (fun J => (φ J).range) J ⟨x, rfl⟩
  set φ' : ∀ J, (CFSG.LieType.Universal.SpecialLinear.rootDatum m K).leviAmalgam J →* G₀ :=
    fun J => (φ J).codRestrict G₀ (hle J) with hφ'
  have hcomp' : CFSG.LieType.CurtisTits.IsCompatible
      (CFSG.LieType.Universal.SpecialLinear.rootDatum m K).leviAmalgam φ' :=
    fun I J hIJ x y hxy => Subtype.ext (hcomp I J hIJ x y hxy)
  have hgen' : ⨆ J, (φ' J).range = ⊤ := by
    apply Subgroup.map_injective G₀.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    refine (iSup_congr fun J => ?_).trans hG₀.symm
    rw [← MonoidHom.range_comp]
    rfl
  have hinjφ : ∀ J, Function.Injective (φ J) := fun J => by
    intro x y hxy
    rw [hφapp, hφapp] at hxy
    have := Subtype.ext_iff.1 ((P (kJ J)).injective hxy)
    exact Subtype.ext ((q2CastSL hm).injective this)
  have hnt : ∃ J, ∃ x, φ' J x ≠ 1 := by
    obtain ⟨J, hJ⟩ := CFSG.LieType.CurtisTits.exists_leviAmalgam_ne_bot
      (CFSG.LieType.Universal.SpecialLinear.steinbergExtras m K) (show 0 < m by omega)
    obtain ⟨x, hx⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hJ
    refine ⟨J, x, fun h => hx ?_⟩
    have h1 : φ J x = φ J 1 := by
      rw [map_one]
      exact congrArg Subtype.val h
    exact hinjφ J h1
  have hadm : StatedLieAdmissible .PSL (m + 1) 2 1 :=
    ⟨Nat.prime_two, le_rfl, by omega, fun h => by simp at h; omega, fun h => by simp at h⟩
  obtain ⟨-, -, hrec, -⟩ :=
    CFSG.LieType.CurtisTits.curtisTitsConclusion_specialLinear.{0} (F := K) hadm
      (by rw [hK, pow_one]) (by omega : 3 ≤ m)
  obtain ⟨ψ₀, hψ₀, hsurj, hker, -, hZ, -, hLM⟩ := hrec G₀ φ' hcomp' hgen' hnt
  have hinj₀ : Function.Injective ψ₀ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro z hz
    exact LinearPilot.eq_one_of_mem_center_specialLinearGroup_of_card_two hK (hker hz)
  have hZbot : Subgroup.center G₀ = ⊥ := by
    rw [hZ, eq_bot_iff]
    rintro _ ⟨z, hz, rfl⟩
    rw [LinearPilot.eq_one_of_mem_center_specialLinearGroup_of_card_two hK hz, map_one]
    exact one_mem _
  set ψ : SpecialLinearGroup (Fin (2 * N + ε)) K →* G :=
    (G₀.subtype.comp ψ₀).comp (q2CastSL hm).symm.toMonoidHom with hψdef
  have hψinj : Function.Injective ψ :=
    (G₀.subtype_injective.comp hinj₀).comp (q2CastSL hm).symm.injective
  have hψrange : ψ.range = G₀ := by
    rw [hψdef, MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulEquiv.surjective _),
      ← MonoidHom.range_eq_map, MonoidHom.range_comp, MonoidHom.range_eq_top.2 hsurj,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hψφ : ∀ J (x : (CFSG.LieType.Universal.SpecialLinear.rootDatum m K).leviAmalgam J),
      ψ (q2CastSL hm x) = φ J x := by
    intro J x
    change ((ψ₀ ((q2CastSL hm).symm (q2CastSL hm x)) : G₀) : G) = _
    rw [MulEquiv.symm_apply_apply]
    exact congrArg Subtype.val (hψ₀ J x)
  have hG₀le : G₀ ≤ nsGlobal e := by
    refine iSup_le fun J => ?_
    rintro _ ⟨x, rfl⟩
    have h1 : φ J x ∈ (P (kJ J)).Φ.range := ⟨_, (hφapp J x).symm⟩
    rw [(P (kJ J)).range_eq] at h1
    rw [nsGlobal_def]
    exact le_iSup (fun i : Fin N => centralizerPerfectCore (modelToG e (nsTorusSp K i))) _ h1
  have hpiece : ∀ k : Fin N, centralizerPerfectCore (modelToG e (nsTorusSp K k)) ≤ G₀ := by
    intro k
    obtain ⟨j, hj⟩ : ∃ j : Fin m, j.val = 2 * k.val := ⟨⟨2 * k.val, by have := k.2; omega⟩, rfl⟩
    have hJ1 : ({j} : Finset (Fin m)).card ≤ 2 := by simp
    set J : {J : Finset (Fin m) // J.card ≤ 2} := ⟨{j}, hJ1⟩ with hJ
    have hc : q2Embed ε hK (nsElt k) ∈ (CFSG.LieType.Universal.SpecialLinear.levi m K {j}).map
        (q2CastSL hm).toMonoidHom := by
      refine blockSpecialLinear_plane_le_map_levi hm k j hj ?_
      rw [show nsElt (K := K) k = longBlock K N k zThreeSL from rfl, q2Embed_longBlock hK,
        ← LinearPilot.range_pairEmbed (q2PlaneNe k)]
      exact ⟨_, rfl⟩
    obtain ⟨x₀, hx₀, hx₀c⟩ := hc
    have hx₀' : x₀ ∈ (CFSG.LieType.Universal.SpecialLinear.rootDatum m K).leviAmalgam J := by
      have h1 : x₀ ∈ CFSG.LieType.CurtisTits.levi
          (CFSG.LieType.Universal.SpecialLinear.rootGroup m K) ({j} : Finset (Fin m)) := by
        rw [CFSG.LieType.Universal.SpecialLinear.levi_rootGroup]
        exact hx₀
      exact h1
    have hkk : kJ J ≠ k := by
      intro hkk
      have h1 := (hkJ J j (Finset.mem_singleton_self j)).1
      rw [hkk] at h1
      apply h1
      rw [mem_planeCoordsQ2_iff]
      refine ⟨by have := k.2; simp only [finCongr_apply, Fin.val_cast, Fin.val_castSucc]; omega,
        ?_⟩
      rw [Finset.mem_singleton]
      exact Fin.ext (by simp only [finCongr_apply, Fin.val_cast, Fin.val_castSucc]; omega)
    have hnk : nsElt (K := K) k ∈ spBlock K ({kJ J} : Finset (Fin N))ᶜ := by
      have := nsElt_mem_spBlock_compl (K := K) hkk
      simpa using this
    have hψc : ψ (q2Embed ε hK (nsElt k)) = ((e.symm (nsElt k) : L) : G) := by
      have h1 := hψφ J ⟨x₀, hx₀'⟩
      change ψ (q2CastSL hm x₀) = _ at h1
      rw [MulEquiv.coe_toMonoidHom] at hx₀c
      rw [← hx₀c, h1, show φ J ⟨x₀, hx₀'⟩ = (P (kJ J)).Φ ⟨q2CastSL hm x₀, hKle J ⟨x₀, hx₀'⟩⟩
        from rfl]
      have h2 := (P (kJ J)).N1 _ hnk
      rw [← h2]
      congr 2
    have hblock : (q2Block ε K {k}).map ψ ≤
        centralizerPerfectCore (modelToG e (nsTorusSp K k)) := by
      refine CFSG.Quasithin.le_perfectCore_of_perfect ?_ ?_
      · rw [nsTorusSp, centralizer_modelToG_zpowers]
        rintro _ ⟨z, hz, rfl⟩
        rw [mem_centralizer_singleton_iff, ← hψc, ← map_mul, ← map_mul]
        congr 1
        have hcb : q2Embed ε hK (nsElt k) ∈ blockSpecialLinear (planeCoordsQ2 ε {k}) := by
          rw [planeCoordsQ2_singleton, show nsElt (K := K) k = longBlock K N k zThreeSL from rfl,
            q2Embed_longBlock hK, ← LinearPilot.range_pairEmbed (q2PlaneNe k)]
          exact ⟨_, rfl⟩
        exact (LinearPilot.commute_blockSpecialLinear_of_disjoint disjoint_compl_right hcb
          hz).eq.symm
      · have hcard : 3 ≤ ((planeCoordsQ2 ε ({k} : Finset (Fin N)))ᶜ).card := by
          rw [Finset.card_compl, card_planeCoordsQ2, Finset.card_singleton, Fintype.card_fin]
          omega
        rw [← map_commutator, commutator_q2Block_eq hcard]
    have hcardE : Nat.card ((q2Block ε K {k}).map ψ) ≥
        Nat.card (centralizerPerfectCore (modelToG e (nsTorusSp K k))) := by
      rw [Subgroup.card_map_of_injective hψinj, ← (P k).range_eq,
        ← Nat.card_congr (MonoidHom.ofInjective (P k).injective).toEquiv]
    have heq := Subgroup.eq_of_le_of_card_ge hblock hcardE
    rw [← heq, ← hψrange]
    rintro _ ⟨z, -, rfl⟩
    exact ⟨z, rfl⟩
  have hG₀eq : G₀ = nsGlobal e := le_antisymm hG₀le (by
    rw [nsGlobal_def]
    exact iSup_le hpiece)
  refine ⟨ψ, hψinj, hψrange.trans hG₀eq, ?_⟩
  have e1 : G₀ ⧸ Subgroup.center G₀ ≃* nsGlobal e :=
    ((QuotientGroup.quotientMulEquivOfEq hZbot).trans QuotientGroup.quotientBot).trans
      (MulEquiv.subgroupCongr hG₀eq)
  rw [← hm]
  exact LieType.CurtisTits.lieModel_of_mulEquiv e1 hLM

end Recognition

end CFSG.SeitzReduction.SymplecticPilot
