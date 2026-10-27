module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizePieces
public import CFSG.LieType.CurtisTits.Symplectic
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.RankOne
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotParamNormalize
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotTwistSp4

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic (equivStatedSp rootGroup rootDatum)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective elt ne_succ')
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open CFSG.LieType.Steinberg.Sp (mem_closure_sl2)
open CFSG.LieType.CurtisTits (rankOne levi IsCompatible)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp)
open CFSG.SeitzReduction.F4Pilot (statedSpMap)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open scoped MatrixGroups

section Supp

variable {n : ℕ}

@[expose] def NotInSupp (k j : Fin n) : Prop :=
  k ≠ j ∧ (j.val + 1 < n → k.val ≠ j.val + 1)

theorem simpleRootSL2_le_spBlock {F : Type} [Field F] {j : Fin n} {N : Finset (Fin n)}
    (hj : j ∈ N) (hj1 : ∀ h : j.val + 1 < n, (⟨j.val + 1, h⟩ : Fin n) ∈ N) :
    simpleRootSL2 F j ≤ spBlock F N := by
  by_cases h : j.val + 1 < n
  · rw [simpleRootSL2_of_lt h]
    rintro _ ⟨A, rfl⟩
    intro r s hrs
    refine isSupp_shortBlock (ne_succ' h) A r s fun hrs' => hrs ⟨?_, ?_⟩
    · rcases hrs'.1 with hr | hr <;> rw [mem_coords] at hr <;>
        rcases hr with rfl | rfl <;> simp only [mem_planeCoords, planeOf_inl, planeOf_inr]
      exacts [hj, hj, hj1 h, hj1 h]
    · rcases hrs'.2 with hr | hr <;> rw [mem_coords] at hr <;>
        rcases hr with rfl | rfl <;> simp only [mem_planeCoords, planeOf_inl, planeOf_inr]
      exacts [hj, hj, hj1 h, hj1 h]
  · rw [simpleRootSL2_of_not_lt h, ← spBlock_singleton]
    exact spBlock_mono (Finset.singleton_subset_iff.2 hj)

theorem simpleRootSL2_le_spBlock_pair {F : Type} [Field F] {j k l : Fin n} (hk : NotInSupp k j)
    (hl : NotInSupp l j) : simpleRootSL2 F j ≤ spBlock F ({k, l}ᶜ : Finset (Fin n)) := by
  refine simpleRootSL2_le_spBlock (mem_compl_pair_iff'.2 ⟨hk.1.symm, hl.1.symm⟩)
    fun h => mem_compl_pair_iff'.2 ⟨fun e => hk.2 h (by rw [← e]), fun e => hl.2 h (by rw [← e])⟩

theorem simpleRootSL2_le_spBlock_compl' {F : Type} [Field F] {j k : Fin n} (hk : NotInSupp k j) :
    simpleRootSL2 F j ≤ spBlock F ({k}ᶜ : Finset (Fin n)) :=
  simpleRootSL2_le_spBlock_compl hk.1 hk.2

theorem exists_notInSupp_pair (hn : 5 ≤ n) (i j : Fin n) :
    ∃ k : Fin n, NotInSupp k i ∧ NotInSupp k j := by
  classical
  obtain ⟨m, hm, hmS⟩ : ∃ m ∈ Finset.range n, m ∉ ({i.val, i.val + 1, j.val, j.val + 1} :
      Finset ℕ) := by
    refine Finset.exists_mem_notMem_of_card_lt_card ?_
    rw [Finset.card_range]
    refine lt_of_le_of_lt (Finset.card_insert_le _ _) ?_
    have h1 := Finset.card_insert_le (i.val + 1) ({j.val, j.val + 1} : Finset ℕ)
    have h2 := Finset.card_insert_le j.val ({j.val + 1} : Finset ℕ)
    rw [Finset.card_singleton] at h2
    omega
  rw [Finset.mem_range] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hmS
  refine ⟨⟨m, hm⟩, ⟨fun e => hmS.1 (by rw [← e]), fun _ e => hmS.2.1 e⟩,
    ⟨fun e => hmS.2.2.1 (by rw [← e]), fun _ e => hmS.2.2.2 e⟩⟩

theorem exists_notInSupp_of_card_le_two (hn : 5 ≤ n) (J : Finset (Fin n)) (hJ : J.card ≤ 2) :
    ∃ k : Fin n, ∀ j ∈ J, NotInSupp k j := by
  classical
  set S : Finset ℕ := J.biUnion fun j => ({j.val, j.val + 1} : Finset ℕ) with hSdef
  have hS : S.card ≤ 4 := by
    calc S.card ≤ ∑ j ∈ J, ({j.val, j.val + 1} : Finset ℕ).card := Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ J, 2 := Finset.sum_le_sum fun j _ => Finset.card_le_two
      _ = 2 * J.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ 4 := by omega
  obtain ⟨m, hm, hmS⟩ : ∃ m ∈ Finset.range n, m ∉ S :=
    Finset.exists_mem_notMem_of_card_lt_card (by rw [Finset.card_range]; omega)
  rw [Finset.mem_range] at hm
  refine ⟨⟨m, hm⟩, fun j hj => ⟨fun e => hmS ?_, fun _ e => hmS ?_⟩⟩
  · refine Finset.mem_biUnion.2 ⟨j, hj, ?_⟩
    rw [← e]
    simp
  · refine Finset.mem_biUnion.2 ⟨j, hj, ?_⟩
    exact Finset.mem_insert_of_mem (Finset.mem_singleton.2 e)

end Supp

section Levi

variable {F : Type} [Field F] {n : ℕ}

theorem rankOne_rootGroup_eq_simpleRootSL2 (j : Fin n) :
    rankOne (rootGroup n F) j = simpleRootSL2 F j := by
  by_cases h : j.val + 1 < n
  · rw [simpleRootSL2_of_lt h, range_shortBlock_eq_rankOne h]
  · rw [simpleRootSL2_of_not_lt h, longRootSp2, range_longBlock_eq_rankOne h]

theorem leviAmalgam_eq_iSup (J : {J : Finset (Fin n) // J.card ≤ 2}) :
    (rootDatum n F).leviAmalgam J = ⨆ j ∈ J.1, simpleRootSL2 F j := by
  change (⨆ j ∈ J.1, rankOne (rootGroup n F) j) = _
  exact iSup_congr fun j => iSup_congr fun _ => rankOne_rootGroup_eq_simpleRootSL2 j

theorem map_statedSpMap_simpleRootSL2_le {K : Type} [Field K] (ι : K →+* F) (j : Fin n) :
    (simpleRootSL2 K j).map (statedSpMap ι n) ≤ simpleRootSL2 F j := by
  rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩
  have hle : Subgroup.closure (Set.range (sl2Upper (k := K)) ∪ Set.range sl2Lower) ≤
      (simpleRootSL2 F j).comap ((statedSpMap ι n).comp (simpleRootHom K j)) := by
    rw [Subgroup.closure_le]
    by_cases h : j.val + 1 < n
    · rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · change statedSpMap ι n (simpleRootHom K j (sl2Upper c)) ∈ simpleRootSL2 F j
        rw [simpleRootHom_of_lt h, shortBlock_sl2Upper, F4Pilot.statedSpMap_elt,
          ← shortBlock_sl2Upper, simpleRootSL2_of_lt h]
        exact ⟨_, rfl⟩
      · change statedSpMap ι n (simpleRootHom K j (sl2Lower c)) ∈ simpleRootSL2 F j
        rw [simpleRootHom_of_lt h, shortBlock_sl2Lower, F4Pilot.statedSpMap_elt,
          ← shortBlock_sl2Lower (ne_succ' h), simpleRootSL2_of_lt h]
        exact ⟨_, rfl⟩
    · rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · change statedSpMap ι n (simpleRootHom K j (sl2Upper c)) ∈ simpleRootSL2 F j
        rw [simpleRootHom_of_not_lt h, longBlock_sl2Upper, F4Pilot.statedSpMap_elt,
          ← longBlock_sl2Upper, simpleRootSL2_of_not_lt h]
        exact ⟨_, rfl⟩
      · change statedSpMap ι n (simpleRootHom K j (sl2Lower c)) ∈ simpleRootSL2 F j
        rw [simpleRootHom_of_not_lt h, longBlock_sl2Lower, F4Pilot.statedSpMap_elt,
          ← longBlock_sl2Lower, simpleRootSL2_of_not_lt h]
        exact ⟨_, rfl⟩
  exact hle (mem_closure_sl2 A)

theorem fieldSp_mem_simpleRootSL2 (σ : F ≃+* F) {j : Fin n} {x : StatedSp n F}
    (hx : x ∈ simpleRootSL2 F j) : fieldSp n F σ x ∈ simpleRootSL2 F j := by
  rw [F4Pilot.fieldSp_eq_statedSpMap]
  exact map_statedSpMap_simpleRootSL2_le (σ : F →+* F) j ⟨x, hx, rfl⟩

end Levi

section Recognition

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  {F : Type} [Field F] [Finite F] {n : ℕ} {e : L ≃* StatedSp n K} {t : G}
  {ι : K →+* F} {σ : F ≃+* F}

omit [CharP K 2] in
@[expose] def FieldParamAgree (P : ∀ k : Fin n, FieldNeighbourParam e t ι σ k) : Prop :=
  ∀ (k l : Fin n) (x : StatedSp n F) (hx : x ∈ spBlock F ({k}ᶜ : Finset (Fin n)))
    (hx' : x ∈ spBlock F ({l}ᶜ : Finset (Fin n))), (P k).Φ ⟨x, hx⟩ = (P l).Φ ⟨x, hx'⟩

theorem exists_injective_fieldRow_of_agree (hK : 4 ≤ Nat.card K) (hn : 5 ≤ n)
    (P : ∀ k : Fin n, FieldNeighbourParam e t ι σ k) (hagree : FieldParamAgree P) :
    ∃ ψ : StatedSp n F →* G, Function.Injective ψ ∧ ψ.range = spGlobal e ∧
      (∀ x : StatedSp n K, ψ (spFieldMap n ι x) = ((e.symm x : L) : G)) ∧
      ∀ x : StatedSp n F, t * ψ x * t⁻¹ = ψ (fieldSp n F σ x) := by
  classical
  have : CharP F 2 := charP_of_injective_ringHom ι.injective 2
  choose kJ hkJ using fun J : {J : Finset (Fin n) // J.card ≤ 2} =>
    exists_notInSupp_of_card_le_two hn J.1 J.2
  have hKle : ∀ J, (rootDatum n F).leviAmalgam J ≤ spBlock F ({kJ J}ᶜ : Finset (Fin n)) :=
    fun J => (leviAmalgam_eq_iSup J).le.trans
      (iSup₂_le fun j hj => simpleRootSL2_le_spBlock_compl' (hkJ J j hj))
  set φ : ∀ J, (rootDatum n F).leviAmalgam J →* G :=
    fun J => (P (kJ J)).Φ.comp (Subgroup.inclusion (hKle J)) with hφ
  have hcomp : IsCompatible (rootDatum n F).leviAmalgam φ := by
    intro I J _ x y hxy
    change (P (kJ I)).Φ ⟨x, hKle I x.2⟩ = (P (kJ J)).Φ ⟨y, hKle J y.2⟩
    have hx' : (x : StatedSp n F) ∈ spBlock F ({kJ J}ᶜ : Finset (Fin n)) := hxy ▸ hKle J y.2
    rw [hagree (kJ I) (kJ J) x (hKle I x.2) hx']
    congr 1
    exact Subtype.ext hxy
  set G₀ : Subgroup G := ⨆ J, (φ J).range with hG₀
  have hle : ∀ J x, φ J x ∈ G₀ := fun J x => le_iSup (fun J => (φ J).range) J ⟨x, rfl⟩
  set φ' : ∀ J, (rootDatum n F).leviAmalgam J →* G₀ := fun J => (φ J).codRestrict G₀ (hle J)
    with hφ'
  have hcomp' : IsCompatible (rootDatum n F).leviAmalgam φ' := fun I J hIJ x y hxy =>
    Subtype.ext (hcomp I J hIJ x y hxy)
  have hgen' : ⨆ J, (φ' J).range = ⊤ := by
    apply Subgroup.map_injective G₀.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    refine (iSup_congr fun J => ?_).trans hG₀.symm
    rw [← MonoidHom.range_comp]
    rfl
  have hinjφ : ∀ J, Function.Injective (φ J) := fun J =>
    (P (kJ J)).injective.comp (Subgroup.inclusion_injective (hKle J))
  have hnt : ∃ J, ∃ x, φ' J x ≠ 1 := by
    obtain ⟨J, hJ⟩ := CFSG.LieType.CurtisTits.exists_leviAmalgam_ne_bot
      (CFSG.LieType.Universal.Symplectic.steinbergExtras n F) (show 0 < n by omega)
    obtain ⟨x, hx⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hJ
    refine ⟨J, x, fun h => hx ?_⟩
    have h1 : φ J x = φ J 1 := by
      rw [map_one]
      exact congrArg Subtype.val h
    exact hinjφ J h1
  obtain ⟨g, hg1, hFc⟩ := F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := F)
  have hadm : StatedLieAdmissible .PSp n 2 g :=
    ⟨Nat.prime_two, hg1, by omega, fun h => by
      have := congrArg Prod.fst h
      simp only at this
      omega⟩
  obtain ⟨-, -, hrec, -⟩ :=
    CFSG.LieType.CurtisTits.curtisTitsConclusion_symplectic.{0} (F := F) hadm hFc
      (by omega : 3 ≤ n)
  obtain ⟨ψ₀, hψ₀, -, hker, -⟩ := hrec G₀ φ' hcomp' hgen' hnt
  have hinj₀ : Function.Injective ψ₀ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans (center_statedSp_eq_bot n).le
  set ψ : StatedSp n F →* G := G₀.subtype.comp ψ₀ with hψdef
  have hψφ : ∀ J (x : (rootDatum n F).leviAmalgam J), ψ x = φ J x :=
    fun J x => congrArg Subtype.val (hψ₀ J x)
  have hJ1 : ∀ j : Fin n, ({j} : Finset (Fin n)).card ≤ 2 := fun j => by simp
  have hψJ : ∀ (j : Fin n) (y : StatedSp n F) (hy : y ∈ simpleRootSL2 F j),
      ψ y = (P (kJ ⟨{j}, hJ1 j⟩)).Φ ⟨y, simpleRootSL2_le_spBlock_compl'
        (hkJ ⟨{j}, hJ1 j⟩ j (Finset.mem_singleton_self j)) hy⟩ := by
    intro j y hy
    have hyK : y ∈ (rootDatum n F).leviAmalgam ⟨{j}, hJ1 j⟩ :=
      (leviAmalgam_eq_iSup ⟨{j}, hJ1 j⟩).ge
        (mem_iSup_of_mem j (mem_iSup_of_mem (Finset.mem_singleton_self j) hy))
    exact hψφ ⟨{j}, hJ1 j⟩ ⟨y, hyK⟩
  refine ⟨ψ, G₀.subtype_injective.comp hinj₀, ?_, ?_, ?_⟩
  ·
    rw [MonoidHom.range_eq_map, ← iSup_simpleRootSL2_eq_top (show 1 ≤ n by omega),
      Subgroup.map_iSup, spGlobal]
    refine iSup_congr fun j => ?_
    set k := kJ ⟨{j}, hJ1 j⟩ with hk
    have hkj := hkJ ⟨{j}, hJ1 j⟩ j (Finset.mem_singleton_self j)
    rw [(P k).pieceCore_singleton_eq_map hK hkj.1 hkj.2]
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, simpleRootSL2_le_spBlock_compl' hkj hy⟩, mem_subgroupOf.2 hy,
        (hψJ j y hy).symm⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, mem_subgroupOf.1 hy, hψJ j y (mem_subgroupOf.1 hy)⟩
  ·
    intro x
    have htop : (⊤ : Subgroup (StatedSp n K)) ≤
        MonoidHom.eqLocus (ψ.comp (spFieldMap n ι)) (L.subtype.comp e.symm.toMonoidHom) := by
      rw [← iSup_simpleRootSL2_eq_top (show 1 ≤ n by omega), iSup_le_iff]
      intro j y hy
      set k := kJ ⟨{j}, hJ1 j⟩ with hk
      have hkj := hkJ ⟨{j}, hJ1 j⟩ j (Finset.mem_singleton_self j)
      have hyF : spFieldMap n ι y ∈ simpleRootSL2 F j := by
        rw [spFieldMap_eq_statedSpMap]
        exact map_statedSpMap_simpleRootSL2_le ι j ⟨y, hy, rfl⟩
      change ψ (spFieldMap n ι y) = ((e.symm y : L) : G)
      rw [hψJ j _ hyF]
      exact (P k).N1 y (simpleRootSL2_le_spBlock_compl' hkj hy)
    exact htop (mem_top x)
  ·
    intro x
    have htop : (⊤ : Subgroup (StatedSp n F)) ≤
        MonoidHom.eqLocus ((MulAut.conj t).toMonoidHom.comp ψ)
          (ψ.comp (fieldSp n F σ).toMonoidHom) := by
      rw [← iSup_simpleRootSL2_eq_top (show 1 ≤ n by omega), iSup_le_iff]
      intro j y hy
      set k := kJ ⟨{j}, hJ1 j⟩ with hk
      have hkj := hkJ ⟨{j}, hJ1 j⟩ j (Finset.mem_singleton_self j)
      have hyσ : fieldSp n F σ y ∈ simpleRootSL2 F j := fieldSp_mem_simpleRootSL2 σ hy
      change t * ψ y * t⁻¹ = ψ (fieldSp n F σ y)
      rw [hψJ j y hy, hψJ j _ hyσ, (P k).N3]
      congr 1
    exact htop (mem_top x)

end Recognition

end CFSG.SeitzReduction.SymplecticPilot
