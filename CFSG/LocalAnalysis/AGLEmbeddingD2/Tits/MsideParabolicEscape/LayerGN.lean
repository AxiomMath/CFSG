module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.LayerGNDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.GNLift
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.GNQuotient
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.GN
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.LocalAnalysis.RankThreeTheoremC
open scoped commutatorElement

section Components

variable {W : Type} [Group W] [Finite W]

omit [Finite W] in
theorem mem_center_map_iff {L : Subgroup W} {x : W} :
    x ∈ (Subgroup.center ↥L).map L.subtype ↔ x ∈ L ∧ ∀ y ∈ L, x * y = y * x := by
  constructor
  · rintro ⟨⟨x, hx⟩, hz, rfl⟩
    refine ⟨hx, fun y hy => ?_⟩
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨y, hy⟩)).symm
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, Subgroup.mem_center_iff.mpr fun y => Subtype.ext (h y y.2).symm, rfl⟩

theorem commute_of_isComponentOf {L L' : Subgroup W} (hL : IsComponentOf L ⊤)
    (hL' : IsComponentOf L' ⊤) (hne : L ≠ L') {x y : W} (hx : x ∈ L) (hy : y ∈ L') :
    Commute x y := by
  rcases CFSG.LocalCores.distinct_components_commute ((CFSG.isComponent_iff_open L).2 hL)
    ((CFSG.isComponent_iff_open L').2 hL') with h | h
  · exact absurd h hne
  · have hc : ⁅x, y⁆ ∈ ⁅L, L'⁆ := Subgroup.commutator_mem_commutator hx hy
    rw [h, Subgroup.mem_bot] at hc
    exact commutatorElement_eq_one_iff_commute.mp hc

omit [Finite W] in
theorem isComponentOf_map_conj {L : Subgroup W} (hL : IsComponentOf L ⊤) (m : W) :
    IsComponentOf (L.map (MulAut.conj m).toMonoidHom) ⊤ :=
  (CFSG.isComponent_iff_open _).1
    (CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj m) ((CFSG.isComponent_iff_open L).2 hL))

theorem mem_center_map_of_mem_of_ne {L L' : Subgroup W} (hL : IsComponentOf L ⊤)
    (hL' : IsComponentOf L' ⊤) (hne : L' ≠ L) {x : W} (hxL : x ∈ L) (hxL' : x ∈ L') :
    x ∈ (Subgroup.center ↥L).map L.subtype :=
  mem_center_map_iff.2 ⟨hxL, fun _ hy => (commute_of_isComponentOf hL' hL hne hxL' hy).eq⟩

theorem mem_normalizer_of_le {L E : Subgroup W} (hL : IsComponentOf L ⊤) (hEL : E ≤ L)
    (hEZ : ¬ E ≤ (Subgroup.center ↥L).map L.subtype) {m : W}
    (hm : m ∈ Subgroup.normalizer (E : Set W)) : m ∈ Subgroup.normalizer (L : Set W) := by
  by_contra hmL
  apply hEZ
  intro e he
  have hne : L.map (MulAut.conj m).toMonoidHom ≠ L := fun h =>
    hmL (Subgroup.mem_normalizer_iff_map_conj_eq.2 h)
  have he' : e ∈ L.map (MulAut.conj m).toMonoidHom := by
    refine ⟨m⁻¹ * e * m, hEL ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (inv_mem hm) e).mp he
      simpa using this
    · simp [mul_assoc]
  exact mem_center_map_of_mem_of_ne hL (isComponentOf_map_conj hL m) hne (hEL he) he'

omit [Finite W] in
theorem conj_mem_center_map {L : Subgroup W} {m : W}
    (hm : m ∈ Subgroup.normalizer (L : Set W)) {z : W}
    (hz : z ∈ (Subgroup.center ↥L).map L.subtype) :
    m * z * m⁻¹ ∈ (Subgroup.center ↥L).map L.subtype := by
  rw [mem_center_map_iff] at hz ⊢
  refine ⟨(Subgroup.mem_normalizer_iff.mp hm z).mp hz.1, fun y hy => ?_⟩
  have hy' : m⁻¹ * y * m ∈ L := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hm) y).mp hy
    simpa using this
  have h := hz.2 _ hy'
  calc m * z * m⁻¹ * y = m * (z * (m⁻¹ * y * m)) * m⁻¹ := by group
    _ = m * ((m⁻¹ * y * m) * z) * m⁻¹ := by rw [h]
    _ = y * (m * z * m⁻¹) := by group

end Components

section GN

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

theorem sq_le_card_of_not_isCyclic {p : ℕ} [hp : Fact p.Prime] {W : Type} [Group W] [Finite W]
    {E : Subgroup W} (hE : IsPGroup p E) (hEc : ¬ IsCyclic E) : p ^ 2 ≤ Nat.card E := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hE
  rcases k with _ | _ | k
  · have : Subsingleton E := Finite.card_le_one_iff_subsingleton.mp (by rw [hk]; simp)
    exact absurd isCyclic_of_subsingleton hEc
  · exact absurd (isCyclic_of_prime_card (p := p) (by simpa using hk)) hEc
  · rw [hk]
    exact Nat.pow_le_pow_right hp.out.pos (by omega)

theorem GNLocal.e9_gnImg (hloc : GNLocal T) {C : Subgroup X} (hC1 : C ≠ ⊥) (hCT : C ≤ T)
    (hchar : (C.subgroupOf T).Characteristic) {E : Subgroup (X ⧸ gnC T)}
    (hE : E ≤ gnImg T (Subgroup.normalizer (C : Set X))) (hE3 : IsPGroup 3 E)
    (hEc : ¬ IsCyclic E) :
    IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      TransitiveOnNonidentity (Subgroup.normalizer (E : Set (X ⧸ gnC T))) E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨U, hUN, hU3, hUE⟩ := OrdinaryProofs.GNLift.exists_isPGroup_map_eq hE3 hE
  have hUc : ¬ IsCyclic U := by
    intro hc
    apply hEc
    rw [← hUE]
    exact isCyclic_of_surjective _ (MonoidHom.subgroupMap_surjective _ U)
  obtain ⟨hUel, hU9, htr⟩ := hloc.e9 C hC1 hCT hchar U hUN hU3 hUc
  have hEel : IsElemAbelian 3 E := hUE ▸ CFSG.SectionRank.isElemAbelian_map hUel _
  have hE9 : Nat.card E = 9 := by
    have hle : Nat.card E ≤ 9 := by
      rw [← hU9, ← hUE]
      exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd U _)
    have := sq_le_card_of_not_isCyclic hE3 hEc
    omega
  refine ⟨hEel, hE9, ?_⟩
  intro x hx y hy hx1 hy1
  rw [← hUE] at hx hy
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨w, hw, rfl⟩ := hy
  have hu1 : u ≠ 1 := fun h => hx1 (by rw [h, map_one])
  have hw1 : w ≠ 1 := fun h => hy1 (by rw [h, map_one])
  obtain ⟨n, hn, hnu⟩ := htr u hu w hw hu1 hw1
  refine ⟨QuotientGroup.mk' (gnC T) n, ?_, ?_⟩
  · rw [← hUE]
    exact Subgroup.le_normalizer_map _ ⟨n, hn, rfl⟩
  · rw [← hnu, map_mul, map_mul, map_inv]

theorem GNLocal.isPSolvable_gnImg (hloc : GNLocal T) {C : Subgroup X} (hC1 : C ≠ ⊥)
    (hCT : C ≤ T) (hchar : (C.subgroupOf T).Characteristic) :
    CFSG.HallHigman.IsPSolvable 3 ↥(gnImg T (Subgroup.normalizer (C : Set X))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact OrdinaryProofs.PSolvableClosure.isPSolvable_map _ (hloc.solv C hC1 hCT hchar)

omit [Finite X] in
theorem le_of_isGNPair {T₁ T₂ : Subgroup X} (hpair : IsGNPair T T₁ T₂) : T₁ ≤ T :=
  hpair.le_center.trans (QuasithinUnique.Setup.omegaOneCenterOf_le T)

theorem GNLocal.gnYComponent (hloc : GNLocal T) {T₁ T₂ : Subgroup X} (hpair : IsGNPair T T₁ T₂)
    {L : Subgroup (X ⧸ gnC T)} (hL : IsComponentOf L ⊤)
    (hns : ¬ CFSG.HallHigman.IsPSolvable 3 ↥L) : GNYComponent T T₁ T₂ L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨hL, fun h => hns ?_, fun h => hns ?_⟩
  · exact OrdinaryProofs.PSolvableClosure.isPSolvable_of_le
      (hloc.isPSolvable_gnImg hpair.ne_bot₁ (le_of_isGNPair hpair) hpair.char₁)
      (h.trans (Subgroup.map_mono (Subgroup.centralizer_le_normalizer _)))
  · exact OrdinaryProofs.PSolvableClosure.isPSolvable_of_le
      (hloc.isPSolvable_gnImg hpair.ne_bot₂ hpair.le₂ hpair.char₂) h

theorem exists_three_elem_of_not_le {Y : Type*} [Group Y] {A Z : Subgroup Y}
    (h : ¬ pElementSubgroup 3 A ≤ Z) : ∃ v ∈ A, (∃ k : ℕ, orderOf v = 3 ^ k) ∧ v ∉ Z := by
  by_contra hne
  push Not at hne
  exact h ((Subgroup.closure_le Z).mpr fun x hx => hne x hx.1 hx.2)

theorem eq_of_gn (hGN : GlaubermanNilesInput) (hX : GNSetting X T) (hloc : GNLocal T)
    {L L' : Subgroup (X ⧸ gnC T)} (hL : IsComponentOf L ⊤) (hL' : IsComponentOf L' ⊤)
    (hns : ¬ CFSG.HallHigman.IsPSolvable 3 ↥L) (hns' : ¬ CFSG.HallHigman.IsPSolvable 3 ↥L') :
    L = L' := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T₁, T₂, hpair, -, hthree, -⟩ := hGN X T hX (hX.ne_bot_of_isComponentOf hL)
  by_contra hne
  obtain ⟨v, hvA, hv3, hvZ⟩ :=
    exists_three_elem_of_not_le (hthree L (hloc.gnYComponent hpair hL hns)).1
  obtain ⟨v', hv'A, hv'3, hv'Z⟩ :=
    exists_three_elem_of_not_le (hthree L' (hloc.gnYComponent hpair hL' hns')).1
  have hvL : v ∈ L := hvA.2
  have hv'L' : v' ∈ L' := hv'A.2
  have hvL' : v ∉ L' := fun h => hvZ (mem_center_map_of_mem_of_ne hL hL' (Ne.symm hne) hvL h)
  have hv'L : v' ∉ L := fun h => hv'Z (mem_center_map_of_mem_of_ne hL' hL hne hv'L' h)
  have hcomm : Commute v v' := commute_of_isComponentOf hL hL' hne hvL hv'L'
  set D : Subgroup (X ⧸ gnC T) := Subgroup.closure ({v, v'} : Set (X ⧸ gnC T)) with hD
  have hvD : v ∈ D := Subgroup.subset_closure (by simp)
  have hv'D : v' ∈ D := Subgroup.subset_closure (by simp)
  have hD3 : IsPGroup 3 D := OrdinaryProofs.GNLift.isPGroup_closure_pair hcomm hv3 hv'3
  have hDle : D ≤ gnImg T (Subgroup.normalizer (T₁ : Set X)) := by
    rw [hD, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hvA.1
    · exact hv'A.1
  have hDc : ¬ IsCyclic D := by
    intro hc
    rcases OrdinaryProofs.GNLift.mem_zpowers_or_mem_zpowers hv3 hv'3 hc with h | h
    · exact hvL' ((Subgroup.zpowers_le.mpr hv'L') h)
    · exact hv'L ((Subgroup.zpowers_le.mpr hvL) h)
  obtain ⟨-, -, htr⟩ := hloc.e9_gnImg hpair.ne_bot₁ (le_of_isGNPair hpair) hpair.char₁ hDle hD3 hDc
  have hv1 : v ≠ 1 := fun h => hvZ (h ▸ Subgroup.one_mem _)
  have hvv1 : v * v' ≠ 1 := by
    intro h
    have : v' = v⁻¹ := eq_inv_of_mul_eq_one_right h
    exact hv'L (this ▸ inv_mem hvL)
  obtain ⟨m, -, hmv⟩ := htr v hvD (v * v') (D.mul_mem hvD hv'D) hv1 hvv1
  by_cases hmL : m ∈ Subgroup.normalizer (L : Set (X ⧸ gnC T))
  ·
    have hvv : v * v' ∈ L := hmv ▸ (Subgroup.mem_normalizer_iff.mp hmL v).mp hvL
    exact hv'L (by simpa using L.mul_mem (inv_mem hvL) hvv)
  ·
    have hne' : L.map (MulAut.conj m).toMonoidHom ≠ L := fun h =>
      hmL (Subgroup.mem_normalizer_iff_map_conj_eq.2 h)
    have hvvm : v * v' ∈ L.map (MulAut.conj m).toMonoidHom := ⟨v, hvL, hmv⟩
    apply hvZ
    refine mem_center_map_iff.2 ⟨hvL, fun y hy => ?_⟩
    have h1 : (v * v') * y = y * (v * v') :=
      (commute_of_isComponentOf (isComponentOf_map_conj hL m) hL hne' hvvm hy).eq
    have h2 : v' * y = y * v' := (commute_of_isComponentOf hL' hL (Ne.symm hne) hv'L' hy).eq
    calc v * y = (v * v') * y * v'⁻¹ := by
          rw [mul_assoc v v' y, h2]; group
      _ = y * (v * v') * v'⁻¹ := by rw [h1]
      _ = y * v := by group

theorem mem_normalizer_of_gn (hGN : GlaubermanNilesInput) (hX : GNSetting X T)
    (hloc : GNLocal T) {L : Subgroup (X ⧸ gnC T)} (hL : IsComponentOf L ⊤)
    (hns : ¬ CFSG.HallHigman.IsPSolvable 3 ↥L) (g : X ⧸ gnC T) :
    g ∈ Subgroup.normalizer (L : Set (X ⧸ gnC T)) := by
  have hns' : ¬ CFSG.HallHigman.IsPSolvable 3 ↥(L.map (MulAut.conj g).toMonoidHom) :=
    fun h => hns (OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
      (L.equivMapOfInjective _ (MulAut.conj g).injective).symm h)
  exact Subgroup.mem_normalizer_iff_map_conj_eq.2
    (eq_of_gn hGN hX hloc (isComponentOf_map_conj hL g) hL hns' hns)

omit [Finite X] in
theorem isElemAbelian_subgroupOf' {p : ℕ} {E : Subgroup X} (hE : IsElemAbelian p E)
    (H : Subgroup X) : IsElemAbelian p (E.subgroupOf H) := CFSG.Open.IsElemAbelian.subgroupOf hE H

theorem false_of_center_three (hloc : GNLocal T) {T₁ T₂ : Subgroup X} (hpair : IsGNPair T T₁ T₂)
    (hcen : GNCentre T T₁ T₂) {L : Subgroup (X ⧸ gnC T)} (hY : GNYComponent T T₁ T₂ L)
    (hLT : gnImg T T ≤ Subgroup.normalizer (L : Set (X ⧸ gnC T)))
    (h3 : Nat.card (Subgroup.center ↥L) = 3)
    (hZE : ∀ E : Subgroup ↥L, IsElemAbelian 3 E → Nat.card E = 9 → Subgroup.center ↥L ≤ E) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hL := hY.1
  have key : ∀ Ti : Subgroup X, Ti ≠ ⊥ → Ti ≤ T → (Ti.subgroupOf T).Characteristic →
      1 < Open.pRank 3 (gnA T Ti L) → False := by
    intro Ti h1 h2 h3' hr
    obtain ⟨E, hEA, hEel, hE9'⟩ := OrdinaryProofs.GNLift.exists_elemAbelian_card_sq hr
    have hE9 : Nat.card E = 9 := by rw [hE9']; norm_num
    have hE3 : IsPGroup 3 E := IsPGroup.of_card (n := 2) hE9'
    obtain ⟨-, -, htr⟩ := hloc.e9_gnImg h1 h2 h3' (hEA.trans inf_le_left) hE3
      (OrdinaryProofs.GNLift.not_isCyclic_of_isElemAbelian hEel hE9')
    have hEL : E ≤ L := hEA.trans inf_le_right
    set Z := (Subgroup.center ↥L).map L.subtype with hZdef
    have hZcard : Nat.card Z = 3 := by
      rw [hZdef, Subgroup.card_map_of_injective L.subtype_injective, h3]
    have hZE' : Z ≤ E := by
      have hsub := hZE (E.subgroupOf L) (isElemAbelian_subgroupOf' hEel L)
        (by rw [← hE9]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv)
      have := Subgroup.map_mono (f := L.subtype) hsub
      rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hEL] at this
    have hEZ : ¬ E ≤ Z := fun h => by
      have := Subgroup.card_le_of_le h
      rw [hE9, hZcard] at this
      omega
    obtain ⟨z, hz, hz1⟩ : ∃ z ∈ Z, z ≠ 1 := by
      by_contra hne
      push Not at hne
      have : Z = ⊥ := (Subgroup.eq_bot_iff_forall Z).mpr hne
      rw [this, Subgroup.card_bot] at hZcard
      omega
    obtain ⟨y, hyE, hyZ⟩ : ∃ y ∈ E, y ∉ Z := Set.not_subset.mp hEZ
    have hy1 : y ≠ 1 := fun h => hyZ (h ▸ Z.one_mem)
    obtain ⟨m, hm, hmz⟩ := htr z (hZE' hz) y hyE hz1 hy1
    exact hyZ (hmz ▸ conj_mem_center_map (mem_normalizer_of_le hL hEL hEZ hm) hz)
  rcases hcen L hY hLT 3 Nat.prime_three (by rw [h3]) with h | h
  · exact key T₁ hpair.ne_bot₁ (le_of_isGNPair hpair) hpair.char₁ h
  · exact key T₂ hpair.ne_bot₂ hpair.le₂ hpair.char₂ h

theorem rankTwo_of_gn_of_ffConclusion (hGN : GlaubermanNilesInput) (h56 : AGL81I56)
    (hRT : KFactParabolicCoverRankTwo) (hA7 : KFactAltSevenE9) (hZ : KFactOddCentreE9)
    (hX : GNSetting X T) (hloc : GNLocal T) {L : Subgroup (X ⧸ gnC T)}
    (hL : IsComponentOf L ⊤) (hJ : ⁅L, gnImg T (thompsonJ T)⁆ = L)
    (hns : ¬ CFSG.HallHigman.IsPSolvable 3 ↥L)
    (hconc : CFSG.HardMathSupport.Cooperstein.Coordinator.FFConclusion (↥L ⧸ Subgroup.center ↥L)) :
    Subgroup.center ↥L = ⊥ ∧ IsRankTwoLayerType (↥L ⧸ Subgroup.center ↥L) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T₁, T₂, hpair, hpar, -, hcen, halt7, -⟩ := hGN X T hX (hX.ne_bot_of_isComponentOf hL)
  have hY := hloc.gnYComponent hpair hL hns
  have hLT : gnImg T T ≤ Subgroup.normalizer (L : Set (X ⧸ gnC T)) :=
    fun g _ => mem_normalizer_of_gn hGN hX hloc hL hns g
  have hT₁ := le_of_isGNPair hpair
  have hodd := OrdinaryProofs.GNQuotient.not_two_dvd_card_center_of_isComponentOf
    (CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.pCore_two_gnQuot hX) hL
  have hcentre : (IsRankTwoLayerType (↥L ⧸ Subgroup.center ↥L) ∨
      Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin 7))) →
      Subgroup.center ↥L = ⊥ := by
    intro h
    rcases hZ ↥L hL.2.2 hodd h with h | ⟨h3, hE, -⟩
    · exact h
    · exact (false_of_center_three hloc hpair hcen hY hLT h3 hE).elim
  have htrA : ∀ Ti : Subgroup X, Ti ≠ ⊥ → Ti ≤ T → (Ti.subgroupOf T).Characteristic →
      ∀ E : Subgroup (X ⧸ gnC T), E ≤ gnA T Ti L → IsElemAbelian 3 E → Nat.card E = 9 →
        TransitiveOnNonidentity (Subgroup.normalizer (E : Set (X ⧸ gnC T))) E := by
    intro Ti h1 h2 h3 E hE hEel hE9
    have hE9' : Nat.card E = 3 ^ 2 := by rw [hE9]; norm_num
    exact (hloc.e9_gnImg h1 h2 h3 (hE.trans inf_le_left) (IsPGroup.of_card hE9')
      (OrdinaryProofs.GNLift.not_isCyclic_of_isElemAbelian hEel hE9')).2.2
  have hclassical : IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L) →
      Subgroup.center ↥L = ⊥ ∧ IsRankTwoLayerType (↥L ⧸ Subgroup.center ↥L) := by
    intro hcl
    have hcov : CoveredByTwo L (gnImg T T ⊓ L) (gnA T T₁ L) (gnA T T₂ L) := by
      intro P hP
      rcases hpar L hL (isChevTwo_of_classicalTwoOrG2 hcl) P hP with h | h
      · exact Or.inl (le_inf (h.trans (Subgroup.map_mono (Subgroup.centralizer_le_normalizer _)))
          ((pElementSubgroup_le P).trans hP.1))
      · exact Or.inr (le_inf h ((pElementSubgroup_le P).trans hP.1))
    have hrt := hRT (X ⧸ gnC T) L (gnImg T T ⊓ L) (gnA T T₁ L) (gnA T T₂ L) hL hcl
      (OrdinaryProofs.GNQuotient.isSylowTwoOf_gnImg_inf hX.sylow hL.2.1) hcov
      (OrdinaryProofs.PSolvableClosure.isPSolvable_of_le
        (hloc.isPSolvable_gnImg hpair.ne_bot₁ hT₁ hpair.char₁) inf_le_left)
      (OrdinaryProofs.PSolvableClosure.isPSolvable_of_le
        (hloc.isPSolvable_gnImg hpair.ne_bot₂ hpair.le₂ hpair.char₂) inf_le_left)
      (fun E hE hE3 hEc => by
        rcases hE with hE | hE
        · exact hloc.e9_gnImg hpair.ne_bot₁ hT₁ hpair.char₁
            ((hE.trans inf_le_left).trans inf_le_left) hE3 hEc
        · exact hloc.e9_gnImg hpair.ne_bot₂ hpair.le₂ hpair.char₂
            ((hE.trans inf_le_left).trans inf_le_left) hE3 hEc)
    exact ⟨hcentre (Or.inl hrt), hrt⟩
  rcases hconc with hcl | ⟨m, hm5, ⟨e⟩⟩
  · exact hclassical hcl
  rcases (by omega : m = 5 ∨ m = 6 ∨ m = 8 ∨ m = 7 ∨ 8 < m) with h | h | h | h7 | h9
  · exact hclassical (Or.inr (Or.inl ⟨m, Or.inl h, ⟨e⟩⟩))
  · exact hclassical (Or.inr (Or.inl ⟨m, Or.inr (Or.inl h), ⟨e⟩⟩))
  · exact hclassical (Or.inr (Or.inl ⟨m, Or.inr (Or.inr h), ⟨e⟩⟩))
  ·
    subst h7
    have hZ1 := hcentre (Or.inr ⟨e⟩)
    have eL : ↥L ≃* alternatingGroup (Fin 7) :=
      (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ1.symm)).trans e
    exfalso
    have key : ∀ Ti : Subgroup X, Ti ≠ ⊥ → Ti ≤ T → (Ti.subgroupOf T).Characteristic →
        1 < Open.pRank 3 (gnA T Ti L) → False := by
      intro Ti h1 h2 h3 hr
      obtain ⟨E, hEA, hEel, hE9'⟩ := OrdinaryProofs.GNLift.exists_elemAbelian_card_sq hr
      have hE9 : Nat.card E = 9 := by rw [hE9']; norm_num
      have htr := htrA Ti h1 h2 h3 E hEA hEel hE9
      have hEL : E ≤ L := hEA.trans inf_le_right
      have hEZ : ¬ E ≤ (Subgroup.center ↥L).map L.subtype := by
        rw [hZ1, Subgroup.map_bot]
        intro h
        have := Subgroup.card_le_of_le h
        rw [hE9, Subgroup.card_bot] at this
        omega
      exact hA7 (X ⧸ gnC T) L E (Subgroup.normalizer (E : Set (X ⧸ gnC T))) hL ⟨eL⟩ hEL hEel
        hE9 (fun m hm => mem_normalizer_of_le hL hEL hEZ hm) le_rfl htr
    rcases halt7 L hL hLT ⟨eL⟩ with h | h
    · exact key T₁ hpair.ne_bot₁ hT₁ hpair.char₁ h
    · exact key T₂ hpair.ne_bot₂ hpair.le₂ hpair.char₂ h
  ·
    exfalso
    apply h56 X T hX L hL hJ m h9 ⟨e⟩
    have hZ1 : omegaOneCenterOf T ≠ ⊥ := fun h =>
      hpair.ne_bot₁ (le_bot_iff.mp (h ▸ hpair.le_center))
    exact OrdinaryProofs.PSolvableClosure.isPSolvable_of_le (hloc.isPSolvable_gnImg hZ1
      (QuasithinUnique.Setup.omegaOneCenterOf_le T)
      (QuasithinUnique.Setup.characteristic_omegaOneCenterOf T))
      (inf_le_left.trans (Subgroup.map_mono (Subgroup.centralizer_le_normalizer _)))

theorem rankTwo_of_gn (hGN : GlaubermanNilesInput)
    (hFFT : CFSG.HardMathSupport.Cooperstein.Coordinator.FFModuleTheorem) (h56 : AGL81I56)
    (hRT : KFactParabolicCoverRankTwo) (hA7 : KFactAltSevenE9) (hZ : KFactOddCentreE9)
    (hX : GNSetting X T) (hloc : GNLocal T) {L : Subgroup (X ⧸ gnC T)}
    (hL : IsComponentOf L ⊤) (hJ : ⁅L, gnImg T (thompsonJ T)⁆ = L)
    (hns : ¬ CFSG.HallHigman.IsPSolvable 3 ↥L) :
    Subgroup.center ↥L = ⊥ ∧ IsRankTwoLayerType (↥L ⧸ Subgroup.center ↥L) :=
  rankTwo_of_gn_of_ffConclusion hGN h56 hRT hA7 hZ hX hloc hL hJ hns
    (CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.gn_ffConclusion hFFT X T hX L hL hJ)

end GN

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
