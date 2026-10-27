module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526Defs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526P0b
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RowStmts
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankBase
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftBasic
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsPair
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair
open scoped commutatorElement

section Row26AB

variable {X : Type} [Group X] [Finite X]

theorem two_le_pRank_pElement_cMLStar {T : Subgroup X} (hX : GNSetting X T)
    {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X} (hL : LiftOf T L Ls) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : 1 < CFSG.Open.pRank p (cMBar L)) :
    2 ≤ CFSG.Open.pRank p (pElementSubgroup p (cMLStar T Ls)) := by
  have hbar : barO2 (cMHat L) = cMBar L := by
    unfold barO2 cMHat
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  have h1 : CFSG.Open.pRank p (cMHat L) = CFSG.Open.pRank p (cMBar L) := by
    rw [pRank_barO2_eq_aux_eq (cMHat L) hp hp2, hbar]
  have hcHat : cMHat L ≤ cMLStar T Ls := by
    intro x hx
    have hx' : (QuotientGroup.mk' (CFSG.pCore 2 X) x : X ⧸ CFSG.pCore 2 X) ∈
        Subgroup.centralizer (barO2 L : Set (X ⧸ CFSG.pCore 2 X)) := hx
    rw [cMLStar, Subgroup.mem_comap, Subgroup.mem_centralizer_iff, ← hL.2]
    rintro _ ⟨l, hl, rfl⟩
    have hb : QuotientGroup.mk' (CFSG.pCore 2 X) l ∈ barO2 L := Subgroup.mem_map_of_mem _ hl
    have hcomm := Subgroup.mem_centralizer_iff.1 hx' _ hb
    have hmk : QuotientGroup.mk' (CFSG.pCore 2 X) (l * x) =
        QuotientGroup.mk' (CFSG.pCore 2 X) (x * l) := by
      rw [map_mul, map_mul]
      exact hcomm
    have hpc : (l * x)⁻¹ * (x * l) ∈ CFSG.pCore 2 X := QuotientGroup.eq.1 hmk
    have hgn : (l * x)⁻¹ * (x * l) ∈ gnC T := pCore_le_gnC hX hpc
    have hc : toStar T (l * x) = toStar T (x * l) := QuotientGroup.eq.2 hgn
    simpa only [map_mul] using hc
  have h2 : CFSG.Open.pRank p (cMHat L) ≤ CFSG.Open.pRank p (pElementSubgroup p (cMLStar T Ls)) := by
    obtain ⟨E, hEH, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (cMHat L)
    refine CFSG.SectionRank.le_pRank hp.one_lt ?_ hE hcard
    intro x hx
    unfold pElementSubgroup
    refine Subgroup.subset_closure ?_
    refine ⟨hcHat (hEH hx), ?_⟩
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one (hE.2 x hx)) with h0 | h0
    · exact ⟨0, by simp [h0]⟩
    · exact ⟨1, by simp [h0]⟩
  omega

end Row26AB

section Row26B

variable {X : Type} [Group X] [Finite X]

theorem relIndex_normalizer_le_two_aux1 (g h : X) (H : Subgroup X) :
    conjSub g (conjSub h H) = conjSub (g * h) H := by
  unfold conjSub
  rw [Subgroup.map_map]
  congr 1
  ext y
  simp [mul_assoc]

theorem relIndex_normalizer_le_two_aux2 (H : Subgroup X) : conjSub 1 H = H := by
  unfold conjSub
  ext y
  simp

theorem relIndex_normalizer_le_two {T T₁ T₂ : Subgroup X} (h : IsGNPair T T₁ T₂)
    (hcard : Set.ncard (CY T T₁ T₂) ≤ 3) {A : Subgroup X} (hAT : A ≤ T) (hA : IsPGroup 2 A)
    {I : Subgroup X} (hI : I ∈ CY T T₁ T₂) :
    (A ⊓ Subgroup.normalizer (I : Set X)).relIndex A ≤ 2 := by
  classical
  letI : MulAction A (Subgroup X) :=
    { smul := fun a J => conjSub (a : X) J
      one_smul := fun J => by
        show conjSub ((1 : A) : X) J = J
        rw [Subgroup.coe_one, relIndex_normalizer_le_two_aux2]
      mul_smul := fun a b J => by
        show conjSub ((a * b : A) : X) J = conjSub (a : X) (conjSub (b : X) J)
        rw [Subgroup.coe_mul, relIndex_normalizer_le_two_aux1] }
  have hmemN : ∀ a : A, (a : X) ∈ Subgroup.normalizer (I : Set X) ↔ a • I = I := by
    intro a
    rw [mem_normalizer_iff_map_conj_eq]
    rfl
  have hstab : MulAction.stabilizer A I = (A ⊓ Subgroup.normalizer (I : Set X)).subgroupOf A := by
    ext a
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf, hmemN]
    exact ⟨fun h' => ⟨a.2, h'⟩, fun h' => h'.2⟩
  have hidx : (A ⊓ Subgroup.normalizer (I : Set X)).relIndex A = (MulAction.stabilizer A I).index := by
    rw [hstab]
    rfl
  have horb : (MulAction.orbit A I).ncard ≤ 3 := by
    refine le_trans (Set.ncard_le_ncard ?_ (Set.toFinite _)) hcard
    rintro J ⟨a, rfl⟩
    exact conj_mem_CY h hI (hAT a.2)
  have hle3 : (MulAction.stabilizer A I).index ≤ 3 := by
    rw [MulAction.index_stabilizer]
    exact horb
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hA
  have hdvd : (MulAction.stabilizer A I).index ∣ 2 ^ n := by
    rw [← hn]
    exact Subgroup.index_dvd_card _
  obtain ⟨m, -, hmeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [hmeq] at hle3
  have hm1 : m ≤ 1 := by
    by_contra hc
    have h4 : 4 ≤ 2 ^ m := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rw [hidx, hmeq]
  interval_cases m <;> norm_num

end Row26B

section Row26C

variable {X : Type} [Group X] [Finite X]

theorem commutator_yLifts_le_aux1 {T T₁ T₂ : Subgroup X} (hX : GNSetting X T)
    {I I' : Subgroup X} (hI : I ∈ CY T T₁ T₂) (hI' : I' ∈ CY T T₁ T₂) {y : X} (hy : y ∈ I)
    {i : X} (hi : i ∈ I') {v : X} (hv : v ∈ gnV T) :
    y * ⁅i, v⁆ * y⁻¹ ∈ ⁅I', gnV T⁆ := by
  haveI hVn : (gnV T).Normal := Subgroup.normalClosure_normal
  have hv' : y * v * y⁻¹ ∈ gnV T := hVn.conj_mem v hv y
  by_cases hII : I = I'
  · subst hII
    have hy' : y * i * y⁻¹ ∈ I := I.mul_mem (I.mul_mem hy hi) (I.inv_mem hy)
    have e : y * ⁅i, v⁆ * y⁻¹ = ⁅y * i * y⁻¹, y * v * y⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.commutator_mem_commutator hy' hv'
  · have hIC : IsC2 I := by
      obtain ⟨_, _, hL⟩ := hI
      exact hL.1
    have hI'C : IsC2 I' := by
      obtain ⟨_, _, hL⟩ := hI'
      exact hL.1
    have hbar := isC2_commute_of_ne hIC hI'C hII
    have h1 : ⁅QuotientGroup.mk' (CFSG.pCore 2 X) y, QuotientGroup.mk' (CFSG.pCore 2 X) i⁆ = 1 := by
      have hmem : ⁅QuotientGroup.mk' (CFSG.pCore 2 X) y, QuotientGroup.mk' (CFSG.pCore 2 X) i⁆ ∈
          ⁅barO2 I, barO2 I'⁆ :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_map_of_mem _ hy)
          (Subgroup.mem_map_of_mem _ hi)
      rw [hbar, Subgroup.mem_bot] at hmem
      exact hmem
    have hc' : Commute (QuotientGroup.mk' (CFSG.pCore 2 X) i) (QuotientGroup.mk' (CFSG.pCore 2 X) y) :=
      (commutatorElement_eq_one_iff_mul_comm.1 h1).symm
    have hcpc : ⁅i⁻¹, y⁆ ∈ CFSG.pCore 2 X := by
      have h2 : QuotientGroup.mk' (CFSG.pCore 2 X) ⁅i⁻¹, y⁆ = 1 := by
        rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.2 hc'.inv_left
      exact (QuotientGroup.eq_one_iff _).1 h2
    have hcC : ⁅i⁻¹, y⁆ ∈ Subgroup.centralizer (gnV T : Set X) := pCore_le_gnC hX hcpc
    have hcv : ∀ w ∈ gnV T, w * ⁅i⁻¹, y⁆ = ⁅i⁻¹, y⁆ * w := fun w hw =>
      Subgroup.mem_centralizer_iff.1 hcC w hw
    have e1 : y * i * y⁻¹ = i * ⁅i⁻¹, y⁆ := by
      simp only [commutatorElement_def]
      group
    have hcw : ⁅i⁻¹, y⁆ * (y * v * y⁻¹) * ⁅i⁻¹, y⁆⁻¹ = y * v * y⁻¹ := by
      rw [← hcv _ hv', mul_assoc, mul_inv_cancel, mul_one]
    have e2 : y * ⁅i, v⁆ * y⁻¹ = ⁅y * i * y⁻¹, y * v * y⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    have key : ∀ (c w : X), c * w * c⁻¹ = w → ⁅i * c, w⁆ = ⁅i, w⁆ := by
      intro c w hcw'
      simp only [commutatorElement_def]
      calc i * c * w * (i * c)⁻¹ * w⁻¹ = i * (c * w * c⁻¹) * i⁻¹ * w⁻¹ := by group
        _ = i * w * i⁻¹ * w⁻¹ := by rw [hcw']
    rw [e2, e1, key _ _ hcw]
    exact Subgroup.commutator_mem_commutator hi hv'
theorem commutator_yLifts_le_aux2 {T T₁ T₂ : Subgroup X} (hX : GNSetting X T) {I : Subgroup X}
    (hI : I ∈ CY T T₁ T₂) {y : X} (hy : y ∈ I) :
    ∀ s ∈ (⨆ I' ∈ CY T T₁ T₂, ⁅I', gnV T⁆ : Subgroup X),
      y * s * y⁻¹ ∈ (⨆ I' ∈ CY T T₁ T₂, ⁅I', gnV T⁆ : Subgroup X) := by
  have hsub : (⨆ I' ∈ CY T T₁ T₂, ⁅I', gnV T⁆ : Subgroup X) ≤
      (⨆ I' ∈ CY T T₁ T₂, ⁅I', gnV T⁆ : Subgroup X).comap (MulAut.conj y).toMonoidHom := by
    refine iSup₂_le fun I' hI' => ?_
    intro x hx
    rw [Subgroup.mem_comap]
    have hc : ⁅I', gnV T⁆ ≤ (⁅I', gnV T⁆ : Subgroup X).comap (MulAut.conj y).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro i hi v hv
      rw [Subgroup.mem_comap]
      exact commutator_yLifts_le_aux1 hX hI hI' hy hi hv
    have hcx : (MulAut.conj y).toMonoidHom x ∈ ⁅I', gnV T⁆ := Subgroup.mem_comap.1 (hc hx)
    exact le_iSup₂ (f := fun J (_ : J ∈ CY T T₁ T₂) => ⁅J, gnV T⁆) I' hI' hcx
  intro s hs
  exact hsub hs

@[expose] def commutator_yLifts_le_aux3K (S V : Subgroup X) : Subgroup X where
  carrier := {y | y ∈ Subgroup.normalizer (S : Set X) ∧ ∀ v ∈ V, ⁅v, y⁆ ∈ S}
  mul_mem' := fun {a b} ha hb => by
    refine ⟨Subgroup.mul_mem _ ha.1 hb.1, fun v hv => ?_⟩
    have e : ⁅v, a * b⁆ = ⁅v, a⁆ * (a * ⁅v, b⁆ * a⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact S.mul_mem (ha.2 v hv) ((Subgroup.mem_normalizer_iff.1 ha.1 _).1 (hb.2 v hv))
  one_mem' := ⟨Subgroup.one_mem _, fun v _ => by simp⟩
  inv_mem' := fun {a} ha => by
    refine ⟨Subgroup.inv_mem _ ha.1, fun v hv => ?_⟩
    have e : ⁅v, a⁻¹⁆ = (a⁻¹ * ⁅v, a⁆ * a⁻¹⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact S.inv_mem ((Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ ha.1) _).1 (ha.2 v hv))
theorem commutator_yLifts_le {T T₁ T₂ : Subgroup X} (hX : GNSetting X T) :
    ⁅gnV T, yLifts T T₁ T₂⁆ ≤ ⨆ I ∈ CY T T₁ T₂, ⁅I, gnV T⁆ := by
  set S : Subgroup X := ⨆ I ∈ CY T T₁ T₂, ⁅I, gnV T⁆ with hS
  have hY : yLifts T T₁ T₂ ≤ commutator_yLifts_le_aux3K S (gnV T) := by
    unfold yLifts
    refine iSup₂_le fun I hI => ?_
    intro y hy
    show y ∈ Subgroup.normalizer (S : Set X) ∧ ∀ v ∈ gnV T, ⁅v, y⁆ ∈ S
    refine ⟨?_, fun v hv => ?_⟩
    · rw [Subgroup.mem_normalizer_iff]
      intro s
      constructor
      · exact commutator_yLifts_le_aux2 hX hI hy s
      · intro hs
        have h1 := commutator_yLifts_le_aux2 hX hI (I.inv_mem hy) (y * s * y⁻¹) hs
        have e : y⁻¹ * (y * s * y⁻¹) * y⁻¹⁻¹ = s := by group
        rw [e] at h1
        exact h1
    · rw [← commutatorElement_inv]
      exact S.inv_mem (le_iSup₂ (f := fun J (_ : J ∈ CY T T₁ T₂) => ⁅J, gnV T⁆) I hI
        (Subgroup.commutator_mem_commutator hy hv))
  refine Subgroup.commutator_le.2 fun v hv y hy => ?_
  exact (hY hy).2 v hv

end Row26C

end CFSG.LocalAnalysis.RankThreeUC.S15
