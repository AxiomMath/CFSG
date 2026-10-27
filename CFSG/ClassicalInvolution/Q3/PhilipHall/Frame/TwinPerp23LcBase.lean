module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPairOdd
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf14E4
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinConnTransportLift
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf5Conn
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23ExU24
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23ExU29

public section

namespace CFSG.ClassicalInvolution.Q3.Q3CH

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Asc77

theorem isSectionMember3_conj_gen {G : Type} [Group G] {Y K : Subgroup G} {z : G}
    (h : IsSectionMember3 Y K z) (n : G) :
    IsSectionMember3 (conjSub n Y) (conjSub n K) (n * z * n⁻¹) where
  le := conjSub_mono (n := n) h.le
  orderOf_eq_two := by
    have := orderOf_injective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective z
    simpa [h.orderOf_eq_two] using this
  mem := conj_mem_conjSub h.mem
  subnormal := by
    have h1 := isSubnormal_map_conj h.subnormal n
    have h2 : (Subgroup.centralizer ({z} : Set G) ⊓ Y).map (MulAut.conj n).toMonoidHom =
        Subgroup.centralizer ({n * z * n⁻¹} : Set G) ⊓ conjSub n Y := by
      rw [Subgroup.map_inf_eq _ _ (MulAut.conj n).toMonoidHom (MulAut.conj n).injective]
      rw [← conjSub_centralizer_singleton n z]
      rfl
    exact h2 ▸ h1
  nonempty_equiv := by
    obtain ⟨e'⟩ := h.nonempty_equiv
    let ε : ↥K ≃* ↥(conjSub n K) :=
      Subgroup.equivMapOfInjective K (MulAut.conj n).toMonoidHom (MulAut.conj n).injective
    exact ⟨(QuotientGroup.congr _ _ ε.symm (OddCore.equiv_invariant ε.symm)).trans e'⟩

theorem liftsAt_z_of_conj {Y : Type} [Group Y] {t u e g : Y} (hgt : g * t * g⁻¹ = u * e)
    {M M' J J' : Subgroup Y}
    (hM : IsSectionMember3 (Subgroup.centralizer ({u} : Set Y)) M (u * e))
    (hM' : IsSectionMember3 (Subgroup.centralizer ({u} : Set Y)) M' (u * e))
    (hJM : conjSub g J ≤ M) (hJ'M' : conjSub g J' ≤ M')
    (hcomm : ∀ a ∈ M, ∀ b ∈ M', a * b = b * a) :
    IsSectionMember3 (Subgroup.centralizer ({g⁻¹ * u * g} : Set Y)) (conjSub g⁻¹ M) t ∧
    IsSectionMember3 (Subgroup.centralizer ({g⁻¹ * u * g} : Set Y)) (conjSub g⁻¹ M') t ∧
    J ≤ conjSub g⁻¹ M ∧ J' ≤ conjSub g⁻¹ M' ∧
    ∀ a ∈ conjSub g⁻¹ M, ∀ b ∈ conjSub g⁻¹ M', a * b = b * a := by
  have ht : g⁻¹ * (u * e) * g⁻¹⁻¹ = t := by
    rw [← hgt]; group
  have hcen : conjSub g⁻¹ (Subgroup.centralizer ({u} : Set Y)) =
      Subgroup.centralizer ({g⁻¹ * u * g} : Set Y) := by
    rw [conjSub_centralizer_singleton g⁻¹ u]; simp
  have h1 := isSectionMember3_conj_gen hM g⁻¹
  have h2 := isSectionMember3_conj_gen hM' g⁻¹
  rw [hcen, ht] at h1 h2
  refine ⟨h1, h2, ?_, ?_, ?_⟩
  · have := conjSub_mono (n := g⁻¹) hJM
    rwa [conjSub_inv_conjSub] at this
  · have := conjSub_mono (n := g⁻¹) hJ'M'
    rwa [conjSub_inv_conjSub] at this
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have := congrArg (fun x => g⁻¹ * x * g⁻¹⁻¹) (hcomm a ha b hb)
    simpa [mul_assoc] using this

end CFSG.ClassicalInvolution.Q3.Q3CH

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Balance

set_option linter.unusedSectionVars false


theorem p23_oddCoreIn_cu_cue_eq_bot {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} {K' W : Subgroup Y} {u e g : Y}
    (hD4 : TwinCentRes.ModelFactD42) (hT : TwinThmE.T4Supply) (hcit : CIT3Below n)
    (hP : TL4.TightBelowRPlus 3 n) (hc : P23Cfg n Y R S t K' W u e g)
    (hOu : oddCoreIn (Subgroup.centralizer ({u} : Set Y)) = ⊥) :
    oddCoreIn (Subgroup.centralizer ({u} : Set Y) ⊓ Subgroup.centralizer ({u * e} : Set Y)) = ⊥ :=
  TwinPairOdd.oddCoreIn_inf_centralizer_eq_bot (ue_comm_u hc) (ue_sq hc) (ue_ne_one hc) hOu
    (p23_movedOddFree_ue hD4 hT hcit hP hc).2

section FzFacts

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

@[expose] def twinCent (R : Subgroup Y) (K' : Subgroup Y) : Subgroup Y :=
  Subgroup.centralizer ((tightCore R ⊔ K' : Subgroup Y) : Set Y)

theorem twinCent_le_cu (hc : P23Cfg n Y R S t K' W u e g) :
    twinCent R K' ≤ Subgroup.centralizer ({u} : Set Y) := by
  refine Subgroup.centralizer_le ?_
  simpa using hc.data.hu

theorem twinCent_le_ct (hc : P23Cfg n Y R S t K' W u e g) :
    twinCent R K' ≤ Subgroup.centralizer ({t} : Set Y) := by
  have hC := CoreData.of_S hc.std.perp.core
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  refine Subgroup.centralizer_le ?_
  simpa using (le_sup_left : tightCore R ≤ tightCore R ⊔ K') hz.mem

theorem lc_conj_sup_le (hc : P23Cfg n Y R S t K' W u e g) {c : Y}
    (hct : c ∈ Subgroup.centralizer ({t} : Set Y)) :
    conjSub c (tightCore R ⊔ K') ≤ tightCore R ⊔ K' := by
  have hC := CoreData.of_S hc.std.perp.core
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hpair := twinSet_eq_pair hc.std.two hc.std.hK' hc.std.hne
  have hK0 : tightCore R ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) := by
    rw [hpair]; simp
  have h0 := conj_mem_twinSet hz hK0 hct
  have h1 := conj_mem_twinSet hz hc.std.hK' hct
  rw [hpair] at h0 h1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h0 h1
  rw [conjSub_sup]
  refine sup_le ?_ ?_
  · rcases h0 with h0 | h0 <;> rw [h0]
    · exact le_sup_left
    · exact le_sup_right
  · rcases h1 with h1 | h1 <;> rw [h1]
    · exact le_sup_left
    · exact le_sup_right

theorem conjSub_twinCent_le (hc : P23Cfg n Y R S t K' W u e g) {c : Y}
    (hct : c ∈ Subgroup.centralizer ({t} : Set Y)) :
    conjSub c (twinCent R K') ≤ twinCent R K' := by
  rintro _ ⟨y, hy, rfl⟩
  rw [twinCent, Subgroup.mem_centralizer_iff]
  intro k hk
  have hk' : c⁻¹ * k * c ∈ tightCore R ⊔ K' := by
    have hct' : c⁻¹ ∈ Subgroup.centralizer ({t} : Set Y) := Subgroup.inv_mem _ hct
    have := lc_conj_sup_le hc hct' ⟨k, hk, rfl⟩
    simpa using this
  have hyc := Subgroup.mem_centralizer_iff.mp hy (c⁻¹ * k * c) hk'
  show k * (c * y * c⁻¹) = c * y * c⁻¹ * k
  calc k * (c * y * c⁻¹) = c * ((c⁻¹ * k * c) * y) * c⁻¹ := by group
    _ = c * (y * (c⁻¹ * k * c)) * c⁻¹ := by rw [hyc]
    _ = c * y * c⁻¹ * k := by group

theorem conjSub_twinCent (hc : P23Cfg n Y R S t K' W u e g) {c : Y}
    (hct : c ∈ Subgroup.centralizer ({t} : Set Y)) :
    conjSub c (twinCent R K') = twinCent R K' := by
  refine le_antisymm (conjSub_twinCent_le hc hct) ?_
  have h := conjSub_mono (n := c) (conjSub_twinCent_le hc (Subgroup.inv_mem _ hct))
  rwa [conjSub_conjSub_inv] at h

theorem twinCent_oddCore_bot (hc : P23Cfg n Y R S t K' W u e g)
    (hodd : classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y)) = ⊥) :
    oddCoreIn (twinCent R K') = ⊥ := by
  have hOt : oddCoreIn (Subgroup.centralizer ({t} : Set Y)) = ⊥ :=
    TwinConnT.oddCoreIn_eq_bot_of_classicalOddCore hodd
  have hD : oddCoreIn (twinCent R K') ≤ oddCoreIn (Subgroup.centralizer ({t} : Set Y)) := by
    refine le_oddCoreIn_of_normalizes ((oddCoreIn_le _).trans (twinCent_le_ct hc)) ?_
      (odd_card_oddCoreIn _)
    intro c hct
    have hfwd : ∀ c ∈ Subgroup.centralizer ({t} : Set Y), ∀ x ∈ oddCoreIn (twinCent R K'),
        c * x * c⁻¹ ∈ oddCoreIn (twinCent R K') := by
      intro c hct x hx
      refine TwinExitPf14.normalizes_oddCoreIn (H := twinCent R K') (g := c) ?_ ?_ hx
      · intro h hh
        have := conjSub_twinCent hc hct
        rw [← this]
        exact ⟨h, hh, rfl⟩
      · intro h hh
        have h1 := conj_mem_conjSub (n := c⁻¹) hh
        rw [conjSub_twinCent hc (Subgroup.inv_mem _ hct)] at h1
        simpa using h1
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hfwd c hct h, fun hh => ?_⟩
    have := hfwd c⁻¹ (Subgroup.inv_mem _ hct) _ hh
    simpa [mul_assoc] using this
  exact le_bot_iff.mp (hD.trans hOt.le)

end FzFacts

section Twins

open CFSG.ClassicalInvolution.Balance

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem lc_members_q8 (hP : TL4.TightBelowRPlus 3 n) (hc : P23Cfg n Y R S t K' W u e g)
    (hno : SecNoExit R e) (hα : alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥) :
    ∀ J ∈ Om R, Nonempty (↥J ≃* QuaternionGroup 2) := by
  have hC := CoreData.of_S hc.std.perp.core
  have h2 := p23_members_isPGroup hP hc hno hα
  have hq8 := q8_conjClass (hC.datum.exists_sylow_q8 hC.q8)
  intro J hJ
  exact hq8 J hJ J ⟨le_rfl, h2 J hJ, fun V' h1 _ h3 => le_antisymm h1 h3⟩

theorem lc_card_eq_eight {J : Subgroup Y} (h : Nonempty (↥J ≃* QuaternionGroup 2)) :
    Nat.card ↥J = 8 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  simp [QuaternionGroup.card]

theorem lc_twins_commute (hP : TL4.TightBelowRPlus 3 n) (hc : P23Cfg n Y R S t K' W u e g)
    (hno : SecNoExit R e) (hα : alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥) :
    ∀ k ∈ tightCore R, ∀ k' ∈ K', k * k' = k' * k := by
  have hC := CoreData.of_S hc.std.perp.core
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  exact OddQuot.commutes_of_twin_pgroup hC.hyp (p23_members_isPGroup hP hc hno hα)
    (CoreAssembly.mem_conjClass_self _) hc.std.hK'.1 hc.std.hne.symm hz hz'

theorem lc_perm (hc : P23Cfg n Y R S t K' W u e g) {c : Y}
    (hct : c ∈ Subgroup.centralizer ({t} : Set Y)) :
    (conjSub c (tightCore R) = tightCore R ∨ conjSub c (tightCore R) = K') ∧
    (conjSub c K' = tightCore R ∨ conjSub c K' = K') := by
  have hC := CoreData.of_S hc.std.perp.core
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hpair := twinSet_eq_pair hc.std.two hc.std.hK' hc.std.hne
  have hK0 : tightCore R ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) := by
    rw [hpair]; simp
  have h0 := conj_mem_twinSet hz hK0 hct
  have h1 := conj_mem_twinSet hz hc.std.hK' hct
  rw [hpair] at h0 h1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h0 h1
  exact ⟨h0, h1⟩

theorem lc_oddCore_twinCent (hc : P23Cfg n Y R S t K' W u e g)
    (hodd : classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y)) = ⊥) :
    oddCore ↥(twinCent R K') = ⊥ :=
  TwinConnT.classicalOddCore_eq_bot_of_oddCoreIn (twinCent_oddCore_bot hc hodd)

end Twins

section Generic

open scoped MatrixGroups

variable {G : Type} [Group G]

theorem lc_oddCore_conj {X : Subgroup G} (n : G) (h : classicalInvolutionOddCore ↥X = ⊥) :
    classicalInvolutionOddCore ↥(conjSub n X) = ⊥ := by
  let ε : ↥X ≃* ↥(conjSub n X) :=
    Subgroup.equivMapOfInjective X (MulAut.conj n).toMonoidHom (MulAut.conj n).injective
  have hO : (classicalInvolutionOddCore ↥X).map ε.toMonoidHom =
      classicalInvolutionOddCore ↥(conjSub n X) :=
    CFSG.ComponentClassification.OddCore.equiv_invariant ε
  rw [← hO, h, Subgroup.map_bot]

theorem lc_equiv_sl2 {Y K : Subgroup G} {z : G} (h : Q3NL.IsSectionMember3 Y K z)
    (hO : classicalInvolutionOddCore ↥K = ⊥) : Nonempty (↥K ≃* SL(2, ZMod 3)) := by
  obtain ⟨e⟩ := h.nonempty_equiv
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot).symm.trans e⟩

end Generic

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
