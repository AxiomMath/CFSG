module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173UniCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentType
import CFSG.GH74.Generic.S1.RCard
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusEightBasic
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentPrim

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.T173U

open Polynomial Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.SeitzGeneration
  CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary
  CFSG.GroupTheory.WeirSylow CFSG.Open CFSG.Yardstones.Md0ec50421ce4
  CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ} {k : ℕ} {U : Fin k → Submodule F V}

private theorem orthDerived_eq_elementaryGroup_minus_six_aux1 {Q : QuadraticForm F V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hdim : Module.finrank F V = 6) :
    elementaryGroup Q ≤ orthDerived Q := by
  refine elementaryGroup_le_of_eichler_mem fun u w hu huw => ?_
  by_cases hu0 : u = 0
  · rw [hu0, eichler_zero_left]
    exact Subgroup.one_mem _
  by_cases hw : ∃ c : F, w = c • u
  · obtain ⟨c, rfl⟩ := hw
    rw [show c • u = 0 + c • u by rw [zero_add], eichler_add_smul_self hu 0 c,
      eichler_zero_right]
    exact Subgroup.one_mem _
  · obtain ⟨P, hPe⟩ := exists_hypPair hQ hu hu0
    have hwe : polar Q w P.e = 0 := by rw [hPe, polar_comm]; exact huw
    have hproj : P.proj w = w - polar Q w P.f • P.e := by
      rw [HypPair.proj, hwe, zero_smul, sub_zero]
    have hw' : w = P.proj w + polar Q w P.f • P.e := by rw [hproj]; abel
    have hmem : P.proj w ∈ P.perp := P.proj_mem_perp w
    have hΩ : eichler Q P.e (P.proj w) ∈ orthDerived Q :=
      eichler_mem_orthDerived_of_regular hQ (by omega) (by intro _ h4; omega) P hmem
    have hwne : P.proj w ≠ 0 := by
      intro h0
      apply hw
      exact ⟨polar Q w P.f, by simpa [h0, hPe] using hw'⟩
    have hgoal : eichler Q u (P.proj w + polar Q w P.f • P.e) =
        eichler Q P.e (P.proj w) := by
      rw [← hPe, eichler_add_smul_self P.Q_e (P.proj w) (polar Q w P.f)]
    rw [hw', hgoal]
    exact hΩ

private theorem orthDerived_eq_elementaryGroup_minus_six_aux2 {Q : QuadraticForm F V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hdim : Module.finrank F V = 6) :
    elementaryGroup Q ≠ ⊥ := by
  obtain ⟨u, -, hu0, hu⟩ := CFSG.ComponentClassification.UnbalancedCatalog.exists_singular_of_three_le (Q := Q) (S := ⊤)
    (polarNondegOn_top hQ) (by rw [finrank_top, hdim]; omega)
  have hpu : polarBilin Q u ≠ 0 := by
    intro h0
    apply hu0
    exact hQ.2 u fun x => by
      rw [polarBilin_apply_apply, polar_comm]
      exact congrArg (fun f => f x) h0
  have hker : Module.finrank F (LinearMap.ker (polarBilin Q u)) = 5 := by
    have := Module.Dual.finrank_ker_add_one_of_ne_zero (f := polarBilin Q u) hpu
    omega
  have hnotle : ¬ LinearMap.ker (polarBilin Q u) ≤ Submodule.span F {u} := by
    intro hle
    have h1 := Submodule.finrank_mono hle
    have h2 : Module.finrank F (Submodule.span F {u}) = 1 := finrank_span_singleton hu0
    omega
  obtain ⟨w, hwker, hwspan⟩ := Set.not_subset.mp hnotle
  have huw : polar Q u w = 0 := by
    simpa [polarBilin_apply_apply] using LinearMap.mem_ker.mp hwker
  have hene : eichler Q u w ≠ 1 := by
    intro he
    obtain ⟨x, hx⟩ : ∃ x, polar Q x u ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hu0 (hQ.2 u fun y => by
        simpa [polarBilin_apply_apply, polar_comm] using hcon y)
    have h1 : eichler Q u w x = x := by rw [he]; rfl
    rw [eichler_apply hu huw] at h1
    have h2 : polar Q x u • w = (polar Q x w + Q w * polar Q x u) • u := by
      have h4 : polar Q x u • w - (polar Q x w + Q w * polar Q x u) • u = 0 := by
        have := congrArg (fun z => z - x) h1
        simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using this
      exact sub_eq_zero.mp h4
    apply hwspan
    refine Submodule.mem_span_singleton.mpr
      ⟨(polar Q x u)⁻¹ * (polar Q x w + Q w * polar Q x u), ?_⟩
    rw [mul_smul, ← h2, smul_smul, inv_mul_cancel₀ hx, one_smul]
  intro hbot
  have := eichler_mem_elementaryGroup Q u w
  rw [hbot, Subgroup.mem_bot] at this
  exact hene this

theorem orthDerived_eq_elementaryGroup_minus_six (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : Module.finrank F V = 6) (hminus : ¬ IsPlusType Q) :
    orthDerived Q = elementaryGroup Q := by
  have hts : ∀ U : Submodule F V, Module.finrank F U = 3 → ∃ u ∈ U, Q u ≠ 0 := by
    intro U hU
    by_contra hcon
    push Not at hcon
    exact hminus ⟨U, by rw [hU, hdim], hcon⟩
  have hle := orthDerived_eq_elementaryGroup_minus_six_aux1 hQ hdim
  have hne := orthDerived_eq_elementaryGroup_minus_six_aux2 hQ hdim
  have hsimple := (CFSG.RankThree.PartOne.even_minus_four_six_actual_derived_extraction Q hQ
    (Or.inr hdim) fun U hU => hts U (by rw [hdim] at hU; omega)).1
  have hnormal : ((elementaryGroup Q).subgroupOf (orthDerived Q)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hle]
    intro h k hh hk
    exact conj_mem_elementaryGroup (Subgroup.commutator_le_self _ hk) hh
  rcases hsimple.eq_bot_or_eq_top_of_normal
    ((elementaryGroup Q).subgroupOf (orthDerived Q)) with h | h
  · exact absurd (Disjoint.eq_bot_of_le (Subgroup.subgroupOf_eq_bot.mp h) hle) hne
  · exact le_antisymm (Subgroup.subgroupOf_eq_top.mp h) hle

theorem orthDerived_eq_elementaryGroup_of_three_le (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {m : ℕ} (hm : 3 ≤ m) (hdim : Module.finrank F V = 2 * m) :
    orthDerived Q = elementaryGroup Q := by
  by_cases hplus : IsPlusType Q
  · exact (CFSG.RankThree.Classical.orthDerived_eq_and_le_closure hQ
      (exists_threeSingular hQ hdim (Or.inl ⟨hplus, hm⟩))).1
  · by_cases hm4 : 4 ≤ m
    · exact (CFSG.RankThree.Classical.orthDerived_eq_and_le_closure hQ
        (exists_threeSingular hQ hdim (Or.inr ⟨hplus, hm4⟩))).1
    · have hm3 : m = 3 := by omega
      subst hm3
      exact orthDerived_eq_elementaryGroup_minus_six hQ (by omega) hplus

theorem eichlerGroupOn_eq_map_orthDerived {W : Submodule F V} (hW : PolarNondegOn Q W) {m : ℕ}
    (hm : 3 ≤ m) (hdim : Module.finrank F W = 2 * m) :
    eichlerGroupOn Q W = (orthDerived (Q.comp W.subtype)).map (OrthNS.extU hW) := by
  have hE := orthDerived_eq_elementaryGroup_of_three_le (nondegenerate_comp_subtype hW) hm hdim
  apply le_antisymm
  · refine eichlerGroupOn_le fun e he w hw => ?_
    refine ⟨eichler (Q.comp W.subtype) ⟨e, he⟩ ⟨w, hw⟩, ?_, OrthNS.extU_eichler hW ⟨e, he⟩ ⟨w, hw⟩⟩
    rw [hE]
    exact eichler_mem_elementaryGroup _ _ _
  · rintro _ ⟨a, ha, rfl⟩
    rw [hE] at ha
    exact OrthNS.extU_mem_eichlerGroupOn hW ha

theorem conj_mem_eichlerGroupOn {W : Submodule F V} {g : V ≃ₗ[F] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hgW : ∀ x ∈ W, g x ∈ W)
    {y : V ≃ₗ[F] V} (hy : y ∈ eichlerGroupOn Q W) : g * y * g⁻¹ ∈ eichlerGroupOn Q W := by
  have hle : eichlerGroupOn Q W ≤ (eichlerGroupOn Q W).comap (MulAut.conj g).toMonoidHom := by
    refine eichlerGroupOn_le fun e he w hw => ?_
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, eichler_conj hg]
    exact eichler_mem_eichlerGroupOn (hgW e he) (hgW w hw)
  exact hle hy

theorem eichlerGroupOn_le_iSup_specialBlock (hk : 3 ≤ k) (hU : IsPlaneSystem Q U) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) {d : V ≃ₗ[F] V} (hd : OddOrderIsometry Q p d)
    (hmaps : ∀ j, ∀ x ∈ U j, d x ∈ U j) (hfix : ∀ x ∈ polarPerp Q (⨆ j, U j), d x = x)
    {h : F[X]} (hh : h ∈ primaryFactors d.toLinearMap) (hh1 : h ≠ X - 1)
    (hUh : ∀ j, U j ≤ primaryComponent d.toLinearMap h) :
    eichlerGroupOn Q (⨆ j, U j) ≤ ⨆ d' ∈ {d' : V ≃ₗ[F] V | IsEvenFlip Q U d d'}, specialBlock Q d' h :=
  eichlerGroupOn_le (eichler_mem_iSup_specialBlock hk hU hp hp2 hpq hd hmaps hfix hh hh1 hUh)

theorem orthDerived_le_iSup_specialBlock (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hk : 3 ≤ k)
    (hU : IsPlaneSystem Q U) (htop : (⨆ j, U j : Submodule F V) = ⊤) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {d : V ≃ₗ[F] V} (hd : OddOrderIsometry Q p d)
    (hmaps : ∀ j, ∀ x ∈ U j, d x ∈ U j) {h : F[X]} (hh : h ∈ primaryFactors d.toLinearMap)
    (hh1 : h ≠ X - 1) (hUh : ∀ j, U j ≤ primaryComponent d.toLinearMap h) :
    orthDerived Q ≤ ⨆ d' ∈ {d' : V ≃ₗ[F] V | IsEvenFlip Q U d d'}, specialBlock Q d' h := by
  have hdim : Module.finrank F V = 2 * k := by
    have h1 := hU.finrank_biSup (Finset.univ : Finset (Fin k))
    have e : (⨆ j ∈ (Finset.univ : Finset (Fin k)), U j) = ⊤ := by
      rw [← htop]; simp
    rw [e] at h1
    simpa [Finset.card_univ, Fintype.card_fin] using h1
  have hfix : ∀ x ∈ polarPerp Q (⨆ j, U j), d x = x := by
    intro x hx
    rw [htop] at hx
    have : x = 0 := by
      refine eq_zero_of_polar_eq_zero hQ fun y => ?_
      have := (mem_polarPerp_iff.1 hx) y Submodule.mem_top
      rw [polar_comm]
      exact this
    rw [this, map_zero]
  rw [orthDerived_eq_elementaryGroup_of_three_le hQ hk hdim]
  refine elementaryGroup_le_of_eichler_mem fun u w _ _ => ?_
  exact eichler_mem_iSup_specialBlock hk hU hp hp2 hpq hd hmaps hfix hh hh1 hUh u
    (by rw [htop]; exact Submodule.mem_top) w (by rw [htop]; exact Submodule.mem_top)

private theorem specialBlock_le_eichlerGroupOn_aux1 (hU : IsPlaneSystem Q U) {d : V ≃ₗ[F] V}
    {h : F[X]} (hfix : ∀ x ∈ polarPerp Q (⨆ j, U j), d x = x)
    (hh : h ∈ primaryFactors d.toLinearMap) (hh1 : h ≠ X - 1)
    (hUh : ∀ j, U j ≤ primaryComponent d.toLinearMap h) :
    primaryComponent d.toLinearMap h = ⨆ j, U j := by
  have hle : (⨆ j, U j) ≤ primaryComponent d.toLinearMap h := iSup_le hUh
  refine le_antisymm ?_ hle
  intro x hx
  have hxsup : x ∈ (⨆ j, U j) ⊔ polarPerp Q (⨆ j, U j) := by
    rw [hU.isCompl_iSup.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨w, hw, r, hr, rfl⟩ := Submodule.mem_sup.mp hxsup
  have hwV : w ∈ primaryComponent d.toLinearMap h := hle hw
  have hrV : r ∈ primaryComponent d.toLinearMap h := by
    have h := Submodule.sub_mem (primaryComponent d.toLinearMap h) hx hwV
    simpa using h
  have hr0 : r = 0 := eq_zero_of_mem_primaryComponent_of_apply_eq hh hh1 hrV (hfix r hr)
  rw [hr0, add_zero]
  exact hw

private theorem specialBlock_le_eichlerGroupOn_aux2 (hU : IsPlaneSystem Q U) (hp : p.Prime)
    (hpq : p ∣ Nat.card F + 1) {d : V ≃ₗ[F] V} (hd : OddOrderIsometry Q p d) {h : F[X]}
    (hh : h ∈ primaryFactors d.toLinearMap) (hh1 : h ≠ X - 1)
    (hVh : primaryComponent d.toLinearMap h = ⨆ j, U j) :
    polarPerp Q (⨆ j, U j) ≤ othersSpace d.toLinearMap h := by
  have hself := hd.reciprocal_eq_of_dvd_card_succ hp hpq hh hh1
  have horbit : orbitSpace d.toLinearMap h = ⨆ j, U j := by
    rw [orbitSpace, hself, sup_idem]
    exact hVh
  have hcompl : IsCompl (⨆ j, U j) (othersSpace d.toLinearMap h) := by
    rw [← horbit]
    exact hd.isCompl_orbit_others hh
  have hothers_le : othersSpace d.toLinearMap h ≤ polarPerp Q (⨆ j, U j) := by
    intro r hr
    rw [mem_polarPerp_iff]
    intro y hy
    exact hd.polar_orbit_others hh (by rw [horbit]; exact hy) hr
  intro r hr
  have hsup : r ∈ (⨆ j, U j) ⊔ othersSpace d.toLinearMap h := by
    rw [hcompl.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨w, hw, s, hs, rfl⟩ := Submodule.mem_sup.mp hsup
  have hwperp : w ∈ polarPerp Q (⨆ j, U j) := by
    have hsub := Submodule.sub_mem (polarPerp Q (⨆ j, U j)) hr (hothers_le hs)
    simpa using hsub
  have hw0 : w = 0 := by
    have hmem : w ∈ (⨆ j, U j) ⊓ polarPerp Q (⨆ j, U j) := Submodule.mem_inf.mpr ⟨hw, hwperp⟩
    rw [disjoint_iff.mp hU.isCompl_iSup.disjoint] at hmem
    simpa using hmem
  rw [hw0, zero_add]
  exact hs

private theorem specialBlock_le_eichlerGroupOn_aux3 (hk : 3 ≤ k) {W : Submodule F V}
    {d : V ≃ₗ[F] V} {h : F[X]} (hW : PolarNondegOn Q W)
    (hdimW : Module.finrank F W = 2 * k) (hperf : Group.IsPerfect ↥(specialBlock Q d h))
    (hmapsW : ∀ g : ↥(specialBlock Q d h), ∀ x ∈ W, (g : V ≃ₗ[F] V) x ∈ W)
    (hfixperp : ∀ g : ↥(specialBlock Q d h), ∀ x ∈ polarPerp Q W, (g : V ≃ₗ[F] V) x = x) :
    specialBlock Q d h ≤ eichlerGroupOn Q W := by
  haveI : Group.IsPerfect ↥(specialBlock Q d h) := hperf
  let φ : ↥(specialBlock Q d h) →* (W ≃ₗ[F] W) :=
    MonoidHom.mk' (fun g => restrictEquiv W (g : V ≃ₗ[F] V)
      (fun u hu => hmapsW g u hu) (fun u hu => by simpa using hmapsW g⁻¹ u hu))
      (fun g g' => by
        refine LinearEquiv.ext fun u => Subtype.ext ?_
        rfl)
  have hφcoe : ∀ (g : ↥(specialBlock Q d h)) (u : W),
      ((φ g u : W) : V) = (g : V ≃ₗ[F] V) (u : V) := fun g u => rfl
  have hleO : φ.range ≤ TauCeti.QuadraticMap.orthogonalGroup (Q.comp W.subtype) := by
    rintro _ ⟨g, rfl⟩
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro u
    have hgs : (g : V ≃ₗ[F] V) ∈ supportedBlock Q d h := (mem_specialBlock.mp g.2).1
    have hic : (g : V ≃ₗ[F] V) ∈ isometryCentralizer Q d := (mem_supportedBlock.mp hgs).1
    have hQpres : ∀ v : V, Q ((g : V ≃ₗ[F] V) v) = Q v :=
      (mem_isometryCentralizer.mp hic).1
    simp only [QuadraticMap.comp_apply, Submodule.coe_subtype]
    rw [hφcoe g u]
    simpa using hQpres (u : V)
  have him : φ.range ≤ orthDerived (Q.comp W.subtype) := by
    have hcomm : ⁅φ.range, φ.range⁆ = φ.range :=
      Subgroup.isPerfect_iff.mp (Group.IsPerfect.range (f := φ))
    calc φ.range = ⁅φ.range, φ.range⁆ := hcomm.symm
      _ ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup (Q.comp W.subtype),
            TauCeti.QuadraticMap.orthogonalGroup (Q.comp W.subtype)⁆ :=
          Subgroup.commutator_mono hleO hleO
      _ = orthDerived (Q.comp W.subtype) := rfl
  intro g hg
  have hmem : φ ⟨g, hg⟩ ∈ orthDerived (Q.comp W.subtype) :=
    him (MonoidHom.mem_range.mpr ⟨⟨g, hg⟩, rfl⟩)
  have heich : OrthNS.extU hW (φ ⟨g, hg⟩) ∈ eichlerGroupOn Q W := by
    rw [eichlerGroupOn_eq_map_orthDerived hW hk hdimW]
    exact Subgroup.mem_map.mpr ⟨φ ⟨g, hg⟩, hmem, rfl⟩
  have hagree : OrthNS.extU hW (φ ⟨g, hg⟩) = g := by
    refine OrthNS.extU_eq_of_agree hW (fun u => (hφcoe ⟨g, hg⟩ u).symm) (fun r hr => ?_)
    exact hfixperp ⟨g, hg⟩ r hr
  rwa [hagree] at heich

theorem specialBlock_le_eichlerGroupOn (hk : 3 ≤ k) (hU : IsPlaneSystem Q U) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) {d : V ≃ₗ[F] V} (hd : OddOrderIsometry Q p d)
    (hmaps : ∀ j, ∀ x ∈ U j, d x ∈ U j) (hfix : ∀ x ∈ polarPerp Q (⨆ j, U j), d x = x)
    {h : F[X]} (hh : h ∈ primaryFactors d.toLinearMap) (hh1 : h ≠ X - 1)
    (hUh : ∀ j, U j ≤ primaryComponent d.toLinearMap h)
    (hperf : Group.IsPerfect ↥(specialBlock Q d h)) :
    specialBlock Q d h ≤ eichlerGroupOn Q (⨆ j, U j) := by
  set W : Submodule F V := ⨆ j, U j with hWdef
  have hVh0 : primaryComponent d.toLinearMap h = ⨆ j, U j :=
    specialBlock_le_eichlerGroupOn_aux1 hU hfix hh hh1 hUh
  have hVh : primaryComponent d.toLinearMap h = W := hVh0.trans hWdef.symm
  have hW : PolarNondegOn Q W := by
    rw [hWdef]
    exact polarNondegOn_iSup_of_isPlaneSystem hU
  have hperp_le : polarPerp Q W ≤ othersSpace d.toLinearMap h := by
    rw [hWdef]
    exact specialBlock_le_eichlerGroupOn_aux2 hU hp hpq hd hh hh1 hVh0
  have hdimW : Module.finrank F W = 2 * k := by
    rw [hWdef]
    have h1 := hU.finrank_biSup (Finset.univ : Finset (Fin k))
    have e : (⨆ j ∈ (Finset.univ : Finset (Fin k)), U j) = ⨆ j, U j := by simp
    rw [e] at h1
    simpa [Finset.card_univ, Fintype.card_fin] using h1
  have hmapsW : ∀ g : ↥(specialBlock Q d h), ∀ x ∈ W, (g : V ≃ₗ[F] V) x ∈ W := by
    intro g x hx
    have hgs : (g : V ≃ₗ[F] V) ∈ supportedBlock Q d h := (mem_specialBlock.mp g.2).1
    have hic : (g : V ≃ₗ[F] V) ∈ isometryCentralizer Q d := (mem_supportedBlock.mp hgs).1
    have hcomm : Commute (g : V ≃ₗ[F] V).toLinearMap d.toLinearMap := by
      ext v
      exact (mem_isometryCentralizer.mp hic).2 v
    have hx' : x ∈ primaryComponent d.toLinearMap h := by rw [hVh]; exact hx
    have hmem := apply_mem_primaryComponent hcomm hx'
    rwa [hVh] at hmem
  have hfixperp : ∀ g : ↥(specialBlock Q d h), ∀ x ∈ polarPerp Q W,
      (g : V ≃ₗ[F] V) x = x := by
    intro g x hx
    have hgs : (g : V ≃ₗ[F] V) ∈ supportedBlock Q d h := (mem_specialBlock.mp g.2).1
    exact (mem_supportedBlock.mp hgs).2 x (hperp_le hx)
  exact specialBlock_le_eichlerGroupOn_aux3 hk hW hdimW hperf hmapsW hfixperp

theorem catalogIs_pSimple_subgroupOf_eichlerGroupOn {W : Submodule F V} (hW : PolarNondegOn Q W)
    {m : ℕ} (hm : 3 ≤ m) (hdim : Module.finrank F W = 2 * m)
    (hle : eichlerGroupOn Q W ≤ orthDerived Q) {Q₁ : TauCeti.CFSGIndex → Prop}
    (h : catalogIs (PSimple p (⊤ : Subgroup ↥(orthDerived (Q.comp W.subtype)))) Q₁) :
    catalogIs (PSimple p ((eichlerGroupOn Q W).subgroupOf (orthDerived Q))) Q₁ := by
  have h3 := eichlerGroupOn_eq_map_orthDerived hW hm hdim
  let e : ↥((eichlerGroupOn Q W).subgroupOf (orthDerived Q)) ≃*
      ↥(⊤ : Subgroup ↥(orthDerived (Q.comp W.subtype))) :=
    (Subgroup.subgroupOfEquivOfLe hle).trans
      ((MulEquiv.subgroupCongr h3).trans
        ((Subgroup.equivMapOfInjective _ _ (OrthNS.extU_injective hW)).symm.trans
          Subgroup.topEquiv.symm))
  exact (S172B.Cent.catalogIs_pSimple_congr_mulEquiv e p Q₁).2 h

private theorem catalogIs_pSimple_top_orthDerived_minus_three_aux1 {f : ℕ} {E : Type} [Field E]
    [Finite E] (hE : Nat.card E = (2 ^ f) ^ 2) {p : ℕ} (hpq : p ∣ 2 ^ f + 1) :
    p ∣ Nat.card ↥(StatedSU 4 (2 ^ f) E) := by
  obtain ⟨p0, f0, hU, hq0⟩ := CFSG.GH74.Generic.S1.rcard_exists_unitaryFieldData hE
  have hcard := CFSG.GH74.Generic.S1.rcard_card_statedSU hU (n := 4) (by norm_num)
  have hpZ : (p : ℤ) ∣ (((p0 ^ f0 : ℕ) : ℤ) + 1) := by
    have := hpq
    rw [hq0] at this
    exact_mod_cast this
  have hfac : (p : ℤ) ∣ ((((p0 ^ f0 : ℕ) : ℤ) ^ 2) - (-1 : ℤ) ^ 2) := by
    obtain ⟨k, hk⟩ := hpZ
    refine ⟨k * ((((p0 ^ f0 : ℕ) : ℤ) - 1)), ?_⟩
    have h : ((((p0 ^ f0 : ℕ) : ℤ) ^ 2) - (-1 : ℤ) ^ 2) =
        ((((p0 ^ f0 : ℕ) : ℤ) + 1) * ((((p0 ^ f0 : ℕ) : ℤ) - 1))) := by ring
    rw [h, hk]
    ring
  have hmem : 2 ∈ Finset.Icc 2 4 := by norm_num
  have hdvdInt : (p : ℤ) ∣ (Nat.card ↥(StatedSU 4 (2 ^ f) E) : ℤ) := by
    rw [hq0, hcard]
    exact Dvd.dvd.mul_left (dvd_trans (by simpa only [Nat.cast_pow] using hfac)
      (Finset.dvd_prod_of_mem (fun i : ℕ =>
        (((p0 ^ f0 : ℕ) : ℤ) ^ i - (-1 : ℤ) ^ i)) hmem)) _
  exact_mod_cast hdvdInt

private theorem catalogIs_pSimple_top_orthDerived_minus_three_aux2 {f : ℕ} {E : Type} [Field E]
    [Finite E] (hE : Nat.card E = (2 ^ f) ^ 2) :
    CFSG.IsQuasisimple ↥(StatedSU 4 (2 ^ f) E) := by
  have hnq : (4, 2 ^ f) ≠ (3, 2) := by
    intro h
    exact absurd (congrArg Prod.fst h) (by norm_num)
  exact (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    (p := 2) (f := f) (F := E) (n := 4) hE (by norm_num) hnq).1

private theorem catalogIs_pSimple_top_orthDerived_minus_three_aux3 {f p : ℕ} {E : Type}
    [Field E] [Finite E] (hE : Nat.card E = (2 ^ f) ^ 2) (hp : p.Prime)
    (hpq : p ∣ 2 ^ f + 1) :
    catalogIs (PSimple p (⊤ : Subgroup ↥(StatedSU 4 (2 ^ f) E))) (isOmMA 3 (2 ^ f)) := by
  have hdvd : p ∣ Nat.card ↥(StatedSU 4 (2 ^ f) E) :=
    catalogIs_pSimple_top_orthDerived_minus_three_aux1 hE hpq
  have hqTopC : CFSG.IsQuasisimple ↥(⊤ : Subgroup ↥(StatedSU 4 (2 ^ f) E)) :=
    CFSG.IsQuasisimple.of_mulEquiv
      (Subgroup.topEquiv (G := ↥(StatedSU 4 (2 ^ f) E)))
      (catalogIs_pSimple_top_orthDerived_minus_three_aux2 hE)
  have hqTop : CFSG.Open.IsQuasisimple ↥(⊤ : Subgroup ↥(StatedSU 4 (2 ^ f) E)) :=
    ⟨@Group.IsPerfect.commutator_eq_top _ _ hqTopC.1, hqTopC.2.1⟩
  have hJ := H81Orth.centerQuotEquivPSimple_of_dvd_card (G := ↥(StatedSU 4 (2 ^ f) E))
    hp (J := ⊤) hqTop (by rwa [Subgroup.card_top])
  let eTop : ↥(⊤ : Subgroup (StatedSU 4 (2 ^ f) E)) ⧸
      Subgroup.center ↥(⊤ : Subgroup (StatedSU 4 (2 ^ f) E)) ≃*
      ↥(StatedSU 4 (2 ^ f) E) ⧸ Subgroup.center ↥(StatedSU 4 (2 ^ f) E) :=
    QuotientGroup.congr _ _ (Subgroup.topEquiv (G := ↥(StatedSU 4 (2 ^ f) E)))
      (Subgroup.map_center_eq (Subgroup.topEquiv (G := ↥(StatedSU 4 (2 ^ f) E))))
  haveI : Fintype E := Fintype.ofFinite E
  have hK : Fintype.card E = (2 ^ f) ^ 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hE
  obtain ⟨q', hv, -, hq'c, ⟨χ⟩⟩ :=
    CFSG.Adapters.CatalogueFieldBridges.exists_twistedA_mulEquiv_centerQuotient_statedSU
      (K := E) (m := 4) (q := 2 ^ f) hK (by norm_num) (by
        intro h
        exact absurd (congrArg Prod.fst h) (by norm_num))
  let i : TauCeti.CFSGIndex := .lie ⟨.twistedA 3 q', hv⟩
  have hi : isOmMA 3 (2 ^ f) i := Or.inr ⟨rfl, rfl, hq'c⟩
  exact ⟨i, hi, ⟨(hJ.symm.trans eTop).trans χ⟩⟩

theorem catalogIs_pSimple_top_orthDerived_minus_three {R : QuadraticForm F V}
    (hR : (QuadraticMap.polarBilin R).Nondegenerate) (hdim : Module.finrank F V = 6)
    (hminus : ¬ IsPlusType R) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) :
    catalogIs (PSimple p (⊤ : Subgroup ↥(orthDerived R))) (isOmMA 3 (Nat.card F)) := by
  classical
  obtain ⟨f, -, hf⟩ := exists_natCard_eq_two_pow F
  have hpq' : p ∣ 2 ^ f + 1 := by rwa [hf] at hpq
  have hts : ∀ U : Submodule F V, Module.finrank F U = 3 → ∃ u ∈ U, R u ≠ 0 := by
    intro U hU
    by_contra hcon
    push Not at hcon
    exact hminus ⟨U, by rw [hU, hdim], hcon⟩
  obtain ⟨E, hEfield, hEfin, hEcard, ⟨θ⟩⟩ :=
    CFSG.SeitzReduction.OmegaPilot.nonempty_orthDerived_mulEquiv_statedSU_of_six hf hR hdim hts
  letI instE : Field E := hEfield
  letI instFin : Finite E := hEfin
  have hθ : ↥(orthDerived R) ≃* ↥(StatedSU 4 (2 ^ f) E) := θ
  have hcatSU := catalogIs_pSimple_top_orthDerived_minus_three_aux3 hEcard hp hpq'
  let e := (Subgroup.topEquiv (G := ↥(orthDerived R))).trans
      (hθ.trans (Subgroup.topEquiv (G := ↥(StatedSU 4 (2 ^ f) E))).symm)
  have hmain := (S172B.Cent.catalogIs_pSimple_congr_mulEquiv e p (isOmMA 3 (2 ^ f))).2 hcatSU
  simpa [hf] using hmain

end CFSG.LocalAnalysis.GLTheoremA.T173U

end
