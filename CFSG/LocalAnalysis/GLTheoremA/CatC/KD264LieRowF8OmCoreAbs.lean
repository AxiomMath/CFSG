module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1OmCFinal

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Om

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.Open CFSG.GroupTheory.WeirSylow
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC
open scoped commutatorElement

local notation "Ω[" Q "]" =>
  ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆

section Plane

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

theorem rot_mem_planeSpan {p : V × V} (h : MinusPair Q p.1 p.2) {x : V} (hx : x ∈ planeSpan p) :
    rot Q p.1 p.2 x ∈ planeSpan p := by
  have h1 : rot Q p.1 p.2 x - x ∈ planeSpan p := rot_sub_mem_span h x
  have : rot Q p.1 p.2 x = (rot Q p.1 p.2 x - x) + x := by abel
  rw [this]
  exact Submodule.add_mem _ h1 hx

theorem exists_rot_sub_eq_mem {p : V × V} (h : MinusPair Q p.1 p.2) {y : V}
    (hy : y ∈ planeSpan p) : ∃ x ∈ planeSpan p, rot Q p.1 p.2 x - x = y := by
  have ha : rot Q p.1 p.2 p.2 - p.2 = p.1 := by rw [rot_apply_right h]; abel
  have hb : rot Q p.1 p.2 (p.1 + p.2) - (p.1 + p.2) = p.2 := by
    rw [map_add, rot_apply_left h, rot_apply_right h]
    abel
  obtain ⟨c, d, rfl⟩ := (mem_planeSpan_iff p y).1 hy
  refine ⟨c • p.2 + d • (p.1 + p.2), ?_, ?_⟩
  · exact Submodule.add_mem _ (Submodule.smul_mem _ _ (right_mem_planeSpan p))
      (Submodule.smul_mem _ _ (Submodule.add_mem _ (left_mem_planeSpan p) (right_mem_planeSpan p)))
  · rw [map_add, map_smul, map_smul]
    linear_combination (norm := module) c • ha + d • hb

theorem polar_planeSpan_of_pairPerp {p q : V × V} (h : PairPerp Q p q) {x : V}
    (hx : x ∈ planeSpan p) : polar Q x q.1 = 0 ∧ polar Q x q.2 = 0 := by
  obtain ⟨c, d, rfl⟩ := (mem_planeSpan_iff p x).1 hx
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_⟩
  · rw [polar_add_left, polar_smul_left, polar_smul_left, h1, h3]
    simp
  · rw [polar_add_left, polar_smul_left, polar_smul_left, h2, h4]
    simp

theorem pres_two {q₁ q₂ : V × V} (hl : IsFrame Q [q₁, q₂]) {g : V ≃ₗ[ZMod 2] V}
    (hg : g * (rot Q q₁.1 q₁.2 * rot Q q₂.1 q₂.2) = (rot Q q₁.1 q₁.2 * rot Q q₂.1 q₂.2) * g) :
    ∀ w ∈ Wspan [q₁, q₂], g w ∈ Wspan [q₁, q₂] := by
  obtain ⟨h1, hperp, hl'⟩ := isFrame_cons.1 hl
  obtain ⟨h2, -, -⟩ := isFrame_cons.1 hl'
  have hq12 : PairPerp Q q₁ q₂ := hperp q₂ (by simp)
  have hq21 : PairPerp Q q₂ q₁ := hq12.symm
  have hW : Wspan [q₁, q₂] = planeSpan q₁ ⊔ planeSpan q₂ := by
    simp [Wspan]
  set c := rot Q q₁.1 q₁.2 * rot Q q₂.1 q₂.2 with hc
  have hrange : ∀ y : V, c y - y ∈ Wspan [q₁, q₂] := by
    intro y
    have e1 : rot Q q₁.1 q₁.2 (rot Q q₂.1 q₂.2 y) - rot Q q₂.1 q₂.2 y ∈ planeSpan q₁ :=
      rot_sub_mem_span h1 _
    have e2 : rot Q q₂.1 q₂.2 y - y ∈ planeSpan q₂ := rot_sub_mem_span h2 y
    have : c y - y = (rot Q q₁.1 q₁.2 (rot Q q₂.1 q₂.2 y) - rot Q q₂.1 q₂.2 y) +
        (rot Q q₂.1 q₂.2 y - y) := by
      rw [hc, LinearEquiv.mul_apply]
      abel
    rw [this, hW]
    exact Submodule.add_mem _ (Submodule.mem_sup_left e1) (Submodule.mem_sup_right e2)
  have hsurj : ∀ w ∈ Wspan [q₁, q₂], ∃ x : V, c x - x = w := by
    intro w hw
    rw [hW] at hw
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.1 hw
    obtain ⟨x₁, hx₁, hx₁u⟩ := exists_rot_sub_eq_mem h1 hu₁
    obtain ⟨x₂, hx₂, hx₂u⟩ := exists_rot_sub_eq_mem h2 hu₂
    have hx₁perp := polar_planeSpan_of_pairPerp hq12 hx₁
    have hr₂ : rot Q q₂.1 q₂.2 x₁ = x₁ := rot_apply_of_perp h2 hx₁perp.1 hx₁perp.2
    have hx₂'perp := polar_planeSpan_of_pairPerp hq21 (rot_mem_planeSpan h2 hx₂)
    have hr₁ : rot Q q₁.1 q₁.2 (rot Q q₂.1 q₂.2 x₂) = rot Q q₂.1 q₂.2 x₂ :=
      rot_apply_of_perp h1 hx₂'perp.1 hx₂'perp.2
    refine ⟨x₁ + x₂, ?_⟩
    have e1 : c x₁ - x₁ = u₁ := by
      rw [hc, LinearEquiv.mul_apply, hr₂, hx₁u]
    have e2 : c x₂ - x₂ = u₂ := by
      rw [hc, LinearEquiv.mul_apply, hr₁, hx₂u]
    rw [map_add]
    calc c x₁ + c x₂ - (x₁ + x₂) = (c x₁ - x₁) + (c x₂ - x₂) := by abel
      _ = u₁ + u₂ := by rw [e1, e2]
  intro w hw
  obtain ⟨x, rfl⟩ := hsurj w hw
  have hgx : g (c x) = c (g x) := by
    have := congrArg (fun φ : V ≃ₗ[ZMod 2] V => φ x) hg
    simpa [LinearEquiv.mul_apply] using this
  rw [map_sub, hgx]
  exact hrange (g x)

end Plane

section Conj

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

theorem fixW_conj_mem' {W : Submodule (ZMod 2) V} {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hs : ∀ w ∈ W, g w ∈ W)
    (hs' : ∀ w ∈ W, g⁻¹ w ∈ W) {h : V ≃ₗ[ZMod 2] V} (hh : h ∈ fixW Q W) :
    g * h * g⁻¹ ∈ fixW Q W := by
  refine ⟨mul_mem (mul_mem hg hh.1) (inv_mem hg), fun w hw => ?_⟩
  have h1 : g⁻¹ w ∈ W := hs' w hw
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hh.2 _ h1]
  exact g.apply_symm_apply w

theorem commutator_fixW_conj' {W : Submodule (ZMod 2) V} {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hs : ∀ w ∈ W, g w ∈ W)
    (hs' : ∀ w ∈ W, g⁻¹ w ∈ W) {n : V ≃ₗ[ZMod 2] V} (hn : n ∈ ⁅fixW Q W, fixW Q W⁆) :
    g * n * g⁻¹ ∈ ⁅fixW Q W, fixW Q W⁆ := by
  set ψ : (V ≃ₗ[ZMod 2] V) →* (V ≃ₗ[ZMod 2] V) := (MulAut.conj g).toMonoidHom with hψ
  have hle : (fixW Q W).map ψ ≤ fixW Q W := by
    rintro _ ⟨h, hh, rfl⟩
    exact fixW_conj_mem' hg hs hs' hh
  have hmap := Subgroup.map_commutator (fixW Q W) (fixW Q W) ψ
  have : ψ n ∈ ⁅(fixW Q W).map ψ, (fixW Q W).map ψ⁆ := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem ψ hn
  exact Subgroup.commutator_mono hle hle this

end Conj

section Comp

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem exists_component_single (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {lJ lI : List (V × V)} (hl : IsFrame Q (lJ ++ lI)) (hJ : lJ ≠ [])
    (hd : finrank (ZMod 2) (perpL Q lI) = 4 ∨ finrank (ZMod 2) (perpL Q lI) = 6)
    (hts : ¬ IsPlusType (Q.comp (perpL Q lI).subtype)) {c : V ≃ₗ[ZMod 2] V}
    (hc : c ∈ torus Q lI)
    (hpres : ∀ g : V ≃ₗ[ZMod 2] V, g * c = c * g → ∀ w ∈ Wspan lI, g w ∈ Wspan lI) :
    ∃ L : Subgroup (V ≃ₗ[ZMod 2] V),
      L ≤ Ω[Q] ⊓ Subgroup.centralizer ({c} : Set (V ≃ₗ[ZMod 2] V)) ∧
      (∀ g ∈ Ω[Q] ⊓ Subgroup.centralizer ({c} : Set (V ≃ₗ[ZMod 2] V)), ∀ x ∈ L,
        g * x * g⁻¹ ∈ L) ∧
      CFSG.Open.IsQuasisimple ↥L ∧ 3 ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) := by
  have hlI : IsFrame Q lI := hl.sublist (List.sublist_append_right _ _)
  have hW : IsCompl (Wspan lI) (perpOf Q (Wspan lI)) := hlI.isCompl
  have hndU : (QuadraticMap.polarBilin (Q.restrict (perpOf Q (Wspan lI)))).Nondegenerate :=
    nondeg_comp_subtype (hlI.perpL_nondeg hQ)
  have hd' : finrank (ZMod 2) (perpOf Q (Wspan lI)) = 4 ∨
      finrank (ZMod 2) (perpOf Q (Wspan lI)) = 6 := hd
  have hts2 : ¬ IsPlusType (Q.comp (perpOf Q (Wspan lI)).subtype) := hts
  have hts' : ∀ U' : Submodule (ZMod 2) (perpOf Q (Wspan lI)),
      finrank (ZMod 2) U' = finrank (ZMod 2) (perpOf Q (Wspan lI)) / 2 →
      ∃ u ∈ U', (Q.restrict (perpOf Q (Wspan lI))) u ≠ 0 := by
    intro U' hU'
    by_contra hno
    push Not at hno
    exact hts2 ⟨U', by omega, fun x hx => hno x hx⟩
  obtain ⟨hsimple, -, hnc, -, -, -, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_four_six_actual_derived_extraction
      (Q.restrict (perpOf Q (Wspan lI))) hndU hd' hts'
  obtain ⟨e⟩ := commutator_fixW_equiv (Q := Q) hW
  haveI : IsSimpleGroup ↥⁅fixW Q (Wspan lI), fixW Q (Wspan lI)⁆ := e.isSimpleGroup
  have hna : ¬ ∀ x y : ↥⁅fixW Q (Wspan lI), fixW Q (Wspan lI)⁆, x * y = y * x := by
    intro h
    apply hnc
    intro x y
    apply e.symm.injective
    rw [map_mul, map_mul, h]
  obtain ⟨hqs, hZ⟩ := isQuasisimple_of_simple_nonabelian hna
  have hperp : ∀ q ∈ lI, ∀ p ∈ lJ, PairPerp Q p q :=
    fun q hq p hp => (List.pairwise_append.1 hl.perp).2.2 p hp q hq
  refine ⟨⁅fixW Q (Wspan lI), fixW Q (Wspan lI)⁆, ?_, ?_, hqs, ?_⟩
  · refine le_inf (Subgroup.commutator_mono fixW_le_orthogonalGroup fixW_le_orthogonalGroup) ?_
    intro x hx
    have hxT : x ∈ Subgroup.centralizer (torus Q lI : Set (V ≃ₗ[ZMod 2] V)) :=
      (fixW_le_centralizer_torus hlI) ((Subgroup.commutator_le_self _) hx)
    rw [Subgroup.mem_centralizer_iff] at hxT ⊢
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hxT _ hc
  · intro g hg x hx
    have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := (Subgroup.commutator_le_self _) hg.1
    have hgc : g * c = c * g := by
      have := (Subgroup.mem_centralizer_iff.1 hg.2) c (Set.mem_singleton _)
      exact this.symm
    have hgc' : g⁻¹ * c = c * g⁻¹ := by
      calc g⁻¹ * c = g⁻¹ * (c * g) * g⁻¹ := by group
        _ = g⁻¹ * (g * c) * g⁻¹ := by rw [hgc]
        _ = c * g⁻¹ := by group
    exact commutator_fixW_conj' hgO (hpres g hgc) (hpres g⁻¹ hgc') hx
  ·
    obtain ⟨p, lJ', rfl⟩ := List.exists_cons_of_ne_nil hJ
    have hp : MinusPair Q p.1 p.2 := hl.pair p (by simp)
    have hpp : ∀ q ∈ lI, PairPerp Q p q := fun q hq => hperp q hq p (by simp)
    have hmem : ∀ x : V, (∀ q ∈ lI, polar Q x q.1 = 0 ∧ polar Q x q.2 = 0) →
        x ∈ perpOf Q (Wspan lI) := by
      intro x hx
      exact (mem_perpL_iff lI x).2 (fun q hq => ⟨by rw [polar_comm]; exact (hx q hq).1, by
        rw [polar_comm]; exact (hx q hq).2⟩)
    have h1 : p.1 ∈ perpOf Q (Wspan lI) := hmem p.1 (fun q hq => ⟨(hpp q hq).1, (hpp q hq).2.1⟩)
    have h2 : p.2 ∈ perpOf Q (Wspan lI) :=
      hmem p.2 (fun q hq => ⟨(hpp q hq).2.2.1, (hpp q hq).2.2.2⟩)
    have hρ : rot Q p.1 p.2 ∈ ⁅fixW Q (Wspan lI), fixW Q (Wspan lI)⁆ :=
      rot_mem_commutator_of hp _ (reflect_mem_fixW h1) (reflect_mem_fixW h2)
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hne : rot Q p.1 p.2 ≠ 1 := by
      intro h1
      have := rot_apply_left hp
      rw [h1] at this
      exact hp.ne this
    have hord : orderOf (rot Q p.1 p.2) = 3 := orderOf_eq_prime (rot_pow_three hp) hne
    have hdvd : 3 ∣ Nat.card ↥⁅fixW Q (Wspan lI), fixW Q (Wspan lI)⁆ := by
      rw [← hord]
      exact Subgroup.orderOf_dvd_natCard _ hρ
    have e2 : (↥⁅fixW Q (Wspan lI), fixW Q (Wspan lI)⁆ ⧸
        Subgroup.center ↥⁅fixW Q (Wspan lI), fixW Q (Wspan lI)⁆) ≃*
        ↥⁅fixW Q (Wspan lI), fixW Q (Wspan lI)⁆ :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    rw [Nat.card_congr e2.toEquiv]
    exact hdvd

end Comp

section Assemble

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem omCoreSingle_abstract (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : finrank (ZMod 2) V = 8) (hnp : ¬ IsPlusType Q)
    {E : Subgroup (V ≃ₗ[ZMod 2] V)} (hEΩ : E ≤ Ω[Q]) (hE : IsElemAbelian 3 E)
    (hmax : ∀ E' : Subgroup (V ≃ₗ[ZMod 2] V), E' ≤ Ω[Q] → IsElemAbelian 3 E' →
      Nat.card E' ≤ Nat.card E) :
    ∃ c ∈ E, c ≠ 1 ∧ ∃ L : Subgroup (V ≃ₗ[ZMod 2] V),
      L ≤ Ω[Q] ⊓ Subgroup.centralizer ({c} : Set (V ≃ₗ[ZMod 2] V)) ∧
      (∀ g ∈ Ω[Q] ⊓ Subgroup.centralizer ({c} : Set (V ≃ₗ[ZMod 2] V)), ∀ x ∈ L,
        g * x * g⁻¹ ∈ L) ∧
      CFSG.Open.IsQuasisimple ↥L ∧ 3 ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) := by
  obtain ⟨l, hl, hEeq, hno⟩ := exists_frame_max hQ hEΩ hE hmax
  have hPd : finrank (ZMod 2) (perpL Q l) = 8 - 2 * l.length := by
    rw [perpL, LinearMap.BilinForm.finrank_orthogonal hQ, hdim, hl.finrank_Wspan]
  have hle2 := hl.finrank_perpL_le hQ hno
  have hWle : finrank (ZMod 2) (Wspan l) ≤ finrank (ZMod 2) V := Submodule.finrank_le _
  rw [hl.finrank_Wspan, hdim] at hWle
  have hs : l.length = 4 ∨ l.length = 3 := by omega
  rcases hs with hs | hs
  ·
    exfalso
    apply hnp
    have hP0 : perpL Q l = ⊥ := Submodule.finrank_eq_zero.1 (by omega)
    have htop : Wspan l = ⊤ := by
      have := hl.isCompl.sup_eq_top
      rwa [hP0, sup_bot_eq] at this
    refine isPlusType_of_Wspan_eq_top htop ((isPlusType_Wspan_iff hl).2 ?_)
    rw [hs]
    decide
  · rcases l with _ | ⟨p, l'⟩
    · simp at hs
    · have hlen : l'.length = 2 := by simpa using hs
      obtain ⟨q₁, q₂, rfl⟩ := List.length_eq_two.1 hlen
      obtain ⟨hp, hperp, hlI⟩ := isFrame_cons.1 hl
      obtain ⟨hq₁, hperp₁, hl₂⟩ := isFrame_cons.1 hlI
      obtain ⟨hq₂, -, -⟩ := isFrame_cons.1 hl₂
      have hq12 : PairPerp Q q₁ q₂ := hperp₁ q₂ (by simp)
      have hPI : finrank (ZMod 2) (perpL Q [q₁, q₂]) = 4 := by
        rw [perpL, LinearMap.BilinForm.finrank_orthogonal hQ, hdim, hlI.finrank_Wspan]
        simp
      have hV0 : finrank (ZMod 2) (perpL Q (p :: [q₁, q₂])) = 2 := by
        rw [hPd]
        simp
      have hV0plus : IsPlusType (Q.comp (perpL Q (p :: [q₁, q₂])).subtype) :=
        isPlusType_of_no_minusPair hV0 hno
      have horth : ∀ a ∈ planeSpan p, ∀ b ∈ perpL Q (p :: [q₁, q₂]), polar Q a b = 0 := by
        intro a ha b hb
        obtain ⟨hb1, hb2⟩ := (mem_perpL_iff _ b).1 hb p List.mem_cons_self
        obtain ⟨c, d, rfl⟩ := (mem_planeSpan_iff p a).1 ha
        rw [polar_add_left, polar_smul_left, polar_smul_left, hb1, hb2]
        simp
      have hdisj : Disjoint (planeSpan p) (perpL Q (p :: [q₁, q₂])) := by
        rw [disjoint_iff, eq_bot_iff]
        intro x hx
        obtain ⟨hb1, hb2⟩ := (mem_perpL_iff _ x).1 hx.2 p List.mem_cons_self
        have := hp.eq_zero_of_mem_planeSpan_of_mem_perp hx.1
          ((mem_perpPlane_iff p x).2 ⟨hb1, hb2⟩)
        exact (Submodule.mem_bot _).2 this
      have hle : planeSpan p ⊔ perpL Q (p :: [q₁, q₂]) ≤ perpL Q [q₁, q₂] := by
        refine sup_le ?_ ?_
        · intro a ha
          rw [perpL, LinearMap.BilinForm.mem_orthogonal_iff]
          intro m hm
          rw [QuadraticMap.polarBilin_apply_apply, polar_comm]
          exact polar_planeSpan_Wspan hperp ha hm
        · intro x hx
          rw [mem_perpL_iff] at hx ⊢
          exact fun q hq => hx q (List.mem_cons_of_mem _ hq)
      have hfin : finrank (ZMod 2)
          (planeSpan p ⊔ perpL Q (p :: [q₁, q₂]) : Submodule (ZMod 2) V) = 4 := by
        have h := Submodule.finrank_sup_add_finrank_inf_eq (planeSpan p)
          (perpL Q (p :: [q₁, q₂]))
        rw [hdisj.eq_bot, finrank_bot, hp.finrank_planeSpan, hV0] at h
        omega
      have heq : planeSpan p ⊔ perpL Q (p :: [q₁, q₂]) = perpL Q [q₁, q₂] :=
        Submodule.eq_of_le_of_finrank_eq hle (by rw [hfin, hPI])
      have hndV0 : (QuadraticMap.polarBilin
          (Q.comp (perpL Q (p :: [q₁, q₂])).subtype)).Nondegenerate :=
        nondeg_comp_subtype (hl.perpL_nondeg hQ)
      have hts : ¬ IsPlusType (Q.comp (perpL Q [q₁, q₂]).subtype) := by
        intro hpl
        have h1 := (isPlusType_congr (CFSG.RankThree.PartOne.K159.isometryOfEq Q heq)).2 hpl
        rw [isPlusType_sup_iff hdisj horth (nondeg_planeSpan hp) hndV0 (le_refl 1) (le_refl 1)
          (by rw [hp.finrank_planeSpan]) (by rw [hV0])] at h1
        exact not_isPlusType_planeSpan hp (h1.2 hV0plus)
      have hcmem : rot Q q₁.1 q₁.2 * rot Q q₂.1 q₂.2 ∈ torus Q [q₁, q₂] :=
        mul_mem (rot_mem_torus (by simp)) (rot_mem_torus (by simp))
      obtain ⟨L, hL1, hL2, hL3, hL4⟩ := exists_component_single hQ (lJ := [p]) (lI := [q₁, q₂]) hl
        (by simp) (Or.inl hPI) hts hcmem (fun g hg => pres_two hlI hg)
      refine ⟨rot Q q₁.1 q₁.2 * rot Q q₂.1 q₂.2, ?_, ?_, L, hL1, hL2, hL3, hL4⟩
      · rw [hEeq]
        exact torus_mono (fun q hq => List.mem_cons_of_mem _ hq) hcmem
      · intro h1
        have h2 : (rot Q q₁.1 q₁.2 * rot Q q₂.1 q₂.2) q₁.1 = q₁.2 := by
          rw [LinearEquiv.mul_apply, rot_apply_of_perp hq₂ hq12.1 hq12.2.1, rot_apply_left hq₁]
        rw [h1] at h2
        exact hq₁.ne h2

end Assemble

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Om

end
