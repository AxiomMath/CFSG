module

public import CFSG.LieType.Chevalley.TrialityExactFiniteOrder
public import CFSG.LieType.Chevalley.OddDiagramFrobeniusFixedDerived
public import CFSG.LieType.Chevalley.GraphFixedOddComponents
public import CFSG.LieType.Chevalley.CLSOddE7RationalDerivedIndex

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Torus

variable {K : Type} [Field K]

theorem rootDiagUnit_mem_graphFixedRootGroup_triality
    [Finite K] (σ : K ≃+* K)
    (hσ3 : ∀ c, σ (σ (σ c)) = c) (hpar : ringChar K = 2 ∨ ∃ n, Odd n ∧ ∀ c, σ c = c ^ n)
    {l : Fin TwistTag.D4.tag.rank → Kˣ}
    (hl : ∀ i, l (TwistTag.D4.perm i) = Units.map σ.toRingHom.toMonoidHom (l i)) :
    rootDiagUnit TwistTag.D4.tag l ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
  obtain ⟨v, rfl⟩ := exists_compatDiag_eq hl
  obtain ⟨s, t, heq⟩ : ∃ (s : (orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩)ˣ)
      (t : (orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩)ˣ),
      (orbitH TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ t : ModGL TwistTag.D4.tag K) *
          orbitH TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ s =
        rootDiagUnit TwistTag.D4.tag (compatDiag TwistTag.D4 σ.toRingHom
          (d4Pair (v ⟨0, by decide⟩) (v ⟨1, by decide⟩))) := by
    rcases hpar with hchar | ⟨n, hn, hσn⟩
    · obtain ⟨s, t, -, -, -, heq⟩ := exists_even_triality_torusWord σ hσ3 hchar
        (v ⟨0, by decide⟩) (v ⟨1, by decide⟩)
      exact ⟨s, t, heq⟩
    · obtain ⟨s, t, -, -, -, heq⟩ := exists_odd_triality_torusWord σ hσ3 hn hσn
        (v ⟨0, by decide⟩) (v ⟨1, by decide⟩)
      exact ⟨s, t, heq⟩
  rw [d4Pair_eta] at heq
  rw [← heq]
  exact mul_mem (orbitH_mem_graphFixedRootGroup _ _ _ _) (orbitH_mem_graphFixedRootGroup _ _ _ _)

theorem twistedFixedGroup_eq_graphFixedRootGroup_triality
    [Finite K] (σ : K ≃+* K)
    (hσ3 : ∀ c, σ (σ (σ c)) = c) (hpar : ringChar K = 2 ∨ ∃ n, Odd n ∧ ∀ c, σ c = c ^ n) :
    twistedFixedGroup TwistTag.D4 K σ.toRingHom =
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
  refine le_antisymm (fun g hg => ?_) (graphFixedRootGroup_le TwistTag.D4 K σ.toRingHom)
  have hg' : g ∈ (twistedFixedGroup TwistTag.D4 K σ.toRingHom : Set (ModGL TwistTag.D4.tag K)) :=
    hg
  rw [coe_twistedFixedGroup_eq_mul σ.surjective] at hg'
  obtain ⟨h, hh, c, hc, rfl⟩ := hg'
  obtain ⟨hhT, hhΓ⟩ := Subgroup.mem_inf.1 hh
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hhT
  exact mul_mem (rootDiagUnit_mem_graphFixedRootGroup_triality σ hσ3 hpar
    (compat_of_twistHom_rootDiagUnit
      ((mem_twistedFixedGroup_iff_twistHom TwistTag.D4 K σ.toRingHom).1 hhΓ).2)) hc

end Torus

section Descent

variable {K Ω : Type} [Field K] [Field Ω] {ι : K →+* Ω} {σ : K ≃+* K} {ψ : Ω ≃+* Ω}

theorem triple_apply_eq_of_mem_orbitField_D4 {a : Fin TwistTag.D4.foldedTag.rank} {c : Ω}
    (hc : c ∈ orbitField TwistTag.D4 Ω ψ.toRingHom a) : ψ (ψ (ψ c)) = c := by
  rw [mem_orbitField] at hc
  obtain ⟨n, hn⟩ := a
  have hn' : n < 2 := hn
  interval_cases n
  · rw [show (TwistTag.D4.orbit ⟨0, by decide⟩).card = 3 by decide, ringHom_pow_three_apply] at hc
    exact hc
  · rw [show (TwistTag.D4.orbit ⟨1, by decide⟩).card = 1 by decide, pow_one] at hc
    change ψ c = c at hc
    rw [hc, hc, hc]

theorem twistedFixedGroup_D4_eq_map_baseChangeGL
    (htorus : ∀ l : Fin TwistTag.D4.tag.rank → Kˣ,
      (∀ i, l (TwistTag.D4.perm i) = Units.map σ.toRingHom.toMonoidHom (l i)) →
        rootDiagUnit TwistTag.D4.tag l ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hcomm : ∀ c, ψ (ι c) = ι (σ c)) (hdesc : ∀ c, ψ (ψ (ψ c)) = c → c ∈ Set.range ι) :
    twistedFixedGroup TwistTag.D4 Ω ψ.toRingHom =
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).map (baseChangeGL ι) := by
  have hcomm' : ∀ c, ψ.toRingHom (ι c) = ι (σ.toRingHom c) := hcomm
  have hpar : ∀ a, ∀ c ∈ orbitField TwistTag.D4 Ω ψ.toRingHom a,
      ∃ c₀ ∈ orbitField TwistTag.D4 K σ.toRingHom a, ι c₀ = c := by
    intro a c hc
    obtain ⟨c₀, rfl⟩ := hdesc c (triple_apply_eq_of_mem_orbitField_D4 hc)
    refine ⟨c₀, ?_, rfl⟩
    rw [mem_orbitField] at hc ⊢
    apply ι.injective
    rw [← ringHom_pow_apply_comm hcomm', hc]
  have hH : graphFixedTorus TwistTag.D4 Ω ψ.toRingHom ≤
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).map (baseChangeGL ι) := by
    intro h hh
    obtain ⟨hhT, hhΓ⟩ := Subgroup.mem_inf.1 hh
    obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hhT
    have hl := compat_of_twistHom_rootDiagUnit
      ((mem_twistedFixedGroup_iff_twistHom TwistTag.D4 Ω ψ.toRingHom).1 hhΓ).2
    have hl' : ∀ i, (l (TwistTag.D4.perm i) : Ω) = ψ (l i) := fun i => congrArg Units.val (hl i)
    have hperm : ∀ i : Fin TwistTag.D4.tag.rank,
        TwistTag.D4.perm (TwistTag.D4.perm (TwistTag.D4.perm i)) = i := by decide
    have h3 : ∀ i, ψ (ψ (ψ (l i : Ω))) = l i := fun i => by
      rw [← hl', ← hl', ← hl', hperm]
    choose c hc using fun i => hdesc _ (h3 i)
    have hc0 : ∀ i, c i ≠ 0 := fun i h0 => (l i).ne_zero (by rw [← hc i, h0, map_zero])
    have hcompat : ∀ i, (fun j => Units.mk0 (c j) (hc0 j)) (TwistTag.D4.perm i) =
        Units.map σ.toRingHom.toMonoidHom ((fun j => Units.mk0 (c j) (hc0 j)) i) :=
      fun i => Units.ext (ι.injective (by
        change ι (c (TwistTag.D4.perm i)) = ι (σ (c i))
        rw [hc, ← hcomm, hc, hl']))
    have heq : rootDiagUnit TwistTag.D4.tag l =
        baseChangeGL ι (rootDiagUnit TwistTag.D4.tag fun j => Units.mk0 (c j) (hc0 j)) := by
      rw [baseChangeGL_rootDiagUnit]
      congr 1
      funext i
      exact Units.ext (hc i).symm
    rw [heq]
    exact Subgroup.mem_map_of_mem _ (htorus _ hcompat)
  refine le_antisymm (fun g hg => ?_) ((map_baseChangeGL_graphFixedRootGroup_le σ.surjective
    hcomm').trans (graphFixedRootGroup_le _ _ _))
  have hg' : g ∈ (twistedFixedGroup TwistTag.D4 Ω ψ.toRingHom : Set (ModGL TwistTag.D4.tag Ω)) :=
    hg
  rw [coe_twistedFixedGroup_eq_mul ψ.surjective] at hg'
  obtain ⟨h, hh, x, hx, rfl⟩ := hg'
  exact mul_mem (hH hh) (graphFixedRootGroup_le_map_baseChangeGL ψ.surjective hcomm' hpar hx)

end Descent

theorem diagramMap_sq_conj_eq_iff
    {L : Type} [Field L] (Fr : L ≃+* L)
    (g : ModGL TwistTag.D4.tag L) :
    diagramMap TwistTag.D4 L ^ 2 * Units.map (entrywiseHom Fr.toRingHom) g *
        (diagramMap TwistTag.D4 L ^ 2)⁻¹ = g ↔
      twistHom TwistTag.D4 L Fr.symm.toRingHom g = g := by
  have hP3 : diagramMap TwistTag.D4 L ^ 3 = 1 := diagramMap_pow_order TwistTag.D4 L
  have hcomp : ∀ (e : L ≃+* L) (x : ModGL TwistTag.D4.tag L),
      Units.map (entrywiseHom e.toRingHom) (Units.map (entrywiseHom e.symm.toRingHom) x) = x := by
    intro e x
    rw [units_map_entrywiseHom_comp]
    have he : e.toRingHom.comp e.symm.toRingHom = RingHom.id L :=
      RingHom.ext fun c => e.apply_symm_apply c
    rw [he]
    exact Units.ext (entrywise_id _)
  have hcomp' : ∀ x : ModGL TwistTag.D4.tag L,
      Units.map (entrywiseHom Fr.symm.toRingHom) (Units.map (entrywiseHom Fr.toRingHom) x) = x := by
    intro x
    have := hcomp Fr.symm x
    rwa [RingEquiv.symm_symm] at this
  rw [twistHom_apply]
  constructor
  · intro h
    have h' := congrArg (Units.map (entrywiseHom Fr.symm.toRingHom)) h
    rw [map_mul, map_mul, map_inv, map_pow, units_map_entrywiseHom_diagramMap, hcomp'] at h'
    rw [← h']
    calc diagramMap TwistTag.D4 L * (diagramMap TwistTag.D4 L ^ 2 * g *
          (diagramMap TwistTag.D4 L ^ 2)⁻¹) * (diagramMap TwistTag.D4 L)⁻¹ =
        diagramMap TwistTag.D4 L ^ 3 * g * (diagramMap TwistTag.D4 L ^ 3)⁻¹ := by group
      _ = g := by rw [hP3, one_mul, inv_one, mul_one]
  · intro h
    have h' := congrArg (Units.map (entrywiseHom Fr.toRingHom)) h
    rw [map_mul, map_mul, map_inv, units_map_entrywiseHom_diagramMap, hcomp] at h'
    rw [← h']
    calc diagramMap TwistTag.D4 L ^ 2 * (diagramMap TwistTag.D4 L * g *
          (diagramMap TwistTag.D4 L)⁻¹) * (diagramMap TwistTag.D4 L ^ 2)⁻¹ =
        diagramMap TwistTag.D4 L ^ 3 * g * (diagramMap TwistTag.D4 L ^ 3)⁻¹ := by group
      _ = g := by rw [hP3, one_mul, inv_one, mul_one]

section Simple

variable {K : Type} [Field K]

theorem orbitX_outer_mem_commutator_triality
    [Finite K] (σ : K ≃+* K)
    (hσ3 : ∀ c, σ (σ (σ c)) = c) (h4 : 4 ≤ Nat.card K)
    (c : orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩) :
    (orbitX TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ c : ModGL TwistTag.D4.tag K) ∈
      ⁅graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom⁆ := by
  have : Fintype K := Fintype.ofFinite K
  have hmem : ∀ x : K, x ∈ orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ := fun x => by
    rw [orbitField_D4_zero_eq_top σ hσ3]
    exact Subfield.mem_top x
  have hL : ∃ s : Finset (orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩), 4 ≤ s.card :=
    ⟨(Finset.univ : Finset K).map ⟨fun x => ⟨x, hmem x⟩, fun x y h => congrArg Subtype.val h⟩,
      by rw [Finset.card_map, Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4⟩
  exact ((fixed_orbit_rank_one_scalar_perfectness TwistTag.D4 K σ.toRingHom).2.2 _ hL c).1

theorem orbitX_middle_mem_commutator_triality
    (hchar : ringChar K = 2) (σ : K ≃+* K)
    (c : orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩) :
    (orbitX TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ c : ModGL TwistTag.D4.tag K) ∈
      ⁅graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom⁆ := by
  have : CharP K 2 := ringChar.of_eq hchar
  have hc : σ (c : K) = c := (mem_orbitField_D4_one σ).1 c.2
  have h3 : (3 : K) * (c : K) = c := by
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    linear_combination (c : K) * h2
  rw [coe_orbitX_of_card_eq_one (show (TwistTag.D4.orbit ⟨1, by decide⟩).card = 1 by decide),
    show TwistTag.D4.orbitMin ⟨1, by decide⟩ = ⟨2, by decide⟩ by decide, ← h3]
  exact xUnit_three_mul_mem_commutator_D4 hc

theorem commutator_graphFixedRootGroup_triality_char_two
    [Finite K] (hchar : ringChar K = 2)
    (σ : K ≃+* K) (hσ3 : ∀ c, σ (σ (σ c)) = c) (h4 : 4 ≤ Nat.card K) :
    ⁅graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom⁆ =
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
  refine le_antisymm (Subgroup.commutator_le.2 fun x hx y hy =>
    mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)) ?_
  refine (le_of_eq (graphFixedRootGroup_eq_closure σ.toRingHom σ.surjective)).trans
    ((Subgroup.closure_le _).2 ?_)
  rintro _ ⟨w, hw, a, c, rfl⟩
  refine conj_mem_commutator_self (canonicalRep_mem_graphFixedRootGroup hw) ?_
  obtain ⟨n, hn⟩ := a
  have hn' : n < 2 := hn
  interval_cases n
  · exact orbitX_outer_mem_commutator_triality σ hσ3 h4 c
  · exact orbitX_middle_mem_commutator_triality hchar σ c

theorem isSimpleGroup_graphFixedRootGroup_of_perfect
    (t : TwistTag) (K : Type) [Field K]
    (σ : K ≃+* K)
    (hperf : ⁅graphFixedRootGroup t K σ.toRingHom, graphFixedRootGroup t K σ.toRingHom⁆ =
      graphFixedRootGroup t K σ.toRingHom) :
    IsSimpleGroup (graphFixedRootGroup t K σ.toRingHom) ∧
    ∃ x y : graphFixedRootGroup t K σ.toRingHom, x * y ≠ y * x := by
  set C := graphFixedRootGroup t K σ.toRingHom with hCdef
  obtain ⟨i₀⟩ : Nonempty (Fin t.tag.rank) := ⟨⟨0, by cases t <;> decide⟩⟩
  set a := t.orbitIndex i₀
  have hx1 : (orbitX t K σ.toRingHom a 1 : ModGL t.tag K) ≠ 1 := fun h => by
    have h' : orbitX t K σ.toRingHom a 1 = orbitX t K σ.toRingHom a 0 := by
      rw [orbitX_zero]
      exact Subtype.ext h
    exact one_ne_zero (orbitX_injective σ.toRingHom a h')
  have hxC : (orbitX t K σ.toRingHom a 1 : ModGL t.tag K) ∈ C :=
    graphFixedPosUnipotent_le_graphFixedRootGroup t K σ.toRingHom
      (orbitX_mem_graphFixedPosUnipotent t σ.toRingHom a 1)
  have hnc : ∃ x y : C, x * y ≠ y * x := by
    by_contra h
    push Not at h
    have hbot : ⁅C, C⁆ = ⊥ := (Subgroup.commutator_eq_bot_iff_le_centralizer).2 fun x hx y hy =>
      congrArg Subtype.val (h ⟨y, hy⟩ ⟨x, hx⟩)
    rw [hperf] at hbot
    exact hx1 (by rw [hbot] at hxC; exact (Subgroup.mem_bot).1 hxC)
  have : Group.IsPerfect C := Subgroup.isPerfect_iff.2 hperf
  have : Nontrivial C := by
    obtain ⟨x, y, hxy⟩ := hnc
    exact ⟨⟨x * y, y * x, hxy⟩⟩
  have hZ := exceptional_fixed_center_trivial t K σ
  refine ⟨IsSimpleGroup.mk fun M hM => ?_, hnc⟩
  by_cases hbot : M = ⊥
  · exact Or.inl hbot
  · right
    have hnot : ¬ M ≤ Subgroup.center C := by
      rw [hZ]
      exact fun h => hbot (le_bot_iff.1 h)
    have hsolv := fixed_noncentral_normal_solvable_quotient t K σ M hnot
    by_contra htop
    have : Nontrivial (C ⧸ M) := by
      rw [← not_subsingleton_iff_nontrivial, QuotientGroup.subsingleton_iff]
      exact htop
    exact Group.IsPerfect.not_isSolvable _ hsolv

end Simple

theorem fixedSet_D4_eq_map_baseChangeGL
    {ℓ d : ℕ} (hℓ : ℓ.Prime) (hd : 1 ≤ d)
    {K : Type} [Field K] (hK : Nat.card K = (ℓ ^ d) ^ 3) {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    [Algebra K Ω] (r : ℕ) (hr : r = 1 ∨ r = 2) (σ : K →+* K)
    (hσ : ∀ c, σ c = c ^ ((ℓ ^ d) ^ r)) (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ (ℓ ^ d)) :
    {g : ModGL TwistTag.D4.tag Ω | g ∈ adjointGroup TwistTag.D4.tag Ω ∧
        diagramMap TwistTag.D4 Ω ^ r * Units.map (entrywiseHom Fr) g *
          (diagramMap TwistTag.D4 Ω ^ r)⁻¹ = g} =
      ((graphFixedRootGroup TwistTag.D4 K σ).map (baseChangeGL (algebraMap K Ω)) :
        Set (ModGL TwistTag.D4.tag Ω)) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have : Fintype K := Fintype.ofFinite K
  have hcharK : CharP K ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ
      (k := d * 3) (by omega) (by rw [hK, pow_mul])
  set q := ℓ ^ d with hqdef
  have hq2 : 2 ≤ q := le_trans hℓ.two_le (Nat.le_self_pow (by omega) ℓ)
  have hq3 : ∀ c : K, c ^ (q ^ 3) = c := fun c => by
    rw [← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hσ3 : ∀ c, σ (σ (σ c)) = c := fun c => by
    rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul]
    rcases hr with rfl | rfl
    · rw [pow_one, show q * (q * q) = q ^ 3 by ring, hq3]
    · rw [show q ^ 2 * (q ^ 2 * q ^ 2) = q ^ 3 * q ^ 3 by ring, pow_mul, hq3, hq3]
  obtain ⟨σE, rfl⟩ : ∃ σE : K ≃+* K, σE.toRingHom = σ :=
    ⟨RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩,
      RingHom.ext fun _ => rfl⟩
  have hσE : ∀ c, σE c = c ^ (q ^ r) := hσ
  have hσ3E : ∀ c, σE (σE (σE c)) = c := hσ3
  have hFrsurj : Function.Surjective Fr := fun y => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq y (pow_pos hℓ.pos d)
    exact ⟨z, by rw [hFr, hz]⟩
  obtain ⟨FrE, rfl⟩ : ∃ FrE : Ω ≃+* Ω, FrE.toRingHom = Fr :=
    ⟨RingEquiv.ofBijective Fr ⟨Fr.injective, hFrsurj⟩, RingHom.ext fun _ => rfl⟩
  have hFrE : ∀ c, FrE c = c ^ q := hFr
  have hpar : ringChar K = 2 ∨ ∃ n, Odd n ∧ ∀ c, σE c = c ^ n := by
    rcases hℓ.eq_two_or_odd' with h2 | hodd
    · exact Or.inl (by rw [ringChar.eq K ℓ, h2])
    · exact Or.inr ⟨q ^ r, hodd.pow.pow, hσE⟩
  have htorus : ∀ l : Fin TwistTag.D4.tag.rank → Kˣ,
      (∀ i, l (TwistTag.D4.perm i) = Units.map σE.toRingHom.toMonoidHom (l i)) →
        rootDiagUnit TwistTag.D4.tag l ∈ graphFixedRootGroup TwistTag.D4 K σE.toRingHom :=
    fun l hl => rootDiagUnit_mem_graphFixedRootGroup_triality σE hσ3E hpar hl
  have hdesc3 : ∀ c : Ω, FrE (FrE (FrE c)) = c → c ∈ Set.range (algebraMap K Ω) := by
    intro c h
    refine mem_range_algebraMap_of_pow_card_eq ?_
    rw [hK, show q ^ 3 = q * q * q by ring, pow_mul, pow_mul]
    rw [hFrE, hFrE, hFrE] at h
    exact h
  obtain ⟨ψ, hfix, hcomm, hdesc⟩ : ∃ ψ : Ω ≃+* Ω,
      (∀ g, (g ∈ adjointGroup TwistTag.D4.tag Ω ∧
        diagramMap TwistTag.D4 Ω ^ r * Units.map (entrywiseHom FrE.toRingHom) g *
          (diagramMap TwistTag.D4 Ω ^ r)⁻¹ = g) ↔
        g ∈ twistedFixedGroup TwistTag.D4 Ω ψ.toRingHom) ∧
      (∀ c, ψ (algebraMap K Ω c) = algebraMap K Ω (σE c)) ∧
      (∀ c, ψ (ψ (ψ c)) = c → c ∈ Set.range (algebraMap K Ω)) := by
    rcases hr with rfl | rfl
    · refine ⟨FrE, fun g => ?_, fun c => ?_, hdesc3⟩
      · rw [mem_twistedFixedGroup_iff_twistHom, twistHom_apply, pow_one]
      · rw [hFrE, hσE, pow_one, map_pow]
    · refine ⟨FrE.symm, fun g => ?_, fun c => ?_, fun c h => hdesc3 c ?_⟩
      · rw [mem_twistedFixedGroup_iff_twistHom, ← diagramMap_sq_conj_eq_iff FrE g]
      · rw [RingEquiv.symm_apply_eq, hFrE, hσE, ← map_pow, ← pow_mul,
          show q ^ 2 * q = q ^ 3 by ring, hq3]
      · calc FrE (FrE (FrE c)) = FrE (FrE (FrE (FrE.symm (FrE.symm (FrE.symm c))))) := by
              rw [h]
          _ = c := by simp only [RingEquiv.apply_symm_apply]
  refine Set.ext fun g => (hfix g).trans ?_
  rw [twistedFixedGroup_D4_eq_map_baseChangeGL htorus hcomm hdesc]
  rfl

theorem triality_both_field_orientations_simple_full_ambient_fixed_group
    (ℓ d : ℕ)
    (hℓ : ℓ.Prime) (hd : 1 ≤ d) (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ d) ^ 3)
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (r : ℕ) (hr : r = 1 ∨ r = 2)
    (σ : K →+* K) (hσ : ∀ c, σ c = c ^ ((ℓ ^ d) ^ r)) (Fr : Ω →+* Ω)
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ d)) :
    orderOf σ = 3 ∧
    {g : ModGL TwistTag.D4.tag Ω | g ∈ adjointGroup TwistTag.D4.tag Ω ∧
        diagramMap TwistTag.D4 Ω ^ r * Units.map (entrywiseHom Fr) g *
          (diagramMap TwistTag.D4 Ω ^ r)⁻¹ = g} =
      ((graphFixedRootGroup TwistTag.D4 K σ).map (baseChangeGL (algebraMap K Ω)) :
        Set (ModGL TwistTag.D4.tag Ω)) ∧
    twistedFixedGroup TwistTag.D4 K σ = graphFixedRootGroup TwistTag.D4 K σ ∧
    IsSimpleGroup (graphFixedRootGroup TwistTag.D4 K σ) ∧
    ∃ x y : graphFixedRootGroup TwistTag.D4 K σ, x * y ≠ y * x := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hGS := fixedSet_D4_eq_map_baseChangeGL hℓ hd hK r hr σ hσ Fr hFr
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have : Fintype K := Fintype.ofFinite K
  have hcharK : CharP K ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ
      (k := d * 3) (by omega) (by rw [hK, pow_mul])
  have hσ1 : σ ≠ 1 := fun h1 => by
    have hcard := card_orbitField_D4_orientation hℓ hd hK hr hσ ⟨1, by decide⟩
    have htop : orbitField TwistTag.D4 K σ ⟨1, by decide⟩ = ⊤ :=
      eq_top_iff.2 fun c _ => by
        rw [mem_orbitField, h1, one_pow]
        rfl
    rw [htop, show (TwistTag.D4.orbit ⟨1, by decide⟩).card = 1 by decide, pow_one,
      Nat.card_congr Subfield.topEquiv.toEquiv, hK] at hcard
    have hq2 : 2 ≤ ℓ ^ d := le_trans hℓ.two_le (Nat.le_self_pow (by omega) ℓ)
    have hlt : ℓ ^ d < (ℓ ^ d) ^ 3 := by
      calc ℓ ^ d = (ℓ ^ d) ^ 1 := (pow_one _).symm
        _ < (ℓ ^ d) ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    exact hlt.ne' hcard
  set q := ℓ ^ d with hqdef
  have hq2 : 2 ≤ q := le_trans hℓ.two_le (Nat.le_self_pow (by omega) ℓ)
  have hq3 : ∀ c : K, c ^ (q ^ 3) = c := fun c => by
    rw [← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hσ3 : ∀ c, σ (σ (σ c)) = c := fun c => by
    rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul]
    rcases hr with rfl | rfl
    · rw [pow_one, show q * (q * q) = q ^ 3 by ring, hq3]
    · rw [show q ^ 2 * (q ^ 2 * q ^ 2) = q ^ 3 * q ^ 3 by ring, pow_mul, hq3, hq3]
  have hord : orderOf σ = 3 :=
    orderOf_eq_prime (RingHom.ext fun c => by rw [ringHom_pow_three_apply, hσ3]; rfl) hσ1
  obtain ⟨σE, rfl⟩ : ∃ σE : K ≃+* K, σE.toRingHom = σ :=
    ⟨RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩,
      RingHom.ext fun _ => rfl⟩
  have hσE : ∀ c, σE c = c ^ (q ^ r) := hσ
  have hσ3E : ∀ c, σE (σE (σE c)) = c := hσ3
  have hpar : ringChar K = 2 ∨ ∃ n, Odd n ∧ ∀ c, σE c = c ^ n := by
    rcases hℓ.eq_two_or_odd' with h2 | hodd
    · exact Or.inl (by rw [ringChar.eq K ℓ, h2])
    · exact Or.inr ⟨q ^ r, hodd.pow.pow, hσE⟩
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 ≤ 2 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq2 3
  have hsimple : IsSimpleGroup (graphFixedRootGroup TwistTag.D4 K σE.toRingHom) ∧
      ∃ x y : graphFixedRootGroup TwistTag.D4 K σE.toRingHom, x * y ≠ y * x := by
    by_cases h2 : ringChar K = 2
    · exact isSimpleGroup_graphFixedRootGroup_of_perfect TwistTag.D4 K σE
        (commutator_graphFixedRootGroup_triality_char_two h2 σE hσ3E h4)
    · obtain ⟨hs, hnc, -⟩ := odd_diagram_field_fixed_p_components TwistTag.D4 K h2 σE
      exact ⟨hs, hnc⟩
  exact ⟨hord, hGS, twistedFixedGroup_eq_graphFixedRootGroup_triality σE hσ3E hpar, hsimple⟩

end CFSG.LieType.Chevalley
